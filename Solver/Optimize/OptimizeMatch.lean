import Lean
import Solver.Optimize.Utils
import Solver.Translate.Env

open Lean Meta Elab
namespace Solver.Optimize

/-- Given a sequence of match pattern `p₁, ..., pₙ`,
    return a sequence of free variables appearing in each `pᵢ`.
    The returned sequence preserves the order of appearance of free variables in
    each `pᵢ` and w.r.t. the input sequence.
    Trigger an error if at least one `pᵢ` does not correspond to:
      - A nullary constructor;
      - A String/Nat literal;
      - A constructor/function application; or
      - A free variable.
    NOTE: This function Assumes that each pᵢ does not have any named pattern,
    i.e., pᵢ has been optimized first.
-/
partial def retrieveAltsArgs (alts : Array Expr) : MetaM (Array Expr) := do
 let rec visit (e : Expr) (args : Array Expr) : MetaM (Array Expr) := do
   match e with
   | Expr.const .. | Expr.lit .. => return args
   | Expr.fvar .. => return args.push e
   | Expr.app .. =>
      Expr.withApp e fun f as => do
       match f with
       | Expr.const n _ =>
          let mut margs := args
          match (← getConstInfo n) with
          | ConstantInfo.ctorInfo info =>
              -- constructor application
              let ctorArgs := as[info.numParams:as.size]
              for i in [:ctorArgs.size] do
                margs ← visit ctorArgs[i]! margs
              return margs
          | _ =>
             for i in [:as.size] do
                margs ← visit as[i]! margs
             return margs
       | _ => throwError "retrieveAltsArgs: const expression expected but got {reprStr f} !!!"
   | _ => throwError "retrieveAltsArgs: unexpected expression: {reprStr e} !!!"
 let mut args := #[]
 for i in [:alts.size] do
   args ← visit alts[i]! args
 return args


/-- Perform beta reduction on a match alternative `alt` according to the provided arguments `args`.
    It is expected that `args` will contain only the free variables appearing in each pattern pᵢ
    and irrespective of named patterns (see `retrieveAltsArgs`).
    Moreover, given a sequence of match pattern `p₁, ..., pₙ => t`, s.t.
    each pᵢ contains named patterns of the form:
      (l₍₁₎₍₁₎ (sp₍₁₎₍₁₎ .. (l₍₁₎₍ₖ₋₁₎ (sp₍₁₎₍ₖ₋₁₎ (l₍₁₎₍ₖ₎ sp₍₁₎₍ₖ₎))))), ...,
      (l₍ₙ₎₍₁₎ (sp₍ₙ₎₍₁₎ .. (l₍ₙ₎₍ₖ₋₁₎ (sp₍ₙ₎₍ₖ₋₁₎ (l₍ₙ₎₍ₖ₎ sp₍ₙ₎₍ₖ₎))))) => t
    with
      - l₍ᵢ₎₍ⱼ₎: correponding to the label of the named sub-pattern.
      - sp₍ᵢ₎₍ⱼ₎: corresponding to a sub-pattern that may contain free variables `v₍ᵢ₎₍ⱼ₎₍₁₎, ..., v₍ᵢ₎₍ⱼ₎₍ₘ₎`
      - args.size = n * k * m (i.e., `args` only contains the free variables `v₍₁₎₍₁₎₍₁₎, ..., v₍ₙ₎₍ₖ₎₍ₘ₎`.
    The corresponding alternative for `t` is expected to be of the following form:
      l₍₁₎₍₁₎ → v₍₁₎₍₁₎₍₁₎ ... → v₍₁₎₍₁₎₍ₘ₎ → ... → l₍₁₎₍ₖ₎ → v₍₁₎₍ₖ₎₍₁₎ ... → v₍₁₎₍ₖ₎₍ₘ₎ →
        l₍₁₎₍₁₎ = sp₍₁₎₍₁₎ → l₍₁₎₍₂₎ = sp₍₁₎₍₂₎ → ... → l₍₁₎₍ₖ₎ = sp₍₁₎₍ₖ₎ → ...

      l₍ₙ₎₍₁₎ → v₍ₙ₎₍₁₎₍₁₎ ... → v₍ₙ₎₍₁₎₍ₘ₎ → ... → l₍ₙ₎₍ₖ₎ → v₍ₙ₎₍ₖ₎₍₁₎ ... → v₍ₙ₎₍ₖ₎₍ₘ₎ →
        l₍ₙ₎₍₁₎ = sp₍ₙ₎₍₁₎ → l₍ₙ₎₍₂₎ = sp₍ₙ₎₍₂₎ → ... → l₍ₙ₎₍ₖ₎ = sp₍ₙ₎₍ₖ₎ → t
    Hence, when args.size > 0 the following substitution on t is applied in reverse order.
      t[l₍ₙ₎₍ₖ₎/sp₍ₙ₎₍ₖ₎] ... [ l₍ₙ₎₍₁₎ / sp₍ₙ₎₍₁₎] [v₍ₙ₎₍ₖ₎₍ₘ₎ / args[n*k*m - 1]] ... [v₍ₙ₎₍₁₎₍₁₎ / args[n*k*m - m]] ...
       [l₍₁₎₍ₖ₎/ sp₍₁₎₍ₖ₎] ... [ l₍₁₎₍₁₎ = sp₍₁₎₍₁₎] [v₍₁₎₍ₖ₎₍ₘ₎ / args[n*k*m - n*k - 1]] ... [v₍₁₎₍₁₎₍₁₎ / args[0]]
-/
partial def betaReduceAlt (alt : Expr) (args : Array Expr) : TranslateEnvT Expr :=
lambdaTelescope alt fun xs rhs => do
  -- populate namedPatternSet first and replace named pattern hypothesis with expression.
  let mut mxs := xs
  let mut namedPatternSet := (.empty : HashSet Expr)
  for i in [:xs.size] do
    let t ← inferType xs[i]!
    if let some (_eq_sort, op1, op2) := t.eq?
    then match op1, op2 with
         | p@(Expr.fvar ..), _ | _,  p@(Expr.fvar ..) =>
              namedPatternSet := namedPatternSet.insert p
              mxs := mxs.set! i t
         | _, _ => throwError "betaReduceAlt: Invalid namedPattern hypothesis {reprStr op1} = {reprStr op2}"
  let mut argsIdx := 0
  let mut betaRhs := rhs
  for i in [:xs.size] do
    let lamArg := mxs[i]!
    match lamArg.eq? with
    | some (_eq_sort, op1@(Expr.fvar ..), op2) | some (_eq_sort, op2, op1@(Expr.fvar ..)) =>
        -- named pattern hypothesis, e.q., l₍ᵢ₎₍ⱼ₎ = sp₍ᵢ₎₍ⱼ₎
        -- Apply optimization rule `N1 + (n - N2) ===> n - (N2 "-" N1) when Type(n) = Nat`
        -- NOTE: This rule is generally unsound for Nat, especially when n < N2 or when N2 < N1
        -- However, it is here sound to apply this optimization as
        -- we know that n ≥ N2 ∧ N2 ≥ N1 (see normMatchExpr? specification).
        betaRhs := betaRhs.replaceFVar op1 (← optimizeSubPattern op2)
    | _ =>
       -- case when op1 and op2 are not fvar is unreachable at this stage
       unless (namedPatternSet.contains lamArg || args.size == 0) do
         let altArg := args[argsIdx]!
         -- only replace with args when lamArg does not correspond to a namedPattern label.
         betaRhs := betaRhs.replaceFVar lamArg altArg
         -- replace all occurrences of lamArg in renaming mxs
         -- This is necessary to apply specific Nat optimization
         -- only on named pattern hypothesis, i.e., not in the rhs expression.
         for j in [i+1:xs.size] do
           mxs := mxs.modify j (fun a => a.replaceFVar lamArg altArg)
         argsIdx := argsIdx + 1
  return betaRhs

  where
    /-- Try to apply optimization rule `N1 + (n - N2) ===> n - (N2 "-" N1) on `sp` when Type(n) = Nat`.
        Perform recursion if `sp := Int.ofNat e`.
        Return `sp` if the optimization cannot be applied.
    -/
    optimizeSubPattern (sp : Expr) : TranslateEnvT Expr :=
       match sp.app2? ``Nat.add with
       | some (Expr.lit (Literal.natVal n1), x) =>
          match x.app2? ``Nat.sub with
          | some (y, Expr.lit (Literal.natVal n2)) =>
              return (mkApp2 (← mkNatSubOp) y (← evalBinNatOp Nat.sub n2 n1))
          | _ => return sp
       | _ =>
         match sp.app1? ``Int.ofNat with
         | some e => return mkApp (← mkIntOfNat) (← optimizeSubPattern e)
         | _ => return sp

/-- Normalize a `match` expression to `if-then-else` only when each match pattern is either
      - an constructor application that does not contain any free variables (e.g., `Nat.zero`, `some Nat.zero`, `List.const 0 (List.nil)`); or
      - a `Nat` or `Int` expression; or
      - a free variable `v`
    Normalization will not take place when no decidable equality instance can be found for each match discriminator.
    Concretely:
      match e₁, ..., eₙ with
      | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
      ...
      | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ
     ===>
       if eq₍₁₎₍₁₎ ∧ ... ∧ eq₍₁₎₍ₙ₎ then t₁[p₍₁₎₍₁₎/e₁] ... [p₍₁₎₍ₙ₎/eₙ]
       else if eq₍₂₎₍₁₎ ∧ ... ∧ eq₍₂₎₍ₙ₎ then t₂[p₍₂₎₍₁₎/e₁] ... [p₍₂₎₍ₙ₎/eₙ]
       ...
       else tₘ[p₍ₘ₎₍₁₎/e₁] ... [p₍ₘ₎₍ₙ₎/eₙ]
     when:
       - ∀ i ∈ [1..m], ∀ j ∈ [1..n],
           ( NoFreeVar(p₍ᵢ₎₍ⱼ₎) ∨ p₍ᵢ₎₍ⱼ₎ = v ∨ Type(eⱼ) ∈ {Nat, Int} ) ∧
           ∃ [ Decidable (eⱼ = p₍ᵢ₎₍ⱼ₎)] ∈ DecidableInstances
     with:
       - ∀ i ∈ [1..m], ∀ j ∈ [1..n],
          - eqᵢⱼ := eᵢ = p₍ᵢ₎₍ⱼ₎      if (p₍ᵢ₎₍ⱼ₎ ≠ v ∧ Type(eᵢ) ∉ {Nat, Int}) ∨ isIntNatCst(p₍ᵢ₎₍ⱼ₎)
                := N ≤ eᵢ           if p₍ᵢ₎₍ⱼ₎ = N + n ∧ Type(eᵢ) = Nat
                := Int.ofNat 0 ≤ eᵢ if p₍ᵢ₎₍ⱼ₎ = Int.ofNat n
                := Int.ofNat N ≤ eᵢ if p₍ᵢ₎₍ⱼ₎ = Int.ofNat (N + n)
                := e ≤ -N           if p₍ᵢ₎₍ⱼ₎ = Int.Neg (Int.ofNat (N + n))
                := True             if p₍ᵢ₎₍ⱼ₎ = v
                := ⊥                otherwise

          - tᵢ[p₍ᵢ₎₍ⱼ₎/eⱼ] := tᵢ[v / eᵢ]               if p₍ᵢ₎₍ⱼ₎ = v
                         := tᵢ[n / eᵢ - N]           if p₍ᵢ₎₍ⱼ₎ = N + n ∧ Type(eᵢ) = Nat
                         := tᵢ[n / Int.toNat eᵢ]     if p₍ᵢ₎₍ⱼ₎ = Int.ofNat n ∧ Type(eᵢ) = Int
                         := tᵢ[n / Int.toNat eᵢ - N] if p₍ᵢ₎₍ⱼ₎ = Int.ofNat (N + n) ∧ Type(eᵢ) = Int
                         := tᵢ[n / (Int.toNat (Int.neg eᵢ)) - N] if p₍ᵢ₎₍ⱼ₎ = Int.Neg (Int.ofNat (N + n)) ∧ Type(eᵢ) = Int
                         := tᵢ                       otherwise

    NOTE: This function corresponds the accumulator `rewriter` function to be used with `matchExprRewriter`, such that:
     - normMatchExpr 0 [e₁, ..., eₙ] [p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎] tₘ none := some (tₘ[p₍ₘ₎₍₁₎/e₁] ... [p₍ₘ₎₍ₙ₎/eₙ])
     - normMatchExpr 1 [e₁, ..., eₙ] [p₍ₘ₋₁₎₍₁₎, ..., p₍ₘ₋₁₎₍ₙ₎] tₘ (some rewrite₀) :=
          some (if if eq₍ₘ₋₁₎₍₁₎ ∧ ... ∧ eq₍ₘ₋₁₎₍ₙ₎ then tₘ₋₁[p₍ₘ₋₁₎₍₁₎/e₁] ... [ p₍ₘ₋₁₎₍ₙ₎/eₙ] else rewrite₀)
     ...
     - normMatchExpr (m-1) [e₁, ..., eₙ] [p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎] t₁ (some rewriteₘ₋₂) :=
         some (if eq₍₁₎₍₁₎ ∧ ... ∧ eq₍₁₎₍ₙ₎ then t₁[p₍₁₎₍₁₎/e₁] ... [p₍₁₎₍ₙ₎/eₙ] else rewriteₘ₋₂)

-/
def normMatchExpr? (idx : Nat) (discrs : Array Expr) (lhs : Array Expr) (alt : Expr) (acc : Option Expr) : TranslateEnvT (Option Expr) := do
  let patternArgs ← retrieveAltsArgs lhs
  if (← isItePattern discrs patternArgs lhs)
  then
    let rhs ← betaReduceAlt alt (← substituteArgs discrs lhs patternArgs)
    if idx == 0 -- last pattern
    then return (some rhs) -- last pattern
    else
      let some elseExpr := acc | return acc
      let condExpr ← mkEqAndExpr discrs lhs
      -- we don't want to cache the decidable constraint as condExpr is not optimized at this stage
      -- return none if decidable instance cannot be synthesized.
      let some decideExpr ← trySynthDecidableInstance? condExpr (cacheDecidableCst := false) | return none
      return (mkApp5 (← mkIteOp) (← inferType rhs) condExpr decideExpr rhs elseExpr)
  else return none

 where

   /-- Return `true` only when the "match" normalization condition is satisfied, i.e,:
        - ∀ i ∈ [1..m], ∀ j ∈ [1..n], ( NoFreeVar(p₍ᵢ₎₍ⱼ₎) ∨ p₍ᵢ₎₍ⱼ₎ = v ∨ Type(eⱼ) ∈ {Nat, Int} )
       NOTE: condition `∃ [ Decidable (eⱼ = p₍ᵢ₎₍ⱼ₎)] ∈ DecidableInstances` is enforced when
       generating the ite expression.
   -/
   isItePattern (discrs : Array Expr) (patternArgs : Array Expr) (lhs : Array Expr) : TranslateEnvT Bool := do
     if patternArgs.size == 0
     then return true
     else
       let mut fvarCnt := 0
       for i in [:lhs.size] do
        let p := lhs[i]!
        let e := discrs[i]!
        let eType ← inferType e
        if (← (pure p.isFVar) <||>
              (pure ((isNatValue? p).isNone && isNatType eType)) <||>
              (pure ((isIntValue? p).isNone && isIntType eType))
           )
        then fvarCnt := fvarCnt + 1
       return (patternArgs.size == fvarCnt)

   /-- Given a sequence of match discriminators `[e₁, ..., eₙ]` and a sequence of match patterns `[p₁, ..., pₙ]`,
       return conjunction `True ∧ eq₁ ∧ ... ∧ eqₙ`, such that:
        - ∀ i ∈ [1..n]
          - eqᵢ := eᵢ = pᵢ           if (pᵢ ≠ v ∧ Type(eᵢ) ∉ {Nat, Int}) ∨ isIntNatCst(pᵢ)
                := N ≤ eᵢ           if pᵢ = N + n ∧ Type(eᵢ) = Nat
                := Int.ofNat 0 ≤ eᵢ if pᵢ = Int.ofNat n
                := Int.ofNat N ≤ eᵢ if pᵢ = Int.ofNat (N + n)
                := e ≤ -N           if pᵢ = Int.neg (Int.ofNat (N + n))
                := True             if pᵢ = v
                := ⊥                otherwise
   -/
   mkEqAndExpr (discrs : Array Expr) (lhs : Array Expr) : TranslateEnvT Expr := do
     let mut andEq ← mkPropTrue
     let eqOp ← mkEqOp
     let andOp ← mkPropAndOp
     for i in [:lhs.size] do
       let p := lhs[i]!
       let e := discrs[i]!
       let eType ← inferType e
       if (← (pure (!p.isFVar && !(isNatType eType) && !(isIntType eType))) <||>
             (pure (isNatValue? p).isSome) <||>
             (pure (isIntValue? p).isSome) )
       then
         -- case: (pᵢ ≠ v ∧ Type(eᵢ) ∉ {Nat, Int}) ∨ isIntNatCst(pᵢ)
         let eqExpr := mkApp3 eqOp eType p e
         andEq := mkApp2 andOp andEq eqExpr
       else match p with
            | (Expr.app (Expr.app (Expr.const ``Nat.add _) n@(Expr.lit (Literal.natVal _))) (Expr.fvar _)) =>
                -- case: pᵢ = N + n ∧ Type(eᵢ) = Nat
                let leExpr := mkApp2 (← mkNatLeOp) n e
                andEq := mkApp2 andOp andEq leExpr
            | (Expr.app (Expr.const ``Int.ofNat _) (Expr.fvar _)) =>
                -- case: pᵢ = Int.ofNat n
                let leExpr := mkApp2 (← mkIntLeOp) (← mkIntLitExpr (Int.ofNat 0)) e
                andEq := mkApp2 andOp andEq leExpr
            | (Expr.app (Expr.const ``Int.ofNat _)
               (Expr.app (Expr.app (Expr.const ``Nat.add _) n@(Expr.lit (Literal.natVal _))) (Expr.fvar _))) =>
               -- case pᵢ = Int.ofNat (N + n)
                let leExpr := mkApp2 (← mkIntLeOp) (mkApp (← mkIntOfNat) n) e
                andEq := mkApp2 andOp andEq leExpr
            | (Expr.app (Expr.const ``Int.neg _)
               (Expr.app (Expr.const ``Int.ofNat _)
                (Expr.app (Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n))) (Expr.fvar _)))) =>
               -- case pᵢ = pᵢ = Int.Neg (Int.ofNat (N + n))
               let leExpr := mkApp2 (← mkIntLeOp) e (← mkNatNegExpr n)
               andEq := mkApp2 andOp andEq leExpr
            | Expr.fvar _ => pure ()  -- case: pᵢ = v
            |_  => throwError "mkEqAndExpr: unexpected pattern {reprStr p}"
     return andEq

   /-- Given a sequence of match discriminators `[e₁, ..., eₙ]`, a sequence of match patterns `[p₁, ..., pₙ]`, and
       a sequence of free variables `[v₁, ..., vₘ]` obtained from function `retrieveAltsArgs`, apply the following
       substituion: on [v₁, ..., vₘ] only when m > 0:
          ∀ i ∈ [1..n],
           let j := NbFeeVars(p₁) + ... + NbFeeVars(pᵢ)
          - [vⱼ / eⱼ]                           if pᵢ = vⱼ ∧ j ≤ m
            [vⱼ / eᵢ - N]                       if pᵢ = N + n ∧ Type(vⱼ) = Type(eᵢ) = Nat ∧ j ≤ m
            [vⱼ / Int.toNat eᵢ]                 if pᵢ = Int.ofNat n ∧ n = vⱼ ∧ j ≤ m
            [vⱼ / Int.toNat eᵢ - N]             if pᵢ = Int.ofNat (N + n) ∧ n = vⱼ ∧ j ≤ m
            [vⱼ / (Int.toNat (Int.neg eᵢ)) - N] if pᵢ = Int.Neg (Int.ofNat (N + n)) ∧ n = vⱼ ∧ j ≤ m
            ⊥                                  otherwise

       An error is triggered if the sequence of match patterns and free variables are not consistent.
   -/
   substituteArgs (discrs : Array Expr) (lhs : Array Expr) (patternArgs : Array Expr) : TranslateEnvT (Array Expr) := do
    if patternArgs.size == 0
    then return patternArgs
    else
      let mut idx := 0
      let mut args := patternArgs
      for i in [:lhs.size] do
        let p := lhs[i]!
        let e := discrs[i]!
        match p with
        | Expr.fvar .. =>
            -- case: pᵢ = vⱼ ∧ j ≤ m
            if args[idx]! != p then
              throwError "substituteArgs: Invalid match pattern arguments (lhs: {reprStr lhs}, args: {reprStr args})"
            args := args.set! idx e
            idx := idx + 1
        | (Expr.app (Expr.app (Expr.const ``Nat.add _) n@(Expr.lit (Literal.natVal _))) n_fv@(Expr.fvar _)) =>
            -- case: pᵢ = N + n ∧ Type(vⱼ) = Type(eᵢ) = Nat ∧ j ≤ m
            if n_fv != args[idx]! then
              throwError "substituteArgs: Invalid match pattern arguments (lhs: {reprStr lhs}, args: {reprStr args})"
            args := args.set! idx (mkApp2 (← mkNatSubOp) e n)
            idx := idx + 1
        | (Expr.app (Expr.const ``Int.ofNat _) (Expr.fvar _)) =>
            -- case: pᵢ = Int.ofNat n ∧ Type(vⱼ) = Nat ∧ j ≤ m
            if !(isNatType (← inferType args[idx]!)) then
              throwError "substituteArgs: Invalid match pattern arguments (lhs: {reprStr lhs}, args: {reprStr args})"
            args := args.set! idx (mkApp (← mkIntToNatOp) e)
            idx := idx + 1
        | (Expr.app (Expr.const ``Int.ofNat _)
             (Expr.app (Expr.app (Expr.const ``Nat.add _) n@(Expr.lit (Literal.natVal _))) n_fv@(Expr.fvar _))) =>
            -- case: pᵢ = Int.ofNat (N + n) ∧ Type(vⱼ) = Nat ∧ j ≤ m
            if n_fv != args[idx]! then
              throwError "substituteArgs: Invalid match pattern arguments (lhs: {reprStr lhs}, args: {reprStr args})"
            args := args.set! idx (mkApp2 (← mkNatSubOp) (mkApp (← mkIntToNatOp) e) n)
            idx := idx + 1
        | (Expr.app (Expr.const ``Int.neg _)
           (Expr.app (Expr.const ``Int.ofNat _)
            (Expr.app (Expr.app (Expr.const ``Nat.add _) n@(Expr.lit (Literal.natVal _))) n_fv@(Expr.fvar _)))) =>
            -- case: pᵢ = Int.Neg (Int.ofNat (N + n)) ∧ Type(vⱼ) = Nat ∧ j ≤ m
            if n_fv != args[idx]! then
              throwError "substituteArgs: Invalid match pattern arguments (lhs: {reprStr lhs}, args: {reprStr args})"
            args := args.set! idx (mkApp2 (← mkNatSubOp) (mkApp (← mkIntToNatOp) (mkApp (← mkIntNegOp) e)) n)
            idx := idx + 1
        | _ => pure () -- case : NbFreeVars(pᵢ) = 0
      return args


/-- Given a `match` application expression of the form
     `f.match.n [p₁, ..., pₙ, pa₍₁₎₍₁₎ → .. → pa₍₁₎₍ₖ₎ → rhs₁, ..., pa₍ₘ₎₍₁₎ → .. → pa₍ₘ₎₍ₖ₎ → rhsₘ]`,
    return `g.match.n q₁, ..., qₕ, pa₍₁₎₍₁₎ → .. → pa₍₁₎₍ₖ₎ → rhs₁, ..., pa₍ₘ₎₍₁₎ → .. → pa₍ₘ₎₍ₖ₎ → rhsₘ`
    if `Type(f.match.n [p₁, ..., pₙ]) := `g.match.n [q₁, ..., qₕ]` exists in match cache.
    Otherwise, perform the following:
      - Add `Type(f.match.n [p₁, ..., pₙ]) := `f.match.n [q₁, ..., qₕ]` in match cache
      - return `f.match.n [p₁, ..., pₙ, pa₍₁₎₍₁₎ → .. → pa₍₁₎₍ₖ₎ → rhs₁, ..., pa₍ₘ₎₍₁₎ → .. → pa₍ₘ₎₍ₖ₎ → rhsₘ]`
-/
def structEqMatch? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
 match f with
 | Expr.const n _ =>
    let some matcherInfo ← getMatcherInfo? n | return none
    -- let cInfo ← getConstInfo n
    -- let matchFun ← instantiateValueLevelParams cInfo dlevel
    let auxApp := mkAppN f args[0 : matcherInfo.getFirstDiscrPos]
    let auxAppType ← inferType auxApp
    let env ← get
    match env.matchCache.find? auxAppType with
    | some gmatch =>
       let altArgs := args[matcherInfo.getFirstDiscrPos : args.size]
       some <$> mkAppExpr gmatch altArgs
    | none =>
       set {env with matchCache := env.matchCache.insert auxAppType auxApp}
       some <$> mkAppExpr f args
 | _ => pure none

end Solver.Optimize
