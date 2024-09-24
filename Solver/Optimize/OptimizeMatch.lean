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
    if args.size = 0, `alt` is expected to have only a single Unit argument, i.e.,
    ```
     alt = fun (_ : Unit) => e
    ```
    In this case `e` is returned as result. Otherwise, an error is triggered.
-/
def betaReduceAlt (alt : Expr) (args : Array Expr) : MetaM Expr := do
  if args.size == 0
  then if alt.getNumHeadLambdas == 1
       then match alt with
            | Expr.lam _n (Expr.const ``Unit _) e _bi => return e
            | _ => throwError "betaReduceAlt: lambda expression expected but got {reprStr alt}"
       else throwError "betaReduceAlt: only unit argument expected but got {reprStr alt}"
  else return (Expr.beta alt args)


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


end Solver.Optimize
