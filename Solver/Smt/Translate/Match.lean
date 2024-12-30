import Lean
import Solver.Optimize.Basic
import Solver.Smt.Env
import Solver.Smt.Translate.Quantifier


open Lean Meta Solver.Optimize

namespace Solver.Smt

structure MatchResult where
  /-- Translated match discriminators -/
  discrTerms : Array SmtTerm
  /-- Ite term generated when translating each match pattern -/
  iteTerm : Option SmtTerm

structure AltsArgsResult where
  /-- Sequence of named pattern and free variables appearing in each match pattern.
      The order of appearance for named pattern and free variables are preserved.
  -/
  patternFreeVars : Array Expr
  /-- Sequence of named pattern equation appearing in each match pattern.
      The order of appearance is preserved. This sequence is appended to patternFreeVars
      is reset once a pattern match for a specific match descriminator has been considered.
  -/
  namedPatternEqs : Array Expr
deriving Inhabited

abbrev AltsArgsEnv := StateRefT AltsArgsResult TranslateEnvT

/-- Adds `fv` to `patternFreeVars` -/
def updatePatternVars (fv : Expr) : AltsArgsEnv Unit := do
 let env ← get
 set {env with patternFreeVars := env.patternFreeVars.push fv}


/-- Adds `peq` to `namedPatternEq` -/
def updatePatternEqs (peq : Expr) : AltsArgsEnv Unit := do
 let env ← get
 set {env with namedPatternEqs := env.namedPatternEqs.push peq}

/-- Performs the following actions:
      - Append patternFreeVars with namedPatternEqs
      - Reset namedPatternEqs (i.e., set to empty Array)
-/
def flushPatternEqs : AltsArgsEnv Unit := do
  let env ← get
  set {env with patternFreeVars := env.patternFreeVars ++ env.namedPatternEqs,
                namedPatternEqs := .empty }

/-- Given a sequence of match pattern `p₁, ..., pₙ` such that each pᵢ may contain named patterns of the form:
      (namedPattern t₍₁₎₍₁₎ l₍₁₎₍₁₎ (.. (namedPattern t₍₁₎₍ₖ₋₁₎ l₍₁₎₍ₖ₋₁₎ (namedPattern t₍₁₎₍ₖ₎ l₍₁₎₍ₖ₎ e₍₁₎₍ₖ₎ h₍₁₎₍ₖ₎) h₍₁₎₍ₖ₋₁₎) h₍₁₎₍₂₎) h₍₁₎₍₁₎), ...,
      (namedPattern t₍ₙ₎₍₁₎ l₍ₙ₎₍₁₎ (.. (namedPattern t₍ₙ₎₍ₖ₋₁₎ l₍ₙ₎₍ₖ₋₁₎ (namedPattern t₍ₙ₎₍ₖ₎ l₍ₙ₎₍ₖ₎ e₍ₙ₎₍ₖ₎ h₍ₙ₎₍ₖ₎) h₍ₙ₎₍ₖ₋₁₎) h₍ₙ₎₍₂₎) h₍ₙ₎₍₁₎)
    with
     ∀ i ∈ [1..n], ∀ j ∈ [1..k]
      - t₍ᵢ₎₍ⱼ₎: corresponding to sort type of the named pattern.
      - l₍ᵢ₎₍ⱼ₎: corresponding to the label of the named pattern.
      - e₍ᵢ₎₍ⱼ₎: corresponding to the expression of the named pattern that may contain free variables `v₍ᵢ₎₍ⱼ₎₍₁₎, ..., v₍ᵢ₎₍ⱼ₎₍ₘ₎`.
      - h₍ᵢ₎₍ⱼ₎: corresponding to the equality equation of the named pattern.
    return the following sequence of free variables
      #[l₍₁₎₍₁₎, v₍₁₎₍₁₎₍₁₎, ..., v₍₁₎₍₁₎₍ₘ₎, l₍₁₎₍₂₎, v₍₁₎₍₂₎₍₁₎, ..., v₍₁₎₍₂₎₍ₘ₎, ...,
        l₍₁₎₍ₖ₎, v₍₁₎₍ₖ₎₍₁₎, ..., v₍₁₎₍ₖ₎₍ₘ₎, h₍₁₎₍₁₎, ..., h₍₁₎₍ₖ₎, ...,
        l₍ₙ₎₍₁₎, v₍ₙ₎₍₁₎₍₁₎, ..., v₍ₙ₎₍₁₎₍ₘ₎, l₍ₙ₎₍₂₎, v₍ₙ₎₍₂₎₍₁₎, ..., v₍ₙ₎₍₂₎₍ₘ₎, ...,
        l₍ₙ₎₍ₖ₎, v₍ₙ₎₍ₖ₎₍₁₎, ..., v₍ₙ₎₍ₖ₎₍ₘ₎, h₍ₙ₎₍₁₎, ..., h₍ₙ₎₍ₖ₎]

    Trigger an error if at least one `pᵢ` does not correspond to:
      - A nullary constructor;
      - A String/Nat literal;
      - A constructor/function application; or
      - A named pattern; or
      - A free variable.
-/
partial def retrieveAltsArgs (lhs : Array Expr) : TranslateEnvT (Array Expr) := do
 let rec visit (e : Expr) : AltsArgsEnv Unit := do
   match e with
   | Expr.const .. | Expr.lit .. => return ()
   | Expr.fvar .. => updatePatternVars e
   | Expr.app .. =>
      Expr.withApp e fun f as => do
       match f with
       | Expr.const n _ =>
          match (← getConstInfo n) with
          | ConstantInfo.ctorInfo info =>
              -- constructor application
              let ctorArgs := as[info.numParams:as.size]
              for i in [:ctorArgs.size] do visit ctorArgs[i]!
          | _ =>
             if n == ``namedPattern then
               -- add named pattern label to pattern vars list
               updatePatternVars as[1]!
               -- add named pattern equation to equation list
               updatePatternEqs as[3]!
               visit as[2]!
             else
               for i in [:as.size] do visit as[i]!
       | _ => throwEnvError f!"retrieveAltsArgs: const expression expected but got {reprStr f}"
   | _ => throwEnvError f!"retrieveAltsArgs: unexpected pattern expression: {reprStr e}"
 let loop : AltsArgsEnv Unit :=
   for i in [:lhs.size] do
     visit lhs[i]!
     flushPatternEqs
 let (_, res) ← loop|>.run default
 return res.patternFreeVars


/-- Return `true` is p is a nat, integer or string literal expression. -/
private def isCstLiteral (p : Expr) : Bool :=
  (isNatValue? p).isSome || (isIntValue? p).isSome || (isStrValue? p).isSome

/-- Return `some (C, #[xₖ, ..., xₙ])` when p := `C x₁ ... xₙ` such that:
     - C is a ctor name.
     - x₁ ... xₖ₋₁ correspond to the polymorphic parameters of the corresponding inductive datatype.
-/
private def isCtorPattern (p : Expr) : TranslateEnvT (Option (Name × Array Expr)) := do
 match p.getAppFn' with
 | Expr.const n _ =>
     match (← getConstInfo n) with
     | ConstantInfo.ctorInfo info =>
         let args := p.getAppArgs
         return (n, args[info.numParams:args.size].toArray)
     | _ => return none
 | _ => return none


mutual
/-- Generate the necessary let expressions when translating a `match` to an smt if-then-else, such that:
    given `se` a match discriminator that has already been translated to an smt term,
    `p` its corresponding match expression and `rhs` the match right-hand side expression,
    `mkLet se p rhs` is defined as follows:
     := (let ((sfv se)) t)     if p = fv with sfv = fvarIdtoSmtSymbol fv
     := t                      if p = C (i.e., nullary constructor)
     := t                      if isIntNatStrCst(p)

     := (let ((sn se)) (mkLet sn' e t))
            if p = namedPattern t n e h` with sn = fvarIdtoSmtSymbol n ∧ sn' = smtSimpleVarId sn

     := (let ((sn (- se N))) t)  if p = N + n ∧ Type(N) = Nat with sn = fvarIdtoSmtSymbol n

     := (let ((sn (- se N))) (mkLet sn' e t))
             if p = N + (namedPattern t n e h) ∧ Type(N) = Nat with sn = fvarIdtoSmtSymbol n ∧ sn' = smtSimpleVarId sn
     := (let ((sn se)) t)       if p = Int.ofNat n with sn = fvarIdtoSmtSymbol n

     := (let ((sn se)) (mkLet sn' e t))
             if p = Int.ofNat (namedPattern t n e t) with sn = fvarIdtoSmtSymbol n ∧ sn' = smtSimpleVarId sn

     := (let ((sn (- se N))) t)  if p = Int.ofNat (N + n) with sn = fvarIdtoSmtSymbol n

     := (let ((sn (- se N))) (mkLet sn' e t))
             if p = Int.ofNat (N + namedPattern t n e h) with sn = fvarIdtoSmtSymbol n ∧ sn' = smtSimpleVarId sn

     := (let ((sn (- (+ se N)))) t) if p' = Int.Neg (Int.ofNat (N + n)) with sn = fvarIdtoSmtSymbol n

     := (let ((sn (- (+ se N)))) (mkLet sn' e t))
             if p' = Int.Neg (Int.ofNat (N + namedPattern t n e h)) with sn = fvarIdtoSmtSymbol n ∧ sn' = smtSimpleVarId sn

     := (mkLet (C.1 se) x₁ {.. (mkLet (C.k-1 se) xₖ₋₁ (mkLet (C.k se) xₙ t)))) if p' = C x₁ ... xₖ

     := ⊥                                  otherwise

-/
private partial def mkLet
  (se : SmtTerm) (p : Expr) (rhs : SmtTerm)
  (k : SmtTerm → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
  if isCstLiteral p then return (← k rhs) -- case: isIntNatStrCst(p)
  match p with
  | Expr.fvar fv =>
      -- case: p = fv with sfv = fvarIdtoSmtSymbol fv
      k (mkLetTerm #[(← fvarIdToSmtSymbol fv, se)] rhs)

  | Expr.const _ _ =>
      -- case: p = C (i.e., nullary constructor)
      k rhs

  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) (Expr.fvar fv)) e) _h =>
      -- case: p := namedPattern t n e h` with sn = fvarIdtoSmtSymbol n
      -- case: p = Int.ofNat (namedPattern t n e t) with sn = fvarIdtoSmtSymbol n
      let sn ← fvarIdToSmtSymbol fv
      mkLet (smtSimpleVarId sn) e rhs
        fun rhs'=> k (mkLetTerm #[(sn, se)] rhs')

  | Expr.app (Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n))) a
  | Expr.app (Expr.const ``Int.ofNat _)
      (Expr.app (Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n))) a) =>
      match a with
      | Expr.fvar fv =>
          -- case: p = N + n ∧ Type(N) = Nat with sn = fvarIdtoSmtSymbol n; or
          -- case: p = Int.ofNat (N + n) with sn = fvarIdtoSmtSymbol n
          k (mkLetTerm #[(← fvarIdToSmtSymbol fv, (subSmt se (natLitSmt n)))] rhs)

      | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) (Expr.fvar fv)) e) _h =>
          -- case: if p = N + (namedPattern t n e h) ∧ Type(N) = Nat with sn = fvarIdtoSmtSymbol n
          -- case: if p = Int.ofNat (N + namedPattern t n e h) with sn = fvarIdtoSmtSymbol n
          let sn ← fvarIdToSmtSymbol fv
          mkLet (smtSimpleVarId sn) e rhs
            fun rhs' => k (mkLetTerm #[(sn, (subSmt se (natLitSmt n)))] rhs')

      | _ => throwEnvError f!"mkLet: unexpected pattern expression: {reprStr p}"

  | Expr.app (Expr.const ``Int.ofNat _) a =>
       match a with
       | Expr.fvar fv =>
            -- case:  p = Int.ofNat n with sn = fvarIdtoSmtSymbol n
            k (mkLetTerm #[(← fvarIdToSmtSymbol fv, se)] rhs)

       | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) (Expr.fvar fv)) e) _h =>
            -- case: p = Int.ofNat (namedPattern t n e t) with sn = fvarIdtoSmtSymbol n
            let sn ← fvarIdToSmtSymbol fv
            mkLet (smtSimpleVarId sn) e rhs
              fun rhs'=> k (mkLetTerm #[(sn, se)] rhs')

       | _ => throwEnvError f!"mkLet: unexpected pattern expression: {reprStr p}"

  | Expr.app (Expr.const ``Int.neg _)
      (Expr.app (Expr.const ``Int.ofNat _)
        (Expr.app (Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n))) a)) =>
      match a with
      | Expr.fvar fv =>
           -- case: p' = Int.Neg (Int.ofNat (N + n)) with sn = fvarIdtoSmtSymbol n
           k (mkLetTerm #[(← fvarIdToSmtSymbol fv, negSmt (addSmt se (natLitSmt n)))] rhs)
      | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) (Expr.fvar fv)) e) _h =>
           -- case: p' = Int.Neg (Int.ofNat (N + namedPattern t n e h)) with sn = fvarIdtoSmtSymbol n
           let sn ← fvarIdToSmtSymbol fv
           mkLet (smtSimpleVarId sn) e rhs
             fun rhs' => k (mkLetTerm #[(sn, negSmt (addSmt se (natLitSmt n)))] rhs')
      | _ => throwEnvError f!"mkLet: unexpected pattern expression: {reprStr p}"

  | _ =>
     let some (n, args) ← isCtorPattern p
       | throwEnvError f!"mkLet: unexpected pattern expression: {reprStr p}"
     if args.size == 0 then
       -- case: p = C (i.e., nullary constructor for polymorphic type, e.g., Option.none)
       k rhs
     else
       -- case: p' = C x₁ ... xₖ
       mkLetCtors n (args.size - 1) args se rhs k

private partial def mkLetCtors
  (c : Name) (idx : Nat) (args : Array Expr) (se : SmtTerm) (rhs : SmtTerm)
  (k : SmtTerm → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
  let selectorTerm := mkSimpleSmtAppN (mkCtorSelectorSymbol c (idx+1)) #[se]
  if idx == 0 then
    mkLet selectorTerm args[idx]! rhs k
  else
    mkLet selectorTerm args[idx]! rhs
      fun rhs' => mkLetCtors c (idx - 1) args se rhs' k
end


/-- Remove all namedPattern expression in `p` and apply optimization whenever necessary. -/
partial def removeNamedPatternExpr (p : Expr) : TranslateEnvT Expr :=
 match p with
 | Expr.const .. | Expr.lit .. | Expr.fvar .. => return p
 | Expr.app .. =>
      Expr.withApp p fun f as => do
        match f with
        | Expr.const n _ =>
           if n == ``namedPattern then
             removeNamedPatternExpr as[2]!
           else
             let mut margs := as
             for i in [:as.size] do
               margs ← margs.modifyM i removeNamedPatternExpr
             optimizeExpr (mkAppN f margs)
        | _ => throwEnvError f!"removeNamedPatternExpr: const expression expected but got {reprStr f}"
 | _ => throwEnvError f!"removeNamedPatternExpr: unexpected pattern expression: {reprStr p}"


/-- Generate the necessary ite condition expressions when translating a `match` to an smt if-then-else, such that:
    given `se` a match discriminator that has already been translated to an smt term, `pp` its
    corresponding match expression, `mkCond se pp` is defined as follows:
     let p' ← removeNamedPatternExpr pp;
      := ( = se sp )    if isIntNatStrCst(p') with sp := termTranslator p'
      := (<= N se )     if p' = N + n ∧ Type(N) = Nat
      := (<= 0 se )     if p' = Int.ofNat n
      := (<= N se )     if p' = Int.ofNat (N + n)
      := (<= se (- N))  if p' = Int.Neg (Int.ofNat (N + n))
      := (is-C se)      if p' = C (i.e., nullary constructor)
      := (and (is-C se) (and (mkCond (C.1 se) x₁) (... (and (mkCond (C.k-1 se) xₖ₋₁) (mkCond (C.k se) xₖ)))))
                        if p' = C x₁ ... xₖ
      := True           if p' = fv
      := ⊥              otherwise
-/
private partial def mkCond
  (se : SmtTerm) (pp : Expr) (andTerms : Array SmtTerm)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT (Array SmtTerm) := do
  let p' ← removeNamedPatternExpr pp
  if isCstLiteral p' then
    -- case: isIntNatStrCst(p')
    return (andTerms.push (eqSmt (← termTranslator p') se))
  match p' with
  | Expr.fvar _ => return andTerms -- case: p' = fv
  | Expr.const c _ =>
      -- case: if p' = C (i.e., nullary constructor)
      if !(← isCtorName c) then
        throwEnvError f!"mkCond: nullary ctor expected but got {reprStr p'}"
      return (andTerms.push (mkCtorTestorTerm c se))
  | Expr.app (Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n))) (Expr.fvar _fv)
  | Expr.app (Expr.const ``Int.ofNat _)
     (Expr.app (Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n))) (Expr.fvar _fv)) =>
      -- case: p' = N + n ∧ Type(N) = Nat
      -- case: p' = Int.ofNat (N + n)
      return (andTerms.push (leqSmt (natLitSmt n) se))
  | Expr.app (Expr.const ``Int.ofNat _) (Expr.fvar _fv) =>
      -- case: p' = Int.ofNat n
      return (andTerms.push (leqSmt (natLitSmt 0) se))
  | Expr.app (Expr.const ``Int.neg _)
    (Expr.app (Expr.const ``Int.ofNat _)
    (Expr.app (Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n))) (Expr.fvar _fv))) =>
      -- case: p' = Int.Neg (Int.ofNat (N + n))
      return (andTerms.push (leqSmt se (negSmt (natLitSmt n))))
  | _ =>
     let some (n, args) ← isCtorPattern p'
       | throwEnvError f!"mkCond: unexpected pattern expression: {reprStr p'}"
     -- case: p' = C x₁ ... xₖ
     let mut mand := andTerms.push (mkCtorTestorTerm n se)
     for i in [:args.size] do
       let selectorTerm := mkSimpleSmtAppN (mkCtorSelectorSymbol n (i+1)) #[se]
       mand ← mkCond selectorTerm args[i]! mand termTranslator
     return mand

/-- Is the accumulator `rewriter` function to be used with `matchExprRewriter`
    when translating a `match` expression to an smt if-then-else.
-/
def translateMatchAux?
  (termTranslator : Expr → TranslateEnvT SmtTerm)
  (idx : Nat) (discrs : Array Expr) (lhs : Array Expr)
  (alt : Expr) (acc : Option MatchResult) : TranslateEnvT (Option MatchResult) := do
  let altArgs ← retrieveAltsArgs lhs
  let rhs := betaReduceRhs alt altArgs
  let hvars ← altArgs.foldlM insertFVars .empty
  if idx == 0 then -- last pattern translated first
    -- translate all discriminators and keep in MatchResult
    let mut discrTerms := #[]
    for i in [:discrs.size] do
      discrTerms := discrTerms.push (← termTranslator discrs[i]!)
    let srhs ← withTranslatePattern hvars $ mkRhs discrTerms lhs rhs
    return some { discrTerms, iteTerm := some srhs }
  else
    let some mres := acc
      | throwEnvError "translateMatchAux?: match result expected"
    withTranslatePattern hvars $ mkIte lhs rhs mres

  where
    betaReduceRhs (alt : Expr) (altArgs : Array Expr) : Expr :=
     if altArgs.size == 0 -- case when there is no free variables in match pattern
     then getLambdaBody alt
     else Expr.beta alt altArgs

    insertFVars (h : HashSet FVarId) (v : Expr) : TranslateEnvT (HashSet FVarId) := do
      match v with
      | Expr.fvar fv =>
          match (← fv.getType).getAppFn' with
          | Expr.const ``Eq _ => return h
          | _ => return h.insert fv
      | _ => return h

    mkRhs (discrTerms : Array SmtTerm) (lhs : Array Expr) (rhs : Expr) : TranslateEnvT SmtTerm := do
      let mut srhs ← termTranslator rhs
      let nbPatterns := lhs.size
      for i in [:nbPatterns] do
        let idx := nbPatterns - i - 1
        srhs ← mkLet discrTerms[idx]! lhs[idx]! srhs (λ x => return x)
      return srhs

    mkIte (lhs : Array Expr) (rhs : Expr) (mres : MatchResult) : TranslateEnvT (Option MatchResult) := do
      let some elseTerm := mres.iteTerm
        | throwEnvError "mkIte: else term expected"
      let thenTerm ← mkRhs mres.discrTerms lhs rhs
      let mut andTerms := (#[] : Array SmtTerm)
      for i in [:lhs.size] do
        andTerms ← mkCond mres.discrTerms[i]! lhs[i]! andTerms termTranslator
      let nbCond := andTerms.size
      if nbCond == 0 then return some {mres with iteTerm := some thenTerm} -- case when else unreachable
      let mut condTerm := andTerms[nbCond-1]!
      for i in [1:nbCond] do
        let idx := nbCond - i - 1
        condTerm := andSmt andTerms[idx]! condTerm
      return some {mres with iteTerm := some (iteSmt condTerm thenTerm elseTerm)}


/-- Translate a `match` expression to an smt if-then-else term s.t.:
      match e₁, ..., eₙ with
      | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
      ...
      | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ
     ===>
       if (mkCond se₁ p₍₁₎₍₁₎) ∧ ... ∧ (mkCond seₙ p₍₁₎₍ₙ₎) then (mkRhs [se₁ ... seₙ] [p₍₁₎₍₁₎ ... p₍₁₎₍ₙ₎] t₁)
       else if (mkCond se₁ p₍₂₎₍₁₎) ∧ ... ∧ (mkCond seₙ p₍₂₎₍ₙ₎) then (mkRhs [se₁ ... seₙ] [p₍₂₎₍₁₎ ... p₍₂₎₍ₙ₎] t₂)
       ...
       else (mkRhs [se₁ ... seₙ] [p₍ₘ₎₍₁₎ ... p₍ₘ₎₍ₙ₎] tₘ)

     with:
       - ∀ i ∈ [1..n], seᵢ := termTranslator e
       - mkCond se p :
          let p' ← removeNamedPatternExpr p;
           := ( = se sp )    if isIntNatStrCst(p') with sp := termTranslator p'
           := (<= N se )     if p' = N + n ∧ Type(N) = Nat
           := (<= 0 se )     if p' = Int.ofNat n
           := (<= N se )     if p' = Int.ofNat (N + n)
           := (<= se (- N))  if p' = Int.Neg (Int.ofNat (N + n))
           := (is-C se)      if p' = C (i.e., nullary constructor)
           := (and (is-C se) (and (mkCond (C.1 se) x₁) (... (and (mkCond (C.k-1 se) xₖ₋₁) (mkCond (C.k se) xₖ)))))
                             if p' = C x₁ ... xₖ
           := True           if p' = fv
           := ⊥              otherwise

       - getPattern(p) := e      if p := `namedPattern` t n e h`
                       := p      otherwise

       - mkRhs [se₁ ... seₙ] [p₁ ... pₙ] t :
           let st := termTranslator t
           := (mkLet se₁ p₁ ( ... (mkLet seₙ₋₁ pₙ₋₁ (mkLet seₙ pₙ st))))

       - mkLet se p t :
           := (let ((sfv se)) t)     if p = fv with sfv = fvarIdtoSmtSymbol fv
           := t                      if p = C (i.e., nullary constructor)
           := t                      if isIntNatStrCst(p)

           := (let ((sn se)) (mkLet sn' e t))
                  if p = namedPattern t n e h` with sn = fvarIdtoSmtSymbol n ∧ sn' = smtSimpleVarId sn

           := (let ((sn (- se N))) t)  if p = N + n ∧ Type(N) = Nat with sn = fvarIdtoSmtSymbol n

           := (let ((sn (- se N))) (mkLet sn' e t))
                   if p = N + (namedPattern t n e h) ∧ Type(N) = Nat with sn = fvarIdtoSmtSymbol n ∧ sn' = smtSimpleVarId sn
           := (let ((sn se)) t)       if p = Int.ofNat n with sn = fvarIdtoSmtSymbol n

           := (let ((sn se)) (mkLet sn' e t))
                   if p = Int.ofNat (namedPattern t n e t) with sn = fvarIdtoSmtSymbol n ∧ sn' = smtSimpleVarId sn

           := (let ((sn (- se N))) t)  if p = Int.ofNat (N + n) with sn = fvarIdtoSmtSymbol n

           := (let ((sn (- se N))) (mkLet sn' e t))
                   if p = Int.ofNat (N + namedPattern t n e h) with sn = fvarIdtoSmtSymbol n ∧ sn' = smtSimpleVarId sn

           := (let ((sn (- (+ se N)))) t) if p' = Int.Neg (Int.ofNat (N + n)) with sn = fvarIdtoSmtSymbol n

           := (let ((sn (- (+ se N)))) (mkLet sn' e t))
                   if p' = Int.Neg (Int.ofNat (N + namedPattern t n e h)) with sn = fvarIdtoSmtSymbol n ∧ sn' = smtSimpleVarId sn

           := (mkLet (C.1 se) x₁ (.. (mkLet (C.k-1 se) xₖ₋₁ (mkLet (C.k se) xₙ t)))) if p' = C x₁ ... xₖ

           := ⊥                                  otherwise

    Note that we here expect the optimization phase must reach match expression whenever
    at least one eᵢ is a constant/ctor.
-/
def translateMatch?
  (f : Expr) (args : Array Expr) (optimizer : Expr → TranslateEnvT Expr)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT (Option SmtTerm) := do
  let res ← withKeepNamedPattern $ matchExprRewriter f args optimizer (translateMatchAux? termTranslator)
  match res with
  | some r => return r.iteTerm
  | _ => return none

end Solver.Smt
