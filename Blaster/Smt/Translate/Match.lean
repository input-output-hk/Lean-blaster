import Lean
import Blaster.Optimize.Basic
import Blaster.Smt.Env
import Blaster.Smt.Translate.Quantifier


open Lean Meta Blaster.Optimize

namespace Blaster.Smt

structure MatchResult where
  /-- Translated match discriminators -/
  discrTerms : Array SmtTerm
  /-- Ite term generated when translating each match pattern -/
  iteTerm : Option SmtTerm

@[always_inline, inline]
def removeAndOptNamedPatternExpr (p : Expr) : TranslateEnvT Expr := do
 -- set start local context
  updateLocalContext (← mkLocalContext)
  withLocalContext $ do removeNamedPatternExpr p

mutual
/-- Generate the necessary let expressions when translating a `match` to an smt if-then-else, such that:
    given `se` a match discriminator that has already been translated to an smt term,
    `p` its corresponding match expression and `rhs` the match right-hand side expression,
    `mkLet se p rhs` is defined as follows:
     := (let ((sfv se)) rhs)     if p = fv with sfv = fvarIdToSmtSymbol fv
     := rhs                      if p = C (i.e., nullary constructor)
     := rhs                      if isIntNatStrCst(p)

     := (let ((sn se)) (mkLet sn' e rhs))
            if p = namedPattern t n e h` with sn = fvarIdToSmtSymbol n ∧ sn' = smtSimpleVarId sn

     := (let ((sn (- se N))) rhs)  if p = N + n ∧ Type(N) = Nat with sn = fvarIdToSmtSymbol n

     := (let ((sn (- se N))) (mkLet sn' e rhs))
             if p = N + (namedPattern t n e h) ∧ Type(N) = Nat with sn = fvarIdToSmtSymbol n ∧ sn' = smtSimpleVarId sn
     := (let ((sn se)) rhs)       if p = Int.ofNat n with sn = fvarIdToSmtSymbol n

     := (let ((sn se)) (mkLet sn' e rhs))
             if p = Int.ofNat (namedPattern t n e h) with sn = fvarIdToSmtSymbol n ∧ sn' = smtSimpleVarId sn

     := (let ((sn (- se N))) rhs)  if p = Int.ofNat (N + n) with sn = fvarIdToSmtSymbol n

     := (let ((sn (- se N))) (mkLet sn' e rhs))
             if p = Int.ofNat (N + namedPattern t n e h) with sn = fvarIdToSmtSymbol n ∧ sn' = smtSimpleVarId sn

     := (let ((sn (- (+ se N)))) rhs) if p' = Int.Neg (Int.ofNat (N + n)) with sn = fvarIdToSmtSymbol n

     := (let ((sn (- (+ se N)))) (mkLet sn' e rhs))
             if p' = Int.Neg (Int.ofNat (N + namedPattern t n e h)) with sn = fvarIdToSmtSymbol n ∧ sn' = smtSimpleVarId sn

     := (mkLet (C.1 se) x₁ {.. (mkLet (C.k-1 se) xₖ₋₁ (mkLet (C.k se) xₙ t)))) if p' = C x₁ ... xₖ

     := ⊥                                  otherwise

-/
private partial def mkLet
  (se : SmtTerm) (p : Expr) (rhs : SmtTerm)
  (k : SmtTerm → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
  if isCstLiteral p then return (← k rhs) -- case: isIntNatStrCst(p)
  match p with
  | Expr.fvar fv =>
      -- case: p = fv with sfv = fvarIdToSmtSymbol fv
      k (mkLetTerm #[(← fvarIdToSmtSymbol fv, se)] rhs)

  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) (Expr.fvar fv)) e) _h =>
      -- case: p := namedPattern t n e h` with sn = fvarIdToSmtSymbol n
      let sn ← fvarIdToSmtSymbol fv
      mkLet (smtSimpleVarId sn) e rhs
        fun rhs'=> k (mkLetTerm #[(sn, se)] rhs')

  | Expr.app (Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n))) a
  | Expr.app (Expr.const ``Int.ofNat _)
      (Expr.app (Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n))) a) =>
      match a with
      | Expr.fvar fv =>
          -- case: p = N + n ∧ Type(N) = Nat with sn = fvarIdToSmtSymbol n; or
          -- case: p = Int.ofNat (N + n) with sn = fvarIdToSmtSymbol n
          k (mkLetTerm #[(← fvarIdToSmtSymbol fv, (subSmt se (natLitSmt n)))] rhs)

      | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) (Expr.fvar fv)) e) _h =>
          -- case: if p = N + (namedPattern t n e h) ∧ Type(N) = Nat with sn = fvarIdToSmtSymbol n
          -- case: if p = Int.ofNat (N + namedPattern t n e h) with sn = fvarIdToSmtSymbol n
          let sn ← fvarIdToSmtSymbol fv
          mkLet (smtSimpleVarId sn) e rhs
            fun rhs' => k (mkLetTerm #[(sn, (subSmt se (natLitSmt n)))] rhs')

      | _ => throwEnvError "mkLet: unexpected pattern expression: {reprStr p}"

  | Expr.app (Expr.const ``Int.ofNat _) a =>
       match a with
       | Expr.fvar fv =>
            -- case:  p = Int.ofNat n with sn = fvarIdToSmtSymbol n
            k (mkLetTerm #[(← fvarIdToSmtSymbol fv, se)] rhs)

       | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) (Expr.fvar fv)) e) _h =>
            -- case: p = Int.ofNat (namedPattern t n e h) with sn = fvarIdToSmtSymbol n
            let sn ← fvarIdToSmtSymbol fv
            mkLet (smtSimpleVarId sn) e rhs
              fun rhs'=> k (mkLetTerm #[(sn, se)] rhs')

       | _ => throwEnvError "mkLet: unexpected pattern expression: {reprStr p}"

  | Expr.app (Expr.const ``Int.neg _)
      (Expr.app (Expr.const ``Int.ofNat _)
        (Expr.app (Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n))) a)) =>
      match a with
      | Expr.fvar fv =>
           -- case: p' = Int.Neg (Int.ofNat (N + n)) with sn = fvarIdToSmtSymbol n
           k (mkLetTerm #[(← fvarIdToSmtSymbol fv, negSmt (addSmt se (natLitSmt n)))] rhs)
      | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) (Expr.fvar fv)) e) _h =>
           -- case: p' = Int.Neg (Int.ofNat (N + namedPattern t n e h)) with sn = fvarIdToSmtSymbol n
           let sn ← fvarIdToSmtSymbol fv
           mkLet (smtSimpleVarId sn) e rhs
             fun rhs' => k (mkLetTerm #[(sn, negSmt (addSmt se (natLitSmt n)))] rhs')
      | _ => throwEnvError "mkLet: unexpected pattern expression: {reprStr p}"

  | _ =>
     let some (n, args) ← isCtorPattern p
       | throwEnvError "mkLet: unexpected pattern expression: {reprStr p}"
     if args.size == 0 then
       -- case: p = C (i.e., nullary constructor)
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

/-- Generate the necessary ite condition expressions when translating a `match` to an smt if-then-else, such that:
    given `se` a match discriminator that has already been translated to an smt term, `pp` its
    corresponding match expression, `mkCond se pp` is defined as follows:
     let p' ← removeAndOptNamedPatternExpr pp;
      := ( = se sp )    if isIntNatStrCst p' ∨ isBoolCtor p' with sp := termTranslator p'
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
  let p' ← removeAndOptNamedPatternExpr pp
  if isCstLiteral p' || isBoolCtor p' then
    -- case: isIntNatStrCst p' ∨ isBoolCtor p'
    return (andTerms.push (eqSmt (← termTranslator p') se))
  match p' with
  | Expr.fvar _ => return andTerms -- case: p' = fv
  | Expr.const c _ =>
      -- case: if p' = C (i.e., nullary constructor)
      if !(← isCtorName c) then
        throwEnvError "mkCond: nullary ctor expected but got {reprStr p'}"
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
       | throwEnvError "mkCond: unexpected pattern expression: {reprStr p'}"
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
  (alt : Expr) (_matchType : Expr) (acc : Option MatchResult) : TranslateEnvT (Option MatchResult) := do
  let altArgsRes ← retrieveAltsArgs lhs
  let rhs := betaReduceRhs alt altArgsRes.altArgs
  let hvars ← altArgsRes.altArgs.foldlM insertFVars .emptyWithCapacity
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
    insertFVars (h : Std.HashSet FVarId) (v : Expr) : TranslateEnvT (Std.HashSet FVarId) := do
      match v with
      | Expr.fvar fv =>
          match (← inferTypeEnv v).getAppFn' with
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
          let p' ← removeAndOptNamedPatternExpr p;
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

       - mkRhs [se₁ ... seₙ] [p₁ ... pₙ] t :
           let st := termTranslator t
           := (mkLet se₁ p₁ ( ... (mkLet seₙ₋₁ pₙ₋₁ (mkLet seₙ pₙ st))))

       - mkLet se p t :
           := (let ((sfv se)) t)     if p = fv with sfv = fvarIdToSmtSymbol fv
           := t                      if p = C (i.e., nullary constructor)
           := t                      if isIntNatStrCst(p)

           := (let ((sn se)) (mkLet sn' e t))
                  if p = namedPattern t n e h` with sn = fvarIdToSmtSymbol n ∧ sn' = smtSimpleVarId sn

           := (let ((sn (- se N))) t)  if p = N + n ∧ Type(N) = Nat with sn = fvarIdToSmtSymbol n

           := (let ((sn (- se N))) (mkLet sn' e t))
                   if p = N + (namedPattern t n e h) ∧ Type(N) = Nat with sn = fvarIdToSmtSymbol n ∧ sn' = smtSimpleVarId sn
           := (let ((sn se)) t)       if p = Int.ofNat n with sn = fvarIdToSmtSymbol n

           := (let ((sn se)) (mkLet sn' e t))
                   if p = Int.ofNat (namedPattern t n e t) with sn = fvarIdToSmtSymbol n ∧ sn' = smtSimpleVarId sn

           := (let ((sn (- se N))) t)  if p = Int.ofNat (N + n) with sn = fvarIdToSmtSymbol n

           := (let ((sn (- se N))) (mkLet sn' e t))
                   if p = Int.ofNat (N + namedPattern t n e h) with sn = fvarIdToSmtSymbol n ∧ sn' = smtSimpleVarId sn

           := (let ((sn (- (+ se N)))) t) if p' = Int.Neg (Int.ofNat (N + n)) with sn = fvarIdToSmtSymbol n

           := (let ((sn (- (+ se N)))) (mkLet sn' e t))
                   if p' = Int.Neg (Int.ofNat (N + namedPattern t n e h)) with sn = fvarIdToSmtSymbol n ∧ sn' = smtSimpleVarId sn

           := (mkLet (C.1 se) x₁ (.. (mkLet (C.k-1 se) xₖ₋₁ (mkLet (C.k se) xₙ t)))) if p' = C x₁ ... xₖ

           := ⊥                                  otherwise

    Note that we here expect the optimization phase must reach match expression whenever
    at least one eᵢ is a constant/ctor.
-/
def translateMatch?
  (f : Expr) (args : Array Expr)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT (Option SmtTerm) := do
  let some mInfo ← isMatcher? f | return none
  let some r ← matchExprRewriter mInfo args (translateMatchAux? termTranslator) | return none
  return r.iteTerm

end Blaster.Smt
