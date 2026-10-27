import Lean
import Blaster.Optimize.Rewriting.Utils
import Blaster.Optimize.Rewriting.OptimizeNat
import Blaster.Optimize.Rewriting.OptimizeInt


open Lean Meta Elab
namespace Blaster.Optimize

def instantiateMatchType (mInfo : MatchInfo) (args : Array Expr) (instKey? : Option Expr := none) : TranslateEnvT Expr := do
  let motive := args[mInfo.getFirstDiscrPos - 1]!
  if !isDependentLambda motive then return motive
  else
    let instKey ← mkInstKey instKey?
    let matchType := (← get).optEnv.memCache.matchTypeCache.getD instKey instCacheMiss
    if exprEq matchType instCacheMiss then
      let matchType ← visit motive mInfo.getFirstDiscrPos mInfo.getFirstAltPos (Array.emptyWithCapacity mInfo.numDiscrs)
      updateMatchTypeCache instKey matchType
      return matchType
    else return matchType

  where
   mkInstKey (instKey? : Option Expr) : TranslateEnvT Expr :=
     match instKey? with
     | some key => return key
     | none => mkAppRangeExpr mInfo.instApp 0 mInfo.getFirstAltPos args

   visit (e : Expr) (idx : Nat) (stop : Nat) (discrs : Array Expr) : TranslateEnvT Expr := do
     match e with
     | .lam _ t b _ =>
         if idx < stop then
           let t' ← if t.hasLooseBVars then instantiateSharedRevRange t discrs.size discrs else pure t
           let discrs := discrs.push args[idx]!
           e.updateLambdaExpr! t' (← visit b (idx + 1) stop discrs)
         else return e
     | b => if b.hasLooseBVars then instantiateSharedRevRange b discrs.size discrs else pure b

@[always_inline, inline]
def getDiscrsType (mInfo : MatchInfo) (args : Array Expr) (instKey : Expr) : TranslateEnvT (Array Expr) := do
  let matchType ← instantiateMatchType mInfo args (instKey? := some instKey)
  getLambdaBinderTypes matchType

@[always_inline, inline]
def getMatchAltsAux (instKey : Expr) (args : Array Expr) (mInfo : MatchInfo) : TranslateEnvT (Array Expr) := do
 match (← get).optEnv.memCache.matchAltsCache.get? instKey with
 | some alts => return alts
 | none =>
    let auxApp ← betaLambdaSharedRange mInfo.instApp mInfo.getFirstAltPos args
    let alts ← getLambdaBoundedBinderTypes auxApp mInfo.numAlts
    -- update cache
    updateMatchAltsCache instKey alts
    return alts

@[always_inline, inline]
def getMatchAlts (args : Array Expr) (mInfo : MatchInfo) : TranslateEnvT (Array Expr) := do
 let genApp ← mkAppRangeExpr mInfo.instApp 0 mInfo.getFirstDiscrPos args
 getMatchAltsAux genApp args mInfo

/-- Return `true` is p is a nat, integer or string literal expression. -/
def isCstLiteral (p : Expr) : Bool :=
  (isNatValue? p).isSome || (isIntValue? p).isSome || (isStrValue? p).isSome


/-- Only apply NatAdd and IntNeg optimization on match pattern --/
@[always_inline, inline]
def optimizePattern (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  match f with
  | Expr.const ``Nat.add _ => optimizeNatAdd f args
  | Expr.const ``Int.neg _ => optimizeIntNeg f args
  | _ => mkAppNExpr f args


/-- Remove all namedPattern expression in `p` and apply optimizePattern whenever necessary.
    TODO: change function to pure tail rec call using stack-based approach
-/
partial def removeNamedPatternExpr (p : Expr) : TranslateEnvT Expr := do
 match p with
 | Expr.const .. | Expr.lit .. | Expr.fvar .. | Expr.lam .. => return p
 | Expr.app .. =>
      let (f, args) := getAppFnWithArgs p
      match f with
      | Expr.const n _ =>
         if n == ``namedPattern then
           removeNamedPatternExpr args[2]!
         else
           let mut args := args
           let pInfo ← getFunEnvInfo f
           for i in [:args.size] do
             if i < pInfo.paramsInfo.size then
              if pInfo.paramsInfo[i]!.isExplicit then
                args ← args.modifyM i removeNamedPatternExpr
             else
                args ← args.modifyM i removeNamedPatternExpr
           optimizePattern f args
      | _ => throwEnvError "removeNamedPatternExpr: const expression expected but got {reprStr f}"
 | _ => throwEnvError "removeNamedPatternExpr: unexpected pattern expression: {reprStr p}"

/-- Assign `fv` to `v` in the local context s.t.,
     - When fv has a lambda free variable declaration (i.e., LocalDecl.cdecl)
         - replace it with a let free variable declaration (i.e., LocalDecl.ldecl with value set to `v`)
     - When fv is a let free variable declaration only replace the let bind value with `v`
-/
def modifyFVarValue (fv : FVarId) (v : Expr) : TranslateEnvT Unit :=
  modifyOptEnv fun ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, ⟨ctx, localInsts⟩, o14⟩ =>
               ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, ⟨ctx.modifyLocalDecl fv declModifier, localInsts⟩, o14⟩

 where
   declModifier (d : LocalDecl) : LocalDecl :=
     match d with
     | LocalDecl.cdecl idx fvarId userName type _ kind =>
        LocalDecl.ldecl idx fvarId userName type v false kind
     | LocalDecl.ldecl idx fvarId userName type _v nonDep kind =>
        LocalDecl.ldecl idx fvarId userName type v nonDep kind

/-- Return `some (C, #[xₖ, ..., xₙ])` when p := `C x₁ ... xₙ` such that:
     - C is a ctor name.
     - x₁ ... xₖ₋₁ correspond to the polymorphic parameters of the corresponding inductive datatype.
-/
def isCtorPattern (p : Expr) : TranslateEnvT (Option (Name × Array Expr)) := do
 match p.getAppFn' with
 | Expr.const n _ =>
     match (← getConstEnvInfo n) with
     | ConstantInfo.ctorInfo info =>
         let args := p.getAppArgs
         return (n, args[info.numParams:args.size].toArray)
     | _ => return none
 | _ => return none

mutual
/-- Special let expression case for parameterized constructors when normalizing a `match` to ite, s.t.,
     Given p = C x₁ ... xₙ and `t`  the match right-hand side expression,
       return `(mkCstLet x₁ (.. (mkCstLet xₖ₋₁ (mkCstLet xₙ t))))`
     where,
      mkCstLet e t :
       := t             if e = C
       := t             if isIntNatStrCst(e)
       := let pn := removeNamedPatternExpr pe in
          let ph := Eq.Refl (← getLevelEnv pt) pt (removeNamedPatternExpr pe)) in
          (mkCstLet pe t)  if e = namedPattern pt pn pe ph
       := let pn := removeNamedPatternExpr pe in
          let ph := Eq.Refl (← getLevelEnv pt) pt (removeNamedPatternExpr pe)) in
          (mkCstLet pe t)  if e = N + (namedPattern pt pn pe ph) ∧ Type(N) = Nat
       := (mkCstLet pe t)  if e = Int.ofNat pe
       := (mkCstLet pe t)  if e = Int.neg pe
       := (mkCstLet x₁ (.. (mkCstLet xₖ₋₁ (mkCstLet xₙ t)))) if e = C x₁ ... xₖ
       := ⊥  otherwise
-/
private partial def mkLetCtors
  (c : Name) (idx : Nat) (args : Array Expr) (t : Expr)
  (k : Expr → TranslateEnvT Expr) : TranslateEnvT Expr := do
  if idx == 0 then
    mkCstLet args[idx]! t k
  else
    mkCstLet args[idx]! t
      fun t' => mkLetCtors c (idx - 1) args t' k

private partial def mkCstLet
   (e : Expr) (t : Expr) (k : Expr → TranslateEnvT Expr) := do
   if isCstLiteral e then return (← k t) -- case: isIntNatStrCst(e)
   match e with
   | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) pt) pn) pe) ph
   | Expr.app (Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal _)))
      (Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) pt) pn) pe) ph) =>
      -- case: e = namedPattern t n pe h
      -- case: e = N + (namedPattern t n pe h) ∧ Type(N) = Nat
      mkCstLet pe t
        fun t' => do
          let pe' ← removeNamedPatternExpr pe
          modifyFVarValue pn.fvarId! pe'
          let lvl ← getLevelEnv pt
          modifyFVarValue ph.fvarId! (← mkApp2Expr (← mkEqRefl [lvl]) pt pe')
          k (← mkLetFVarsExpr #[pn] (← mkLetFVarsExpr #[ph] t'))

   | Expr.app (Expr.const ``Int.ofNat _) pe
   | Expr.app (Expr.const ``Int.neg _) pe =>
        -- case: e = Int.ofNat pe
        -- case: e = Int.neg pe
        mkCstLet pe t k
   | _ =>
     let some (n, args) ← isCtorPattern e
       | throwEnvError "mkCstLet: unexpected pattern expression: {reprStr e}"
     if args.size == 0 then
       -- case: e = C (i.e., nullary constructor)
       k t
     else mkLetCtors n (args.size - 1) args t k -- case: e = C x₁ ... xₖ

end

/-- Generate the necessary let expressions when normalizing a `match` to ite, s.t.,
    given `e` a match discriminator, `p` its corresponding match expression and
    `t` the match right-hand side expression, `mkLet e p t` is defined as follows:
       := let v := e in t  if p = v
       := t                if p = C (i.e., nullary constructor)
       := t                if isIntNatStrCst(p)
       := let pn := e in
          let ph := Eq.refl (← getLevelEnv pt) pt e in
          (mkLet pn pe t)  if p = namedPattern pt pn pe ph
       := let n := e - N in t  if p = N + n ∧ Type(N) = Nat
       := let pn := e - N in
          let ph := Eq.refl (← getLevelEnv pt) pt (e - N) in
          (mkLet pn pe t) if p = N + (namedPattern pt pn pe ph) ∧ Type(N) = Nat
       := let n := Int.toNat e in t         if p = Int.ofNat n
       := let pn := Int.toNat e in
          let ph := Eq.refl (← getLevelEnv pt) pt (Int.toNat e) in
          (mkLet pn pe t) if p = Int.ofNat (namedPattern pt pn pe ph)
       := let n := Int.toNat e - N in t  if p = Int.ofNat (N + n)
       := let pn := Int.toNat e - N in
          let ph := Eq.refl (← getLevelEnv pt) pt (Int.toNat e - N) in
          (mkLet pn pe t) if p = Int.ofNat (N + namedPattern pt pn pe ph)
       := let n := (Int.toNat (Int.neg e)) - N in t   if p = Int.neg (Int.ofNat (N + n))
       := let pn := (Int.toNat (Int.neg e)) - N in
          let ph := Eq.refl (← getLevelEnv pt) pt (Int.toNat (Int.neg e)) - N in
          (mkLet pn pe t)  if p = Int.neg (Int.ofNat (N + namedPattern pt pn pe ph))
       := (mkCstLet x₁ (.. (mkCstLet xₖ₋₁ (mkCstLet xₙ t)))) if p = C x₁ ... xₖ
       := ⊥  otherwise
-/
private partial def mkLet
  (e : Expr) (p : Expr) (t : Expr)
  (k : Expr → TranslateEnvT Expr) : TranslateEnvT Expr := do
  if isCstLiteral p then return (← k t) -- case: isIntNatStrCst(p)
  match p with
  | Expr.fvar fv =>
      -- case: p = v
      modifyFVarValue fv e
      k (← mkLetFVarsExpr #[p] t)

  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) pt) pn) pe) ph =>
      -- case: p := namedPattern pt pn pe ph
      mkLet pn pe t
       fun t' => do
         modifyFVarValue pn.fvarId! e
         let lvl ← getLevelEnv pt
         modifyFVarValue ph.fvarId! (← mkApp2Expr (← mkEqRefl [lvl]) pt e)
         k (← mkLetFVarsExpr #[pn] (← mkLetFVarsExpr #[ph] t'))

  | Expr.app (Expr.app (Expr.const ``Nat.add _) n) a =>
      if !(isNatValue n) then throwEnvError "mkLet: unexpected pattern expression: {reprStr p}"
      let v ← mkApp2Expr (← mkNatSubOp) e n
      match a with
      | Expr.fvar fv =>
          -- case: p = N + n ∧ Type(N) = Nat
          modifyFVarValue fv v
          k (← mkLetFVarsExpr #[a] t)

      | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) pt) pn) pe) ph =>
          mkLet pn pe t
            fun t' => do
              modifyFVarValue pn.fvarId! v
              let lvl ← getLevelEnv pt
              modifyFVarValue ph.fvarId! (← mkApp2Expr (← mkEqRefl [lvl]) pt v)
              k (← mkLetFVarsExpr #[pn] (← mkLetFVarsExpr #[ph] t'))

      | _ => throwEnvError "mkLet: unexpected pattern expression: {reprStr p}"

  | Expr.app (Expr.const ``Int.ofNat _) a =>
       let v ← mkAppExpr (← mkIntToNatOp) e
       match a with
       | Expr.fvar fv =>
            -- case: p = Int.ofNat n
            modifyFVarValue fv v
            k (← mkLetFVarsExpr #[a] t)

       | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) pt) pn) pe) ph =>
            -- case: p = Int.ofNat (namedPattern s n pe t)
            mkLet pn pe t
              fun t' => do
                modifyFVarValue pn.fvarId! v
                let lvl ← getLevelEnv pt
                modifyFVarValue ph.fvarId! (← mkApp2Expr (← mkEqRefl [lvl]) pt v)
                k (← mkLetFVarsExpr #[pn] (← mkLetFVarsExpr #[ph] t'))

       | Expr.app (Expr.app (Expr.const ``Nat.add _) n) b =>
           if !(isNatValue n) then throwEnvError "mkLet: unexpected pattern expression: {reprStr p}"
           let bv ← mkApp2Expr (← mkNatSubOp) (← mkAppExpr (← mkIntToNatOp) e) n
           match b with
           | Expr.fvar fv =>
               -- case: p = Int.ofNat (N + n)
               modifyFVarValue fv bv
               k (← mkLetFVarsExpr #[b] t)

           | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) pt) pn) pe) ph =>
               -- case: p = Int.ofNat (N + namedPattern s n pe h)
                mkLet pn pe t
                  fun t' => do
                    modifyFVarValue pn.fvarId! bv
                    let lvl ← getLevelEnv pt
                    modifyFVarValue ph.fvarId! (← mkApp2Expr (← mkEqRefl [lvl]) pt bv)
                    k (← mkLetFVarsExpr #[pn] (← mkLetFVarsExpr #[ph] t'))

           | _ => throwEnvError "mkLet: unexpected pattern expression: {reprStr p}"

       | _ => throwEnvError "mkLet: unexpected pattern expression: {reprStr p}"

  | Expr.app (Expr.const ``Int.neg _)
      (Expr.app (Expr.const ``Int.ofNat _)
        (Expr.app (Expr.app (Expr.const ``Nat.add _) n) a)) =>
      if !(isNatValue n) then throwEnvError "mkLet: unexpected pattern expression: {reprStr p}"
      let v ← mkApp2Expr (← mkNatSubOp) (← mkAppExpr (← mkIntToNatOp) (← mkAppExpr (← mkIntNegOp) e)) n
      match a with
      | Expr.fvar fv =>
           -- case: p = Int.neg (Int.ofNat (N + n))
           modifyFVarValue fv v
           k (← mkLetFVarsExpr #[a] t)

      | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) pt) pn) pe) ph =>
           -- case: p = Int.neg (Int.ofNat (N + namedPattern s n pe h))
           mkLet pn pe t
             fun t' => do
               modifyFVarValue pn.fvarId! v
               let lvl ← getLevelEnv pt
               modifyFVarValue ph.fvarId! (← mkApp2Expr (← mkEqRefl [lvl]) pt v)
               k (← mkLetFVarsExpr #[pn] (← mkLetFVarsExpr #[ph] t'))

      | _ => throwEnvError "mkLet: unexpected pattern expression: {reprStr p}"

  | _ =>
     let some (n, args) ← isCtorPattern p
       | throwEnvError "mkLet: unexpected pattern expression: {reprStr p}"
     if args.size == 0 then
       -- case: p = C (i.e., nullary constructor)
       k t
     else
       -- case: p' = C x₁ ... xₖ
       mkLetCtors n (args.size - 1) args t k

/-- Generate the necessary ite condition expressions when normalizing a `match` to ite, such that:
    given `e` a match discriminator and `pp` its corresponding match expression
    for which `p ← removeNamedPatternExpr pp`,
    `mkCond e p` is defined as follows:
       := e = p            if (p ≠ v ∧ Type(eᵢ) ∉ {Nat, Int}) ∨ isIntNatStrCst(p)
       := N ≤ e            if p = N + n ∧ Type(N) = Nat
       := Int.ofNat 0 ≤ e  if p = Int.ofNat n
       := Int.ofNat N ≤ e  if p = Int.ofNat (N + n)
       := e ≤ -N           if p = Int.neg (Int.ofNat (N + n))
       := True             if p = v
       := ⊥                otherwise
-/
private def mkCond (e : Expr) (p : Expr) (eType : Expr) (andTerms : Array Expr) : TranslateEnvT (Array Expr) := do
  if !(p.isFVar || (isNatType eType) || (isIntType eType)) || (isCstLiteral p) then
    -- case: (p ≠ v ∧ Type(eᵢ) ∉ {Nat, Int}) ∨ isIntNatStrCst(p)
    return andTerms.push (← mkApp3Expr (← mkEqOp) eType p e)
  match p with
  | Expr.fvar _ => return andTerms -- case: p = v

  | Expr.app (Expr.app (Expr.const ``Nat.add _) n) (Expr.fvar _fv) =>
     -- case: p = N + n ∧ Type(N) = Nat
     if !(isNatValue n) then throwEnvError "mkCond: unexpected pattern: {reprStr p}"
     else return andTerms.push (← mkAppExpr (← mkPropNotOp) (← mkApp2Expr (← mkNatLtOp) e n))

  | Expr.app (Expr.const ``Int.ofNat _) (Expr.fvar _fv) =>
      -- case: p = Int.ofNat n
      return andTerms.push (← mkAppExpr (← mkPropNotOp) (← mkApp2Expr (← mkIntLtOp) e (← mkIntLitExpr (Int.ofNat 0))))

  | Expr.app (Expr.const ``Int.ofNat _)
     (Expr.app (Expr.app (Expr.const ``Nat.add _) n) (Expr.fvar _fv)) =>
      -- case: p = Int.ofNat (N + n)
      if !(isNatValue n) then throwEnvError "mkCond: unexpected pattern: {reprStr p}"
      else return andTerms.push (← mkAppExpr (← mkPropNotOp) (← mkApp2Expr (← mkIntLtOp) e (← mkAppExpr (← mkIntOfNat) n)))

  | Expr.app (Expr.const ``Int.neg _)
    (Expr.app (Expr.const ``Int.ofNat _)
    (Expr.app (Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n))) (Expr.fvar _fv))) =>
      -- case: p = Int.neg (Int.ofNat (N + n))
      return andTerms.push (← mkAppExpr (← mkPropNotOp) (← mkApp2Expr (← mkIntLtOp) (← mkNatNegExpr n) e))

  | _ => throwEnvError "mkCond: unexpected pattern: {reprStr p}"

/- Return `true` only when `e` corresponds to an optimized Int/Nat const literal.
   Assumes that `e` corresponds to a pattern match.
-/
def isIntNatPatternExpr (e : Expr) : TranslateEnvT Bool := do
 match e.getAppFn' with
 | Expr.const ``Int.ofNat _
 | Expr.const ``Int.neg _
 | Expr.lit (Literal.natVal _)
 | Expr.const ``Nat.add _ => return true
 | fv@(Expr.fvar _) => do
       let t ← inferTypeEnv fv
       return (isNatType t || isIntType t)
 | _ => return false

partial def patternHasFVarOrProof (p : Expr) : TranslateEnvT Bool := do
 let rec visit (e : Expr) : TranslateEnvT Bool := do
   match e with
   | Expr.fvar .. => return true
   | Expr.app .. =>
      let (f, args) := getAppFnWithArgs e
      let pInfo ← getFunEnvInfo f
      match f with
      | Expr.const n _ =>
         -- constructor application
         match (← getConstEnvInfo n) with
         | ConstantInfo.ctorInfo info =>
             -- constructor application
             let args := e.getAppArgs
             let ctorArgs := args[info.numParams:args.size]
             for h : i in [:ctorArgs.size] do
               if pInfo.paramsInfo[i]!.isProp then return true
               if ← visit ctorArgs[i] then return true
             return false
         | _ =>
             for h : i in [:args.size] do
               if pInfo.paramsInfo[i]!.isProp then return true
               if ← visit args[i] then return true
             return false
      | _ => throwEnvError "retrieveAltsArgs: const expression expected but got {reprStr f}"
   | _ => return false
 visit p

structure CommonMatchRewriterParams where
  /-- Match info for current match -/
  mInfo : MatchInfo
  /-- Match arguments -/
  margs : Array Expr
  /-- Match discriminators's type -/
  discrsType : Array Expr
  /-- Match return type -/
  retType : Expr

/-- Is the accumulator `rewriter` function to be used with `matchExprRewriter` when attempting
    to normalize a `match` expression to `if-then-else` (see `normMatchExpr?`).
    Asssumes that matchType := λ β₁ => ... => βₘ
-/
def normMatchExprAux?
  (lastPattern : Bool) (common : CommonMatchRewriterParams)
  (lhs : Array Expr) (rhs : Expr) (params : Array Expr) (acc : Option Expr) : TranslateEnvT (Option Expr) := do
  let plhs ← removeNamedPatterns lhs
  if !(← isItePattern plhs common.discrsType) then return none
  let rhs ← betaLambdaShared rhs params
  if lastPattern then return some (← mkRhs lhs rhs (lastPattern := true)) -- last pattern
  let some elseExpr := acc | return acc
  mkIte lhs plhs rhs elseExpr

 where

   removeNamedPatterns (lhs : Array Expr) : TranslateEnvT (Array Expr) := do
     let mut plhs := Array.emptyWithCapacity lhs.size
     for h : i in [:lhs.size] do
       plhs := plhs.push (← removeNamedPatternExpr lhs[i])
     return plhs

   /-- Return `true` only when the "match" normalization condition is satisfied, i.e,:
        - ∀ i ∈ [1..m], ∀ j ∈ [1..n],
           ¬ isIndexedInductiveType (Type eᵢ) ∧
           ((NoProof (p₍ᵢ₎₍ⱼ₎) ∧ NoFreeVar(p₍ᵢ₎₍ⱼ₎)) ∨ p₍ᵢ₎₍ⱼ₎ = v ∨ isIntNatStrCst(p₍ᵢ₎₍ⱼ₎) ∨ Type(eⱼ) ∈ {Nat, Int} )
   -/
   isItePattern (plhs : Array Expr) (discrsType : Array Expr) : TranslateEnvT Bool := do
     for h : i in [:plhs.size] do
       let p := plhs[i]
       if ← isIndexedInductiveType discrsType[i]! then return false
       if (← patternHasFVarOrProof p) && !p.isFVar && !(isCstLiteral p) && !(← isIntNatPatternExpr p)
       then return false
     return true

   replaceDiscrInLastRhs (lastPattern : Bool) (discr : Expr) (pattern : Expr) (rhs : Expr) : TranslateEnvT Expr := do
     if lastPattern then
       let pattern' ← removeNamedPatternExpr pattern
       if (← isCtorExpr discr.getAppFn') || pattern'.isFVar
       then return rhs
       else replaceShared rhs (λ a => do if exprEq a discr then return pattern' else return none) (resolveMVars := true)
     else return rhs

   mkRhs (lhs : Array Expr) (rhs : Expr) (lastPattern := false) : TranslateEnvT Expr := do
    let mut mrhs := rhs
    let nbPatterns := lhs.size
    for i in [:nbPatterns] do
      let idx := nbPatterns - i - 1
      let pattern := lhs[idx]!
      let discr := common.margs[common.mInfo.getFirstDiscrPos + idx]!
      mrhs ← replaceDiscrInLastRhs lastPattern discr pattern mrhs
      mrhs ← mkLet discr lhs[idx]! mrhs (λ x => return x)
    return mrhs

   mkIte (lhs : Array Expr) (plhs: Array Expr) (rhs : Expr) (elseExpr : Expr) : TranslateEnvT (Option Expr) := do
     let thenExpr ← mkRhs lhs rhs
     let mut andTerms := (#[] : Array Expr)
     for h : i in [:plhs.size] do
       andTerms ← mkCond common.margs[common.mInfo.getFirstDiscrPos + i]! plhs[i] common.discrsType[i]! andTerms
     let nbCond := andTerms.size
     if nbCond == 0 then return thenExpr -- case when else unreachable (i.e., renaming pattern redundant)
     let mut condTerm := andTerms[nbCond-1]!
     let andOp ← mkPropAndOp
     for i in [1:nbCond] do
       let idx := nbCond - i - 1
       condTerm ← mkApp2Expr andOp andTerms[idx]! condTerm
     let hName ← Term.mkFreshBinderName
     let lam1 ← mkLambdaExpr hName BinderInfo.default condTerm thenExpr
     let notCond ← mkAppExpr (← mkPropNotOp) condTerm
     let lam2 ← mkLambdaExpr hName BinderInfo.default notCond elseExpr
     mkApp4Expr (← mkBlasterDIteOp) (common.retType) condTerm lam1 lam2

/-- Instantiating Heq match equation in provided rhs parameters  -/
partial def assignEqRefl
  (mInfo : MatchInfo) (rhs_params : Array Expr)
  (margs : Array Expr) (discrsType : Array Expr) : TranslateEnvT (Array Expr) := do
  let rec visit (idx : Nat) (stop : Nat) (nbHeq : Nat) (xs : Array Expr) : TranslateEnvT (Array Expr) := do
    if idx < stop then return xs
    else
      let idxDiscr := idx - mInfo.getFirstDiscrPos
      if (mInfo.discrInfos[idxDiscr]!).hName?.isSome then
        -- assign mvars to mkEqRefl
        let dType := discrsType[idxDiscr]!
        let lvl ← getLevelEnv dType
        let nbHeq := nbHeq + 1
        let idxMVar := xs.size - nbHeq
        visit (idx - 1) stop nbHeq (xs.set! idxMVar (← mkApp2Expr (← mkEqRefl [lvl]) dType margs[idx]!))
      else
        visit (idx - 1) stop nbHeq xs
   -- traverse discrs in reverse order to properly set heq
   visit (mInfo.getFirstAltPos - 1) mInfo.getFirstDiscrPos 0 rhs_params

/-- A generic match expression rewriter that given a `MatchInfo` instance representing a match application,
    apply the `rewriter` function on each match pattern. The `rewriter` function
    is applied from the last match pattern to the first one.
    Concretely, given a match expression of the form:
      match e₁, ..., eₙ with
      | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
      ...
      | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ

   `matchExprRewriter` return the following evaluation:
     rewriter m-1 [e₁, ..., eₙ] [p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎] t₁ matchType
       ...
       (rewriter 1 [e₁, ..., eₙ] [p₍ₘ₋₁₎₍₁₎, ..., p₍ₘ₋₁₎₍ₙ₎] tₘ₋₁ matchType
         (rewriter 0 [e₁, ..., eₙ] [p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎] tₘ matchType none))
   where,
     - matchType := args[mInfo.getFirstDiscrPos - 1]!
     - the first application is passed the `none` accumulator
     - the `Nat` argument corresponding to the traversed index, starting with 0.
   NOTE: The evaluation stops when at least one of the `rewriter` invocation return `none`.
-/
@[specialize]
def matchExprRewriter
    (mInfo : MatchInfo) (args : Array Expr)
    (rewriter : (lastPattern : Bool) → CommonMatchRewriterParams →
                (lhs : Array Expr) → (rhs : Expr) → (params : Array Expr) → (acc : Option α) → TranslateEnvT (Option α)) :
    TranslateEnvT (Option α) := do
    let instCommonKey ← mkAppRangeExpr mInfo.instApp 0 mInfo.getFirstDiscrPos args
    let alts ← getMatchAltsAux instCommonKey args mInfo
    let instKey ← mkAppRangeExpr instCommonKey mInfo.getFirstDiscrPos mInfo.getFirstAltPos args
    let matchType ← instantiateMatchType mInfo args (instKey? := some instKey)
    let discrsType ← getLambdaBinderTypes matchType
    let retType := getLambdaBody matchType
    commonMatchRewriter ⟨mInfo, args, discrsType, retType⟩ alts

  where
    commonMatchRewriter (common : CommonMatchRewriterParams) (alts : Array Expr) : TranslateEnvT (Option α) := do
      let mut accExpr := (none : Option α)
      -- traverse in reverse order to handle last pattern first
      let nbAlts := alts.size
      for i in [:nbAlts] do
        let idx := nbAlts - i - 1
        accExpr ←
          forallTelescope alts[idx]! fun xs b => do
            let mut lhs := b.getAppArgs
            -- trace[Optimize.normMatch.pattern] "match patterns to optimize {reprStr lhs}"
            -- NOTE: lhs is now implicitly normalized when computing MatchInfo
            let xs ← assignEqRefl mInfo xs common.margs common.discrsType
            rewriter (i == 0) common lhs args[mInfo.getFirstAltPos + idx]! xs accExpr
        unless (accExpr.isSome) do return accExpr -- break if accExpr is still none
      return accExpr


/-- Normalize a `match` expression to `if-then-else` only when each match pattern is either
      - an constructor application that does not contain any free variables (e.g., `Nat.zero`, `some Nat.zero`, `List.const 0 (List.nil)`); or
      - a `Nat`, `Int` or `String` literal; or
      - a `Nat` or `Int` expression; or
      - a free variable `v`

    Concretely:
      match e₁, ..., eₙ with
      | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
      ...
      | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ
     ===>
       sif h1 : (mkCond e₁ p₍₁₎₍₁₎) ∧ ... ∧ (mkCond eₙ p₍₁₎₍ₙ₎) then (mkRhs [e₁ ... eₙ] [p₍₁₎₍₁₎ ... p₍₁₎₍ₙ₎] t₁)
       else sif h2 : (mkCond e₁ p₍₂₎₍₁₎) ∧ ... ∧ (mkCond eₙ p₍₂₎₍ₙ₎) then (mkRhs [e₁ ... eₙ] [p₍₂₎₍₁₎ ... p₍₂₎₍ₙ₎] t₂)
       ...
       else (mkRhs [e₁ ... eₙ] [p₍ₘ₎₍₁₎ ... p₍ₘ₎₍ₙ₎] tₘ)
     when:
       - ∀ i ∈ [1..m], ∀ j ∈ [1..n],
          ¬ isIndexedInductiveType (Type eᵢ) ∧
           ( (NoProof (p₍ᵢ₎₍ⱼ₎) ∧ NoFreeVar(p₍ᵢ₎₍ⱼ₎)) ∨
              p₍ᵢ₎₍ⱼ₎ = v ∨ isIntNatStrCst(p₍ᵢ₎₍ⱼ₎) ∨ Type(eⱼ) ∈ {Nat, Int} )
     with:
       - mkCond e p :
          let p' ← removeNamedPatternExpr p;
           := e = p'           if (p ≠ v ∧ Type(eᵢ) ∉ {Nat, Int}) ∨ isIntNatStrCst(p)
           := N ≤ e            if p' = N + n ∧ Type(N) = Nat
           := Int.ofNat 0 ≤ e  if p' = Int.ofNat n
           := (Int.ofNat N ≤ e if p' = Int.ofNat (N + n)
           := e ≤ -N           if p' = Int.neg (Int.ofNat (N + n))
           := True             if p' = v
           := ⊥                otherwise

       - mkRhs [e₁ ... eₙ] [p₁ ... pₙ] t :
           := (mkLet e₁ p₁ ( ... (mkLet eₙ₋₁ ₙ₋₁ (mkLet eₙ pₙ t))))

       - mkLet e p t :
          let t' := t[e/p']   if (isIntNatStrCst(p') ∨ isCtorPattern p') with p' ← (removeNamedPatternExpr p)
                 := t         otherwise
           := let v := e in t'  if p = v
           := t'                if p = C (i.e., nullary constructor)
           := t'                if isIntNatStrCst(p)
           := let pn := e in
              let ph := Eq.refl (← getLevelEnv pt) pt e in
              (mkLet pn pe t') if p = namedPattern pt pn pe ph ∧ ¬ isIntNatStrCst(pe') ∧
                                  ( Type(eⱼ) ∈ {Nat, Int} ∨ ¬ isCtorPattern pe' )
                               with pe' ← (removeNamedPatternExpr pe)
           := let pn := pe' in
              let ph := Eq.refl (← getLevelEnv pt) pt e in
              (mkCstLet pe t') if p = namedPattern pt pn pe ph ∧
                                      (isIntNatStrCst(pe') ∨ (Type(eⱼ) ∉ {Nat, Int} ∧ isCtorPattern pe'))
                                      with pe' ← (removeNamedPatternExpr pe)
           := let n := e - N in t'  if p = N + n ∧ Type(N) = Nat
           := let pn := e - N in
              let ph := Eq.refl (← getLevelEnv pt) pt (e - N) in
              (mkLet pn pe t')  if p = N + (namedPattern pt pn pe ph) ∧ Type(N) = Nat ∧ ¬ isIntNatStrCst(pe')
                                with pe' ← (removeNamedPatternExpr pe)
           := let pn := pe' in
              let ph := Eq.refl (← getLevelEnv pt) pt pe' in
              (mkCstLet pe t')  if p = N + (namedPattern pt pn pe ph) ∧ Type(N) = Nat ∧ isIntNatStrCst(pe')
                                with pe' ← (removeNamedPatternExpr pe)
           := let n := Int.toNat e in t'        if p = Int.ofNat n
           := let pn := Int.toNat e in
              let ph := Eq.refl (← getLevelEnv pt) pt (Int.toNat e) in
              (mkLet pn pe t')  if p = Int.ofNat (namedPattern pt pn pe ph) ∧ ¬ isIntNatStrCst(pe')
                               with pe' ← (removeNamedPatternExpr pe)
           := let pn := pe' in
              let ph := Eq.refl (← getLevelEnv pt) pt pe' in
              (mkCstLet pe t')  if p = Int.ofNat (namedPattern pt pn pe ph) ∧ isIntNatStrCst(pe')
                                with pe' ← (removeNamedPatternExpr pe)
           := let n := Int.toNat e - N in t'  if p = Int.ofNat (N + n)
           := let pn := Int.toNat e - N in
              let ph := Eq.refl (← getLevelEnv pt) pt (Int.toNat e - N) in
              (mkLet pn pe t')  if p = Int.ofNat (N + namedPattern pt pn pe ph) ∧ ¬ isIntNatStrCst(pe')
                                with pe' ← (removeNamedPatternExpr pe)
           := let pn := pe' in
              let ph := Eq.refl (← getLevelEnv pt) pt pe' in
              (mkCstLet pe t')  if p = Int.ofNat (N + namedPattern pt pn pe ph) ∧ isIntNatStrCst(pe')
                                with pe' ← (removeNamedPatternExpr pe)
           := let n := (Int.toNat (Int.neg e)) - N in t'   if p = Int.neg (Int.ofNat (N + n))
           := let pn := (Int.toNat (Int.neg e)) - N in
              let ph := Eq.refl (← getLevelEnv pt) pt (Int.toNat (Int.neg e)) - N in
              (mkLet pn pe t')  if p = Int.neg (Int.ofNat (N + namedPattern pt pn pe ph)) ∧ ¬ isIntNatStrCst(pe')
                                with pe' ← (removeNamedPatternExpr pe)
           := let pn := pe' in
              let ph := Eq.refl (← getLevelEnv pt) pt pe' in
              (mkCstLet n pe t')  if p = Int.neg (Int.ofNat (N + namedPattern pt pn pe ph)) ∧ isIntNatStrCst(pe')
                                  with pe' ← (removeNamedPatternExpr pe)
           := (mkCstLet x₁ (.. (mkCstLet xₖ₋₁ (mkCstLet xₙ t')))) if p = C x₁ ... xₖ
           := ⊥  otherwise

       - mkCstLet e t :
           := t             if e = C
           := t             if isIntNatStrCst(e)
           := let pn := removeNamedPatternExpr pe in
              let ph := Eq.Refl (← getLevelEnv pt) pt (removeNamedPatternExpr pe)) in
              (mkCstLet pe t)    if e = namedPattern pt pn pe ph
           := let n := removeNamedPatternExpr pe in
              let ph := Eq.Refl (← getLevelEnv pt) pt (removeNamedPatternExpr pe)) in
              (mkCstLet pe t) if e = N + (namedPattern pt pn pe ph) ∧ Type(N) = Nat
           := (mkCstLet pe t)  if e = Int.ofNat pe
           := (mkCstLet pe t)  if e = Int.neg pe
           := (mkCstLet x₁ (.. (mkCstLet xₖ₋₁ (mkCstLet xₙ t)))) if e = C x₁ ... xₖ
           := ⊥  otherwise
-/
def normMatchExpr? (args : Array Expr) (mInfo : MatchInfo) : TranslateEnvT (Option Expr) := do
  match (← get).optEnv.memCache.isMatchToIte.get? mInfo.name with
  | some b => if b then matchExprRewriter mInfo args normMatchExprAux?
                   else return none
  | none =>
      let r ← matchExprRewriter mInfo args normMatchExprAux?
      updateMatchToIteCache mInfo.name r.isSome
      return r

initialize
  registerTraceClass `Optimize.normMatch.pattern

end Blaster.Optimize
