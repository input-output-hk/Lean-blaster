import Lean
import Solver.Optimize.Rewriting.Utils
import Solver.Optimize.Env

open Lean Meta Elab
namespace Solver.Optimize


structure MatchInfo where
  /-- Name of match -/
  name : Name
  /-- Name expression of match -/
  nameExpr : Expr
  /-- Match arguments -/
  args : Array Expr
  /-- match instantiation -/
  instApp : Expr
  /-- MatcherInfo for match -/
  mInfo : MatcherInfo

/-- Determine if `e` is an `match` expression and return a MatchInfo instance.
    Otherwise return `none`.
-/
@[always_inline, inline]
def isMatcher? (e : Expr) : TranslateEnvT (Option MatchInfo) := do
 let (pm, args) := getAppFnWithArgs e
 let Expr.const n l := pm | return none
 let some mInfo ← getMatcherRecInfo? n l | return none
 let cInfo ← getConstEnvInfo n
 let matchFun ← instantiateValueLevelParams cInfo l
 let instApp := Expr.beta matchFun (args.take mInfo.getFirstAltPos)
 return some { name := n, nameExpr := pm, args, instApp, mInfo}

/-- Return `true` is p is a nat, integer or string literal expression. -/
def isCstLiteral (p : Expr) : Bool :=
  (isNatValue? p).isSome || (isIntValue? p).isSome || (isStrValue? p).isSome

/-- Given a match alternative `alt` and its corresponding effective arguments `altArgs`
    perform beta reduction such that:
      - When altArgs.isEmpty
         - return `getLambdaBody alt` (i.e., no free variables in match pattern)
      - otherwise
          - return Expr.beta alt altArgs
-/
def betaReduceRhs (alt : Expr) (altArgs : Array Expr) : Expr :=
  if altArgs.size == 0 -- case when there is no free variables in match pattern
  then getLambdaBody alt
  else Expr.beta alt altArgs

structure AltArgsCache where
  /-- Sequence of named pattern and free variables appearing in each match pattern.
      The order of appearance for named pattern and free variables are preserved.
  -/
  patternFreeVars : Array Expr
  /-- Sequence of named pattern equation appearing in each match pattern.
      The order of appearance is preserved. This sequence is appended to patternFreeVars
      is reset once a pattern match for a specific match descriminator has been considered.
  -/
  namedPatternEqs : Array Expr

  /-- Number of named pattern encountered in the match patten. -/
  nbNamedPatterns: Nat
deriving Inhabited


abbrev AltArgsEnv := StateRefT AltArgsCache TranslateEnvT

/-- Adds `fv` to `patternFreeVars` -/
def updatePatternVars (fv : Expr) : AltArgsEnv Unit := do
  modify (fun env => { env with patternFreeVars := env.patternFreeVars.push fv})


/-- Adds `peq` to `namedPatternEq` -/
def updatePatternEqs (peq : Expr) : AltArgsEnv Unit := do
  modify (fun env => {env with namedPatternEqs := env.namedPatternEqs.push peq})

/-- Performs the following actions:
      - Append patternFreeVars with namedPatternEqs
      - Increment nbNamedPatterns with namedPatternsEq.size
      - Reset namedPatternEqs (i.e., set to empty Array)
-/
def flushPatternEqs : AltArgsEnv Unit := do
  modify (fun env =>
           {env with patternFreeVars := env.patternFreeVars ++ env.namedPatternEqs,
                     namedPatternEqs := .empty,
                     nbNamedPatterns := env.nbNamedPatterns + env.namedPatternEqs.size
           })

structure AltArgsResult where
  /-- Sequence of named pattern labels, named pattern equations and free variables
      appearing in each match pattern.
      The order of appearance for named pattern and free variables are preserved.
      (see function `retrieveAltsArgs`).
  -/
  altArgs : Array Expr

  /-- Number of named pattern encountered in the match patten. -/
  nbNamedPatterns : Nat
deriving Inhabited

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
partial def retrieveAltsArgs (lhs : Array Expr) : TranslateEnvT AltArgsResult := do
 let rec visit (e : Expr) : AltArgsEnv Unit := do
   match e with
   | Expr.const .. | Expr.lit .. => return ()
   | Expr.fvar .. => updatePatternVars e
   | Expr.app .. =>
      Expr.withApp e fun f as => do
       match f with
       | Expr.const n _ =>
          match (← getConstEnvInfo n) with
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
 let loop : AltArgsEnv Unit :=
   for i in [:lhs.size] do
     visit lhs[i]!
     flushPatternEqs
 let (_, res) ← loop|>.run default
 return {altArgs := res.patternFreeVars, nbNamedPatterns := res.nbNamedPatterns}

/-- Remove all namedPattern expression in `p` and apply optimization whenever necessary. -/
partial def removeNamedPatternExpr (optimizer : Expr -> TranslateEnvT Expr) (p : Expr) : TranslateEnvT Expr :=
 match p with
 | Expr.const .. | Expr.lit .. | Expr.fvar .. => return p
 | Expr.app .. =>
      Expr.withApp p fun f as => do
        match f with
        | Expr.const n _ =>
           if n == ``namedPattern then
             removeNamedPatternExpr optimizer as[2]!
           else
             let mut margs := as
             let fInfo ← getFunInfoNArgs f as.size
             for i in [:as.size] do
               if i < fInfo.paramInfo.size then
                if fInfo.paramInfo[i]!.isExplicit then
                  margs ← margs.modifyM i (removeNamedPatternExpr optimizer)
               else
                  margs ← margs.modifyM i (removeNamedPatternExpr optimizer)
             optimizer (mkAppN f margs)
        | _ => throwEnvError f!"removeNamedPatternExpr: const expression expected but got {reprStr f}"
 | _ => throwEnvError f!"removeNamedPatternExpr: unexpected pattern expression: {reprStr p}"


/-- Assign `fv` to `v` in the local context and execute k s.t.,
     - When fv has a lambda free variable declaration (i.e., LocalDecl.cdecl)
         - replace it with a let free variable declaration (i.e., LocalDecl.ldecl with value set to `v`)
     - When fv is a let free variable declaration only replace the let bind value with `v`
-/
def withModifyFVarValue (fv : FVarId) (v : Expr) (k : TranslateEnvT α) : TranslateEnvT α := do
 let lctx := (← getLCtx).modifyLocalDecl fv declModifier
 withLCtx' lctx k

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
       := let n := removeNamedPatternExpr optimizer pe in (mkCstLet pe t) if e = namedPattern t n pe h
       := let n := removeNamedPatternExpr optimizer pe in (mkCstLet pe t) if e = N + (namedPattern t n pe h) ∧ Type(N) = Nat
       := (mkCstLet pe t)  if e = Int.ofNat pe
       := (mkCstLet pe t)  if e = Int.Neg pe
       := (mkCstLet x₁ (.. (mkCstLet xₖ₋₁ (mkCstLet xₙ t)))) if e = C x₁ ... xₖ
       := ⊥  otherwise
-/
private partial def mkLetCtors
  (optimizer : Expr -> TranslateEnvT Expr)
  (c : Name) (idx : Nat) (args : Array Expr) (t : Expr)
  (k : Expr → TranslateEnvT Expr) : TranslateEnvT Expr := do
  if idx == 0 then
    mkCstLet optimizer args[idx]! t k
  else
    mkCstLet optimizer args[idx]! t
      fun t' => mkLetCtors optimizer c (idx - 1) args t' k

 private partial def mkCstLet
   (optimizer : Expr -> TranslateEnvT Expr)
   (e : Expr) (t : Expr) (k : Expr → TranslateEnvT Expr) := do
   if isCstLiteral e then return (← k t) -- case: isIntNatStrCst(e)
   match e with
   | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) np@(Expr.fvar fv)) pe) _h
   | Expr.app (Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal _)))
      (Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) np@(Expr.fvar fv)) pe) _h) =>
      -- case: e = namedPattern t n pe h
      -- case: e = N + (namedPattern t n pe h) ∧ Type(N) = Nat
      mkCstLet optimizer pe t
        fun t' => do
          withModifyFVarValue fv (← removeNamedPatternExpr optimizer pe) $ do
            k (← mkLetFVars #[np] t')

   | Expr.app (Expr.const ``Int.ofNat _) pe
   | Expr.app (Expr.const ``Int.neg _) pe =>
        -- case: e = Int.ofNat pe
        -- case: e = Int.Neg pe
        mkCstLet optimizer pe t k
   | _ =>
     let some (n, args) ← isCtorPattern e
       | throwEnvError f!"mkCstLet: unexpected pattern expression: {reprStr e}"
     if args.size == 0 then
       -- case: e = C (i.e., nullary constructor)
       k t
     else mkLetCtors optimizer n (args.size - 1) args t k -- case: e = C x₁ ... xₖ

end

/-- Generate the necessary let expressions when normalizing a `match` to ite, s.t.,
    given `e` a match discriminator, `p` its corresponding match expression and
    `t` the match right-hand side expression, `mkLet e p t` is defined as follows:
      let t' := t[e/p']   if (isIntNatStrCst(p') ∨ isCtorPattern p') with p' ← (removeNamedPatternExpr optimizer p)
             := t         otherwise
       := let v := e in t'  if p = v
       := t'                if p = C (i.e., nullary constructor)
       := t'                if isIntNatStrCst(p)
       := let n := e in (mkLet n pe t')  if p = namedPattern t n pe h ∧ ¬ isIntNatStrCst(pe') ∧
                                            ( Type(eⱼ) ∈ {Nat, Int} ∨ ¬ isCtorPattern pe' )
                                         with pe' ← (removeNamedPatternExpr optimizer pe)
       := let n := pe' in (mkCstLet pe t')  if p = namedPattern t n pe h ∧
                                               (isIntNatStrCst(pe') ∨ (Type(eⱼ) ∉ {Nat, Int} ∧ isCtorPattern pe'))
                                            with pe' ← (removeNamedPatternExpr optimizer pe)
       := let n := e - N in t'  if p = N + n ∧ Type(N) = Nat
       := let n := e - N in (mkLet n pe t')  if p = N + (namedPattern t n pe h) ∧ Type(N) = Nat ∧ ¬ isIntNatStrCst(pe')
                                             with pe' ← (removeNamedPatternExpr optimizer pe)
       := let n := pe' in (mkCstLet pe t')  if p = N + (namedPattern t n pe h) ∧ Type(N) = Nat ∧ isIntNatStrCst(pe')
                                            with pe' ← (removeNamedPatternExpr optimizer pe)
       := let n := Int.toNat e in t'        if p = Int.ofNat n
       := let n := Int.toNat e in (mkLet n pe t')  if p = Int.ofNat (namedPattern t n pe t) ∧ ¬ isIntNatStrCst(pe')
                                                   with pe' ← (removeNamedPatternExpr optimizer pe)
       := let n := pe' in (mkCstLet pe t')  if p = Int.ofNat (namedPattern t n pe t) ∧ isIntNatStrCst(pe')
                                            with pe' ← (removeNamedPatternExpr optimizer pe)
       := let n := Int.toNat e - N in t'  if p = Int.ofNat (N + n)
       := let n := Int.toNat e - N in (mkLet n pe t')  if p = Int.ofNat (N + namedPattern t n pe h) ∧ ¬ isIntNatStrCst(pe')
                                                       with pe' ← (removeNamedPatternExpr optimizer pe)
       := let n := pe' in (mkCstLet pe t')  if p = Int.ofNat (N + namedPattern t n pe h) ∧ isIntNatStrCst(pe')
                                            with pe' ← (removeNamedPatternExpr optimizer pe)
       := let n := (Int.toNat (Int.neg e)) - N in t'   if p = Int.Neg (Int.ofNat (N + n))
       := let n := (Int.toNat (Int.neg e)) - N in (mkLet n pe t')  if p = Int.Neg (Int.ofNat (N + namedPattern t n pe h)) ∧
                                                                      ¬ isIntNatStrCst(pe')
                                                                   with pe' ← (removeNamedPatternExpr optimizer pe)
       := let n := pe' in (mkCstLet n pe t')  if p = Int.Neg (Int.ofNat (N + namedPattern t n pe h)) ∧ isIntNatStrCst(pe')
                                              with pe' ← (removeNamedPatternExpr optimizer pe)
       := (mkCstLet x₁ (.. (mkCstLet xₖ₋₁ (mkCstLet xₙ t')))) if p = C x₁ ... xₖ
       := ⊥  otherwise
-/
private partial def mkLet
  (optimizer : Expr -> TranslateEnvT Expr)
  (e : Expr) (p : Expr) (ot : Expr)
  (k : Expr → TranslateEnvT Expr) : TranslateEnvT Expr := do
  let p' ← removeNamedPatternExpr optimizer p
  let eType ← inferType e
  let t := if isCstLiteral p' || (!(isNatType eType || isIntType eType) && (← isCtorMatch p'))
           then ot.replace (λ a => if a == e then some p' else none)
           else ot
  if isCstLiteral p then return (← k t) -- case: isIntNatStrCst(p)
  match p with
  | Expr.fvar fv =>
      -- case: p = v
      withModifyFVarValue fv e $ do
        k (← mkLetFVars #[p] t)

  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) np@(Expr.fvar fv)) pe) _h =>
      -- case: p := namedPattern t n pe h
      let pe' ← removeNamedPatternExpr optimizer pe
      if isCstLiteral pe' || (!(isNatType eType || isIntType eType) && (← isCtorMatch pe'))
      then
        -- case: isIntNatStrCst(pe') ∨ (Type(eⱼ) ∉ {Nat, Int} ∧ isCtorPattern pe'))
        mkCstLet optimizer pe t
         fun t' =>
           withModifyFVarValue fv pe' $ do
             k (← mkLetFVars #[np] t')
      else
        -- case: ¬ isIntNatStrCst(pe') ∧( Type(eⱼ) ∈ {Nat, Int} ∨ ¬ isCtorPattern pe' )
        mkLet optimizer np pe t
          fun t' =>
            withModifyFVarValue fv e $ do
              k (← mkLetFVars #[np] t')

  | Expr.app (Expr.app (Expr.const ``Nat.add _) n@(Expr.lit (Literal.natVal _))) a =>
      let v := mkApp2 (← mkNatSubOp) e n
      match a with
      | Expr.fvar fv =>
          -- case: p = N + n ∧ Type(N) = Nat
          withModifyFVarValue fv v $ do
           k (← mkLetFVars #[a] t)

      | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) np@(Expr.fvar fv)) pe) _h =>
          -- case: p = N + (namedPattern t n pe h) ∧ Type(N) = Nat
          let pe' ← removeNamedPatternExpr optimizer pe
          if isCstLiteral pe'
          then
            -- case: isIntNatStrCst(pe')
            mkCstLet optimizer pe t
              fun t' =>
                withModifyFVarValue fv pe' $ do
                 k (← mkLetFVars #[np] t')
          else
            -- case: ¬ isIntNatStrCst(pe')
            mkLet optimizer np pe t
              fun t' =>
                withModifyFVarValue fv v $ do
                  k (← mkLetFVars #[np] t')

      | _ => throwEnvError f!"mkLet: unexpected pattern expression: {reprStr p}"

  | Expr.app (Expr.const ``Int.ofNat _) a =>
       let v := mkApp (← mkIntToNatOp) e
       match a with
       | Expr.fvar fv =>
            -- case: p = Int.ofNat n
            withModifyFVarValue fv v $ do
              k (← mkLetFVars #[a] t)

       | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) np@(Expr.fvar fv)) pe) _h =>
            -- case: p = Int.ofNat (namedPattern t n pe t)
            let pe' ← removeNamedPatternExpr optimizer pe
            if isCstLiteral pe'
            then
              -- case: isIntNatStrCst(pe')
              mkCstLet optimizer pe t
                fun t' =>
                  withModifyFVarValue fv pe' $ do
                  k (← mkLetFVars #[np] t')
            else
              -- case: ¬ isIntNatStrCst(pe')
              mkLet optimizer np pe t
                fun t' =>
                  withModifyFVarValue fv v $ do
                    k (← mkLetFVars #[np] t')

       | Expr.app (Expr.app (Expr.const ``Nat.add _) n@(Expr.lit (Literal.natVal _))) b =>
           let bv := mkApp2 (← mkNatSubOp) (mkApp (← mkIntToNatOp) e) n
           match b with
           | Expr.fvar fv =>
               -- case: p = Int.ofNat (N + n)
               withModifyFVarValue fv bv $ do
               k (← mkLetFVars #[b] t)

           | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) np@(Expr.fvar fv)) pe) _h =>
               -- case: p = Int.ofNat (N + namedPattern t n pe h)
               let pe' ← removeNamedPatternExpr optimizer pe
               if isCstLiteral pe'
               then
                 -- case: isIntNatStrCst(pe')
                 mkCstLet optimizer pe t
                   fun t' =>
                     withModifyFVarValue fv pe' $ do
                     k (← mkLetFVars #[np] t')
               else
                 -- case: ¬ isIntNatStrCst(pe')
                 mkLet optimizer np pe t
                   fun t' =>
                     withModifyFVarValue fv bv $ do
                       k (← mkLetFVars #[np] t')

           | _ => throwEnvError f!"mkLet: unexpected pattern expression: {reprStr p}"

       | _ => throwEnvError f!"mkLet: unexpected pattern expression: {reprStr p}"

  | Expr.app (Expr.const ``Int.neg _)
      (Expr.app (Expr.const ``Int.ofNat _)
        (Expr.app (Expr.app (Expr.const ``Nat.add _) n@(Expr.lit (Literal.natVal _))) a)) =>
      let v := mkApp2 (← mkNatSubOp) (mkApp (← mkIntToNatOp) (mkApp (← mkIntNegOp) e)) n
      match a with
      | Expr.fvar fv =>
           -- case: p = Int.Neg (Int.ofNat (N + n))
           withModifyFVarValue fv v $ do
             k (← mkLetFVars #[a] t)

      | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) np@(Expr.fvar fv)) pe) _h =>
           -- case: p = Int.Neg (Int.ofNat (N + namedPattern t n pe h))
           let pe' ← removeNamedPatternExpr optimizer pe
           if isCstLiteral pe'
           then
             -- case: isIntNatStrCst(pe')
             mkCstLet optimizer pe t
               fun t' =>
                 withModifyFVarValue fv pe' $ do
                 k (← mkLetFVars #[np] t')
           else
             -- case: ¬ isIntNatStrCst(pe')
             mkLet optimizer np pe t
               fun t' =>
                 withModifyFVarValue fv v $ do
                   k (← mkLetFVars #[np] t')

      | _ => throwEnvError f!"mkLet: unexpected pattern expression: {reprStr p}"

  | _ =>
     let some (n, args) ← isCtorPattern p
       | throwEnvError f!"mkLet: unexpected pattern expression: {reprStr p}"
     if args.size == 0 then
       -- case: p = C (i.e., nullary constructor)
       k t
     else
       -- case: p' = C x₁ ... xₖ
       mkLetCtors optimizer n (args.size - 1) args t k

  where
    isCtorMatch (e : Expr) := isCtorExpr e.getAppFn'

/-- Generate the necessary ite condition expressions when normalizing a `match` to ite, such that:
    given `e` a match discriminator and `pp` its corresponding match expression
    for which `p ← removeNamedPatternExpr optimizer pp`,
    `mkCond e p` is defined as follows:
       := e = p            if (p ≠ v ∧ Type(eᵢ) ∉ {Nat, Int}) ∨ isIntNatStrCst(p)
       := N ≤ e            if p = N + n ∧ Type(N) = Nat
       := Int.ofNat 0 ≤ e  if p = Int.ofNat n
       := Int.ofNat N ≤ e  if p = Int.ofNat (N + n)
       := e ≤ -N           if p = Int.Neg (Int.ofNat (N + n))
       := True             if p = v
       := ⊥                otherwise
-/
private def mkCond (e : Expr) (p : Expr) (andTerms : Array Expr) : TranslateEnvT (Array Expr) := do
  let eType ← inferType e
  if !(p.isFVar || (isNatType eType) || (isIntType eType)) || (isCstLiteral p) then
    -- case: (p ≠ v ∧ Type(eᵢ) ∉ {Nat, Int}) ∨ isIntNatStrCst(p)
    return andTerms.push (mkApp3 (← mkEqOp) eType p e)
  match p with
  | Expr.fvar _ => return andTerms -- case: p = v

  | Expr.app (Expr.app (Expr.const ``Nat.add _) n@(Expr.lit (Literal.natVal _))) (Expr.fvar _fv) =>
     -- case: p = N + n ∧ Type(N) = Nat
     return andTerms.push (mkApp2 (← mkNatLeOp) n e)

  | Expr.app (Expr.const ``Int.ofNat _) (Expr.fvar _fv) =>
      -- case: p = Int.ofNat n
      return andTerms.push (mkApp2 (← mkIntLeOp) (← mkIntLitExpr (Int.ofNat 0)) e)

  | Expr.app (Expr.const ``Int.ofNat _)
     (Expr.app (Expr.app (Expr.const ``Nat.add _) n@(Expr.lit (Literal.natVal _))) (Expr.fvar _fv)) =>
      -- case: p = Int.ofNat (N + n)
      return andTerms.push (mkApp2 (← mkIntLeOp) (mkApp (← mkIntOfNat) n) e)

  | Expr.app (Expr.const ``Int.neg _)
    (Expr.app (Expr.const ``Int.ofNat _)
    (Expr.app (Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n))) (Expr.fvar _fv))) =>
      -- case: p = Int.Neg (Int.ofNat (N + n))
      return andTerms.push (mkApp2 (← mkIntLeOp) e (← mkNatNegExpr n))

  | _ => throwEnvError f!"mkCond: unexpected pattern: {reprStr p}"


/-- Is the accumulator `rewriter` function to be used with `matchExprRewriter` when attempting
    to normalize a `match` expression to `if-then-else` (see `normMatchExpr?`).
-/
def normMatchExprAux?
  (optimizer : Expr -> TranslateEnvT Expr)
  (idx : Nat) (discrs : Array Expr)
  (lhs : Array Expr) (alt : Expr) (acc : Option Expr) : TranslateEnvT (Option Expr) := do
  let altArgsRes ← retrieveAltsArgs lhs
  let plhs ← removeNamedPatterns lhs
  if !(← isItePattern discrs altArgsRes plhs) then return none
  let rhs := betaReduceRhs alt altArgsRes.altArgs
  if idx == 0 then return some (← mkRhs discrs lhs rhs) -- last pattern
  let some elseExpr := acc | return acc
  mkIte discrs lhs plhs rhs elseExpr

 where

   removeNamedPatterns (lhs : Array Expr) : TranslateEnvT (Array Expr) := do
     let mut plhs := #[]
     for i in [:lhs.size] do
       plhs := plhs.push (← removeNamedPatternExpr optimizer lhs[i]!)
     return plhs

   /-- Return `true` only when the "match" normalization condition is satisfied, i.e,:
        - ∀ i ∈ [1..m], ∀ j ∈ [1..n], ( NoFreeVar(p₍ᵢ₎₍ⱼ₎) ∨ p₍ᵢ₎₍ⱼ₎ = v ∨ isIntNatStrCst(p₍ᵢ₎₍ⱼ₎) ∨ Type(eⱼ) ∈ {Nat, Int} )
       NOTE: condition `∃ [ Decidable (eⱼ = p₍ᵢ₎₍ⱼ₎)] ∈ DecidableInstances` is enforced when
       generating the ite expression.
   -/
   isItePattern (discrs : Array Expr) (argsResult : AltArgsResult) (plhs : Array Expr) : TranslateEnvT Bool := do
     if argsResult.altArgs.size == 0 then return true
     let mut fvarCnt := 0
     for i in [:plhs.size] do
      let p := plhs[i]!
      let e := discrs[i]!
      let eType ← inferType e
      if (p.isFVar || (!(isCstLiteral p) && (isNatType eType || isIntType eType)))
      then fvarCnt := fvarCnt + 1
     -- filter out named pattern equations and named pattern labels
     return (argsResult.altArgs.size - (argsResult.nbNamedPatterns * 2) == fvarCnt)

   mkRhs (discrs : Array Expr) (lhs : Array Expr) (rhs : Expr) : TranslateEnvT Expr := do
    let mut mrhs := rhs
    let nbPatterns := lhs.size
    for i in [:nbPatterns] do
      let idx := nbPatterns - i - 1
      mrhs ← mkLet optimizer discrs[idx]! lhs[idx]! mrhs (λ x => return x)
    return mrhs

   mkIte (discrs : Array Expr) (lhs : Array Expr)
         (plhs: Array Expr) (rhs : Expr) (elseExpr : Expr) : TranslateEnvT (Option Expr) := do
     let thenExpr ← mkRhs discrs lhs rhs
     let mut andTerms := (#[] : Array Expr)
     for i in [:lhs.size] do
       andTerms ← mkCond discrs[i]! plhs[i]! andTerms
     let nbCond := andTerms.size
     if nbCond == 0 then return thenExpr -- case when else unreachable (i.e., renaming pattern redundant)
     let mut condTerm := andTerms[nbCond-1]!
     let andOp ← mkPropAndOp
     for i in [1:nbCond] do
       let idx := nbCond - i - 1
       condTerm := mkApp2 andOp andTerms[idx]! condTerm
     -- we don't want to cache the decidable constraint as condExpr is not optimized at this stage
     -- return none if decidable instance cannot be synthesized.
     let some decideExpr ← trySynthDecidableInstance? condTerm (cacheDecidableCst := false) | return none
     return (mkApp5 (← mkIteOp) (← inferType rhs) condTerm decideExpr thenExpr elseExpr)


/-- A generic match expression rewriter that given a `MatchInfo` instance representing a match application,
    apply the `rewriter` function on each match pattern. The `rewriter` function
    is applied from the last match pattern to the first one.
    Concretely, given a match expression of the form:
      match e₁, ..., eₙ with
      | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
      ...
      | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ

   `matchExprRewriter` return the following evaluation:
     rewriter m-1 [e₁, ..., eₙ] [p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎] t₁
       ...
       (rewriter 1 [e₁, ..., eₙ] [p₍ₘ₋₁₎₍₁₎, ..., p₍ₘ₋₁₎₍ₙ₎] tₘ₋₁
         (rewriter 0 [e₁, ..., eₙ] [p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎] tₘ none))
   where,
     - the first application is passed the `none` accumulator
     - the `Nat` argument corresponding to the traversed index, starting with 0.
   NOTE: The evaluation stops when at least one of the `rewriter` invocation return `none`.
-/
-- @[specialize]
def matchExprRewriter
    (mInfo : MatchInfo)
    (optimizer : Expr -> TranslateEnvT Expr)
    (rewriter : Nat → Array Expr → Array Expr → Expr → Option α → TranslateEnvT (Option α)) :
    TranslateEnvT (Option α) := do
    let discrs := mInfo.args.extract mInfo.mInfo.getFirstDiscrPos mInfo.mInfo.getFirstAltPos
    let rhs := mInfo.args.extract mInfo.mInfo.getFirstAltPos mInfo.mInfo.arity
    if (isCasesOnRecursor (← getEnv) mInfo.name) then
      lambdaTelescope mInfo.instApp fun xs _t =>
        commonMatchRewriter discrs xs[xs.size - rhs.size:] rhs
    else
      forallTelescope (← inferType mInfo.instApp) fun xs _t =>
        commonMatchRewriter discrs xs[xs.size - rhs.size:] rhs

  where
    commonMatchRewriter
      (discrs : Array Expr) (alts : Array Expr) (rhs : Array Expr) : TranslateEnvT (Option α) := do
      let mut accExpr := (none : Option α)
      -- traverse in reverse order to handle last pattern first
      let nbAlts := alts.size
      for i in [:nbAlts] do
        let idx := nbAlts - i - 1
        accExpr ←
          forallTelescope (← inferType alts[idx]!) fun _xs b => do
            let mut lhs := b.getAppArgs
            trace[Optimize.normMatch.pattern] "match patterns to optimize {reprStr lhs}"
            -- NOTE: lhs has not been normalized as is kept at the type level.
            -- normalizing lhs
            for j in [:lhs.size] do
              lhs ← lhs.modifyM j optimizer
            trace[Optimize.normMatch.optPattern] "optimized match patterns {reprStr lhs}"
            rewriter i discrs lhs rhs[idx]! accExpr
        unless (accExpr.isSome) do return accExpr -- break if accExpr is still none
      return accExpr


/-- Normalize a `match` expression to `if-then-else` only when each match pattern is either
      - an constructor application that does not contain any free variables (e.g., `Nat.zero`, `some Nat.zero`, `List.const 0 (List.nil)`); or
      - a `Nat`, `Int` or `String` literal; or
      - a `Nat` or `Int` expression; or
      - a free variable `v`
    Normalization will NOT take place when no decidable equality instance can be found for each match discriminator.
    Concretely:
      match e₁, ..., eₙ with
      | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
      ...
      | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ
     ===>
       if (mkCond e₁ p₍₁₎₍₁₎) ∧ ... ∧ (mkCond eₙ p₍₁₎₍ₙ₎) then (mkRhs [e₁ ... eₙ] [p₍₁₎₍₁₎ ... p₍₁₎₍ₙ₎] t₁)
       else if (mkCond e₁ p₍₂₎₍₁₎) ∧ ... ∧ (mkCond eₙ p₍₂₎₍ₙ₎) then (mkRhs [e₁ ... eₙ] [p₍₂₎₍₁₎ ... p₍₂₎₍ₙ₎] t₂)
       ...
       else (mkRhs [e₁ ... eₙ] [p₍ₘ₎₍₁₎ ... p₍ₘ₎₍ₙ₎] tₘ)
     when:
       - ∀ i ∈ [1..m], ∀ j ∈ [1..n],
           ( NoFreeVar(p₍ᵢ₎₍ⱼ₎) ∨ p₍ᵢ₎₍ⱼ₎ = v ∨ isIntNatStrCst(p₍ᵢ₎₍ⱼ₎) ∨ Type(eⱼ) ∈ {Nat, Int} ) ∧
           ∃ [ Decidable (eⱼ = p₍ᵢ₎₍ⱼ₎)] ∈ DecidableInstances
     with:
       - mkCond e p :
          let p' ← removeNamedPatternExpr optimizer p;
           := e = p'           if (p ≠ v ∧ Type(eᵢ) ∉ {Nat, Int}) ∨ isIntNatStrCst(p)
           := N ≤ e            if p' = N + n ∧ Type(N) = Nat
           := Int.ofNat 0 ≤ e  if p' = Int.ofNat n
           := (Int.ofNat N ≤ e if p' = Int.ofNat (N + n)
           := e ≤ -N           if p' = Int.Neg (Int.ofNat (N + n))
           := True             if p' = v
           := ⊥                otherwise

       - mkRhs [e₁ ... eₙ] [p₁ ... pₙ] t :
           := (mkLet e₁ p₁ ( ... (mkLet eₙ₋₁ ₙ₋₁ (mkLet eₙ pₙ t))))

       - mkLet e p t :
          let t' := t[e/p']   if (isIntNatStrCst(p') ∨ isCtorPattern p') with p' ← (removeNamedPatternExpr optimizer p)
                 := t         otherwise
           := let v := e in t'  if p = v
           := t'                if p = C (i.e., nullary constructor)
           := t'                if isIntNatStrCst(p)
           := let n := e in (mkLet n pe t')  if p = namedPattern t n pe h ∧ ¬ isIntNatStrCst(pe') ∧
                                               ( Type(eⱼ) ∈ {Nat, Int} ∨ ¬ isCtorPattern pe' )
                                             with pe' ← (removeNamedPatternExpr optimizer pe)
           := let n := pe' in (mkCstLet pe t')  if p = namedPattern t n pe h ∧
                                                   (isIntNatStrCst(pe') ∨ (Type(eⱼ) ∉ {Nat, Int} ∧ isCtorPattern pe'))
                                                with pe' ← (removeNamedPatternExpr optimizer pe)
           := let n := e - N in t'  if p = N + n ∧ Type(N) = Nat
           := let n := e - N in (mkLet n pe t')  if p = N + (namedPattern t n pe h) ∧ Type(N) = Nat ∧ ¬ isIntNatStrCst(pe')
                                                 with pe' ← (removeNamedPatternExpr optimizer pe)
           := let n := pe' in (mkCstLet pe t')  if p = N + (namedPattern t n pe h) ∧ Type(N) = Nat ∧ isIntNatStrCst(pe')
                                                with pe' ← (removeNamedPatternExpr optimizer pe)
           := let n := Int.toNat e in t'        if p = Int.ofNat n
           := let n := Int.toNat e in (mkLet n pe t')  if p = Int.ofNat (namedPattern t n pe t) ∧ ¬ isIntNatStrCst(pe')
                                                       with pe' ← (removeNamedPatternExpr optimizer pe)
           := let n := pe' in (mkCstLet pe t')  if p = Int.ofNat (namedPattern t n pe t) ∧ isIntNatStrCst(pe')
                                                with pe' ← (removeNamedPatternExpr optimizer pe)
           := let n := Int.toNat e - N in t'  if p = Int.ofNat (N + n)
           := let n := Int.toNat e - N in (mkLet n pe t')  if p = Int.ofNat (N + namedPattern t n pe h) ∧ ¬ isIntNatStrCst(pe')
                                                           with pe' ← (removeNamedPatternExpr optimizer pe)
           := let n := pe' in (mkCstLet pe t')  if p = Int.ofNat (N + namedPattern t n pe h) ∧ isIntNatStrCst(pe')
                                                with pe' ← (removeNamedPatternExpr optimizer pe)
           := let n := (Int.toNat (Int.neg e)) - N in t'   if p = Int.Neg (Int.ofNat (N + n))
           := let n := (Int.toNat (Int.neg e)) - N in (mkLet n pe t')  if p = Int.Neg (Int.ofNat (N + namedPattern t n pe h)) ∧
                                                                          ¬ isIntNatStrCst(pe')
                                                                       with pe' ← (removeNamedPatternExpr optimizer pe)
           := let n := pe' in (mkCstLet n pe t')  if p = Int.Neg (Int.ofNat (N + namedPattern t n pe h)) ∧ isIntNatStrCst(pe')
                                                  with pe' ← (removeNamedPatternExpr optimizer pe)
           := (mkCstLet x₁ (.. (mkCstLet xₖ₋₁ (mkCstLet xₙ t')))) if p = C x₁ ... xₖ
           := ⊥  otherwise

       - mkCstLet e t :
           := t             if e = C
           := t             if isIntNatStrCst(e)
           := let n := removeNamedPatternExpr optimizer pe in (mkCstLet pe t) if e = namedPattern t n pe h
           := let n := removeNamedPatternExpr optimizer pe in (mkCstLet pe t) if e = N + (namedPattern t n pe h) ∧ Type(N) = Nat
           := (mkCstLet pe t)  if e = Int.ofNat pe
           := (mkCstLet pe t)  if e = Int.Neg pe
           := (mkCstLet x₁ (.. (mkCstLet xₖ₋₁ (mkCstLet xₙ t)))) if e = C x₁ ... xₖ
           := ⊥  otherwise
-/
def normMatchExpr?
  (f : Expr) (args : Array Expr)
  (optimizer : Expr -> TranslateEnvT Expr) : TranslateEnvT (Option Expr) := do
  let some mInfo ← isMatcher? (mkAppN f args) | return none
  if !(← hasDecidableEq mInfo) then return none
  matchExprRewriter mInfo optimizer (normMatchExprAux? optimizer)

  where
    /-- Determines if all discriminators has a DecidableEq instance -/
    hasDecidableEq (mInfo : MatchInfo) : TranslateEnvT Bool := do
     let eqOpExpr ← mkEqOp
     for i in mInfo.mInfo.getDiscrRange do
       let eqExpr := mkApp3 eqOpExpr (← inferType mInfo.args[i]!) mInfo.args[i]! mInfo.args[i]!
       if (← trySynthDecidableInstance? eqExpr).isNone then
         return false
     return true

initialize
  registerTraceClass `Optimize.normMatch.optPattern
  registerTraceClass `Optimize.normMatch.pattern

end Solver.Optimize
