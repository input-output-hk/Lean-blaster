import Lean
import Blaster.Smt.Env
import Blaster.Optimize.Basic

open Lean Meta Blaster.Optimize

namespace Blaster.Smt

/-- Removes an occurrence of type abbreviation in type expression `t` -/
partial def removeTypeAbbrev (te : Expr) : TranslateEnvT Expr := do
  let rec visit (te : Expr) (k : Expr → TranslateEnvT Expr) : TranslateEnvT Expr := do
    match te.getAppFn with
    | Expr.const _ _ => k (← resolveTypeAbbrev te)
    | e@(Expr.forallE _ t b bi) =>
         visit t
          (fun t' =>
             visit b
               (fun b' => k (Expr.updateForall! e bi t' b'))
          )
    | Expr.mdata _ d => visit d k
    | _ => k te
  visit te (fun e => pure e)

  -- /-- Map keeping track of visited inductive datatype during translation.
  --     An entry in this map is expected to be of the form `d := some pbody`,
  --     where `pbody` correspond to the body of the function predicate to qualify quantifiers
  --     for this inductive datatype.

  --     The body is defined only when the inductive datatype instance has at least
  --     one constructor whith a proposition argument. E.g.,
  --     Given the following inductive datatype
  --      inductive NatGroup where
  --      | first (n : Nat) (h1 : n ≥ 10) (h2 : n < 100) : NatGroup
  --      | second (n : Nat) (h1 : n > 100) (h2 : n < 200) : NatGroup
  --      | next (n : NatGroup)

  --     The entry in `indTypeMap` is the following:
  --       `NatGroup := some (ite (is-first x) (and (= (first.2 x) (<= 10 (first.1 x)))
  --                                           (and (= (first.3 x) (< (first.1 x) 100))
  --                                           (and (<= 10 (first.1 x)) (< (first.1 x) 100))))
  --                         (ite (is-second x) (and (= (second.2 x) (< 100 (second.1 x)))
  --                                            (and (= (second.3 x) (< (second.1 x) 200))
  --                                            (and (< 100 (second.1 x)) (< (second.1 x) 200))))
  --                                            true))`

  --     Note that any user-defined selectors for each constructor are replaced with generated ones during translation:
  --     E.g., `first (n : Nat) (h1 : n ≥ 10) (h2 : n < 100) ===> first (first.1 : Nat) (first.2 : n ≥ 10) (first.3 : n < 100)`
  --     Moreover, proposition arguments are replaced with boolean expressions.

  --     For each inductive datatype instance, a corresponding declared/defined qualifier predicate will be generated s.t.:
  --      - an uninterpreted predicate function will be generated when the entry in indTypeMap points to `none`, e.g.
  --         - (declare-fun isList_1 ((List Int)) Bool)
  --      - a defined predicate function will be generated when the entry in indTypeMap points to `some ..`, e.g.
  --         - (define-fun isNatGroup (x IsNatGroup) Bool
  --                       (ite (is-first x) (and (= (first.2 x) (<= 10 (first.1 x)))
  --                                         (and (= (first.3 x) (< (first.1 x) 100))
  --                                         (and (<= 10 (first.1 x)) (< (first.1 x) 100))))
  --                       (ite (is-second x) (and (= (second.2 x) (< 100 (second.1 x)))
  --                                          (and (= (second.3 x) (< (second.1 x) 200))
  --                                          (and (< 100 (second.1 x)) (< (second.1 x) 200))))
  --                                          true))
  -- -/

/-- Generate an smt symbol from a given Name. -/
def nameToSmtSymbol (n : Name) : SmtSymbol :=
  mkNormalSymbol s!"{n}"

/-- Generate a smt symbol for a free variable id corresponding to a sort name (e.g., α : Type) s.t.:
     - return smt symbol `"@" ++ v.getUserName ++ v.name` when `unique` is set to `true`
     - return smt symbol `"@" ++ v.getUserName` otherwise.
-/
def typeParamNameToSmtSymbol (v : FVarId) (unique := true) : TranslateEnvT SmtSymbol := do
  if unique
  then return mkNormalSymbol s!"@{← v.getUserName}{v.name}"
  else return mkNormalSymbol s!"@{← v.getUserName}"


/-- Generate an smt symbol from a given inductive type name. -/
def indNameToSmtSymbol (indName : Name) : SmtSymbol :=
  mkNormalSymbol s!"@{indName.toString}"


/-- Return `some b` if `e := mkAnnotation `__solver.ctorSelector b'`. -/
def toTaggedCtorSelector? (e : Expr) : Option Expr :=
 match e with
 | Expr.mdata d b =>
      if d.size == 1 && d.getBool `_solver.ctorSelector false
      then some b else none
 | _ => none

/-- Return `true` if `e := mkAnnotation `_solver.ctorSelector b'`. -/
def isTaggedCtorSelector (e : Expr) : Bool :=
 match e with
 | Expr.mdata d _ => d.size == 1 && d.getBool `_solver.ctorSelector
 | _ => false

/-- Given `ctor` a constructor name and `idx` corresponding to
    the index for one of the ctor's effective parameters,
    create the ctor selector symbol `ctor.idx`
-/
def mkCtorSelectorSymbol (ctor : Name) (idx : Nat) :=
  mkNormalSymbol s!"{ctor}.{idx}"


/-- Given `ctor` a constructor name and `idx` corresponding to the index for
    one of the ctor's arguments and `arg` the current ctor arg and `t` its corresponding type,
    perform the following:
      - add `{ctor}.idx := ← getFunEnvInfo arg` to `funCtorCache` when `isFunType t`
      - create expression `ctor.idx x` and tag it as a ctor selector.
      - create the corresponding smt term
      - return both as result
    The tag is used during translation.
-/
def mkCtorSelectorExpr (ctor : Name) (idx : Nat) (arg : Expr) (type : Expr) : TranslateEnvT (Expr × SmtTerm) := do
  let sctor := s!"{ctor}.{idx}".toName
  unless !(← isFunType type) do
    let pInfo ← getFunEnvInfo arg
    modify (fun env => {env with smtEnv.funCtorCache := env.smtEnv.funCtorCache.insert sctor pInfo})
  let selectorSym := mkCtorSelectorSymbol ctor idx
  let appExpr := mkApp (mkConst sctor) (mkConst "x".toName)
  let smtTerm := mkSimpleSmtAppN selectorSym #[smtSimpleVarId (mkReservedSymbol "@x")]
  return (mkAnnotation `_solver.ctorSelector appExpr, smtTerm)

/-- Given `ctor` a constructor name and an smt term `s`,
    create the smt term application `is-ctor s`.
-/
def mkCtorTestorTerm (ctor : Name) (s : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN (mkNormalSymbol s!"is-{ctor}") #[s]

/-- Given `ctor` a constructor name, create the smt term `is-ctor x`. -/
def mkGenericCtorTestorTerm (ctor : Name) : SmtTerm :=
   mkCtorTestorTerm ctor (smtSimpleVarId (mkReservedSymbol "@x"))

/-- Return `s` when `nbArity := s` exists in `arrowTypeArities`. Otherwise,
    perform the following:
     - let s := `@@ArrowT{nbArity}`
     - Add entry `nbArity := s` in arrowTypeArities
     - declare sort `(declare-sort s nbArity)`
     - return `s`
-/
def declareArrowTypeSort (nbArity : Nat) : TranslateEnvT SmtSymbol := do
  match (← get).smtEnv.options.arrowTypeArities.get? nbArity with
  | some s => return s
  | none =>
      let s := mkReservedSymbol s!"@@ArrowT{nbArity}"
      modify (fun env => { env with smtEnv.options.arrowTypeArities :=
                                    env.smtEnv.options.arrowTypeArities.insert nbArity s})
      declareSort s nbArity
      return s

/-- Add an inductive datatype name to the visited inductive datatype cache. -/
def cacheIndName (indName : Name) : TranslateEnvT Unit := do
  modify (fun env => { env with smtEnv.indTypeVisited := env.smtEnv.indTypeVisited.insert indName})


/-- Return `true` when `indName` is already in the visited inductive
    datatype cache (i.e., `indTypeCache`)
-/
def isVisitedIndName (indName : Name) : TranslateEnvT Bool :=
  return (← get).smtEnv.indTypeVisited.contains indName

/-- Given
      - `d` corresponding to a inductive datatype name expression, or an instantiated polymorphic inductive datatype,
           or a function instance declaration;
      - `n` a unique smt identifier generated for `d`;
      - `instSort` the instantiated Smt sort for `d`;
      - `applyInstName` optional `@apply{<UUID>}` function generated when `d` is a HOF function (see `generateFunInstDeclAux`)
      - `instInstanceSort` optional @Instance{<UUID>}` sort generated when `d` is a sort type with a specified type universe
         (see `generateSortInstDecl`).

    perform the following:
     - let decl := {instName := "@is{n}", instSort, instInstanceSort, applyInstName}`
     - Add entry `d := decl` in `indTypeInstCache`
     - return `decl`
-/
def updateIndInstCache
  (d : Expr) (n : SmtSymbol) (instSort : SortExpr)
  (isReservedSymbol := false) (applyInstName : Option SmtSymbol := none)
  (instInstanceSort : Option SortExpr := none) : TranslateEnvT IndTypeDeclaration := do
  let instName := if isReservedSymbol then mkReservedSymbol s!"@is{n}" else mkNormalSymbol s!"@is{n}"
  let decl := ({instName, instSort, instInstanceSort, applyInstName} : IndTypeDeclaration)
  modify (fun env => {env with smtEnv.indTypeInstCache := env.smtEnv.indTypeInstCache.insert d decl})
  return decl

/-- Return `true` if `v` is tagged as a top level free variable. -/
def isTopLevelFVar (v : FVarId) : TranslateEnvT Bool := do
  match (← get).smtEnv.quantifiedFVars.get? v with
  | none => return false
  | some b => return b


private partial def updateTopLevelVars (step : Nat) (vars : TopLevelVars) (s : SmtSymbol) (uname : Name) : TopLevelVars :=
 if h : step < vars.size
 then vars.set step ((s, uname) :: vars[step])
 else loop vars.size vars

 where
   loop (idx : Nat) (vars : TopLevelVars) : TopLevelVars :=
     if idx == step then vars.push [(s, uname)]
     else loop (idx + 1) (vars.push [])

/-- Perform the following:
      - add `v` to `quantifierFvars` cache
      - add `v` to `topLevelVars` only when topLevel is set to `true` and `¬ isTypeUniverse (← inferTypeEnv (mkFVar v))`.
-/
def updateQuantifiedFVarsCache (v : FVarId) (topLevel : Bool) : TranslateEnvT Unit := do
  let s ← fvarIdToSmtSymbol v
  let t ← inferTypeEnv (mkFVar v)
  let uname ← v.getUserName
  let idx ← getCurrentDepth
  modify
    (fun env =>
      let updatedVars := env.smtEnv.quantifiedFVars.insert v topLevel
      if topLevel && !(isTypeUniverse t)
      then
        { env with
              smtEnv.quantifiedFVars := updatedVars,
              smtEnv.topLevelVars := updateTopLevelVars idx env.smtEnv.topLevelVars s uname
        }
      else
        { env with smtEnv.quantifiedFVars := updatedVars }
    )

/-- Return `true` if `v` is in the quantified fvars cache. -/
def isInQuantifiedFVarsCache (v : FVarId) : TranslateEnvT Bool := do
  return (← get).smtEnv.quantifiedFVars.contains v

/-- Return `true` when an entry exists for `v` in `inPatternMatching`. -/
def isPatternMatchFVar (v : FVarId) : TranslateEnvT Bool := do
  return (← get).smtEnv.options.inPatternMatching.contains v

/-- Return an Smt Array sort when args.size > 1.
    Otherwise return args[0]!.
    An error is triggered when args.size < 1.
-/
def createSortExpr (args : Array SortExpr) : TranslateEnvT SortExpr := do
  if args.size < 1 then throwEnvError "createSortExpr: args size expected to be ≥ 1"
  if h : args.size = 1 then return args[0]
  return (arraySort args)


/-- Given `n` corresponding to the name of an inductive datatype, and `x₀ ... xₖ` the parameters instantiating
    the inductive datatype, perform the following actions:
     - When k > 0:
         let A := [x₀, ..., xₖ]
         let B := [typeTranslator A[i] | i ∈ [0..k] ∧ ¬ isClassConstraintExpr (← inferTypeEnv A[i])]
          - return `ParamSort (indNameToSmtSymbol n) B`
     - When k = 0:
        - return `SymbolSort indNameToSmtSymbol n)`
-/
def generateInstType
  (indName : Name) (args : Array Expr)
  (typeTranslator : Expr → TranslateEnvT SortExpr) : TranslateEnvT SortExpr := do
 let indSym := indNameToSmtSymbol indName
 if args.size == 0 then return .SymbolSort indSym
 let mut iargs := #[]
 for h : i in [:args.size] do
   if !(← isClassConstraintExpr (← inferTypeEnv args[i])) then -- ignore class constraints
     iargs := iargs.push (← typeTranslator args[i])
 return (.ParamSort indSym iargs)

/-- Given arguments `x₀ ... xₙ` perform the following:
      let A := [x₀, ..., xₙ]
      let V := {α | i ∈ [0..n] ∧ α ∈ getFVarsInExpr A[i] ∧ isGenericParam A[i]}
      return `[α | α ∈ V]`
-/
def retrieveGenericArgs (args : Array Expr) : TranslateEnvT (Array Expr) := do
  let mut genericArgs := #[]
  let mut knownGenParams := (.emptyWithCapacity : Std.HashSet Expr)
  for h : i in [:args.size] do
    let e := args[i]
    if (← isGenericParam e) then
      (genericArgs, knownGenParams) ← updateGenericArgs e genericArgs knownGenParams
  return genericArgs

/-- Same as getIndInst but also returns the generic arguments -/
@[always_inline, inline]
def getIndInst' (t : Expr) (args : Array Expr) : TranslateEnvT (Expr × Array Expr) := do
  let genericArgs ← retrieveGenericArgs args
  let auxApp := mkAppN t args
  return (← mkLambdaFVars genericArgs auxApp (usedOnly := true), genericArgs)

/-- Given an inductive datatype instance `t x₀ ... xₙ`, perform the following:
     - When `∀ i ∈ [0..n], ¬ isGenericParam xᵢ`,
         - return `t x₀ ... xₙ`
     - When `∃ i ∈ [0..n], isGenericParam xᵢ`,
        let A := [x₀, ..., xₙ]
        let V := [α | i ∈ [0..n] ∧ α ∈ getFVarsInExpr A[i] ∧ isGenericParam A[i] ]
        let [b₀ ... bₘ ] := V
          - return `λ b₀ → .. → bₘ → t x₀ ... xₙ`
-/
def getIndInst (t : Expr) (args : Array Expr) : TranslateEnvT Expr :=
  return (← getIndInst' t args).1

/-- Given `t := ∀ α₀ → ∀ α₁ ... → αₙ` returns #[α₀, α₁ ..., αₙ].
    Assumes that `t` no more contains any class constraints (see function `removeClassConstraintsInFunType`).
-/
def retrieveArrowTypes (t : Expr) : Array Expr :=
 let rec visit (e : Expr) (arrowTypes : Array Expr) : Array Expr :=
   match e with
   | Expr.forallE _ t b _ => visit b (arrowTypes.push t)
   | _ => arrowTypes.push e
 visit t #[]


/-- Given `t := Expr.sort _` perform the following actions:
     - When `t := decl ∈ IndTypeDeclaration`
         - return `decl`
     - Otherwise:
         - When `t := Expr.sort .zero`
            - let decl := {@isProp, propSort, none}
            - add entry `t := decl to `indTypeInstCache`
            - define smt sort `(define-sort Prop () Bool)`
            - declare smt predicate `(declare-fun @isProp ((Prop)) Bool)` with `true` assertion
            - return `decl`
         - Otherwise
            - let n ← mkFreshId
            - let typeName := "@Type{n}"
            - let instTypeName := "@Instance{n}"
            - let typeSort := .SymbolSort typeName
            - let instTypeSort := .SymbolSort instTypeName
            - let decl := {@isInstance{n}, typeSort, some instTypeSort, none}
            - add entry `t := decl to `indTypeInstCache`
            - declare smt sort `(declare-sort typeName 0)`
            - declare smt sort `(declare-sort instTypeSort 0)`
            - declare smt predicate `(declare-fun @isInstance{n} (((instSort typeSort)) Bool)`
            - return `decl`

    An error is triggered when t is not the expected sort type.
-/
def generateSortInstDecl (t : Expr) : TranslateEnvT IndTypeDeclaration := do
 let Expr.sort u := t | throwEnvError "generateSortInstDecl: sort type expected but got {reprStr t}"
  match (← get).smtEnv.indTypeInstCache.get? t with
   | some decl => return decl
   | none =>
      match u with
      | .zero =>
          let decl ← updateIndInstCache t propSymbol propSort (isReservedSymbol := true)
          definePropSort decl.instName
          return decl
      | _ =>
        let n ← mkFreshId
        let typeName := mkReservedSymbol s!"@Type{n}"
        let instTypeName := mkReservedSymbol s!"@Instance{n}"
        let instName := mkReservedSymbol s!"Instance{n}"
        let typeSort := .SymbolSort typeName
        let instTypeSort := .SymbolSort instTypeName
        let decl ← updateIndInstCache t instName typeSort (isReservedSymbol := true) (instInstanceSort := some instTypeSort)
        defineTypeSort typeName instTypeName decl
        return decl

/-- Given `t := ∀ α₀ → ∀ α₁ ... → αₙ`, perform the following:
     - let A := [αᵢ | i ∈ [0..n-1], isClassConstraintExpr αᵢ]
     - let [α'₀ ... α'ₚ] := A
     - return ∀ α'₀ → α'₁ → ... → α'ₚ → αₙ`
-/
def removeClassConstraintsInFunType (t : Expr) : TranslateEnvT Expr :=
  Optimize.forallTelescope t fun fvars body => do
    let mut xs := #[]
    for h : i in [:fvars.size] do
      let decl ← getFVarLocalDecl fvars[i]
      if !(← isClassConstraintExpr decl.type) then
        xs := xs.push fvars[i]
    Optimize.mkForallFVars' xs body

/-- Given #[fv₀, ..., fvₙ] an array of generic parameters perform the following:
     - [(svᵢ, stᵢ) | i ∈ [0..,n], isTypeUniverse (← inferTypeEnv fvᵢ) ∧
                    svᵢ = typeParamNameToSmtSymbol fvᵢ (unique := !inPredQualifier ∧
                    declᵢ = generateSortInstDecl (← inferTypeEnv fvᵢ)
                    stᵢ = declᵢ.instSort
       ]
    Assumes that fv₀, ..., fvₙ are FVar expressions.
-/
def genericArgsToSortedVars (fvars : Array Expr) (inPredQualifier := false) : TranslateEnvT SortedVars := do
  let mut svars := (#[] : SortedVars)
  for h : i in [:fvars.size] do
    let v := fvars[i]
    let fdecl ← getFVarLocalDecl v
    if (isTypeUniverse fdecl.type) then -- only considering polymorphic types
      let decl ← generateSortInstDecl fdecl.type
      let smtSym ← typeParamNameToSmtSymbol v.fvarId! (unique := !inPredQualifier)
      svars := svars.push (smtSym, decl.instSort)
  return svars

/-- Given `t := Expr.const n _` corresponding to an inductive datatype name and
    `args` the parameters instantiating the inductive datatype (if any),
    perform the following actions:
     - When args.size > 0:
         - instName := nameToSmtSymbol (n ++ (← mkFreshId)) (i.e., generate a unique name for instance)
         - instSort ← generateInstType n args typeTranslator
         - instApp ← getIndInst t args
         - add entry `instApp := {@is{instName}, instSort}` to `indTypeInstCache`
         - When declarePredicate
            - let V := {α | i ∈ [0..args.size-1] ∧ α ∈ getFVarsInExpr args[i] ∧ isGenericParam args[i] ∧ isTypeUniverse (← inferTypeEnv α)}
            - let [gt₀ ... gtₘ] := [typeTranslator V[i] | i ∈ [0..V.size-1]]
            - When `assertFlag := some b`:
                - define smt predicate `(define-fun @is{instName} ((@t₀ gt₀) .. (@tₘ gtₘ) (@x instSort)) Bool b)`
            - Otherwise:
                - declare smt predicate `(declare-fun @is{instName} ((gt₀) .. (gtₘ) (instSort)) Bool)`
         - return {instName, instSort}
    - When args.size = 0:
        - instName := nameToSmtSymbol n
        - instSort ← generateInstType n args typeTranslator
        - add entry `t := {@is{instName}, instSort}` to `indTypeInstCache`
        - When declarePredicate:
            - When `assertFlag := some b`:
                - define smt predicate `(define-fun @is{instName} ((@x instSort)) Bool b)`
            - Otherwise:
                - declare smt predicate `(declare-fun @is{instName} ((instSort)) Bool)`
        - return `{instName, instSort}`
    Assumes that `t` corresponds to the name of an inductive datatype.
-/
def generateIndInstDecl
  (t : Expr) (args : Array Expr) (assertFlag : Option Bool)
  (typeTranslator : Expr → TranslateEnvT SortExpr) (declarePredicate := true) :
  TranslateEnvT IndTypeDeclaration := do
 let Expr.const n _ := t | throwEnvError "generateIndInstDecl: name expression expected but got {reprStr t}"
 let instSort ← generateInstType n args typeTranslator
 if args.size == 0
 then
   let instName := nameToSmtSymbol n
   let decl ← updateIndInstCache t instName instSort
   if declarePredicate then definePredQualifier decl.instName #[decl.instSort] assertFlag
   return decl
 else
   let v ← mkFreshId
   let instName := nameToSmtSymbol (n ++ v)
   let (instApp, genArgs) ← getIndInst' t args
   let decl ← updateIndInstCache instApp instName instSort
   if declarePredicate then
     let sargs ← genericArgsToSortedVars genArgs (inPredQualifier := true)
     let genSorts := sargs.map (λ s => s.2)
     definePredQualifier decl.instName (genSorts.push decl.instSort) assertFlag
   return decl


/-- Given `t := ∀ α₀ → ∀ α₁ ... → αₙ`, perform the following:
     Let A := [αᵢ | i ∈ [0..n-1]]
     - When `∀ i ∈ [0..n], ¬ isGenericParam A[i]`,
         - return `t`
     - When `∃ i ∈ [0..n], isGenericParam A[i]`,
        let V := {v | i ∈ [0..n] ∧ v ∈ getFVarsInExpr A[i] ∧ isGenericParam A[i]}
        let B := [v | v ∈ V] ++ [A[i] | i ∈ [0..n] ∧ isGenericParam A[i]]
        let [b₀ ... bₘ ] := B
        let [α'₀ ... α'ₚ] := A
          - return `λ b₀ → .. → bₘ → ∀ α'₀ → α'₁ → ... → α'ₚ → αₙ`
    Assumes that `t` does not have any implicit types (i.e., removeClassConstraintsInFunType called)
-/
def getFunInstDeclAux (t : Expr) : TranslateEnvT Expr := do
  let genericArgs ← retrieveGenericArgs (retrieveArrowTypes t)
  mkLambdaFVars' genericArgs t

/-- Same as `getFunInstDeclAux` but calls `removeClassConstraintsInFunType on `t` first. -/
def getFunInstDecl (t : Expr) : TranslateEnvT Expr := do
  let t' ← removeClassConstraintsInFunType t
  getFunInstDeclAux t'


/-- Given `t := ∀ α₀ → ∀ α₁ ... → αₙ`, execute k t', with t' obtained as follows:
     - let [α'₀ ... α'ₚ] := [αᵢ | i ∈ [0..n-1], isExplicit αᵢ]
     - t' := ∀ α'₀ → α'₁ → ... → α'ₚ → αₙ`
     - with free variables created for implicit arguments.
-/
def withInstantiatedImplicitArgs (t : Expr) (k : Expr → TranslateEnvT α) : TranslateEnvT α :=
 Optimize.forallTelescope t fun fvars body => do
   let mut explicitArgs := #[]
   for h : i in [:fvars.size] do
     let v := fvars[i]
     let decl ← getFVarLocalDecl v
     -- Need to consider case when fun type has implicit sort type arguments (see `Issue15.thm4`)
     if decl.binderInfo.isExplicit then
       explicitArgs := explicitArgs.push v
   let t' ← Optimize.mkForallFVars' explicitArgs body -- keeping implicit arguments instantiated
   k t'

/-- Same as withInstantiatedImplicitArgs but also passes the instantiated implicit arguments to k. -/
def withInstantiatedImplicitArgs' (t : Expr) (k : Std.HashSet Expr → Expr → TranslateEnvT α) : TranslateEnvT α :=
 Optimize.forallTelescope t fun fvars body => do
   let mut explicitArgs := #[]
   let mut implicitArgs := Std.HashSet.emptyWithCapacity
   for h : i in [:fvars.size] do
     let v := fvars[i]
     let decl ← getFVarLocalDecl v
     -- Need to consider case when fun type has implicit sort type arguments (see `Issue15.thm4`)
     if decl.binderInfo.isExplicit then
       explicitArgs := explicitArgs.push v
     else
       implicitArgs := implicitArgs.insert v
   let t' ← Optimize.mkForallFVars' explicitArgs body -- keeping implicit arguments instantiated
   k implicitArgs t'

/-- Canonicalize a parameterized indexed type's `Nat` bound to a raw literal so
    that cache writes and reads agree regardless of how the bound was elaborated:
    a raw `Nat` literal, `@OfNat.ofNat Nat n _`, or `Expr.proj OfNat 0 …` (the
    form a reverted hypothesis binder carries). This is the single source of
    truth for the indexed-type cache key — both `translate{Fin,BitVec,Vector}Type`
    (write) and `getPredicateDeclaration` (read) route through it.

    Non-indexed types, and indexed types whose bound is not a literal after
    `whnf`, are returned unchanged (the per-type translators surface their own
    "non-literal bound" errors). -/
def canonicalizeIndexedType (t : Expr) : TranslateEnvT Expr := do
  match t.getAppFn with
  | Expr.const ``Fin _ | Expr.const ``BitVec _ =>
      let args := t.getAppArgs
      if args.size == 1 then
        match isNatValue? (← whnf args[0]!) with
        | some n => return mkApp t.getAppFn (mkLit (Literal.natVal n))
        | none => return t
      else return t
  | Expr.const ``Vector _ =>
      let args := t.getAppArgs
      if args.size == 2 then
        match isNatValue? (← whnf args[1]!) with
        | some n => return mkApp (mkApp t.getAppFn args[0]!) (mkLit (Literal.natVal n))
        | none => return t
      else return t
  | _ => return t

/-- Return `decl.instName` when `t := decl` exists in `indTypeInstCache`.
    Otherwise `none`.
    TODO: UPDATE
-/
def getPredicateDeclaration (t : Expr) : TranslateEnvT (Option IndTypeDeclaration) := do
  let t' ← getType t
  -- Canonicalize the indexed-type bound so the lookup key matches the canonical
  -- key written by translate{Fin,BitVec,Vector}Type (else a proj-form bound from
  -- a reverted hypothesis binder misses the cache).
  let typeInst ← getInst (← canonicalizeIndexedType t')
  return (← get).smtEnv.indTypeInstCache.get? typeInst

 where
  getInst (e : Expr) : TranslateEnvT Expr := do
    if e.isForall then
      withInstantiatedImplicitArgs e fun t => do
        getFunInstDecl t -- arrow type case
    else
      let (f, args) := getAppFnWithArgs e
      if args.size == 0
      then return f
      else getIndInst f args

  getType (e : Expr) : TranslateEnvT Expr := do
   match e with
   | Expr.fvar _ => inferTypeEnv e
   | _ => pure e


/-- Return `n` only when entry `t := decl` exists in `indTypeInstCache` and
    `decl.applyInstName := some n`.
    An error is triggered when:
     - no entry exist for `t`
     - decl.applyInstName is set to `none`.
-/
def getApplyInstName (t : Expr) : TranslateEnvT SmtSymbol := do
  match ← getPredicateDeclaration t with
  | none => throwEnvError "getApplyInstName: declaration instance expected for {reprStr t} !!!"
  | some decl =>
      let some n := decl.applyInstName |
        throwEnvError "getApplyInstName: @apply instance function expected to be defined for {reprStr t} !!!"
      return n

/-- Given `st` an smt term and `t` its corresponding type expression, `decl` its inductive type declaration,
    perform the following:
      - When `decl.instInstanceSort = none`
        - When t := `∀ α₀ → .. → αₙ` (i.e., function type)
           - When inPredQualifier
               - let (implicits, ∀ β₀ → .. → βₖ) ← withInstantiatedimplicitArgs' t
               - let V := {v | v ∈ getFVarsInExpr βₖ ∧ isGenericParam βₖ}
               - let [(sv₀, st₀), ..., (svₖ, stₖ)] := genericArgsToSortedVars V inPredQualifier
               - let localGenArgs ← getLocalPolymorphicTypes V implicits
               - When localGenArgs.isEmpty
                  - return `(mkSimpleSmtAppN decl.instName #[sv₀, ..., svₖ, st])`
               - Otherwise: (i.e., case when constructors has local polymorphic types (see Issue15.lean)
                   - let (gv₀, gt₀), ..., (gvₖ, gtₖ) := genericArgsToSortedVars localGenArgs inPredQualifier
                   - `return (forall ((gv₀, gt₀) ... (gvₖ, gtₖ)) (mkSimpleSmtAppN decl.instName #[sv₀, ..., svₖ, st]))`
           - Otherwise:
               - let V := {v | v ∈ getFVarsInExpr αₙ ∧ isGenericParam αₙ}
               - let [(sv₀, st₀), ..., (svₖ, stₖ)] := genericArgsToSortedVars V
               - return `(mkSimpleSmtAppN decl.instName #[sv₀, ..., svₖ, st])`

        - When t := D x₀ .. xₙ (i.e., an instantiated inductive data type)
            - let V := {α | i ∈ [0..n] ∧ α ∈ getFVarsInExpr xᵢ ∧ isGenericParam xᵢ}
            - let [(sv₀, st₀), ..., (svₖ, stₖ)] := genericArgsToSortedVars V inPredQualifier
            - return `(mkSimpleSmtAppN decl.instName #[sv₀, ..., svₖ, st])`

        - Otherwise (i.e., case for non-parameteric inductive datatype)
             return `(mkSimpleSmtAppN decl.instName #[st])`

      - Otherwise:
          - When t.isFVar (i.e, return @isInstance_<UUID> application)
                 - return `(mkSimpleSmtAppN decl.instName #[st, smtSimpleVarId (← typeParamNameToSmtSymbol t.fvarId! (unique := !inPredQualifier)))])`
          - Otherwise:
              - return ⊥

    Assume that there is no type abbreviation in `t`, i.e., call to `removeTypeAbbrev` has been applied.
-/

def createPredQualifierAppAux'
  (st : SmtTerm) (t : Expr) (decl : IndTypeDeclaration)
  (inPredQualifier := false) : TranslateEnvT SmtTerm := do
  if decl.instInstanceSort.isNone then
    match t with
    | Expr.forallE .. =>
        -- arrow type case
        if inPredQualifier then
          -- case when polymorphic type instance (if any) is local
          withInstantiatedImplicitArgs' t fun implicits t' => do
            let genArgs ← retrieveGenericArgs (getReturnType t')
            let sargs ← genericArgsToSortedVars genArgs inPredQualifier
            let localGenArgs ← getLocalPolymorphicTypes genArgs implicits
            let appTerm := mkSimpleSmtAppN decl.instName ((sargs.map (λ s => smtSimpleVarId s.1)).push st)
            if localGenArgs.isEmpty then
              return appTerm
            else
              let quantifiers ← genericArgsToSortedVars localGenArgs inPredQualifier
              return mkForallTerm none quantifiers appTerm none
        else
          -- NOTE: When inPreqQualifier is set to false, it is assumed that all types in t are
          -- fully instantiated (i.e., no bounded loose variables)
          -- case when polymorphic type instance (if any) is global
          let sargs ← genericArgsToSortedVars (← retrieveGenericArgs (getReturnType t))
          return mkSimpleSmtAppN decl.instName ((sargs.map (λ s => smtSimpleVarId s.1)).push st)
    | Expr.app .. =>
        -- instantiated inductive data type case
        let sargs ← genericArgsToSortedVars (← retrieveGenericArgs t.getAppArgs) inPredQualifier
        return mkSimpleSmtAppN decl.instName ((sargs.map (λ s => smtSimpleVarId s.1)).push st)

    | _ => return mkSimpleSmtAppN decl.instName #[st]
  else
    let Expr.fvar v := t
         | throwEnvError "createPredQualifierAppAux: FVarExpr expected for polymorphic type but got {reprStr t}"
    return (mkSimpleSmtAppN decl.instName #[st, smtSimpleVarId (← typeParamNameToSmtSymbol v (unique := !inPredQualifier))])

  where
    @[always_inline, inline]
    getReturnType (t : Expr) : Array Expr :=
      let funTypes := retrieveArrowTypes t
      let retIdx := funTypes.size - 1
      #[removeOutParam funTypes[retIdx]!]

    @[always_inline, inline]
    getLocalPolymorphicTypes (genArgs : Array Expr) (implicits : Std.HashSet Expr) : TranslateEnvT (Array Expr) := do
      let mut localArgs := #[]
      for h : i in [:genArgs.size] do
        let v := genArgs[i]
        if implicits.contains v then
          localArgs := localArgs.push v
      return localArgs

/-- Given `st` an smt term and `t` its corresponding type expression, perform the following:
      When some decl ← getPredicateDeclaration t:
         - When decl.instInstanceSort.isNone
            - return `(mkSimpleSmtAppN decl.instName #[st])`
         - Otherwise:
             - When t.isFVar (i.e, return @isInstance_<UUID> application)
                 - return `(mkSimpleSmtAppN decl.instName #[st, smtSimpleVarId (← typeParamNameToSmtSymbol t.fvarId!)])`
             - Otherwise:
                - return ⊥
      Otherwise:
         - return ⊥
    Assume that there is no type abbreviation in `t`, i.e., call to `removeTypeAbbrev` has been applied.
-/
def createPredQualifierAppAux (st : SmtTerm) (t : Expr) (inPredQualifier := false) : TranslateEnvT SmtTerm := do
  let some decl ← getPredicateDeclaration t
    | throwEnvError "createPredQualifierAppAux: predicate declaration expected for {reprStr t}"
  createPredQualifierAppAux' st t decl inPredQualifier

/-- Same as `createPredQualifierAppAux` but accepts an SmtSymbol as argument. -/
def createPredQualifierApp (smtSym : SmtSymbol) (t : Expr) (inPredQualifier := false) : TranslateEnvT SmtTerm :=
  createPredQualifierAppAux (smtSimpleVarId smtSym) t inPredQualifier


/-- Given `t := α₁ → α₂ ... → αₙ` and `st` its corresponding smt representation (i.e., ArrowTN sα₁ sα₂ sαₙ),
    perform the following action:
      - let funInst ← getFunInstDecl t
      - When funInst := {@is{instName}, st, applyInstName} ∈ indTypeInstCache
         - return `{@is{instName}, st, applyInstName}`
      - Otherwise:
         - let n ← mkFreshId
         - let instName := Fun ++ n (i.e., generate a unique name for function instance)
         - add entry `t := {@is{instName}, st, applyInstName := some @apply{n}}` to `indTypeInstCache`
         - let R := {v | v ∈ getFVarsInExpr (removeOutparam αₙ) ∧ isGenericParam (removeOutparam αₙ) ∧ isTypeUniverse (← inferTypeEnv v)}
         - let [rt₀ ... rtₖ] := [typeTranslator R[i] | i ∈ [0..V.size]]
         - let V := {v | i ∈ [0..n-1] ∧ v ∈ getFVarsInExpr αᵢ ∧ isGenericParam αᵢ ∧ isTypeUniverse (← inferTypeEnv v)}
         - let [gt₀ ... gtₘ] := [typeTranslator V[i] | i ∈ [0..V.size]]
         - declare smt predicate `(declare-fun @is{instName} ((rt₀) .. (rtₖ) (instSort)) Bool)`
         - declare apply function `(declare-fun @apply{n} (st sα₁ ... sαₙ₋₁) sαₙ)`
         - assert the following propositions to specify congruence, extensionality and codomain value constraints:
            - `(assert (forall ((@t₀ gt₀) ... (@tₘ gtₘ) (@r₀ rt₀) ... (@rₖ rtₖ) (@f (ArrowTN sα₁ sα₂ sαₙ))
                                (@x₁ sα₁) ... (@xₙ₋₁ sαₙ₋₁) (@y₁ sα₁) ... (@yₙ₋₁ sαₙ₋₁))
               (! (=> (@is{instName} @r₀ ... @rₖ @f)
                  (=> (@isType₁ @x₁)
                  ...
                  (=> (@isTypeₙ₋₁ @xₙ₋₁)
                  (=> (@isType₁ @y₁)
                  ...
                  (=> (@isTypeₙ₋₁ @yₙ₋₁)
                  (=> (= @x₁ @y₁)
                  (=> (= @x₂ @y₂)
                  ...
                  (=> (= @xₙ₋₁ @yₙ₋₁)
                      (= (@apply{n} @f @x₁ ... @xₙ₋₁) (@apply{n} @f @y₁ ... @yₙ₋₁))))))))))
                  :qid @apply{n}_congr_args)))`

            - `(assert (forall ((@t₀ gt₀) ... (@tₘ gtₘ) (@r₀ rt₀) ... (@rₖ rtₖ) (@f (ArrowTN sα₁ sα₂ sαₙ)) (@g (ArrowTN sα₁ sα₂ sαₙ)))
               (! (=> (@is{instName} @r₀ ... @rₖ @f)
                  (=> (@is{instName} @r₀ ... @rₖ @g)
                  (=> (= @f @g)
                    (forall ((@x₁ sα₁) ... (@xₙ₋₁ sαₙ₋₁))
                      (=> (@isType₁ @x₁)
                      ...
                      (=> (@isTypeₙ₋₁ @xₙ₋₁)
                          (= (@apply{n} @f @x₁ ... @xₙ₋₁) (@apply{n} @g @x₁ ... @xₙ₋₁))))))))
                  :qid @apply{n}_congr_fun)))`

            - `(assert (forall ((@t₀ gt₀) ... (@tₘ gtₘ) (@r₀ rt₀) ... (@rₖ rtₖ) (@f (ArrowTN sα₁ sα₂ sαₙ)) (@g (ArrowTN sα₁ sα₂ sαₙ)))
                 (! (=> (@is{instName} @r₀ ... @rₖ @f)
                    (=> (@is{instName} @r₀ ... @rₖ @g)
                    (=> (forall ((@x₁ sα₁) ... (@xₙ₋₁ sαₙ₋₁))
                         (=> (@isType₁ @x₁)
                          ...
                         (=> (@isTypeₙ₋₁ @xₙ₋₁)
                           (= (@apply{n} @f @x₁ ... @xₙ₋₁) (@apply{n} @g @x₁ ... @xₙ₋₁)))))
                        (= @f @g))))
                    :qid @apply{n}_ext_fun)))`

            - `(assert (forall ((@r₀ rt₀) ... (@rₖ rtₖ) (@f (ArrowTN sα₁ sα₂ ... sαₙ)))
                (! (= (forall ((@x₁ sα₁) ... (@xₙ₋₁ sαₙ₋₁)) (@isTypeₙ (@apply{n} @f @x₁ ... @xₙ₋₁)))
                      (@is{instName} @r₀ ... @rₖ @f) )
                   :pattern ( (@is{instName} @r₀ ... @rₖ @f)) :qid @isFun{v}_cstr)))`

            - with ∀ i ∈ [1..n] = s
         - return `{@is{instName}, st}`
-/
def generateFunInstDeclAux (t : Expr) (st : SortExpr) : TranslateEnvT IndTypeDeclaration := do
  let t' ← removeClassConstraintsInFunType t
  let funInst ← getFunInstDeclAux t'
  match ((← get).smtEnv.indTypeInstCache.get? funInst) with
   | some decl => return decl
   | none =>
       let v ← mkFreshId
       let instName := mkReservedSymbol s!"Fun{v}"
       let applyName := mkReservedSymbol s!"@apply{v}"
       let decl ← updateIndInstCache funInst instName st (applyInstName := some applyName)
       generateApplyFunAndAssertions t' decl applyName
       return decl

  where

    generateApplyFunAndAssertions (t : Expr) (decl : IndTypeDeclaration) (applyName : SmtSymbol) : TranslateEnvT Unit := do
     let funTypes := retrieveArrowTypes t
     let .ParamSort _ smtTypes := st | throwEnvError "defineFunAssertions: ParamSort expected but got {st}"
     let nbTypes := funTypes.size - 1
     -- declare @isFun predicate qualifier
     -- Need to remove outParam on return type (if necessary) (see, translateLambda)
     let retType := removeOutParam funTypes[nbTypes]!
     let rt_args ← genericArgsToSortedVars (← retrieveGenericArgs #[retType]) (inPredQualifier := true)
     let sargs ← genericArgsToSortedVars (← retrieveGenericArgs $ funTypes ++ #[retType]) (inPredQualifier := true)
     let genSorts := rt_args.map (λ s => s.2)
     definePredQualifier decl.instName (genSorts.push decl.instSort) none
     -- declare apply function `(declare-fun @apply{n} (st sα₁ ... sαₙ₋₁) sαₙ)`
     let declArgs := Array.foldl (λ acc s => acc.push s) #[st] smtTypes (stop := smtTypes.size - 1)
     declareFun applyName declArgs smtTypes[nbTypes]!
     let fsym := mkReservedSymbol "@f"
     let fId := smtSimpleVarId fsym
     let gsym := mkReservedSymbol "@g"
     let gId := smtSimpleVarId gsym
     let xsyms := Array.ofFn (λ f : Fin nbTypes => mkReservedSymbol s!"@x{f.val}")
     let xIds := Array.map (λ s => smtSimpleVarId s) xsyms
     let ysyms := Array.ofFn (λ f : Fin nbTypes => mkReservedSymbol s!"@y{f.val}")
     let yIds := Array.map (λ s => smtSimpleVarId s) ysyms
     let f_applyTerm1 := mkSimpleSmtAppN applyName (#[fId] ++ xIds)
     let f_applyTerm2 := mkSimpleSmtAppN applyName (#[fId] ++ yIds)
     let g_applyTerm := mkSimpleSmtAppN applyName (#[gId] ++ xIds)
     let mut co_quantifiers := (#[] : SortedVars)
     let mut arg_quantifiers := sargs.push (fsym, st)
     let mut forallCFunBody := eqSmt f_applyTerm1 f_applyTerm2
     let mut innerForallBody := eqSmt f_applyTerm1 g_applyTerm
     for i in [:nbTypes] do
       let idx := nbTypes - i - 1
       let predAppX ← createPredQualifierAppAux xIds[idx]! funTypes[idx]! (inPredQualifier := true)
       let predAppY ← createPredQualifierAppAux yIds[idx]! funTypes[idx]! (inPredQualifier := true)
       let eqPremise := eqSmt xIds[idx]! yIds[idx]!
       forallCFunBody := impliesSmt eqPremise forallCFunBody
       forallCFunBody := impliesSmt predAppY forallCFunBody
       forallCFunBody := impliesSmt predAppX forallCFunBody
       innerForallBody := impliesSmt predAppX innerForallBody
       co_quantifiers := co_quantifiers.push (xsyms[i]!, smtTypes[i]!)
       arg_quantifiers := (arg_quantifiers.push (xsyms[i]!, smtTypes[i]!)).push (ysyms[i]!, smtTypes[i]!)
     -- isFun constraint
     let forallCoBody ← createPredQualifierAppAux f_applyTerm1 retType (inPredQualifier := true)
     let forallCoDomain := mkForallTerm none co_quantifiers forallCoBody none
     let rt_args_vIds := rt_args.map (λ s => smtSimpleVarId s.1)
     let f_funPredApp := mkSimpleSmtAppN decl.instName (rt_args_vIds.push fId)
     let g_funPredApp := mkSimpleSmtAppN decl.instName (rt_args_vIds.push gId)
     let forallFunBody := eqSmt forallCoDomain f_funPredApp
     let qidName := appendSymbol decl.instName "cstr"
     let fun_annotations := some #[mkPattern #[f_funPredApp], mkQid qidName]
     assertTerm (mkForallTerm none (rt_args.push (fsym, st)) forallFunBody fun_annotations)
     -- congruence on fun
     let qidName := appendSymbol applyName "congr_ext_fun"
     let eqFun := eqSmt fId gId
     let fg_quantifiers : SortedVars := (sargs.push (fsym, st)).push (gsym, st)
     let innerForall := mkForallTerm none co_quantifiers innerForallBody none
     let forallCArgBody := impliesSmt f_funPredApp (impliesSmt g_funPredApp (impliesSmt eqFun innerForall))
     assertTerm (mkForallTerm none fg_quantifiers forallCArgBody (some #[mkQid qidName]))
     -- extensionality
     let qidName := appendSymbol applyName "ext_fun"
     let forallExtBody := impliesSmt f_funPredApp (impliesSmt g_funPredApp (impliesSmt innerForall eqFun))
     assertTerm (mkForallTerm none fg_quantifiers forallExtBody (some #[mkQid qidName]))
     -- congruence on args
     let qidName := appendSymbol applyName "congr_args"
     forallCFunBody := impliesSmt f_funPredApp forallCFunBody
     assertTerm (mkForallTerm none arg_quantifiers forallCFunBody (some #[mkQid qidName]))


/-- Same as `generateFunInstDeclAux` but return (). -/
@[always_inline, inline]
def generateFunInstDecl (t : Expr) (st : SortExpr) : TranslateEnvT Unit :=
  discard $ generateFunInstDeclAux t st


def getInstanceSort (decl : IndTypeDeclaration) : TranslateEnvT SortExpr := do
  match decl.instInstanceSort with
  | none => throwEnvError "getInstanceSort: instance type sort expected !!!"
  | some t => return t

/-- TODO: UPDATE SPEC -/
def getRecRuleFor (recVal : RecursorVal) (c : Name) : TranslateEnvT RecursorRule :=
   match (recVal.rules.find? fun r => r.ctor == c) with
    | some r => return r
    | none => throwEnvError "getRecRuleFor: no RecursorRule found for {c}"

/-- Options for translateType. -/
structure TypeOptions where
  /-- flag set to `true` only when translating an inductive datatype
      so as not to generate predicate qualifier for generic types
     used in ctor parameters.
  -/
  inTypeDefinition : Bool := false
deriving Inhabited

/-- type options to be used when translating inductive datatype. -/
def optionsForInductiveType : TypeOptions :=
  { inTypeDefinition := true}

/-- TODO: UPDATE SPEC

Given `indValStart` an inductive value info for an inductive datatype,
    update the inductive datatype declaration `indTypeMap`.
    Intuitively, for the non-mutual inductive `List`,
      inductive List (α : Type u) where
      | nil : List α
      | cons (head : α) (tail : List α) : List α

     The following entry will be added.
     `List :=
           [{ indName := List,
              numParams := 1,
              hasProp := false
              ctors := [ { ctorName := nil,
                           nbFields := 0,
                           hasProp := false,
                           propIndices := [],
                           rhs := λ α : Type u → nil
                         },
                         { ctorName := cons,
                           nbFields := 2,
                           hasProp := false,
                           propIndices := [],
                           rhs := λ α : Type u → λ head : α → λ tail : List α → cons head tail
                         } ]

    As for the following mutual inductive declaration,
      mutual
        inductive Attribute (α : Type u) where
          | Named (n : String)
          | Pattern (p : List (Term α))
          | Qid (n : String)

        inductive Term (α : Type u) where
        | Ident (s : String)
        | App (nm : String) (args : List (Term α))
        | Annotated (t : Term α) (annot : List (Attribute α))
      end

    The following entries will be added:
       - `Attribute := decls`
       - `Term := decls`
      with
        decls := [{ indName := Attribute,
                    numParams := 1,
                    hasProp := false,
                    ctors := [ { ctorName := Named,
                                 nbFields := 1,
                                 hasProp := false,
                                 propIndices := [],
                                 rhs := λ α : Type u → λ n : String → Named n
                               },
                               { ctorName := Pattern,
                                 nbFields := 1,
                                 hasProp := false,
                                 propIndices := [],
                                 rhs := λ α : Type u → λ p : List (Term α) → Pattern p
                               }
                               { ctorName := Qid,
                                 nbFields := 1,
                                 hasProp := false,
                                 propIndices := [],
                                 rhs := λ α : Type u → λ n : String → Qid n
                               } ]
                  },
                  { indName := Term,
                    numParams := 1,
                    hasProp := false,
                    ctors := [ { ctorName := Named,
                                 nbFields := 1,
                                 hasProp := false,
                                 propIndices := [],
                                 rhs := λ α : Type u → λ s : String → Ident s
                               },
                               { ctorName := App,
                                 nbFields := 2,
                                 hasProp := false,
                                 propIndices := [],
                                 rhs := λ α : Type u → λ nm : String → λ args : List (Term α) → App nm args
                               },
                               { ctorName := Annotated,
                                 nbFields := 2,
                                 hasProp := false,
                                 propIndices := [],
                                 rhs := λ α : Type u → λ t : Term α → λ annot : List (Attribute α) → Annotated nm args
                               } ]
                   } ]

    Note that `optimizer` is called on each constructor `rhs` to apply proper formalization
    when at least one of the arguments is a proposition.

    An error is triggered when:
     - ∀ n ∈ indValStart.all
        - no inductive info is found for `n`;
        - no recursive info is found for `n`;
        - no recursor rule is found for at least one constructor for `n`.
-/
def translateInductiveType
  (indValStart : InductiveVal) (typeTranslator : Expr → TranslateEnvT SortExpr) :
  TranslateEnvT Unit := do

  -- add all inductive name to cache
  indValStart.all.forM fun n => cacheIndName n

  let mut sortDecls := (#[] : Array SmtSortDecl)
  let mut dataTypeDecls := (#[] : Array SmtDatatypeDecl)
  for indName in indValStart.all do
    let ConstantInfo.inductInfo indVal ← getConstEnvInfo indName
      | throwEnvError "translateInductiveType: no InductInfo found for {indName}"
    -- recVal to get the list of RecusorRule for all ctors
    let ConstantInfo.recInfo recVal ← getConstEnvInfo (mkRecName indName)
      | throwEnvError "translateInductiveType: {mkRecName indName} not a recinfo"
    let params ← genIndParams indVal
    let ctors ← createCtorDecls recVal indVal.ctors
    let arity := if let some pars := params then pars.size else 0
    let sortDecl := {name := indNameToSmtSymbol indName, arity}
    sortDecls := sortDecls.push sortDecl
    dataTypeDecls := dataTypeDecls.push {params, ctors}
  defineDataType sortDecls dataTypeDecls

 where
  defineDataType (sortDecls : Array SmtSortDecl) (typeDecls : Array SmtDatatypeDecl) : TranslateEnvT Unit := do
    if sortDecls.size == 1
    then declareDataType sortDecls[0]!.name typeDecls[0]!
    else declareMutualDataTypes sortDecls typeDecls

  genIndParams (indVal : InductiveVal) : TranslateEnvT (Option (Array SmtSymbol)) := do
   let params ←
     Optimize.forallTelescope indVal.type fun fvars _ => do
        let mut polyParams := #[]
        for h : i in [: fvars.size] do
          let arg := fvars[i]
          let decl ← getFVarLocalDecl arg
          if !(← isClassConstraintExpr decl.type) then -- ignore class constraints
            let Expr.fvar v := arg
              | throwEnvError "translateInductiveType: FVarExpr expected but got {reprStr arg}"
            -- resolve type abbreviation (useful when handling instance parameters)
            -- TODO: IMP need to apply optimizer on argument to instance parameters
            let argType' ← removeTypeAbbrev decl.type
            if isTypeUniverse argType' then
              polyParams := polyParams.push (← typeParamNameToSmtSymbol v false)
            else throwEnvError "Inductive datatype with instance parameters not supported: {reprStr indVal.name}"
        return polyParams
   if params.isEmpty then return none else return (some params)

  createCtorDeclaration (recVal : RecursorVal) (recRule : RecursorRule) : TranslateEnvT SmtConstructorDecl := do
    let ctorSym := nameToSmtSymbol recRule.ctor
    let firstCtorFieldIdx := recVal.numParams + recVal.numMotives + recVal.numMinors
    Optimize.forallTelescope (← inferTypeEnv recRule.rhs) fun fvars _ => do
      if recRule.nfields == 0 then return (ctorSym, none) -- nullary constructor
      let mut selectors := #[]
      for h : i in [firstCtorFieldIdx : fvars.size] do
        let arg := fvars[i]
        let decl ← getFVarLocalDecl arg
        let selectorIdx := i - firstCtorFieldIdx
        let selSym := mkCtorSelectorSymbol recRule.ctor selectorIdx
        if (← isPropEnv decl.type) then
          selectors := selectors.push (selSym, boolSort)
        else
          -- resolve type abbreviation
          let argType' ← removeTypeAbbrev decl.type
          selectors := selectors.push (selSym, ← typeTranslator argType')
      return (ctorSym, some selectors)

  createCtorDecls (recVal : RecursorVal) (ctors : List Name) : TranslateEnvT (Array SmtConstructorDecl) := do
   let mut ctorDecls := (#[] : Array SmtConstructorDecl)
   for c in ctors do
     let ctorDecl ← createCtorDeclaration recVal (← getRecRuleFor recVal c)
     ctorDecls := ctorDecls.push ctorDecl
   return ctorDecls

/-- Given an instantiated inductive data type `t x₁ ... xₙ`, generate it's corresponding
    predicate qualifier predicate and propositional assertions when instance is not already
    in `indTypeInstCache`. In particular,
     - let instApp ← getIndInst t #[x₁, ..., xₙ]
     - When instApp := {instName, instSort} ∈ indTypeInstCache
         - return ()
     - Otherwise:
        - let {instName, instSort} ← generateIndInstDecl t args typeTranslator
        - When `∀ c ∈ Ctors(t), c = C (i.e., nullary constructors)
           - declare smt predicate (declare-fun @is{instName} ((instSort)) Bool)`
        - Otherwise:
           - declare smt predicate (declare-fun @is{instName} ((instSort)) Bool)`
           - For each c ∈ Ctors(t),
              - When c = C (i.e., nullary constructor) don't generate any assertion
              - When c = C p₁ ... pₙ, generate assertion
                  `(assert (forall ((@x instSort))
                     (! (=> (@is{instName} @x) (=> is-C @x (and predTermᵢ ... predTermₙ)))
                       :pattern ((@is{instName} @x) (is-C @x)))))`
                 with ∀ i ∈ [1..n],
                        (isProp pᵢ → predTermᵢ = `(= (C.i @x) (← termTranslator (← optimizeExpr pᵢ)))`) ∧
                        (¬ isProp pᵢ → predTermᵢ = `(isTypeᵢ (C.i @x))`)
    TODO: UPDATE SPEC
-/
partial def defineInstPredicateQualifier
    (typeTranslator : Expr → TranslateEnvT SortExpr)
    (termTranslator : Expr → TranslateEnvT SmtTerm)
    (t : Expr) (args : Array Expr) : TranslateEnvT Unit := do
 -- get inst application
 let instApp ← getIndInst t args
 unless ((← get).smtEnv.indTypeInstCache.get? instApp).isSome do
   declareIndInst t args


where
  isEnumeration (indVal : InductiveVal) : TranslateEnvT Bool := do
    match indVal.all with
    | [n] =>
      let ConstantInfo.recInfo recVal ← getConstEnvInfo (mkRecName n)
        | throwEnvError "isEnumeration: {mkRecName n} not a recinfo"
      for c in indVal.ctors do
        if (← getRecRuleFor recVal c).nfields != 0 then return false
      return true
    | _ => return false

  declareIndInst
    (t : Expr) (args : Array Expr) : TranslateEnvT Unit := do
     let Expr.const indName l := t
       | throwEnvError "declareIndInst: name expression expected but got {reprStr t}"
     let ConstantInfo.inductInfo indVal ← getConstEnvInfo indName
       | throwEnvError "declareIndInst: inductive info expected for {indName}"
     if (← isEnumeration indVal) then
       -- only declare smt predicate
       discard $ generateIndInstDecl t args (some true) typeTranslator
     else if indVal.isRec && indVal.all.length > 1 then
       -- generate inductive instance for all mutually inductive datatypes
       -- NOTE: Lean4 imposes that all inductive data type within a mutual block
       -- must have the same parameters. Otherwise, any error is triggered
       let decls ← List.mapM
                 (fun n => Prod.mk n <$> generateIndInstDecl (mkConst n l) args none typeTranslator)
                 indVal.all
       for d in decls do generatePredicates d.1 l d.2 args (mutualRec := true)
     else
       -- define predicate qualifier for single inductive datatype
       let decl ← generateIndInstDecl t args none typeTranslator (declarePredicate := indVal.isRec)
       generatePredicates indName l decl args (mutualRec := indVal.isRec)

  generatePredicates
    (indName : Name) (us : List Level) (decl : IndTypeDeclaration)
    (args : Array Expr) (mutualRec := false) : TranslateEnvT Unit := do
   let ConstantInfo.inductInfo indVal ← getConstEnvInfo indName
       | throwEnvError "generatePredicates: inductive info expected for {indName}"
   let ConstantInfo.recInfo recVal ← getConstEnvInfo (mkRecName indName)
     | throwEnvError "generatePredicates: {mkRecName indName} not a recinfo"
   let mut funBody := trueSmt
   for c in indVal.ctors do
     funBody ← generatePredicateAssertions indName us decl recVal (← getRecRuleFor recVal c) args funBody
   -- define function and add proposition assertion for limited call (if necessary)
   let funName := if mutualRec then appendSymbol decl.instName "LRec" else decl.instName
   let xsym := mkReservedSymbol "@x"
   let quantifiers ← genericArgsToSortedVars (← retrieveGenericArgs args) (inPredQualifier := true)
   let quantifiers := quantifiers.push (xsym, decl.instSort)
   defineFun funName quantifiers boolSort funBody indVal.isRec
   unless !(mutualRec) do
     let varIds := quantifiers.map (λ q => smtSimpleVarId q.1)
     let predRecApp := mkSimpleSmtAppN decl.instName varIds
     let limitedApp := mkSimpleSmtAppN funName varIds
     let patterns := some #[mkPattern #[predRecApp]]
     let forallTerm := (eqSmt limitedApp predRecApp)
     assertTerm (mkForallTerm none quantifiers forallTerm patterns)

  substitutePred (sub : Expr × Expr) (e : Expr) : Option Expr :=
    if sub.1 == e then some sub.2 else none -- TODO: check if we can use pointer equality

  updatePredTerm (prevTerm : SmtTerm) (newTerm : SmtTerm) : SmtTerm :=
    if isTrueSmt prevTerm
    then newTerm
    else andSmt prevTerm newTerm

  updateIteTerm (recRule : RecursorRule) (prevTerm : SmtTerm) (predTerm : SmtTerm) : SmtTerm :=
   if recRule.nfields == 0 then
     prevTerm -- nullary constructor case
   else iteSmt (mkGenericCtorTestorTerm recRule.ctor) predTerm prevTerm

  getPredicateQualifierInst (t : Expr) (currDecl : IndTypeDeclaration) : TranslateEnvT (IndTypeDeclaration) := do
    match (← getPredicateDeclaration t) with
    | some decl =>
        if currDecl.instName == decl.instName
        then return { decl with instName := appendSymbol decl.instName "LRec" }
        else return decl

    | none =>
        if t.isForall then -- function ctor parameter
          withInstantiatedImplicitArgs t fun t' => do
            let decl ← generateFunInstDeclAux t' (← typeTranslator t')
            return decl
        else -- other inductive datatype
          let (f, args) := getAppFnWithArgs t
          defineInstPredicateQualifier typeTranslator termTranslator f args
          let some decl ← getPredicateDeclaration t
            | throwEnvError "predicate qualifier name expected for {reprStr t}"
          return decl


  generatePredicateAssertions
    (indName : Name) (us : List Level) (declInd : IndTypeDeclaration)
    (recVal : RecursorVal) (recRule : RecursorRule)
    (args : Array Expr) (funBody: SmtTerm) : TranslateEnvT SmtTerm := do
    let cinfo ← getConstEnvInfo indName
    -- NOTE: we need to only consider level for provided arguments only.
    -- Indeed, we must not instantiated internal polymorphic types
    let auxApp := (mkAppN recRule.rhs args).instantiateLevelParams cinfo.levelParams (List.take args.size us)
    let firstCtorFieldIdx := recVal.numMotives + recVal.numMinors
    -- NOTE: recVal.numParams is ignored here when determining firstCtorFieldIdx
    -- as we are instantiating the datatype parameters
    Optimize.forallTelescope (← inferTypeEnv auxApp) fun fvars _ => do
      -- list to replace each ctor field with appropriate selector name
      let mut substituteList := []
      -- predTerm condition to be asserted
      let mut predTermCond := trueSmt
      for h : i in [firstCtorFieldIdx : fvars.size] do
        let arg := fvars[i]
        let decl ← getFVarLocalDecl arg
        let selectorIdx := i - firstCtorFieldIdx
        let selTerms ← mkCtorSelectorExpr recRule.ctor selectorIdx arg decl.type
        substituteList := (arg, selTerms.1) :: substituteList
        if (← isPropEnv decl.type) then
          let optExpr ← optimizeExpr' decl.type
          -- apply substitue list on optExpr before translation
          let propTerm ← termTranslator (substituteList.foldr (fun a acc => acc.replace (substitutePred a)) optExpr)
          predTermCond := updatePredTerm predTermCond (andSmt (eqSmt selTerms.2 propTerm) selTerms.2)
        else
          -- resolve type abbreviation first
          let argType' ← removeTypeAbbrev decl.type
          -- For BitVec types, normalize the width argument (OfNat/proj → raw Nat literal)
          -- so that the indTypeInstCache lookup in getPredicateQualifierInst hits the
          -- canonical entry stored by translateBitVecType (keyed under `BitVec (Expr.lit w)`).
          let argType' ← if isBitVecType argType' then do
                            let widthArg ← whnf argType'.appArg!
                            pure (mkApp argType'.appFn! widthArg)
                          else pure argType'
          let declInst ← getPredicateQualifierInst argType' declInd
          let appTerm ← createPredQualifierAppAux' selTerms.2 argType' declInst (inPredQualifier := true)
          predTermCond := updatePredTerm predTermCond appTerm
      -- update fun body
      return updateIteTerm recRule funBody predTermCond

/-- TODO: UPDATE SPEC. -/
def translateNonOpaqueType
  (t : Expr) (args : Array Expr)
  (typeTranslator : Expr → TypeOptions → TranslateEnvT SortExpr)
  (termTranslator : Expr → TranslateEnvT SmtTerm)
  (topts : TypeOptions) :
  TranslateEnvT SortExpr := do
  match t with
  | Expr.const n _ =>
      if (← isVisitedIndName n) then return (← translateInstType n)
      let ConstantInfo.inductInfo indVal ← getConstEnvInfo n
        | throwEnvError "translateNonOpaqueType: inductive info expected for {n}"
      -- we should not define sort for polymorphic inductive parameters,
      -- we should set genericParamFun to `false` and inTypeDefinition to `true`
      translateInductiveType indVal (λ e => typeTranslator e optionsForInductiveType)
      return (← translateInstType n)
  | _ => throwEnvError "translateNonOpaqueType: name expression expected but got {reprStr t}"

 where
   translateInstType (indName : Name) : TranslateEnvT SortExpr := do
     let env ← get
     let instApp ← getIndInst t args
     match env.smtEnv.indTypeInstCache.get? instApp with
     | some decl => return decl.instSort
     | none =>
       let typeTrans := λ e => typeTranslator e topts
       let smtType ← generateInstType indName args typeTrans
       if !topts.inTypeDefinition then
          -- generate predicate qualifier
          -- reset indTypeDefinition flag
          defineInstPredicateQualifier (λ e => typeTranslator e default) termTranslator t args
       return smtType


/-- Given `n` a name expression for which a corresponding smt sort exists (e.g., Bool, Int, String),
    `s` its corresponding Smt symbol and `t` its corresponding Smt sort,
    perform the following actions:
     - When entry `n := s` exists in `indTypeInstCache`
         - return `t`
     - Otherwise:
        - add entry `n := s` in `indTypeInstCache`
        - define smt predicate `(define-fun @is{s} ((@x s)) Bool true)`
        - return `t`
-/
def translateSmtEquivType (n : Expr) (s : SmtSymbol) (t : SortExpr) : TranslateEnvT SortExpr := do
 match (← get).smtEnv.indTypeInstCache.get? n with
 | none =>
    let decl ← updateIndInstCache n s t (isReservedSymbol := true)
    definePredQualifier decl.instName #[t] (some true)
    return t
 | some decl => return decl.instSort


/-- Perform the following actions:
     - When entry `n := "Nat"` exists in `indTypeInstCache` return #[natSort]
     - Otherwise:
        - add entry `n := {@isNat, natSort}` in `indTypeInstCache`
        - define smt sort `(define-sort Nat () Int)`
        - define smt predicate `(define-fun @isNat ((@x Nat)) Bool (<= 0 @x))`
        - return `natSort`
  Assume that `n := Expr.const ``Nat []`.

-/
def translateNatType (n : Expr) : TranslateEnvT SortExpr := do
 match (← get).smtEnv.indTypeInstCache.get? n with
 | none =>
    let decl ← updateIndInstCache n natSymbol natSort (isReservedSymbol := true)
    defineNatSort decl.instName
    return natSort
 | some decl => return decl.instSort


/-- Perform the following actions:
     - When entry `n := "Empty"` exists in `indTypeInstCache`
        - return `emptySort`
     - Otherwise:
        - add entry `n := "Empty"` in `indTypeInstCache`
        - add entry `n := {@isEmpty, emptySort} in `indTypeInstCache`
        - declare smt sort `(declare-sort Empty 0)`
        - define smt predicate `(define-fun @isEmpty (@x (Empty)) Bool false)`
        - return `emptySort`
  Assume that `n := Expr.const ``Empty []`.
-/
def translateEmptyType (n : Expr) : TranslateEnvT SortExpr := do
 match (← get).smtEnv.indTypeInstCache.get? n with
 | none =>
    let decl ← updateIndInstCache n emptySymbol emptySort (isReservedSymbol := true)
    defineEmptySort decl.instName
    return emptySort
 | some decl => return decl.instSort


/-- Perform the following actions:
     - When entry `n := "PEmpty"` exists in `indTypeInstCache`
          - return `pemptySort`
     - Otherwise:
        - add entry `n := {@isPEmpty, pemptySort}` in `indTypeInstCache`
        - declare smt sort `(declare-sort PEmpty 0)`
        - define smt predicate `(define-fun @isPEmpty ((PEmpty)) Bool false)`
        - return `pemptySort`
  Assume that `n := Expr.const ``PEmpty [..]`.
-/
def translatePEmptyType (n : Expr) : TranslateEnvT SortExpr := do
 match (← get).smtEnv.indTypeInstCache.get? n with
 | none =>
    let decl ← updateIndInstCache n pemptySymbol pemptySort (isReservedSymbol := true)
    definePEmptySort decl.instName
    return pemptySort
 | some decl => return decl.instSort


/-- Translate `SMTArray α` (the single-field structure, NOT raw `Array α` — raw
    arrays stay on the opaque-datatype path so concrete arrays keep structural
    equality) to a freshly-declared SMT **datatype pair**, NOT a bare array-theory
    sort.  `σ_α` is the translated element sort; the index domain is always `Int`
    (SMT integer theory) because `SMTArray.get`/`set` take a `Nat` index.

    The datatype has a single constructor with two selectors — the backing array
    and the (logical) size — plus a per-instance out-of-bounds default constant:
    `(declare-datatype SMTArray_v
       ((@mkSMTArray_v (@dataSMTArray_v (Array Int σ)) (@sizeSMTArray_v Int))))`
    `(declare-const @dfltSMTArray_v σ)`  -- out-of-bounds value, see below
    This size-aware pair is what makes `get`/`set`/`size` (see `translateSMTArrayOp?`)
    match the bounds-checked Lean semantics: out-of-range `get` returns the default,
    out-of-range `set` is a no-op, and `size` reads the size selector.  A bare
    `(Array Int σ)` sort could not model the size or the out-of-bounds behaviour.

    The out-of-bounds default `@dfltSMTArray_v` is declared as a free constant and
    only constrained to satisfy the element qualifier.  This is SOUND: it
    over-approximates Lean's fixed `Inhabited.default`, so the solver sees at most
    more countermodels, never a false proof (computing the exact default is
    deferred — this is incompleteness, not unsoundness).

    Qualifier uniqueness: `updateIndInstCache` derives the qualifier name as
    `@is<symbol>`.  Using a single fixed symbol (e.g. `@isSMTArray`) would collide when
    two different element types are used in the same query (Z3 rejects duplicate
    `define-fun`).  We therefore derive a fresh counter-based symbol per call;
    the `indTypeInstCache` lookup at the top of this function ensures the fresh id
    is generated only once per distinct element-type expression.

    The predicate qualifier constrains the size to be non-negative and lifts the
    element type's qualifier pointwise over the backing array (all-Int domain):
    `(define-fun @isSMTArray_v ((@x <datatypeSort>)) Bool
       (and (<= 0 (@sizeSMTArray_v @x))
            (forall ((@i Int)) (@isElem (select (@dataSMTArray_v @x) @i)))))`.
    The pointwise element lift is a soundness requirement — without it, elements of
    `SMTArray Nat` / `SMTArray (Fin n)` are unconstrained Ints and admit spurious
    witnesses in positive position. For exact element types (Int/BitVec/Bool)
    `@isElem` is trivially `true`, so that conjunct reduces to `(forall i true)`.
-/
def translateArrayType
    (typeTranslator : Expr → TranslateEnvT SortExpr)
    (t : Expr) : TranslateEnvT SortExpr := do
  -- Cache lookup: key is the full `SMTArray α` expression.
  match (← get).smtEnv.indTypeInstCache.get? t with
  | some decl => return decl.instSort
  | none =>
    let elemType := t.appArg!
    let elemSort ← typeTranslator elemType
    let dataSort := arraySort #[intSort, elemSort]
    -- Generate a fresh ID so that `SMTArray Int` and `SMTArray (BitVec 8)`
    -- produce distinct datatype/qualifier names.
    let v ← mkFreshId
    let names := smtArrNames v
    -- Faithful size-aware encoding: a datatype pair (data : (Array Int σ), size : Int)
    -- plus a per-instance out-of-bounds `default` constant. `get`/`set`/`size`
    -- (see translateSMTArrayOp?) interpret these so the SMT model matches the
    -- bounds-checked Lean semantics of `SMTArray.get`/`set`/`size`.
    let ctorDecl : SmtConstructorDecl :=
      (names.ctorSym, some #[(names.dataSel, dataSort), (names.sizeSel, intSort)])
    declareDataType names.sortSym { params := none, ctors := #[ctorDecl] }
    let arrSort := SortExpr.SymbolSort names.sortSym
    -- per-instance out-of-bounds default constant, constrained to satisfy the element qualifier.
    -- SOUNDNESS: leaving this value free (only element-qualifier-constrained) over-approximates
    -- Lean's fixed `Inhabited.default`, so the solver gets at most more countermodels, never a
    -- false proof (the exact default is deferred — incompleteness, not unsoundness).
    declareConst names.dfltSym elemSort
    let dfltPred ← createPredQualifierAppAux (smtSimpleVarId names.dfltSym) elemType (inPredQualifier := true)
    assertTerm dfltPred
    let decl ← updateIndInstCache t names.sortSym arrSort (isReservedSymbol := true)
    -- Cache key coupling: this writer keys on the raw `t`, and the reader
    -- (`translateSMTArrayOp?`) looks up via the `inferTypeEnv`-derived binder type. The two MUST
    -- stay in lockstep. Unlike Vector/Fin/BitVec, SMTArray has no numeric index to canonicalize,
    -- so raw `t` is correct here — do NOT canonicalize this key without canonicalizing the reader.
    modify (fun env => { env with smtEnv.smtArrNamesCache := env.smtEnv.smtArrNamesCache.insert t names })
    -- qualifier: size >= 0 AND elements satisfy the element qualifier through the data selector.
    -- The pointwise element lift is a SOUNDNESS requirement (without it, `SMTArray Nat`/
    -- `SMTArray (Fin n)` elements are unconstrained Ints and admit spurious witnesses).
    --   (define-fun @isSMTArray_v ((@x SMTArray_v)) Bool
    --      (and (<= 0 (@sizeSMTArray_v @x))
    --           (forall ((@i Int)) (@isElem (select (@dataSMTArray_v @x) @i)))))
    let xsym := mkReservedSymbol "@x"
    let isym := mkReservedSymbol "@i"
    let sizeNonNeg := leqSmt (natLitSmt 0) (smtSelectorApp names.sizeSel (smtSimpleVarId xsym))
    let elemSel := selectSmt (smtSelectorApp names.dataSel (smtSimpleVarId xsym)) #[smtSimpleVarId isym]
    let elemPred ← createPredQualifierAppAux elemSel elemType (inPredQualifier := true)
    let elemForall := mkForallTerm none #[(isym, intSort)] elemPred none
    let body := andSmt sizeNonNeg elemForall
    defineFun decl.instName #[(xsym, arrSort)] boolSort body
    return arrSort

/-- Translate `Vector α n` (literal `n` only) to the SMT array theory sort `(Array Int σ_α)`,
    where `σ_α` is the translated element sort.  The index domain is always `Int` (SMT integer
    theory) because `Vector.get` takes a `Fin n` index, which is range-checked at the Lean level;
    at the SMT level we lift the element qualifier pointwise over all integers, matching the
    treatment of `SMTArray`.

    The length argument must be a Nat literal (WHNF-reduced); non-literal lengths are not
    supported (use `SMTArray` for dynamically-sized arrays).

    Qualifier uniqueness: a fresh ID is generated per distinct `Vector α n` expression so that
    `Vector Int 3` and `Vector (BitVec 8) 4` produce distinct qualifier names (e.g.,
    `@isVector_1`, `@isVector_2`), avoiding Z3 `define-fun` redefinition errors.

    The predicate qualifier lifts the element type's qualifier pointwise (all-Int domain, same as
    `translateArrayType`):
    `(define-fun @isVector_v ((@x (Array Int σ))) Bool (forall ((@i Int)) (@isElem (select @x @i))))`.
-/
def translateVectorType
    (typeTranslator : Expr → TranslateEnvT SortExpr)
    (t : Expr) : TranslateEnvT SortExpr := do
  -- Cache key is the canonical `Vector α (lit n)` form (single source of truth:
  -- see canonicalizeIndexedType) so a proj-form length from a reverted hypothesis
  -- binder shares the entry written here and read by getPredicateDeclaration.
  let tKey ← canonicalizeIndexedType t
  match (← get).smtEnv.indTypeInstCache.get? tKey with
  | some decl => return decl.instSort
  | none =>
    let args := t.getAppArgs
    -- Element type is the first explicit arg; length is the second.
    let elemType := args[0]!
    let lengthArg ← whnf args[1]!
    let some _n := isNatValue? lengthArg
      | throwEnvError "translateVectorType: Vector with non-literal length is not supported (got {reprStr args[1]!})"
    let elemSort ← typeTranslator elemType
    let sort := arraySort #[intSort, elemSort]
    -- Generate a fresh ID so that `Vector Int 3` and `Vector (BitVec 8) 4`
    -- produce distinct qualifier names, e.g. `@isVector_1` and `@isVector_2`.
    let v ← mkFreshId
    let sym := mkReservedSymbol s!"Vector_{v}"
    let decl ← updateIndInstCache tKey sym sort (isReservedSymbol := true)
    -- Lift the element qualifier pointwise over all integers (all-Int domain, same as
    -- translateArrayType).
    --   (define-fun @isVector_v ((@x (Array Int σ))) Bool
    --      (forall ((@i Int)) (@isElem (select @x @i))))
    let xsym := mkReservedSymbol "@x"
    let isym := mkReservedSymbol "@i"
    let elemPred ← createPredQualifierAppAux
      (selectSmt (smtSimpleVarId xsym) #[smtSimpleVarId isym]) elemType (inPredQualifier := true)
    let body := mkForallTerm none #[(isym, intSort)] elemPred none
    defineFun decl.instName #[(xsym, sort)] boolSort body
    return sort

/-- Translate `BitVec w` (literal `w` only) to the builtin Smt sort `(_ BitVec w)`.
    A trivial predicate qualifier `@isBitVec_{w}` is defined (the Smt sort is exact).
    An error is triggered when the width is not a Nat literal.
    Assume `t := Expr.app (Expr.const ``BitVec _) widthArg`.
    The width argument is WHNF-reduced before checking; this normalizes non-literal
    forms such as `@OfNat.ofNat Nat 8 (instOfNatNat 8)` or
    `Expr.proj OfNat 0 (instOfNatNat 8)` to `Expr.lit (natVal 8)`.  Such forms arise
    from UInt8/UInt32 structure definitions where the width is written via the OfNat
    typeclass rather than a raw numeral.
    The cache is keyed by the CANONICAL form `BitVec (litVal w)` so all non-literal
    width representations of the same width share a single cache entry.
-/
def translateBitVecType (t : Expr) : TranslateEnvT SortExpr := do
    -- WHNF-reduce the width argument to normalize OfNat/proj forms to raw Nat literals.
    let widthArg ← whnf t.appArg!
    let some w := isNatValue? widthArg
      | throwEnvError "translateBitVecType: BitVec with non-literal width is not supported, got {reprStr t.appArg!}"
    if w == 0 then
      throwEnvError "translateBitVecType: BitVec 0 is not representable in SMT-Lib ((_ BitVec 0) is illegal)"
    -- Canonicalize: always use `BitVec (Expr.lit w)` as the cache key so that
    -- `BitVec 8 (lit)`, `BitVec (OfNat.ofNat ... 8)`, and `BitVec (proj OfNat 0 ...)` all
    -- share a single entry.
    let tNorm ← canonicalizeIndexedType t
    match (← get).smtEnv.indTypeInstCache.get? tNorm with
    | some decl => return decl.instSort
    | none =>
      let decl ← updateIndInstCache tNorm (bitvecSymbol w) (bitvecSort w) (isReservedSymbol := true)
      definePredQualifier decl.instName #[bitvecSort w] (some true)
      return decl.instSort

/-- Translate `Fin n` (literal `n` only) to the Int-aliased `Fin_n` sort with
    range qualifier `(and (<= 0 x) (< x n))`.
    Non-literal bound → error pointing at SMTArray.
    Assume `t := Expr.app (Expr.const ``Fin _) boundArg`.
    The bound argument is WHNF-reduced before checking; this normalizes
    non-literal forms such as `@OfNat.ofNat Nat 5 (instOfNatNat 5)` to
    `Expr.lit (natVal 5)`.
    The cache is keyed by the CANONICAL form `Fin (litVal n)` so all non-literal
    bound representations of the same bound share a single cache entry.
-/
def translateFinType (t : Expr) : TranslateEnvT SortExpr := do
    -- WHNF-reduce the bound argument to normalize OfNat/proj forms to raw Nat literals.
    let boundArg ← whnf t.appArg!
    let some n := isNatValue? boundArg
      | throwEnvError "translateFinType: Fin with non-literal bound is not supported (got {reprStr t.appArg!}); use SMTArray for dynamically-sized indexing"
    -- Canonicalize the cache key (single source of truth: see canonicalizeIndexedType).
    let tNorm ← canonicalizeIndexedType t
    match (← get).smtEnv.indTypeInstCache.get? tNorm with
    | some decl => return decl.instSort
    | none =>
      let decl ← updateIndInstCache tNorm (finSymbol n) (finSort n) (isReservedSymbol := true)
      defineFinSort decl.instName n
      return decl.instSort

/-- Translate opaque sorts to their Smt counterpart.
    An error is triggered when `e` does not correspond to a name expression.
    TODO: update function when opacifying other Lean inductive types (e.g., Char, etc).
-/
def translateOpaqueType (e : Expr) : TranslateEnvT (Option SortExpr) := do
 match e with
 | Expr.const n _ =>
    match n with
    | ``Bool => translateSmtEquivType e boolSymbol boolSort
    | ``Empty => translateEmptyType e
    | ``Int => translateSmtEquivType e intSymbol intSort
    | ``Nat => translateNatType e
    | ``PEmpty => translatePEmptyType e
    | ``String => translateSmtEquivType e stringSymbol stringSort
    | _ => return none
 | _ => throwEnvError "translateOpaqueType: name expression expected but got {reprStr e}"

/-- Read the configured USize/ISize bit-width from the solver options.
    Validates that the value is 32 or 64; throws a clear error otherwise. -/
def getUsizeWidth : TranslateEnvT Nat := do
  let w := (← get).optEnv.options.solverOptions.usizeWidth
  if w == 32 || w == 64 then return w
  throwEnvError s!"usize-width must be 32 or 64, but got {w}"

/-- Translate a UInt/Int family type to its underlying `(_ BitVec w)` sort
    (wrappers erased — UInt8 and BitVec 8 share the SMT sort).
    Assume `t.getAppFn = Expr.const n _` with n a UInt/Int family name.

    Qualifier uniqueness: the qualifier name is derived from the TYPE name
    (`@isUInt8`, `@isInt8`, `@isUSize`, …), NOT the width: a width-derived
    `@isBitVec_8` would collide across `UInt8`/`Int8`/`BitVec 8` (all map
    to `(_ BitVec 8)`) → duplicate `define-fun` → Z3 error.  The sort is
    built-in (no `define-sort`), so a distinct predicate name fully resolves it.
-/
def translateUIntType (t : Expr) : TranslateEnvT SortExpr := do
  match (← get).smtEnv.indTypeInstCache.get? t with
  | some decl => return decl.instSort
  | none =>
    let Expr.const n _ := t.getAppFn
      | throwEnvError "translateUIntType: name expression expected but got {reprStr t}"
    let w ← match uintWidth? n with
      | some w => pure w
      | none => getUsizeWidth  -- USize/ISize: read from usize-width option
    let decl ← updateIndInstCache t (mkReservedSymbol s!"{n}") (bitvecSort w) (isReservedSymbol := true)
    definePredQualifier decl.instName #[bitvecSort w] (some true)
    return decl.instSort

/-- TODO: UPDATE SPEC -/
partial def translateTypeAux
  (termTranslator : Expr → TranslateEnvT SmtTerm)
  (t : Expr) (topts := (default : TypeOptions)) :
  TranslateEnvT SortExpr := do
   let e := t.getAppFn
   match e with
   | Expr.const ``Blaster.SMTArray _ => translateArrayType (λ a => translateTypeAux termTranslator a) t
   | Expr.const ``Array _ => translateArrayType (λ a => translateTypeAux termTranslator a) t
   | Expr.const ``Vector _ => translateVectorType (λ a => translateTypeAux termTranslator a) t
   | Expr.const ``Fin _ => translateFinType t
   | Expr.const ``BitVec _ => translateBitVecType t
   | Expr.const .. =>
      if isUIntFamilyType e then return (← translateUIntType t)
      if let some r ← translateOpaqueType e then return r
      translateNonOpaqueType e t.getAppArgs
        (λ a b => translateTypeAux termTranslator a b)
        termTranslator topts

   | Expr.fvar v =>
      let t ← inferTypeEnv e
      if !(isTypeUniverse t) then throwEnvError "translateType: sort type expected but got {reprStr t}"
      -- NOTE: `inTypeDefinition` is set to `true` only when translating inductive datatype`,
      -- while `genericParamFun` is set to `true` when generating predicate qualifiers.
      if !topts.inTypeDefinition then
         -- case when polymorphic type (e.g., α : Type u) is declared at top level
         let decl ← generateSortInstDecl t
         -- check if already declared
         if !(← (isInQuantifiedFVarsCache v)) then
           let smtSym ← typeParamNameToSmtSymbol v
           updateQuantifiedFVarsCache v false
           declareConst smtSym decl.instSort
         -- return @Instance_xxx as type
         return (← getInstanceSort decl)
      else -- case when inTypeDefinition is set to true
         -- implicit polymorphic type case (see note in `translateArrowType`)
         if ← (isInQuantifiedFVarsCache v) then
            let decl ← generateSortInstDecl t
            -- return @Instance_xxx as type
            return (← getInstanceSort decl)
         else -- case when sort is a param of an inductive data type.
            return .SymbolSort (← typeParamNameToSmtSymbol v false)

   | Expr.forallE .. =>
       let st ← translateArrowType t topts
       if !topts.inTypeDefinition then
         -- NOTE: predicate qualifier and congruence constraints not generated when translating
         -- fun defined in an inductive predicate
         -- NOTE: use of smt universal type @Type in predicate qualifier signature,
         -- especially when polymorphic types still remain.
         withInstantiatedImplicitArgs t fun t' => do generateFunInstDecl t' st
       return st

   | Expr.sort .zero =>
        let decl ← generateSortInstDecl e
        return decl.instSort

   | Expr.sort .. => throwEnvError "translateType: unexpected sort type {reprStr e}"

   | _ => throwEnvError "translateType: type expression expected but got {reprStr e}"

 where
   translateArrowType (e : Expr) (opts : TypeOptions) : TranslateEnvT SortExpr := do
     Optimize.forallTelescope e fun fvars body => do
       let mut arrowArgs := #[]
       for h : i in [:fvars.size] do
         let v := fvars[i]
         let decl ← getFVarLocalDecl v
         if !(← isClassConstraintExpr decl.type) then -- ignore class constraints
          if decl.binderInfo.isExplicit then
            arrowArgs := arrowArgs.push (← translateTypeAux termTranslator decl.type opts)
          else
            -- Need to consider case when fun/proposition in type definition has implicit polymorphic type (see `Issue15.thm4`)
            discard $ translateTypeAux termTranslator v default
       arrowArgs := arrowArgs.push (← translateTypeAux termTranslator body opts)
       let arrowT ← declareArrowTypeSort arrowArgs.size
       return paramSort arrowT arrowArgs

/-- TODO: UPDATE SPEC -/
def translateType
  (termTranslator : Expr → TranslateEnvT SmtTerm)
  (t : Expr) (topts := (default : TypeOptions)) :
  TranslateEnvT SortExpr := do
  -- resolve type abbreviation first
  translateTypeAux termTranslator (← removeTypeAbbrev t) topts


structure QuantifierEnv where
  quantifiers: SortedVars
  premises : Array SmtTerm
  topLevel : Bool
deriving Inhabited

abbrev QuantifierEnvT := StateRefT QuantifierEnv TranslateEnvT


def initialQuantifierEnv (topLevel : Bool) : QuantifierEnv :=
  { quantifiers := #[], premises := #[], topLevel }

/-- Translate a quantifier `(n : t)` by performing the following actions:

    Assume that `t` is not a proposition (i.e., !(← isPropEnv t)) nor a class constraint.
    An error is triggered if `n` is not an `fvar` expression.

    TODO: UPDATE SPEC
-/
def translateQuantifier
  (n : Expr) (t : Expr) (termTranslator : Expr → TranslateEnvT SmtTerm) : QuantifierEnvT Unit := do
 let Expr.fvar v := n | throwEnvError "translateQuantifier: FVarExpr expected but got {reprStr n}"
 -- update quantified fvars cache
 updateQuantifiedFVarsCache v (← get).topLevel
 -- polymorphic type case (e.g., α : Type u)
 if isTypeUniverse t then
   let decl ← generateSortInstDecl t
   let smtSym ← typeParamNameToSmtSymbol v
   addQuantifier smtSym decl.instSort
 else
   -- No more required to resolve type at this stage.
   let smtType ← translateTypeAux termTranslator t
   let smtSym ← fvarIdToSmtSymbol v
   updatePredicateQualifiers t smtSym -- update predicate qualifiers list
   addQuantifier smtSym smtType

 where

   updatePredicateQualifiers (t : Expr) (smtSym : SmtSymbol) : QuantifierEnvT Unit := do
     let pTerm ← createPredQualifierApp smtSym t
     modify (fun env => { env with premises := env.premises.push pTerm})

   updateQuantifiers (smtSym : SmtSymbol) (smtType: SortExpr) : QuantifierEnvT Unit := do
    modify (fun env => { env with quantifiers := env.quantifiers.push (smtSym, smtType)})

   addQuantifier (smtSym : SmtSymbol) (smtType: SortExpr) : QuantifierEnvT Unit := do
     if !(← get).topLevel
     then updateQuantifiers smtSym smtType -- add quantifier to list
     else declareConst smtSym smtType -- declare quantifier at top level

/-- TODO: UPDATE SPEC -/
def translateForAll
  (e : Expr) (termTranslator : Expr → TranslateEnvT SmtTerm) : QuantifierEnvT SmtTerm := do
 Optimize.forallTelescope e fun fvars b => do
   for h : i in [:fvars.size] do
     let v := fvars[i]
     let decl ← getFVarLocalDecl v
     if (← isPropEnv decl.type) then
       updatePremises (← termTranslator decl.type)
     -- need to filter out class constraints
     else if !(← isClassConstraintExpr decl.type) then
       translateQuantifier v decl.type termTranslator
   let fbody ← termTranslator b
   genForAllTerm fbody

 where
   genForAllTerm (fbody : SmtTerm) : QuantifierEnvT SmtTerm := do
    let env ← get
    let mut forallTerm := fbody
    let nbPremises := env.premises.size
    for i in [:env.premises.size] do
      let idx := nbPremises - i - 1
      forallTerm := impliesSmt env.premises[idx]! forallTerm
    if env.topLevel then return forallTerm
    if env.quantifiers.isEmpty then return forallTerm -- imply case
    return mkForallTerm none env.quantifiers forallTerm none

   updatePremises (p : SmtTerm) : QuantifierEnvT Unit := do
    modify (fun env => { env with premises := env.premises.push p})


/-- Translate free variable expression `f := Expr.fvar v` to an Smt term such that:
    - When `v ∈ (← get).smtEnv.quantifiedFVars`:
       - return `fvarIdToSmtTerm v
    - When `v ∉ (← get).smtEnv.quantifiedFVars`:
       - add `v` to the quantified fvars cache
       - Let t' ← removeTypeAbbrev (← inferTypeEnv f)
       - smtType ← translateType optimize termTranslator t'
       - smtSym ← fvarIdToSmtSymbol v
       - declare smt symbol at top level, i.e., `(declare-const smtSym smtType)`
       - pTerm ← createPredQualifierApp smtSym t'
       - assert pTerm at smt level, i.e., `(assert pTerm)`
       - return `smtSimpleVarId smtSym`
    An error is triggered when
      - `f` is not an `fvar` expression; or
      - `f` has a sort type
-/
def translateFreeVar
  (f : Expr) (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
 let Expr.fvar v := f | throwEnvError "translateFreeVar: FVarExpr expected but got {reprStr f}"
 let t ← inferTypeEnv f
 if ← (isInQuantifiedFVarsCache v) <||> (isPatternMatchFVar v)
 then
   if isTypeUniverse t
   then smtSimpleVarId <$> typeParamNameToSmtSymbol v -- case when polymorphic types are used in expression (see, Issue31.lean)
   else fvarIdToSmtTerm v
 else
   -- top level declaration case
   updateQuantifiedFVarsCache v true
   if isTypeUniverse t then throwEnvError "translateFreeVar: sort type not expected but got {reprStr t}"
   let t' ← removeTypeAbbrev t
   let smtType ← translateTypeAux termTranslator t'
   let smtSym ← fvarIdToSmtSymbol v
   declareConst smtSym smtType -- declare free variable at top level
   let pTerm ← createPredQualifierApp smtSym t'
   assertTerm pTerm
   return (smtSimpleVarId smtSym)

end Blaster.Smt
