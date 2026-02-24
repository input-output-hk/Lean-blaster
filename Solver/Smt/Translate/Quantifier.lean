import Lean
import Solver.Smt.Env
import Solver.Optimize.Basic

open Lean Meta Solver.Optimize

namespace Solver.Smt

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
def sortNameToSmtSymbol (v : FVarId) (unique := true) : TranslateEnvT SmtSymbol := do
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

/-- Define smt universal sort @@Type and its corresponding predicate qualified
    whenever flag `typeUniverse` is not set.
    Do nothing otherwise.
    Assume `isTypeSym := @isType`
-/
def declareTypeSort (isTypeSym : SmtSymbol) : TranslateEnvT Unit := do
 unless ((← get).smtEnv.options.typeUniverse) do
  defineTypeSort isTypeSym
  modify (fun env => { env with smtEnv.options.typeUniverse := true })

/-- Update sort cache with `v`. -/
def updateSortCache (v : FVarId) (s : SmtSymbol) : TranslateEnvT Unit := do
  modify (fun env => { env with smtEnv.sortCache := env.smtEnv.sortCache.insert v s})


/-- Return `vstrₙ` when entry `v := vstrₙ` exists in `sortCache`,
    otherwise, perform the following:
      - `vstr := "@" ++ v.getUserName ++ v.name`.
      - add `define-sort "vstr" () @@Type` to the Smt context
      - add entry `v := vstr` to `sortCache`
      - return vstr
-/
def defineSortAndCache (v : FVarId) : TranslateEnvT SmtSymbol := do
  let env ← get
  match env.smtEnv.sortCache.get? v with
  | none =>
      let s ← sortNameToSmtSymbol v
      defineSort s none typeSort
      updateSortCache v s
      return s
  | some s => return s

/-- Add an inductive datatype name to the visited inductive datatype cache. -/
def cacheIndName (indName : Name) : TranslateEnvT Unit := do
  modify (fun env => { env with smtEnv.indTypeVisited := env.smtEnv.indTypeVisited.insert indName})


/-- Return `true` when `indName` is already in the visited inductive
    datatype cache (i.e., `indTypeCache`)
-/
def isVisitedIndName (indName : Name) : TranslateEnvT Bool :=
  return (← get).smtEnv.indTypeVisited.contains indName

/-- Given `d` corresponding to a inductive datatype name expression,
    or an instantiated polymorphic inductive datatype, or a function instance declaration and
    `n` a unique smt identifier generated for `d` and
    `instSort` the instantiated Smt sort for `d`, perform the following:
      - add entry `d := {instName := "@is{n}", instSort, applyInstName}` in `indTypeInstCache`
      - return {instName := "@is{n}", instSort, applyInstName}

    with `applyInstName` set to `none` for inductive datatype and set to `some @apply{uniq_xxx}`.
    See function `generateFunInstDeclAux`.
-/
def updateIndInstCacheAux
  (d : Expr) (n : SmtSymbol) (instSort : SortExpr)
  (isReservedSymbol := false) (applyInstName : Option SmtSymbol := none) : TranslateEnvT IndTypeDeclaration := do
  let instName := if isReservedSymbol then mkReservedSymbol s!"@is{n}" else mkNormalSymbol s!"@is{n}"
  let decl := ({instName, instSort, applyInstName} : IndTypeDeclaration)
  modify (fun env => {env with smtEnv.indTypeInstCache := env.smtEnv.indTypeInstCache.insert d decl})
  return decl

/-- Same as `updateIndInstCacheAux` but return value is discarded. -/
def updateIndInstCache (d : Expr) (n : SmtSymbol) (instSort : SortExpr) : TranslateEnvT Unit :=
  discard (updateIndInstCacheAux d n instSort)

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
      - add `v` to `topLevelVars` only when topLevel is set to `true` and `¬ isType (← getType v)`.
-/
def updateQuantifiedFVarsCache (v : FVarId) (topLevel : Bool) : TranslateEnvT Unit := do
  let s ← fvarIdToSmtSymbol v
  let t ← v.getType
  let uname ← v.getUserName
  let idx ← getCurrentDepth
  modify
    (fun env =>
      let updatedVars := env.smtEnv.quantifiedFVars.insert v topLevel
      if topLevel && !t.isType
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

/-- Given an inductive datatype instance `t x₀ ... xₙ`, perform the following:
     - When `∀ i ∈ [0..n], ¬ isGenericParam xᵢ`,
         - return `t x₀ ... xₙ`
     - When `∃ i ∈ [0..n], isGenericParam xᵢ`,
        let A := [x₀, ..., xₙ]
        let V := [α | i ∈ [0..n] ∧ α ∈ getFVarsInExpr A[i] ∧ isGenericParam A[i] ]
        let [b₀ ... bₘ ] := V
          - return `λ b₀ → .. → bₘ → t x₀ ... xₙ`
-/
def getIndInst (t : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  let genericArgs ← retrieveGenericArgs args
  let auxApp := mkAppN t args
  mkLambdaFVars genericArgs auxApp (usedOnly := true)

/-- Given `t := ∀ α₀ → ∀ α₁ ... → αₙ` returns #[α₀, α₁ ..., αₙ].
    Assumes that `t` no more contains any class constraints (see function `removeClassConstraintsInFunType`).
-/
def retrieveArrowTypes (t : Expr) : Array Expr :=
 let rec visit (e : Expr) (arrowTypes : Array Expr) : Array Expr :=
   match e with
   | Expr.forallE _ t b _ => visit b (arrowTypes.push t)
   | _ => arrowTypes.push e
 visit t #[]

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
    mkForallFVars xs body

/-- Given `t := Expr.const n _` corresponding to an inductive datatype name and
    `args` the parameters instantiating the inductive datatype (if any),
    perform the following actions:
     - When args.size > 0:
         - instName := nameToSmtSymbol (n ++ (← mkFreshId)) (i.e., generate a unique name for instance)
         - instSort ← generateInstType n args typeTranslator
         - instApp ← getIndInst t args
         - add entry `instApp := {@is{instName}, instSort}` to `indTypeInstCache`
         - declare smt predicate `(declare-fun @is{instName} ((instSort)) Bool)`
           (only when definePredicate is set)
         - return {instName, instSort}
    - When args.size = 0:
        - instName := nameToSmtSymbol n
        - instSort ← generateInstType n args typeTranslator
        - add entry `t := {@is{instName}, instSort}` to `indTypeInstCache`
        - declare smt predicate `(declare-fun @is{instName} ((st)) Bool)` (only wwhen definedPredicate is set).
        - return `{instName, instSort}`
    Assumes that `t` corresponds to the name of an inductive datatype.
-/
def generateIndInstDecl
  (t : Expr) (args : Array Expr) (assertFlag : Option Bool)
  (typeTranslator : Expr → TranslateEnvT SortExpr) : TranslateEnvT IndTypeDeclaration := do
 let Expr.const n _ := t | throwEnvError "generateIndInstDecl: name expression expected but got {reprStr t}"
 let instSort ← generateInstType n args typeTranslator
 if args.size == 0
 then
   let instName := nameToSmtSymbol n
   let decl ← updateIndInstCacheAux t instName instSort
   definePredQualifier decl.instName decl.instSort assertFlag
   return decl
 else
   let v ← mkFreshId
   let instName := nameToSmtSymbol (n ++ v)
   let instApp ← getIndInst t args
   let decl ← updateIndInstCacheAux instApp instName instSort
   definePredQualifier decl.instName decl.instSort assertFlag
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
  mkLambdaFVars genericArgs t

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
   let t' ← mkForallFVars explicitArgs body -- keeping implicit arguments instantiated
   k t'

/-- Return `decl.instName` when `t := decl` exists in `indTypeInstCache`.
    Otherwise `none`.
    TODO: UPDATE
-/
def getPredicateDeclaration (t : Expr) : TranslateEnvT (Option IndTypeDeclaration) := do
  let t' ← getType t
  let typeInst ← getInst t'
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

  getType (e : Expr) : TranslateEnvT Expr :=
   match e with
   | Expr.fvar v => v.getType
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

/-- Given `st` an smt term and `t` its corresponding type expression, perform the following:
     - retrieve predicate qualifier name `instName` for `t`
     - return smt application (instName v)
    An error is triggered if the predicate qualifier name for `t` does not exists.
    Assume that there is no type abbreviation in `t`, i.e., call to `removeTypeAbbrev` has been applied.
-/
def createPredQualifierAppAux (st : SmtTerm) (t : Expr) : TranslateEnvT SmtTerm := do
  let some decl ← getPredicateDeclaration t
    | throwEnvError "createPredQualifierApp: predicate declaration expected for {reprStr t}"
  return (mkSimpleSmtAppN decl.instName #[st])

/-- Same as `createPredQualifierAppAux` but accepts an SmtSymbol as argument. -/
def createPredQualifierApp (smtSym : SmtSymbol) (t : Expr) : TranslateEnvT SmtTerm :=
  createPredQualifierAppAux (smtSimpleVarId smtSym) t


/-- Given `t := α₁ → α₂ ... → αₙ` and `st` its corresponding smt representation (i.e., ArrowTN sα₁ sα₂ sαₙ),
    perform the following action:
      - let funInst ← getFunInstDecl t
      - When funInst := {@is{instName}, st, applyInstName} ∈ indTypeInstCache
         - return `{@is{instName}, st, applyInstName}`
      - Otherwise:
         - let n ← mkFreshId
         - instName ← (Fun ++ n) (i.e., generate a unique name for function instance)
         - add entry `t := {@is{instName}, st, applyInstName := some @apply{n}}` to `indTypeInstCache`
         - declare smt predicate `(declare-fun @is{instName} ((instSort)) Bool)`
         - declare apply function `(declare-fun @apply{n} (st sα₁ ... sαₙ₋₁) sαₙ)`
         - assert the following propositions to specify congruence, extensionality and codomain values constraints:
            - `(assert (forall ((@f (ArrowTN sα₁ sα₂ sαₙ))(@x₁ sα₁) ... (@xₙ₋₁ sαₙ₋₁) (@y₁ sα₁) ... (@yₙ₋₁ sαₙ₋₁))
               (! (=> (= @x₁ @y₁)
                  (=> (= @x₂ @y₂)
                  ...
                  (=> (= @xₙ₋₁ @yₙ₋₁)
                      (= (@apply{n} @f @x₁ ... @xₙ₋₁) (@apply{n} @f @y₁ ... @yₙ₋₁)))))
                  :pattern ((@apply{n} @f @x₁ ... @xₙ₋₁) (@apply{n} @f @y₁ ... @yₙ₋₁)
                            (= @x₁ @y₁) ... (= @xₙ₋₁ @yₙ₋₁))
                  :qid @apply{n}_congr_args)))`

            - `(assert (forall ((@f (ArrowTN sα₁ sα₂ sαₙ)) (@g (ArrowTN sα₁ sα₂ sαₙ))
                                (@x₁ sα₁) ... (@xₙ₋₁ sαₙ₋₁))
               (! (=> (= @f @g) (= (@apply{n} @f @x₁ ... @xₙ₋₁) (@apply{n} @g @x₁ ... @xₙ₋₁)))
                  :pattern ((@apply{n} @f @x₁ ... @xₙ₋₁) (@apply{n} @g @x₁ ... @xₙ₋₁) (= @f @g))
                  :qid @apply{n}_congr_fun)))`

            - `(assert (forall ((@f (ArrowTN sα₁ sα₂ sαₙ)) (@g (ArrowTN sα₁ sα₂ sαₙ))
                                (@x₁ sα₁) ... (@xₙ₋₁ sαₙ₋₁))
               (! (=> (= (@apply{n} @f @x₁ ... @xₙ₋₁) (@apply{n} @g @x₁ ... @xₙ₋₁)) (= @f @g))
                  :pattern (= (@apply{n} @f @x₁ ... @xₙ₋₁) (@apply{n} @g @x₁ ... @xₙ₋₁)))
                  :qid @apply{n}_ext_fun)))`

            - `(assert (forall ((@f (ArrowTN sα₁ sα₂ ... αₙ)))
                (! (= (forall ((@x₁ sα₁) ... (@xₙ₋₁ sαₙ₋₁)) (@isTypeₙ (@apply{n} @f @x₁ ... @xₙ₋₁)))
                      (@is{instName} @f) )
                   :pattern ( (@is{instName} @f)) :qid @isFun{v}_cstr)))`

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
       let decl ← updateIndInstCacheAux funInst instName st (applyInstName := some applyName)
       definePredQualifier decl.instName decl.instSort none
       generateApplyFunAndAssertions t' decl.instName applyName
       return decl

  where
    generateApplyFunAndAssertions (t : Expr) (instName : SmtSymbol) (applyName : SmtSymbol): TranslateEnvT Unit := do
     let funTypes := retrieveArrowTypes t
     let .ParamSort _ smtTypes := st | throwEnvError "defineFunAssertions: ParamSort expected but got {st}"
     let nbTypes := funTypes.size - 1
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
     let mut arg_quantifiers := (#[(fsym, st)] : SortedVars)
     let mut arg_patterns := #[f_applyTerm1, f_applyTerm2]
     let mut forallCFunBody := eqSmt f_applyTerm1 f_applyTerm2
     for i in [:nbTypes] do
       let idx := nbTypes - i - 1
       let eqPremise := eqSmt xIds[idx]! yIds[idx]!
       forallCFunBody := impliesSmt eqPremise forallCFunBody
       arg_patterns := arg_patterns.push eqPremise
       co_quantifiers := co_quantifiers.push (xsyms[i]!, smtTypes[i]!)
       arg_quantifiers := (arg_quantifiers.push (xsyms[i]!, smtTypes[i]!)).push (ysyms[i]!, smtTypes[i]!)
     -- isFun constraint
     let coDomainCstr ← createPredQualifierAppAux f_applyTerm1 funTypes[nbTypes]!
     let forallCoDomain := mkForallTerm none co_quantifiers coDomainCstr none
     let f_funPredApp := mkSimpleSmtAppN instName #[fId]
     let forallFunBody := eqSmt forallCoDomain f_funPredApp
     let qidName := appendSymbol instName "cstr"
     let fun_annotations := some #[mkPattern #[f_funPredApp], mkQid qidName]
     assertTerm (mkForallTerm none #[(fsym, st)] forallFunBody fun_annotations)
     -- congruence on fun
     let qidName := appendSymbol applyName "congr_fun"
     let quantifiers_fun := (co_quantifiers.push (fsym, st)).push (gsym, st)
     let eqFun := eqSmt fId gId
     let fun_patterns := #[eqFun, f_applyTerm1, g_applyTerm]
     let eqAppFun := eqSmt f_applyTerm1 g_applyTerm
     let forallCArgBody := impliesSmt eqFun eqAppFun
     assertTerm (mkForallTerm none quantifiers_fun forallCArgBody (some #[mkPattern fun_patterns, mkQid qidName]))
     -- extensionality
     let qidName := appendSymbol applyName "ext_fun"
     let forallExtBody := impliesSmt eqAppFun eqFun
     assertTerm (mkForallTerm none quantifiers_fun forallExtBody (some #[mkPattern #[eqAppFun], mkQid qidName]))
     -- congruence on args
     let qidName := appendSymbol applyName "congr_args"
     assertTerm (mkForallTerm none arg_quantifiers forallCFunBody (some #[mkPattern arg_patterns, mkQid qidName]))


/-- Same as `generateFunInstDeclAux` but return (). -/
@[always_inline, inline]
def generateFunInstDecl (t : Expr) (st : SortExpr) : TranslateEnvT Unit :=
  discard $ generateFunInstDeclAux t st


/-- Given `t := Expr.sort _` perform the following actions only when
    no entry for `t` exists in `indTypeInstCache`:
     - When `t := Expr.sort .zero`
        - add entry `t := {@isProp, propSort} to `indTypeInstCache`
        - define smt sort `(define-sort Prop () Bool)`
        - declare smt function `(declare-fun @isProp ((Prop)) Bool)` with `true` assertion

     - When `isType t`
         - add entry `t := {@isType, typeSort} to `indTypeInstCache`
         - Define smt univseral sort @@Type when flag `typeUniverse is not set
           (see function `declareTypeSort`)

    An error is triggered when t is not the expected sort type.
-/
def generateSortInstDecl (t : Expr) : TranslateEnvT Unit := do
 let Expr.sort u := t | throwEnvError "generateSortInstDecl: sort type expected but got {reprStr t}"
 unless ((← get).smtEnv.indTypeInstCache.get? t).isSome do
   match u with
   | .zero =>
        let decl ← updateIndInstCacheAux t propSymbol propSort (isReservedSymbol := true)
        definePropSort decl.instName
   | _ =>
       if !t.isType then throwEnvError "generateSortInstDecl: sort type expected but got {reprStr t}"
       let decl ← updateIndInstCacheAux t (mkReservedSymbol "Type") typeSort (isReservedSymbol := true)
       declareTypeSort decl.instName

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
  /-- flag set to true only when translating type of function arguments
      so as to use universal sort @@Type when function are still
      polymorphic after instantiation.
  -/
  genericParamFun : Bool := false
deriving Inhabited

/-- type options to be used when translating inductive datatype. -/
def optionsForInductiveType : TypeOptions :=
  { inTypeDefinition := true, genericParamFun := false}

/-- type options to be used when generating predicate qualifiers. -/
def optionsForPredicateQualifier : TypeOptions :=
  { inTypeDefinition := false, genericParamFun := true}

/-- Same as optionsForPredicateQualifier. -/
def optionsForFunLambdaParam : TypeOptions :=
  { inTypeDefinition := false, genericParamFun := true}

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
            if argType'.isType then
              polyParams := polyParams.push (← sortNameToSmtSymbol v false)
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
        let selectorIdx := i - firstCtorFieldIdx + 1
        let selSym := mkNormalSymbol s!"{ctorSym}.{selectorIdx}"
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
     else if indVal.isRec then
       -- generate inductive instance for all mutually inductive datatypes
       -- NOTE: Lean4 imposes that all inductive data type within a mutual block
       -- must have the same parameters. Otherwise, any error is triggered
       let decls ← List.mapM
                 (fun n => Prod.mk n <$> generateIndInstDecl (mkConst n l) args none typeTranslator)
                 indVal.all
       for d in decls do generatePredicates d.1 l d.2 args
     else
       -- define predicate qualifier for non-recursive inductive datatype
       let decl ← generateIndInstDecl t args none typeTranslator
       generatePredicates indName l decl args

  generatePredicates
    (indName : Name) (us : List Level) (decl : IndTypeDeclaration)
    (args : Array Expr) : TranslateEnvT Unit := do
   let ConstantInfo.inductInfo indVal ← getConstEnvInfo indName
       | throwEnvError "generatePredicates: inductive info expected for {indName}"
   let ConstantInfo.recInfo recVal ← getConstEnvInfo (mkRecName indName)
     | throwEnvError "generatePredicates: {mkRecName indName} not a recinfo"
   let mut funBody := trueSmt
   for c in indVal.ctors do
     funBody ← generatePredicateAssertions indName us decl recVal (← getRecRuleFor recVal c) args funBody
   -- define function and add proposition assertion for limited call (if necessary)
   let suffix := if indVal.isRec then "LRec" else "Def"
   let funName := appendSymbol decl.instName suffix
   let xsym := mkReservedSymbol "@x"
   let quantifiers := #[(xsym, decl.instSort)]
   defineFun funName quantifiers boolSort funBody indVal.isRec
   let xId := smtSimpleVarId xsym
   let predRecApp := mkSimpleSmtAppN decl.instName #[xId]
   let patterns := some #[mkPattern #[predRecApp]]
   let limitedApp := mkSimpleSmtAppN funName #[xId]
   let forallTerm := (eqSmt predRecApp limitedApp)
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

  getPredicateQualifierName (t : Expr) (currDecl : IndTypeDeclaration) : TranslateEnvT SmtSymbol := do
    match (← getPredicateDeclaration t) with
    | some decl =>
        if decl.instName == currDecl.instName then
          -- recursive call : append with limited function prefix
          return appendSymbol decl.instName "LRec"
        else return decl.instName
    | none =>
        if t.isForall then -- function ctor parameter
          withInstantiatedImplicitArgs t fun t' => do
            let decl ← generateFunInstDeclAux t' (← typeTranslator t')
            return decl.instName
        else -- other inductive datatype
          let (f, args) := getAppFnWithArgs t
          defineInstPredicateQualifier typeTranslator termTranslator f args
          let some decl ← getPredicateDeclaration t
            | throwEnvError "predicate qualifier name expected for {reprStr t}"
          return decl.instName


  generatePredicateAssertions
    (indName : Name) (us : List Level) (declInd : IndTypeDeclaration)
    (recVal : RecursorVal) (recRule : RecursorRule)
    (args : Array Expr) (funBody: SmtTerm) : TranslateEnvT SmtTerm := do
    let cinfo ← getConstEnvInfo indName
    let auxApp := (mkAppN recRule.rhs args).instantiateLevelParams cinfo.levelParams us
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
        let selectorIdx := i - firstCtorFieldIdx + 1
        let selTerms ← mkCtorSelectorExpr recRule.ctor selectorIdx arg decl.type
        substituteList := (arg, selTerms.1) :: substituteList
        if (← isPropEnv decl.type) then
          let optExpr ← optimizeExpr' decl.type
          -- apply substitue list on optExpr before translation
          let propTerm ← termTranslator (substituteList.foldr (fun a acc => acc.replace (substitutePred a)) optExpr)
          predTermCond := updatePredTerm predTermCond (andSmt (eqSmt selTerms.2 propTerm) selTerms.2)
        else
          -- resolve type abbreviation first
          let argType' ← resolveTypeAbbrev decl.type
          let instName ← getPredicateQualifierName argType' declInd
          predTermCond := updatePredTerm predTermCond (mkSimpleSmtAppN instName #[selTerms.2])
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
          -- reset indTypeDefinition flag and set genericParamFun to `true`
          defineInstPredicateQualifier (λ e => typeTranslator e optionsForPredicateQualifier) termTranslator t args
       return smtType


/-- Given `n` a name expression for which a corresponding smt sort exists (e.g., Bool, Int, String),
    `s` its corresponding Smt symbol and `t` its corresponding Smt sort,
    perform the following actions:
     - When entry `n := s` exists in `indTypeInstCache`
         - return `t`
     - Otherwise:
        - add entry `n := s` in `indTypeInstCache`
        - declare smt predicate `(declare-fun @is{s} ((s)) Bool)` with `true` assertion
        - return `t`
-/
def translateSmtEquivType (n : Expr) (s : SmtSymbol) (t : SortExpr) : TranslateEnvT SortExpr := do
 match (← get).smtEnv.indTypeInstCache.get? n with
 | none =>
    let decl ← updateIndInstCacheAux n s t (isReservedSymbol := true)
    definePredQualifier decl.instName t (some true)
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
    let decl ← updateIndInstCacheAux n natSymbol natSort (isReservedSymbol := true)
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
    let decl ← updateIndInstCacheAux n emptySymbol emptySort (isReservedSymbol := true)
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
    let decl ← updateIndInstCacheAux n pemptySymbol pemptySort (isReservedSymbol := true)
    definePEmptySort decl.instName
    return pemptySort
 | some decl => return decl.instSort


/-- Perform the following actions for `BitVec n` where `n` is a static Nat literal:
     - When entry `BitVec n` exists in `indTypeInstCache` return `bitvecSort n`
     - Otherwise:
        - add entry `BitVec n := {@isBitVec_n, (_ BitVec n)}` in `indTypeInstCache`
        - declare smt predicate `(declare-fun @isBitVec_n ((_ BitVec n)) Bool)` with `true` assertion
        - return `bitvecSort n`
  Assume that `bvExpr` is `Expr.app (Expr.const ``BitVec _) (Expr.lit (Literal.natVal n))`.
-/
def translateBitVecType (bvExpr : Expr) (n : Nat) : TranslateEnvT SortExpr := do
  match (← get).smtEnv.indTypeInstCache.get? bvExpr with
  | some decl => return decl.instSort
  | none =>
      let bvSym := mkReservedSymbol s!"BitVec_{n}"
      let bvSrt := bitvecSort n
      let decl ← updateIndInstCacheAux bvExpr bvSym bvSrt (isReservedSymbol := true)
      defineBitVecSort decl.instName n
      return bvSrt


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

/-- TODO: UPDATE SPEC -/
partial def translateTypeAux
  (termTranslator : Expr → TranslateEnvT SmtTerm)
  (t : Expr) (topts := (default : TypeOptions)) :
  TranslateEnvT SortExpr := do
   let e := t.getAppFn
   match e with
   | Expr.const nm _ =>
      -- Handle `BitVec n` with a static (literal) width before the general opaque-type path.
      -- `BitVec n` is parameterized, so `translateOpaqueType` (which only sees the fn) cannot
      -- produce the indexed sort `(_ BitVec n)`; we intercept it here where the args are in scope.
      if nm == ``BitVec then
        let args := t.getAppArgs
        if args.size == 1 then
          if let Expr.lit (Literal.natVal width) := args[0]! then
            return ← translateBitVecType t width
      if let some r ← translateOpaqueType e then return r
      translateNonOpaqueType e t.getAppArgs
        (λ a b => translateTypeAux termTranslator a b)
        termTranslator topts

   | Expr.fvar v =>
      let t ← v.getType
      if !t.isType then throwEnvError "translateType: sort type expected but got {reprStr t}"
      -- Need to call defineSortAndCache to handle case when sort is defined a top level
      -- `defineSortAndCache` is called only when flags `inTypeDefinition` and `genericParamFun`
      -- are set to `false`
      -- NOTE: `inTypeDefinition` is set to `true` only when translating inductive datatype`,
      -- while `genericParamFun` is set to `true` when generating predicate qualifiers.
      if !topts.inTypeDefinition && !topts.genericParamFun then
        generateSortInstDecl t
        let smtSym ← defineSortAndCache v
        return .SymbolSort smtSym
      else if topts.genericParamFun then
        return typeSort
      else -- case when inTypeDefinition is set to true
        -- check if sort has been defined at top level (see note in `translateArrowType`)
        match (← get).smtEnv.sortCache.get? v with
        | some s => -- case when sort defined at top level
           return .SymbolSort s
        | _ => -- case when sort is a param of an inductive data type.
          return .SymbolSort (← sortNameToSmtSymbol v false)

   | Expr.forallE .. =>
       let st ← translateArrowType t topts
       if !topts.inTypeDefinition then
         -- NOTE: predicate qualifier and congruence constraints not generated when translating
         -- fun defined in an inductive predicate
         -- NOTE: use of smt universal type @@Type in predicate qualifier signature,
         -- especially when polymorphic types still remain.
         withInstantiatedImplicitArgs t fun t' => do generateFunInstDecl t' st
       return st

   | Expr.sort .zero =>
        generateSortInstDecl e
        return boolSort -- prop sort represented as bool at smt level

   | Expr.sort .. =>
       throwEnvError "translateType: unexpected sort type {reprStr e}"

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
            -- Need to consider case when fun type has implicit sort type arguments (see `Issue15.thm4`)
            -- In this case, we need to define a sort at top level, i.e.,
            -- reset flags inTypeDefinition and genericParamFun.
            -- We should include the defined sort in fun signature
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
     - Add `n` to the quantified fvars cache.
     - When isType t, e.g., (α : Type or α : Sort u)
       - Call `declareSortAndCache n` to declare an Smt sort and return quantified array `qts` unchanged
     - When ¬ isType t:
        - translate n to an Smt symbol `s`
        - translate t to a Smt type `st`
        - When toplevel flag is set:
           - Call `declareConst s st` to declare a free Smt scalar variable when `st := α` (i.e., scalar type).
           - Call `declareFun s #[α₁ ... αₙ] β` to declare an uninterpreted Smt function when `st := α₁ → ... → αₙ → β`.
        - When toplevel flag is not set:
          - Add (s : st) to quantifier array `qts` when `st := α` (i.e., scalar type)
          - Add (s : Array α₁ ... αₙ β) to quantifier array `qts` when `st := α₁ → ... → αₙ → β`.

    Assume that `t` is not a proposition (i.e., !(← isPropEnv t)) nor a class constraint.
    An error is triggered if `n` is not an `fvar` expression.

    TODO: UPDATE SPEC
-/
def translateQuantifier
  (n : Expr) (t : Expr) (termTranslator : Expr → TranslateEnvT SmtTerm) : QuantifierEnvT Unit := do
 let Expr.fvar v := n | throwEnvError "translateQuantifier: FVarExpr expected but got {reprStr n}"
 -- update quantified fvars cache
 updateQuantifiedFVarsCache v (← get).topLevel
 -- define sort if t is a sort type
 if t.isType then
   generateSortInstDecl t
   discard $ defineSortAndCache v
 else
   -- No more required to resolve type at this stage.
   let smtType ← translateTypeAux termTranslator t
   let smtSym ← fvarIdToSmtSymbol v
   updatePredicateQualifiers t smtSym -- update predicate qualifiers list
   if !(← get).topLevel
   then updateQuantifiers smtSym smtType -- add quantifier to list
   else declareConst smtSym smtType -- declare quantifier at top level

 where
   updatePredicateQualifiers (t : Expr) (smtSym : SmtSymbol) : QuantifierEnvT Unit := do
     let pTerm ← createPredQualifierApp smtSym t
     modify (fun env => { env with premises := env.premises.push pTerm})

   updateQuantifiers (smtSym : SmtSymbol) (smtType: SortExpr) : QuantifierEnvT Unit := do
    modify (fun env => { env with quantifiers := env.quantifiers.push (smtSym, smtType)})


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
   isPatternApp (t : SmtTerm) : Bool :=
     match t with
     | .AppTerm (.SimpleIdent sym) _ =>
         -- we are not considering ite in pattern
         sym != iteSymbol
     | _ => false

   getPattern (t : SmtTerm) : QuantifierEnvT (Option SmtTerm) := do
     match notSmt? t with
     | none => if isPatternApp t then return some t else return none
     | res@(some r) => if isPatternApp r then return res else return none

   genPattern (fbody : SmtTerm) : QuantifierEnvT (Option (Array SmtAttribute)) := do
    let env ← get
    if env.topLevel then return none -- no pattern if toplevel flag set
    let mut patterns := #[]
    for p in env.premises do
      -- we are considering all premises for e-pattern
      if let some p' ← getPattern p then
        patterns := patterns.push p'
    if let some p ← getPattern fbody then
      patterns := patterns.push p
    if patterns.isEmpty
    then return none
    else return some (#[mkPattern patterns])

   genForAllTerm (fbody : SmtTerm) : QuantifierEnvT SmtTerm := do
    let env ← get
    let mut forallTerm := fbody
    let nbPremises := env.premises.size
    for i in [:env.premises.size] do
      let idx := nbPremises - i - 1
      forallTerm := impliesSmt env.premises[idx]! forallTerm
    if env.topLevel then return forallTerm
    if env.quantifiers.isEmpty then return forallTerm -- imply case
    return mkForallTerm none env.quantifiers forallTerm (← genPattern fbody)

   updatePremises (p : SmtTerm) : QuantifierEnvT Unit := do
    modify (fun env => { env with premises := env.premises.push p})


/-- Translate free variable expression `f := Expr.fvar v` to an Smt term such that:
    - When `v ∈ (← get).smtEnv.quantifiedFVars`:
       - return `fvarIdToSmtTerm v
    - When `v ∉ (← get).smtEnv.quantifiedFVars`:
       - add `v` to the quantified fvars cache
       - Let t' ← removeTypeAbbrev (← v.getType)
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
 if ← (isInQuantifiedFVarsCache v) <||> (isPatternMatchFVar v)
 then fvarIdToSmtTerm v
 else
   -- top level declaration case
   updateQuantifiedFVarsCache v true
   let t ← v.getType
   if t.isType then throwEnvError "translateFreeVar: sort type not expected but got {reprStr t}"
   let t' ← removeTypeAbbrev t
   let smtType ← translateTypeAux termTranslator t'
   let smtSym ← fvarIdToSmtSymbol v
   declareConst smtSym smtType -- declare free variable at top level
   let pTerm ← createPredQualifierApp smtSym t'
   assertTerm pTerm
   return (smtSimpleVarId smtSym)

end Solver.Smt
