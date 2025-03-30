import Lean
import Solver.Smt.Env
import Solver.Optimize.Rewriting.Utils

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


/-- Return `some b` if `e := mkAnnotation `_solver.recursivecall b'`. -/
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
    one of the ctor's effective parameters,
      - create expression `ctor.idx x` and tag it as a ctor selector.
      - create the corresponding smt term
      - return both as result
    The tag is used during translation.
-/
def mkCtorSelectorExpr (ctor : Name) (idx : Nat) : (Expr × SmtTerm) :=
  let sctor := s!"{ctor}.{idx}"
  let selectorSym := mkCtorSelectorSymbol ctor idx
  let appExpr := mkApp (mkConst sctor.toName) (mkConst "x".toName)
  let smtTerm := mkSimpleSmtAppN selectorSym #[smtSimpleVarId (mkReservedSymbol "@x")]
  (mkAnnotation `_solver.ctorSelector appExpr, smtTerm)

/-- Given `ctor` a constructor name and an smt term `s`,
    create the smt term application `is-ctor s`.
-/
def mkCtorTestorTerm (ctor : Name) (s : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN (mkNormalSymbol s!"is-{ctor}") #[s]

/-- Given `ctor` a constructor name, create the smt term `is-ctor x`. -/
def mkGenericCtorTestorTerm (ctor : Name) : SmtTerm :=
   mkCtorTestorTerm ctor (smtSimpleVarId (mkReservedSymbol "@x"))


/-- Declare smt universal sort @@Type and its corresponding predicate qualified
    whenever flag `typeUniverse` is not set.
    Do nothing otherwise.
-/
def declareTypeSort : TranslateEnvT Unit := do
 unless ((← get).smtEnv.options.typeUniverse) do
  defineTypeSort
  let env ← get
  set { env with smtEnv.options.typeUniverse := true }

/-- Update sort cache with `v`. -/
def updateSortCache (v : FVarId) (s : SmtSymbol) : TranslateEnvT Unit := do
  let env ← get
  let smtEnv := {env.smtEnv with sortCache := env.smtEnv.sortCache.insert v s}
  set {env with smtEnv := smtEnv}


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
      declareTypeSort
      let s ← sortNameToSmtSymbol v
      defineSort s none typeSort
      updateSortCache v s
      return s
  | some s => return s

/-- Add an inductive datatype name to the visited inductive datatype cache. -/
def cacheIndName (indName : Name) : TranslateEnvT Unit := do
  let env ← get
  let smtEnv := {env.smtEnv with indTypeVisited := env.smtEnv.indTypeVisited.insert indName}
  set {env with smtEnv := smtEnv}


/-- Return `true` when `indName` is already in the visited inductive
    datatype cache (i.e., `indTypeCache`)
-/
def isVisitedIndName (indName : Name) : TranslateEnvT Bool :=
  return (← get).smtEnv.indTypeVisited.contains indName

/-- Given `d` corresponding to a inductive datatype name expression
    or an instantiated polymorphic inductive datatype,
    `n` a unique smt identifier generated for the inductive datatype and
    `instSort` the instantiated Smt inductive datatype, perform the following:
      - add entry `d := {instName := "@is{n}", instSort}` indTypeInstCache
      - return {instName := "@is{n}", instSort}
-/
def updateIndInstCacheAux (d : Expr) (n : SmtSymbol) (instSort : SortExpr) : TranslateEnvT IndTypeDeclaration := do
  let env ← get
  let instName := mkNormalSymbol s!"@is{n}"
  let decl := {instName, instSort}
  let smtEnv := {env.smtEnv with indTypeInstCache := env.smtEnv.indTypeInstCache.insert d {instName, instSort}}
  set {env with smtEnv := smtEnv}
  return decl

/-- Same as `updateIndInstCacheAux` but return value is discarded. -/
def updateIndInstCache (d : Expr) (n : SmtSymbol) (instSort : SortExpr) : TranslateEnvT Unit :=
  discard (updateIndInstCacheAux d n instSort)


/-- Perform the following:
      - add `v` to `quantifierFvars` cache
      - add `v` to `topLevelVars` only when topLevel is set to `true` and `¬ isType (← getType v)`.
-/
def updateQuantifiedFVarsCache (v : FVarId) (topLevel : Bool) : TranslateEnvT Unit := do
  let env ← get
  let s ← fvarIdToSmtSymbol v
  let t ← v.getType
  let topVars := if topLevel && !t.isType then env.smtEnv.topLevelVars.insert s else env.smtEnv.topLevelVars
  set {env with
           smtEnv.quantifiedFVars := env.smtEnv.quantifiedFVars.insert v,
           smtEnv.topLevelVars := topVars
      }

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
  if args.size == 1 then return args[0]!
  return (arraySort args)


/-- Given `n` corresponding to the name of an inductive datatype, and `x₀ ... xₖ` the parameters instantiating
    the inductive datatype, perform the following actions:
     - When k > 0:
         let A := [x₀, ..., xₖ]
         let B := [typeTranslator A[i] | i ∈ [0..k] ∧ ¬ isClassConstraintExpr (← inferType A[i])]
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
 for i in [:args.size] do
   if !(← isClassConstraintExpr (← inferType args[i]!)) then -- ignore class constraints
     iargs := iargs.push (← typeTranslator args[i]!)
 return (.ParamSort indSym iargs)


/-- Given arguments `x₀ ... xₙ` perform the following:
      let A := [x₀, ..., xₙ]
      let V := {α | i ∈ [0..n] ∧ α ∈ getFVarsInExpr A[i] ∧ isGenericParam A[i]}
      return `[α | α ∈ V]`
-/
def retrieveGenericArgs (args : Array Expr) : TranslateEnvT (Array Expr) := do
  let mut genericArgs := #[]
  let mut knownGenParams := (.empty : Std.HashSet Expr)
  for i in [:args.size] do
    if (← isGenericParam args[i]! (skipInductiveCheck := true)) then
      (genericArgs, knownGenParams) ← updateGenericArgs args[i]! genericArgs knownGenParams
  return genericArgs

where
   updateGenericArgs (e : Expr) (gargs : Array Expr) (pset : Std.HashSet Expr) : MetaM (Array Expr × Std.HashSet Expr) := do
     let fvars ← getFVarsInExpr e
     let mut mgargs := gargs
     let mut mpset := pset
     for i in [:fvars.size] do
       let p := fvars[i]!
       if !(pset.contains p) then
         mgargs := mgargs.push p
         mpset := mpset.insert p
     return (mgargs, mpset)

/-- Given an inductive datatype instance `t x₀ ... xₙ`, perform the following:
     - When `∀ i ∈ [0..n], ¬ isGenericParam xᵢ`,
         - return `t x₁ ... xₙ`
     - When `∃ i ∈ [0..n], isGenericParam xᵢ`,
        let A := [x₀, ..., xₙ]
        let V := {α | i ∈ [0..n] ∧ α ∈ getFVarsInExpr A[i] ∧ isGenericParam A[i] ∧ a ≠ A[i]}
        let B := [α | α ∈ V] ++ [A[i] | i ∈ [0..n] ∧ isGenericParam A[i] ∧ isFVar A[i]]
        let [b₀ ... bₘ ] := B
          - return `λ b₀ → .. → bₘ → t x₀ ... xₙ`
-/
def getIndInst (t : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  let genericArgs ← retrieveGenericArgs args
  let auxApp := mkAppN t args
  mkLambdaFVars genericArgs auxApp


/-- Given `t := Expr.const n _` corresponding to an inductive datatype name and
    `args` the parameters instantiating the inductive datatype (if any),
    perform the following actions:
     - When args.size > 0:
         - instName := nameToSmtSymbol (n ++ (← mkFreshId)) (i.e., generate a unique name for instance)
         - instSort ← generateInstType n args typeTranslator
         - instApp ← getIndInst t args
         - add entry `instApp := {instName, instSort}` to `indTypeInstCache`
         - return {instName, instSort}
    - When args.size = 0:
        - instName := nameToSmtSymbol n
        - instSort ← generateInstType n args typeTranslator
        - add entry `t := {instName, instSort}` to `indTypeInstCache`
        - return `{instName, instSort}`
    Assumes that `t` corresponds to the name of an inductive datatype.
-/
def generateIndInstDecl
  (t : Expr) (args : Array Expr)
  (typeTranslator : Expr → TranslateEnvT SortExpr) : TranslateEnvT IndTypeDeclaration := do
 let Expr.const n _ := t | throwEnvError f!"generateIndInstDecl: name expression expected but got {reprStr t}"
 let instSort ← generateInstType n args typeTranslator
 if args.size == 0
 then
   let instName := nameToSmtSymbol n
   updateIndInstCacheAux t instName instSort
 else
   let v ← mkFreshId
   let instName := nameToSmtSymbol (n ++ v)
   let instApp ← getIndInst t args
   updateIndInstCacheAux instApp instName instSort

/-- Given `t := α₀ → α₁ ... → αₙ`, perform the following:
     - When `∀ i ∈ [0..n], ¬ isGenericParam αᵢ`,
         - return `t`
     - When `∃ i ∈ [0..n], isGenericParam αᵢ`,
        let A := [α₀, ..., αₙ]
        let V := {v | i ∈ [0..n] ∧ v ∈ getFVarsInExpr A[i] ∧ isGenericParam A[i] ∧ a ≠ A[i]}
        let B := [v | v ∈ V] ++ [A[i] | i ∈ [0..n] ∧ isGenericParam A[i]]
        let [b₀ ... bₘ ] := B
          - return `λ b₀ → .. → bₘ → t`
-/
def getFunInstDecl (t : Expr) : TranslateEnvT Expr := do
  let genericArgs ← retrieveGenericArgs (retrieveArrowTypes t #[])
  mkLambdaFVars genericArgs t

 where
   retrieveArrowTypes (e : Expr) (arrowTypes : Array Expr) : Array Expr :=
     match e with
     | Expr.forallE _ t b _ => retrieveArrowTypes b (arrowTypes.push t)
     | _ => arrowTypes.push e

/-- Given `t := α₁ → α₂ ... → αₙ` and `st` its corresponding smt representation (i.e., Array α₁ α₂ αₙ),
    perform the following action only when no entry exists in `indTypeInstCache` for `getFunInstDecl t`:
      - instName ←  (Fun ++ (← mkFreshId)) (i.e., generate a unique name for function instance)
      - add entry `t := {instName, st}` to `indTypeInstCache`
      - declare smt predicate function `@is{instName} (@x : st) Bool`
-/
def generateFunInstDecl (t : Expr) (st : SortExpr) : TranslateEnvT Unit := do
  let funInst ← getFunInstDecl t
  unless ((← get).smtEnv.indTypeInstCache.get? funInst).isSome do
   let v ← mkFreshId
   let instName := mkNormalSymbol s!"Fun{v}"
   let decl ← updateIndInstCacheAux funInst instName st
   declareFun (decl.instName) #[decl.instSort] boolSort


/-- Given `t := Expr.sort _` perform the following actions only when
    no entry for `t` exists in `indTypeInstCache`:
     - When `t := Expr.sort .zero`
        - add entry `t := {@isProp, propSort} to `indTypeInstCache`
        - define Smt sort `(define-sort Prop () Bool)`
        - declare smt predicate function `(declare-fun @isProp (Prop) Bool)`

     - When `t.isType`
         - add entry `t := {@isType, typeSort} to `indTypeInstCache`

    An error is triggered when t is not the expected sort type.
-/
def generateSortInstDecl (t : Expr) : TranslateEnvT Unit := do
 let Expr.sort u := t | throwEnvError f!"generateSortInstDecl: sort type expected but got {reprStr t}"
 unless ((← get).smtEnv.indTypeInstCache.get? t).isSome do
   match u with
   | .zero =>
        updateIndInstCache t (mkReservedSymbol "Prop") propSort
        definePropSort
   | _ =>
       if !t.isType then throwEnvError f!"generateSortInstDecl: sort type expected but got {reprStr t}"
       updateIndInstCache t (mkReservedSymbol "Type") typeSort

/-- TODO: UPDATE SPEC -/
def getRecRuleFor (recVal : RecursorVal) (c : Name) : TranslateEnvT RecursorRule :=
   match (recVal.rules.find? fun r => r.ctor == c) with
    | some r => return r
    | none => throwEnvError f!"getRecRuleFor: no RecursorRule found for {c}"

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
  /-- flag set to true only when translating function/lambda parameters. -/
  forFunLambdaParam : Bool := false

deriving Inhabited

/-- type options to be used when translating inductive datatype. -/
def optionsForInductiveType : TypeOptions :=
  { inTypeDefinition := true, genericParamFun := false, forFunLambdaParam := false}

/-- type options to be used when generating predicate qualifiers. -/
def optionsForPredicateQualifier : TypeOptions :=
  { inTypeDefinition := true, genericParamFun := true, forFunLambdaParam := false}

/-- Return a TypeOptions instance where flag `forFunLambdaParam` is set to `b`. -/
def optionsForFunLambdaParam (b : Bool) : TypeOptions :=
  { inTypeDefinition := false, genericParamFun := b, forFunLambdaParam := true}

/-- TODO: UPDATE SPEC

Given `indValStart` an inductive value info for an inductive datatype and an optimization function `optimizer`,
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
    let ConstantInfo.inductInfo indVal ← getConstInfo indName
      | throwEnvError f!"translateInductiveType: no InductInfo found for {indName}"
    -- recVal to get the list of RecusorRule for all ctors
    let ConstantInfo.recInfo recVal ← getConstInfo (mkRecName indName)
      | throwEnvError f!"translateInductiveType: {mkRecName indName} not a recinfo"
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
     forallTelescope indVal.type fun xs _ => do
        let mut polyParams := #[]
        for i in [: xs.size] do
          let arg := xs[i]!
          let argType ← inferType arg
          if !(← isClassConstraintExpr argType) then -- ignore class constraints
            let Expr.fvar v := arg
              | throwEnvError f!"translateInductiveType: FVarExpr expected but got {reprStr arg}"
            -- resolve type abbreviation (useful when handling instance parameters)
            -- TODO: IMP need to apply optimizer on argument to instance parameters
            let argType' ← removeTypeAbbrev argType
            if argType'.isType then
              polyParams := polyParams.push (← sortNameToSmtSymbol v false)
            else throwEnvError f!"Inductive datatype with instance parameters not supported: {reprStr indVal.name}"
        return polyParams
   if params.isEmpty then return none else return (some params)

  createCtorDeclaration (recVal : RecursorVal) (recRule : RecursorRule) : TranslateEnvT SmtConstructorDecl := do
    let ctorSym := nameToSmtSymbol recRule.ctor
    let firstCtorFieldIdx := recVal.numParams + recVal.numMotives + recVal.numMinors
    forallTelescope (← inferType recRule.rhs) fun xs _ => do
      if recRule.nfields == 0 then return (ctorSym, none) -- nullary constructor
      let mut selectors := #[]
      for i in [firstCtorFieldIdx : xs.size] do
        let arg := xs[i]!
        let selectorIdx := i - firstCtorFieldIdx + 1
        let argType ← inferType arg
        let selSym := mkNormalSymbol s!"{ctorSym}.{selectorIdx}"
        if (← isProp argType) then
          selectors := selectors.push (selSym, boolSort)
        else
          -- resolve type abbreviation
          let argType' ← removeTypeAbbrev argType
          selectors := selectors.push (selSym, ← typeTranslator argType')
      return (ctorSym, some selectors)

  createCtorDecls (recVal : RecursorVal) (ctors : List Name) : TranslateEnvT (Array SmtConstructorDecl) := do
   let mut ctorDecls := (#[] : Array SmtConstructorDecl)
   for c in ctors do
     let ctorDecl ← createCtorDeclaration recVal (← getRecRuleFor recVal c)
     ctorDecls := ctorDecls.push ctorDecl
   return ctorDecls


/-- Return `decl.instName` when `t := decl` exists in `indTypeInstCache`.
    Otherwise `none`.
    TODO: UPDATE
-/
def getPredicateQualifierName (t : Expr) : TranslateEnvT (Option SmtSymbol) := do
  let t' ← getType t
  let typeInst ← getInst t'
  match (← get).smtEnv.indTypeInstCache.get? typeInst with
  | some decl => return decl.instName
  | none => return none

 where
  getInst (e : Expr) : TranslateEnvT Expr :=
    if e.isForall then
      getFunInstDecl e -- arrow type case
    else
      let f := e.getAppFn
      getIndInst f e.getAppArgs

  getType (e : Expr) : TranslateEnvT Expr :=
   match e with
   | Expr.fvar v => v.getType
   | _ => pure e


structure FunctionDefinitions where
  funDecls : Array SmtFunDecl
  funBodies : Array SmtTerm
  isRec : Bool
deriving Inhabited

abbrev FunctionGenEnv := StateRefT FunctionDefinitions TranslateEnvT

def defineFunctions (defs : FunctionDefinitions) : TranslateEnvT Unit := do
 if defs.funDecls.size == 1 then
   let funDecl := defs.funDecls[0]!
   defineFun funDecl.name funDecl.params funDecl.ret defs.funBodies[0]! defs.isRec
 else defineMutualFuns defs.funDecls defs.funBodies

/-- TODO: UPDATE SPEC -/
partial def defineInstPredicateQualifier
    (typeTranslator : Expr → TranslateEnvT SortExpr)
    (termTranslator : Expr → TranslateEnvT SmtTerm)
    (optimizer : Expr → TranslateEnvT Expr)
    (t : Expr) (args : Array Expr) : TranslateEnvT Unit := do
 -- get inst application
 let instApp ← getIndInst t args
 unless ((← get).smtEnv.indTypeInstCache.get? instApp).isSome do
  let (indVal, (indName, (us, decl))) ← declareIndInst t args
  if (← isEnumeration indVal) then
    declareFun decl.instName #[decl.instSort] boolSort
  else
    let (_, defs) ← generatePredicates indName us indVal decl args|>.run default
    defineFunctions defs

where
  isEnumeration (indVal : InductiveVal) : TranslateEnvT Bool := do
   match indVal.all with
    | [n] =>
      let ConstantInfo.recInfo recVal ← getConstInfo (mkRecName n)
        | throwEnvError f!"isEnumeration: {mkRecName n} not a recinfo"
      for c in indVal.ctors do
        if (← getRecRuleFor recVal c).nfields != 0 then return false
      return true
    | _ => return false

  declareIndInst (t : Expr) (args : Array Expr) :
    TranslateEnvT (InductiveVal × Name × List Level × IndTypeDeclaration) := do
     let decl ← generateIndInstDecl t args typeTranslator
     let Expr.const indName l := t
       | throwEnvError f!"declareIndInst: name expression expected but got {reprStr t}"
     let ConstantInfo.inductInfo indVal ← getConstInfo indName
       | throwEnvError f!"declareIndInst: inductive info expected for {indName}"
     return (indVal, indName, l, decl)

  generatePredicates
    (indName : Name) (us : List Level) (indVal : InductiveVal)
    (decl : IndTypeDeclaration) (args : Array Expr) (inMutualDefinition := false) : FunctionGenEnv Unit := do
   let ConstantInfo.recInfo recVal ← getConstInfo (mkRecName indName)
     | throwEnvError f!"generatePredicates: {mkRecName indName} not a recinfo"
   let funDecl := {name := decl.instName, params := #[(mkReservedSymbol "@x", decl.instSort)], ret := boolSort}
   let mut funBody := trueSmt
   for c in indVal.ctors do
     funBody ← updatePredicateBody indName us recVal (← getRecRuleFor recVal c) args funBody inMutualDefinition
   let env ← get
   let funDecls := env.funDecls.push funDecl
   let funBodies := env.funBodies.push funBody
   set { env with funDecls := funDecls, funBodies := funBodies, isRec := indVal.isRec }

  substitutePred (sub : Expr × Expr) (e : Expr) : Option Expr :=
    if sub.1 == e then some sub.2 else none -- TODO: check if we can use pointer equality

  addCtorIteCase (recRule : RecursorRule) (propList : List SmtTerm) (funBody : SmtTerm) : FunctionGenEnv SmtTerm := do
    if recRule.nfields == 0 then return funBody -- nullary constructor case
    match propList with
    | [] => throwEnvError "addCtorIteCase: at least one element expected in propList"
    | firstTerm :: nextTerms =>
        let thenTerm := nextTerms.foldl (fun a acc => andSmt a acc) firstTerm
        return (iteSmt (mkGenericCtorTestorTerm recRule.ctor) thenTerm funBody)

  hasMutualDataType (recVal : RecursorVal) (t : Expr) : Bool :=
    let rec visit (t : Expr) (k : Bool → Bool) :=
      match (t : Expr) with
      | Expr.const n _ => k (recVal.all.contains n)
      | Expr.app f arg =>
           visit f
            (fun rf' =>
              if rf' then k rf'
              else visit arg (fun rarg' => k rarg'))
      | _ => k false
    visit t id

  updatePredicateBody
    (indName : Name) (us : List Level)
    (recVal : RecursorVal) (recRule : RecursorRule)
    (args : Array Expr) (funBody : SmtTerm) (inMutualDefinition : Bool) : FunctionGenEnv SmtTerm := do
    let cinfo ← getConstInfo indName
    let auxApp := (mkAppN recRule.rhs args).instantiateLevelParams cinfo.levelParams us
    let firstCtorFieldIdx := recVal.numMotives + recVal.numMinors
    -- NOTE: recVal.numParams is ignored here when determining firstCtorFieldIdx
    -- as we are instantiating the datatype parameters
    forallTelescope (← inferType auxApp) fun xs _ => do
      -- list to replace each ctor field with appropriate selector name
      let mut substituteList := []
      -- list of prop terms generated for each proposition argument (if any) of the current ctor
      -- as well as predicate qualifier term generated of each non proposition arguments.
      let mut predTermList := []
      for i in [firstCtorFieldIdx : xs.size] do
        let arg := xs[i]!
        let selectorIdx := i - firstCtorFieldIdx + 1
        let selTerms := mkCtorSelectorExpr recRule.ctor selectorIdx
        substituteList := (arg, selTerms.1) :: substituteList
        let argType ← inferType arg
        if (← isProp argType) then
          let optExpr ← optimizer argType
          -- apply substitue list on optExpr before translation
          let propTerm ← termTranslator (substituteList.foldr (fun a acc => acc.replace (substitutePred a)) optExpr)
          predTermList := (andSmt (eqSmt selTerms.2 propTerm) selTerms.2) :: predTermList
        else
          -- resolve type abbreviation first
          let argType' ← resolveTypeAbbrev argType
          match (← getPredicateQualifierName argType') with
          | some instName => predTermList := mkSimpleSmtAppN instName #[selTerms.2] :: predTermList
          | none =>
              -- instantiated polymorphic inductive datatype expected
              let t := argType'.getAppFn
              let t_args := argType'.getAppArgs
              if inMutualDefinition || hasMutualDataType recVal argType' then -- mututal datatype case
                let (indVal, (indName', (l, decl))) ← declareIndInst t t_args
                generatePredicates indName' l indVal decl t_args (inMutualDefinition := true)
              else -- other inductive datatype
                defineInstPredicateQualifier typeTranslator termTranslator optimizer t t_args
              let some instName ← getPredicateQualifierName argType'
                  | throwEnvError f!"updatePredicateBody: predicate qualifier name expected for {reprStr argType'}"
              predTermList := mkSimpleSmtAppN instName #[selTerms.2] :: predTermList
      addCtorIteCase recRule predTermList funBody


/-- TODO: UPDATE SPEC. -/
def translateNonOpaqueType
  (t : Expr) (args : Array Expr)
  (typeTranslator : Expr → TypeOptions → TranslateEnvT SortExpr)
  (termTranslator : Expr → TranslateEnvT SmtTerm)
  (optimizer : Expr → TranslateEnvT Expr)
  (topts : TypeOptions) :
  TranslateEnvT SortExpr := do
  match t with
  | Expr.const n _ =>
      if (← isVisitedIndName n) then return (← translateInstType n)
      let ConstantInfo.inductInfo indVal ← getConstInfo n
        | throwEnvError f!"translateNonOpaqueType: inductive info expected for {n}"
      -- we should not define sort for polymorphic inductive parameters,
      -- we should set genericParamFun to `false` and inTypeDefinition to `true`
      translateInductiveType indVal (λ e => typeTranslator e optionsForInductiveType)
      return (← translateInstType n)
  | _ => throwEnvError f!"translateNonOpaqueType: name expression expected but got {reprStr t}"

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
        if !topts.forFunLambdaParam then
          -- generate predicate qualifier
          -- reset indTypeDefinition flag and set genericParamFun to `true`
          defineInstPredicateQualifier (λ e => typeTranslator e optionsForPredicateQualifier)
            termTranslator optimizer t args
       return smtType


/-- Given `n` a name expression for which a corresponding smt sort exists (e.g., Bool, Int, String),
    `s` its corresponding Smt symbol and `t` its corresponding Smt sort,
    perform the following actions:
     - When entry `n := s` exists in `indTypeInstCache` return #[t]
     - Otherwise:
        - add entry `n := s` in `indTypeInstCache`
        - declare smt predicate function `@is{s} (@x : s) Bool`
        - return #[t]
-/
def translateSmtEquivType (n : Expr) (s : SmtSymbol) (t : SortExpr) : TranslateEnvT SortExpr := do
 match (← get).smtEnv.indTypeInstCache.get? n with
 | none =>
    updateIndInstCache n s t
    definePredQualifier s t none
    return t
 | some decl => return decl.instSort


/-- Perform the following actions:
     - When entry `n := "Nat"` exists in `indTypeInstCache` return #[natSort]
     - Otherwise:
        - add entry `n := "Nat"` in `indTypeInstCache`
        - define Smt sort `(define-sort Nat () Int)`
        - define Smt predicate function `@isNat (@x : Nat) := (<= 0 @x)`
        - return #[natSort]
  Assume that `n := Expr.const ``Nat []`.

-/
def translateNatType (n : Expr) : TranslateEnvT SortExpr := do
 match (← get).smtEnv.indTypeInstCache.get? n with
 | none =>
    updateIndInstCache n natSymbol natSort
    defineNatSort
    return natSort
 | some decl => return decl.instSort


/-- Perform the following actions:
     - When entry `n := "Empty"` exists in `indTypeInstCache` return #[emptySort]
     - Otherwise:
        - add entry `n := "Empty"` in `indTypeInstCache`
        - declare Smt sort `(declare-sort Empty 0)`
        - define Smt predicate function `@isEmpty (@x : Empty) := false`
        - return #[emptySort]
  Assume that `n := Expr.const ``Empty []`.
-/
def translateEmptyType (n : Expr) : TranslateEnvT SortExpr := do
 match (← get).smtEnv.indTypeInstCache.get? n with
 | none =>
    updateIndInstCache n emptySymbol emptySort
    defineEmptySort
    return emptySort
 | some decl => return decl.instSort


/-- Perform the following actions:
     - When entry `n := "PEmpty"` exists in `indTypeInstCache` return #[pemptySort]
     - Otherwise:
        - add entry `n := "PEmpty"` in `indTypeInstCache`
        - declare Smt sort `(declare-sort PEmpty 0)`
        - define Smt predicate function `@isPEmpty (x : PEmpty) := false`
        - return #[pemptySort]
  Assume that `n := Expr.const ``PEmpty [..]`.
-/
def translatePEmptyType (n : Expr) : TranslateEnvT SortExpr := do
 match (← get).smtEnv.indTypeInstCache.get? n with
 | none =>
    updateIndInstCache n pemptySymbol pemptySort
    definePEmptySort
    return pemptySort
 | some decl => return decl.instSort


/-- Translate opaque sorts to their Smt counterpart.
    An error is triggered when `e` does not correspond to a name expression.
    TODO: update function when opacifying other Lean inductive types (e.g., BitVector, Char, etc).
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
 | _ => throwEnvError f!"translateOpaqueType: name expression expected but got {reprStr e}"

/-- TODO: UPDATE SPEC -/
partial def translateTypeAux
  (optimizer : Expr → TranslateEnvT Expr)
  (termTranslator : Expr → TranslateEnvT SmtTerm)
  (t : Expr) (topts := (default : TypeOptions)) :
  TranslateEnvT SortExpr := do
   let e := t.getAppFn
   match e with
   | Expr.const .. =>
      if let some r ← translateOpaqueType e then return r
      translateNonOpaqueType e t.getAppArgs
        (λ a b => translateTypeAux optimizer termTranslator a b)
        termTranslator optimizer topts

   | Expr.fvar v =>
      let t ← v.getType
      if !t.isType then throwEnvError f!"translateType: sort type expected but got {reprStr t}"
      -- Need to call defineSortAndCache to handle case when sort is defined a top level
      -- `defineSortAndCache` is called only flags `inTypeDefinition` and `genericParamFun`
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
        return .SymbolSort (← sortNameToSmtSymbol v false)

   | Expr.forallE .. =>
       let st ← translateArrowType e topts #[]
       if !topts.forFunLambdaParam then
         -- NOTE: generate predicate qualifier not generated when translating
         -- function and lambda parameters.
         generateFunInstDecl t (← translateArrowType e (optionsForFunLambdaParam true) #[])
       return st

   | Expr.sort .zero =>
        generateSortInstDecl e
        return boolSort -- prop sort represented as bool at smt level

   | Expr.sort .. =>
       throwEnvError f!"translateType: unexpected sort type {reprStr e}"

   | _ => throwEnvError f!"translateType: type expression expected but got {reprStr e}"

 where
   translateArrowType (e : Expr) (opts : TypeOptions) (arrowArgs : Array SortExpr) : TranslateEnvT SortExpr := do
     match e with
     | Expr.forallE _ t b _ =>
         translateArrowType b opts (arrowArgs.push (← translateTypeAux optimizer termTranslator t opts))
     | _ => return arraySort (arrowArgs.push (← translateTypeAux optimizer termTranslator e opts))

/-- TODO: UPDATE SPEC -/
def translateType
  (optimizer : Expr → TranslateEnvT Expr)
  (termTranslator : Expr → TranslateEnvT SmtTerm)
  (t : Expr) (topts := (default : TypeOptions)) :
  TranslateEnvT SortExpr := do
  -- resolve type abbreviation first
  translateTypeAux optimizer termTranslator (← removeTypeAbbrev t) topts


structure QuantifierEnv where
  quantifiers: SortedVars
  premises : Array SmtTerm
  topLevel : Bool
deriving Inhabited

abbrev QuantifierEnvT := StateRefT QuantifierEnv TranslateEnvT


def initialQuantifierEnv (topLevel : Bool) : QuantifierEnv :=
  { quantifiers := #[], premises := #[], topLevel }



/-- Given `v` an smt symbol corresponding to either a forall quantifier or a globally declared variable,
    and `t` its corresponding type expresson, perform the following:
     - retrieve predicate qualifier name `instName` for `t`
     - return smt application (instName v)
    An error is triggered if the predicate qualifier name for `t` does not exists.
    Assume that there is no type abbreviation in `t`, i.e., call to `removeTypeAbbrev` has been applied.
-/
def createPredQualifierApp (smtSym : SmtSymbol) (t : Expr) : TranslateEnvT SmtTerm := do
  let some instName ← getPredicateQualifierName t
    | throwEnvError f!"createPredQualifierApp: predicate qualifier name expected for {reprStr t}"
  return (mkSimpleSmtAppN instName #[smtSimpleVarId smtSym])

/-- Translate a quantifier `(n : t)` by performing the following actions:
     - Add `n` to the quantified fvars cache.
     - When t.isType, e.g., (α : Type)
       - Call `declareSortAndCache n` to declare an Smt sort and return quantified array `qts` unchanged
     - When ¬ (t.isType):
        - translate n to an Smt symbol `s`
        - translate t to a Smt type `st`
        - When toplevel flag is set:
           - Call `declareConst s st` to declare a free Smt scalar variable when `st := α` (i.e., scalar type).
           - Call `declareFun s #[α₁ ... αₙ] β` to declare an uninterpreted Smt function when `st := α₁ → ... → αₙ → β`.
        - When toplevel flag is not set:
          - Add (s : st) to quantifier array `qts` when `st := α` (i.e., scalar type)
          - Add (s : Array α₁ ... αₙ β) to quantifier array `qts` when `st := α₁ → ... → αₙ → β`.

    Assume that `t` is not a proposition (i.e., !(← isProp t)) nor a class constraint.
    An error is triggered if `n` is not an `fvar` expression.

    TODO: UPDATE SPEC
-/
def translateQuantifier
  (n : Expr) (t : Expr)
  (optimizer : Expr → TranslateEnvT Expr)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : QuantifierEnvT Unit := do
 let Expr.fvar v := n | throwEnvError f!"translateQuantifier: FVarExpr expected but got {reprStr n}"
 -- update quantified fvars cache
 updateQuantifiedFVarsCache v (← get).topLevel
 -- define sort if t is a sort type
 if t.isType then
   generateSortInstDecl t
   discard $ defineSortAndCache v
 else
   let t' ← removeTypeAbbrev t
   let smtType ← translateTypeAux optimizer termTranslator t'
   let smtSym ← fvarIdToSmtSymbol v
   updatePredicateQualifiers t' smtSym -- update predicate qualifiers list
   if !(← get).topLevel
   then updateQuantifiers smtSym smtType -- add quantifier to list
   else declareConst smtSym smtType -- declare quantifier at top level

 where
   updatePredicateQualifiers (t : Expr) (smtSym : SmtSymbol) : QuantifierEnvT Unit := do
     let env ← get
     let pTerm ← createPredQualifierApp smtSym t
     set { env with premises := env.premises.push pTerm }

   updateQuantifiers (smtSym : SmtSymbol) (smtType: SortExpr) : QuantifierEnvT Unit := do
    let env ← get
    set {env with quantifiers := env.quantifiers.push (smtSym, smtType)}


/-- TODO: UPDATE SPEC -/
def translateForAll
  (e : Expr) (optimizer : Expr → TranslateEnvT Expr)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : QuantifierEnvT SmtTerm := do
 forallTelescope e fun xs b => do
   for i in [:xs.size] do
     let t ← inferType xs[i]!
     if (← isProp t) then
       updatePremises (← termTranslator t)
     -- need to filter out class constraints
     else if !(← isClassConstraintExpr t) then
       translateQuantifier xs[i]! t optimizer termTranslator
   let fbody ← termTranslator b
   genForAllTerm fbody

 where
   isPatternApp (t : SmtTerm) : Bool :=
     match t with
     | .AppTerm (.SimpleIdent sym) _ =>
         -- we are not considering relational and ite in pattern
         sym != leqSymbol && sym != ltSymbol && sym != iteSymbol
     | _ => false

   getPattern (t : SmtTerm) : QuantifierEnvT (Option SmtTerm) := do
     if let some (op1, op2) := eqSmt? t
     then match isPatternApp op1, isPatternApp op2 with
          | true, true -- left operand considered for pattern
          | true, false => return (some op1)
          | false, true => return (some op2)
          | false, false => return none
     if isPatternApp t then return some t else return none

   genPattern (fbody : SmtTerm) : QuantifierEnvT (Option (Array SmtAttribute)) := do
    let env ← get
    let mut patterns := env.premises -- we are considering all premises for e-pattern
    if env.topLevel then return none -- no pattern if toplevel flag set
    if let some p ← getPattern fbody
    then patterns := patterns.push p
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
    let env ← get
    set {env with premises := env.premises.push p}


/-- Translate free variable expression `f := Expr.fvar v` to an Smt term such that:
    - When `v ∈ (← get).smtEnv.quantifiedFVars`:
       - return `fvarIdToSmtTerm v
    - When `v ∉ (← get).smtEnv.quantifiedFVars`:
       -  add `v` to the quantified fvars cache
       - smtType ← translateType optimize termTranslator (← v.getType)
       - smtSym ← fvarIdToSmtSymbol v
       - declare smt symbol at top level, i.e., `(declare-const smtSym smtType)`
       - pTerm ← createPredQualifierApp smtSym (← v.getType)
       - assert pTerm at smt level, i.e., `(assert pTerm)`
       - return `smtSimpleVarId smtSym`
    An error is triggered when
      - `f` is not an `fvar` expression; or
      - `f` has a sort type
-/
def translateFreeVar
  (f : Expr) (optimizer : Expr → TranslateEnvT Expr)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
 let Expr.fvar v := f | throwEnvError f!"translateFreeVar: FVarExpr expected but got {reprStr f}"
 if ← (isInQuantifiedFVarsCache v) <||> (isPatternMatchFVar v)
 then fvarIdToSmtTerm v
 else
   -- top level declaration case
   updateQuantifiedFVarsCache v true
   let t ← v.getType
   if t.isType then throwEnvError f!"translateFreeVar: sort type not expected but got {reprStr t}"
   let t' ← removeTypeAbbrev t
   let smtType ← translateTypeAux optimizer termTranslator t'
   let smtSym ← fvarIdToSmtSymbol v
   declareConst smtSym smtType -- declare free variable at top level
   let pTerm ← createPredQualifierApp smtSym t'
   assertTerm pTerm
   return (smtSimpleVarId smtSym)

end Solver.Smt
