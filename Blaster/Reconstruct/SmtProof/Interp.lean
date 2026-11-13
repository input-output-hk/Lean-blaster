import Lean
import Blaster.Reconstruct.SmtProof.Term
import Blaster.Reconstruct.SmtProof.SortInfer

/-!
# Interpretation of SMT terms in Lean

SMT terms occurring in a proof are interpreted as Lean terms:
 - `Int`-sorted terms are interpreted as Lean `Int` terms. Lean terms of type `Nat` occurring in
   `Int` positions are cast (`(↑n : Int)`), and `Int` terms occurring in Lean positions of type `Nat`
   (e.g., arguments of Lean functions, constructor fields) are converted with `Int.toNat`;
 - `Bool`-sorted terms are interpreted as propositions, and converted with `decide` (resp. `= true`)
   when a Lean `Bool` is expected (resp. given);
 - other sorts (e.g., datatypes, `String`, uninterpreted sorts) are interpreted as the corresponding
   Lean types; the sorts `@Instance` and `@Type` of Blaster's polymorphic encoding are interpreted as a
   sort variable and `Unit`, or as the universe `Poly.Univ.{u}` of the values of `Sort u` and `Sort u`
   (see `Poly.lean`).

The interpretation of the symbols of the query is given by a `SymTable`. Each step of an SMT proof is
then replayed as a Lean proof of the interpretation of its conclusion. Since the Lean proof is checked by
the kernel, an inadequate interpretation (e.g., a step that is not valid for the chosen interpretation)
only results in a failed replay.
-/

open Lean Meta

namespace Blaster.Reconstruct.SmtProof

/-- Interpretation of an SMT function symbol. -/
inductive SymInterp where
  /-- a Lean term (constant, free variable, function): applications are built with casts on arguments -/
  | expr (e : Expr)
  /-- an SMT macro (`define-fun`), expanded during interpretation -/
  | macro (params : Array (String × SExpr)) (body : STerm)
  /-- a type predicate of Blaster's encoding, interpreted as `fun _ => True` -/
  | trueFun
  /-- a Lean function given as a lambda (e.g., the membership predicates of the polymorphic encoding, see
      `Poly.lean`): applications are β-reduced -/
  | lam (e : Expr)
  /-- a datatype constructor -/
  | ctor (n : Name)
  /-- a datatype selector: constructor, index of the field -/
  | selector (ctor : Name) (idx : Nat)
  /-- a datatype tester -/
  | tester (ctor : Name)
  /-- application of a function value (Blaster's `@apply` functions for higher-order arguments) -/
  | apply
  /-- skolem function of Z3's `sk` steps: for `¬ ∀ x, φ(ys, x)` (resp. `∃ x, φ(ys, x)`) where `ys` are the
      variables of the context, `fun ys => ε x, ¬ φ(ys, x)` (resp. `ε x, φ(ys, x)`) -/
  | skolem (params : Array String) (x : String) (sort : SExpr) (body : STerm) (neg : Bool)
  deriving Inhabited

/-- Interpretation of the symbols and sorts of an SMT query. -/
structure SymTable where
  syms : Std.HashMap String SymInterp := {}
  /-- sort symbols (after alias expansion) to Lean type constructors -/
  sorts : Std.HashMap String Expr := {}
  /-- sort aliases (`define-sort` without parameters) -/
  aliases : Std.HashMap String SExpr := {}
  /-- Lean types of the datatype sorts as they occur in proofs (aliases expanded), e.g., `(@List Int) ↦ List Nat`
      when the query only uses `(@List Nat)`. -/
  expandedSorts : Std.HashMap String Expr := {}
  /-- guards of Z3's case predicates of recursive functions `((_ case-def k f) args)`, per key `k f` (see
      `caseDefKey?`): arguments of the predicate and guard (see `RecFun.lean`) -/
  caseGuards : Std.HashMap String (Array (Array STerm × STerm)) := {}
  deriving Inhabited

/-- Key `k f` of the indices `k (_ f 0)` of a case predicate `((_ case-def k (_ f 0)) args)` (Z3). -/
def caseDefKey? (idx : Array STerm) : Option String :=
  match idx[0]?, idx[1]? with
  | some (STerm.num k), some (STerm.iapp f _ #[]) | some (STerm.num k), some (STerm.sym f)
  | some (STerm.num k), some (STerm.app f #[]) => some s!"{k} {f}"
  | _, _ => none

structure InterpCtx where
  table : SymTable
  /-- bound variables (quantifiers, `proof-bind`, fresh definitions) -/
  locals : Std.HashMap String Expr := {}
  /-- interpretation of the (closed) terms already interpreted, on term object addresses: terms are
      shared DAGs (e.g., after the expansion of `let`), which must not be traversed as trees; the terms are kept alive
      (see `TermMemo`), e.g., the quantifiers built for the conclusions of `proof-bind` steps -/
  cache : Option (IO.Ref (TermMemo Expr)) := none
  /-- the type parameters of applications that nothing determines are left as metavariables, to be assigned by
      unification with the context or defaulted after the interpretation of the whole term (see `defaultTypes`) -/
  deferTypes : Bool := false
  /-- interpretation of the terms already interpreted in the current scope of local variables (e.g., the body
      of a macro for given arguments): set when the scope is entered (see `withScopeCache`) -/
  scopeCache : Option (IO.Ref (TermMemo Expr)) := none
  /-- instances of the constructor applications that their arguments don't determine (e.g., `List.nil`), inferred on
      the whole proof (see `SortInfer`), on term object addresses -/
  sortHints : TermCache SortInfer.Hint := {}
  /-- the hints of the terms interpreted with undetermined types (see `withSortHint`) -/
  pendingHints : Option (IO.Ref (Array (Expr × SortInfer.Hint))) := none

abbrev InterpM := ReaderT InterpCtx MetaM

/-- Run `x` with the local variables `locals` (a new scope: terms are memoized in a fresh cache). -/
def withScopeCache (locals : Std.HashMap String Expr) (x : InterpM α) : InterpM α := do
  let ref ← IO.mkRef {}
  withReader (fun c => { c with locals, scopeCache := some ref }) x

/-! ## Casts -/

def intType : Expr := mkConst ``Int
def natType : Expr := mkConst ``Nat

def isNatType (t : Expr) : Bool := t.isConstOf ``Nat
def isIntType (t : Expr) : Bool := t.isConstOf ``Int
def isBoolType (t : Expr) : Bool := t.isConstOf ``Bool

/-- `(↑e : Int)`, in the canonical form expected by tactics (`Nat.cast`). Nat literals are converted
    to `Int` literals. -/
def mkIntOfNat (e : Expr) : Expr :=
  match e.rawNatLit?, e.nat? with
  | some n, _ | _, some n => mkApp3 (mkConst ``OfNat.ofNat [levelZero]) (mkConst ``Int) (mkRawNatLit n)
                                (mkApp (mkConst ``instOfNat) (mkRawNatLit n))
  | _, _ => mkApp3 (mkConst ``Nat.cast [levelZero]) (mkConst ``Int) (mkConst ``instNatCastInt) e

def mkIntToNat (e : Expr) : Expr :=
  -- `Int.toNat (↑n) = n`
  match e.getAppFnArgs with
  | (``Nat.cast, #[_, _, n]) => n
  | (``Int.ofNat, #[n]) => n
  | (``OfNat.ofNat, #[_, n, _]) => mkApp3 (mkConst ``OfNat.ofNat [levelZero]) (mkConst ``Nat) n (mkApp (mkConst ``instOfNatNat) n)
  | _ => mkApp (mkConst ``Int.toNat) e

/-- `decide p` with the classical instance. -/
def mkClassicalDecide (p : Expr) : Expr :=
  mkApp2 (mkConst ``Decidable.decide) p (mkApp (mkConst ``Classical.propDecidable) p)

def mkBoolTrue (b : Expr) : Expr :=
  -- `decide p = true` is `p`
  match b.getAppFnArgs with
  | (``Decidable.decide, #[p, _]) => p
  | _ => mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool) b (mkConst ``Bool.true)

/-- Coerce `e : actual` to `expected` (Nat ↔ Int, Bool ↔ Prop). -/
partial def coerce (e actual expected : Expr) : MetaM Expr := do
  if ← isDefEq actual expected then return e
  let actual ← whnfR actual
  let expected' ← whnfR expected
  if isNatType actual && isIntType expected' then return mkIntOfNat e
  if isIntType actual && isNatType expected' then return mkIntToNat e
  if actual.isProp && isBoolType expected' then return mkClassicalDecide e
  if isBoolType actual && expected'.isProp then return mkBoolTrue e
  -- proof arguments (e.g., proof fields of constructors, encoded as `true` by Blaster): a proof by decision
  -- of the expected proposition
  if (actual.isProp || isBoolType actual) && (← isProp expected) then
    try
      let d ← mkDecide expected
      if (← withAtLeastTransparency .default (whnf d)).isConstOf ``Bool.true then
        return ← mkDecideProof expected
    catch _ => pure ()
  -- constructor applications of another instance of the datatype (e.g., `some (x + y) : Option Int` where
  -- `Option Nat` is expected): the arguments are coerced
  if let .const c _ := e.getAppFn then
    if let some (.ctorInfo info) := (← getEnv).find? c then
      if actual.getAppFn.isConstOf info.induct && expected'.getAppFn.isConstOf info.induct then
        let args := e.getAppArgs
        if args.size == info.numParams + info.numFields then
          let k ← mkConstWithFreshMVarLevels c
          let (ms, _, rt) ← forallMetaTelescopeReducing (← inferType k)
          if ms.size == args.size && (← isDefEq rt expected) then
            for i in [info.numParams:args.size] do
              let fty ← instantiateMVars (← inferType ms[i]!)
              ms[i]!.mvarId!.assign (← coerce args[i]! (← inferType args[i]!) fty)
            let r ← instantiateMVars (mkAppN k ms)
            if !r.hasExprMVar then return r
  -- functions (e.g., lambda terms with `Nat` parameters and an `Int` body where `Nat → Nat` is expected): the
  -- arguments are coerced back and the results coerced, pointwise
  if let (.forallE _ a b _, .forallE n a' b' bi) := (actual, expected') then
    if !b.hasLooseBVars && !b'.hasLooseBVars then
      return ← withLocalDecl n bi a' fun y => do
        let x ← coerce y a' a
        mkLambdaFVars #[y] (← coerce (mkApp e x).headBeta b b')
  throwError "smt proof: can't coerce {e} : {actual} to {expected}"

/-- Normalize the type of an interpreted term for the SMT world: `Nat` terms are cast to `Int`,
    `Bool` terms are converted to propositions. -/
def toSmtWorld (e : Expr) : MetaM Expr := do
  let t ← whnfR (← inferType e)
  if isNatType t then return mkIntOfNat e
  if isBoolType t then return mkBoolTrue e
  return e

/-! ## Types -/

/-- Type aliases, per constant (see `isTypeAlias`). -/
initialize typeAliasCache : IO.Ref (Std.HashMap Name Bool) ← IO.mkRef {}

/-- Whether `c` is a type alias: a non-recursive definition of a type or of a type constructor (e.g.,
    `def ScriptHash : Type := ByteString`), which Blaster's translation unfolds. The types of the interpretation
    itself (e.g., `Poly.Univ`) are not aliases. -/
def isTypeAlias (c : Name) : MetaM Bool := do
  if let some b := (← typeAliasCache.get).get? c then return b
  let env ← getEnv
  let b := match env.find? c with
    | some (.defnInfo info) =>
        !(`Blaster).isPrefixOf c && info.type.getForallBody.isSort && !isInstanceCore env c &&
        !(info.value.find? (·.isConstOf c)).isSome
    | _ => false
  typeAliasCache.modify (·.insert c b)
  return b

/-- `t` with its type aliases unfolded (see `isTypeAlias`): the canonical form of the types of the interpretation.
    The SMT sorts are interpreted as the unfolded types, while the types of Lean declarations (e.g., of the fields of
    constructors) may refer to the aliases (e.g., `Option ScriptHash` and `Option ByteString` in the testers of a
    field and of the branches of a conditional), which unification identifies but the syntactic comparisons of the
    replay (e.g., `congrDescent`) do not. -/
def unfoldTypeAliases (t : Expr) : MetaM Expr := do
  if !(← t.getUsedConstants.anyM isTypeAlias) then return t
  Meta.transform t (pre := fun e => do
    let .const c _ := e.getAppFn | return .continue
    if !(← isTypeAlias c) then return .continue
    let some e' ← unfoldDefinition? e | return .continue
    return .visit e'.headBeta)

/-- User name of the metavariables standing for the default values of selectors (see `mkSelector`). -/
def defaultMVarName : Name := `_blaster_selector_default

/-- Apply `f` to `args`, instantiating implicit arguments by unification and coercing explicit
    arguments when necessary. Arguments whose type is `Int` or `Prop` (i.e., flexible w.r.t. coercions)
    are unified last. -/
def mkAppCoerce (f : Expr) (args : Array Expr) (allowMVars := false) (allowTypeMVars := false) : MetaM Expr := do
  let fty ← inferType f
  let (mvars, bis, _) ← forallMetaTelescopeReducing fty
  let explicit := (List.range mvars.size).toArray.filter fun i => bis[i]!.isExplicit
  if explicit.size < args.size then throwError "smt proof: too many arguments for {f}"
  let types ← args.mapM inferType
  -- first pass: rigid arguments
  let mut done := Array.replicate args.size false
  for j in [:args.size] do
    let t ← whnfR types[j]!
    if isIntType t || t.isProp then continue
    let m := mvars[explicit[j]!]!
    if ← isDefEq (← inferType m) types[j]! then
      m.mvarId!.assign args[j]!
      done := done.set! j true
  -- second pass: flexible arguments, with coercions
  for j in [:args.size] do
    if done[j]! then continue
    let m := mvars[explicit[j]!]!
    let expected ← instantiateMVars (← inferType m)
    if expected.isMVar then
      -- no constraint on the type: keep the SMT type, except for formulas (e.g., `(Option.some true)`),
      -- interpreted as Lean `Bool` terms
      if types[j]!.isProp then
        if ← isDefEq expected (mkConst ``Bool) then
          m.mvarId!.assign (mkClassicalDecide args[j]!)
          continue
      if !(← isDefEq expected types[j]!) then throwError "smt proof: ill-typed argument for {f}"
      m.mvarId!.assign args[j]!
    else
      m.mvarId!.assign (← coerce args[j]! types[j]! expected)
  -- remaining implicit arguments: instances (of the used prefix)
  let used := if args.size = explicit.size then mvars.size else explicit[args.size]!
  for i in [:used] do
    let m := mvars[i]!
    if (← instantiateMVars m).isMVar then
      if bis[i]!.isInstImplicit then
        let inst ← synthInstance (← instantiateMVars (← inferType m))
        m.mvarId!.assign inst
  -- NOTE: the type arguments with their type aliases unfolded (see `unfoldTypeAliases`)
  let r ← instantiateMVars (mkAppN f (← (mvars.extract 0 used).mapIdxM fun i m => do
    let v ← instantiateMVars m
    if bis[i]!.isExplicit || bis[i]!.isInstImplicit || v.hasMVar then return v
    unfoldTypeAliases v))
  -- NOTE: the remaining implicit arguments (e.g., the type parameter `α` of `Sum.inr (b : β) : α ⊕ β`) may be
  -- assigned by unification with the context
  if r.hasMVar && !allowMVars then
    -- NOTE: the default values of selectors (see `mkSelector`), and type parameters when `allowTypeMVars`, may be
    -- chosen later
    let pending (m : MVarId) : MetaM Bool := do
      if (← m.getDecl).userName == defaultMVarName then return true
      return allowTypeMVars && (← instantiateMVars (← m.getType)).isSort
    -- NOTE: the universe levels of the type parameters may be chosen later too (see `defaultTypes`)
    if (r.hasLevelMVar && !allowTypeMVars) || (← (← getMVars r).anyM fun m => return !(← pending m)) then
      throwError "smt proof: can't infer implicit arguments of {f}"
  return r

/-! ## Sorts -/

partial def expandSort (tbl : SymTable) (s : SExpr) : SExpr :=
  match s with
  | .atom a => match tbl.aliases.get? a with
    | some s' => expandSort tbl s'
    | none => s
  | .list xs => .list (xs.map (expandSort tbl))
  | s => s

/-- Lean type of an SMT sort. -/
partial def sortToType (s : SExpr) : InterpM Expr := do
  let tbl := (← read).table
  match s with
  | .atom "Int" => return intType
  | .atom "Bool" => return mkSort levelZero
  | .atom "String" => return mkConst ``String
  | .atom "Real" => throwError "smt proof: Real sort not supported"
  | _ =>
    if let some t := tbl.expandedSorts.get? (toString (expandSort tbl s)) then return t
    match s with
    | .atom a =>
        if let some s' := tbl.aliases.get? a then return ← sortToType s'
        match tbl.sorts.get? a with
        | some (.const n []) =>
            let info ← getConstInfo n
            return mkConst n (info.levelParams.map fun _ => levelZero)
        | some t => return t
        | none => throwError "smt proof: unknown sort {a}"
    | .list xs =>
        let some (SExpr.atom a) := xs[0]? | throwError "smt proof: unsupported sort {s}"
        -- NOTE: in the sort arguments of the query, `Nat` stands for Lean `Nat` (e.g., `List Nat`) and
        -- `Bool` for Lean `Bool` (e.g., `List Bool`)
        let args ← (xs.extract 1 xs.size).mapM fun s =>
          if s == .atom "Nat" then pure natType
          else if s == .atom "Bool" then pure (mkConst ``Bool)
          else sortToType s
        -- arrow sorts of Blaster's encoding of function values
        if a.startsWith "@@ArrowT" then
          let some r := args.back? | throwError "smt proof: ill-formed arrow sort {s}"
          return args.pop.foldr (fun d acc => mkForall `x .default d acc) r
        let some t := tbl.sorts.get? a | throwError "smt proof: unknown sort {a}"
        -- NOTE: universe levels are inferred from the arguments
        if let .const n _ := t then return ← mkAppM n args
        return mkAppN t args
    | _ => throwError "smt proof: unsupported sort {s}"

/-! ## Terms -/

/-- Interpretation of SMT-LIB's `str.from_code`: the string of the character of code `n` when `n` is a code of the SMT
    string alphabet (`[0, 196607]`), the empty string otherwise.
    NOTE: Lean characters exclude the surrogate code points (mapped to `'\0'` by `Char.ofNat`): the steps relying on
    the injectivity of `str.from_code` on them do not replay. -/
def strFromCode (n : Int) : String := if 0 ≤ n ∧ n ≤ 196607 then String.singleton (Char.ofNat n.toNat) else ""

/-- Decode the escape sequences `\u{h...}` and `\uhhhh` of SMT-LIB string literals. -/
partial def decodeSmtString (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < cs.size do
    if cs[i]! == '\\' && i + 1 < cs.size && cs[i+1]! == 'u' then
      let hexVal (ds : List Char) : Option Nat :=
        if ds.isEmpty then none else ds.foldlM (fun acc d =>
          if d.isDigit then some (16 * acc + (d.toNat - '0'.toNat))
          else if 'a' ≤ d && d ≤ 'f' then some (16 * acc + (d.toNat - 'a'.toNat + 10))
          else if 'A' ≤ d && d ≤ 'F' then some (16 * acc + (d.toNat - 'A'.toNat + 10))
          else none) 0
      if i + 2 < cs.size && cs[i+2]! == '{' then
        let mut j := i + 3
        while j < cs.size && cs[j]! != '}' do j := j + 1
        if let some v := hexVal (cs.extract (i+3) j).toList then
          out := out.push (Char.ofNat v); i := j + 1; continue
      else if i + 5 < cs.size then
        if let some v := hexVal (cs.extract (i+2) (i+6)).toList then
          out := out.push (Char.ofNat v); i := i + 6; continue
    out := out.push cs[i]!
    i := i + 1
  return out

def mkIntLit (n : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [levelZero]) (mkConst ``Int) (mkRawNatLit n) (mkApp (mkConst ``instOfNat) (mkRawNatLit n))

def mkIntAdd (a b : Expr) : Expr := mkApp2 (mkApp4 (mkConst ``HAdd.hAdd [0, 0, 0]) intType intType intType
  (mkApp2 (mkConst ``instHAdd [0]) intType (mkConst ``Int.instAdd))) a b
def mkIntSub (a b : Expr) : Expr := mkApp2 (mkApp4 (mkConst ``HSub.hSub [0, 0, 0]) intType intType intType
  (mkApp2 (mkConst ``instHSub [0]) intType (mkConst ``Int.instSub))) a b
def mkIntMul (a b : Expr) : Expr := mkApp2 (mkApp4 (mkConst ``HMul.hMul [0, 0, 0]) intType intType intType
  (mkApp2 (mkConst ``instHMul [0]) intType (mkConst ``Int.instMul))) a b
def mkIntDiv (a b : Expr) : Expr := mkApp2 (mkApp4 (mkConst ``HDiv.hDiv [0, 0, 0]) intType intType intType
  (mkApp2 (mkConst ``instHDiv [0]) intType (mkConst ``Int.instDiv))) a b
def mkIntMod (a b : Expr) : Expr := mkApp2 (mkApp4 (mkConst ``HMod.hMod [0, 0, 0]) intType intType intType
  (mkApp2 (mkConst ``instHMod [0]) intType (mkConst ``Int.instMod))) a b
def mkIntNeg (a : Expr) : Expr := mkApp (mkApp2 (mkConst ``Neg.neg [0]) intType (mkConst ``Int.instNegInt)) a
def mkIntLe (a b : Expr) : Expr := mkApp4 (mkConst ``LE.le [0]) intType (mkConst ``Int.instLEInt) a b
def mkIntLt (a b : Expr) : Expr := mkApp4 (mkConst ``LT.lt [0]) intType (mkConst ``Int.instLTInt) a b

def mkStrLt (a b : Expr) : Expr := mkApp4 (mkConst ``LT.lt [0]) (mkConst ``String) (mkConst ``String.instLT) a b

/-- `if c then a else b` with the classical instance. -/
def mkClassicalIte (c a b : Expr) : MetaM Expr := do
  let t ← inferType a
  let u ← getLevel t
  return mkApp5 (mkConst ``ite [u]) t c (mkApp (mkConst ``Classical.propDecidable) c) a b

/-- Left-associated application of a binary operation. -/
def foldBin (op : Expr → Expr → Expr) (args : Array Expr) : MetaM Expr := do
  let some a := args[0]? | throwError "smt proof: operation without arguments"
  return (args.extract 1 args.size).foldl op a

def foldBinRight (op : Expr → Expr → Expr) (args : Array Expr) : MetaM Expr := do
  let some a := args.back? | throwError "smt proof: operation without arguments"
  return args.pop.foldr op a

/-- Chain of relations `r a₀ a₁ ∧ r a₁ a₂ ∧ ...`. -/
def chain (r : Expr → Expr → MetaM Expr) (args : Array Expr) : MetaM Expr := do
  if args.size < 2 then throwError "smt proof: relation with less than two arguments"
  let mut cs := #[]
  for i in [:args.size - 1] do cs := cs.push (← r args[i]! args[i+1]!)
  foldBinRight mkAnd cs

/-- Equality of interpreted terms (with coercions to a common type). -/
def mkEqSmt (a b : Expr) : MetaM Expr := do
  let ta ← inferType a
  let tb ← inferType b
  if ← isDefEq ta tb then return ← mkEq a b
  let a ← toSmtWorld a
  let b ← toSmtWorld b
  let ta ← inferType a
  let tb ← inferType b
  if ← isDefEq ta tb then return ← mkEq a b
  -- e.g., constructor applications of different instances of a datatype
  try return ← mkEq (← coerce a ta tb) b
  catch _ => mkEq a (← coerce b tb ta)

/-- The type of `x` (in weak head normal form), an application of the inductive type `induct`: when it is not
    determined yet (a metavariable, e.g., the type of a selector of an undetermined instance of a datatype), it is
    unified with an application of `induct` to fresh metavariables (determined by the context, or defaulted, see
    `defaultTypes`). -/
def inductTypeOf (x : Expr) (induct : Name) : MetaM Expr := do
  let xt ← whnfD (← instantiateMVars (← inferType x))
  if !xt.getAppFn.isMVar then return xt
  let (ps, _, _) ← forallMetaTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels induct))
  let c ← mkConstWithFreshMVarLevels induct
  if ← isDefEq xt (mkAppN c ps) then return ← whnfD (← instantiateMVars xt)
  return xt

/-- Selector of field `idx` of constructor `ctor` applied to `x`, defined by case analysis (with
    `default` for the other constructors). -/
partial def mkSelector (ctor : Name) (idx : Nat) (x : Expr) (deferDefault := false) : MetaM Expr := do
  let some (.ctorInfo cinfo) := (← getEnv).find? ctor | throwError "smt proof: unknown constructor {ctor}"
  let xt ← inductTypeOf x cinfo.induct
  if !xt.getAppFn.isConstOf cinfo.induct then throwError "smt proof: selector {ctor} applied to {xt}"
  let lvls := xt.getAppFn.constLevels!
  let some (.inductInfo iinfo) := (← getEnv).find? cinfo.induct | throwError "smt proof: unknown inductive {cinfo.induct}"
  let params ← (xt.getAppArgs.extract 0 iinfo.numParams).mapM unfoldTypeAliases
  let xt := mkAppN xt.getAppFn (params ++ xt.getAppArgs.extract iinfo.numParams xt.getAppNumArgs)
  -- NOTE: an inductive proposition with data fields (e.g., `SomeBig.intro (n : Nat) (h : n > 5)`) has no selectors:
  -- neither a projection nor a case analysis eliminates a proof into data (the propositions of its proof fields
  -- depend on the data fields)
  if ← isProp xt then
    let hasData ← forallTelescopeReducing (← instantiateForall (cinfo.instantiateTypeLevelParams lvls) params) fun fs _ =>
      fs.anyM fun f => return !(← isProof f)
    if hasData then throwError "smt proof: selector of the inductive proposition {cinfo.induct} with data fields"
  -- structure: projection (a proof field is interpreted as its proposition)
  if iinfo.ctors.length == 1 && iinfo.numIndices == 0 && !iinfo.isRec then
    let p := mkProj cinfo.induct idx x
    if ← isProof p then return ← inferType p
    return p
  let ctorType (c : ConstantInfo) := c.instantiateTypeLevelParams lvls
  let fieldTy ← forallTelescopeReducing (← instantiateForall (ctorType (.ctorInfo cinfo)) params) fun fs _ => do
    let t ← inferType fs[idx]!
    if t.hasAnyFVar (fs.contains <| .fvar ·) then throwError "smt proof: dependent field selector not supported"
    unfoldTypeAliases t
  -- default value for the other constructors: `x` itself when the field has the type of `x` (e.g., the
  -- argument of a recursive constructor), an inhabitant of the field type otherwise
  -- NOTE: when the field type is not known yet (e.g., `List.nil` of an unknown instance), the inhabitant can be
  -- chosen after the interpretation of the whole term (`deferDefault`, see `fillDefaults`)
  let dflt ← if ← isDefEq fieldTy xt then pure x
    else if deferDefault && (← instantiateMVars fieldTy).hasExprMVar then mkFreshExprMVar fieldTy (userName := defaultMVarName)
    else mkDefault fieldTy (locals := deferDefault)
  let motive := mkLambda `x .default xt fieldTy
  let mut minors := #[]
  for c in iinfo.ctors do
    let some ci := (← getEnv).find? c | unreachable!
    let minor ← forallTelescopeReducing (← instantiateForall (ctorType ci) params) fun fs _ => do
      if c == ctor then mkLambdaFVars fs fs[idx]! else mkLambdaFVars fs dflt
    minors := minors.push minor
  let u ← getLevel fieldTy
  let casesOn ← getConstInfo (cinfo.induct ++ `casesOn)
  if casesOn.levelParams.length != lvls.length + 1 then throwError "smt proof: no large elimination for {cinfo.induct}"
  return mkAppN (mkConst (cinfo.induct ++ `casesOn) (u :: lvls)) (params ++ #[motive, x] ++ minors)
where
  mkDefault (t : Expr) (locals := false) : MetaM Expr := do
    if let some v ← inhabitant? t 8 locals then return v
    throwError "smt proof: no inhabitant found for {t}"
  /-- An inhabitant of `t`: from an instance, or a constructor application with inhabited fields (or a variable of
      the context when `locals`). -/
  inhabitant? (t : Expr) (depth : Nat) (locals := false) : MetaM (Option Expr) := do
    let u ← getLevel t
    try
      let inst ← synthInstance (mkApp (mkConst ``Inhabited [u]) t)
      return some (mkApp2 (mkConst ``Inhabited.default [u]) t inst)
    catch _ => pure ()
    try
      let inst ← synthInstance (mkApp (mkConst ``Nonempty [u]) t)
      return some (mkApp2 (mkConst ``Classical.ofNonempty [u]) t inst)
    catch _ => pure ()
    -- in the interpretation: a variable of the context of type `α` (a sort variable of the goal, e.g., `x : α`)
    -- NOTE: the first one, i.e., a variable of the goal when there is one (the variables of the replay come later)
    if locals && t.isFVar then
      if let some d := (← getLCtx).findDecl? fun d =>
          if !d.isImplementationDetail && d.type == t then some d else none then
        return some d.toExpr
    if depth == 0 then return none
    let t ← whnfD t
    let .const n lvls := t.getAppFn | return none
    let some (.inductInfo info) := (← getEnv).find? n | return none
    let params := t.getAppArgs.extract 0 info.numParams
    for c in info.ctors do
      let ci ← getConstInfo c
      let r ← forallTelescopeReducing (← instantiateForall (ci.instantiateTypeLevelParams lvls) params) fun fs _ => do
        let mut vals := #[]
        for f in fs do
          let ft ← inferType f
          -- non-dependent fields only
          if ft.hasAnyFVar (fs.contains <| .fvar ·) then return none
          match ← inhabitant? ft (depth - 1) locals with
          | some v => vals := vals.push v
          | none => return none
        return some (mkAppN (mkAppN (mkConst c lvls) params) vals)
      if r.isSome then return r
    return none

/-- Assign the metavariables of `e` standing for default values of selectors (see `mkSelector`) whose type is
    known, with inhabitants of their types. -/
def fillDefaults (e : Expr) : MetaM Expr := do
  if !e.hasExprMVar then return e
  for m in (← getMVars e) do
    if (← m.isAssigned) || (← m.getDecl).userName != defaultMVarName then continue
    let t ← instantiateMVars (← m.getType)
    if t.hasExprMVar || (← isProp t) then continue
    if let some v ← mkSelector.inhabitant? t 8 (locals := true) then m.assign v
  instantiateMVars e

/-- Replace the remaining type metavariables of `e` with `dflt`: the type parameters that nothing determines (e.g.,
    of `Option.none` under a tester, whose instance Z3 doesn't print), then the default values of selectors of
    these types. The metavariables are substituted, not assigned: they may be shared with the interpretations of
    the same subterms in other steps, where their context determines them. -/
def defaultTypes (e : Expr) (dflt : Expr := mkConst ``Unit) : MetaM Expr := do
  if !e.hasExprMVar then return e
  let dfltTy ← inferType dflt
  let mut subst : Std.HashMap MVarId Expr := {}
  for m in (← getMVars e) do
    if ← m.isAssigned then continue
    let t ← instantiateMVars (← m.getType)
    -- NOTE: the universe of the parameter may be a metavariable (e.g., `Option.{?u} ?α`)
    if t.isSort && (← isDefEq t dfltTy) then subst := subst.insert m dflt
  if subst.isEmpty then return e
  let apply (subst : Std.HashMap MVarId Expr) (x : Expr) : Expr :=
    x.replace fun y => if let .mvar m := y then subst.get? m else none
  -- the default values of selectors whose type is now known
  for m in (← getMVars e) do
    if (← m.isAssigned) || subst.contains m || (← m.getDecl).userName != defaultMVarName then continue
    let t := apply subst (← instantiateMVars (← m.getType))
    if t.hasExprMVar || (← isProp t) then continue
    if let some v ← mkSelector.inhabitant? t 8 then subst := subst.insert m v
  -- NOTE: the universe levels of the substituted parameters are assigned (e.g., `?u` in `Option.{?u} ?α`)
  instantiateMVars (apply subst e)

/-- Assign the remaining type metavariables of `e` with `dflt` (see `defaultTypes`), e.g., the type parameters of the
    constructors of an undetermined instance in the instantiations of quantifiers, which unification does not
    determine when the constructor applications are reduced (e.g., `Either.Right.0 (Either.Right x)`). -/
def assignDefaultTypes (e : Expr) (dflt : Expr) : MetaM Expr := do
  if !e.hasExprMVar then return e
  for m in (← getMVars e) do
    if ← m.isAssigned then continue
    if (← instantiateMVars (← m.getType)).isSort then discard <| isDefEq (mkMVar m) dflt
  instantiateMVars e

/-- Tester for constructor `ctor` applied to `x`: a proposition defined by case analysis. -/
def mkTester (ctor : Name) (x : Expr) : MetaM Expr := do
  let some (.ctorInfo cinfo) := (← getEnv).find? ctor | throwError "smt proof: unknown constructor {ctor}"
  let xt ← inductTypeOf x cinfo.induct
  if !xt.getAppFn.isConstOf cinfo.induct then throwError "smt proof: tester {ctor} applied to {xt}"
  let lvls := xt.getAppFn.constLevels!
  let some (.inductInfo iinfo) := (← getEnv).find? cinfo.induct | throwError "smt proof: unknown inductive {cinfo.induct}"
  let params ← (xt.getAppArgs.extract 0 iinfo.numParams).mapM unfoldTypeAliases
  let xt := mkAppN xt.getAppFn (params ++ xt.getAppArgs.extract iinfo.numParams xt.getAppNumArgs)
  let motive := mkLambda `x .default xt (mkSort levelZero)
  let mut minors := #[]
  for c in iinfo.ctors do
    let some ci := (← getEnv).find? c | unreachable!
    let minor ← forallTelescopeReducing (← instantiateForall (ci.instantiateTypeLevelParams lvls) params) fun fs _ =>
      mkLambdaFVars fs (if c == ctor then mkConst ``True else mkConst ``False)
    minors := minors.push minor
  let casesOn ← getConstInfo (cinfo.induct ++ `casesOn)
  if casesOn.levelParams.length != lvls.length + 1 then throwError "smt proof: no large elimination for {cinfo.induct}"
  return mkAppN (mkConst (cinfo.induct ++ `casesOn) (levelOne :: lvls)) (params ++ #[motive, x] ++ minors)

/-- Interpret `e` as a proposition (a Lean `Bool` term `b` is interpreted as `b = true`). -/
def asProp (e : Expr) : MetaM Expr := do
  let t ← whnfR (← inferType e)
  if isBoolType t then return mkBoolTrue e
  return e

/-- The type of the (possibly partial) sort hint `h` (see `SortInfer`): the unknown parts are metavariables. -/
partial def hintType (h : SortInfer.Hint) : InterpM Expr := do
  if let some s := h.toSExpr? then
    if let some t ← (try some <$> sortToType s catch _ => pure none) then return t
  match h with
  | .unknown => mkFreshTypeMVar
  | .con n args =>
      -- NOTE: an atomic sort not interpreted by `sortToType` (see above) is unknown
      if args.isEmpty then return ← mkFreshTypeMVar
      let some t := (← read).table.sorts.get? n | mkFreshTypeMVar
      -- NOTE: as in `sortToType`, `Bool` stands for Lean `Bool` in the sort arguments
      let arg (a : SortInfer.Hint) : InterpM (Option Expr) :=
        if a == .unknown then pure none
        else if a == .con "Bool" #[] then pure (some (mkConst ``Bool))
        else some <$> hintType a
      let .const c _ := t | return mkAppN t (← args.mapM fun a => do (← arg a).getDM mkFreshTypeMVar)
      -- NOTE: the type constructor instantiated by unification (not `mkAppM`, whose new metavariable context can't
      -- assign the universe levels of the metavariables of the unknown parts)
      let f ← mkConstWithFreshMVarLevels c
      let (ms, _, _) ← forallMetaTelescopeReducing (← inferType f)
      if ms.size != args.size then throwError "smt proof: ill-formed sort hint for {c}"
      for (m, a) in ms.zip args do
        if let some ty ← arg a then
          unless ← isDefEq m ty do throwError "smt proof: ill-typed sort hint for {c}"
      instantiateMVars (mkAppN f ms)

/-- The interpretation `x` of the term `t`, recording the hint of `t` (the instance of a constructor application
    inferred on the whole proof, see `SortInfer`) when its type is not determined yet: the hints are applied to the
    types that the whole term leaves undetermined (see `applySortHints`), i.e., they don't override the instances that
    the term determines (e.g., `List Nat` vs. `List Int`, of the same sort `(@List Int)`). -/
def withSortHint (t : STerm) (x : InterpM Expr) : InterpM Expr := do
  let e ← x
  let some ref := (← read).pendingHints | return e
  let some h := (← read).sortHints.get? (termAddr t) | return e
  if e.hasExprMVar then ref.modify (·.push (← inferType e, h))
  return e

/-- Unify the types of the pending hints (see `withSortHint`) that are still undetermined with their hints (e.g.,
    `List.nil` interpreted as `@List.nil (Prod Data ?β)` in all the steps, where `?β` is then defaulted like the
    undetermined instances of the step). -/
def applySortHints (pending : Array (Expr × SortInfer.Hint)) : InterpM Unit := do
  for (ty, h) in pending do
    let ty ← instantiateMVars ty
    if !ty.hasExprMVar then continue
    let some hty ← (try some <$> hintType h catch _ => pure none) | continue
    discard <| isDefEq ty hty

/-- Run `x`, then apply the hints of the terms it interpreted (see `withSortHint`). -/
def withSortHints (x : InterpM α) : InterpM α := do
  let ref ← IO.mkRef #[]
  let r ← withReader (fun c => { c with pendingHints := some ref }) x
  applySortHints (← ref.get)
  return r

mutual
/-- Interpret the SMT term `t` as a Lean term. -/
partial def interp (t : STerm) : InterpM Expr := do
  let ctx ← read
  -- NOTE: terms are memoized when no local variable is in scope (closed terms)
  -- NOTE: the memos keep the terms alive (see `TermMemo`), such that their addresses aren't reused by other terms
  if let some ref := ctx.cache then
    if ctx.locals.isEmpty then
      let addr := termAddr t
      if let some (_, e) := (← ref.get).get? addr then return e
      let e ← interpCore t
      if !e.hasMVar then ref.modify (·.insert addr (t, e))
      return e
  -- NOTE: terms below binders are memoized for their scope (e.g., the shared subterms of macro bodies)
  if let some ref := ctx.scopeCache then
    if !ctx.locals.isEmpty then
      let addr := termAddr t
      if let some (_, e) := (← ref.get).get? addr then return e
      let e ← interpCore t
      if !e.hasMVar then ref.modify (·.insert addr (t, e))
      return e
  interpCore t

/-- Interpret the SMT formula `t` as a proposition. -/
partial def interpProp (t : STerm) : InterpM Expr := do
  asProp (← interp t)

partial def interpCore (t : STerm) : InterpM Expr := do
  match t with
  | .num n => return mkIntLit n
  | .lit s => throwError "smt proof: unsupported literal {s}"
  | .metadata _ => throwError "smt proof: proof metadata is not a logical term"
  | .str s => return mkStrLit (decodeSmtString s)
  | .annot t _ => interp t
  | .sym s => withSortHint t (interpApp s #[])
  | .app f args => withSortHint t (interpApp f args)
  | .qual f sort args =>
      let ty ← sortToType sort
      -- constructors: the parameters of the datatype are given by the sort (e.g., `(as Option.some (Option Nat))`
      -- applied to an `Int` term)
      if let some (.ctor n) := (← read).table.syms.get? f then
        if !args.isEmpty then
          let c ← mkConstWithFreshMVarLevels n
          let (ms, bis, rt) ← forallMetaTelescopeReducing (← inferType c)
          let explicit := (List.range ms.size).toArray.filter fun i => bis[i]!.isExplicit
          if explicit.size == args.size && (← isDefEq rt ty) then
            for (i, a) in explicit.zip args do
              let v ← interp a
              let expected ← instantiateMVars (← inferType ms[i]!)
              ms[i]!.mvarId!.assign (← coerce v (← inferType v) expected)
            let r ← instantiateMVars (mkAppN c ms)
            if !r.hasExprMVar then return r
      let e ← interpApp f args
      let ety ← inferType e
      if ← isDefEq ety ty then return e
      coerce e ety ty
  | .iapp f idx args =>
      -- testers: `((_ is C) x)` and `((_ is-C C is-C) x)` (Z3)
      -- character literals `(_ Char n)`
      if f == "case-def" then return ← interpCaseDef idx args
      if f == "Char" && args.isEmpty then
        let some (STerm.num n) := idx[0]? | throwError "smt proof: ill-formed character {t}"
        return mkApp (mkConst ``Char.ofNat) (mkRawNatLit n)
      if f == "is" || f.startsWith "is-" then
        let ctorSym := if f == "is" then (match idx[0]? with | some (STerm.sym c) => c | _ => "") else f.drop 3
        let some x := args[0]? | throwError "smt proof: tester without argument"
        match (← read).table.syms.get? ctorSym with
        | some (.ctor c) => mkTester c (← interp x)
        | _ => throwError "smt proof: unknown constructor {ctorSym}"
      -- pseudo-Boolean constraints (Z3): `((_ pbge k c₁ ... cₙ) a₁ ... aₙ)` is `c₁ [a₁] + ... + cₙ [aₙ] ≥ k`
      -- where `[a]` is `if a then 1 else 0` (resp. `≤ k`, `= k` for `pble`, `pbeq`), and the cardinality
      -- constraints `((_ at-least k) a₁ ... aₙ)` (resp. `at-most`) have the coefficients `1`
      else if ["pbge", "pble", "pbeq", "at-least", "at-most"].contains f then
        let nums ← idx.mapM fun i => match i with
          | STerm.num n => pure n
          | _ => throwError "smt proof: ill-formed pseudo-Boolean constraint {t}"
        let some k := nums[0]? | throwError "smt proof: ill-formed pseudo-Boolean constraint {t}"
        let coeffs := if f.startsWith "at-" then Array.replicate args.size 1 else nums.extract 1 nums.size
        if coeffs.size != args.size || args.isEmpty then throwError "smt proof: ill-formed pseudo-Boolean constraint {t}"
        let mut terms := #[]
        for (c, a) in coeffs.zip args do
          let ind ← mkClassicalIte (← interpProp a) (mkIntLit 1) (mkIntLit 0)
          terms := terms.push (if c == 1 then ind else mkIntMul (mkIntLit c) ind)
        let sum ← foldBin mkIntAdd terms
        match f with
        | "pbge" | "at-least" => return mkIntLe (mkIntLit k) sum
        | "pble" | "at-most" => return mkIntLe sum (mkIntLit k)
        | _ => mkEq sum (mkIntLit k)
      else
        -- indexed applications of recursive functions (e.g., `((_ @Nat.pow 0) x y)` in Z3 proofs)
        interpApp f args
  | .quant k vars body => interpQuant k vars body

partial def interpQuant (k : QuantKind) (vars : Array (String × SExpr)) (body : STerm) : InterpM Expr := do
  -- NOTE: the parameters of sort `Nat` of lambda terms (e.g., Blaster's translation of Lean lambdas) are
  -- interpreted as Lean `Nat` variables, i.e., as `↑x` in the body
  let natParam (s : SExpr) : Bool := k == .lambda && s == .atom "Nat"
  let types ← vars.mapM fun (_, s) => if natParam s then pure natType else sortToType s
  let rec go (i : Nat) (fvars : Array Expr) : InterpM Expr := do
    if h : i < vars.size then
      withLocalDeclD (Name.mkSimple vars[i].1) types[i]! fun x =>
        let v := if natParam vars[i].2 then mkIntOfNat x else x
        withReader (fun ctx => { ctx with locals := ctx.locals.insert vars[i].1 v }) (go (i + 1) (fvars.push x))
    else
      -- NOTE: the hints of the body are applied before its abstraction (the metavariables of the types it leaves
      -- undetermined would then depend on the bound variables)
      let b ← withScopeCache (← read).locals do
        if (← read).pendingHints.isSome then withSortHints (interp body) else interp body
      match k with
      | .forall => mkForallFVars fvars b
      | .lambda => mkLambdaFVars fvars b
      | .exists =>
          let mut r := b
          for x in fvars.reverse do
            r ← mkAppM ``Exists #[← mkLambdaFVars #[x] r]
          return r
  go 0 #[]

partial def interpApp (f : String) (args : Array STerm) : InterpM Expr := do
  let ctx ← read
  if let some x := ctx.locals.get? f then
    if args.isEmpty then return x
    return ← mkAppCoerce x (← args.mapM interp) (allowTypeMVars := ctx.deferTypes)
  match f, args.size with
  | "true", 0 => return mkConst ``True
  | "false", 0 => return mkConst ``False
  | "not", 1 => return mkNot (← interpProp args[0]!)
  | "and", _ => if args.isEmpty then return mkConst ``True else foldBinRight mkAnd (← args.mapM interpProp)
  | "or", _ => if args.isEmpty then return mkConst ``False else foldBinRight mkOr (← args.mapM interpProp)
  | "=>", _ => foldBinRight (fun a b => mkForall `h .default a b) (← args.mapM interpProp)
  | "xor", 2 => return mkNot (← mkEq (← interpProp args[0]!) (← interpProp args[1]!))
  | "=", _ => chain mkEqSmt (← args.mapM interp)
  -- equisatisfiability (Z3): interpreted as an implication
  | "~", 2 => return mkForall `h .default (← interpProp args[0]!) (← interpProp args[1]!)
  | "distinct", _ =>
      let es ← args.mapM interp
      let mut cs := #[]
      for i in [:es.size] do
        for j in [i+1:es.size] do cs := cs.push (mkNot (← mkEqSmt es[i]! es[j]!))
      if cs.isEmpty then return mkConst ``True else foldBinRight mkAnd cs
  | "ite", 3 =>
      let (x, y) := (← interpInt? args[1]!, ← interpInt? args[2]!)
      let c ← interpProp args[0]!
      -- NOTE: the branches have the same type: the parameters of nullary constructors in a branch (e.g.,
      -- `Option.none` of an undetermined instance, see `deferTypes`) are given by the other branch, and the branches
      -- may be interpreted in different instances of a datatype (e.g., `Option Nat` and `Option Int`)
      let (tx, ty) := (← inferType x, ← inferType y)
      if ← isDefEq tx ty then return ← mkClassicalIte c x y
      if let some y' ← (try some <$> coerce y ty tx catch _ => pure none) then return ← mkClassicalIte c x y'
      mkClassicalIte c (← coerce x tx ty) y
  | "+", _ => foldBin mkIntAdd (← args.mapM interpInt)
  | "-", 1 => return mkIntNeg (← interpInt args[0]!)
  | "-", _ => foldBin mkIntSub (← args.mapM interpInt)
  | "*", _ => foldBin mkIntMul (← args.mapM interpInt)
  | "div", _ => foldBin mkIntDiv (← args.mapM interpInt)
  | "mod", 2 => return mkIntMod (← interpInt args[0]!) (← interpInt args[1]!)
  -- Z3's (unspecified) division and modulo by zero (e.g., `(= (div x y) (div0 x y))` in the lemmas on `y = 0`),
  -- interpreted as the division and modulo
  | "div0", 2 => return mkIntDiv (← interpInt args[0]!) (← interpInt args[1]!)
  | "mod0", 2 => return mkIntMod (← interpInt args[0]!) (← interpInt args[1]!)
  | "abs", 1 => return mkApp (mkConst ``Int.natAbs) (← interpInt args[0]!) |> mkIntOfNat
  | "<=", _ => chain (fun a b => pure (mkIntLe a b)) (← args.mapM interpInt)
  | "<", _ => chain (fun a b => pure (mkIntLt a b)) (← args.mapM interpInt)
  | ">=", _ => chain (fun a b => pure (mkIntLe b a)) (← args.mapM interpInt)
  | ">", _ => chain (fun a b => pure (mkIntLt b a)) (← args.mapM interpInt)
  | "str.++", _ | "seq.++", _ => foldBin (fun a b => mkApp2 (mkConst ``String.append) a b) (← args.mapM interp)
  | "str.len", 1 | "seq.len", 1 => return mkIntOfNat (mkApp (mkConst ``String.length) (← interp args[0]!))
  | "str.from_code", 1 => return mkApp (mkConst ``strFromCode) (← interp args[0]!)
  -- lexicographic order (`str.<=` as the negation of the converse, the order being total)
  | "str.<", 2 => return mkStrLt (← interp args[0]!) (← interp args[1]!)
  | "str.<=", 2 => return mkNot (mkStrLt (← interp args[1]!) (← interp args[0]!))
  -- strings as sequences of characters (Z3 proofs): `(seq.unit (_ Char n))`
  | "seq.unit", 1 => return mkApp (mkConst ``String.singleton) (← interp args[0]!)
  | "seq.empty", 0 => return mkStrLit ""
  | _, _ =>
    match ctx.table.syms.get? f with
    | some (.expr e) =>
        if args.isEmpty then return e
        -- NOTE: interpretations of auxiliary functions are lambdas (see `auxiliaryInterp`)
        return (← mkAppCoerce e (← args.mapM interp) (allowTypeMVars := ctx.deferTypes)).headBeta
    | some (.macro params body) =>
        if args.isEmpty && !params.isEmpty then
          -- the function itself (e.g., `(= @isNat (lambda ((x Int)) (<= 0 x)))` in cvc5 proofs)
          return ← interpQuant .lambda params body
        if params.size != args.size then throwError "smt proof: wrong number of arguments for {f}"
        let vals ← args.mapM interp
        -- NOTE: macro bodies only refer to their parameters
        let locals := (params.zip vals).foldl (fun m ((x, _), v) => m.insert x v) {}
        withScopeCache locals (interp body)
    | some .trueFun => return mkConst ``True
    | some (.lam e) =>
        if args.isEmpty then return e
        -- NOTE: the arguments may be constructor applications of undetermined instances (see `deferTypes`)
        return (← mkAppCoerce e (← args.mapM interp) (allowTypeMVars := ctx.deferTypes)).headBeta
    | some (.ctor n) =>
        let c ← mkConstWithFreshMVarLevels n
        if args.isEmpty then
          -- nullary constructor (e.g., `List.nil`): parameters are left as metavariables, to be
          -- assigned by unification with the context (e.g., the other side of an equality)
          let (ms, _, _) ← forallMetaTelescopeReducing (← inferType c)
          return mkAppN c ms
        mkAppCoerce c (← args.mapM interp) (allowMVars := true)
    | some (.selector c i) =>
        let some a := args[0]? | throwError "smt proof: selector without argument"
        let e ← mkSelector c i (← interp a) (deferDefault := true)
        toSmtWorld e
    | some (.tester c) =>
        let some a := args[0]? | throwError "smt proof: tester without argument"
        mkTester c (← interp a)
    | some (.skolem params x sort body neg) =>
        if params.size != args.size then throwError "smt proof: wrong number of arguments for {f}"
        let vals ← args.mapM interp
        let ty ← sortToType sort
        let u ← getLevel ty
        let inst ← synthInstance (mkApp (mkConst ``Nonempty [u]) ty)
        withLocalDeclD (Name.mkSimple x) ty fun fx => do
          let locals := (params.zip vals).foldl (fun m (y, v) => m.insert y v) ctx.locals |>.insert x fx
          let φ ← withScopeCache locals (interpProp body)
          let p ← mkLambdaFVars #[fx] (if neg then mkNot φ else φ)
          return mkApp3 (mkConst ``Classical.epsilon [u]) ty inst p
    | some .apply =>
        let some fn := args[0]? | throwError "smt proof: apply without argument"
        let r ← mkAppCoerce (← interp fn) (← (args.extract 1 args.size).mapM interp) (allowTypeMVars := ctx.deferTypes)
        toSmtWorld r
    | none => throwError "smt proof: unknown symbol {f}"

/-- Z3's case predicate `((_ case-def k f) args)` of a recursive function `f`: the conjunction of the guards
    of the case given by the proof for `args` (`True` when there is none). Case predicates are introduced
    by Z3 to unfold recursive functions by cases; any interpretation validating the steps of the proof can be
    chosen (see `RecFun.lean`). -/
partial def interpCaseDef (idx args : Array STerm) : InterpM Expr := do
  let some key := caseDefKey? idx | throwError "smt proof: ill-formed case predicate {idx.map toString}"
  let vals ← args.mapM interp
  let mut guards : Array Expr := #[]
  for (as, g) in (← read).table.caseGuards.getD key #[] do
    if as.size != vals.size then continue
    let vs ← as.mapM interp
    if ← (vs.zip vals).allM fun (a, b) => do return a == b || (← withReducible (isDefEq a b)) then
      let p ← interpProp g
      if !guards.contains p then guards := guards.push p
  if guards.isEmpty then return mkConst ``True
  foldBinRight mkAnd guards

/-- Interpret `t` as an `Int` term (casting `Nat` terms). -/
partial def interpInt (t : STerm) : InterpM Expr := do
  let e ← interp t
  let ty ← whnfR (← inferType e)
  if isNatType ty then return mkIntOfNat e
  return e

/-- Interpret `t`, casting `Nat`/`Bool` terms to the SMT world. -/
partial def interpInt? (t : STerm) : InterpM Expr := do
  toSmtWorld (← interp t)
end

end Blaster.Reconstruct.SmtProof
