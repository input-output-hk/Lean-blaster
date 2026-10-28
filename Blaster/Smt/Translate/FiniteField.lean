import Blaster.Smt.FiniteFieldPreflight
import Blaster.Smt.FiniteFieldSyntax
import Blaster.Smt.Env
import Blaster.FiniteField.Pow

open Lean Meta Blaster.Optimize Blaster.FiniteField

namespace Blaster.Smt

/-- Per-query caches. Admissions are never retained beyond their local scope. -/
private structure PolynomialState where
  admissions : Std.HashMap Expr NativeFieldAdmission := {}
  sorts : Std.HashMap Nat SortExpr := {}
  operations : Std.HashSet (Nat × String) := {}
  terms : Std.HashMap Expr SmtTerm := {}
  scope : Name := .anonymous
  inverses : Std.HashMap (Nat × Expr) SmtTerm := {}
  graphs : Array SmtTerm := #[]

private abbrev PolynomialM := StateT PolynomialState TranslateEnvT

private def unsupported (e : Expr) : PolynomialM α :=
  throwError "native finite-field polynomial fragment: unsupported expression {e}; use canonical Residue addition, multiplication, negation, subtraction, inverse, division, literal natural powers, equality and Boolean/ite expressions; variable/integer exponents, .val/.rep, order, representation casts, residual quantifiers/lambdas and mixed theories are not supported"

private def associate (symbol : SmtSymbol) (source type : Expr) (modulus : Option Nat)
    (modelVariable := false) (inverseGraph : Option InverseGraphWitness := none) :
    PolynomialM Unit := do
  let userName ← if source.isFVar then pure (← source.fvarId!.getDecl).userName
    else pure source.getAppFn.constName!
  let entry : SourceAssociation := {
    symbol, userName, source, type, modulus, polarity := .negated,
    localContext := ← getLCtx, localInstances := ← getLocalInstances, inverseGraph }
  modifyThe TranslateEnv fun env => { env with
    smtEnv.sourceAssociations := env.smtEnv.sourceAssociations.push entry
    smtEnv.topLevelVars := if modelVariable then
      env.smtEnv.topLevelVars.push [(symbol, userName)] else env.smtEnv.topLevelVars }

/-- Reuse only exact carrier admissions checked in this query's opened scope.
Aliases still share their normalized sort; no evidence escapes into global caches.
Only the approved route may reach this function, including transcript mode. -/
private def fieldSort (type : Expr) : PolynomialM (Nat × SortExpr) := do
  let admission ← match (← get).admissions[type]? with
    | some admission => pure admission
    | none => do
        let some descriptor ← getResidueDescriptor? type | unsupported type
        let admission ← admitNativeField descriptor
        modify fun state => { state with admissions := state.admissions.insert type admission }
        pure admission
  let p := admission.residue.modulusValue
  if let some sort := (← get).sorts[p]? then return (p, sort)
  let some indexed := finiteFieldSort p | throwError "native field admission supplied zero modulus"
  let symbol := mkReservedSymbol s!"@FF{p}"
  defineSort symbol none indexed
  associate symbol type (← inferType type) (some p)
  let sort := SortExpr.SymbolSort symbol
  modify fun state => { state with sorts := state.sorts.insert p sort }
  return (p, sort)

private def literal (p : Nat) (n : Int) : PolynomialM SmtTerm := do
  let some term := finiteFieldLit n p | throwError "native field literal requires admitted positive modulus"
  return term

/-- Encode the total inverse graph, not just the nonzero reciprocal equation.
The caller asserts this obligation positively, outside all Boolean occurrences
of the witness and alongside the negated residual query. -/
def translateInverseGraph (p : Nat) (denominator witness : SmtTerm) : Option SmtTerm := do
  let zero ← finiteFieldLit 0 p
  let one ← finiteFieldLit 1 p
  return orSmt (andSmt (eqSmt denominator zero) (eqSmt witness zero))
    (eqSmt (mkSimpleSmtAppN (mkReservedSymbol "ff.mul") #[denominator, witness]) one)

/-- A denominator has one typed witness per normalized modulus and exact source
expression in this opened query. No recursive translation opens binders, and
this cache is discarded before the telescope closes. In particular no local
dependent inverse becomes a global function or a cross-query declaration. -/
private def inverseWitness (p : Nat) (sort : SortExpr) (denominator : Expr)
    (term : SmtTerm) : PolynomialM SmtTerm := do
  if let some witness := (← get).inverses[(p, denominator)]? then return witness
  let type ← inferType denominator
  let some admission := (← get).admissions[type]?
    | throwError "inverse graph requires the denominator's scoped field admission"
  let dictionary := mkApp2 (mkConst ``Residue.instInv)
    admission.residue.modulus admission.evidence
  let source := mkApp3 (mkConst ``Inv.inv [levelZero]) type dictionary denominator
  let symbol := mkReservedSymbol s!"@ffinv{← mkFreshId}"
  let witness := smtSimpleVarId symbol
  let some graph := translateInverseGraph p term witness
    | throwError "inverse graph requires an admitted positive modulus"
  declareConst symbol sort
  associate symbol source type (some p) false
    (some { scope := (← get).scope, denominator })
  modify fun state => { state with
    inverses := state.inverses.insert (p, denominator) witness
    graphs := state.graphs.push graph }
  return witness

/-- Typed semantic wrappers are keyed by normalized modulus, never the printed
source carrier. Subtraction is addition of the additive inverse. -/
private def operation (p : Nat) (sort : SortExpr) (name : String) (source : Expr) :
    PolynomialM SmtSymbol := do
  let symbol := mkReservedSymbol s!"@FF{p}.{name}"
  unless (← get).operations.contains (p, name) do
    let x := mkReservedSymbol "@x"
    let y := mkReservedSymbol "@y"
    let xv := smtSimpleVarId x
    let yv := smtSimpleVarId y
    let native (op : String) (args : Array SmtTerm) := mkSimpleSmtAppN (mkReservedSymbol op) args
    let (params, body) := match name with
      | "add" => (#[(x, sort), (y, sort)], native "ff.add" #[xv, yv])
      | "mul" => (#[(x, sort), (y, sort)], native "ff.mul" #[xv, yv])
      | "neg" => (#[(x, sort)], native "ff.neg" #[xv])
      | _ => (#[(x, sort), (y, sort)], native "ff.add" #[xv, native "ff.neg" #[yv]])
    defineFun symbol params sort body
    associate symbol source (← inferType source) (some p)
    modify fun state => { state with operations := state.operations.insert (p, name) }
  return symbol

/-- One shared square-and-multiply function per modulus/exponent. Each binary
step binds its square once in a nested SMT let (bindings are not simultaneous).
Construction and printed body size are logarithmic, including exponent zero. -/
private def power (p : Nat) (sort : SortExpr) (n : Nat) (source : Expr) :
    PolynomialM SmtSymbol := do
  let name := s!"pow{n}"
  let symbol := mkReservedSymbol s!"@FF{p}.{name}"
  unless (← get).operations.contains (p, name) do
    let x := mkReservedSymbol "@x"
    let mul (a b : SmtTerm) := mkSimpleSmtAppN (mkReservedSymbol "ff.mul") #[a, b]
    let mut exponent := n
    let mut base := smtSimpleVarId x
    let mut result ← literal p 1
    let mut bindings : Array (SmtSymbol × SmtTerm) := #[]
    let mut index := 0
    while exponent > 0 do
      if exponent % 2 == 1 then
        let acc := mkReservedSymbol s!"@acc{index}"
        bindings := bindings.push (acc, mul result base)
        result := smtSimpleVarId acc
      exponent := exponent / 2
      if exponent > 0 then
        let square := mkReservedSymbol s!"@square{index}"
        bindings := bindings.push (square, mul base base)
        base := smtSimpleVarId square
      index := index + 1
    for binding in bindings.reverse do
      result := .LetTerm #[binding] result
    defineFun symbol #[(x, sort)] sort result
    associate symbol source (← inferType source) (some p)
    modify fun state => { state with operations := state.operations.insert (p, name) }
  return symbol

private def booleanType (type : Expr) : MetaM Bool := do
  return type.isProp || (← isDefEq type (mkConst ``Bool))

/-- Translate only the admitted bounded fragment. There is deliberately no
fallback to generic datatype, integer, conversion or uninterpreted encoding. -/
private partial def polynomialTerm (e : Expr) : PolynomialM SmtTerm := do
  if let some term := (← get).terms[e]? then return term
  let term ← visit e
  modify fun state => { state with terms := state.terms.insert e term }
  return term
where
  visit (e : Expr) : PolynomialM SmtTerm := do
    if let .mdata _ body := e then return ← polynomialTerm body
    if let .letE _ _ value body _ := e then return ← polynomialTerm (body.instantiate1 value)
    let type ← inferType e
    let field := (← getResidueModulus? type).isSome
    unless field || (← booleanType type) do unsupported e
    if e.isFVar then
      let (modulus, sort) ← if field then do
          let (p, sort) ← fieldSort type
          pure (some p, sort)
        else pure (none, boolSort)
      let symbol := mkReservedSymbol s!"@ffvar{← mkFreshId}"
      declareConst symbol sort
      associate symbol e type modulus true
      return smtSimpleVarId symbol
    match e with
    | .const ``True _ | .const ``Bool.true _ => return trueSmt
    | .const ``False _ | .const ``Bool.false _ => return falseSmt
    | .forallE _ domain body _ =>
        -- Nondependent implication is Boolean structure, not a residual quantifier.
        if !(← isProp domain) || body.hasLooseBVars then unsupported e
        return impliesSmt (← polynomialTerm domain) (← polynomialTerm body)
    | .app .. =>
        let f := e.getAppFn
        let args := e.getAppArgs
        let .const name _ := f | unsupported e
        if field && (← isOpaqueResidueOperation name args) then
          let (p, sort) ← fieldSort type
          match name with
          | ``OfNat.ofNat =>
              let some n ← getNatModulus? args[1]! | unsupported e
              return ← literal p n
          | ``Nat.cast | ``NatCast.natCast | ``Int.cast | ``IntCast.intCast =>
              -- Only closed literals are coefficients; no representation bridge.
              let value := args.back!
              if let some n := isIntValue? value then return ← literal p n
              if let some n := isNatValue? value then return ← literal p n
              unsupported e
          | ``HPow.hPow =>
              let some n ← getNatModulus? args.back! | unsupported e
              let op ← power p sort n e
              return mkSimpleSmtAppN op #[← polynomialTerm args[args.size - 2]!]
          | ``Inv.inv =>
              let denominator := args.back!
              return ← inverseWitness p sort denominator (← polynomialTerm denominator)
          | ``HDiv.hDiv | ``Div.div =>
              let numerator ← polynomialTerm args[args.size - 2]!
              let denominator := args.back!
              let witness ← inverseWitness p sort denominator (← polynomialTerm denominator)
              let op ← operation p sort "mul" e
              return mkSimpleSmtAppN op #[numerator, witness]
          | ``Neg.neg =>
              if let .const coefficientName _ := args.back!.getAppFn then
                if ← isOpaqueResidueOperation coefficientName args.back!.getAppArgs then
                  if let some n := coefficient? args.back! then return ← literal p (-n)
              let op ← operation p sort "neg" e
              return mkSimpleSmtAppN op #[← polynomialTerm args.back!]
          | _ =>
              let opName := if name == ``HAdd.hAdd || name == ``Add.add then "add"
                else if name == ``HMul.hMul || name == ``Mul.mul then "mul" else "sub"
              let op ← operation p sort opName e
              return mkSimpleSmtAppN op #[← polynomialTerm args[args.size - 2]!, ← polynomialTerm args.back!]
        match name with
        | ``Eq =>
            if args.size != 3 then unsupported e
            return eqSmt (← polynomialTerm args[1]!) (← polynomialTerm args[2]!)
        | ``Ne =>
            if args.size != 3 then unsupported e
            return notSmt (eqSmt (← polynomialTerm args[1]!) (← polynomialTerm args[2]!))
        | ``And | ``and => return andSmt (← polynomialTerm args[0]!) (← polynomialTerm args[1]!)
        | ``Or | ``or => return orSmt (← polynomialTerm args[0]!) (← polynomialTerm args[1]!)
        | ``Iff => return eqSmt (← polynomialTerm args[0]!) (← polynomialTerm args[1]!)
        | ``Not | ``not => return notSmt (← polynomialTerm args[0]!)
        | ``Blaster.decide' => return ← polynomialTerm args[0]!
        | ``ite => return iteSmt (← polynomialTerm args[1]!) (← polynomialTerm args[3]!) (← polynomialTerm args[4]!)
        | ``Blaster.dite' =>
            let branch (value : Expr) : PolynomialM SmtTerm := do
              let .lam _ _ body _ := value | unsupported value
              if body.hasLooseBVars then unsupported value
              polynomialTerm body
            return iteSmt (← polynomialTerm args[1]!) (← branch args[2]!) (← branch args[3]!)
        | _ => unsupported e
    | _ => unsupported e

  coefficient? (e : Expr) : Option Int := do
    let args := e.getAppArgs
    if !e.getAppFn.isConstOf ``OfNat.ofNat then none
    else (isNatValue? args[1]!).map Int.ofNat

/-- Translate an optimized native query while its opened theorem parameters and
checked prime evidence are in scope. Returns none only for a non-native query.
Preflight must have selected the approved session (or cvc5 transcript route).
The resulting term is the positive goal; the caller asserts its negation.
All graph obligations are separate positive assertions, hence conjoined with
that negation, never inserted under an occurrence's Boolean polarity. -/
def translatePolynomial (e : Expr) : TranslateEnvT (Option SmtTerm) :=
  withNativeFieldQuery e fun parameters body fields => do
    if fields.isEmpty then return none
    let env ← get
    unless env.smtEnv.nativeFieldQualified && env.smtEnv.singleSolver == some .cvc5 do
      throwEnvError "native finite-field translation requires the approved cvc5 preflight route"
    unless env.optEnv.options.solverOptions.onlySmtLib || !env.smtEnv.sessions.isEmpty do
      throwEnvError "native finite-field translation requires an active preflight-qualified session"
    let action : PolynomialM SmtTerm := do
      let mut premises : Array SmtTerm := #[]
      for parameter in parameters do
        let type ← inferType parameter
        if (type.app1? ``PrimeModulus).isSome then
          -- Checked by admission, not an SMT predicate or an arbitrary assumption.
          pure ()
        else if ← isProp type then
          premises := premises.push (← polynomialTerm type)
        else
          discard <| polynomialTerm parameter
      let mut result ← polynomialTerm body
      for premise in premises.reverse do result := impliesSmt premise result
      for graph in (← get).graphs do assertTerm graph
      return result
    let admissions := fields.foldl (fun cache field =>
      cache.insert field.residue.type field) ({} : Std.HashMap Expr NativeFieldAdmission)
    return some (← action.run' { admissions, scope := ← mkFreshId })

end Blaster.Smt
