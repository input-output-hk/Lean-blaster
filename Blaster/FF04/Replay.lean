import Blaster.FF04.Nominal
import Lean

/-!
# FF-04 checked text-proof slice

This deliberately small CPC reader requires explicit step conclusions. It maps
solver declarations to existing Lean locals, discharges each parsed assumption
from the original context, and proves every step as a closed implication from
only its named premises. Rule labels (including `trust`) carry no authority.
Unsupported syntax and failed proof search are errors, never admissions.
-/

namespace Blaster.FF04.Replay
open Lean Meta Elab Tactic

inductive SExpr where
  | atom : String → SExpr
  | list : List SExpr → SExpr
  deriving Repr, BEq

private def tokenize (s : String) : List String := Id.run do
  let mut tokens := []
  let mut word := ""
  let mut comment := false
  for c in s.toList do
    if comment then
      if c == '\n' then comment := false
    else if c == ';' || c.isWhitespace || c == '(' || c == ')' then
      if !word.isEmpty then tokens := word :: tokens; word := ""
      if c == ';' then comment := true
      if c == '(' || c == ')' then tokens := String.singleton c :: tokens
    else word := word.push c
  if !word.isEmpty then tokens := word :: tokens
  return tokens.reverse

private partial def parseOne : List String → Except String (SExpr × List String)
  | [] => .error "unexpected end of CPC input"
  | ")" :: _ => .error "unexpected closing parenthesis"
  | "(" :: ts => do
    let (xs, rest) ← parseList ts
    return (.list xs, rest)
  | s :: ts => .ok (.atom s, ts)
where
  parseList : List String → Except String (List SExpr × List String)
    | [] => .error "unclosed CPC list"
    | ")" :: ts => .ok ([], ts)
    | ts => do
      let (x, ts) ← parseOne ts
      let (xs, ts) ← parseList ts
      return (x :: xs, ts)

/-- Parse exactly one CPC proof, optionally prefixed by the solver's `unsat`. -/
def parse (s : String) : Except String (List SExpr) := do
  let ts := tokenize s
  let ts := if ts.head? == some "unsat" then ts.drop 1 else ts
  let (.list xs, []) ← parseOne ts | .error "expected one complete CPC proof"
  return xs

private abbrev Bindings := List (String × Expr)

private def lookup (xs : Bindings) (name : String) : TacticM Expr := do
  let some (_, e) := xs.find? (fun x => x.1 == name)
    | throwError "unknown CPC identifier {name}"
  return e

private def fresh (xs : Bindings) (name : String) : TacticM Unit := do
  if xs.any (fun x => x.1 == name) then throwError "duplicate CPC identifier {name}"

private partial def term (modulus : Nat) (xs : Bindings) : SExpr → TacticM Expr
  | .atom "true" => pure (mkConst ``True)
  | .atom "false" => pure (mkConst ``False)
  | .atom s => lookup xs s
  | .list [.atom "ff.value", .atom p, .atom n] => do
    unless p.toNat? == some modulus do throwError "CPC literal modulus mismatch"
    let some n := n.toNat? | throwError "invalid CPC numeral"
    mkAppOptM ``OfNat.ofNat #[some (mkApp (mkConst ``Blaster.FiniteField.Residue) (mkNatLit modulus)),
      some (mkNatLit n), none]
  | .list [.atom "=", a, b] => do mkEq (← term modulus xs a) (← term modulus xs b)
  | .list [.atom "not", a] => do mkAppM ``Not #[← term modulus xs a]
  | .list [.atom "ff.neg", a] => do mkAppM ``Neg.neg #[← term modulus xs a]
  | .list [.atom "ff.add", a, b] => do mkAppM ``HAdd.hAdd #[← term modulus xs a, ← term modulus xs b]
  | .list [.atom "ff.mul", a, b] => do mkAppM ``HMul.hMul #[← term modulus xs a, ← term modulus xs b]
  | e => throwError "unsupported CPC term {repr e}"

private def localNamed (name : String) : TacticM Expr := do
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && decl.userName.toString == name then
      return decl.toExpr
  throwError "CPC declaration has no original Lean variable {name}"

private def premiseNames : List SExpr → TacticM (String × List String)
  | [.atom ":rule", .atom rule] => pure (rule, [])
  | .atom ":rule" :: .atom rule :: rest => do
    let mut premises := []
    let mut seenPremises := false
    let mut seenArgs := false
    let mut rest := rest
    while !rest.isEmpty do
      match rest with
      | .atom ":premises" :: .list ps :: tail =>
        if seenPremises then throwError "duplicate CPC premises"
        seenPremises := true
        premises ← ps.mapM fun p => match p with
          | .atom s => pure s
          | _ => throwError "invalid CPC premise"
        rest := tail
      | .atom ":args" :: .list _ :: tail =>
        if seenArgs then throwError "duplicate CPC args"
        seenArgs := true
        rest := tail
      | _ => throwError "unsupported CPC step attributes"
    return (rule, premises)
  | _ => throwError "missing CPC rule"

/-- Recheck a closed implication; no unrelated original hypotheses are available. -/
private def proveStep (vars premises : Array Expr) (conclusion : Expr) : TacticM Expr := do
  let mut ty := conclusion
  for premise in premises.reverse do
    ty ← mkArrow (← inferType premise) ty
  ty ← mkForallFVars vars ty
  let proof ← withLCtx {} {} do
    let goal ← mkFreshExprMVar ty
    let saved ← getGoals
    setGoals [goal.mvarId!]
    evalTactic (← `(tactic| (intros; grind (ematch := 0))))
    unless (← getGoals).isEmpty do throwError "CPC step left unsolved goals"
    let proof ← instantiateMVars goal
    setGoals saved
    return proof
  return mkAppN proof (vars ++ premises)

/-- Replay the bounded CPC ring/Boolean slice against the current original goal. -/
def replay (text : String) : TacticM Unit := withMainContext do
  let commands ← match parse text with
    | .ok xs => pure xs
    | .error e => throwError "{e}"
  let original ← getMainGoal
  let target ← original.getType
  unless ← isProp target do throwError "FF-04 expects a proposition"
  evalTactic (← `(tactic| apply Classical.byContradiction))
  evalTactic (← `(tactic| intro ff04_negatedGoal))
  withMainContext do
    let mut terms : Bindings := []
    let mut proofs : Bindings := []
    let mut vars := #[]
    let mut modulus : Option Nat := none
    let mut finalProof : Option Expr := none
    for command in commands do
      match command with
      | .list [.atom "declare-const", .atom name,
          .list [.atom "_", .atom "FiniteField", .atom p]] =>
        fresh terms name
        let some p := p.toNat? | throwError "invalid CPC modulus"
        if p < 2 then throwError "FF-04 expects modulus at least two"
        if let some previous := modulus then
          unless previous == p do throwError "mixed CPC moduli"
        modulus := some p
        let v ← localNamed name
        unless ← isDefEq (← inferType v) (mkApp (mkConst ``Blaster.FiniteField.Residue) (mkNatLit p)) do
          throwError "CPC variable type does not match original Lean local"
        terms := (name, v) :: terms
        vars := vars.push v
      | .list [.atom "define", .atom name, .list [], rhs] =>
        fresh terms name
        let some p := modulus | throwError "missing CPC field declaration"
        terms := (name, ← term p terms rhs) :: terms
      | .list [.atom "assume", .atom name, proposition] =>
        fresh proofs name
        let some p := modulus | throwError "missing CPC field declaration"
        let ty ← term p terms proposition
        unless ← isProp ty do throwError "CPC assumption is not a proposition"
        let g ← mkFreshExprMVar ty
        try g.mvarId!.assumption
        catch _ => throwError "CPC assumption does not match an original Lean hypothesis or negated goal"
        proofs := (name, ← instantiateMVars g) :: proofs
      | .list (.atom "step" :: .atom name :: proposition :: attrs) =>
        fresh proofs name
        let (rule, names) ← premiseNames attrs
        unless ["evaluate", "eq-refl", "refl", "trust", "cong", "nary_cong", "trans", "eq_resolve"].contains rule do
          throwError "unsupported CPC rule {rule}"
        let some p := modulus | throwError "missing CPC field declaration"
        let ty ← term p terms proposition
        unless ← isProp ty do throwError "CPC conclusion is not a proposition"
        let ps ← names.toArray.mapM (lookup proofs)
        let pr ← proveStep vars ps ty
        proofs := (name, pr) :: proofs
        finalProof := some pr
      | _ => throwError "unsupported CPC command {repr command}"
    let some proof := finalProof | throwError "CPC proof has no final step"
    unless ← isDefEq (← inferType proof) (mkConst ``False) do
      throwError "CPC final step is not false"
    (← getMainGoal).assign proof
    replaceMainGoal []

elab "ff04_replay " text:str : tactic => replay text.getString

end Blaster.FF04.Replay
