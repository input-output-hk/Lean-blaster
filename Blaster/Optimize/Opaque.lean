import Lean
import Blaster.Optimize.Decidable
import Blaster.FiniteField.Structural
import Blaster.FiniteField.Field

open Lean Meta

namespace Blaster.Optimize

/-- Recognize only the instantiated canonical residue dictionary, not merely an
    overloaded operator name or its surface carrier. Symbolic moduli are valid
    here: concrete recognition and prime admission belong to higher layers.
    Definitional dictionary aliases are accepted; unrelated local instances are
    not. Fresh comparison metavariables never escape into the caller's state. -/
def isOpaqueResidueOperation (f : Name) (args : Array Expr) : MetaM Bool := do
  let (instanceName, instanceIndex, wrapper) ←
    match f with
    | ``HAdd.hAdd => pure (``Blaster.FiniteField.Residue.instAdd, 3, some ``instHAdd)
    | ``HMul.hMul => pure (``Blaster.FiniteField.Residue.instMul, 3, some ``instHMul)
    | ``HSub.hSub => pure (``Blaster.FiniteField.Residue.instSub, 3, some ``instHSub)
    | ``HDiv.hDiv => pure (``Blaster.FiniteField.Residue.instDiv, 3, some ``instHDiv)
    | ``Add.add => pure (``Blaster.FiniteField.Residue.instAdd, 1, none)
    | ``Mul.mul => pure (``Blaster.FiniteField.Residue.instMul, 1, none)
    | ``Sub.sub => pure (``Blaster.FiniteField.Residue.instSub, 1, none)
    | ``Neg.neg => pure (``Blaster.FiniteField.Residue.instNeg, 1, none)
    | ``Inv.inv => pure (``Blaster.FiniteField.Residue.instInv, 1, none)
    | ``Div.div => pure (``Blaster.FiniteField.Residue.instDiv, 1, none)
    | ``OfNat.ofNat => pure (``Blaster.FiniteField.Residue.instOfNat, 2, none)
    | ``Nat.cast
    | ``NatCast.natCast => pure (``Blaster.FiniteField.Residue.instNatCast, 1, none)
    | ``Int.cast
    | ``IntCast.intCast => pure (``Blaster.FiniteField.Residue.instIntCast, 1, none)
    | ``HPow.hPow => pure (``Blaster.FiniteField.Residue.instHPowNat, 3, none)
    | _ => return false
  if args.size ≤ instanceIndex then return false
  let type := args[0]!
  let some modulus ← Blaster.FiniteField.getResidueModulus? type | return false
  let actual := args[instanceIndex]!
  -- Do not solve caller-owned metavariables just to recognize an operation.
  if actual.hasMVar || type.hasMVar then return false
  withoutModifyingState do
    let canonical := mkConst instanceName
    let (params, _, _) ← forallMetaTelescope (← inferType canonical)
    unless ← isDefEq params[0]! modulus do return false
    let mut expected := mkAppN canonical params
    if let some wrapperName := wrapper then
      expected := mkApp2 (mkConst wrapperName [levelZero]) type expected
    -- Checking the instantiated dictionary type also checks all heterogeneous
    -- carrier positions, the literal index, and the natural exponent type.
    unless ← isDefEq (← inferType actual) (← inferType expected) do return false
    if instanceIndex == 3 then
      unless ← isDefEq args[2]! type do return false
      let rhsType := if f == ``HPow.hPow then mkConst ``Nat else type
      unless ← isDefEq args[1]! rhsType do return false
    if f == ``OfNat.ofNat then
      unless ← isDefEq params[2]! args[1]! do return false
    isDefEq actual expected

/-- list of operators that must not be unfolded, i.e., they will directly be
translated to their corresponding SMT counterpart.
-/
def opaqueFuns : NameHashSet :=
  List.foldr (fun c s => s.insert c) Std.HashSet.emptyWithCapacity
  [
    -- structural equality
    ``Eq,
    -- decide predicate on proposition (normalized to Blaster.decide')
    ``Decidable.decide,
    -- Prop operators
    ``And,
    ``Or,
    ``Not,
    ``Iff,
    -- if then else
    ``ite, -- normalized to Blaster.dite'
    -- dependent ite
    ``dite, -- normalized to Blaster.dite'
    -- existential quantifier
    ``Exists,
    -- Int operators
    ``Int.add, -- Int.sub is defined as m + (-n)
    ``Int.neg,
    ``Int.mul,
    ``Int.toNat,
    -- Division rounding towards zero
    ``Int.tdiv,
    ``Int.tmod,
    -- Division rounding towards negative infinity
    ``Int.fdiv,
    ``Int.fmod,
    -- Euclidean division (default one)
    ``Int.ediv,
    ``Int.emod,
    ``Int.pow,
    ``Int.le, -- defining LE.le for Int, Int.lt is defined with ≤
    -- Bool operators
    ``and,
    ``or,
    ``not,
    -- Nat operators
    ``Nat.add,
    ``Nat.sub,
    ``Nat.mul,
    ``Nat.div,
    ``Nat.mod,
    ``Nat.pred,
    ``Nat.ble, -- Nat.blt is defined with Nat.beq
    ``Nat.beq,
    ``Nat.pow,
    ``Nat.le, -- defining LE.le for Nat, Nat.lt is defined with Nat.le
    ``Blaster.decide', -- decide predicate that ignores decidable instance
    ``Blaster.dite', -- dependent ite that ignores decidable instance
    -- Note: ite is normalized to Blaster.dite'
    -- String operators
    ``String.append,
    ``String.replace,
    ``String.length
  ]

/-- list of types for which:
     - LT instance is guaranteed to be irrelexive, anti-symmetric and transitive.
     - LE instance is guaranteed to be reflexive, symmetric and transitive.
TODO: add other basic lean types (e.g., Char, etc)
-/
def relationalCompatibleTypes : NameHashSet :=
  List.foldr (fun c s => s.insert c) Std.HashSet.emptyWithCapacity
  [ ``Nat,
    ``Int,
    ``Bool,
    ``String
  ]

/-- Return `true` is `e` corresponds to a sort in `relationalCompatibletypes`.
-/
def isCompatibleRelationalType (e : Expr) : Bool :=
  match e with
  | Expr.const n _ => relationalCompatibleTypes.contains n
  | _ => false

end Blaster.Optimize
