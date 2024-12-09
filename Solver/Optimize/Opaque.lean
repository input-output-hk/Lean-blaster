import Lean
open Lean Meta

namespace Solver.Optimize

/-- list of operators that must not be unfolded, i.e., they will directly be
translated to their corresponding SMT counterpart.
-/
def opaqueFuns : NameHashSet :=
  List.foldr (fun c s => s.insert c) HashSet.empty
  [
    -- structural equality
    ``Eq,
    -- decide predicate on proposition
    ``Decidable.decide,
    -- Prop operators
    ``And,
    ``Or,
    ``Not,
    -- ite
    ``ite,
    -- dependent ite
    ``dite,
    -- existential quantifier
    ``Exists,
    -- Int operators
    ``Int.add, -- Int.sub is defined as m + (-n)
    ``Int.neg,
    ``Int.mul,
    ``Int.toNat,
    -- Division rounding towards zero
    ``Int.div,
    ``Int.mod,
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
    ``Nat.le -- defining LE.le for Nat, Nat.lt is defined with Nat.le
  ]

/-- list of types for which:
     - BEq instance is guaranteed to be reflexive, symmetric and transitive.
     - LT instance is guaranteed to be irrelexive, anti-symmetric and transitive.
     - LE instance is guaranteed to be reflexive, symmetric and transitive.
TODO: add other basic lean types (e.g., Char, etc)
-/
def relationalCompatibleTypes : NameHashSet :=
  List.foldr (fun c s => s.insert c) HashSet.empty
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

/-- Given `f x₁ ... xₙ`, return `true` only when one of the following conditions is satisfied:
     - `f := BEq.beq` with sort parameter in `relationalCompatibleTypes`
     - `f := LT.lt` with sort parameter in `relationalCompatibleTypes`
     - `f : LE.le` with sort parameter in `relationalCompatibleTypes`

In fact, we can't assume that `BEq.beq`, `LT.lt` and `LE.le` will properly be defined
for any user-defined types or parametric inductive types (e.g., List, Option, etc).
-/
def isOpaqueRelational (f : Name) (args : Array Expr) : MetaM Bool := do
  match f with
  | `BEq.beq
  | `LT.lt
  | `LE.le =>
      if args.size < 1 then throwError "isOpaqueRelational: implicit arguments"
      return (isCompatibleRelationalType args[0]!)
  | _ => return false


/-- Return `true` if function name `f` is tagged as an opaque definition. -/
def isOpaqueFun (f : Name) (args: Array Expr) : MetaM Bool :=
  return (opaqueFuns.contains f || (← isOpaqueRelational f args))

/-- Same as `isOpaqueFun` expect that `f` is an expression. -/
def isOpaqueFunExpr (f : Expr) (args: Array Expr) : MetaM Bool :=
  match f with
  | Expr.const n _ => isOpaqueFun n args
  | _ => return false

end Solver.Optimize
