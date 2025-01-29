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
    ``Iff,
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
    ``Nat.le, -- defining LE.le for Nat, Nat.lt is defined with Nat.le
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

end Solver.Optimize
