import Lean
import Blaster.Optimize.Env.Types
import Blaster.Data.HashSet
import Blaster.Optimize.Decidable

open Lean Meta Blaster.Data.HashSet

namespace Blaster.Optimize

/-- list of operators that must not be unfolded, i.e., they will directly be
translated to their corresponding SMT counterpart.
-/
def opaqueFuns : HashSet Name :=
  List.foldr (fun c s => s.insert c) HashSet.emptyWithCapacity
  [
    -- structural equality
    ``Eq,
    ``Ne,
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
    ``Int.pow,
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

/-- list of non-opaque rec operators on which normalization rules and constant propagation are applied. -/
def optRecFuns : HashSet Name :=
  List.foldr (fun c s => s.insert c) HashSet.emptyWithCapacity
  [ -- List operators
    ``List.append,
    ``List.get?Internal,
    ``List.length,
    ``List.reverseAux,
    ``List.take,
    ``List.drop,
    ``List.replicate
  ]

/-- list of types for which:
     - LT instance is guaranteed to be irrelexive, anti-symmetric and transitive.
     - LE instance is guaranteed to be reflexive, symmetric and transitive.
    NOTE: add other basic lean types (e.g., Char, etc)
-/
def relationalCompatibleTypes : HashSet Name :=
  List.foldr (fun c s => s.insert c) HashSet.emptyWithCapacity
  [ ``Nat,
    ``Int,
    ``Bool,
    ``String
  ]

/-- Return `true` if `e` corresponds to a type in `relationalCompatibletypes`. -/
def isCompatibleRelationalType (e : Expr) : Bool :=
  match e.getAppFn with
  | Expr.const n _ => relationalCompatibleTypes.contains n
  | _ => false

/-- list of types for OfNat.ofNat for which we have a normalization rule. -/
def ofNatTypes : HashSet Name :=
  List.foldr (fun c s => s.insert c) HashSet.emptyWithCapacity
  [ ``Nat,
    ``Int,
    ``UInt8,
    ``UInt16,
    ``UInt32,
    ``UInt64,
    ``USize,
    ``Int8,
    ``Int16,
    ``Int32,
    ``Int64,
    ``ISize,
    ``Fin,
    ``BitVec,
  ]

/-- Return `true` if `e` corresponds to a type in `ofNatTypes`. -/
def isOfNatType (e : Expr) : Bool :=
  match e.getAppFn with
  | Expr.const n _ => ofNatTypes.contains n
  | _ => false

end Blaster.Optimize
