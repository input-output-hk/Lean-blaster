import Lean
open Lean Meta

/-- Return `true` if `op1` and `op2` are physically equivalent, i.e., points to same memory address.
-/
@[inline] private unsafe def exprEqUnsafe (op1 : Expr) (op2 : Expr) : MetaM Bool :=
  pure (ptrEq op1 op2)

/-- Safe implementation of physically equivalence for Expr.
-/
@[implemented_by exprEqUnsafe]
def exprEq (op1 : Expr) (op2 : Expr) : MetaM Bool := isDefEqGuarded op1 op2

/-- list of operators that must not be unfolded, i.e., they will directly be
translated to their corresponding SMT counterpart.
-/
def opaqueFuns : NameHashSet :=
  List.foldr (fun c s => s.insert c) HashSet.empty
  [
    -- structural equality
    ``Eq,
    -- DecidableEq constraint
    ``DecidableEq,
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
    -- Relational operators
    ``LE.le, -- GE.ge a b is abbrev for LE.le b a
    ``LT.lt, -- Gt.gt a b is abbrev for LT.lt b a
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
    ``Nat.ble,
    ``Nat.blt,
    ``Nat.beq,
    ``Nat.pow,
  ]

/-- list of types for which the BEq instance is guaranteed to be reflexive, symmetric and transitive.
TODO: add other basic lean types (e.g., Char, etc)
-/
def beqCompatibleTypes : NameHashSet :=
  List.foldr (fun c s => s.insert c) HashSet.empty
  [ ``Nat,
    ``Int,
    ``Bool,
    ``String
  ]

/-- Return `true` is `e` corresponds to a sort in `beqCompatibletypes`.
-/
def isCompatibleBeqType (e : Expr) : Bool :=
  match e with
  | Expr.const n _ => beqCompatibleTypes.contains n
  | _ => false

/-- Return `true` if function name is `BEq.beq` with a sort parameter in `beqCompatibletypes`.
In fact, we can't assume that `BEq.beq` will properly be defined for any user-defined types or
parametric inductive types (e.g., List, Option, etc). Indeed, the provided definition
may not satisfy refl, symm and trans.
-/
def isOpaqueBeq (f : Name) (args : Array Expr) : Bool :=
  if f == `BEq.beq && args.size > 0
  then isCompatibleBeqType args[0]!
  else false

/-- Return `true` if function name `f` is tagged as an opaque definition. -/
def isOpaqueFun (f : Name) (args: Array Expr) : Bool :=
  opaqueFuns.contains f || isOpaqueBeq f args

/-- Same as `isOpaqueFun` expect that `f` is an expression. -/
def isOpaqueFunExpr (f : Expr) (args: Array Expr) : Bool :=
  match f with
  | Expr.const n _ => isOpaqueFun n args
  | _ => false
