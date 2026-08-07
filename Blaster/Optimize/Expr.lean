import Lean
import Blaster.Data.HashSet
import Blaster.Optimize.Decidable

open Lean Meta Declaration Blaster.Data.HashSet

namespace Blaster.Optimize

/-- Sentinel for the allocation-free cache probes in the shared-expression walkers. -/
def instCacheMiss : Expr := .const `__Blaster.dummy__ []

/-- Physically equivalence for Expr. -/
@[inline] def exprEq (op1 : Expr) (op2 : Expr) : Bool :=
  unsafe ptrEq op1 op2

structure PtrExpr where
 expr : Lean.Expr
deriving Repr

@[always_inline, inline]
def ptrAddrHash (x : USize) : UInt64 :=
    let x0 := x.toUInt64
    let x1 := x0 ^^^ (x0 >>> 33)
    let x2 := x1 * 0xff51afd7ed558ccd
    let x3 := x2 ^^^ x2 >>> 33
    let x4 := x3 * 0xc4ceb9fe1a85ec53;
    x4 ^^^ (x4 >>> 33)

abbrev hashPtrExpr (e : PtrExpr) : UInt64 :=
  unsafe ptrAddrHash (ptrAddrUnsafe e.expr)

instance : BEq PtrExpr where
  beq e1 e2 := exprEq e1.expr e2.expr

instance : Hashable PtrExpr where
  hash e := hashPtrExpr e

instance : Inhabited PtrExpr where
  default := ⟨mkSort levelZero⟩

instance : Coe Expr PtrExpr where
 coe e := ⟨e⟩

structure SharedExpr where
  expr : Expr

private def hashChild (e : Expr) : UInt64 :=
  match e with
  | .bvar .. | .mvar .. | .const .. | .fvar .. | .sort .. | .lit .. => hash e
  | .app .. | .letE .. | .forallE .. | .lam .. | .mdata .. | .proj .. => hashPtrExpr e


private def sharedHash (e : Expr) : UInt64 :=
  match e with
  | .bvar .. | .mvar .. | .const .. | .fvar .. | .sort .. | .lit .. => hash e
  | .app f a => mixHash 5 (mixHash (hashChild f) (hashChild a))
  | .letE _ _ v b _ => mixHash 7 (mixHash (hashChild v) (hashChild b))
  | .forallE _ d b _ => mixHash 11 (mixHash (hashChild d) (hashChild b))
  | .lam _ d b _ => mixHash 13 (mixHash (hashChild d) (hashChild b))
  | .mdata _ b => mixHash 17 (hashChild b)
  | .proj n i b => mixHash 19 (mixHash (mixHash (hash n) (hash i)) (hashChild b))

private def sharedEq (e1 e2 : Expr) : Bool :=
  if exprEq e1 e2 then true
  else
    match e1 with
    | .bvar .. | .mvar .. | .const .. | .fvar .. | .sort .. | .lit .. => e1 == e2
    | .app f1 a1 =>
         if let .app f2 a2 := e2
         then exprEq f1 f2 && exprEq a1 a2
         else false
    | .letE _ _ v1 b1 _ =>
         if let .letE _ _ v2 b2 _ := e2
         then exprEq v1 v2 && exprEq b1 b2
         else false
    | .forallE _ d1 b1 _ =>
         if let .forallE _ d2 b2 _ := e2
         then exprEq d1 d2 && exprEq b1 b2
         else false
    | .lam _ d1 b1 _ =>
         if let .lam _ d2 b2 _ := e2
         then exprEq d1 d2 && exprEq b1 b2
         else false
    | .mdata d1 b1 =>
         if let .mdata d2 b2 := e2
         then exprEq b1 b2 && d1 == d2
         else false
    | .proj n1 i1 b1 =>
         if let .proj n2 i2 b2 := e2
         then n1 == n2 && i1 == i2 && exprEq b1 b2
         else false

instance : Hashable SharedExpr where
  hash e := sharedHash e.expr

instance : Inhabited SharedExpr where
  default := ⟨mkSort levelZero⟩

instance : BEq SharedExpr where
  beq e1 e2 := sharedEq e1.expr e2.expr

instance : Coe Expr SharedExpr where
 coe e := ⟨e⟩


/-- Cache key for the per-call instantiation/abstraction caches: the subterm's
    47-bit user-space address and the binder offset packed as
    `addr ||| (offset <<< 47)` — a 111-bit value (`BitVec 111` semantics: 47 bits
    of address + up to 64 bits of offset) represented as `Nat`, which is exactly
    `BitVec 111`'s runtime representation but skips its `% 2^111` normalizations.
    For offsets < 2^16 the key fits in 62 bits, so it is an unboxed tagged
    scalar: probes and inserts allocate nothing and map teardown never touches
    refcounts for keys. Larger offsets (deeply nested binders, e.g. huge
    unrolled functions) transparently become GMP bignum keys — slower, but
    correct, with no hard depth limit. -/
structure InstKey where
  packed : Nat

instance : BEq InstKey := ⟨fun a b => a.packed == b.packed⟩
/-- Hash of the key's low 64 bits: exact for scalar keys; bignum keys whose
    offsets agree modulo 2^17 collide in hash (disambiguated by `BEq`), which is
    acceptable because offsets ≥ 2^16 are rare. -/
instance : Hashable InstKey := ⟨fun a => ptrAddrHash (USize.ofNat a.packed)⟩
instance : Inhabited InstKey := ⟨⟨0⟩⟩

/-- Offsets below this bound (2^16) keep `mkInstKey` on the packed-scalar fast path. -/
private def scalarOffsetBound : USize := 65536

@[always_inline, inline]
unsafe def mkInstKeyAux (e : Expr) (offset : USize) : InstKey :=
  if offset < scalarOffsetBound then
    -- addr < 2^47, offset < 2^16 ⇒ packed < 2^63: `toNat` is a tag, not an allocation
    ⟨(ptrAddrUnsafe e ||| (offset <<< 47)).toNat⟩
  else
    ⟨(ptrAddrUnsafe e).toNat ||| (offset.toNat <<< 47)⟩

@[always_inline, inline]
def mkInstKey (e : Expr) (offset : USize) : InstKey :=
  unsafe mkInstKeyAux e offset

/-! ### Allocation-free hash-cons probes

The functions below look up a *composite* expression in a hash-cons set from
its components, without first allocating the candidate node (`Expr.app f a`,
`Expr.lam ..`, etc.). On a cache hit — the common case during optimization —
this avoids the construction (and immediate destruction) of a fresh `Expr`
node that exists only to serve as a probe key.

Each probe must compute exactly `sharedHash` of the would-be node and test
exactly `sharedEq` against stored elements.
-/

/-- Find the canonical `.app f a` in a hash-cons set, if present. -/
@[always_inline, inline]
def findSharedApp? (s : HashSet SharedExpr) (f a : Expr) : SharedExpr :=
  s.getByD (mixHash 5 (mixHash (hashChild f) (hashChild a)))
  (fun x => match x.expr with
            | .app f' a' => exprEq f f' && exprEq a a'
            | _ => false)
  instCacheMiss

/-- Find a canonical `.lam _ d b _` (binder name/info ignored, matching `sharedEq`). -/
@[always_inline, inline]
def findSharedLambda? (s : HashSet SharedExpr) (d b : Expr) : SharedExpr :=
  s.getByD (mixHash 13 (mixHash (hashChild d) (hashChild b)))
  (fun x => match x.expr with
            | .lam _ d' b' _ => exprEq d d' && exprEq b b'
            | _ => false)
  instCacheMiss

/-- Find a canonical `.forallE _ d b _` (binder name/info ignored, matching `sharedEq`). -/
@[always_inline, inline]
def findSharedForall? (s : HashSet SharedExpr) (d b : Expr) : SharedExpr :=
  s.getByD (mixHash 11 (mixHash (hashChild d) (hashChild b)))
  (fun x => match x.expr with
            | .forallE _ d' b' _ => exprEq d d' && exprEq b b'
            | _ => false)
  instCacheMiss

/-- Find a canonical `.letE _ _ v b _` (name/type ignored, matching `sharedEq`). -/
@[always_inline, inline]
def findSharedLet? (s : HashSet SharedExpr) (v b : Expr) : SharedExpr :=
  s.getByD (mixHash 7 (mixHash (hashChild v) (hashChild b)))
  (fun x => match x.expr with
            | .letE _ _ v' b' _ => exprEq v v' && exprEq b b'
            | _ => false)
  instCacheMiss

/-- Find the canonical `.proj n i b` in a hash-cons set, if present. -/
@[always_inline, inline]
def findSharedProj? (s : HashSet SharedExpr) (n : Name) (i : Nat) (b : Expr) : SharedExpr :=
  s.getByD (mixHash 19 (mixHash (mixHash (hash n) (hash i)) (hashChild b)))
  (fun x => match x.expr with
            | .proj n' i' b' => n' == n && i' == i && exprEq b b'
            | _ => false)
  instCacheMiss

/-- Find a canonical `.mdata d b` with the given data and child, if present. -/
@[always_inline, inline]
def findSharedMData? (s : HashSet SharedExpr) (d : MData) (b : Expr) : SharedExpr :=
  s.getByD (mixHash 17 (hashChild b))
  (fun x => match x.expr with
            | .mdata d' b' => exprEq b b' && d' == d
            | _ => false)
  instCacheMiss

/-- Physical equality for `Level`. -/
@[inline] def levelEq (l1 : Level) (l2 : Level) : Bool :=
  unsafe ptrEq l1 l2

/-- Physical equality for `List Level`. -/
@[inline] def levelsEq (l1 : List Level) (l2 : List Level) : Bool :=
  unsafe ptrEq l1 l2


structure PtrName where
  name : Name

/-- Physically equivalence for Name. -/
@[inline] def nameEq (n1 : Name) (n2 : Name) : Bool :=
  unsafe ptrEq n1 n2

abbrev hashPtrName (n : PtrName) : UInt64 :=
  unsafe ptrAddrHash (ptrAddrUnsafe n.name)

instance : BEq PtrName where
  beq n1 n2 := nameEq n1.name n2.name

instance : Inhabited PtrName where
  default := ⟨`__Blaster.dummy__⟩

instance : Hashable PtrName where
  hash n := hashPtrName n

instance : Coe Name PtrName where
 coe n := ⟨n⟩


def getAppFnWithArgsAux : Expr → Array Expr → Nat → (Expr × Array Expr)
  | Expr.app f a, as, i => getAppFnWithArgsAux f (as.set! i a) (i-1)
  | f,       as, _ => (f, as)

/-- Return a function and its arguments -/
@[always_inline, inline] def getAppFnWithArgs (e : Expr) : (Expr × Array Expr) :=
  let dummy := mkSort levelZero
  let nargs := e.getAppNumArgs
  getAppFnWithArgsAux e (Array.replicate nargs dummy) (nargs-1)


/-- Return a function and its arguments with extra args appended -/
@[always_inline, inline]
def getAppFnArgsWithExtraRange (e : Expr) (beginIdx endIdx : Nat) (args : Array Expr) : (Expr × Array Expr) :=
  let dummy := mkSort levelZero
  let nargs := e.getAppNumArgs
  let nbSize := nargs + endIdx - beginIdx
  let repArray := go beginIdx endIdx nargs (Array.replicate nbSize dummy)
  getAppFnWithArgsAux e repArray (nargs-1)

  where
    go (i : Nat) (stop : Nat) (offset : Nat) (repArray : Array Expr) : Array Expr :=
      if i ≥ stop then repArray
      else go (i + 1) stop (offset + 1) (repArray.set! offset args[i]!)

private def getAppArgsAux : Expr → Array Expr → Nat → Array Expr
  | .app f a, as, i => getAppArgsAux f (as.set! i a) (i-1)
  | _,       as, _ => as

/-- Given the function's arguments with extra agrs appended -/
@[inline] def getAppArgsWithExtraRange (e : Expr) (beginIdx endIdx : Nat) (args : Array Expr) : Array Expr :=
  let dummy := mkSort levelZero
  let nargs := e.getAppNumArgs
  let nbSize := nargs + endIdx - beginIdx
  let repArray := go beginIdx endIdx nargs (Array.replicate nbSize dummy)
  getAppArgsAux e repArray (nargs-1)

  where
    go (i : Nat) (stop : Nat) (offset : Nat) (repArray : Array Expr) : Array Expr :=
      if i ≥ stop then repArray
      else go (i + 1) stop (offset + 1) (repArray.set! offset args[i]!)

/-- Return `true` if e contains free / bounded variables. -/
@[always_inline, inline]
def hasVars (e : Expr) : Bool := e.hasFVar || e.hasLooseBVars

structure stkEntry where
  prev : Expr
  next : Expr
 deriving Inhabited

/-- Return true iff `e` contains a free variable `v`. -/
@[always_inline, inline] private unsafe def containsFVarImp (e : Expr) (v : Expr) : Bool :=
  let rec visit (e : Expr) (stk : Array stkEntry) (cache : HashSet PtrExpr) :=
    let skipToNext (xs : Array stkEntry) (cache : HashSet PtrExpr) : Bool :=
      if xs.usize > 0 then
        let topIdx := xs.usize - 1
        let res := xs.uget topIdx lcProof
        let xs := xs.pop
        let cache := cache.insert res.prev
        visit res.next xs cache
      else false
    let continuity (xs : Array stkEntry) (cache : HashSet PtrExpr) : Bool :=
      if xs.usize > 0 then
        let topIdx := xs.usize - 1
        let res := xs.uget topIdx lcProof
        let xs := xs.pop
        if ptrEq res.prev res.next then
          skipToNext xs cache
        else
          let cache := cache.insert res.prev
          visit res.next xs cache
      else false
    if cache.contains e then
      continuity stk cache
    else
      if !e.hasFVar then
        continuity stk cache
      else
        match e with
        | Expr.forallE _ d b _
        | Expr.lam _ d b _
        | Expr.app d b =>
            let stk := stk.push ⟨d, b⟩
            let stk := stk.push ⟨e, e⟩
            visit d stk cache
        | Expr.letE _ t v b _ =>
            let stk := stk.push ⟨v, b⟩
            let stk := stk.push ⟨t, v⟩
            let stk := stk.push ⟨e, e⟩
            visit t stk cache
        | Expr.mdata _ n
        | Expr.proj _ _ n =>
            let stk := stk.push ⟨e, e⟩
            visit n stk cache
        | Expr.fvar _ =>
            if exprEq e v then true
            else continuity stk cache
        | _ => continuity stk cache
  visit e (Array.emptyWithCapacity (e.approxDepth.toNat * 17)) (HashSet.emptyWithCapacity (e.approxDepth.toNat * 123))

@[always_inline, inline]
def containsFVar (e : Expr) (v : Expr) : Bool :=
  if e.hasFVar
  then unsafe containsFVarImp e v
  else false


/-- Return `true` only when the given expression is a `.sort u` such that `u ≠ .zero`. -/
def isTypeUniverse : Expr → Bool
| Expr.sort u => u != .zero
| _ => false


/-- Return the body in a sequence of forall / lambda. -/
def getForallLambdaBody (e : Expr) : Expr :=
 match e with
 | Expr.lam _ _ b _ => getForallLambdaBody b
 | Expr.forallE _ _ b .. => getForallLambdaBody b
 | _ => e

/-- If the `e` is a sequence of lambda `fun x₁ => fun x₂ => ... fun xₙ => b`,
    return `b`. Otherwise return `e`.
-/
def getLambdaBody (e : Expr) : Expr :=
 match e with
 | Expr.lam _ _ b _ => getLambdaBody b
 | _ => e

/-- Determine if `e` is a boolean `not` expression and return its corresponding argument.
    Otherwise return `none`.
-/
@[always_inline, inline] def boolNot? (e: Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.const ``not _) n => some n
  | _ => none

/-- Determine if `e` is a boolean `and` expression and return its corresponding argument.
    Otherwise return `none`.
-/
@[always_inline, inline] def boolAnd? (e: Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``and _) op1) op2 => some (op1, op2)
  | _ => none

/-- Determine if `e` is a boolean `or` expression and return its corresponding argument.
    Otherwise return `none`.
-/
@[always_inline, inline] def boolOr? (e: Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``or _) op1) op2 => some (op1, op2)
  | _ => none


/-- Determine if `e` is a `Bool` literal expression b and return `some b`.
    Otherwise `none`
-/
@[always_inline, inline]
def isBoolValue? (e : Expr) : Option Bool :=
 match e with
 | Expr.const ``true _ => some true
 | Expr.const ``false _ => some false
 | _ => none

/-- Return `true` only when `e` is a `Bool` literal`.
    Otherwise `false`
-/
@[always_inline, inline]
def isBoolCtor (e : Expr) : Bool :=
 match e with
 | Expr.const ``true _
 | Expr.const ``false _ => true
 | _ => false

/-- Return `true` only when `e` is a `Prop` literal`.
    Otherwise `false`
-/
@[always_inline, inline]
def isPropCtor (e : Expr) : Bool :=
 match e with
 | Expr.const ``True _
 | Expr.const ``False _ => true
 | _ => false

@[always_inline, inline]
def isTrueExpr (e : Expr) : Bool :=
 match e with
 | Expr.const ``True _ => true
 | _ => false


@[always_inline, inline]
def isFalseExpr (e : Expr) : Bool :=
 match e with
 | Expr.const ``False _ => true
 | _ => false


/-- Determine if `e` is an boolean `==` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[always_inline, inline] def beq? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``BEq.beq _) psort) pdecide) e1) e2 =>
      some (psort, pdecide, e1, e2)
  | _ => none


/-- Determine if `e` is an `Eq` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[always_inline, inline] def eq? (e : Expr) : Option (Expr × Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) psort) e1) e2 =>
      some (psort, e1, e2)
  | _ => none


/-- Determine if `e` is an `LE.le` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[always_inline, inline] def le? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``LE.le _) psort) pinst) e1) e2 =>
      some (psort, pinst, e1, e2)
  | _ => none

/-- Determine if `e` is an `LT.lt` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[always_inline, inline] def lt? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``LT.lt _) psort) pinst) e1) e2 =>
      some (psort, pinst, e1, e2)
  | _ => none


/-- Determine if `e` is an `Not` expression and return its corresponding argument.
    Otherwise return `none`.
-/
@[always_inline, inline] def propNot? (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.const ``Not _) n => some n
  | _ => none


/-- Determine if `e` is an `And` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[always_inline, inline] def propAnd? (e : Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``And _) op1) op2 => some (op1, op2)
  | _ => none

/-- Determine if `e` is an `Or` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[always_inline, inline] def propOr? (e : Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) op1) op2 => some (op1, op2)
  | _ => none

/-- Return `true` when `e1 := ¬ ne ∧ ne =ₚₜᵣ e2`. Otherwise `false`.
-/
def isNotExprOf (e1 : Expr) (e2 : Expr) : Bool :=
  match propNot? e1 with
  | some op => exprEq e2 op

  | _ => false

/-- Return `true` when `e1 := not ne ∧ ne =ₚₜᵣ e2`. Otherwise `false`.
-/
def isBoolNotExprOf (e1: Expr) (e2 : Expr) : Bool :=
  match boolNot? e1 with
  | some op => exprEq e2 op
  | _ => false

/-- Return `true` when `e1 := false = c ∧ e2 := true = c`. -/
def isNegBoolEqOf (e1: Expr) (e2: Expr) : Bool :=
 match eq? e1, eq? e2 with
 | some (_, e1_op1, e1_op2), some (_, e2_op1, e2_op2) =>
     match e1_op1, e2_op1 with
      | Expr.const ``false _, Expr.const ``true _ => exprEq e1_op2 e2_op2
      | _, _ => false
 | _, _ => false

/-- Return `true` if the given expression is of the form `const ``Bool`. -/
def isBoolType (e : Expr) : Bool :=
  match e with
  | Expr.const ``Bool _ => true
  | _ => false

/-- Return `true` if the given expression is of the form `const ``Nat`. -/
def isNatType (e : Expr) : Bool :=
  match e with
  | Expr.const ``Nat _ => true
  | _ => false

/-- Return `true` if the given expression is of the form `const ``Int`. -/
def isIntType (e : Expr) : Bool :=
  match e with
  | Expr.const ``Int _ => true
  | _ => false

/-- Return `true` if the given expression is of the form `const ``String`. -/
def isStringType (e : Expr) : Bool :=
  match e with
  | Expr.const ``String _ => true
  | _ => false

/-- Determine if `e` is an `autoParam` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[always_inline, inline] def autoParam? (e : Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``autoParam _) t) tac => some (t, tac)
  | _ => none

/-- Return `true` only when `e` is a `Nat` literal expression `Expr.lit (Literal.natVal n)`
-/
@[always_inline, inline]
def isNatValue (e : Expr) : Bool :=
  match e with
  | Expr.lit (Literal.natVal _) => true
  | _ => false

/-- Determine if `e` is a `Nat` literal expression `Expr.lit (Literal.natVal n)`
    and return `some n` as result. Otherwise return `none`
    NOTE: This function is to be used only when it is guaranteed that
    `Nat.zero` has been normalized to `Expr.lit (Literal.natVal 0)`.
-/
@[always_inline, inline]
def isNatValue? (e : Expr) : Option Nat :=
  match e with
  | Expr.lit (Literal.natVal n) => some n
  | _ => none

/-- Determine if `e` is a `String` literal expression `Expr.lit (Literal.strVal s)`
    and return `some s` as result. Otherwise return `none`.
-/
def isStrValue? (e : Expr) : Option String :=
  match e with
  | Expr.lit (Literal.strVal s) => some s
  | _ => none

/-- Determine if `e` is a `UInt32` literal expression `UInt32.mk (Fin.mk UInt32.size n isLt)`
    and return `some n` only when n < UInt32.size.
    Otherwise return `none`
-/
def isUInt32Value? (e : Expr) : Option Nat :=
  match e with
  | Expr.app (Expr.const ``UInt32.ofBitVec _) fn1 =>
     match fn1 with
     | Expr.app (Expr.app (Expr.const ``BitVec.ofFin _) _) fn2 =>
        match fn2 with
        | Expr.app (Expr.app (Expr.app (Expr.const ``Fin.mk _)
            (Expr.lit (Literal.natVal s))) (Expr.lit (Literal.natVal n))) _ =>
            if s != UInt32.size || Nat.ble UInt32.size n
            then none
            else some n
        | _ => none
     | _ => none
  | _ => none


/-- Determine if `e` is a `Char` literal expression `Char.mk (UInt32.mk (Fin.mk UInt32.size n isLt)`
    and return `some Char.ofNat n)` only when `Nat.isValidChar n`.
    Otherwise return `none`
-/
@[always_inline, inline]
def isCharValue? (e : Expr) : Option Char :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Char.mk _) ui) _ =>
      match isUInt32Value? ui with
      | some n => if Nat.isValidChar n then some (Char.ofNat n) else none
      | _ => none
  | _ => none


/-- Return `true` if `e := Nat.add e1 e2`. Otherwise return `false`.
    Note that `true` is returned only when e is a fully applied `Nat.add expression.
-/
def isNatAddExpr (e : Expr) : Bool :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.add _) _) _ => true
  | _ => false


/-- Return `true` if `e := Nat.sub e1 e2`. Otherwise return `false`.
    Note that `true` is returned only when e is a fully applied `Nat.sub expression.
-/
def isNatSubExpr (e: Expr) : Bool :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.sub _) _) _ => true
  | _ => false


/-- Return `true` if `e := Nat.pow e1 e2`. Otherwise return `false`.
    Note that `true` is returned only when e is a fully applied `Nat.pow expression.
-/
def isNatPowExpr (e : Expr) : Bool :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.pow _) _) _ => true
  | _ => false

/-- Determine if `e` is a `Nat.mul` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[always_inline, inline] def natMul? (e: Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.mul _) op1) op2 => some (op1, op2)
  | _ => none

/-- Determine if `e` is a `Nat.add` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[always_inline, inline] def natAdd? (e: Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.add _) op1) op2 => some (op1, op2)
  | _ => none


/-- Determine if `e` is a `Nat.sub` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[always_inline, inline] def natSub? (e: Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.sub _) op1) op2 => some (op1, op2)
  | _ => none


/-- Determine if `e` is a `Nat.pow` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[always_inline, inline] def natPow? (e: Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.pow _) op1) op2 => some (op1, op2)
  | _ => none


/-- Return `some (f, op1, op2)` when `e` is a binary operator. Otherwise `none`. -/
@[always_inline, inline] def binOp? (e : Expr) : Option (Expr × Expr × Expr) :=
  match e with
  | Expr.app (Expr.app f op1) op2 =>
       if f.isApp then none
       else some (f, op1, op2)
  | _ => none

/-- Determine if `e` is an Int.neg expression and return its corresponding argument.
    Otherwise return `none`.
-/
@[always_inline, inline] def intNeg? (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.const ``Int.neg _) n => some n
  | _ => none

/-- Determine if `e` is a `Int.add` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[always_inline, inline] def intAdd? (e: Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Int.add _) op1) op2 => some (op1, op2)
  | _ => none

/-- Determine if `e` is a `Int.mul` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[always_inline, inline] def intMul? (e: Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Int.mul _) op1) op2 => some (op1, op2)
  | _ => none


/-- Determine if `e` is a `Int.tdiv` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[always_inline, inline] def intTDiv? (e: Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Int.tdiv _) op1) op2 => some (op1, op2)
  | _ => none

/-- Return `true` when `e1 := -ne ∧ ne =ₚₜᵣ e2`. Otherwise `false`.
 -/
@[always_inline, inline]
def isIntNegExprOf (e1: Expr) (e2 : Expr) : Bool :=
  match intNeg? e1 with
  | some op => exprEq e2 op
  | _ => false

/-- Determine if `e` is a `Blaster.decide'` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[always_inline, inline] def decide'? (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.const ``Blaster.decide' _) op => some op
  | _ => none


/-- Determine if `e` is an `Blaster.ite'` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[always_inline, inline] def ite'? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``Blaster.ite' _) psort) pcond) e1) e2 =>
      some (psort, pcond, e1, e2)
  | _ => none


/-- Determine if `e` is an `Blaster.dite'` expression and return its corresponding arguments.
    Otherwise return `none`.
-/
@[always_inline, inline] def dite'? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``Blaster.dite' _) psort) pcond) e1) e2 =>
      some (psort, pcond, e1, e2)
  | _ => none

/-- Return `true` only when `e := Expr.const ``Blaster.dite' _`
    Otherwise `false`.
-/
@[always_inline, inline]
def isBlasterDiteConst (e : Expr) : Bool :=
  match e with
  | Expr.const ``Blaster.dite' _ => true
  | _ => false

/-- Return `true` only when `e` is a `Int` expression corresponding to one of the following:
     - `Int.ofNat (Expr.lit (Literal.natVal n))`
     - `Int.negSucc (Expr.lit (Literal.natVal n))`
-/
@[always_inline, inline]
def isIntValue (e : Expr) : Bool :=
  match e with
  | Expr.app f a =>
    if isNatValue a then
      match f with
      | Expr.const ``Int.ofNat _
      | Expr.const ``Int.negSucc _ => true
      | _ => false
    else false
  | _ => false

/-- Determine if `e` is a `Int` expression corresponding to one of the following:
     - `Int.ofNat (Expr.lit (Literal.natVal n))`
     - `Int.negSucc (Expr.lit (Literal.natVal n))`
    Return either `some (Int.ofNat n)` or `some (Int.negSucc n)` as result.
    Otherwise return `none`
    NOTE: This function is to be used only when it is guaranteed that
    `Nat.zero` has been normalized to `Expr.lit (Literal.natVal 0)`.
-/
@[always_inline, inline]
def isIntValue? (e : Expr) : Option Int :=
  match e with
  | Expr.app f a =>
    match isNatValue? a with
    | some n =>
        match f with
        | Expr.const ``Int.ofNat _ => Int.ofNat n
        | Expr.const ``Int.negSucc _ => Int.negSucc n
        | _ => none
    | none => none
  | _ => none

/-- Remove `outParam` application if encountered. -/
def removeOutParam : Expr → Expr
 | Expr.app (Expr.const ``outParam _) e => e
 | e => e


/-- Returns all axioms only defined in current module. -/
def findLocalAxioms : MetaM (List Expr) := do
 let env ← getEnv
 (Environment.constants env).toList.filterMapM
    (λ c : Name × ConstantInfo => do
      if !Environment.isImportedConst env c.1
      then
        match c.2 with
        | .axiomInfo info =>
            if wasOriginallyTheorem env c.1 then return none
            if ← isProp (info.type) then
              return some info.type
            else return none
        | _ => return none
      else return none
    )

end Blaster.Optimize
