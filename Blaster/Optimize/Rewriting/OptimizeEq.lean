import Lean
import Blaster.Optimize.Hypotheses
import Blaster.Optimize.Lemmas.LemmasDecide

open Lean Meta
namespace Blaster.Optimize

/-- Proof of the ground decidable proposition `p` from its `Decidable` instance `inst`:
    `of_decide_eq_true p inst rfl` when `b` (a proof of `p`), `of_decide_eq_false p inst rfl`
    otherwise (a proof of `¬ p`). Built raw, so that the optimizer caches stay untouched; the
    kernel evaluates `decide p` at replay. -/
def mkGroundDecideProof (p inst : Expr) (b : Bool) : Expr :=
  let bv := mkConst (if b then ``Bool.true else ``Bool.false)
  mkApp3 (mkConst (if b then ``of_decide_eq_true else ``of_decide_eq_false)) p inst
    (mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) bv)

/-- Push the step `(a = b) = (b = a)` (`propext eq_comm`) for `a b : ty`, with `ty : Type`. -/
def pushEqCommStep (ty a b : Expr) : TranslateEnvT Unit := do
  let eq := mkConst ``Eq [levelOne]
  pushProofStep (.rewrite (mkApp3 (mkConst ``propext) (mkApp3 eq ty a b) (mkApp3 eq ty b a)
    (mkApp3 (mkConst ``eq_comm [levelOne]) ty a b)))

/-- Proof returning companion to `nonZeroIntInHyps` for a non-literal `e`: when an hypothesis entailing
    `0 ≠ e` (stored as `0 < e`, `e < 0`, or `¬ (0 = e)`) is in the context, returns its proof;
    for a non-zero literal `N` returns a decide proof of `0 ≠ N`;
    otherwise none.
    The hypothesis keys are built as `nonZeroIntInHyps` builds them, so that they are the
    hash-consed terms the hypothesis map is keyed on.
-/
def findNeZeroIntProof? (e : Expr) : TranslateEnvT (Option Expr) := do
  match isIntValue? e with
  | .some (Int.ofNat 0) => return none
  | .some _ =>
    let zero := mkApp (mkConst ``Int.ofNat) (mkRawNatLit 0)
    let int := mkConst ``Int
    return mkGroundDecideProof (mkApp3 (mkConst ``Eq [levelOne]) int zero e)
      (mkApp2 (mkConst ``Int.instDecidableEq) zero e) false
  | _ =>
    let zero_int ← mkIntLitExpr 0
    let zero_lt ← mkIntLtExpr zero_int e
    if let some p ← hypMapFind? zero_lt then
      return mkApp2 (mkConst ``Blaster.int_not_zero_eq_of_zero_lt) e p
    let zero_gt ← mkIntLtExpr e zero_int
    if let some p ← hypMapFind? zero_gt then
      return mkApp2 (mkConst ``Blaster.int_not_zero_eq_of_lt_zero) e p
    let zero_eq ← mkIntEqExpr zero_int e
    hypMapFind? (← mkAppExpr (← mkPropNotOp) zero_eq)

/-- Proof-returning companion to `nonZeroNatInHyps` for a non-literal `e`: when a hypothesis
  entailing `0 ≠ e` (stored as `0 < e` or `0 ≠ e`) is in the context, return its proof;
  for a non-zero literal `N` returns a decide proof of `0 ≠ N`;
  otherwise `none`.
  The hypothesis keys are built as `nonZeroNatInHyps` builds them, so that they are the
  hash-consed terms the hypothesis map is keyed on.
-/
def findNeZeroNatProof? (e : Expr) : TranslateEnvT (Option Expr) := do
  match isNatValue? e with
    | .some 0 => return none
    | .some _ =>
      let zero := mkRawNatLit 0
      return mkGroundDecideProof (mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Nat) zero e)
        (mkApp2 (mkConst ``instDecidableEqNat) zero e) false
    | _ =>
      let zero_nat ← mkNatLitExpr 0
      let zero_lt ← mkNatLtExpr zero_nat e
      if let some p ← hypMapFind? zero_lt then
        return mkApp2 (mkConst ``Blaster.nat_not_zero_eq_of_zero_lt) e p
      let zero_eq ← mkNatEqExpr zero_nat e
      hypMapFind? (← mkAppExpr (← mkPropNotOp) zero_eq)

/-- Push `lemma x y z p`, with `p` the proof of `¬ (0 = x)` given by `findNeZero`
    (`findNeZeroNatProof?` or `findNeZeroIntProof?`). -/
def pushNeZeroStep (findNeZero : Expr → TranslateEnvT (Option Expr)) (lemma : Name) (x y z : Expr) :
    TranslateEnvT Unit := do
  if let some p ← findNeZero x then
    pushProofStep (.rewrite (mkApp4 (mkConst lemma) x y z p))

/-- Return `some true` if op1 and op2 are constructors that are structurally equivalent modulo
    variable name/function equivalence
    Return `some false` if op1 and op2 are constructors that are NOT structurally equivalent.
    Return `none` otherwise.
    Assume that memoization is performed on expressions.
-/
partial def structEq? (op1 : Expr) (op2: Expr) : TranslateEnvT (Option Bool) := do
 let rec visit (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Bool) := do
   match op1, op2 with
    | Expr.lit _, Expr.lit _ => return exprEq op1 op2
    | Expr.const n1 _, Expr.const n2 _ =>
       if (← (isCtorName n1) <&&> (isCtorName n2))
       then return exprEq op1 op2
       else return none -- function case not structurally equivalent
    | Expr.app .., Expr.app .. =>
        Expr.withApp op1 fun f1 as1 =>
         Expr.withApp op2 fun f2 as2 => do
          -- recursive call on visit instead of structEq? to properly handle case
          -- when f1 and f2 are fun calls with different arguments.
          -- Case when f1 and f2 are equal is handled when first calling structEq? (e.g., f x = f x)
          match (← visit f1 f2) with
          | some b =>
              if b && as1.size == as2.size then
                -- lattice to handle arguments
                -- some false -> some none -> some true
                let mut lat := some true
                for h : i in [:as1.size] do
                  lat := updateLattice lat (← structEq? as1[i] as2[i]!)
                  unless (!isTop lat) do return lat -- break if false
                return lat
              else return false
          | none => return none
     | Expr.app .., Expr.const ..
     | Expr.const .., Expr.app .. => visit op1.getAppFn' op2.getAppFn'
     | _, _ =>
       -- return `none` for all other cases if physically equality fails
       pure none
 if exprEq op1 op2 then return true
 visit op1 op2

 where
   /-- update the lattice for application arguments such that:
        - some true corresponds to the bottom element
        - some false corresponds to the top element (the identity element)
        - some none the middle element
       The join rules applied on update are the following:
        - some true, some false ==> some false
        - none, some false ==> some false
        - some false, some false ==> some false
        - some true, none ==> none
        - none, none ==> none
        - some true, some true ==> some true

   -/
   updateLattice : Option Bool -> Option Bool -> Option Bool
     | some false, _ | _, some false => some false
     | none, _ | _, none => none
     | some true, some true => some true

   isTop : Option Bool -> Bool
    | some false => true
    | _ => false

/- Given `op1` and `op2` corresponding to the operands for `Eq`,
    - When `op1 := 0` ∧ `op2 := -x ∧ Type(x) = Int`:
       - return `some 0 = x`
    - Otherwise `none`.
-/
def zeroEqNegReduce? (op1 : Expr) (op2 : Expr) (eqType : Expr) : TranslateEnvT (Option Expr) := do
  match isIntValue? op1, intNeg? op2 with
  | some 0, some e =>
       setRestart
       mkApp3Expr (← mkEqOp) eqType op1 e
  | _, _ => return none

/- Given `op1` and `op2` corresponding to the operands for `Eq`,
    - When `op1 := 0` ∧ `op2 := x * y` ∧ Type(x) = Nat ∧ nonZeroNatInHyps x ∧ nonZeroNatInHyps y:
       - return `some False`
    - Otherwise `none`.
-/
def natZeroEqMulReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
  match isNatValue? op1, natMul? op2 with
  | some 0, some (e1, e2) =>
       if (← nonZeroNatInHyps e1 <&&> nonZeroNatInHyps e2)
       then
         if let some p1 ← findNeZeroNatProof? e1 then
           if let some p2 ← findNeZeroNatProof? e2 then
             pushProofStep (.rewrite (mkApp4 (mkConst ``Blaster.nat_mul_eq_false_of_ne) e1 e2 p1 p2))
         mkPropFalse
       else return none
  | _, _ => return none

/- Given `op1` and `op2` corresponding to the operands for `Eq`,
    - When `op1 := 0` ∧ `op2 := x * y` ∧ Type(x) = Int ∧ nonZeroIntInHyps x ∧ nonZeroIntInHyps y:
       - return `some False`
    - Otherwise `none`.
-/
def intZeroEqMulReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
  match isIntValue? op1, intMul? op2 with
  | some 0, some (e1, e2) =>
       if (← nonZeroIntInHyps e1 <&&> nonZeroIntInHyps e2)
       then
         if let some p1 ← findNeZeroIntProof? e1 then
           if let some p2 ← findNeZeroIntProof? e2 then
             pushProofStep (.rewrite (mkApp4 (mkConst ``Blaster.int_mul_eq_false_of_ne) e1 e2 p1 p2))
         mkPropFalse
       else return none
  | _, _ => return none

/- Given `op1` and `op2` corresponding to the operands for `Eq` and `Type(op1) = Nat`,
    - When (op1 := x + y ∧ op2 := x + z) ∨
           (op1 := y + x ∧ op2 := x + z) ∨
           (op1 := x + y ∧ op2 := z + x) ∨
           (op1 := y + x ∧ op2 := z + x)
        - return `some (y, z)`
    - Otherwise
        - return `none`
-/
def natAddEqReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option (Expr × Expr)) := do
  match natAdd? op1, natAdd? op2 with
  | some (e1, e2), some (e3, e4) =>
     if exprEq e1 e3 then
      pushProofStep (.rewrite (mkConst ``Blaster.nat_add_eq_add_rgt))
      setRestart
      return (e2, e4)
     if exprEq e1 e4 then
      pushProofStep (.rewrite (mkConst ``Blaster.nat_add_eq_add_lft))
      setRestart
      return (e2, e3)
     if exprEq e2 e3 then
      pushProofStep (.rewrite (mkConst ``Blaster.nat_add_lft_eq_add))
      setRestart
      return (e1, e4)
     if exprEq e2 e4 then
      pushProofStep (.rewrite (mkConst ``Blaster.nat_add_lft_eq_add_lft))
      setRestart
      return (e1, e3)
     return none
  | _, _ => return none

/- Given `op1` and `op2` corresponding to the operands for `Eq` and `Type(op1) = Int`,
    - When (op1 := x + y ∧ op2 := x + z) ∨
           (op1 := y + x ∧ op2 := x + z) ∨
           (op1 := x + y ∧ op2 := z + x) ∨
           (op1 := y + x ∧ op2 := z + x)
        - return `some (y, z)`
    - Otherwise
        - return `none`
-/
def intAddEqReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option (Expr × Expr)) := do
  match intAdd? op1, intAdd? op2 with
  | some (e1, e2), some (e3, e4) =>
     if exprEq e1 e3 then
      pushProofStep (.rewrite (mkConst ``Blaster.int_add_eq_add_rgt))
      setRestart
      return (e2, e4)
     if exprEq e1 e4 then
      pushProofStep (.rewrite (mkConst ``Blaster.int_add_eq_add_lft))
      setRestart
      return (e2, e3)
     if exprEq e2 e3 then
      pushProofStep (.rewrite (mkConst ``Blaster.int_add_lft_eq_add))
      setRestart
      return (e1, e4)
     if exprEq e2 e4 then
      pushProofStep (.rewrite (mkConst ``Blaster.int_add_lft_eq_add_lft))
      setRestart
      return (e1, e3)
     return none
  | _, _ => return none


/- Given `op1` and `op2` corresponding to the operands for `Eq` and `Type(op1) = Nat`,
    - When ( (op1 := x * y ∧ op2 := x * z) ∨
             (op1 := x * y ∧ op2 := z * x) ∨
             (op1 := y * x ∧ op2 := x * z) ∨
             (op1 := y * x ∧ op2 := z * x) )
           ∧ nonZeroNatInHyps x
        - return `some (y, z)`
    - Otherwise
        - return `none`
-/
def natMulEqReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option (Expr × Expr)) := do
  match natMul? op1, natMul? op2 with
  | some (e1, e2), some (e3, e4) =>
     if exprEq e1 e3 then
      if ← nonZeroNatInHyps e1 then
        pushNeZeroStep findNeZeroNatProof? ``Blaster.nat_mul_eq_mul_rgt e1 e2 e4
        setRestart
        return (e2, e4)
     if exprEq e1 e4 then
      if ← nonZeroNatInHyps e1 then
        pushNeZeroStep findNeZeroNatProof? ``Blaster.nat_mul_eq_mul_lft e1 e2 e3
        setRestart
        return (e2, e3)
     if exprEq e2 e3 then
      if ← nonZeroNatInHyps e2 then
        pushNeZeroStep findNeZeroNatProof? ``Blaster.nat_mul_lft_eq_mul e2 e1 e4
        setRestart
        return (e1, e4)
     if exprEq e2 e4 then
      if ← nonZeroNatInHyps e2 then
        pushNeZeroStep findNeZeroNatProof? ``Blaster.nat_mul_lft_eq_mul_lft e2 e1 e3
        setRestart
        return (e1, e3)
     return none
  | _, _ => return none


/- Given `op1` and `op2` corresponding to the operands for `Eq` and `Type(op1) = Int`,
    - When ( (op1 := x * y ∧ op2 := x * z) ∨
             (op1 := x * y ∧ op2 := z * x) ∨
             (op1 := y * x ∧ op2 := x * z) ∨
             (op1 := y * x ∧ op2 := z * x) )
           ∧ nonZeroIntInHyps x
        - return `some (y, z)`
    - Otherwise
        - return `none`
-/
def intMulEqReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option (Expr × Expr)) := do
  match intMul? op1, intMul? op2 with
  | some (e1, e2), some (e3, e4) =>
     if exprEq e1 e3 then
      if ← nonZeroIntInHyps e1 then
        pushNeZeroStep findNeZeroIntProof? ``Blaster.int_mul_eq_mul_rgt e1 e2 e4
        setRestart
        return (e2, e4)
     if exprEq e1 e4 then
      if ← nonZeroIntInHyps e1 then
        pushNeZeroStep findNeZeroIntProof? ``Blaster.int_mul_eq_mul_lft e1 e2 e3
        setRestart
        return (e2, e3)
     if exprEq e2 e3 then
      if ← nonZeroIntInHyps e2 then
        pushNeZeroStep findNeZeroIntProof? ``Blaster.int_mul_lft_eq_mul e2 e1 e4
        setRestart
        return (e1, e4)
     if exprEq e2 e4 then
      if ← nonZeroIntInHyps e2 then
        pushNeZeroStep findNeZeroIntProof? ``Blaster.int_mul_lft_eq_mul_lft e2 e1 e3
        setRestart
        return (e1, e3)
     return none
  | _, _ => return none

/-- Given `op1` and `op2` corresponding to the operands for `Eq`:
      - return `some False` when `op1 := N + e ∧ op2 := e ∧ N ≠ 0 ∧ Type(N) = Int`
      - return `some False` when `op1 := a + b ∧ op2 := a ∧ Type(a) = Int ∧ nonZeroIntInHyps b`
      - return `some False` when `op1 := b + a ∧ op2 := a ∧ Type(a) = Int ∧ nonZeroIntInHyps b`
    Otherwise `none`.
-/
def intEqReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := intAdd? op1 | return none
 match isIntValue? e1 with
 | some n =>
     if n == 0 then return none
     if !(exprEq e2 op2) then return none
     if let some hNe ← findNeZeroIntProof? e1 then
       pushEqCommStep (mkConst ``Int) op2 op1
       pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.int_add_left_eq_false) e2 e1 hNe))
     return ← mkPropFalse
 | none =>
     if exprEq e1 op2 then
      if ← nonZeroIntInHyps e2 then
        if let some p ← findNeZeroIntProof? e2 then
          pushEqCommStep (mkConst ``Int) op2 op1
          pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.int_add_right_eq_false) e1 e2 p))
        return ← mkPropFalse
     if exprEq e2 op2 then
      if ← nonZeroIntInHyps e1 then
        if let some p ← findNeZeroIntProof? e1 then
          pushEqCommStep (mkConst ``Int) op2 op1
          pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.int_add_left_eq_false) e2 e1 p))
        return ← mkPropFalse
     return none

/-- Given `op1` and `op2` corresponding to the operands for `Eq`:
      - return `some False` when `op1 := N + e ∧ op2 := e ∧ N ≠ 0 ∧ Type(N) = Nat`
      - return `some False` when `op1 := a + b ∧ op2 := a ∧ Type(a) = Nat ∧ nonZeroNatInHyps b`
      - return `some False` when `op1 := b + a ∧ op2 := a ∧ Type(a) = Nat ∧ nonZeroNatInHyps b`
    Otherwise `none`.
-/
def natEqReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := natAdd? op1 | return none
 match isNatValue? e1 with
 | some n =>
     if n == 0 then return none
     if !(exprEq e2 op2) then return none
     if let some hNe ← findNeZeroNatProof? e1 then
       pushEqCommStep (mkConst ``Nat) op2 op1
       pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.nat_add_left_eq_false) e2 e1 hNe))
     return ← mkPropFalse
 | none =>
     if exprEq e1 op2 then
      if ← nonZeroNatInHyps e2 then
        if let some p ← findNeZeroNatProof? e2 then
          pushEqCommStep (mkConst ``Nat) op2 op1
          pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.nat_add_right_eq_false) e1 e2 p))
        return ← mkPropFalse
     if exprEq e2 op2 then
      if ← nonZeroNatInHyps e1 then
        if let some p ← findNeZeroNatProof? e1 then
          pushEqCommStep (mkConst ``Nat) op2 op1
          pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.nat_add_left_eq_false) e2 e1 p))
        return ← mkPropFalse
     return none

/-- Given `op1` and `op2` corresponding to the operands for `Eq`
      - return `some False` when `op1 := 0` ∧ op2 := x + y ∧ nonZeroNatInHyps x ∨ nonZeroNatInHyps y`
    Otherwise `none`.
-/
def addNatEqZeroReduce? (op1 op2 : Expr) : TranslateEnvT (Option Expr) := do
  let some (e1, e2) := natAdd? op2 | return none
  match isNatValue? op1 with
  | some 0 =>
      if ← nonZeroNatInHyps e1 then
        if let some p ← findNeZeroNatProof? e1 then
          pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.nat_add_eq_false_of_ne_fst) e1 e2 p))
        return ← mkPropFalse
      if ← nonZeroNatInHyps e2 then
        if let some p ← findNeZeroNatProof? e2 then
          pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.nat_add_eq_false_of_ne_snd) e1 e2 p))
        return ← mkPropFalse
      return none
  | _ => return none

/-- Given `op1` and `op2` corresponding to the operands for `Eq`:
      - return `some False` when `op1 := N1 ∧ op2 := N2 + a ∧ N1 < N2 ∧ Type(a) = Nat`:
      - return `some N1 "-" N2 = a` when `op1 := N1 ∧ op2 := N2 + a ∧ N1 ≥ N2 ∧ Type(a) = Nat`:
      - return `some N1 "-" min(N1, N2) + a = N2 "-" min(N1, N2) + b`
               when `op1 := N1 + a ∧ op2 := N2 + b ∧ Type(a) = Nat`:
   Otherwise `none`.
-/
def addNatEqReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := natAdd? op2 | return none
 let some n2 := isNatValue? e1 | return none
 match isNatValue? op1 with
 | some n1 =>
     let nat := mkConst ``Nat
     if n1 < n2 then
      let hLt := mkGroundDecideProof (mkApp4 (mkConst ``LT.lt [levelZero]) nat (mkConst ``instLTNat) op1 e1)
        (mkApp2 (mkConst ``Nat.decLt) op1 e1) true
      pushProofStep (.rewrite (mkApp4 (mkConst ``Blaster.nat_eq_add_false_if_lt) e1 op1 e2 hLt))
      return ← mkPropFalse
     let hGe := mkGroundDecideProof (mkApp4 (mkConst ``LE.le [levelZero]) nat (mkConst ``instLENat) e1 op1)
       (mkApp2 (mkConst ``Nat.decLe) e1 op1) true
     pushProofStep (.rewrite (mkApp4 (mkConst ``Blaster.nat_sub_eq_from_ge_add) op1 e1 e2 hGe))
     setRestart -- restart necessary
     mkNatEqExpr (← evalBinNatOp Nat.sub n1 n2) e2
 | _ =>
   let some (p1, p2) := natAdd? op1 | return none
   let some n1 := isNatValue? p1 | return none
   setRestart
   let minValue := min n1 n2
   let leftValue := n1 - minValue
   let rightValue := n2 - minValue
   let lit1 ← mkNatLitExpr leftValue
   let lit2 ← mkNatLitExpr rightValue
   let op1' ← mkApp2Expr (← mkNatAddOp) lit1 p2
   let op2' ← mkApp2Expr (← mkNatAddOp) lit2 e2
   let refl1 := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Nat) lit1
   let refl2 := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Nat) lit2
   pushProofStep (.rewrite (mkAppN (mkConst ``Blaster.nat_add_with_min)
     #[p1, e1, p2, e2, lit1, lit2, refl1, refl2]))
   mkNatEqExpr op1' op2'

/-- Proof-returning companion to `gtZeroIntInHyps` for a non literal `e`:
  when a hypothesis entailing `0 < e` is in the context;
  for a positive literal `N` returns a decide proof of `0 < N`;
  otherwise `none`.
-/
def gtZeroIntInHypsProof (e : Expr) : TranslateEnvT (Option Expr) := do
  match isIntValue? e with
  | .some (.ofNat 0) => return none
  | .some (.ofNat _) =>
    let zero := mkApp (mkConst ``Int.ofNat) (mkRawNatLit 0)
    return mkGroundDecideProof
      (mkApp4 (mkConst ``LT.lt [levelZero]) (mkConst ``Int) (mkConst ``Int.instLTInt) zero e)
      (mkApp2 (mkConst ``Int.decLt) zero e) true
  | .some _          => return none
  | .none =>
    let zero_int ← mkIntLitExpr (Int.ofNat 0)
    let zero_lt ← mkIntLtExpr zero_int e
    hypMapFind? zero_lt


/-- Proof-returning companion to `ltZeroIntInHyps` for a non literal `e`:
  when a hypothesis entailing `e < 0` is in the context;
  for a negative literal `N` returns a decide proof of `N < 0`;
  otherwise `none`
-/
def ltZeroIntInHypsProof (e : Expr) : TranslateEnvT (Option Expr) := do
  match isIntValue? e with
  | .some (.ofNat 0) => return none
  | .some (.ofNat _) => return none
  | .some _          =>
    let zero := mkApp (mkConst ``Int.ofNat) (mkRawNatLit 0)
    return mkGroundDecideProof
      (mkApp4 (mkConst ``LT.lt [levelZero]) (mkConst ``Int) (mkConst ``Int.instLTInt) e zero)
      (mkApp2 (mkConst ``Int.decLt) e zero) true
  | .none =>
    let zero_int ← mkIntLitExpr (Int.ofNat 0)
    let lt_zero ← mkIntLtExpr e zero_int
    hypMapFind? lt_zero

/-- Given `op1` and `op2` corresponding to the operands for `Eq`:
      - return `some False` when `gtZeroIntInHyps x ∧ gtZeroIntInHyps y`
      - return `some False` when `ltZeroIntInHyps x ∧ ltZeroIntInHyps y`
    Otherwise `none`.
-/
def addIntEqZeroReduce? (op1 op2 : Expr) : TranslateEnvT (Option Expr) := do
  let some (e1, e2) := intAdd? op2 | return none
  match isIntValue? op1 with
  | some 0 =>
      if (← gtZeroIntInHyps e1 <&&> gtZeroIntInHyps e2) then
        if let some p1 ← gtZeroIntInHypsProof e1 then
          if let some p2 ← gtZeroIntInHypsProof e2 then
            pushProofStep (.rewrite (mkApp4 (mkConst ``Blaster.int_add_eq_false_of_gt) e1 e2 p1 p2))
        return ← mkPropFalse
      if (← ltZeroIntInHyps e1 <&&> ltZeroIntInHyps e2) then
        if let some p1 ← ltZeroIntInHypsProof e1 then
          if let some p2 ← ltZeroIntInHypsProof e2 then
            pushProofStep (.rewrite (mkApp4 (mkConst ``Blaster.int_add_eq_false_of_lt) e1 e2 p1 p2))
        return ← mkPropFalse
      return none
  | _ => return none


/-- Given `op1` and `op2` corresponding to the operands for `Eq`:
      - return `some N1 "-" N2 = a` when `op1 := N1 ∧ op2 := N2 + a ∧ Type(a) = Int`:
      - return `some N1 "-" min(N1, N2) + a = N2 "-" min(N1, N2) + b`
               when `op1 := N1 + a ∧ op2 := N2 + b ∧ Type(a) = Int`:
    Otherwise `none`.
-/
def addIntEqReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 let some (e1, e2) := intAdd? op2 | return none
 let some n2 := isIntValue? e1 | return none
 match isIntValue? op1 with
 | some n1 =>
     let m ← evalBinIntOp Int.sub n1 n2
     let refl := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Int) m
     pushProofStep (.rewrite (mkAppN (mkConst ``Blaster.int_sub_of_eq_add) #[op1, e1, e2, m, refl]))
     setRestart -- restart necessary
     mkIntEqExpr m e2
 | _ =>
   let some (p1, p2) := intAdd? op1 | return none
   let some n1 := isIntValue? p1 | return none
   setRestart
   let minValue := min n1 n2
   let leftValue := n1 - minValue
   let rightValue := n2 - minValue
   let lit1 ← mkIntLitExpr leftValue
   let lit2 ← mkIntLitExpr rightValue
   let op1' ← mkApp2Expr (← mkIntAddOp) lit1 p2
   let op2' ← mkApp2Expr (← mkIntAddOp) lit2 e2
   let refl1 := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Int) lit1
   let refl2 := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Int) lit2
   pushProofStep (.rewrite (mkAppN (mkConst ``Blaster.int_add_with_min)
    #[p1, e1, p2, e2, lit1, lit2, refl1, refl2]))
   mkIntEqExpr op1' op2'

/-- Apply the following simplification/normalization rules on `Eq` :
     - N + e = e | e = N + e ==> False (if Type(e) ∈ [Nat, Int]) [proof:
                                                                    Blaster.nat_add_left_eq_false,
                                                                    Blaster.int_add_left_eq_false
                                                                  ]
     - a + b = a | a = a + b | b + a = a | a = b + a ==> False (if Type(a) ∈ [Nat, Int] ∧ nonZeroInHyps b) [proof:
                                                                                                              Blaster.nat_add_left_eq_false,
                                                                                                              Blaster.nat_add_right_eq_false,
                                                                                                              Blaster.int_add_left_eq_false,
                                                                                                              Blaster.int_add_right_eq_false
                                                                                                            ]
     - N2 = N1 + a ==> False (if Type(a) = Nat) ∧ N2 < N1)                    [proof: Blaster.nat_eq_add_false_if_lt]
     - N2 = N1 + a ==> N2 "-" N1 = a (if Type(a) = Nat) if N2 ≥ N1) (restart) [proof: Blaster.nat_sub_eq_from_ge_add]
     - N2 = N1 + a ===> N2 "-" N1 = a (if Type(a) = Int) (restart)            [proof: Blaster.int_sub_of_eq_add]
     - N1 + a = N2 + b ==> N1 "-" min(N1, N2) + a = N2 "-" min(N1, N2) + b (if Type(a) ∈ [Nat, Int]) [proof:
                                                                                                        Blaster.nat_add_with_min,
                                                                                                        Blaster.int_add_with_min
                                                                                                      ]
     with:
       nonZeroInHyps x := nonZeroNatInHyps x If Type(x) = Nat
                       := nonZeroIntInHyps x Otherwise
-/
def arithEq? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
  if let some r ← intEqReduce? op1 op2 then return r
  if let some r ← intEqReduce? op2 op1 then return r
  if let some r ← natEqReduce? op1 op2 then return r
  if let some r ← natEqReduce? op2 op1 then return r
  if let some r ← addNatEqReduce? op1 op2 then return r
  if let some r ← addIntEqReduce? op1 op2 then return r
  return none

/-- Try to prove `op1 = op2 → False`, assuming `structEq? op1 op2 = some false`.
    Descend through constructor fields towards a mismatch that `noConfusion` can carry, in a loop
    so that deep terms do not exhaust the stack. Return `none` when the descent finds no such
    mismatch. It runs `MetaM` inference on the optimizer's terms, so call it under
    `withLocalContext`. -/
def structNeProof? (op1 op2 : Expr) : TranslateEnvT (Option Expr) := do
  let mut a := op1
  let mut b := op2
  -- Constructor applications crossed by the descent, with their mismatching fields.
  let mut frames : Array (Expr × Expr × Expr × Expr) := #[]
  repeat
    if exprEq a b then return none
    match a, b with
    | .lit (.natVal n1), .lit (.natVal n2) =>
        if n1 == n2 then return none
        return ← fold frames (litNe (mkConst ``Nat) (mkConst ``instDecidableEqNat) a b)
    | .lit (.strVal s1), .lit (.strVal s2) =>
        if s1 == s2 then return none
        return ← fold frames (litNe (mkConst ``String) (mkConst ``instDecidableEqString) a b)
    | _, _ =>
      let some (c1, as1) ← ctorApp? a | return none
      let some (c2, as2) ← ctorApp? b | return none
      if c1.name != c2.name then return ← fold frames (← ctorNe a b)
      if as1.size == c1.numParams then return none
      -- Take the first mismatching field that is not a proof, since `noConfusion` omits proofs.
      -- Otherwise take the last field, which keeps lists linear but may not be a mismatch.
      let mut i := as1.size - 1
      for j in [c1.numParams:as1.size - 1] do
        if (← structEq? as1[j]! as2[j]!) == some false then
          unless ← isProp (← inferType as1[j]!) do
            i := j
            break
      frames := frames.push (a, b, as1[i]!, as2[i]!)
      a := as1[i]!
      b := as2[i]!
  return none
 where
   /-- Inductives in `Prop` have no `noConfusion`, so `mkNoConfusion` would build a term the
       kernel rejects. -/
   ctorApp? (e : Expr) : MetaM (Option (ConstructorVal × Array Expr)) := do
     let some (ci, as) ← constructorApp? e | return none
     unless (← getEnv).contains (ci.induct.str "noConfusion") do return none
     return some (ci, as)

   /-- Proof of `¬ a = b` for distinct literals. Built raw so that the optimizer caches stay
       untouched. -/
   litNe (ty inst a b : Expr) : Expr :=
     mkGroundDecideProof (mkApp3 (mkConst ``Eq [levelOne]) ty a b) (mkApp2 inst a b) false

   /-- Proof of `a = b → False` for distinct constructors. -/
   ctorNe (a b : Expr) : MetaM Expr := do
     withLocalDeclD `h (← mkEq a b) fun h => do
       mkLambdaFVars #[h] (← mkNoConfusion (mkConst ``False) h)

   /-- `fun q h => nc (fun premises => q e)` lifting `q : fa = fb → False` to `a = b → False`,
       with `fa`, `fb` fields of `a`, `b`. -/
   fieldNe (a b fa fb : Expr) : MetaM (Option Expr) := do
     withLocalDeclD `q (← mkArrow (← mkEq fa fb) (mkConst ``False)) fun q => do
       withLocalDeclD `h (← mkEq a b) fun h => do
         let nc ← mkNoConfusion (mkConst ``False) h
         -- `nc : (premises → False) → False`. Premises are found by type since `noConfusion`
         -- omits `Prop` fields.
         let .forallE _ k _ _ ← whnf (← inferType nc) | return none
         let pk? ← forallTelescopeReducing k fun es _ => do
           for e in es do
             let ty ← inferType e
             if let some (_, x, y) := ty.eq? then
               if x == fa && y == fb then
                 return some (← mkLambdaFVars es (mkApp q e))
             if let some (α, x, β, y) := ty.heq? then
               if α == β && x == fa && y == fb then
                 let e' := mkApp4 (mkConst ``eq_of_heq ty.getAppFn.constLevels!) α x y e
                 return some (← mkLambdaFVars es (mkApp q e'))
           return none
         let some pk := pk? | return none
         return some (← mkLambdaFVars #[q, h] (mkApp nc pk))

   /-- Fold the frames from the innermost outwards. Each frame is applied to the inner proof
       without beta reduction, so that the inner proof is neither traversed again nor nested
       under the binders of the frame, which keeps the proof size linear. -/
   fold (frames : Array (Expr × Expr × Expr × Expr)) (leaf : Expr) : MetaM (Option Expr) := do
     let mut p := leaf
     for (a, b, fa, fb) in frames.reverse do
       let some f ← fieldNe a b fa fb | return none
       p := mkApp f p
     return some p

/-- Apply the following simplification/normalization rules on `Eq` :
     - False = e ==> ¬ e                          [proof: Blaster.false_prop_is_neg]
     - True = e ==> e                             [proof: Blaster.true_prop_is_idem]
     - e = ¬ e ==> False                          [proof: Blaster.eq_neg_is_false]
     - e = not e ==> False                        [proof: Blaster.eq_not_is_false]
     - e1 = e2 ==> True (if e1 =ₚₜᵣ e2)            [proof: eq_self]
     - e1 = e2 ==> False (if structEq? e1 e2 = some false) (NOTE: `some true` case already handled by =ₚₜᵣ)
                         [proof: eq_false ∘ structNeProof?]
     - true = not e ==> false = e                 [proof: Blaster.true_eq_not_is_false_eq]
     - false = not e ==> true = e                 [proof: Blaster.false_eq_not_is_true_eq]
     - ¬ e1 = ¬ e2 ==> e1 = e2 (require classical)[proof: Blaster.neg_eq_neg_is_eq]
     - not e1 = not e2 ==> e1 = e2                [proof: Blaster.not_eq_not_is_eq]
     - 0 = (-e) ==> 0 = e (if Type(e) = Int)      [proof: Blaster.zero_eq_int]
     - Int.neg e1 = Int.neg e2 ==> e1 = e2        [proof: Blaster.int_neg_eq]
     - Int.ofNat e1 = Inf.ofNat e2 ==> e1 = e2    [proof: Int.ofNat.injEq]
     - Int.ofNat e1 = Int.neg (Int.ofNat e2) ==> 0 = e1 ∧ 0 = e2 (restart)    [proof: Blaster.int_ofNat_eq_neg_ofNat]
     - Int.negSucc N = Int.neg (Int.ofNat e) ==> (N "+" 1) = e    [proof: Blaster.int_negSucc_eq_neg_ofNat]
     - Int.negSucc N = Int.neg e ==> Int.ofNat (N "+" 1) = e     [proof: Blaster.int_negSucc_eq_neg]
     - 0 = x * y ==> False (if Type(x) ∈ [Nat, Int] ∧ nonZeroInHyps x ∧ nonZeroInHyps y)  [proof: Blaster.nat_mul_eq_false_of_ne, Blaster.int_mul_eq_false_of_ne]
     - 0 = x + y ==> False (if Type (x) = Nat ∧ (nonZeroNatInHyps x ∨ nonZeroNatInHyps y))[proof: Blaster.nat_add_eq_false_of_ne_fst, Blaster.nat_add_eq_false_of_ne_snd]
     - 0 = x + y ==> False (if Type (x) = Int ∧ gtZeroIntInHyps x ∧ gtZeroIntInHyps y)    [proof: Blaster.int_add_eq_false_of_gt]
     - 0 = x + y ==> False (if Type (x) = Int ∧ ltZeroIntInHyps x ∧ ltZeroIntInHyps y)    [proof: Blaster.int_add_eq_false_of_lt]
     - e1 = e2 ==> r (if some r ← arithEq? e1 e2)
     - x + y = x + z | y + x = x + z | x + y = z + x | y + x = z + x ==> y = z (if Type(x) ∈ [Nat, Int]]
     - x * y = x * z | y * x = x * z | x * y = z * x | y * x = z * x ==> y = z (if Type(x) ∈ [Nat, Int] ∧ nonZeroInHyps x]
     - e1 = e2 ==> e2 = e1 (if e2 <ₒ e1)
     with:
       nonZeroInHyps x := nonZeroNatInHyps x If Type(x) = Nat
                       := nonZeroIntInHyps x Otherwise
   Assume that f = Expr.const ``Eq.
   Do nothing if operator is partially applied (i.e., args.size < 3)

   TODO: consider additional simplification rules
   TODO: seperate rewriting that require classical reasoning from others.
   TODO: add an option to activate/deactivate classical simplification (same for optimizeProp).
-/
def optimizeEq (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 if args.size != 3 then return ← mkAppNExpr f args
 -- args[0] is sort parameter
 -- args[1] left operand
 -- args[2] right operand
 let op1 := args[1]!
 let op2 := args[2]!
 let eqType := args[0]!
 if let Expr.const ``False _ := op1 then
    pushProofStep (.rewrite (mkConst ``Blaster.false_prop_is_neg))
    setRestart
    return ← mkAppExpr (← mkPropNotOp) op2
 if let Expr.const ``True _ := op1 then
  pushProofStep (.rewrite (mkConst ``Blaster.true_prop_is_idem))
  if let Expr.const ``True _ := op2 then
    pushProofStep (.exact (mkConst ``True.intro))
  return op2
 if isNotExprOf op2 op1 || isBoolNotExprOf op2 op1 then
  if isNotExprOf op2 op1 then
    pushProofStep (.rewrite (mkConst ``Blaster.eq_neg_is_false))
  else
    pushProofStep (.rewrite (mkConst ``Blaster.eq_not_is_false))
  return ← mkPropFalse
 if exprEq op1 op2 then
  let lvl ← mkFreshLevelMVar
  pushProofStep (.rewrite (mkConst ``eq_self [lvl]))
  pushProofStep (.exact (mkConst ``True.intro))
  return ← mkPropTrue
 if let some false ← structEq? op1 op2 then
   -- Only this operand order: `reorderOperands` already pushed `eq_comm` when it flipped the sides.
   if let some notEq ← withLocalContext (structNeProof? op1 op2) then
     pushProofStep (.rewrite (mkApp2 (mkConst ``eq_false) (mkApp3 (mkConst ``Eq f.constLevels!) eqType op1 op2) notEq))
   return ← mkPropFalse
 if let some (e1, e2) ← notNegEqSimp? op1 op2 then return ← mkApp3Expr f eqType e1 e2
 if let some r ← zeroEqNegReduce? op1 op2 eqType then
  pushProofStep (.rewrite (mkConst ``Blaster.zero_eq_int))
  return r
 if let some r ← intCtorEqReduce? op1 op2 then return r
 if let some r ← natZeroEqMulReduce? op1 op2 then return r
 if let some r ← intZeroEqMulReduce? op1 op2 then return r
 if let some r ← addNatEqZeroReduce? op1 op2 then return r
 if let some r ← addIntEqZeroReduce? op1 op2 then return r
 if let some r ← arithEq? op1 op2 then return r
 if let some (e1, e2) ← natAddEqReduce? op1 op2 then return ← mkApp3Expr f eqType e1 e2
 if let some (e1, e2) ← intAddEqReduce? op1 op2 then return ← mkApp3Expr f eqType e1 e2
 if let some (e1, e2) ← natMulEqReduce? op1 op2 then return ← mkApp3Expr f eqType e1 e2
 if let some (e1, e2) ← intMulEqReduce? op1 op2 then return ← mkApp3Expr f eqType e1 e2
 -- no caching at this level as optimizeEq is called by optimizeDecideEq
 mkApp3Expr f eqType op1 op2

 where
   /- Given `op1` and `op2` corresponding to the operands for `Eq`,
       - When `op1 := Int.neg x` ∧ `op2 := Int.neg y`:
          - return `x = y`
      - When `op1 := Int.ofNat x` ∧ `op2 := Int.ofNat y`:
          - return `x = y`
      - When `op1 := Int.ofNat x` ∧ `op2 := Int.neg (Int.ofNat y)`:
          - return `0 = x ∧ 0 = y`
      - When `op1 := Int.negSucc N` ∧ `op2 := Int.neg (Int.ofNat y)`:
          - return `(N "+" 1) = y`
      - When `op1 := Int.negSucc N` ∧ `op2 := Int.neg y`:
          - return `Int.ofNat (N "+" 1) = y`
      - Otherwise `none`.
      with nonZeroNat e := nonZeroNatInHyps e ∨ (e := N + e' ∧ N ≠ 0)
   -/
   intCtorEqReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
     match op1 with
     | Expr.app (Expr.const ``Int.neg _) e1 =>
         let Expr.app (Expr.const ``Int.neg _) e2 := op2 | return none
         pushProofStep (.rewrite (mkConst ``Blaster.int_neg_eq))
         setRestart
         mkApp3Expr f (← mkIntType) e1 e2
     | Expr.app (Expr.const ``Int.ofNat _) e1 =>
          match op2 with
          | Expr.app (Expr.const ``Int.ofNat _) e2 =>
               pushProofStep (.rewrite (mkApp2 (mkConst ``Int.ofNat.injEq) e1 e2))
               setRestart
               mkApp3Expr f (← mkNatType) e1 e2
          | Expr.app (Expr.const ``Int.neg _) (Expr.app (Expr.const ``Int.ofNat _) e2) =>
               pushProofStep (.rewrite (mkApp2 (mkConst ``Blaster.int_ofNat_eq_neg_ofNat) e1 e2))
               setRestart
               let zeroNat ← mkNatLitExpr 0
               let eq1 ← mkNatEqExpr zeroNat e1
               let eq2 ← mkNatEqExpr zeroNat e2
               mkApp2Expr (← mkPropAndOp) eq1 eq2
          | _ => return none
     | Expr.app (Expr.const ``Int.negSucc _) (Expr.lit (Literal.natVal n)) =>
          let Expr.app (Expr.const ``Int.neg _) e2 := op2 | return none
          setRestart
          -- `m` is the literal `N "+" 1` of the result, `N + 1 = m` holds by evaluation
          let m := mkRawNatLit (n + 1)
          let h := mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Nat) m
          match e2 with
          | Expr.app (Expr.const ``Int.ofNat _) e2' =>
              pushProofStep (.rewrite (mkApp4 (mkConst ``Blaster.int_negSucc_eq_neg_ofNat) op1.appArg! m e2' h))
              mkApp3Expr f (← mkNatType) (← mkNatLitExpr (n + 1)) e2'
          | _ =>
              pushProofStep (.rewrite (mkApp4 (mkConst ``Blaster.int_negSucc_eq_neg) op1.appArg! m e2 h))
              mkApp3Expr f (← mkIntType) (← mkAppExpr (← mkIntOfNat) (← mkNatLitExpr (n + 1))) e2
     | _ => return none

   /- Return `true` when `e` is a non-zero Nat, i.e., `nonZeroNatInHyps e` or `e := N + e'` with `N ≠ 0`. -/
   nonZeroNat (e : Expr) : TranslateEnvT Bool := do
     match natAdd? e with
     | some (Expr.lit (Literal.natVal n), _) => return n != 0 -- condition is always true
     | _ => nonZeroNatInHyps e

   /- Given `op1` and `op2` corresponding to the operands for `Eq`,
      - return `some (false, e)` when `op1 := true ∧ op2 := not e`
      - return `some (true, e)` when `op1 := false ∧ op2 := not e`
      - return `some (e1, e2)` when `op1 := not e1 ∧ op2 := not e2`
      - return `some (e1, e2)` when `op1 := ¬ e1 ∧ op2 := ¬ e2`
      Otherwise `none`.
   -/
   notNegEqSimp? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option (Expr × Expr)) := do
    match op1, boolNot? op2, boolNot? op1 with
    | Expr.const ``true _, some e, _ =>
         pushProofStep (.rewrite (mkConst ``Blaster.true_eq_not_is_false_eq))
         setRestart
         return some (← mkBoolFalse, e)
    | Expr.const ``false _, some e, _ =>
         pushProofStep (.rewrite (mkConst ``Blaster.false_eq_not_is_true_eq))
         setRestart
         return (some (← mkBoolTrue, e))
    | _, some e2, some e1 =>
         pushProofStep (.rewrite (mkConst ``Blaster.not_eq_not_is_eq))
         setRestart
         return (some (e1, e2))
    | _, _, _ =>
      match propNot? op1, propNot? op2 with
      | some e1, some e2 =>
           pushProofStep (.rewrite (mkConst ``Blaster.neg_eq_neg_is_eq))
           setRestart
           return (some (e1, e2))
      | _, _ => return none

/-- Apply the following simplification/normalization rules on `BEq.beq` :
     - false == e ==> not e                       [proof: Bool.false_beq]
     - true == e ==> e                            [proof: Bool.true_beq]
     - e == not e ==> false                       [proof: Bool.beq_not_self]
     - e1 == e2 ==> true (if e1 =ₚₜᵣ e2)            [proof: beq_self_eq_true]
     - e1 == e2 ==> false (if structEq? e1 e2 = some false) (NOTE: `some true` case already handled by =ₚₜᵣ)
                          [proof: Blaster.beq_eq_false_of_not_eq ∘ structNeProof?]
     - not e1 == not e2 ==> e1 == e2              [proof: Blaster.not_beq_not]
     - e1 == e2 ==> e2 == e1 (if e2 <ₒ e1)        [proof: Blaster.beq_comm]

   Assume that f = Expr.const ``BEq.beq.
   This function simply returns the function application when:
     - `BEq.beq is partially applied (i.e., args.size < 4)
     - isOpaqueRelational f.constName args is not satisfied.

   NOTE: The above simplification rules are applied only on `BEq.beq` satisfiying `isOpaqueRelational` predicate.
   In fact, we can't assume that `BEq.beq` will properly be defined for user-defined types or parametric inductive types.

   NOTE: `BEq.beq` is expected to be unfolded if isOpaqueRelational predicate is not satisfied.
   However, unfolding will not be performed for class constraint [BEq α] that does not have a defined instance
   (see `getUnfoldFunDef?`).

   TODO: consider additional simplification rules
-/
def optimizeBEq (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 if !(← isOpaqueRelational f.constName args) then return ← mkAppNExpr f args
 if args.size != 4 then return mkAppN f args
 -- args[0] is sort parameter
 -- args[1] decidable instance parameter
 -- args[2] left operand
 -- args[3] right operand
 let op1 := args[2]!
 let op2 := args[3]!
 if let Expr.const ``false _ :=  op1 then
   pushProofStep (.rewrite (mkApp (mkConst ``Bool.false_beq) op2))
   setRestart
   return ← mkAppExpr (← mkBoolNotOp) op2
 if let Expr.const ``true _ := op1 then
   pushProofStep (.rewrite (mkApp (mkConst ``Bool.true_beq) op2))
   return op2
 if isBoolNotExprOf op2 op1 then
   pushProofStep (.rewrite (mkApp (mkConst ``Bool.beq_not_self) op1))
   return (←  mkBoolFalse)
 if exprEq op1 op2 then
   pushProofStep (.rewrite (mkConst ``beq_self_eq_true f.constLevels!))
   return (← mkBoolTrue)
 if let some false ← structEq? op1 op2 then
   -- Only this operand order: `reorderOperands` already pushed `Blaster.beq_comm` when it flipped the sides.
   if let some notEq ← withLocalContext (structNeProof? op1 op2) then
     pushProofStep (.rewrite
       (mkApp4 (mkConst ``Blaster.beq_eq_false_of_not_eq f.constLevels!) args[0]! op1 op2 notEq))
   return (← mkBoolFalse)
 if let some r ← boolNotEqReduce? op1 op2 then return r
 mkApp4Expr f args[0]! args[1]! op1 op2

 where
   /-- Given `op1` and `op2` corresponding to the operands for `BEq.beq`,
       return `some e1 == e2` when `op1 := not e1` ∧ `op2 := not e2`.
       Otherwise none.
   -/
   boolNotEqReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
     match boolNot? op1, boolNot? op2 with
     | some e1, some e2 =>
          pushProofStep (.rewrite (mkApp2 (mkConst ``Blaster.not_beq_not) e1 e2))
          setRestart
          mkApp4Expr f args[0]! args[1]! e1 e2
     | _, _ => return none

/- Call `optimizeEq f args` and apply the following `decide'` simplification/normalization
   rules on the resulting `Eq` expression (if any):
     - true = (a == b) ==> a = b (if hasLawFulBEqInstance (a == b))         [proof: Blaster.true_eq_beq]
     - false = (a == b) ==> ¬ (a = b) (if hasLawFulBEqInstance (a == b))    [proof: Blaster.false_eq_beq]
     - c = (a == b) | (a == b) = c ==> (true = c) = (a = b) (if hasLawFulBEqInstance (a == b))
                                                     [proof: Blaster.bool_eq_beq, Blaster.beq_eq_bool]
     - (B1 = a) = (B2 = b) ==> NOP(B1, a) = NOP(B2, b)
     - true = decide' e ==> e
     - false = decide' e ==> ¬ e
     - decide' e1 = decide' e2 ==> e1 = e2
     - decide' e1 = e2 | e2 = decide' e1 ===> e1 = (true = e2)

   with NOP(B, e) := e  if B
                  := !e otherwise

   Assume that f := Expr.const ``Eq.

   - TODO: may be we need to reverse the following simplification rules to maximize equivalence
      - true = (a == b) ==> a = b (if hasLawFulBEqInstance (a == b))
      - false = (a == b) ==> ¬ (a = b) (if hasLawFulBEqInstance (a == b))
      - c = (a == b) | (a == b) = c ==> (true = c) = (a = b) (if hasLawFulBEqInstance (a == b))
        This rule will not more be required if the two above rules are reversed.
      - The revering is essential to hanlde example like "EqBoolAndEqBoolUnchanged_7"

-/
def optimizeDecideEq (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 let e ← optimizeEq f args
 let some (_, op1, op2) := eq? e | return e
 if let some r ← beqToEq? op1 op2 then return r
 if let some r ← boolEqtoEq? op1 op2 then return r
 if let some r ← decideBoolEqSimp? op1 op2 then return r
 if let some r ← decideEqDecide? op1 op2 then return r
 return e

 where
   isBeqCompatibleType? (e : Expr) : TranslateEnvT (Option (Expr × Expr × Expr × Expr)) := do
     match beq? e with
     | r@(some (beq_sort, beq_inst, _, _)) =>
         if (← hasLawfulBEqInstance beq_sort beq_inst) then return r else return none
     | _ => return none

   mkBeqToEq (beq_sort : Expr) (beq_op1 : Expr) (beq_op2 : Expr) (c : Expr) (proof : Expr) : TranslateEnvT Expr := do
      setRestart
      pushProofStep (.rewrite (mkApp4 proof beq_sort beq_op1 beq_op2 c))
      let op1Expr ← mkApp3Expr f (← mkBoolType) (← mkBoolTrue) c
      let op2Expr ← mkApp3Expr f beq_sort beq_op1 beq_op2
      mkApp3Expr f (← mkPropType) op1Expr op2Expr


   /- Given `op1` and `op2` corresponding to the operands for `Eq`,
      - return `some (a = b)` when `op1 := true ∧ op2 := a == b ∧ `hasLawFulBEqInstance (a == b)`
      - return `some ¬ (a = b)` when `op1 := false ∧ op2 := a == b ∧ `hasLawFulBEqInstance (a == b)`
      - return `some (true = c) = (a = b)` when `op1 := c ∧ op2 := a == b ∧ `hasLawFulBEqInstance (a == b)`
      - return `some (true = c) = (a = b)` when `op1 := a == b ∧ op2 := c ∧ `hasLawFulBEqInstance (a == b)`
      Otherwise `none`.
   -/
   beqToEq? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
    match isBoolValue? op1 with
    | some bv =>
      match (← isBeqCompatibleType? op2) with
      | some (beq_sort, _, beq_op1, beq_op2) =>
          let eqExpr ← mkApp3Expr f beq_sort beq_op1 beq_op2
          setRestart
          let lemma := if bv then ``Blaster.true_eq_beq else ``Blaster.false_eq_beq
          pushProofStep (.rewrite (mkApp3 (mkConst lemma op2.getAppFn.constLevels!) beq_sort beq_op1 beq_op2))
          if bv
          then return eqExpr -- return when bv = true
          else mkAppExpr (← mkPropNotOp) eqExpr
      | _ => return none
    | none =>
       match (← isBeqCompatibleType? op1), (← isBeqCompatibleType? op2) with
         | some (beq_sort, _, beq_op1, beq_op2), _ =>
             mkBeqToEq beq_sort beq_op1 beq_op2 op2
               (mkConst ``Blaster.beq_eq_bool op1.getAppFn.constLevels!)
         | _, some (beq_sort, _, beq_op1, beq_op2) =>
             mkBeqToEq beq_sort beq_op1 beq_op2 op1
               (mkConst ``Blaster.bool_eq_beq op2.getAppFn.constLevels!)
         | _, _ => return none

   /- Given `op1` and `op2` corresponding to the operands for `Eq`,
      return `some NOP(B1, e1) = NOP(B2, e2)` only when
      `op1 := B1 = e1 ∧ op2 := B2 = e2`.
      Otherwise `none`.
   -/
   boolEqtoEq? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
    match eq? op1, eq? op2 with
    | some (eq_sort, a_op1, a_op2), some (_, b_op1, b_op2) =>
       match isBoolValue? a_op1, isBoolValue? b_op1 with
       | some bv1, some bv2 => do
           setRestart
           let lemma :=
            if bv1 && bv2 then
              ``Blaster.bridge_eq_tt
            else if bv1 then
              ``Blaster.bridge_eq_tf
            else if bv2 then
              ``Blaster.bridge_eq_ft
            else
              ``Blaster.bridge_eq_ff
           pushProofStep (.rewrite (mkApp2 (mkConst lemma) a_op2 b_op2))
           mkApp3Expr f eq_sort (← toBoolNotExpr bv1 a_op2) (← toBoolNotExpr bv2 b_op2)
       | _, _ => return none
    | _, _ => return none

   /- Given `op1` and `op2` corresponding to the operands for `Eq`,
       - return `some e` when `op1 := true ∧ op2 := decide e`
       - return `some ¬ e` when `op1 := false ∧ op2 := decide e`
      Otherwise `none`.
   -/
   decideBoolEqSimp? (op1: Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
    match op1, decide'? op2 with
    | Expr.const ``true _, some e =>
         pushProofStep (.rewrite (mkApp (mkConst ``Blaster.true_eq_decide') e))
         return some e -- no need to restart
    | Expr.const ``false _, some e =>
         setRestart
         pushProofStep (.rewrite (mkApp (mkConst ``Blaster.false_eq_decide') e))
         mkAppExpr (← mkPropNotOp) e
    | _, _ => return none

   /- Given `op1` and `op2` corresponding to the operands for `Eq`,
       - return `some e1 = e2` when `op1 := decide e1 ∧ op2 = decide e2`
       - return `some e1 = (true = e2)` when `op1 := decide e1 ∧ op2 := e2`
       - return `some e1 = (true = e2)` when `op1 := e2 ∧ op2 := decide e1`
      Otherwise `none`.
   -/
   decideEqDecide? (op1: Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
     match decide'? op1, decide'? op2 with
     | some e1, some e2 =>
          setRestart
          pushProofStep (.rewrite (mkApp2 (mkConst ``Blaster.decide'_eq_decide') e1 e2))
          mkApp3Expr f (← mkPropType) e1 e2
     | some e1, _ =>
          setRestart
          pushProofStep (.rewrite (mkApp2 (mkConst ``Blaster.decide'_eq_bool) e1 op2))
          mkApp3Expr f (← mkPropType) e1 (← mkApp3Expr f (← mkBoolType) (← mkBoolTrue) op2)
     | _, some e1 =>
          setRestart
          pushProofStep (.rewrite (mkApp2 (mkConst ``Blaster.bool_eq_decide') e1 op1))
          mkApp3Expr f (← mkPropType) e1 (← mkApp3Expr f (← mkBoolType) (← mkBoolTrue) op1)
     | _, _ => return none


/-- Apply simplification and normalization rules on `Eq` and `BEq.beq` :
-/
def optimizeEquality? (f : Expr) (args: Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n _ := f | return none
  match n with
   | ``Eq => optimizeDecideEq f args
   | ``BEq.beq => optimizeBEq f args
   | _ => pure none

end Blaster.Optimize
