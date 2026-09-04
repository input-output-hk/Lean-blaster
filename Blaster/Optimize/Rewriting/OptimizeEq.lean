import Lean
import Blaster.Optimize.Hypotheses

open Lean Meta
namespace Blaster.Optimize


/-- Return `true` when `e` corresponds to the zero int literal. -/
@[always_inline, inline]
def isZeroInt (e : Expr) : Bool :=
  match isIntValue? e with
  | some (Int.ofNat 0) => true
  | _ => false

/-- Find an FVar proof of `e ≠ 0` in the optimizer's local context, wrapping the
    hypothesis found (`0 < e`, `e < 0`, or `¬ (0 = e)`) with the matching bridge
    lemma. Assumes `nonZeroIntInHyps e` has returned `true`. -/
def findNeZeroIntProof? (e : Expr) : TranslateEnvT (Option Expr) := do
  match isIntValue? e with
  | .some (Int.ofNat 0) => return none
  | .some _ => return none
  | _ =>
    let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
    let zero_int ← mkIntLitExpr 0
    let zero_lt ← mkIntLtExpr zero_int e
    if let some p := hyps.get? zero_lt then
      return mkApp2 (mkConst ``Blaster.int_ne_zero_of_zero_lt) e p
    let zero_gt ← mkIntLtExpr e zero_int
    if let some p := hyps.get? zero_gt then
      return mkApp2 (mkConst ``Blaster.int_ne_zero_of_lt_zero) e p
    let zero_eq ← mkIntEqExpr zero_int e
    if let some p := hyps.get? (mkApp (← mkPropNotOp) zero_eq) then
      return some (← mkAppM ``Blaster.int_ne_zero_of_not_zero_eq #[p])
    return none

/-- Proof-returning companion to `nonZeroNatInHyps` for a non-literal `e`: when a hypothesis
  entailing `0 ≠ e` (stores as `0 < e` or `0 ≠ e`) is in the context, return its proof; otherwise `none`.
-/
def findNeZeroNatProof? (e : Expr) : TranslateEnvT (Option Expr) := do
  match isNatValue? e with
    | .some 0 => return none
    | .some _ => return none
    | _ =>
      let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
      let zero_nat ← mkNatLitExpr 0
      let zero_lt ← mkNatLtExpr zero_nat e
      if let some p := hyps.get? zero_lt then
        return mkApp2 (mkConst ``Blaster.nat_zero_lt_imp_zero_neq) e p
      let zero_eq ← mkNatEqExpr zero_nat e
      if let some p := hyps.get? (mkApp (← mkPropNotOp) zero_eq) then
        return some (← mkAppM ``Ne.symm #[p])
      return none

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
       return mkApp3 (← mkEqOp) eqType op1 e
  | _, _ => return none

/- Given `op1` and `op2` corresponding to the operands for `Eq`,
    - When `op1 := 0` ∧ `op2 := x * y` ∧ Type(x) = Nat ∧ nonZeroNatInHyps x ∧ nonZeroNatInHyps y:
       - return `some False`
    - Otherwise `none`.
-/
def natZeroEqMulReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
    match isNatValue? op1, natMul? op2 with
  | some 0, some (e1, e2) =>
      if let (some p1 , some p2) :=  (← findNeZeroNatProof? e1, ← findNeZeroNatProof? e2) then
        let conj ← mkAppM ``And.intro #[p1, p2]
        pushProofStep (.rewrite (← mkAppM ``Blaster.nat_mul_eq_false_of_ne #[e1 , e2 , conj]))
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
       if let (some p1, some p2) := (← findNeZeroIntProof? e1, ← findNeZeroIntProof? e2)
       then
          let conj ← mkAppM ``And.intro #[p1, p2]
          pushProofStep (.rewrite (← mkAppM ``Blaster.int_mul_eq_false_of_ne #[e1, e2, conj]))
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
     if exprEq e1 e3 then setRestart return (e2, e4)
     if exprEq e1 e4 then setRestart return (e2, e3)
     if exprEq e2 e3 then setRestart return (e1, e4)
     if exprEq e2 e4 then setRestart return (e1, e3)
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
     if exprEq e1 e3 then setRestart return (e2, e4)
     if exprEq e1 e4 then setRestart return (e2, e3)
     if exprEq e2 e3 then setRestart return (e1, e4)
     if exprEq e2 e4 then setRestart return (e1, e3)
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
     if exprEq e1 e3 then if ← nonZeroNatInHyps e1 then setRestart return (e2, e4)
     if exprEq e1 e4 then if ← nonZeroNatInHyps e1 then setRestart return (e2, e3)
     if exprEq e2 e3 then if ← nonZeroNatInHyps e2 then setRestart return (e1, e4)
     if exprEq e2 e4 then if ← nonZeroNatInHyps e2 then setRestart return (e1, e3)
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
     if exprEq e1 e3 then if ← nonZeroIntInHyps e1 then setRestart return (e2, e4)
     if exprEq e1 e4 then if ← nonZeroIntInHyps e1 then setRestart return (e2, e3)
     if exprEq e2 e3 then if ← nonZeroIntInHyps e2 then setRestart return (e1, e4)
     if exprEq e2 e4 then if ← nonZeroIntInHyps e2 then setRestart return (e1, e3)
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
     return ← mkPropFalse
 | none =>
     if exprEq e1 op2 then if ← nonZeroIntInHyps e2 then return ← mkPropFalse
     if exprEq e2 op2 then if ← nonZeroIntInHyps e1 then return ← mkPropFalse
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
     return ← mkPropFalse
 | none =>
     if exprEq e1 op2 then if ← nonZeroNatInHyps e2 then return ← mkPropFalse
     if exprEq e2 op2 then if ← nonZeroNatInHyps e1 then return ← mkPropFalse
     return none

/-- Given `op1 := 0` and `op2 := x + y`:
      - return `some False` when `nonZeroNatInHyps x ∨ nonZeroNatInHyps y`
    Otherwise `none`.
-/
def addNatEqZeroReduce? (op1 op2 : Expr) : TranslateEnvT (Option Expr) := do
  let some (e1, e2) := natAdd? op2 | return none
  match isNatValue? op1 with
  | some 0 =>
      if let some p ← findNeZeroNatProof? e1 then
        pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.nat_add_eq_false_of_ne_fst) e1 e2 p))
        return ← mkPropFalse
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
     if n1 < n2 then return ← mkPropFalse
     setRestart -- restart necessary
     mkNatEqExpr (← evalBinNatOp Nat.sub n1 n2) e2
 | _ =>
   let some (p1, p2) := natAdd? op1 | return none
   let some n1 := isNatValue? p1 | return none
   setRestart
   let minValue := min n1 n2
   let leftValue := n1 - minValue
   let rightValue := n2 - minValue
   let op1' := mkApp2 (← mkNatAddOp) (← mkNatLitExpr leftValue) p2
   let op2' := mkApp2 (← mkNatAddOp) (← mkNatLitExpr rightValue) e2
   mkNatEqExpr op1' op2'

/-- Proof-returning companion to `gtZeroIntInHyps` for a non literal `e` :
  when a hypothesis entailing `0 < e` is in the context, otherwise `none`
-/
def gtZeroIntInHypsProof (e : Expr) : TranslateEnvT (Option Expr) := do
  match isIntValue? e with
  | .some (.ofNat 0) => return none
  | .some (.ofNat _) => return none
  | .some _          => return none
  | .none =>
    let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
    let zero_int ← mkIntLitExpr (Int.ofNat 0)
    let zero_lt ← mkIntLtExpr zero_int e
    return hyps.get? zero_lt


/-- Proof-returning companion to `ltZeroIntInHyps` for a non literal `e` :
  when a hypothesis entailing `e < 0` is in the context, otherwise `none`
-/
def ltZeroIntInHypsProof (e : Expr) : TranslateEnvT (Option Expr) := do
  match isIntValue? e with
  | .some (.ofNat 0) => return none
  | .some (.ofNat _) => return none
  | .some _          => return none
  | .none =>
    let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
    let zero_int ← mkIntLitExpr (Int.ofNat 0)
    let lt_zero ← mkIntLtExpr e zero_int
    return hyps.get? lt_zero

/-- Given `op1` and `op2` corresponding to the operands for `Eq`:
      - return `some False` when `gtZeroIntInHyps x ∧ gtZeroIntInHyps y`
      - return `some False` when `ltZeroIntInHyps x ∧ ltZeroIntInHyps y`
    Otherwise `none`.
-/
def addIntEqZeroReduce? (op1 op2 : Expr) : TranslateEnvT (Option Expr) := do
  let some (e1, e2) := intAdd? op2 | return none
  match isIntValue? op1 with
  | some 0 =>
      if let (some p1, some p2) := (← gtZeroIntInHypsProof e1 , ← gtZeroIntInHypsProof e2) then
        let conj ← mkAppM ``And.intro #[p1, p2]
        pushProofStep (.rewrite (← mkAppM ``Blaster.int_add_eq_false_of_gt #[e1, e2, conj]))
        return ← mkPropFalse
      if let (some p1, some p2) := (← ltZeroIntInHypsProof e1 , ← ltZeroIntInHypsProof e2) then
        let conj ← mkAppM ``And.intro #[p1, p2]
        pushProofStep (.rewrite (← mkAppM ``Blaster.int_add_eq_false_of_lt #[e1, e2, conj]))
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
     setRestart -- restart necessary
     mkIntEqExpr (← evalBinIntOp Int.sub n1 n2) e2
 | _ =>
   let some (p1, p2) := intAdd? op1 | return none
   let some n1 := isIntValue? p1 | return none
   setRestart
   let minValue := min n1 n2
   let leftValue := n1 - minValue
   let rightValue := n2 - minValue
   let op1' := mkApp2 (← mkIntAddOp) (← mkIntLitExpr leftValue) p2
   let op2' := mkApp2 (← mkIntAddOp) (← mkIntLitExpr rightValue) e2
   mkIntEqExpr op1' op2'

/-- Apply the following simplification/normalization rules on `Eq` :
     - N + e = e | e = N + e ==> False (if Type(e) ∈ [Nat, Int])
     - a + b = a | a = a + b | b + a = a | a = b + a ==> False (if Type(a) ∈ [Nat, Int] ∧ nonZeroInHyps b)
     - N2 = N1 + a ==> False (if Type(a) = Nat) ∧ N2 < N1)
     - N2 = N1 + a ==> N2 "-" N1 = a (if Type(a) = Nat) if N2 ≥ N1) (restart)
     - N2 = N1 + a ===> N2 "-" N1 = a (if Type(a) = Int) (restart)
     - N1 + a = N2 + b ==> N1 "-" min(N1, N2) + a = N2 "-" min(N1, N2) + b (if Type(a) ∈ [Nat, Int])
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

/-- Apply the following simplification/normalization rules on `Eq` :
     - False = e ==> ¬ e                          [proof: Blaster.false_prop_is_neg]
     - True = e ==> e                             [proof: Blaster.true_prop_is_idem]
     - e = ¬ e ==> False                          [proof: Blaster.eq_neg_is_false]
     - e = not e ==> False                        [proof: Blaster.eq_not_is_false]
     - e1 = e2 ==> True (if e1 =ₚₜᵣ e2)            [proof: eq_self]
     - e1 = e2 ==> False (if structEq? e1 e2 = some false) (NOTE: `some true` case already handled by =ₚₜᵣ)
     - true = not e ==> false = e                 [proof: Blaster.true_eq_not_is_false_eq]
     - false = not e ==> true = e                 [proof: Blaster.false_eq_not_is_true_eq]
     - ¬ e1 = ¬ e2 ==> e1 = e2 (require classical)[proof: Blaster.neg_eq_neg_is_eq]
     - not e1 = not e2 ==> e1 = e2                [proof: Blaster.not_eq_not_is_eq]
     - 0 = (-e) ==> 0 = e (if Type(e) = Int)      [proof: Blaster.zero_eq_int]
     - -e1 = -e2 ==> e1 = e2 (if Type(e1) = Int)  [proof: Blaster.int_neg_eq]
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
 if args.size != 3 then return mkAppN f args
 -- args[0] is sort parameter
 -- args[1] left operand
 -- args[2] right operand
 let op1 := args[1]!
 let op2 := args[2]!
 let eqType := args[0]!
 if let Expr.const ``False _ := op1 then
    pushProofStep (.rewrite (mkConst ``Blaster.false_prop_is_neg))
    setRestart
    return mkApp (← mkPropNotOp) op2
 if let Expr.const ``True _ := op1 then
  pushProofStep (.rewrite (mkConst ``Blaster.true_prop_is_idem))
  if let Expr.const ``True _ := op2 then
    pushProofStep (.exact (mkConst ``True.intro))
  return op2
 if isNotExprOf op2 op1 then
  pushProofStep (.rewrite (mkConst ``Blaster.eq_neg_is_false))
  return ← mkPropFalse
 if isBoolNotExprOf op2 op1 then
  pushProofStep (.rewrite (mkConst ``Blaster.eq_not_is_false))
  return ← mkPropFalse
 if exprEq op1 op2 then
  let lvl ← mkFreshLevelMVar
  pushProofStep (.rewrite (mkConst ``eq_self [lvl]))
  pushProofStep (.exact (mkConst ``True.intro))
  return ← mkPropTrue
 if let some false ← structEq? op1 op2 then
   try
     let notEq ← mkDecideProof (mkApp (mkConst ``Not) (← mkEq op1 op2))
     pushProofStep (.rewrite (← mkAppM ``eq_false #[notEq]))
   catch _ => pure ()
   return ← mkPropFalse
 if let some (e1, e2) ← notNegEqSimp? op1 op2 then return mkApp3 f eqType e1 e2
 if let some r ← zeroEqNegReduce? op1 op2 eqType then
  pushProofStep (.rewrite (mkConst ``Blaster.zero_eq_int))
  return r
 if let some (e1, e2) ← intNegEqReduce? op1 op2 then
  pushProofStep (.rewrite (mkConst ``Blaster.int_neg_eq))
  return mkApp3 f eqType e1 e2
 if let some r ← natZeroEqMulReduce? op1 op2 then return r
 if let some r ← intZeroEqMulReduce? op1 op2 then return r
 if let some r ← addNatEqZeroReduce? op1 op2 then return r
 if let some r ← addIntEqZeroReduce? op1 op2 then return r
 if let some r ← arithEq? op1 op2 then return r
 if let some (e1, e2) ← natAddEqReduce? op1 op2 then return mkApp3 f eqType e1 e2
 if let some (e1, e2) ← intAddEqReduce? op1 op2 then return mkApp3 f eqType e1 e2
 if let some (e1, e2) ← natMulEqReduce? op1 op2 then return mkApp3 f eqType e1 e2
 if let some (e1, e2) ← intMulEqReduce? op1 op2 then return mkApp3 f eqType e1 e2
 -- no caching at this level as optimizeEq is called by optimizeDecideEq
 return mkApp3 f eqType op1 op2

 where
   /- Given `op1` and `op2` corresponding to the operands for `Eq`,
       - When `op1 := -x` ∧ `op2 := -y ∧ Type(x) = Int`:
          - return `some (x, y)`
       - Otherwise `none`.
   -/
   intNegEqReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option (Expr × Expr)) := do
     match intNeg? op1, intNeg? op2 with
     | some e1, some e2 =>
          setRestart
          return (some (e1, e2))
     | _, _ => return none

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
     - false == e ==> not e
     - true == e ==> e
     - e == not e ==> false
     - e1 == e2 ==> true (if e1 =ₚₜᵣ e2)
     - e1 = e2 ==> false (if structEq? e1 e2 = some false) (NOTE: `some true` case already handled by =ₚₜᵣ)
     - not e1 == not e2 ==> e1 == e2
     - e1 == e2 ==> e2 == e1 (if e2 <ₒ e1)

   Assume that f = Expr.const ``BEq.beq.
   This function simply returns the function application when:
     - `BEq.beq is partially applied (i.e., args.size < 4)
     - isOpaqueRelational f.constName args is not satisfied.

   NOTE: The above simplification rules are applied only on `BEq.beq` satisfiying `isOpaqueRelational` predicate.
   In fact, we can't assume that `BEq.beq` will properly be defined for user-defined types or parametric inductive types.

   NOTE: `BEq.beq` is expected to be unfolded if isOpaqueRelational predicate is not satisfied.
   However, class constraint [BEq α] for which there is no defined instance the unfolding will not be performed
   (see `getUnfoldFunDef?`).

   TODO: consider additional simplification rules
-/
def optimizeBEq (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
 if !(← isOpaqueRelational f.constName args) then return mkAppN f args
 if args.size != 4 then return mkAppN f args
 -- args[0] is sort parameter
 -- args[1] decidable instance parameter
 -- args[2] left operand
 -- args[3] right operand
 let op1 := args[2]!
 let op2 := args[3]!
 if let Expr.const ``false _ :=  op1 then
   setRestart
   return mkApp (← mkBoolNotOp) op2
 if let Expr.const ``true _ := op1 then return op2
 if isBoolNotExprOf op2 op1 then return (←  mkBoolFalse)
 if exprEq op1 op2 then return (← mkBoolTrue)
 if let some false ← structEq? op1 op2 then return (← mkBoolFalse)
 if let some r ← boolNotEqReduce? op1 op2 then return r
 return (mkApp4 f args[0]! args[1]! op1 op2)

 where
   /-- Given `op1` and `op2` corresponding to the operands for `BEq.beq`,
       return `some e1 == e2` when `op1 := not e1` ∧ `op2 := not e2`.
       Otherwise none.
   -/
   boolNotEqReduce? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
     match boolNot? op1, boolNot? op2 with
     | some e1, some e2 =>
          setRestart
          return mkApp4 f args[0]! args[1]! e1 e2
     | _, _ => return none

/- Call `optimizeEq f args` and apply the following `decide'` simplification/normalization
   rules on the resulting `Eq` expression (if any):
     - true = (a == b) ==> a = b (if hasLawFulBEqInstance (a == b))
     - false = (a == b) ==> ¬ (a = b) (if hasLawFulBEqInstance (a == b))
     - c = (a == b) | (a == b) = c ==> (true = c) = (a = b) (if hasLawFulBEqInstance (a == b))
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

   mkBeqToEq (beq_sort : Expr) (beq_op1 : Expr) (beq_op2 : Expr) (c : Expr) : TranslateEnvT Expr := do
      setRestart
      let op1Expr := mkApp3 f (← mkBoolType) (← mkBoolTrue) c
      let op2Expr := mkApp3 f beq_sort beq_op1 beq_op2
      return mkApp3 f (← mkPropType) op1Expr op2Expr


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
          let eqExpr := mkApp3 f beq_sort beq_op1 beq_op2
          setRestart
          if bv
          then return some eqExpr -- return when bv = true
          else return mkApp (← mkPropNotOp) eqExpr
      | _ => return none
    | none =>
       match (← isBeqCompatibleType? op1), (← isBeqCompatibleType? op2) with
         | some (beq_sort, _, beq_op1, beq_op2), _ =>
             mkBeqToEq beq_sort beq_op1 beq_op2 op2
         | _, some (beq_sort, _, beq_op1, beq_op2) =>
             mkBeqToEq beq_sort beq_op1 beq_op2 op1
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
           return mkApp3 f eq_sort (← toBoolNotExpr bv1 a_op2) (← toBoolNotExpr bv2 b_op2)
       | _, _ => return none
    | _, _ => return none

   /- Given `op1` and `op2` corresponding to the operands for `Eq`,
       - return `some e` when `op1 := true ∧ op2 := decide e`
       - return `some ¬ e` when `op1 := false ∧ op2 := decide e`
      Otherwise `none`.
   -/
   decideBoolEqSimp? (op1: Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
    match op1, decide'? op2 with
    | Expr.const ``true _, some e => return some e -- no need to restart
    | Expr.const ``false _, some e =>
         setRestart
         return mkApp (← mkPropNotOp) e
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
          return mkApp3 f (← mkPropType) e1 e2
     | some e1, _ =>
          setRestart
          return mkApp3 f (← mkPropType) e1 (mkApp3 f (← mkBoolType) (← mkBoolTrue) op2)
     | _, some e1 =>
          setRestart
          return mkApp3 f (← mkPropType) e1 (mkApp3 f (← mkBoolType) (← mkBoolTrue) op1)
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
