import Lean
import Blaster.Optimize.Rewriting.OptimizeEq
import Blaster.Optimize.Rewriting.OptimizeNat
import Blaster.Optimize.Rewriting.Utils
import Blaster.Optimize.Env

open Lean Meta
namespace Blaster.Optimize

theorem int_add_neg_add (a b c : Int) : a + -(b + c) = (a - b) + -c := by omega

/-- Apply the following simplification/normalization rules on `Int.neg` :
     - - (N) ==> "-" N
     - - (- n) ==> n      [proof: Int.neg_neg]
   Assume that f = Expr.const ``Int.neg.
   An error is triggered if args.size ≠ 1 (i.e., only fully applied `Int.neg` expected at this stage)
   TODO: consider additional simplification rules
-/
def optimizeIntNeg (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 1 then throwEnvError "optimizeIntNeg: only one argument expected"
 let op := args[0]!
 if let some n1 := isIntValue? op then return (← mkIntLitExpr (Int.neg n1))
 if let some e := intNeg? op then
  pushProofStep (.rewrite (mkConst ``Int.neg_neg))
  return e
 return (mkApp f op)


/-- Apply the following simplification/normalization rules on `Int.add` :
     - 0 + n ==> n                          [proof: Int.zero_add]
     - N1 + N2 ==> N1 "+" N2
     - N1 + (N2 + n) ==> (N1 "+" N2) + n    [proof: ← Int.add_assoc]
     - N1 + -(N2 + n) ==> (N1 "-" N2) + -n  [proof: int_add_neg_add]
     - n1 + (-n2) ==> 0 if (if n1 =ₚₜᵣ n2)
     - n1 + n2 ==> n2 + n1 (if n2 <ₒ n1)    [proof: Int.add_comm, see reorderOperands]
   Assume that f = Expr.const ``Int.add.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Int.add` expected at this stage)

-/
def optimizeIntAdd (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeIntAdd: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 -- let op1 := opArgs[0]!
 -- let op2 := opArgs[1]!
 match isIntValue? op1, isIntValue? op2 with
 | some (Int.ofNat 0), _ =>
  pushProofStep (.rewrite (mkConst ``Int.zero_add))
  return op2
 | some n1, some n2 => evalBinIntOp Int.add n1 n2
 | nv1, _ =>
   if let some r ← cstAddProp? nv1 op1 op2 then return r
   if isIntNegExprOf op2 op1 then return (← mkIntLitExpr (Int.ofNat 0))
   return (mkApp2 f op1 op2)

 where
  /- Given `mv1`, `op1` and `op2`,
      - return `some ((N1 "+" N2) + n)` when `mv1 := some N1 ∧ op2 := (N2 + n)`
      - return `some ((N1 "-" N2) + -n)` when `mv1 := some N1 ∧ op2 := -(N2 + n)`
     Otherwise `none`
  -/
 @[always_inline, inline]
 cstAddProp? (mv1 : Option Int) (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
  match mv1 with
  | some n1 =>
     match (toIntCstOpExpr? op2) with
     | some (IntCstOpInfo.IntAddExpr n2 e2) =>
         -- `op2 := Int.add N2 n`, so `op2.appFn!.appArg!` is the `N2` operand.
         let n2Expr := op2.appFn!.appArg!
         pushProofStep (.rewrite (mkApp3 (mkConst ``Int.add_assoc) op1 n2Expr e2) (symm := true))
         setRestart
         return mkApp2 f (← evalBinIntOp Int.add n1 n2) e2
     | some (IntCstOpInfo.IntNegAddExpr n2 e2) =>
         -- `op2 := Int.neg (Int.add N2 n)`, so `op2.appArg!.appFn!.appArg!` is `N2`.
         let n2Expr := op2.appArg!.appFn!.appArg!
         pushProofStep (.rewrite (mkApp3 (mkConst ``int_add_neg_add) op1 n2Expr e2))
         setRestart
         return mkApp2 f (← evalBinIntOp Int.sub n1 n2) (mkApp (← mkIntNegOp) e2)
     | _ => return none
  | none => return none

/-- Apply the following simplification/normalization rules on `Int.mul` :
     - 0 * n ==> 0                          [proof: Int.zero_mul]
     - 1 * n ==> n                          [proof: Int.one_mul]
     - -1 * n ==> -n                        [proof: Int.neg_one_mul]
     - N1 * N2 ==> N1 "*" N2
     - N1 * (N2 * n) ==> (N1 "*" N2) * n    [proof: ← Int.mul_assoc]
     - n1 * n2 ==> n2 * n1 (if n2 <ₒ n1)    [proof: Int.mul_comm, see reorderOperands]
   Assume that f = Expr.const ``Int.mul.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Int.mul` expected at this stage)
-/
def optimizeIntMul (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeIntMul: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 match isIntValue? op1, isIntValue? op2 with
 | some (Int.ofNat 0), _ =>
  pushProofStep (.rewrite (mkConst ``Int.zero_mul))
  return op1
 | some (Int.ofNat 1), _ =>
  pushProofStep (.rewrite (mkConst ``Int.one_mul))
  return op2
 | some (Int.negSucc 0), _ =>
      pushProofStep (.rewrite (mkConst ``Int.neg_one_mul))
      setRestart
      return mkApp (← mkIntNegOp) op2
 | some n1, some n2 => evalBinIntOp Int.mul n1 n2
 | nv1, _ =>
   if let some r ← cstMulProp? nv1 op1 op2 then return r
   return (mkApp2 f op1 op2)

 where
   /- Given `mv1`, `op1` and `op2` return `some ((N1 "*" N2) * n)` when
      `mv1 := some N1 ∧ op2 := (N2 * n)`. Otherwise `none`
   -/
   @[always_inline, inline]
   cstMulProp? (mv1 : Option Int) (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
    match mv1, toIntCstOpExpr? op2 with
    | some n1, some (IntCstOpInfo.IntMulExpr n2 e2) =>
       -- `op2 := Int.mul N2 n`, so `op2.appFn!.appArg!` is the `N2` operand.
       let n2Expr := op2.appFn!.appArg!
       pushProofStep (.rewrite (mkApp3 (mkConst ``Int.mul_assoc) op1 n2Expr e2) (symm := true))
       return (mkApp2 f (← evalBinIntOp Int.mul n1 n2) e2)
    | _, _ => return none

/-- Given `e1` and `e2` corresponding to the operands for `Int.ediv`, `Int.tdiv` and `Int.fdiv`,
    return `some 1` only when the following conditions are satisfied:
      - e1 =ₚₜᵣ e2 ∧
      - 0 < e1 := _ ∈ hypothesisContext.hypothesisMap ∨
        e1 < 0 := _ ∈ hypothesisContext.hypothesisMap ∨
        ¬ (0 = e1) := _ ∈ hypothesisContext.hypothesisMap
    Otherwise, return none.
-/
@[always_inline, inline]
def intDivSelfReduce? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
  if !(exprEq e1 e2) then return none
  if (← nonZeroIntInHyps e1)
  then return ← mkIntLitExpr (Int.ofNat 1)
  else return none

/-- Given `e1` and `e2` corresponding to the operands for `Int.ediv`, `Int.tdiv` and `Int.fdiv`,
    return `some n` only when one of the following conditions is satisfied:
     - `e1 := m * n` ∧ e2 = m ∧
       ( 0 < m := _ ∈ hypothesisContext.hypothesisMap ∨
         m < 0 := _ ∈ hypothesisContext.hypothesisMap ∨
         ¬ (0 = m) := _ ∈ hypothesisContext.hypothesisMap ); or
     - `e1 := n * m` ∧ e2 = m ∧
        ( 0 < m := _ ∈ hypothesisContext.hypothesisMap ∨
          m < 0 := _ ∈ hypothesisContext.hypothesisMap ∨
          ¬ (0 = m) := _ ∈ hypothesisContext.hypothesisMap );
    Otherwise, return none.
-/
@[always_inline, inline]
def mulIntDivReduceExpr? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
  match intMul? e1 with
  | some (op1, op2) =>
     if exprEq op1 e2 then if (← nonZeroIntInHyps e2) then return some op2
     if exprEq op2 e2 then if (← nonZeroIntInHyps e2) then return some op1
     return none
  | none => return none

/--
  Data type to distinguish between the three integer division operators:
   - `Int.ediv`
   - `Int.tdiv`
   - `Int.fdiv`
-/
inductive DivKind where
  | ediv
  | tdiv
  | fdiv

/-- Given `op1` and `op2` corresponding to the operands for `Int.ediv`, `Int.tdiv` and `Int.fdiv`,
    try to apply the following simplification rules:
     - n / 0 ==> 0
     - n / 1 ==> n
     - 0 / n ==> 0
     - N1 / N2 ==> N1 "/" N2
     - n / n ==> 1
         (if 0 < n := _ ∈ hypothesisContext.hypothesisMap ∨
             ¬ (0 = n) := _ ∈ hypothesisContext.hypothesisMap ∨
             n < 0 := _ ∈ hypothesisContext.hypothesisMap )
     - (m * n) / m | (n * m) / m ==> n
          (if  0 < m := _ ∈ hypothesisContext.hypothesisMap ∨
               ¬ (0 = m) := _ ∈ hypothesisContext.hypothesisMap ∨
               m < 0 := _ ∈ hypothesisContext.hypothesisMap)
-/
@[always_inline, inline]
def optimizeIntDivCommon (d: DivKind) (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 match isIntValue? op1, isIntValue? op2 with
 | _, some (Int.ofNat 0) =>
  match d with
  | DivKind.ediv => pushProofStep (.rewrite (mkConst ``Int.ediv_zero))
  | DivKind.tdiv => pushProofStep (.rewrite (mkConst ``Int.tdiv_zero))
  | DivKind.fdiv => pushProofStep (.rewrite (mkConst ``Int.fdiv_zero))
  return op2
 | _, some (Int.ofNat 1) =>
  match d with
  | DivKind.ediv => pushProofStep (.rewrite (mkConst ``Int.ediv_one))
  | DivKind.tdiv => pushProofStep (.rewrite (mkConst ``Int.tdiv_one))
  | DivKind.fdiv => pushProofStep (.rewrite (mkConst ``Int.fdiv_one))
  return op1
 | some (Int.ofNat 0), _ =>
  match d with
  | DivKind.ediv => pushProofStep (.rewrite (mkConst ``Int.zero_ediv))
  | DivKind.tdiv => pushProofStep (.rewrite (mkConst ``Int.zero_tdiv))
  | DivKind.fdiv => pushProofStep (.rewrite (mkConst ``Int.zero_fdiv))
  return op1
 | some n1, some n2 => evalBinIntOp Int.ediv n1 n2
 | _, _ =>
   if let some r ← intDivSelfReduce? op1 op2 then return r
   if let some r ← mulIntDivReduceExpr? op1 op2 then return r
   return none

/- Given `op1` and `op2` corresponding to the operands for `Int.ediv`, `Int.tdiv` and `Int.fdiv`,
   and `f_div` the corresponding divisor operator,
     - return `some (((f_div N1 (Int.gcd N1 N2)) * n), (f_div N2 (Int.gcd N1 N2)))`
       when `op1 := (N1 * n) ∧ op2 := N2 ∧ Int.gcd N1 N2 ≠ 1
   Otherwise `none`.
   Assumes that N2 ≠ 0
-/
@[always_inline, inline]
def cstCommonDivProp?
  (op1 : Expr) (op2 : Expr) (f_div : Int -> Int -> Int) : TranslateEnvT (Option (Expr × Expr)) := do
 let some (n, e1) := intMul? op1 | return none
 match isIntValue? n, isIntValue? op2 with
 | some n1, some n2 =>
    let gcd := Int.gcd n1 n2
    if gcd == 1 then return none
    setRestart
    let mulExpr := mkApp2 (← mkIntMulOp) (← evalBinIntOp f_div n1 gcd) e1
    return (mulExpr, (← evalBinIntOp f_div n2 gcd))
 | _, _ => return none


/-- Apply the following simplification/normalization rules on `Int.ediv`:
     - n / 0 ==> 0                                              [proof: Int.ediv_zero]
     - n / 1 ==> n                                              [proof: Int.ediv_one]
     - 0 / n ==> 0                                              [proof: Int.zero_ediv]
     - N1 / N2 ==> N1 "/ₑ" N2
     - n / n ==> 1
         (if 0 < n := _ ∈ hypothesisContext.hypothesisMap ∨
             ¬ (0 = n) := _ ∈ hypothesisContext.hypothesisMap ∨
             n < 0 := _ ∈ hypothesisContext.hypothesisMap )
     - (m * n) / m | (n * m) / m ==> n
         (if  0 < m := _ ∈ hypothesisContext.hypothesisMap ∨
              ¬ (0 = m) := _ ∈ hypothesisContext.hypothesisMap ∨
              m < 0 := _ ∈ hypothesisContext.hypothesisMap)
     - (N1 * n) / N2 ===> ((N1 "/" Int.gcd N1 N2) * n) / (N2 "/ₑ" Int.gcd N1 N2) (if N2 ≠ 0 ∧ Int.gcd N1 N2 ≠ 1)
   Assume that f = Expr.const ``Int.ediv.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Int.ediv` expected at this stage)
-/
def optimizeIntEDiv (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeIntEDiv: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 if let some r ← optimizeIntDivCommon DivKind.ediv op1 op2 then return r
 if let some (op1', op2') ← cstCommonDivProp? op1 op2 Int.ediv then return mkApp2 f op1' op2'
 return (mkApp2 f op1 op2)

/-- Given `e1` and `e2` corresponding to the operands for `Int.emod`, `Int.fmod` and `Int.tmod`,
    return `some 0` only when one of the following conditions is satisfied:
     - e1 =ₚₜᵣ e2; or
     - `e1 := m * n` ∧ e2 = m; or
     - `e1 := n * m` ∧ e2 = m;
    Otherwise, return none.
-/
@[always_inline, inline]
def intModToZeroExpr? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
  if exprEq e1 e2 then return (some (← mkIntLitExpr (Int.ofNat 0)))
  match intMul? e1 with
  | some (op1, op2) =>
     if exprEq op1 e2 || exprEq op2 e2 then return (← mkIntLitExpr (Int.ofNat 0))
     return none
  | none => return none


/-- Data type for distinguishing between the three integer modulo operators:
   - `Int.emod`
   - `Int.tmod`
   - `Int.fmod`
-/
inductive ModKind where
  | emod
  | tmod
  | fmod

/--  Given `op1` and `op2` corresponding to the operands for `Int.emod`, `Int.fmod` and `Int.tmod`,
     try to apply the following simplification rules:
     - n % 0 ==> n
     - n % 1 ==> 0
     - 0 % n ==> 0
     - N1 % N2 ==> N1 "%" N2
     - (N1 * n) % N2 ==> 0 (if N1 % N2 = 0)
     - n1 % n2 ==> 0 (if n1 =ₚₜᵣ n2)
     - (m * n) % m | (n * m) % m ==> 0
-/
@[always_inline, inline]
def optimizeIntModCommon (m : ModKind) (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 match isIntValue? op1, isIntValue? op2 with
 | _, some (Int.ofNat 0) =>
  match m with
  | ModKind.emod => pushProofStep (.rewrite (mkConst ``Int.emod_zero))
  | ModKind.tmod => pushProofStep (.rewrite (mkConst ``Int.tmod_zero))
  | ModKind.fmod => pushProofStep (.rewrite (mkConst ``Int.fmod_zero))
  return op1
 | _, some (Int.ofNat 1) =>
  match m with
  | ModKind.emod => pushProofStep (.rewrite (mkConst ``Int.emod_one))
  | ModKind.tmod => pushProofStep (.rewrite (mkConst ``Int.tmod_one))
  | ModKind.fmod => pushProofStep (.rewrite (mkConst ``Int.fmod_one))
  mkIntLitExpr (Int.ofNat 0)
 | some (Int.ofNat 0), _ =>
  match m with
  | ModKind.emod => pushProofStep (.rewrite (mkConst ``Int.zero_emod))
  | ModKind.tmod => pushProofStep (.rewrite (mkConst ``Int.zero_tmod))
  | ModKind.fmod => pushProofStep (.rewrite (mkConst ``Int.zero_fmod))
  return op1
 | some n1, some n2 => evalBinIntOp Int.emod n1 n2
 | _, nv2 =>
   if let some r ← cstModProp? op1 nv2 then return r
   if let some r ← intModToZeroExpr? op1 op2 then return r
   return none

 where
   /- Given `op1` and `mv2`, return `some 0`
      when `op1 := N1 * n ∧ mv2 := N2 ∧ N1 % N2 = 0`
      Otherwise `none`.
      Assumes that N2 > 0
   -/
   @[always_inline, inline]
   cstModProp? (op1 : Expr) (mv2 : Option Int) : TranslateEnvT (Option Expr) := do
   let some (n, _e1) := intMul? op1 | return none
    match isIntValue? n, mv2 with
    | some n1, some n2 =>
        if Int.emod n1 n2 == 0
        then return (← mkIntLitExpr (Int.ofNat 0))
        else return none
    | _, _ => return none

/-- Apply the following simplification/normalization rules on `Int.emod` :
     - n % 0 ==> n                            [proof: Int.emod_zero]
     - n % 1 ==> 0                            [proof: Int.emod_one]
     - 0 % n ==> 0                            [proof: Int.zero_emod]
     - N1 % N2 ==> N1 "%" N2
     - (N1 * n) % N2 ==> 0 (if N1 % N2 = 0)
     - n1 % n2 ==> 0 (if n1 =ₚₜᵣ n2)
     - (m * n) % m | (n * m) % m ==> 0
   Assume that f = Expr.const ``Int.emod.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Int.emod` expected at this stage)
-/

def optimizeIntEMod (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeIntEMod: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 if let some r ← optimizeIntModCommon ModKind.emod op1 op2 then return r
 return (mkApp2 f op1 op2)

/-- Apply the following simplification/normalization rules on `Int.tdiv`:
     - n / 0 ==> 0                                              [proof: Int.tdiv_zero]
     - n / 1 ==> n                                              [proof: Int.tdiv_one]
     - 0 / n ==> 0                                              [proof: Int.zero_tdiv]
     - N1 / N2 ==> N1 "/" N2
     - n / n ==> 1
         (if 0 < n := _ ∈ hypothesisContext.hypothesisMap ∨
             ¬ (0 = n) := _ ∈ hypothesisContext.hypothesisMap ∨
             n < 0 := _ ∈ hypothesisContext.hypothesisMap )
     - (m * n) / m | (n * m) / m ==> n
         (if  0 < m := _ ∈ hypothesisContext.hypothesisMap ∨
              ¬ (0 = m) := _ ∈ hypothesisContext.hypothesisMap ∨
              m < 0 := _ ∈ hypothesisContext.hypothesisMap)
     - (n / N1) / N2 ==> n / (N1 "*" N2) (only valid for Int.tdiv)
     - (N1 * n) / N2 ===> ((N1 "/" Int.gcd N1 N2) * n) / (N2 "/" Int.gcd N1 N2) (if N2 ≠ 0 ∧ Int.gcd N1 N2 ≠ 1)
   Assume that f = Expr.const ``Int.tdiv.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Int.tdiv` expected at this stage)
-/
def optimizeIntTDiv (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeIntTDiv: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 if let some r ← optimizeIntDivCommon DivKind.tdiv op1 op2 then return r
 if let some r ← cstTDivProp? op1 op2 then return r
 if let some (op1', op2') ← cstCommonDivProp? op1 op2 Int.tdiv then return mkApp2 f op1' op2'
 else return (mkApp2 f op1 op2)

 where
   /- Given `op1` and `op2` corresponding to the operands for Int.tdiv,
       - return `some (n /ₑ (N1 "*" N2))` when `op1 := (n /ₑ N1) ∧ op2 := N2`
      Otherwise `none`.
      Assumes that N2 ≠ 0
   -/
   @[always_inline, inline]
   cstTDivProp? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
     let some (e1, n) := intTDiv? op1 | return none
     match isIntValue? n, isIntValue? op2 with
     | some n1, some n2 => return (mkApp2 f e1 (← evalBinIntOp Int.mul n1 n2))
     | _, _ => return none

/-- Apply the following simplification/normalization rules on `Int.tmod` :
     - n % 0 ==> n              [proof: Int.tmod_zero]
     - n % 1 ==> 0              [proof: Int.tmod_one]
     - 0 % n ==> 0              [proof: Int.zero_tmod]
     - N1 % N2 ==> N1 "%" N2
     - (N1 * n) % N2 ==> 0 (if N1 % N2 = 0)
     - n1 % n2 ==> 0 (if n1 =ₚₜᵣ n2)
     - (m * n) % m | (n * m) % m ==> 0
   Assume that f = Expr.const ``Int.tmod.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Int.tmod` expected at this stage)
-/

def optimizeIntTMod (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeIntTMod: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 if let some r ← optimizeIntModCommon ModKind.tmod op1 op2 then return r
 return (mkApp2 f op1 op2)

/-- Apply the following simplification/normalization rules on `Int.fdiv`:
     - n / 0 ==> 0                                        [proof: Int.fdiv_zero]
     - n / 1 ==> n                                        [proof: Int.fdiv_one]
     - 0 / n ==> 0                                        [proof: Int.zero_fdiv]
     - N1 / N2 ==> N1 "/" N2
     - n / n ==> 1
         (if 0 < n := _ ∈ hypothesisContext.hypothesisMap ∨
             ¬ (0 = n) := _ ∈ hypothesisContext.hypothesisMap ∨
             n < 0 := _ ∈ hypothesisContext.hypothesisMap )
     - (m * n) / m | (n * m) / m ==> n
         (if  0 < m := _ ∈ hypothesisContext.hypothesisMap ∨
              ¬ (0 = m) := _ ∈ hypothesisContext.hypothesisMap ∨
              m < 0 := _ ∈ hypothesisContext.hypothesisMap)
     - (N1 * n) / N2 ===> ((N1 "/" Int.gcd N1 N2) * n) / (N2 "/" Int.gcd N1 N2) (if N2 ≠ 0 ∧ Int.gcd N1 N2 ≠ 1)
   Assume that f = Expr.const ``Int.fdiv.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Int.fdiv` expected at this stage)
-/
def optimizeIntFDiv (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeIntFDiv: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 if let some r ← optimizeIntDivCommon DivKind.fdiv op1 op2 then return r
 if let some (op1', op2') ← cstCommonDivProp? op1 op2 Int.fdiv then return mkApp2 f op1' op2'
 return (mkApp2 f op1 op2)

/-- Apply the following simplification/normalization rules on `Int.fmod` :
     - n % 0 ==> n                          [proof: Int.fmod_zero]
     - n % 1 ==> 0                          [proof: Int.fmod_one]
     - 0 % n ==> 0                          [proof: Int.zero_fmod]
     - N1 % N2 ==> N1 "%" N2
     - (N1 * n) % N2 ==> 0 (if N1 % N2 = 0)
     - n1 % n2 ==> 0 (if n1 =ₚₜᵣ n2)
     - (m * n) % m | (n * m) % m ==> 0
   Assume that f = Expr.const ``Int.fmod.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Int.fmod` expected at this stage)
-/

def optimizeIntFMod (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeIntFMod: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 if let some r ← optimizeIntModCommon ModKind.fmod op1 op2 then return r
 return (mkApp2 f op1 op2)


/-- Return `some e` if `n := Int.neg (Int.ofNat e)`. Otherwise return `none`. -/
@[always_inline, inline]
def intNegOfNat? (n : Expr) : Option Expr :=
  match intNeg? n with
  | some e => e.app1? ``Int.ofNat
  | none => none

/-- Apply the following simplification rules on `Int.toNat` :
     - Int.toNat N1 ===> "Int.toNat" N1
     - Int.toNat (Int.ofNat e) ===> e
     - Int.toNat (Int.neg (Int.ofNat e)) ===> 0
   Assume that f = Expr.const ``Int.toNat.
   An error is triggered if args.size ≠ 1.
-/
def optimizeIntToNat (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 1 then throwEnvError "optimizeIntToNat: only one argument expected"
 let op := args[0]!
 if let some n := isIntValue? op then return (← mkNatLitExpr (Int.toNat n))
 if let some e := op.app1? ``Int.ofNat then return e
 if let some .. := intNegOfNat? op then return (← mkNatLitExpr 0)
 return (mkApp f op)

/-- Normalize `Int.negSucc n` to `Int.neg (Int.ofNat (1 + n))` only when `n` is not a constant value.
    An error is triggered if args.size ≠ 1.
    Assume that f = Expr.const ``Int.negSucc.
    NOTE: This rule is still required here to avoid normalizationg Int.negSucc when `n`
    is a constant value.
--/
def optimizeIntNegSucc (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 1 then throwEnvError "optimizeIntNegSucc: only one argument expected"
 let op := args[0]!
 if isNatValue op then return (mkApp f op)
 setRestart
 let addExpr := mkApp2 (← mkNatAddOp) (← mkNatLitExpr 1) args[0]!
 let intExpr := mkApp (← mkIntOfNat) addExpr
 return mkApp (← mkIntNegOp) intExpr

/-- Apply simplification/normalization rules on `Int` operators.
-/
@[always_inline, inline]
def optimizeInt? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n _ := f | return none
  match n with
  | ``Int.add => optimizeIntAdd f args
  | ``Int.mul => optimizeIntMul f args
  | ``Int.neg => optimizeIntNeg f args
  | ``Int.negSucc => optimizeIntNegSucc f args
  | ``Int.toNat => optimizeIntToNat f args
  | ``Int.ediv => optimizeIntEDiv f args
  | ``Int.emod => optimizeIntEMod f args
  | ``Int.tdiv => optimizeIntTDiv f args
  | ``Int.tmod => optimizeIntTMod f args
  | ``Int.fdiv => optimizeIntFDiv f args
  | ``Int.fmod => optimizeIntFMod f args
  | _=> return none

end Blaster.Optimize
