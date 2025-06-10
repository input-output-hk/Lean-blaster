import Lean
import Solver.Optimize.Rewriting.OptimizeEq
import Solver.Optimize.Rewriting.OptimizeNat
import Solver.Optimize.Rewriting.Utils
import Solver.Optimize.Env

open Lean Meta
namespace Solver.Optimize


/-- Apply the following simplification/normalization rules on `Int.neg` :
     - - (N) ==> "-" N
     - - (- n) ==> n
   Assume that f = Expr.const ``Int.neg.
   An error is triggered if args.size ≠ 1 (i.e., only fully applied `Int.neg` expected at this stage)
   TODO: consider additional simplification rules
-/
def optimizeIntNeg (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 1 then throwEnvError "optimizeIntNeg: only one argument expected"
 let op := args[0]!
 if let some n1 := isIntValue? op then return (← mkIntLitExpr (Int.neg n1))
 if let some e := intNeg? op then return e
 mkAppExpr f args


/-- Apply the following simplification/normalization rules on `Int.add` :
     - 0 + n ==> n
     - N1 + N2 ==> N1 "+" N2
     - N1 + (N2 + n) ==> (N1 "+" N2) + n
     - N1 + -(N2 + n) ==> (N1 "-" N2) + -n
     - n1 + (-n2) ==> 0 if (if n1 =ₚₜᵣ n2)
     - n1 + n2 ==> n2 + n1 (if n2 <ₒ n1)
   Assume that f = Expr.const ``Int.add.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Int.add` expected at this stage)

-/
partial def optimizeIntAdd (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeIntAdd: exactly two arguments expected"
 let opArgs ← reorderIntOp args -- error triggered when args.size ≠ 2
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 match isIntValue? op1, isIntValue? op2 with
 | some (Int.ofNat 0), _ => return op2
 | some n1, some n2 => evalBinIntOp Int.add n1 n2
 | nv1, _ =>
   if let some (Int.ofNat 0) := nv1 then return op2
   if let some r ← cstAddProp? nv1 op2 then return r
   if (← isIntNegExprOf op2 op1) then return (← mkIntLitExpr (Int.ofNat 0))
   mkExpr (mkApp2 f op1 op2)

 where
  /- Given `mv1` and `op2`,
      - return `some ((N1 "+" N2) + n)` when `mv1 := some N1 ∧ op2 := (N2 + n)`
      - return `some ((N1 "-" N2) + -n)` when `mv1 := some N1 ∧ op2 := -(N2 + n)`
     Otherwise `none`
  -/
 cstAddProp? (mv1 : Option Int) (op2 : Expr) : TranslateEnvT (Option Expr) := do
  match mv1 with
  | some n1 =>
     match (toIntCstOpExpr? op2) with
     | some (IntCstOpInfo.IntAddExpr n2 e2) =>
         some <$> optimizeIntAdd f #[(← evalBinIntOp Int.add n1 n2), e2]
     | some (IntCstOpInfo.IntNegAddExpr n2 e2) =>
         some <$> optimizeIntAdd f #[(← evalBinIntOp Int.sub n1 n2), (← optimizeIntNeg (← mkIntNegOp) #[e2])]
     | _ => return none
  | none => return none

/-- Apply the following simplification/normalization rules on `Int.mul` :
     - 0 * n ==> 0
     - 1 * n ==> n
     - -1 * n ==> -n
     - N1 * N2 ==> N1 "*" N2
     - N1 * (N2 * n) ==> (N1 "*" N2) * n
     - n1 * n2 ==> n2 * n1 (if n2 <ₒ n1)
   Assume that f = Expr.const ``Int.mul.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Int.mul` expected at this stage)
-/
def optimizeIntMul (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeIntMul: exactly two arguments expected"
 let opArgs ← reorderIntOp args -- error triggered when args.size ≠ 2
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 match isIntValue? op1, isIntValue? op2 with
 | some (Int.ofNat 0), _ => return op1
 | some (Int.ofNat 1), _ => return op2
 | some (Int.negSucc 0), _ => return (← optimizeIntNeg (← mkIntNegOp) #[op2])
 | some n1, some n2 => evalBinIntOp Int.mul n1 n2
 | nv1, _ =>
   if let some (Int.ofNat 0) := nv1 then return op1
   if let some (Int.ofNat 1) := nv1 then return op2
   if let some (Int.negSucc 0) := nv1 then return (← optimizeIntNeg (← mkIntNegOp) #[op2])
   if let some r ← cstMulProp? nv1 op2 then return r
   mkExpr (mkApp2 f op1 op2)

 where
   /- Given `mv1` and `op2` return `some ((N1 "*" N2) * n)` when
      `mv1 := some N1 ∧ op2 := (N2 * n)`. Otherwise `none`
   -/
   cstMulProp? (mv1 : Option Int) (op2 : Expr) : TranslateEnvT (Option Expr) := do
    match mv1, toIntCstOpExpr? op2 with
    | some n1, some (IntCstOpInfo.IntMulExpr n2 e2) =>
       some <$> mkExpr (mkApp2 f (← evalBinIntOp Int.mul n1 n2) e2)
    | _, _ => return none

/-- Given `e1` and `e2` corresponding to the operands for `Int.ediv`, `Int.tdiv` and `Int.fdiv`,
    return `some 1` only when the following conditions are satisfied:
      - e1 =ₚₜᵣ e2 ∧
      - 0 < e1 := _ ∈ hypsInContext ∨ e < 0 := _ ∈ hypsInContext ∨ ¬ (0 = e1) := _ ∈ hypsInContext
    Otherwise, return none.
-/
def intDivSelfReduce? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
  if !(← exprEq e1 e2) then return none
  if (← nonZeroIntInHyps e1)
  then return ← mkIntLitExpr (Int.ofNat 1)
  else return none

/-- Given `e1` and `e2` corresponding to the operands for `Int.ediv`, `Int.tdiv` and `Int.fdiv`,
    return `some n` only when one of the following conditions is satisfied:
     - `e1 := m * n` ∧ e2 = m ∧ (0 < m := _ ∈ hypsInContext ∨ m < 0 := _ ∈ hypsInContext ∨ ¬ (0 = m) := _ ∈ hypsInContext); or
     - `e1 := n * m` ∧ e2 = m ∧ (0 < m := _ ∈ hypsInContext ∨ m < 0 := _ ∈ hypsInContext ∨ ¬ (0 = m) := _ ∈ hypsInContext);
    Otherwise, return none.
-/
def mulIntDivReduceExpr? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
  match intMul? e1 with
  | some (op1, op2) =>
     unless !(← exprEq op1 e2) do
       if (← nonZeroIntInHyps e2) then return some op2
     unless !(← exprEq op2 e2) do
       if (← nonZeroIntInHyps e2) then return some op1
     return none
  | none => return none


/-- Given `op1` and `op2` corresponding to the operands for `Int.ediv`, `Int.tdiv` and `Int.fdiv`,
    try to apply the following simplification rules:
     - n / 0 ==> 0
     - n / 1 ==> n
     - 0 / n ==> 0
     - N1 / N2 ==> N1 "/" N2
     - n / n ==> 1
         (if 0 < n := _ ∈ hypsInContext ∨ ¬ (0 = n) := _ ∈ hypsInContext ∨ n < 0 := _ ∈ hypsInContext )
     - (m * n) / m | (n * m) / m ==> n
          (if  0 < m := _ ∈ hypsInContext ∨ ¬ (0 = m) := _ ∈ hypsInContext ∨ m < 0 := _ ∈ hypsInContext)
-/
def optimizeIntDivCommon (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 match isIntValue? op1, isIntValue? op2 with
 | _, some (Int.ofNat 0) => return op2
 | _, some (Int.ofNat 1)
 | some (Int.ofNat 0), _ => return op1
 | some n1, some n2 => evalBinIntOp Int.ediv n1 n2
 | _, _ =>
   if let some r ← intDivSelfReduce? op1 op2 then return r
   if let some r ← mulIntDivReduceExpr? op1 op2 then return r
   return none

/- Given `op1` and `op2` corresponding to the operands for `Int.ediv`, `Int.tdiv` and `Int.fdiv`,
   and `f_div` the corresponding divisor operator,
     - return `some (((f_div N1 (Int.gcd N1 N2)) * n), (f_div N2 (Int.gcd N1 N2)))`
       when `op1 := (N1 * n) ∧ op2 := N2 ∧ Int.gcd N1 N2
   Otherwise `none`.
   Assumes that N2 ≠ 0
-/
def cstCommonDivProp?
  (op1 : Expr) (op2 : Expr) (f_div : Int -> Int -> Int) : TranslateEnvT (Option (Expr × Expr)) := do
 let some (n, e1) := intMul? op1 | return none
 match isIntValue? n, isIntValue? op2 with
 | some n1, some n2 =>
    let gcd := Int.gcd n1 n2
    if gcd == 1 then return none
    let mulExpr ← optimizeIntMul (← mkIntMulOp) #[(← evalBinIntOp f_div n1 gcd), e1]
    return (mulExpr, (← evalBinIntOp f_div n2 gcd))
 | _, _ => return none


/-- Apply the following simplification/normalization rules on `Int.ediv`:
     - n / 0 ==> 0
     - n / 1 ==> n
     - 0 / n ==> 0
     - N1 / N2 ==> N1 "/ₑ" N2
     - n / n ==> 1
         (if 0 < n := _ ∈ hypsInContext ∨ ¬ (0 = n) := _ ∈ hypsInContext ∨ n < 0 := _ ∈ hypsInContext )
     - (m * n) / m | (n * m) / m ==> n
         (if  0 < m := _ ∈ hypsInContext ∨ ¬ (0 = m) := _ ∈ hypsInContext ∨ m < 0 := _ ∈ hypsInContext)
     - (N1 * n) / N2 ===> ((N1 "/" Int.gcd N1 N2) * n) / (N2 "/ₑ" Int.gcd N1 N2) (if N2 ≠ 0 ∧ Int.gcd N1 N2 ≠ 1)
   Assume that f = Expr.const ``Int.ediv.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Int.ediv` expected at this stage)
-/
partial def optimizeIntEDiv (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeIntEDiv: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 if let some r ← optimizeIntDivCommon op1 op2 then return r
 else if let some (op1', op2') ← cstCommonDivProp? op1 op2 Int.ediv
      then optimizeIntEDiv f #[op1', op2']
 else mkExpr (mkApp2 f op1 op2)

/-- Given `e1` and `e2` corresponding to the operands for `Int.emod`, `Int.fmod` and `Int.tmod`,
    return `some 0` only when one of the following conditions is satisfied:
     - e1 =ₚₜᵣ e2; or
     - `e1 := m * n` ∧ e2 = m; or
     - `e1 := n * m` ∧ e2 = m;
    Otherwise, return none.
-/
def intModToZeroExpr? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
  if (← exprEq e1 e2) then return (some (← mkIntLitExpr (Int.ofNat 0)))
  match intMul? e1 with
  | some (op1, op2) =>
     if (← exprEq op1 e2 <||> exprEq op2 e2) then return (← mkIntLitExpr (Int.ofNat 0))
     return none
  | none => return none

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

def optimizeIntModCommon (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
 match isIntValue? op1, isIntValue? op2 with
 | _, some (Int.ofNat 0) => return op1
 | _, some (Int.ofNat 1) => mkIntLitExpr (Int.ofNat 0)
 | some (Int.ofNat 0), _ => return op1
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
   cstModProp? (op1 : Expr) (mv2 : Option Int) : TranslateEnvT (Option Expr) := do
   let some (n, _e1) := intMul? op1 | return none
    match isIntValue? n, mv2 with
    | some n1, some n2 =>
        if Int.emod n1 n2 == 0
        then return (← mkIntLitExpr (Int.ofNat 0))
        else return none
    | _, _ => return none

/-- Apply the following simplification/normalization rules on `Int.emod` :
     - n % 0 ==> n
     - n % 1 ==> 0
     - 0 % n ==> 0
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
 if let some r ← optimizeIntModCommon op1 op2 then return r
 mkExpr (mkApp2 f op1 op2)

/-- Apply the following simplification/normalization rules on `Int.tdiv`:
     - n / 0 ==> 0
     - n / 1 ==> n
     - 0 / n ==> 0
     - N1 / N2 ==> N1 "/" N2
     - n / n ==> 1
         (if 0 < n := _ ∈ hypsInContext ∨ ¬ (0 = n) := _ ∈ hypsInContext ∨ n < 0 := _ ∈ hypsInContext )
     - (m * n) / m | (n * m) / m ==> n
         (if  0 < m := _ ∈ hypsInContext ∨ ¬ (0 = m) := _ ∈ hypsInContext ∨ m < 0 := _ ∈ hypsInContext)
     - (n / N1) / N2 ==> n / (N1 "*" N2) (only valid for Int.tdiv)
     - (N1 * n) / N2 ===> ((N1 "/" Int.gcd N1 N2) * n) / (N2 "/" Int.gcd N1 N2) (if N2 ≠ 0 ∧ Int.gcd N1 N2 ≠ 1)
   Assume that f = Expr.const ``Int.tdiv.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Int.tdiv` expected at this stage)
-/
partial def optimizeIntTDiv (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeIntTDiv: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 if let some r ← optimizeIntDivCommon op1 op2 then return r
 else if let some r ← cstTDivProp? op1 op2 then return r
 else if let some (op1', op2') ← cstCommonDivProp? op1 op2 Int.tdiv
      then optimizeIntTDiv f #[op1', op2']
 else mkExpr (mkApp2 f op1 op2)

 where
   /- Given `op1` and `op2` corresponding to the operands for Int.tdiv,
       - return `some (n /ₑ (N1 "*" N2))` when `op1 := (n /ₑ N1) ∧ op2 := N2`
      Otherwise `none`.
      Assumes that N2 ≠ 0
   -/
   cstTDivProp? (op1 : Expr) (op2 : Expr) : TranslateEnvT (Option Expr) := do
     let some (e1, n) := intTDiv? op1 | return none
     match isIntValue? n, isIntValue? op2 with
     | some n1, some n2 => mkExpr (mkApp2 f e1 (← evalBinIntOp Int.mul n1 n2))
     | _, _ => return none

/-- Apply the following simplification/normalization rules on `Int.tmod` :
     - n % 0 ==> n
     - n % 1 ==> 0
     - 0 % n ==> 0
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
 if let some r ← optimizeIntModCommon op1 op2 then return r
 mkExpr (mkApp2 f op1 op2)

/-- Apply the following simplification/normalization rules on `Int.fdiv`:
     - n / 0 ==> 0
     - n / 1 ==> n
     - 0 / n ==> 0
     - N1 / N2 ==> N1 "/" N2
     - n / n ==> 1
         (if 0 < n := _ ∈ hypsInContext ∨ ¬ (0 = n) := _ ∈ hypsInContext ∨ n < 0 := _ ∈ hypsInContext )
     - (m * n) / m | (n * m) / m ==> n
         (if  0 < m := _ ∈ hypsInContext ∨ ¬ (0 = m) := _ ∈ hypsInContext ∨ m < 0 := _ ∈ hypsInContext)
     - (N1 * n) / N2 ===> ((N1 "/" Int.gcd N1 N2) * n) / (N2 "/" Int.gcd N1 N2) (if N2 ≠ 0 ∧ Int.gcd N1 N2 ≠ 1)
   Assume that f = Expr.const ``Int.fdiv.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Int.fdiv` expected at this stage)
-/
partial def optimizeIntFDiv (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeIntFDiv: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 if let some r ← optimizeIntDivCommon op1 op2 then return r
 else if let some (op1', op2') ← cstCommonDivProp? op1 op2 Int.fdiv
      then optimizeIntFDiv f #[op1', op2']
 else mkExpr (mkApp2 f op1 op2)

/-- Apply the following simplification/normalization rules on `Int.fmod` :
     - n % 0 ==> n
     - n % 1 ==> 0
     - 0 % n ==> 0
     - N1 % N2 ==> N1 "%" N2
     - (N1 * n) % N2 ==> 0 (if N1 % N2 = 0)
     - n1 % n2 ==> 0 (if n1 =ₚₜᵣ n2)
     - (m * n) % m | (n * m) % m ==> 0
   Assume that f = Expr.const ``Int.tmod.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Int.fmod` expected at this stage)
-/

def optimizeIntFMod (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeIntFMod: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 if let some r ← optimizeIntModCommon op1 op2 then return r
 mkExpr (mkApp2 f op1 op2)


/-- Return `some e` if `n := Int.neg (Int.ofNat e)`. Otherwise return `none`. -/
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
 mkAppExpr f args

/-- Normalize `Int.negSucc n` to `Int.neg (Int.ofNat (Nat.add 1 n))` only when `n` is not a constant value.
    An error is triggered if args.size ≠ 1.
    Assume that f = Expr.const ``Int.negSucc.
-/
def optimizeIntNegSucc (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 1 then throwEnvError "optimizeIntNegSucc: only one argument expected"
 let op := args[0]!
 if (isNatValue? op).isSome then return (← mkAppExpr f args)
 let addExpr ← optimizeNatAdd (← mkNatAddOp) #[← mkNatLitExpr 1, args[0]!]
 let intExpr ← mkExpr (mkApp (← mkIntOfNat) addExpr)
 optimizeIntNeg (← mkIntNegOp) #[intExpr]

/-- Normalize `Int.le x y` to `LE.le Int instLEInt x y`. -/
def optimizeIntLe (b_args : Array Expr) : TranslateEnvT Expr := do
  Expr.withApp (← mkIntLeOp) fun f i_args =>
    optimizeLE f (i_args ++ b_args)

/-- Apply simplification/normalization rules on `Int` operators.
-/
def optimizeInt? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n _ := f | return none
  match n with
  | ``Int.add => optimizeIntAdd f args
  | ``Int.mul => optimizeIntMul f args
  | ``Int.neg => optimizeIntNeg f args
  | ``Int.negSucc => optimizeIntNegSucc f args
  | ``Int.toNat => optimizeIntToNat f args
  | ``Int.le => optimizeIntLe args
  | ``Int.ediv => optimizeIntEDiv f args
  | ``Int.emod => optimizeIntEMod f args
  | ``Int.tdiv => optimizeIntTDiv f args
  | ``Int.tmod => optimizeIntTMod f args
  | ``Int.fdiv => optimizeIntFDiv f args
  | ``Int.fmod => optimizeIntFMod f args
  | _=> return none

end Solver.Optimize
