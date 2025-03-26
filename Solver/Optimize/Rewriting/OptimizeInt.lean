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
 if let some .. := isNatValue? op then return (← mkAppExpr f args)
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
  | _=> return none

end Solver.Optimize
