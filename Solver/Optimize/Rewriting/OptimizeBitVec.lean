import Lean
import Solver.Optimize.Rewriting.Utils
import Solver.Optimize.Env

open Lean Meta
namespace Solver.Optimize

/-- Extract the static width from the first argument of a BitVec operation.
    All BitVec ops have `{n : Nat}` as their first implicit parameter. -/
private def getWidthFromBitVecArgs (args : Array Expr) : Option Nat :=
  if args.isEmpty then none else isNatValue? args[0]!

/-- Reorder the two explicit operands of a commutative BitVec binary operation
    (args = [wExpr, op1, op2]) to a canonical form, following the same heuristics
    as `reorderNatOp`:
     - #[w, N, e]   ===> args          (constant first: keep)
     - #[w, e, N]   ===> #[w, N, e]   (constant to front)
     - #[w, fv1, fv2] ===> #[w, fv2, fv1]  (if fv2 < fv1 by name)
     - #[w, fv, e]  ===> args          (fvar first: keep)
     - #[w, e, fv]  ===> #[w, fv, e]  (fvar to front)
     - #[w, e1, e2] ===> #[w, e2, e1]  (if e2 < e1 by Expr.lt)
     - #[w, e1, e2] ===> args
    An error is triggered if args.size ≠ 3.
-/
private def reorderBitVecOp (args : Array Expr) : TranslateEnvT (Array Expr) := do
  if args.size != 3 then throwEnvError "reorderBitVecOp: three arguments expected"
  let wExpr := args[0]!
  let e1    := args[1]!
  let e2    := args[2]!
  let mkSwapped : Array Expr := #[wExpr, e2, e1]
  let isConst1 := (isBitVecValue? e1).isSome
  let isConst2 := (isBitVecValue? e2).isSome
  match isConst1, isConst2 with
  | true, _  => return args       -- constant first: keep
  | _,  true => return mkSwapped  -- constant to front
  | _, _ =>
    match e1, e2 with
    | Expr.fvar _, Expr.fvar _ =>
        if e2.lt e1 then return mkSwapped else return args
    | Expr.fvar _, _ => return args
    | _, Expr.fvar _ => return mkSwapped
    | _, _ =>
        -- Put recursive-call expressions last; otherwise use Expr.lt for canonical form
        let swap := (isTaggedRecursiveCall e1 && !isTaggedRecursiveCall e2) || e2.lt e1
        if swap then return mkSwapped else return args

/-- Detect `BitVec.add w N eInner` and return `(N, eInner)`.
    Assumes operands have already been reordered (constant is first). -/
private def bvAddCstExpr? (e : Expr) : Option (Nat × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``BitVec.add _) _) n2Expr) eInner =>
      match isBitVecValue? n2Expr with
      | some (_, n2) => some (n2, eInner)
      | none => none
  | _ => none

/-- Detect `BitVec.mul w N eInner` and return `(N, eInner)`.
    Assumes operands have already been reordered (constant is first). -/
private def bvMulCstExpr? (e : Expr) : Option (Nat × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``BitVec.mul _) _) n2Expr) eInner =>
      match isBitVecValue? n2Expr with
      | some (_, n2) => some (n2, eInner)
      | none => none
  | _ => none

/-- Apply simplification/normalization rules on `BitVec.not`:
     - not N ==> ~N
     - not (not x) ==> x
    Assume that `f = Expr.const ``BitVec.not`.
    An error is triggered if args.size ≠ 2 (implicit width + one operand).
-/
def optimizeBitVecNot (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if args.size != 2 then throwEnvError "optimizeBitVecNot: exactly two arguments expected (width + operand)"
  let op := args[1]!
  if let some (w, v) := isBitVecValue? op then
    -- bitwise NOT at width w: flip all w bits = allOnes XOR v
    return (← mkBitVecLitExpr w ((2^w - 1) ^^^ v))
  -- not (not x) ==> x
  match op with
  | Expr.app (Expr.app (Expr.const ``BitVec.not _) _) inner => return inner
  | _ => return (mkApp2 f args[0]! op)

/-- Apply simplification/normalization rules on `BitVec.neg`:
     - neg N ==> -N (mod 2^w)
     - neg 0_w ==> 0_w
    Assume that `f = Expr.const ``BitVec.neg`.
    An error is triggered if args.size ≠ 2.
-/
def optimizeBitVecNeg (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if args.size != 2 then throwEnvError "optimizeBitVecNeg: exactly two arguments expected (width + operand)"
  let op := args[1]!
  if let some (w, v) := isBitVecValue? op then
    return (← mkBitVecLitExpr w ((2^w - v) % (2^w)))
  return (mkApp2 f args[0]! op)

/-- Apply simplification/normalization rules on `BitVec.and`:
     - N1 &&& N2 ==> N1 "&" N2
     - 0_w &&& x ==> 0_w   (also handles x &&& 0_w via reordering)
     - allOnes &&& x ==> x  (also handles x &&& allOnes via reordering)
     - x &&& x ==> x
     - x &&& y ==> y &&& x  (canonical operand order via reorderBitVecOp)
    Assume that `f = Expr.const ``BitVec.and`.
    An error is triggered if args.size ≠ 3.
-/
def optimizeBitVecAnd (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if args.size != 3 then throwEnvError "optimizeBitVecAnd: exactly three arguments expected (width + two operands)"
  let ordArgs ← reorderBitVecOp args
  let wExpr := ordArgs[0]!
  let op1   := ordArgs[1]!
  let op2   := ordArgs[2]!
  match isBitVecValue? op1 with
  | some (w, v1) =>
      match isBitVecValue? op2 with
      | some (_, v2) => return (← mkBitVecLitExpr w (v1 &&& v2))
      | none =>
          if v1 == 0 then return (← mkBitVecLitExpr w 0)
          if v1 == 2^w - 1 then return op2
          return (mkAppN f #[wExpr, op1, op2])
  | none =>
      if (← exprEq op1 op2) then return op1
      return (mkAppN f #[wExpr, op1, op2])

/-- Apply simplification/normalization rules on `BitVec.or`:
     - N1 ||| N2 ==> N1 "|" N2
     - 0_w ||| x ==> x     (also handles x ||| 0_w via reordering)
     - allOnes ||| x ==> allOnes  (also handles x ||| allOnes via reordering)
     - x ||| x ==> x
     - x ||| y ==> y ||| x  (canonical operand order via reorderBitVecOp)
    Assume that `f = Expr.const ``BitVec.or`.
    An error is triggered if args.size ≠ 3.
-/
def optimizeBitVecOr (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if args.size != 3 then throwEnvError "optimizeBitVecOr: exactly three arguments expected (width + two operands)"
  let ordArgs ← reorderBitVecOp args
  let wExpr := ordArgs[0]!
  let op1   := ordArgs[1]!
  let op2   := ordArgs[2]!
  match isBitVecValue? op1 with
  | some (w, v1) =>
      match isBitVecValue? op2 with
      | some (_, v2) => return (← mkBitVecLitExpr w (v1 ||| v2))
      | none =>
          if v1 == 0 then return op2
          if v1 == 2^w - 1 then return op1
          return (mkAppN f #[wExpr, op1, op2])
  | none =>
      if (← exprEq op1 op2) then return op1
      return (mkAppN f #[wExpr, op1, op2])

/-- Apply simplification/normalization rules on `BitVec.xor`:
     - N1 ^^^ N2 ==> N1 "^" N2
     - 0_w ^^^ x ==> x     (also handles x ^^^ 0_w via reordering)
     - x ^^^ x ==> 0_w
     - x ^^^ y ==> y ^^^ x  (canonical operand order via reorderBitVecOp)
    Assume that `f = Expr.const ``BitVec.xor`.
    An error is triggered if args.size ≠ 3.
-/
def optimizeBitVecXor (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if args.size != 3 then throwEnvError "optimizeBitVecXor: exactly three arguments expected (width + two operands)"
  let ordArgs ← reorderBitVecOp args
  let wExpr := ordArgs[0]!
  let op1   := ordArgs[1]!
  let op2   := ordArgs[2]!
  match isBitVecValue? op1 with
  | some (w, v1) =>
      match isBitVecValue? op2 with
      | some (_, v2) => return (← mkBitVecLitExpr w (v1 ^^^ v2))
      | none =>
          if v1 == 0 then return op2
          return (mkAppN f #[wExpr, op1, op2])
  | none =>
      if (← exprEq op1 op2) then
        let some w := getWidthFromBitVecArgs ordArgs
          | throwEnvError "optimizeBitVecXor: static width required for x ^^^ x ==> 0"
        return (← mkBitVecLitExpr w 0)
      return (mkAppN f #[wExpr, op1, op2])

/-- Apply simplification/normalization rules on `BitVec.add`:
     - N1 + N2 ==> (N1 + N2) mod 2^w
     - N1 + (N2 + n) ==> (N1 + N2) + n  (constant propagation + associativity)
     - 0_w + x ==> x   (also handles x + 0_w via reordering)
     - x + y ==> y + x  (canonical operand order via reorderBitVecOp)
    Assume that `f = Expr.const ``BitVec.add`.
    An error is triggered if args.size ≠ 3.
-/
def optimizeBitVecAdd (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if args.size != 3 then throwEnvError "optimizeBitVecAdd: exactly three arguments expected (width + two operands)"
  let ordArgs ← reorderBitVecOp args
  let wExpr := ordArgs[0]!
  let op1   := ordArgs[1]!
  let op2   := ordArgs[2]!
  match isBitVecValue? op1 with
  | some (_, 0) => return op2
  | some (w, n1) =>
      match isBitVecValue? op2 with
      | some (_, n2) => evalBitVecOp (· + ·) w n1 n2
      | none =>
          -- associativity: N1 + (N2 + n) ==> (N1 + N2) + n
          if let some (n2, eInner) := bvAddCstExpr? op2 then
            setRestart
            return (mkAppN f #[wExpr, ← mkBitVecLitExpr w ((n1 + n2) % 2^w), eInner])
          return (mkAppN f #[wExpr, op1, op2])
  | none => return (mkAppN f #[wExpr, op1, op2])

/-- Apply simplification/normalization rules on `BitVec.sub`:
     - N1 - N2 ==> (N1 - N2) mod 2^w
     - x - 0_w ==> x
     - x - x ==> 0_w
    Assume that `f = Expr.const ``BitVec.sub`.
    An error is triggered if args.size ≠ 3.
-/
def optimizeBitVecSub (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if args.size != 3 then throwEnvError "optimizeBitVecSub: exactly three arguments expected (width + two operands)"
  let wExpr := args[0]!
  let op1 := args[1]!
  let op2 := args[2]!
  match isBitVecValue? op1, isBitVecValue? op2 with
  | some (w, v1), some (_, v2) => evalBitVecOp (fun a b => a + (2^w - b)) w v1 v2
  | _, some (_, 0) => return op1
  | _, _ =>
      if (← exprEq op1 op2) then
        let some w := getWidthFromBitVecArgs args
          | throwEnvError "optimizeBitVecSub: static width required for x - x ==> 0"
        return (← mkBitVecLitExpr w 0)
      return (mkAppN f #[wExpr, op1, op2])

/-- Apply simplification/normalization rules on `BitVec.mul`:
     - N1 * N2 ==> (N1 * N2) mod 2^w
     - N1 * (N2 * n) ==> (N1 * N2) * n  (constant propagation + associativity)
     - 0_w * x ==> 0_w  (also handles x * 0_w via reordering)
     - 1_w * x ==> x    (also handles x * 1_w via reordering)
     - x * y ==> y * x  (canonical operand order via reorderBitVecOp)
    Assume that `f = Expr.const ``BitVec.mul`.
    An error is triggered if args.size ≠ 3.
-/
def optimizeBitVecMul (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if args.size != 3 then throwEnvError "optimizeBitVecMul: exactly three arguments expected (width + two operands)"
  let ordArgs ← reorderBitVecOp args
  let wExpr := ordArgs[0]!
  let op1   := ordArgs[1]!
  let op2   := ordArgs[2]!
  match isBitVecValue? op1 with
  | some (w, 0) => return (← mkBitVecLitExpr w 0)
  | some (_, 1) => return op2
  | some (w, n1) =>
      match isBitVecValue? op2 with
      | some (_, n2) => evalBitVecOp (· * ·) w n1 n2
      | none =>
          -- associativity: N1 * (N2 * n) ==> (N1 * N2) * n
          if let some (n2, eInner) := bvMulCstExpr? op2 then
            setRestart
            return (mkAppN f #[wExpr, ← mkBitVecLitExpr w ((n1 * n2) % 2^w), eInner])
          return (mkAppN f #[wExpr, op1, op2])
  | none => return (mkAppN f #[wExpr, op1, op2])

/-- Apply simplification/normalization rules on BitVec shift operations
    (`shiftLeft`, `ushiftRight`, `sshiftRight`):
     - x <<< 0 ==> x; x >>> 0 ==> x
     - N <<< s ==> (N << s) mod 2^w  (when s is a literal Nat)
    Assume that args layout is [n_implicit, x_explicit, s_explicit : Nat].
    An error is triggered if args.size ≠ 3.
-/
def optimizeBitVecShift (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if args.size != 3 then throwEnvError "optimizeBitVecShift: exactly three arguments expected (width + value + shift)"
  let wExpr := args[0]!
  let op := args[1]!
  let shiftArg := args[2]!
  match isNatValue? shiftArg with
  | some 0 => return op
  | some s =>
      match isBitVecValue? op with
      | some (w, v) =>
          let Expr.const n _ := f | return (mkAppN f #[wExpr, op, shiftArg])
          let result := match n with
            | ``BitVec.shiftLeft   => (v <<< s) % (2^w)
            | ``BitVec.ushiftRight => v >>> s
            | _                    => (v >>> s)  -- sshiftRight: sign-extend MSB, approx for concrete folding
          return (← mkBitVecLitExpr w result)
      | none => return (mkAppN f #[wExpr, op, shiftArg])
  | none => return (mkAppN f #[wExpr, op, shiftArg])

/-- Apply simplification/normalization rules on BitVec operators. -/
def optimizeBitVec? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n _ := f | return none
  match n with
  | ``BitVec.not         => return some (← optimizeBitVecNot f args)
  | ``BitVec.neg         => return some (← optimizeBitVecNeg f args)
  | ``BitVec.and         => return some (← optimizeBitVecAnd f args)
  | ``BitVec.or          => return some (← optimizeBitVecOr  f args)
  | ``BitVec.xor         => return some (← optimizeBitVecXor f args)
  | ``BitVec.add         => return some (← optimizeBitVecAdd f args)
  | ``BitVec.sub         => return some (← optimizeBitVecSub f args)
  | ``BitVec.mul         => return some (← optimizeBitVecMul f args)
  | ``BitVec.shiftLeft
  | ``BitVec.ushiftRight
  | ``BitVec.sshiftRight => return some (← optimizeBitVecShift f args)
  | _                    => return none

end Solver.Optimize
