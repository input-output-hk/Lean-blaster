import Lean
import Blaster.Optimize.Rewriting.Utils
import Blaster.Optimize.Env

open Lean Meta
namespace Blaster.Optimize

/-- Evaluate a binary BitVec op on literal values using Lean's own BitVec
    semantics (exactness over speed: folding MUST agree with the kernel).
    Uses named ops (`.udiv`, `.umod`, `.sdiv`, `.smod`, `.srem`) throughout
    to eliminate any HDiv/HMod instance ambiguity.
-/
private def evalBitVecBinOp (op : Name) (w v1 v2 : Nat) : Option Nat :=
  let x := BitVec.ofNat w v1
  let y := BitVec.ofNat w v2
  match op with
  | ``BitVec.add  => some (x.add y).toNat
  | ``BitVec.sub  => some (x.sub y).toNat
  | ``BitVec.mul  => some (x.mul y).toNat
  | ``BitVec.and  => some (x.and y).toNat
  | ``BitVec.or   => some (x.or y).toNat
  | ``BitVec.xor  => some (x.xor y).toNat
  | ``BitVec.udiv => some (x.udiv y).toNat
  | ``BitVec.umod => some (x.umod y).toNat
  | ``BitVec.sdiv => some (x.sdiv y).toNat
  | ``BitVec.smod => some (x.smod y).toNat
  | ``BitVec.srem => some (x.srem y).toNat
  | _ => none

/-- Apply constant-folding and identity rules on opaque BitVec applications:
     - BitVec.toNat w V     ==> V (as Nat literal) (literal bv)
     - LT.lt  (BitVec w) _ V1 V2 ==> True/False   (both literal, unsigned)
     - LE.le  (BitVec w) _ V1 V2 ==> True/False   (both literal, unsigned)
     - BitVec.ult/ule/slt/sle w V1 V2 ==> true/false (both literal)
     - binop V1 V2          ==> V1 "op" V2   (both literal)
     - BitVec.not V / neg V ==> folded literal
     - x &&& 0 / 0 &&& x    ==> 0
     - x ||| 0 / 0 ||| x    ==> x
     - x ^^^ x              ==> 0
     - x ^^^ 0 / 0 ^^^ x    ==> x
     - x + 0 / 0 + x        ==> x
     - x - x                ==> 0
     - x - 0                ==> x
     - x * 1 / 1 * x        ==> x
     - x * 0 / 0 * x        ==> 0
    Return `none` when no rule applies (translation handles the rest).
-/
def optimizeBitVec? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n _ := f | return none
  -- BitVec.toNat w x  (args := #[w, x]) — fold when x is a literal
  if n == ``BitVec.toNat then
    if args.size != 2 then return none
    let some (_, v) := isBitVecValue? args[1]! | return none
    return some (← mkNatLitExpr v)
  -- Prop LT/LE on BitVec literals — fold to True/False (unsigned semantics)
  if n == ``LT.lt || n == ``LE.le then
    if args.size != 4 then return none
    if !isBitVecType args[0]! then return none
    let some (_, v1) := isBitVecValue? args[2]! | return none
    let some (_, v2) := isBitVecValue? args[3]! | return none
    let b := if n == ``LT.lt then Nat.blt v1 v2 else Nat.ble v1 v2
    return some (← mkPropLit b)
  -- Bool comparison ops on BitVec literals — fold to true/false
  if n == ``BitVec.ult || n == ``BitVec.ule ||
     n == ``BitVec.slt || n == ``BitVec.sle then
    if args.size != 3 then return none
    let some w := isNatValue? args[0]! | return none
    let some (_, v1) := isBitVecValue? args[1]! | return none
    let some (_, v2) := isBitVecValue? args[2]! | return none
    let x := BitVec.ofNat w v1
    let y := BitVec.ofNat w v2
    let b := match n with
             | ``BitVec.ult => x.ult y
             | ``BitVec.ule => x.ule y
             | ``BitVec.slt => x.slt y
             | _            => x.sle y  -- ``BitVec.sle
    return some (← mkBoolLit b)
  -- unary ops: args := #[w, x]
  if n == ``BitVec.not || n == ``BitVec.neg then
    if args.size != 2 then return none
    let some w := isNatValue? args[0]! | return none
    let some (_, v) := isBitVecValue? args[1]! | return none
    let r := if n == ``BitVec.not
             then (BitVec.ofNat w v).not.toNat
             else (BitVec.ofNat w v).neg.toNat
    return some (← mkBitVecLitExpr w r)
  -- binary ops: args := #[w, x, y]
  if args.size != 3 then return none
  let some w := isNatValue? args[0]! | return none
  let v1? := isBitVecValue? args[1]!
  let v2? := isBitVecValue? args[2]!
  match v1?, v2? with
  | some (_, v1), some (_, v2) =>
      match evalBitVecBinOp n w v1 v2 with
      | some r => return some (← mkBitVecLitExpr w r)
      | none => return none
  | _, _ => identityRules n w args v1? v2?

 where
  identityRules (n : Name) (w : Nat) (args : Array Expr)
      (v1? v2? : Option (Nat × Nat)) : TranslateEnvT (Option Expr) := do
    let x := args[1]!
    let y := args[2]!
    let isZero (v? : Option (Nat × Nat)) := v?.map (·.2) == some 0
    let isOne  (v? : Option (Nat × Nat)) := v?.map (·.2) == some 1
    match n with
    | ``BitVec.and =>
        if isZero v1? || isZero v2? then return some (← mkBitVecLitExpr w 0) else return none
    | ``BitVec.or =>
        if isZero v1? then return some y
        else if isZero v2? then return some x else return none
    | ``BitVec.xor =>
        if exprEq x y then return some (← mkBitVecLitExpr w 0)
        else if isZero v1? then return some y
        else if isZero v2? then return some x else return none
    | ``BitVec.add =>
        if isZero v1? then return some y
        else if isZero v2? then return some x else return none
    | ``BitVec.sub =>
        if exprEq x y then return some (← mkBitVecLitExpr w 0)
        else if isZero v2? then return some x else return none
    | ``BitVec.mul =>
        if isZero v1? || isZero v2? then return some (← mkBitVecLitExpr w 0)
        else if isOne v1? then return some y
        else if isOne v2? then return some x else return none
    | _ => return none

end Blaster.Optimize
