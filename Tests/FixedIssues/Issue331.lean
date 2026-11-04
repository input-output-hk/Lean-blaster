import Lean
import Blaster
import Tests.Utils

namespace Tests.Issue331

-- Issue: https://github.com/input-output-hk/Lean-blaster/issues/331
--        matching a negative `Int` literal against an `Int.negSucc m` pattern binds `m` one too
--        low, e.g., `Int.natAbs (-7)` reduces to `6`: `blaster` falsifies `Int.natAbs (-7) = 7`
--        and proves `Int.natAbs (-7) = 6`.
--
-- NOTE: A negative literal is normalized to `Int.negSucc (n - 1)` while a symbolic `Int.negSucc m`
--       is normalized to `Int.neg (Int.ofNat (1 + m))`, both for discriminators and patterns.
--       `isPatternMatch` and `unifyAndUpdateEqMap` must therefore relate `Int.negSucc` literals
--       with `Int.neg (Int.ofNat _)` expressions on both sides.
--       See Tests/Optimize/OptimizeMatch/MatchReduce.lean for the broader Nat/Int literal coverage.

set_option warn.sorry false

def negOf (i : Int) : Nat := match i with | .ofNat m => m | .negSucc m => m

#testOptimize ["NatAbsNegLit"] Int.natAbs (-7) = 7 ===> True
#testOptimize ["NatAbsNegOne"] Int.natAbs (-1) = 1 ===> True
#testOptimize ["NegSuccArgLit"] negOf (-7) = 6 ===> True
#testOptimize ["NegSuccArgOne"] negOf (-1) = 0 ===> True
#testOptimize ["NatAbsNegLitOffByOne"] Int.natAbs (-7) = 6 ===> False
#testOptimize ["NegSuccArgLitOffByOne"] negOf (-7) = 5 ===> False

-- the literal reaches the match through a hypothesis
theorem natAbs_of_eq_neg_lit : ∀ (x : Int), x = -7 → x.natAbs = 7 := by blaster

theorem negOf_neg_lit : ∀ (x : Int), x = -1234 → negOf x = 1233 := by blaster

-- symbolic `Int.negSucc` already worked; it must keep working
theorem natAbs_negSucc : ∀ (m : Nat), Int.natAbs (Int.negSucc m) = m + 1 := by blaster

theorem negOf_negSucc : ∀ (m : Nat), negOf (Int.negSucc m) = m := by blaster

-- must be falsified, not merely undetermined
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Int), x = -7 → x.natAbs = 6]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Int), x = -1234 → negOf x = 1232]

/-! ## Negative literal discriminators against `Int.negSucc` literal, offset, variable and named patterns -/

def negLit (i : Int) : Nat :=
  match i with
  | .negSucc 0 => 300
  | .negSucc 4 => 304
  | n@(.negSucc m@(k + 2)) => n.natAbs + m * k
  | .negSucc k => 2 * k
  | .ofNat k => k

-- `Int.negSucc` literal patterns
#testOptimize ["NegLitZero"] negLit (-1) = 300 ===> True
#testOptimize ["NegLitFour"] negLit (-5) = 304 ===> True
-- `Int.negSucc (k + 2)` offset pattern with named patterns: `-7 = Int.negSucc 6`, so `m := 6`, `k := 4`
#testOptimize ["NegLitNamedOffset"] negLit (-7) = 31 ===> True
#testOptimize ["NegLitNamedOffsetMin"] negLit (-3) = 3 ===> True
-- `Int.negSucc 1` does not unify with `Int.negSucc (k + 2)` (literal < offset)
#testOptimize ["NegLitVar"] negLit (-2) = 2 ===> True
-- `Int.ofNat` literal falls through all `Int.negSucc` patterns
#testOptimize ["NegLitOfNat"] negLit 7 = 7 ===> True
#testOptimize ["NegLitOfNatZero"] negLit 0 = 0 ===> True
-- negative literal spelled with the constructor or obtained by constant folding
#testOptimize ["NegLitCtor"] negLit (Int.negSucc 6) = 31 ===> True
#testOptimize ["NegLitFolded"] negLit (0 - 7) = 31 ===> True
#testOptimize ["NegLitNegZero"] negLit (-0) = 0 ===> True
-- off-by-one must be refuted
#testOptimize ["NegLitZeroOffByOne"] negLit (-1) = 0 ===> False
#testOptimize ["NegLitNamedOffsetOffByOne"] negLit (-7) = 21 ===> False
#testOptimize ["NegLitVarOffByOne"] negLit (-2) = 0 ===> False

-- no match reduction: `Int.negSucc m` is normalized to `Int.neg (Int.ofNat (1 + m))`, the
-- `Int.negSucc` literal patterns potentially match and bind `m` in their alternative, while
-- the named patterns `n`, `m` and `k` are bound through the equality map.
variable (m : Nat)
#testOptimize ["NegLitSym"] (norm-result: 1)
  negLit (Int.negSucc m) ===>
  Blaster.dite' (0 = m) (fun _ => 300) fun _ =>
    Blaster.dite' (4 = m) (fun _ => 304) fun _ =>
      Blaster.dite' (Int.negSucc 2 < Int.neg (Int.ofNat (Nat.add 1 m)))
        (fun _ => Blaster.dite' (Int.negSucc 0 < Int.neg (Int.ofNat (Nat.add 1 m))) (fun _ => 0) fun _ => Nat.mul 2 m)
        fun _ => Nat.add (Nat.add 1 m) (Nat.mul m (Nat.sub m 2))

-- same with a symbolic offset discriminator: `Int.negSucc (m + 2)` is `Int.neg (Int.ofNat (3 + m))`,
-- so `Int.negSucc 0` cannot match (`1 = 3 + m` is refuted) and `Int.negSucc 4` matches when `2 = m`
#testOptimize ["NegLitSymOffset"] (norm-result: 1)
  negLit (Int.negSucc (m + 2)) ===>
  Blaster.dite' (2 = m) (fun _ => 304) fun _ =>
    Blaster.dite' (Int.negSucc 2 < Int.neg (Int.ofNat (Nat.add 3 m)))
      (fun _ => Blaster.dite' (Int.negSucc 0 < Int.neg (Int.ofNat (Nat.add 3 m))) (fun _ => 0) fun _ => Nat.mul 2 (Nat.add 2 m))
      fun _ => Nat.add (Nat.add 3 m) (Nat.mul m (Nat.add 2 m))

-- end-to-end through the solver
theorem negLit_neg_lit : ∀ (x : Int), x = -7 → negLit x = 31 := by blaster
theorem negLit_neg_lit_min : ∀ (x : Int), x = -3 → negLit x = 3 := by blaster
theorem negLit_neg_lit_var : ∀ (x : Int), x = -2 → negLit x = 2 := by blaster
theorem negLit_negSucc : ∀ (m : Nat),
  negLit (Int.negSucc m) = if m = 0 then 300 else if m = 4 then 304 else if m ≥ 2 then m + 1 + m * (m - 2) else 2 * m := by blaster

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Int), x = -7 → negLit x = 21]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Int), x = -2 → negLit x = 0]

end Tests.Issue331
