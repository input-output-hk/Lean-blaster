import Lean
import Tests.Utils
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Test.ExtensionCyclic

/-! ## Cyclic rewriting detection

An expression entering the optimizer is recorded in the cyclic cache (`isInOptimizeEnvCache`) and
removed from it when its optimization returns (`stackContinuity`, `.InitOptimizeReturn`). When a
registered rule rewrites an expression to a (hash-consed) expression that is still being optimized
(`applyExtension?`, `inCyclicCache`), the rule is ignored: a warning is logged, the pending restart
is reset and the optimization goes on as if no rule had matched (the arguments are optimized and the
rules are tried again on the normalized application). The last rewriting before the cycle closes is
therefore kept (`f1 5 ↦ g1 5`, not `f1 5`) and the enclosing expression is optimized normally.

NOTE: on a closed goal written with a literal the cycle is detected twice, on two distinct
hash-consed expressions printed identically: first on the elaborated `f1 (OfNat.ofNat Nat 5 _)`,
when the rules are tried before the arguments are optimized (`InitNonFunOptimizeArgs`), then on
`f1 5` once the literal is normalized and the application is rewritten again. The warning is logged
once with a bound variable (`ExtCyclicVar_*`) or a raw literal (`ExtCyclicRawLit_*`), whose
normal form is the elaborated term.

NOTE: the expression is printed in the warning without its local context, a bound variable appears
as `_fvar.N` with an unstable number. The warning is therefore only checked (`#guard_msgs (warning)`)
on closed terms; the cases with bound variables only check the result of the optimization and drop
the warning. The `✅ Success` info messages are passed through by `#guard_msgs (warning)`.
-/

axiom c : Nat → Prop

/-! Two rules rewriting into each other. -/
axiom f1 : Nat → Nat
axiom g1 : Nat → Nat

@[blaster]
axiom f1_g1 : ∀ (n : Nat), f1 n = g1 n

@[blaster]
axiom g1_f1 : ∀ (n : Nat), g1 n = f1 n

/--
warning: [blaster]: Cyclic rewriting detected on f1 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
---
warning: [blaster]: Cyclic rewriting detected on f1 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
-/
#guard_msgs (warning) in
#testOptimize [ "ExtCyclic_1" ] (norm-result: 1) ∀ (m : Nat), f1 5 = m ===> ∀ (m : Nat), m = g1 5

/--
warning: [blaster]: Cyclic rewriting detected on g1 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
---
warning: [blaster]: Cyclic rewriting detected on g1 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
-/
#guard_msgs (warning) in
#testOptimize [ "ExtCyclic_2" ] (norm-result: 1) ∀ (m : Nat), g1 5 = m ===> ∀ (m : Nat), m = f1 5

-- `g1 5` is found in the optimization cache (`g1 5 ↦ f1 5`): `f1 5 = f1 5` reduces to `True`
/--
warning: [blaster]: Cyclic rewriting detected on f1 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
---
warning: [blaster]: Cyclic rewriting detected on f1 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
-/
#guard_msgs (warning) in
#testOptimize [ "ExtCyclic_3" ] f1 5 = g1 5 ===> True

-- the second occurrence of `f1 5` is found in the optimization cache: the cycle is not detected again
/--
warning: [blaster]: Cyclic rewriting detected on f1 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
---
warning: [blaster]: Cyclic rewriting detected on f1 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
-/
#guard_msgs (warning) in
#testOptimize [ "ExtCyclic_4" ] (norm-result: 1) ∀ (m k : Nat), f1 5 = m ∧ f1 5 = k ===> ∀ (m k : Nat), m = g1 5 ∧ k = g1 5

/--
warning: [blaster]: Cyclic rewriting detected on f1 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
---
warning: [blaster]: Cyclic rewriting detected on f1 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
-/
#guard_msgs (warning) in
#testOptimize [ "ExtCyclic_5" ] (norm-result: 1) ∀ (n : Nat), c n → f1 5 = n ===> ∀ (n : Nat), c n → n = g1 5

-- the enclosing expression is optimized normally (operands reordered, literal `0` normalized)
-- around the rewritten sub-expression
/--
warning: [blaster]: Cyclic rewriting detected on f1 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
---
warning: [blaster]: Cyclic rewriting detected on f1 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
-/
#guard_msgs (warning) in
#testOptimize [ "ExtCyclicSub_1" ] (norm-result: 1)
  ∀ (m : Nat), Nat.add (f1 5) m = 0 ===>
  ∀ (m : Nat), 0 = Nat.add m (g1 5)

-- bound variables: the warning (logged once, `f1 n` is already in normal form) is dropped
-- (unstable `_fvar.N` in the message)
#guard_msgs (drop warning) in
#testOptimize [ "ExtCyclicVar_1" ] ∀ (n m : Nat), f1 n = m ===> ∀ (n m : Nat), m = g1 n
#guard_msgs (drop warning) in
#testOptimize [ "ExtCyclicVar_2" ] ∀ (n m : Nat), g1 n = m ===> ∀ (n m : Nat), m = f1 n
#guard_msgs (drop warning) in
#testOptimize [ "ExtCyclicVar_3" ] ∀ (n : Nat), f1 n = g1 n ===> True

-- raw literal: the argument is already in normal form, the cycle is detected once
/--
warning: [blaster]: Cyclic rewriting detected on f1 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
-/
#guard_msgs (warning) in
#testOptimize [ "ExtCyclicRawLit_1" ] ∀ (m : Nat), f1 (nat_lit 5) = m ===> ∀ (m : Nat), m = g1 (nat_lit 5)
/--
warning: [blaster]: Cyclic rewriting detected on g1 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
-/
#guard_msgs (warning) in
#testOptimize [ "ExtCyclicRawLit_2" ] ∀ (m : Nat), g1 (nat_lit 5) = m ===> ∀ (m : Nat), m = f1 (nat_lit 5)

/-! `noRestart` does not prevent the cycle: the rewritten term is not re-optimized by the rule itself
    but its arguments are optimized and the registered rules are tried again when the application is
    finalized (`finalizeNonFunApp`). Without restart the normalized `g2 5` is not rewritten again
    after the cycle is detected: the cycle is reported once and `f2 5` is kept. -/
axiom f2 : Nat → Nat
axiom g2 : Nat → Nat

@[blaster (noRestart := true)]
axiom f2_g2 : ∀ (n : Nat), f2 n = g2 n

@[blaster (noRestart := true)]
axiom g2_f2 : ∀ (n : Nat), g2 n = f2 n

/--
warning: [blaster]: Cyclic rewriting detected on f2 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
-/
#guard_msgs (warning) in
#testOptimize [ "ExtCyclicNoRestart_1" ] (norm-result: 1) ∀ (m : Nat), f2 5 = m ===> ∀ (m : Nat), m = f2 5

/-! Three rules forming a cycle. -/
axiom f3 : Nat → Nat
axiom g3 : Nat → Nat
axiom k3 : Nat → Nat

@[blaster]
axiom f3_g3 : ∀ (n : Nat), f3 n = g3 n

@[blaster]
axiom g3_k3 : ∀ (n : Nat), g3 n = k3 n

@[blaster]
axiom k3_f3 : ∀ (n : Nat), k3 n = f3 n

/--
warning: [blaster]: Cyclic rewriting detected on f3 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
---
warning: [blaster]: Cyclic rewriting detected on f3 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
-/
#guard_msgs (warning) in
#testOptimize [ "ExtCyclic3_1" ] (norm-result: 1) ∀ (m : Nat), f3 5 = m ===> ∀ (m : Nat), m = k3 5

/--
warning: [blaster]: Cyclic rewriting detected on k3 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
---
warning: [blaster]: Cyclic rewriting detected on k3 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
-/
#guard_msgs (warning) in
#testOptimize [ "ExtCyclic3_2" ] (norm-result: 1) ∀ (m : Nat), k3 5 = m ===> ∀ (m : Nat), m = g3 5

/-! Cycle closed by a premise: without the hypothesis the first rule does not fire and there is no
    cycle. With the hypothesis the premise `c 5` only holds once the literal is normalized (the
    first rule fires when the application is finalized): the cycle closes on `g5 5`, reported once,
    and `f5 5` is kept. -/
axiom f5 : Nat → Nat
axiom g5 : Nat → Nat

@[blaster]
axiom f5_g5 : ∀ (n : Nat), c n → f5 n = g5 n

@[blaster]
axiom g5_f5 : ∀ (n : Nat), g5 n = f5 n

/--
warning: [blaster]: Cyclic rewriting detected on g5 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
-/
#guard_msgs (warning) in
#testOptimize [ "ExtCyclicPrem_1" ] (norm-result: 1) ∀ (m : Nat), c 5 → f5 5 = m ===> ∀ (m : Nat), c 5 → m = f5 5

-- premise not available: no rewriting, no cycle
#testOptimize [ "ExtCyclicPrem_2" ] (norm-result: 1) ∀ (m : Nat), f5 5 = m ===> ∀ (m : Nat), m = f5 5

-- `g5 5` is rewritten to `f5 5`, on which the first rule does not fire
#testOptimize [ "ExtCyclicPrem_3" ] (norm-result: 1) ∀ (m : Nat), g5 5 = m ===> ∀ (m : Nat), m = f5 5

/-! Cycle between `Iff` rules (predicate rewriting). -/
axiom P6 : Nat → Prop
axiom Q6 : Nat → Prop

@[blaster]
axiom P6_Q6 : ∀ (n : Nat), P6 n ↔ Q6 n

@[blaster]
axiom Q6_P6 : ∀ (n : Nat), Q6 n ↔ P6 n

/--
warning: [blaster]: Cyclic rewriting detected on P6 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
---
warning: [blaster]: Cyclic rewriting detected on P6 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
-/
#guard_msgs (warning) in
#testOptimize [ "ExtCyclicIff_1" ] (norm-result: 1) P6 5 ===> Q6 5

/--
warning: [blaster]: Cyclic rewriting detected on Q6 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
---
warning: [blaster]: Cyclic rewriting detected on Q6 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
-/
#guard_msgs (warning) in
#testOptimize [ "ExtCyclicIff_2" ] (norm-result: 1) Q6 5 ===> P6 5

/-! A single rule swapping its arguments cycles with itself. -/
axiom f8 : Nat → Nat → Nat

@[blaster]
axiom f8_swap : ∀ (n m : Nat), f8 n m = f8 m n

/--
warning: [blaster]: Cyclic rewriting detected on f8 1 2.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
---
warning: [blaster]: Cyclic rewriting detected on f8 1 2.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
-/
#guard_msgs (warning) in
#testOptimize [ "ExtCyclicSwap_1" ] (norm-result: 1) ∀ (z : Nat), f8 1 2 = z ===> ∀ (z : Nat), z = f8 2 1

-- `f8 2 1` is found in the optimization cache (`f8 2 1 ↦ f8 1 2`): `f8 1 2 = f8 1 2` reduces to `True`
/--
warning: [blaster]: Cyclic rewriting detected on f8 1 2.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
---
warning: [blaster]: Cyclic rewriting detected on f8 1 2.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
-/
#guard_msgs (warning) in
#testOptimize [ "ExtCyclicSwap_2" ] f8 1 2 = f8 2 1 ===> True

/-! The lhs occurs in the rhs: the rule fires on the outer `f10 5` and again on the inner occurrence
    while the arguments of the rhs are optimized; the cycle is detected when the inner occurrence is
    rewritten to `Nat.add 1 (f10 5)`, which is still being optimized. The rule is thus applied once
    at each level and `Nat.add 1 (Nat.add 1 (f10 5))` is folded to `Nat.add 2 (f10 5)`. -/
axiom f10 : Nat → Nat

@[blaster]
axiom f10_grow : ∀ (n : Nat), f10 n = Nat.add 1 (f10 n)

/--
warning: [blaster]: Cyclic rewriting detected on Nat.add 1 (f10 5).
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
---
warning: [blaster]: Cyclic rewriting detected on Nat.add 1 (f10 5).
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
-/
#guard_msgs (warning) in
#testOptimize [ "ExtCyclicGrow_1" ] (norm-result: 1)
  ∀ (m : Nat), f10 5 = m ===> ∀ (m : Nat), m = Nat.add 2 (f10 5)

/-! Controls: chains of rules that terminate must not be reported. -/

/-! Acyclic chain `f7 ↦ g7 ↦ k7`. -/
axiom f7 : Nat → Nat
axiom g7 : Nat → Nat
axiom k7 : Nat → Nat

@[blaster]
axiom f7_g7 : ∀ (n : Nat), f7 n = g7 n

@[blaster]
axiom g7_k7 : ∀ (n : Nat), g7 n = k7 n

#guard_msgs (warning) in
#testOptimize [ "ExtCyclicChain_1" ] (norm-result: 1) ∀ (m : Nat), f7 5 = m ===> ∀ (m : Nat), m = k7 5
#guard_msgs (warning) in
#testOptimize [ "ExtCyclicChain_2" ] (norm-result: 1) f7 5 = f7 6 ===> k7 5 = k7 6
#guard_msgs (warning) in
#testOptimize [ "ExtCyclicChain_3" ] f7 5 = g7 5 ===> True

/-! The same rule fired repeatedly on a decreasing argument. -/
axiom len : List Nat → Nat

@[blaster]
axiom len_cons : ∀ (a : Nat) (xs : List Nat), len (a :: xs) = Nat.add 1 (len xs)

@[blaster (noRestart := true)]
axiom len_nil : len [] = 0

#guard_msgs (warning) in
#testOptimize [ "ExtCyclicDecr_1" ] (norm-result: 1) ∀ (m : Nat), len [1, 2, 3] = m ===> ∀ (m : Nat), 3 = m
-- NOTE: the unused binder `a` is removed by the optimizer
#guard_msgs (warning) in
#testOptimize [ "ExtCyclicDecr_2" ] (norm-result: 1) ∀ (a : Nat) (xs : List Nat) (m : Nat), len (a :: xs) = m ===> ∀ (xs : List Nat) (m : Nat), m = Nat.add 1 (len xs)

end Test.ExtensionCyclic
