import Lean
import Tests.Utils
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Test.ExtensionStatic

/-! ## Static detection of cyclic rewriting

Before the optimization function of a tagged theorem is generated, the rule is checked against the
rules previously generated (`Blaster.ThmOptFn.findCyclicRewriting`, see
`Blaster.Optimize.Env.ExtensionRules`): there is an edge `A ⟶ B` when the lhs pattern of `B`
matches a sub-term of the rhs of `A`, either as stored (the term handed to the matcher before its
arguments are normalized) or normalized with unfolding of the non-recursive functions (the term
handed to the matcher once its arguments are normalized). Only the pattern variables of `B` may be
instantiated, the variables of the rhs of `A` are rigid. When a path leads from the new rule back
to itself, a warning is logged and no optimization function is generated: the previously generated
rules are kept and the optimization goes on with them.

The check is an over-approximation: premises are ignored and a chain of rules is only reported when
it closes on the new rule. Option `(cyclicCheck := false)` skips the check for a theorem, which is
then only protected by the run-time check (see `ExtensionCyclic.lean`); the theorem is still recorded
for the check of the subsequent ones.
-/

axiom c : Nat → Prop

/-! Two rules rewriting into each other: the second one closes the cycle and is not generated. -/
axiom f1 : Nat → Nat
axiom g1 : Nat → Nat

@[blaster]
axiom f1_g1 : ∀ (n : Nat), f1 n = g1 n

/--
warning: [blaster]: Cyclic rewriting detected: `Test.ExtensionStatic.g1_f1` ↦ `Test.ExtensionStatic.f1_g1` ↦ `Test.ExtensionStatic.g1_f1` (the rhs of each rule contains an instance of the lhs of the next one).
No optimization function generated for `Test.ExtensionStatic.g1_f1`.
-/
#guard_msgs (warning) in
@[blaster]
axiom g1_f1 : ∀ (n : Nat), g1 n = f1 n

-- `f1_g1` is applied, `g1_f1` is not registered: no run-time cycle, no warning
#testOptimize [ "ExtStatic_1" ] (norm-result: 1) ∀ (m : Nat), f1 5 = m ===> ∀ (m : Nat), m = g1 5
#testOptimize [ "ExtStatic_2" ] (norm-result: 1) ∀ (m : Nat), g1 5 = m ===> ∀ (m : Nat), m = g1 5

/-! Growing cycle: the run-time check cannot detect it (the rewritten terms are never identical),
    the static check does. -/
axiom f2 : Nat → Nat
axiom g2 : Nat → Nat

@[blaster]
axiom f2_g2 : ∀ (n : Nat), f2 n = g2 n

/--
warning: [blaster]: Cyclic rewriting detected: `Test.ExtensionStatic.g2_f2` ↦ `Test.ExtensionStatic.f2_g2` ↦ `Test.ExtensionStatic.g2_f2` (the rhs of each rule contains an instance of the lhs of the next one).
No optimization function generated for `Test.ExtensionStatic.g2_f2`.
-/
#guard_msgs (warning) in
@[blaster]
axiom g2_f2 : ∀ (n : Nat), g2 n = f2 (Nat.add 1 n)

#testOptimize [ "ExtStaticGrow_1" ] (norm-result: 1) ∀ (m : Nat), f2 5 = m ===> ∀ (m : Nat), m = g2 5

/-! Rule whose lhs is an instance of a sub-term of its own rhs. -/
axiom f3 : Nat → Nat

/--
warning: [blaster]: Cyclic rewriting detected: `Test.ExtensionStatic.f3_grow` ↦ `Test.ExtensionStatic.f3_grow` (the rhs of each rule contains an instance of the lhs of the next one).
No optimization function generated for `Test.ExtensionStatic.f3_grow`.
-/
#guard_msgs (warning) in
@[blaster]
axiom f3_grow : ∀ (n : Nat), f3 n = Nat.add 1 (f3 n)

#testOptimize [ "ExtStaticSelf_1" ] (norm-result: 1) ∀ (m : Nat), f3 5 = m ===> ∀ (m : Nat), m = f3 5

/-! Three-rule cycle: the last rule is the one reported. -/
axiom f4 : Nat → Nat
axiom g4 : Nat → Nat
axiom k4 : Nat → Nat

@[blaster]
axiom f4_g4 : ∀ (n : Nat), f4 n = g4 n

@[blaster]
axiom g4_k4 : ∀ (n : Nat), g4 n = k4 n

/--
warning: [blaster]: Cyclic rewriting detected: `Test.ExtensionStatic.k4_f4` ↦ `Test.ExtensionStatic.f4_g4` ↦ `Test.ExtensionStatic.g4_k4` ↦ `Test.ExtensionStatic.k4_f4` (the rhs of each rule contains an instance of the lhs of the next one).
No optimization function generated for `Test.ExtensionStatic.k4_f4`.
-/
#guard_msgs (warning) in
@[blaster]
axiom k4_f4 : ∀ (n : Nat), k4 n = f4 n

#testOptimize [ "ExtStatic3_1" ] (norm-result: 1) ∀ (m : Nat), f4 5 = m ===> ∀ (m : Nat), m = k4 5

/-! Chains are not cycles, whatever the registration order. -/
axiom f5 : Nat → Nat
axiom g5 : Nat → Nat
axiom k5 : Nat → Nat

@[blaster]
axiom g5_k5 : ∀ (n : Nat), g5 n = k5 n

@[blaster]
axiom f5_g5 : ∀ (n : Nat), f5 n = g5 n

#testOptimize [ "ExtStaticChain_1" ] (norm-result: 1) ∀ (m : Nat), f5 5 = m ===> ∀ (m : Nat), m = k5 5

/-! Structurally decreasing rules: the variables of the rhs are rigid, `len xs` is not an instance of
    `len (?a :: ?xs)`. -/
axiom len : List Nat → Nat

@[blaster]
axiom len_cons : ∀ (a : Nat) (xs : List Nat), len (a :: xs) = Nat.add 1 (len xs)

@[blaster (noRestart := true)]
axiom len_nil : len [] = 0

#testOptimize [ "ExtStaticDecr_1" ] (norm-result: 1) ∀ (m : Nat), len [1, 2] = m ===> ∀ (m : Nat), 2 = m

axiom f6 : Nat → Nat

@[blaster]
axiom f6_pred : ∀ (n : Nat), f6 (Nat.add 1 n) = Nat.add 1 (f6 n)

#testOptimize [ "ExtStaticDecr_2" ] (norm-result: 1) ∀ (n m : Nat), f6 (Nat.add 1 n) = m ===> ∀ (n m : Nat), m = Nat.add 1 (f6 n)

/-! Non-linear patterns: `f7 ?n ?n` is not an instance of `f7 n (Nat.add 1 n)`. -/
axiom f7 : Nat → Nat → Nat
axiom g7 : Nat → Nat

@[blaster]
axiom f7_g7 : ∀ (n : Nat), f7 n n = g7 n

@[blaster]
axiom g7_f7 : ∀ (n : Nat), g7 n = f7 n (Nat.add 1 n)

#testOptimize [ "ExtStaticNonLinear_1" ] (norm-result: 1) ∀ (m : Nat), f7 5 5 = m ===> ∀ (m : Nat), m = f7 5 6

/-! Literal patterns: `f8 0` is not an instance of `f8 (Nat.add 1 n)`. -/
axiom f8 : Nat → Nat
axiom g8 : Nat → Nat

@[blaster]
axiom f8_g8 : f8 0 = g8 0

@[blaster]
axiom g8_f8 : ∀ (n : Nat), g8 n = f8 (Nat.add 1 n)

#testOptimize [ "ExtStaticLit_1" ] (norm-result: 1) ∀ (m : Nat), f8 0 = m ===> ∀ (m : Nat), m = f8 1

/-! Edge visible only once the rhs is unfolded: `g9 (wrap n)` is stored as is, whereas the matcher
    is handed `g9 (Nat.add 1 n)` once the argument is normalized. -/
def wrap (n : Nat) : Nat := Nat.add 1 n

axiom f9 : Nat → Nat
axiom g9 : Nat → Nat

@[blaster]
axiom f9_g9 : ∀ (n : Nat), f9 n = g9 (wrap n)

/--
warning: [blaster]: Cyclic rewriting detected: `Test.ExtensionStatic.g9_f9` ↦ `Test.ExtensionStatic.f9_g9` ↦ `Test.ExtensionStatic.g9_f9` (the rhs of each rule contains an instance of the lhs of the next one).
No optimization function generated for `Test.ExtensionStatic.g9_f9`.
-/
#guard_msgs (warning) in
@[blaster]
axiom g9_f9 : ∀ (n : Nat), g9 (Nat.add 1 n) = f9 n

/-! A registered head that is a non-recursive definition is not unfolded in the rhs, even when it is only
    revealed by unfolding a wrapper: at run time its rules are tried on its normalized arguments before it is
    unfolded (`g17 n ↦ wrap17 n ↦ f17 (Nat.add 1 n) ↦ g17 n`). -/
def f17 (n : Nat) : Nat := n
axiom g17 : Nat → Nat
def wrap17 (n : Nat) : Nat := f17 (Nat.add 1 n)

@[blaster]
axiom f17_g17 : ∀ (m : Nat), f17 (Nat.add 1 m) = g17 m

/--
warning: [blaster]: Cyclic rewriting detected: `Test.ExtensionStatic.g17_f17` ↦ `Test.ExtensionStatic.f17_g17` ↦ `Test.ExtensionStatic.g17_f17` (the rhs of each rule contains an instance of the lhs of the next one).
No optimization function generated for `Test.ExtensionStatic.g17_f17`.
-/
#guard_msgs (warning) in
@[blaster]
axiom g17_f17 : ∀ (n : Nat), g17 n = wrap17 n

/-! Premises are ignored: a cycle closed by rules whose premises are never satisfied together is reported. -/
axiom f10 : Nat → Nat
axiom g10 : Nat → Nat

@[blaster]
axiom f10_g10 : ∀ (n : Nat), c n → f10 n = g10 n

/--
warning: [blaster]: Cyclic rewriting detected: `Test.ExtensionStatic.g10_f10` ↦ `Test.ExtensionStatic.f10_g10` ↦ `Test.ExtensionStatic.g10_f10` (the rhs of each rule contains an instance of the lhs of the next one).
No optimization function generated for `Test.ExtensionStatic.g10_f10`.
-/
#guard_msgs (warning) in
@[blaster]
axiom g10_f10 : ∀ (n : Nat), ¬ c n → g10 n = f10 n

/-! Equivalences and argument swapping. -/
axiom P11 : Nat → Prop
axiom Q11 : Nat → Prop

@[blaster]
axiom P11_Q11 : ∀ (n : Nat), P11 n ↔ Q11 n

/--
warning: [blaster]: Cyclic rewriting detected: `Test.ExtensionStatic.Q11_P11` ↦ `Test.ExtensionStatic.P11_Q11` ↦ `Test.ExtensionStatic.Q11_P11` (the rhs of each rule contains an instance of the lhs of the next one).
No optimization function generated for `Test.ExtensionStatic.Q11_P11`.
-/
#guard_msgs (warning) in
@[blaster]
axiom Q11_P11 : ∀ (n : Nat), Q11 n ↔ P11 n

axiom f12 : Nat → Nat → Nat

/--
warning: [blaster]: Cyclic rewriting detected: `Test.ExtensionStatic.f12_swap` ↦ `Test.ExtensionStatic.f12_swap` (the rhs of each rule contains an instance of the lhs of the next one).
No optimization function generated for `Test.ExtensionStatic.f12_swap`.
-/
#guard_msgs (warning) in
@[blaster]
axiom f12_swap : ∀ (n m : Nat), f12 n m = f12 m n

/-! Sub-terms under binders are examined. -/
axiom f13 : Nat → List Nat
axiom g13 : Nat → Nat

@[blaster]
axiom f13_g13 : ∀ (n : Nat), f13 n = List.map (fun x => g13 x) [n]

/--
warning: [blaster]: Cyclic rewriting detected: `Test.ExtensionStatic.g13_f13` ↦ `Test.ExtensionStatic.f13_g13` ↦ `Test.ExtensionStatic.g13_f13` (the rhs of each rule contains an instance of the lhs of the next one).
No optimization function generated for `Test.ExtensionStatic.g13_f13`.
-/
#guard_msgs (warning) in
@[blaster]
axiom g13_f13 : ∀ (n : Nat), g13 n = List.length (f13 n)

/-! Option `(cyclicCheck := false)`: the cycle is only detected at run time. -/
axiom f14 : Nat → Nat
axiom g14 : Nat → Nat

@[blaster]
axiom f14_g14 : ∀ (n : Nat), f14 n = g14 n

@[blaster (cyclicCheck := false)]
axiom g14_f14 : ∀ (n : Nat), g14 n = f14 n

/--
warning: [blaster]: Cyclic rewriting detected on f14 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
---
warning: [blaster]: Cyclic rewriting detected on f14 5.
Verify tagged [@blaster] theorems/axioms for cyclic dependencies.
-/
#guard_msgs (warning) in
#testOptimize [ "ExtStaticNoCheck_1" ] (norm-result: 1) ∀ (m : Nat), f14 5 = m ===> ∀ (m : Nat), m = g14 5

/-! A theorem tagged with `(cyclicCheck := false)` is still recorded for the subsequent checks. -/
axiom g15 : Nat → Nat
axiom k15 : Nat → Nat

@[blaster (cyclicCheck := false)]
axiom g15_k15 : ∀ (n : Nat), g15 n = k15 n

/--
warning: [blaster]: Cyclic rewriting detected: `Test.ExtensionStatic.k15_g15` ↦ `Test.ExtensionStatic.g15_k15` ↦ `Test.ExtensionStatic.k15_g15` (the rhs of each rule contains an instance of the lhs of the next one).
No optimization function generated for `Test.ExtensionStatic.k15_g15`.
-/
#guard_msgs (warning) in
@[blaster]
axiom k15_g15 : ∀ (n : Nat), k15 n = g15 n

/-! A theorem tagged with `(register := false)` is recorded as well (it is applied through a hand-written
    optimization function). -/
axiom f16 : Nat → Nat
axiom g16 : Nat → Nat

@[blaster (register := false)]
axiom f16_g16 : ∀ (n : Nat), f16 n = g16 n

/--
warning: [blaster]: Cyclic rewriting detected: `Test.ExtensionStatic.g16_f16` ↦ `Test.ExtensionStatic.f16_g16` ↦ `Test.ExtensionStatic.g16_f16` (the rhs of each rule contains an instance of the lhs of the next one).
No optimization function generated for `Test.ExtensionStatic.g16_f16`.
-/
#guard_msgs (warning) in
@[blaster]
axiom g16_f16 : ∀ (n : Nat), g16 n = f16 n

/-! Target head under an `ite`: the rules are tried before the arguments are normalized, an unguarded
    recursion unrolls forever on a symbolic argument. The sub-terms of the branches are examined. -/
axiom f18 : Nat → Nat

/--
warning: [blaster]: Cyclic rewriting detected: `Test.ExtensionStatic.f18_ite` ↦ `Test.ExtensionStatic.f18_ite` (the rhs of each rule contains an instance of the lhs of the next one).
No optimization function generated for `Test.ExtensionStatic.f18_ite`.
-/
#guard_msgs (warning) in
@[blaster]
axiom f18_ite : ∀ (n : Nat), f18 n = if n = 0 then 0 else f18 (Nat.sub n 1)

-- structurally decreasing under an `ite`: no cycle
axiom f19 : Nat → Nat

@[blaster]
axiom f19_ite : ∀ (n : Nat), f19 (Nat.add 1 n) = if n = 0 then 0 else f19 n

#testOptimize [ "ExtStaticIte_1" ] (norm-result: 1) ∀ (n m : Nat), f19 (Nat.add 1 n) = m ===> ∀ (n m : Nat), m = Blaster.dite' (0 = n) (fun _ => 0) (fun _ => f19 n)

-- cycle through two rules, one of them under an `ite`
axiom f20 : Nat → Nat
axiom g20 : Nat → Nat

@[blaster]
axiom f20_g20 : ∀ (n : Nat), f20 n = if n = 0 then g20 n else 0

/--
warning: [blaster]: Cyclic rewriting detected: `Test.ExtensionStatic.g20_f20` ↦ `Test.ExtensionStatic.f20_g20` ↦ `Test.ExtensionStatic.g20_f20` (the rhs of each rule contains an instance of the lhs of the next one).
No optimization function generated for `Test.ExtensionStatic.g20_f20`.
-/
#guard_msgs (warning) in
@[blaster]
axiom g20_f20 : ∀ (n : Nat), g20 n = f20 n

/-! Target head under a `match`: the alternatives are examined (the pattern variables of the
    alternatives are bound variables, which an argument of the lhs pattern may match). -/
axiom len21 : List Nat → Nat

/--
warning: [blaster]: Cyclic rewriting detected: `Test.ExtensionStatic.len21_match` ↦ `Test.ExtensionStatic.len21_match` (the rhs of each rule contains an instance of the lhs of the next one).
No optimization function generated for `Test.ExtensionStatic.len21_match`.
-/
#guard_msgs (warning) in
@[blaster]
axiom len21_match : ∀ (a : Nat) (xs : List Nat),
  len21 (a :: xs) = match xs with
                    | [] => 1
                    | b :: ys => Nat.add 1 (len21 (b :: ys))

-- structurally decreasing under a `match`: no cycle
axiom len22 : List Nat → Nat

@[blaster]
axiom len22_match : ∀ (a : Nat) (xs : List Nat),
  len22 (a :: xs) = match xs with
                    | [] => 1
                    | _ :: ys => Nat.add 2 (len22 ys)

#testOptimize [ "ExtStaticMatch_1" ] (norm-result: 1) ∀ (m : Nat), len22 [1, 2, 3] = m ===> ∀ (m : Nat), 3 = m

/-! Rules on recursive definitions: the definition is not unfolded by the optimizer, its rules are. -/
def sum23 : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.add x (sum23 xs)

@[blaster]
axiom sum23_cons : ∀ (x : Nat) (xs : List Nat), sum23 (x :: xs) = Nat.add x (sum23 xs)

@[blaster]
axiom sum23_nil : sum23 [] = 0

#testOptimize [ "ExtStaticRec_1" ] (norm-result: 1) ∀ (m : Nat), sum23 [1, 2] = m ===> ∀ (m : Nat), 3 = m

def sum24 : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.add x (sum24 xs)

/--
warning: [blaster]: Cyclic rewriting detected: `Test.ExtensionStatic.sum24_grow` ↦ `Test.ExtensionStatic.sum24_grow` (the rhs of each rule contains an instance of the lhs of the next one).
No optimization function generated for `Test.ExtensionStatic.sum24_grow`.
-/
#guard_msgs (warning) in
@[blaster]
axiom sum24_grow : ∀ (xs : List Nat), sum24 xs = sum24 (0 :: xs)

-- cycle between a rule on a recursive definition and a rule on an axiom
def sum25 : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.add x (sum25 xs)
axiom g25 : List Nat → Nat

@[blaster]
axiom sum25_g25 : ∀ (xs : List Nat), sum25 xs = g25 xs

/--
warning: [blaster]: Cyclic rewriting detected: `Test.ExtensionStatic.g25_sum25` ↦ `Test.ExtensionStatic.sum25_g25` ↦ `Test.ExtensionStatic.g25_sum25` (the rhs of each rule contains an instance of the lhs of the next one).
No optimization function generated for `Test.ExtensionStatic.g25_sum25`.
-/
#guard_msgs (warning) in
@[blaster]
axiom g25_sum25 : ∀ (xs : List Nat), g25 xs = sum25 (List.reverseAux xs [])

def g (x y : Nat) : Nat := x + y

/--
warning: [blaster]: Cyclic rewriting detected: `Test.ExtensionStatic.g_comm` ↦ `Test.ExtensionStatic.g_comm` (the rhs of each rule contains an instance of the lhs of the next one).
No optimization function generated for `Test.ExtensionStatic.g_comm`.
-/
#guard_msgs (warning) in
@[blaster]
theorem g_comm (x y : Nat) : g x y = g y x := Nat.add_comm x y

axiom myF : Nat → Nat → Nat
/--
warning: [blaster]: Cyclic rewriting detected: `Test.ExtensionStatic.myF_comm` ↦ `Test.ExtensionStatic.myF_comm` (the rhs of each rule contains an instance of the lhs of the next one).
No optimization function generated for `Test.ExtensionStatic.myF_comm`.
-/
#guard_msgs (warning) in
@[blaster] axiom myF_comm : ∀ x y, myF x y = myF y x

end Test.ExtensionStatic
