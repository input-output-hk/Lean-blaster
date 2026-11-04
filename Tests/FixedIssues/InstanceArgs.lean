import Lean
import Blaster

namespace Tests.InstanceArgs

-- Issue: Unexpected Valid for falsifiable goals with instances that are not the canonical ones.
-- Diagnosis: `@LT.lt α inst` (resp. `LE.le`) was taken as the relation of the SMT theory for `α ∈ [Nat, Int, Bool,
--            String]` whatever `inst`, and the instance arguments of function values (e.g., a structure field
--            `f [LT α] : α → α`) are erased by the translation. Other instances of `LT`/`LE` are now unfolded, and
--            applications of function values are only translated with canonical (or local) instances.

def lt1 : LT Nat := ⟨fun a b => a < b⟩
def lt2 : LT Nat := ⟨fun a b => b < a⟩

def g {α : Type} [LT α] [DecidableRel (α := α) (· < ·)] (x y : α) : Bool := decide (x < y)

instance d1 : @DecidableRel Nat Nat (@LT.lt Nat lt1) := fun a b => Nat.decLt a b
instance d2 : @DecidableRel Nat Nat (@LT.lt Nat lt2) := fun a b => Nat.decLt b a

theorem g_differ : ¬ ∀ (x y : Nat), @g Nat lt1 d1 x y = @g Nat lt2 d2 x y :=
  fun h => absurd (h 1 2) (by decide)

#blaster (gen-cex: 0) (solve-result: 1) (timeout: 10) [∀ (x y : Nat), @g Nat lt1 d1 x y = @g Nat lt2 d2 x y]

-- Valid expected: the canonical instance and an equivalent definition
#blaster [∀ (x y : Nat), @g Nat lt1 d1 x y = decide (x < y)]

structure FunRel where
  f [LT α] : α → α

-- Valid expected: canonical and local instances
#blaster [∀ (r : FunRel) (x y : Nat), x = y → r.f x = r.f y]
#blaster [∀ (α : Type) [LT α] (r : FunRel) (x : α), r.f x = r.f x]

/-! Relations of the SMT theories only for the canonical instances of `LT`/`LE`. -/

def revLT : LT Nat := ⟨fun a b => b < a⟩
def revLE : LE Nat := ⟨fun a b => b ≤ a⟩
def trueLT : LT Int := ⟨fun _ _ => True⟩

theorem revLT_counterexample : ¬ ¬ (@LT.lt Nat revLT 1 0) := fun h => h (show 0 < 1 from Nat.zero_lt_one)

#blaster (gen-cex: 0) (solve-result: 1) [¬ (@LT.lt Nat revLT 1 0)]

theorem revLT_forall_counterexample : ¬ (∀ x : Nat, ¬ (@LT.lt Nat revLT 0 x) → 0 = x) :=
  fun h => absurd (h 1 (fun (hx : 1 < 0) => absurd hx (by decide))) (by decide)

#blaster (gen-cex: 0) (solve-result: 1) [∀ x : Nat, ¬ (@LT.lt Nat revLT 0 x) → 0 = x]

theorem revLE_counterexample : ¬ (@LE.le Nat revLE 0 1) := fun (h : 1 ≤ 0) => absurd h (by decide)

#blaster (gen-cex: 0) (solve-result: 1) [@LE.le Nat revLE 0 1]

theorem trueLT_counterexample : ¬ (∀ x y : Int, (@LT.lt Int trueLT x y) → x < y) :=
  fun h => absurd (h 0 0 trivial) (by decide)

#blaster (gen-cex: 0) (solve-result: 1) [∀ x y : Int, (@LT.lt Int trueLT x y) → x < y]

-- Valid expected: the canonical instances
#blaster [∀ x y : Nat, x < y → ¬ (y < x)]
#blaster [∀ x y : Int, x ≤ y → y ≤ x → x = y]

/-! Instance arguments of function values: a function of type `[Inhabited Nat] → Nat → Nat` applied to two different
    instances. The application is only translated with canonical (or local) instances: an error is reported otherwise,
    instead of the unsound `Valid` result. -/

theorem inhabited_args_counterexample : ¬ (∀ (f : [Inhabited Nat] → Nat → Nat), @f ⟨0⟩ 3 = @f ⟨1⟩ 3) :=
  fun h => absurd (h (fun [i : Inhabited Nat] _ => i.default)) (by decide)

/--
error: createAppNAux: non-canonical instance argument of a function value { default := 0 }
-/
#guard_msgs (error, drop info) in
#blaster [∀ (f : [Inhabited Nat] → Nat → Nat), @f ⟨0⟩ 3 = @f ⟨1⟩ 3]

end Tests.InstanceArgs
