import Tests.Utils

namespace Tests.SpecializeMatch

inductive Symbolic where
  | bool : Bool → Symbolic
  | nat : Nat → Symbolic

-- Tail recursion also keeps native module initialization safe when Lean lifts the
-- closed calls below. Symbolic unfolding still requires a million recursive steps.
def workAux : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => workAux n (acc + 1)

-- The cost of this branch must not affect a match on a different constructor.
def work (n : Nat) : Nat := workAux n 0

def minimal : Symbolic → Nat
  | .bool false => 0
  | .bool true => 1
  | .nat _ => work 1000000

#testOptimize ["Specialize_dummy_alternative_parameter"]
  ∀ (b : Bool), minimal (.bool b) = (if b then 1 else 0) ===> True

inductive Value (α : Type) where
  | pair : Bool → α → Value α
  | other : Nat → Value α

def select : Value Nat → Nat
  | .pair false x => x
  | .pair true x => x + 1
  | .other _ => work 1000000

#testOptimize ["Specialize_unreachable_body"]
  ∀ (b : Bool) (n : Nat), select (.pair b n) = (if b then n + 1 else n) ===> True

-- The same matcher is called with different known constructors in one optimization.
#testOptimize ["Specialize_call_specific"]
  ∀ (b : Bool) (n : Nat), select (.pair b n) = (if b then n + 1 else n) ∧
    select (.pair (!b) n) = (if !b then n + 1 else n) ===> True

def ordered : Value Nat → Bool → Nat
  | .pair false x, _ => x
  | .pair _ x, false => x + 1
  | .pair _ x, true => x + 2
  | .other _, _ => work 1000000

#testOptimize ["Specialize_order_and_multiple_discriminators"]
  ∀ (b c : Bool) (n : Nat), ordered (.pair b n) c =
    (if b then (if c then n + 2 else n + 1) else n) ===> True

def polymorphic (fallback : α) : Value α → α
  | .pair false x => x
  | .pair true _ => fallback
  | .other _ => fallback

#testOptimize ["Specialize_type_parameters"]
  ∀ (α : Type) (fallback x : α) (b : Bool), polymorphic fallback (.pair b x) =
    (if b then fallback else x) ===> True

def nested : Option (Value Nat) → Nat
  | some (.pair false x) => x
  | some (.pair true x) => x + 1
  | some (.other _) => work 1000000
  | none => 42

#testOptimize ["Specialize_nested_constructors"]
  ∀ (b : Bool) (n : Nat), nested (some (.pair b n)) = (if b then n + 1 else n) ===> True

-- A compatible expensive branch must remain reachable.
def reachable : Value Nat → Nat
  | .pair false _ => 0
  | .pair true x => work x
  | .other _ => 2

#testOptimize ["Specialize_reachable_branch"]
  ∀ (b : Bool), reachable (.pair b 3) = (if b then 3 else 0) ===> True

#testOptimize ["Specialize_negative_control"]
  ∀ (b : Bool), reachable (.pair b 3) = 0 ===> ∀ (b : Bool), false = b

#testOptimize ["Specialize_branch_contexts"]
  ∀ (b : Bool), (if b then reachable (.pair b 3) else reachable (.pair b 0)) =
    (if b then 3 else 0) ===> True

#testOptimize ["Specialize_different_constructors"]
  ∀ (b : Bool), reachable (.pair b 3) = (if b then 3 else 0) ∧
    reachable (.other 7) = 2 ===> True

-- Unknown nested constructors require extraction: preserve the existing matcher.
def extract : Option (Option Nat) → Nat
  | some (some n) => n
  | some none => 0
  | none => 1

#testOptimize ["Specialize_unknown_fields_fallback"] (norm-result: 1)
  ∀ (x : Option Nat), extract (some x) = 2 ===>
    ∀ (x : Option Nat), 2 = (match some x with
      | some (some n) => n
      | some none => 0
      | none => 1)

-- Dependent constructor fields and indexed families are outside this pass.
def dependentFields : Sigma (fun b : Bool => if b then Nat else Bool) → Nat
  | ⟨false, false⟩ => 0
  | ⟨false, true⟩ => 1
  | ⟨true, n⟩ => n

#testOptimize ["Specialize_dependent_fields_fallback"]
  ((∀ (b : Bool), dependentFields ⟨false, b⟩ = (if b then 1 else 0)) =
    (∀ (b : Bool), ((match (⟨false, b⟩ : Sigma (fun b : Bool => if b then Nat else Bool)) with
       | ⟨false, false⟩ => 0
       | ⟨false, true⟩ => 1
       | ⟨true, n⟩ => n) : Nat) = (if b then 1 else 0))) ===> True

inductive Tagged : Nat → Type where
  | item : Bool → Tagged 0

def indexed : Tagged 0 → Nat
  | .item false => 0
  | .item true => 1

#testOptimize ["Specialize_indexed_family_fallback"]
  ∀ (b : Bool), indexed (.item b) = 2 ===> False

-- Independent kernel checks for the equations used as optimization regressions.
example (b : Bool) : minimal (.bool b) = (if b then 1 else 0) := by
  cases b <;> rfl

example (b : Bool) (n : Nat) : select (.pair b n) = (if b then n + 1 else n) := by
  cases b <;> rfl

example (b c : Bool) (n : Nat) : ordered (.pair b n) c =
    (if b then (if c then n + 2 else n + 1) else n) := by
  cases b <;> cases c <;> rfl

example (α : Type) (fallback x : α) (b : Bool) :
    polymorphic fallback (.pair b x) = (if b then fallback else x) := by
  cases b <;> rfl

example (b : Bool) (n : Nat) : nested (some (.pair b n)) = (if b then n + 1 else n) := by
  cases b <;> rfl

example (b : Bool) : reachable (.pair b 3) = (if b then 3 else 0) := by
  cases b <;> rfl

example (b : Bool) : dependentFields ⟨false, b⟩ = (if b then 1 else 0) := by
  cases b <;> rfl

example (b : Bool) : indexed (.item b) ≠ 2 := by
  cases b <;> decide

end Tests.SpecializeMatch
