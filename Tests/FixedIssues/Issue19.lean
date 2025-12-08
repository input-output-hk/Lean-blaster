import Lean
import Blaster

namespace Tests.Issue19

-- Issue: Unexpected smt error: (error "line 14 column 202: as-array takes one parameter, a function declaration with arity greater than zero")
-- Diagnosis : We must properly handle function using ArrowT type representation at smt level.

class Group (G : Type) where
  neutral : G                  -- Neutral element
  inv : G → G              -- Inverse function
  op : G → G → G          -- Binary op

def op_assoc (G : Type) [Group G] (a b c : G): Prop :=
   Group.op a (Group.op b c) = Group.op (Group.op a b) c

def neutral_op (G : Type) [Group G] (a : G): Prop :=
   Group.op Group.neutral a = a

def op_neutral (G : Type) [Group G] (a : G) : Prop :=
  Group.op a Group.neutral = a

def op_left_inv (G : Type) [Group G] (a : G): Prop :=
   Group.op (Group.inv a) a = Group.neutral

theorem uniqueness_neutral_gen : ∀ (G : Type) [Group G] (a : G),
  (op_neutral G a) →  (op_left_inv G a) → (neutral_op G a) →

  ((∀ (b : G), Group.op a b = b) → a = Group.neutral) :=
      by
        intros G instG a h_op_neutral h_op_left_inv h_neutral_op hb
        simp [op_neutral] at h_op_neutral
        simp [op_left_inv] at h_op_left_inv
        simp [neutral_op] at h_neutral_op
        have h_specific := hb Group.neutral
        rw [h_op_neutral] at h_specific
        exact h_specific

#blaster [uniqueness_neutral_gen]

end Tests.Issue19
