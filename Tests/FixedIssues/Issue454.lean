import Lean
import Blaster
import Tests.Utils

namespace Tests.Issue454

-- Issue: https://github.com/input-output-hk/Lean-blaster/issues/454
--        a datatype was declared with the parameter names of an earlier alpha-equivalent
--        inductive, while its constructors' fields used its own: any goal with both `Except`
--        and `Prod` (which share `Type u → Type v → Type (max u v)`) failed with
--        "invalid datatype declaration, unknown sort '@ε'", in either order, and names in
--        another order swapped the fields' sorts ("unknown constant @isInt (@PUnit)").
--
-- Diagnosis: `genIndParams` telescoped `(← hashcons indVal.type)`. Hash-consing ignores binder
--            names, so the shared type carried the names of whichever alpha-equivalent type
--            the goal met first, while `createCtorDeclaration` names the field sorts from the
--            inductive's own recursor rule.
-- Modifications: `genIndParams` telescopes `indVal.type` itself, as on `main`.
--
-- NOTE: each datatype passes alone; the failures need an alpha-equivalent type earlier in the goal.

set_option warn.sorry false

inductive AlphaBeta (α : Type) (β : Type) where
  | left : α → AlphaBeta α β
  | right : β → AlphaBeta α β

inductive EpsAlpha (ε : Type) (α : Type) where
  | left : ε → EpsAlpha ε α
  | right : α → EpsAlpha ε α

inductive BetaAlpha (β : Type) (α : Type) where
  | left : β → BetaAlpha β α
  | right : α → BetaAlpha β α

/-! ## Original example: `Except` and `Prod` in one goal -/

theorem except_after_prod : ∀ (q : Int × Int) (r : Except String Int),
    (match q with | (a, b) => a + b) = 7 →
    (match r with | .ok n => n | .error _ => 0) = 7 → r = .ok 7 := by blaster

theorem prod_after_except : ∀ (r : Except String Int) (q : Int × Int),
    (match r with | .ok n => n | .error _ => 0) = 7 →
    (match q with | (a, b) => a + b) = 7 → r = .ok 7 := by blaster

/-! ## Other names after an alpha-equivalent type -/

theorem eps_alpha_after_alpha_beta : ∀ (q : AlphaBeta Int Int) (r : EpsAlpha Int Int),
    (match q with | .left n => n | .right n => n) = 7 →
    (match r with | .left n => n | .right n => n) = 7 →
    (r = .left 7 ∨ r = .right 7) := by blaster

/-! ## The same names in another order: the fields' sorts must not swap -/

-- `left` holds the only `Unit`, so two lefts are equal
theorem beta_alpha_lefts_equal_after_alpha_beta : ∀ (q : AlphaBeta Int Int) (r s : BetaAlpha Unit Int),
    (match q with | .left n => n | .right n => n) = 7 →
    (match r with | .left _ => true | .right _ => false) = true →
    (match s with | .left _ => true | .right _ => false) = true → r = s := by blaster

-- `right` holds an `Int`, so two rights needn't be: counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [∀ (q : AlphaBeta Int Int) (r s : BetaAlpha Unit Int),
    (match q with | .left n => n | .right n => n) = 7 →
    (match r with | .left _ => false | .right _ => true) = true →
    (match s with | .left _ => false | .right _ => true) = true → r = s]

end Tests.Issue454
