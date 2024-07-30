import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeLet

-- let x := v in b ===> b[x/v]
-- NOTE: Reordering applied on commutative operators
#testOptimize [ "LetElimOne" ] ∀ (a b : Prop), let x := a ∧ b; x ===> ∀ (a b : Prop), b ∧ a

-- let x := v in
-- let y := z in b ===> b[x/v][y/z] with x ∉ Var(z)
#testOptimize [ "LetElimTwo" ] ∀ (a b c : Prop), let x := a ∧ b; let y := c ∨ b; y ∧ x ===> ∀ (a b c : Prop), (c ∨ b) ∧ (a ∧ b)

-- let x := v in
-- let y := z in b ===> b[x/v][y/z] with x ∈ z
-- NOTE: Reordering applied on commutative operators
#testOptimize [ "LetElimThree" ] ∀ (a b c : Prop), let x := a ∧ b; let y := x ∨ c; y ∨ b ===> ∀ (a b c : Prop), b ∨ (c ∨ (a ∧ b))

-- let x := a ∧ b in
-- let y := c ∨ b in
--  (y ∧ x) = ((b ∧ a) ∧ (b ∨ c)) ===> True
#testOptimize [ "LetElimFour" ] ∀ (a b c : Prop), let x := a ∧ b; let y := c ∨ b; (y ∧ x) = ((b ∧ a) ∧ (b ∨ c)) ===> True

-- let x := a = b in
-- let y := c = b in
--  (y ∧ x) = ((b = a) ∧ (b = c)) ===> True
-- With Type(a) = Type(b) = α
#testOptimize [ "LetElimFive" ] ∀ (α : Type) (a b c : α), let x := a = b; let y := c = b; (y ∧ x) = ((b = a) ∧ (b = c)) ===> True

-- let x := v in ===> b[x/v] with Type(v) = α -> β
-- NOTE: Reordering applied on commutative operators
#testOptimize [ "LetElimSix" ] ∀ (a b c : Prop), let x := fun z => a ∧ z; x b ∨ x c ===> ∀ (a b c : Prop), (c ∧ a) ∨ (a ∧ b)

end Tests.OptimizeLet
