import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeProjection

/-! ## Test objectives to validate normalization and simplification rules on projections -/

/-! Test cases for projection reductions `(C.mk e₁ … eₙ).i  ==> eᵢ` -/

-- ∀ (a b : Nat), (Prod.mk a b).1 = a ===> True
#testOptimize [ "NatProdProj_1", proof ] ∀ (a b : Nat), (Prod.mk a b).1 = a ===> True

-- ∀ (a b : Nat), (Prod.mk a b).2 = b ===> True
#testOptimize [ "NatProdProj_2", proof ] ∀ (a b : Nat), (Prod.mk a b).2 = b ===> True


structure Point where
  x : Nat
  y: Nat

-- ∀ (a b : Nat), (Point.mk a b).x = a ===> True
#testOptimize [ "PointProj_1", proof] ∀ (a b : Nat), (Point.mk a b).x = a ===> True

-- ∀ (a b : Nat), (Point.mk a b).y = b ===> True
#testOptimize [ "PointProj_2", proof] ∀ (a b : Nat), (Point.mk a b).y = b ===> True

/-! Test cases for projection function unfolding `S.f s  ==> s.i ` -/

-- ∀ (p : Nat × Nat), Prod.fst p = p.1 ===> True
#testOptimize [ "ProdProjFun_1", proof] ∀ (p : Nat × Nat), Prod.fst p = p.1 ===> True

-- ∀ (p : Nat × Nat), Prod.snd p = p.2 ===> True
#testOptimize [ "ProdProjFun_2", proof] ∀ (p : Nat × Nat), Prod.snd p = p.2 ===> True

-- ∀ (p : Point), Point.x p = p.x ===> True
#testOptimize [ "PointProjFun_1", proof] ∀ (p : Point), Point.x p = p.x ===> True

-- ∀ (p : Point), Point.y p = p.y ===> True
#testOptimize [ "PointProjFun_2", proof] ∀ (p : Point), Point.y p = p.y ===> True

end Test.OptimizeProjection
