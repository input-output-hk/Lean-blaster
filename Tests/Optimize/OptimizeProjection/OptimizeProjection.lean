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
  x: Nat
  y: Nat

-- ∀ (a b : Nat), (Point.mk a b).x = a ===> True
#testOptimize [ "PointProj_1", proof] ∀ (a b : Nat), (Point.mk a b).x = a ===> True

-- ∀ (a b : Nat), (Point.mk a b).y = b ===> True
#testOptimize [ "PointProj_2", proof] ∀ (a b : Nat), (Point.mk a b).y = b ===> True

/-! Test cases for projection function unfolding `S.f s  ==> s.i ` -/

-- ∀ (p : Nat × Nat), Prod.fst p + Prod.snd p = p.1 + p.2 ===> True
#testOptimize [ "ProdProjFun_1", proof] ∀ (p : Int × Int), Prod.fst p + Prod.snd p = p.1 + p.2 ===> True

-- ∀ (p : Nat × Nat), Prod.fst p < 3 ===> ∀ (p : Nat × Nat), p.1 < 3
#testOptimize [ "ProdProjFun_2", proof] (norm-result: 1) ∀ (p : Nat × Nat), Prod.fst p < 3 ===> ∀ (p : Nat × Nat), p.1 < 3

-- ∀ (p : Point), Point.x p + Point.y p = p.x + p.y ===> True
#testOptimize [ "PointProjFun_1", proof] ∀ (p : Point), Point.x p + Point.y p = p.x + p.y ===> True

-- ∀ (p : Point), Point.x p < 3 ===> ∀ (p : Point), p.x < 3
#testOptimize [ "PointProjFun_2", proof] (norm-result: 1) ∀ (p : Point), Point.x p < 3 ===> ∀ (p : Point), p.x < 3

end Test.OptimizeProjection
