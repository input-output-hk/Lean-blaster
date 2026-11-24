import Tests.Utils

namespace Tests.Issue227

-- Issue: https://github.com/input-output-hk/Lean-blaster/issues/227
-- Diagnosis: We are always using instantiateSharedRevRange starting with index zero.
--            and make the assumption that any outer de bruijn indices have properly been instantiated.
-- Modifications: We now restrict instantiateSharedRevRange to always start with index zero and updated the specification
--                to state the afore-mentioned assumptions.


#testOptimize ["BetaUnderBinders"]
  (fun x y : Nat => (fun a b : Nat => a + b) y x) ===>
  (fun x y : Nat => Nat.add x y)

#testOptimize ["BetaPreservesOuterVariable"]
  (fun x : Nat => (fun _y : Nat => fun _z : Nat => x) 10) ===>
  (fun x _z : Nat => x)

#blaster [∀ x y : Nat, (fun a b : Nat => a + b) y x = x + y]

end Tests.Issue227
