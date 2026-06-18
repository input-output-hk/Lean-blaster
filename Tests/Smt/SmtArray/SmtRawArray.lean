import Blaster

-- SOUND: out-of-bounds set! is a no-op → unguarded set!/get! is NOT valid
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a : Array Int) (i : Nat) (v : Int), (a.set! i v).get! i = v]
-- SOUND positive: in-bounds guard makes it valid
#blaster [∀ (a : Array Int) (i : Nat) (v : Int), i < a.size → (a.set! i v).get! i = v]
-- setIfInBounds, same shape
#blaster [∀ (a : Array Int) (i : Nat) (v : Int), i < a.size → (a.setIfInBounds i v).get! i = v]
-- getD returns the explicit default out of bounds
#blaster [∀ (a : Array Int) (i : Nat) (d : Int), a.size ≤ i → a.getD i d = d]
