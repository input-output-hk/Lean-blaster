import Lean
import Tests.Utils

open Lean Elab Command Term Meta

namespace Tests.ProjectionPropagation

/-! ## Test objectives to validate projection propagation over dite and match (`optimizeProjection?`),
    with a focus on indexed inductive datatypes (`diteProj?` and `matchProj?`): the pushed projection
    must get the field type as sort of the pulled `dite'`, or as return type of the pulled match
    (abstracting the discriminators as done by Lean's `match` elaborator). -/

inductive FnIdx : Nat → Type where
  | z : FnIdx 0
  | s : FnIdx 1

/-- Structure parameterized by the index of an indexed inductive datatype field. -/
structure Pack (n : Nat) where
  v : FnIdx n
  m : Nat

/-- Structure whose second field type depends on the first field. -/
structure DPack where
  n : Nat
  v : FnIdx n

/-- Structure with a parameter and no indexed field. -/
structure Box (n : Nat) where
  m : Nat

axiom g : Bool → Nat
axiom dupFn {n : Nat} (x : FnIdx n) : FnIdx n

def mkFn : (b : Bool) → FnIdx (cond b 0 1)
  | true => .z
  | false => .s

def mkPack : (b : Bool) → Pack (cond b 0 1)
  | true => ⟨.z, 1⟩
  | false => ⟨.s, 2⟩

def mkBoxG (b : Bool) : Box (g b) :=
  match b with
  | true => ⟨1⟩
  | false => ⟨2⟩

def fnPack (n : Nat) (v : FnIdx n) : Pack 0 :=
  match n, v with
  | .(0), .z => ⟨.z, 1⟩
  | .(1), .s => ⟨.z, 2⟩

def fnPackD (n : Nat) (v : FnIdx n) : Pack n :=
  match n, v with
  | .(0), .z => ⟨.z, 1⟩
  | .(1), .s => ⟨.s, 2⟩

def idxO : Option Nat → Nat
  | none => 0
  | some _ => 1

def pkO : (o : Option Nat) → Pack (idxO o)
  | none => ⟨.z, 1⟩
  | some j => ⟨.s, j⟩

def fnD (n : Nat) (v : FnIdx n) : DPack :=
  match n, v with
  | .(0), .z => ⟨0, .z⟩
  | .(1), .s => ⟨1, .s⟩

/-! Test cases to validate projection over dite propagation (`diteProj?`). -/

-- ∀ (c : Prop) [Decidable c] (k : Nat) (w : FnIdx k) (x : Nat), (if c then (⟨w, 1⟩ : Pack k) else ⟨w, 2⟩).m = x ===>
-- ∀ (c : Prop) (x : Nat), x = Blaster.dite' c (fun _ => 1) (fun _ => 2)
-- NOTE: the sort of the `dite'` (`Pack k`) is closed; the projection is pushed and reduced in each branch.
#testOptimize [ "DIteProj_1" ] (norm-result: 1)
  ∀ (c : Prop) [Decidable c] (k : Nat) (w : FnIdx k) (x : Nat), (if c then (⟨w, 1⟩ : Pack k) else ⟨w, 2⟩).m = x ===>
  ∀ (c : Prop) (x : Nat), x = Blaster.dite' c (fun _ => 1) (fun _ => 2)

-- ∀ (c : Prop) [Decidable c] (k : Nat) (w w' y : FnIdx k), (if c then (⟨w, 1⟩ : Pack k) else ⟨w', 2⟩).v = y ===>
-- ∀ (c : Prop) (k : Nat) (w w' y : FnIdx k), y = Blaster.dite' c (fun _ => w) (fun _ => w')
-- NOTE: the projected field has an indexed inductive type (`FnIdx k`), which becomes the sort of the `dite'`.
#testOptimize [ "DIteProj_2" ]
  ∀ (c : Prop) [Decidable c] (k : Nat) (w w' y : FnIdx k), (if c then (⟨w, 1⟩ : Pack k) else ⟨w', 2⟩).v = y ===>
  ∀ (c : Prop) (k : Nat) (w w' y : FnIdx k), y = Blaster.dite' c (fun _ => w) (fun _ => w')

-- ∀ (b : Bool) (x : Nat), (mkBoxG b).m = x ===>
-- ∀ (b : Bool) (x : Nat), x = Blaster.dite' (true = b) (fun _ => 1) (fun _ => 2)
-- NOTE: `mkBoxG b` is normalized to a `dite'` whose sort `Box (g b)` depends on the condition
-- through the opaque function `g`.
#testOptimize [ "DIteProj_3" ] (norm-result: 1)
  ∀ (b : Bool) (x : Nat), (mkBoxG b).m = x ===>
  ∀ (b : Bool) (x : Nat), x = Blaster.dite' (true = b) (fun _ => 1) (fun _ => 2)

-- ∀ (b : Bool) (x : Nat), (mkPack b).m = x ===>
-- ∀ (b : Bool) (x : Nat), x = Blaster.dite' (true = b) (fun _ => 1) (fun _ => 2)
-- NOTE: `mkPack b` is normalized to a `dite'` whose sort `Pack (cond b 0 1)` is itself normalized to
-- `Pack (Blaster.dite' (true = b) (fun _ => 0) (fun _ => 1))`. The sort must stay an application of the
-- structure type `Pack` (i.e., `funPropagation?` must not push the type constructor `Pack` in the inner
-- `dite'`, giving `Blaster.dite' Type (true = b) (fun _ => Pack 0) (fun _ => Pack 1)`), otherwise
-- `inferTypeEnv` (whnf) cannot reduce it to a structure type in `diteProj?` (`invalid projection`).
-- This used to fail when `funPropagation?` was eagerly applied on not yet optimized arguments.
#testOptimize [ "DIteProj_4" ] (norm-result: 1)
  ∀ (b : Bool) (x : Nat), (mkPack b).m = x ===>
  ∀ (b : Bool) (x : Nat), x = Blaster.dite' (true = b) (fun _ => 1) (fun _ => 2)

-- ∀ (b : Bool), (mkPack b).v = mkFn b ===> True
-- NOTE: the projected field has the indexed inductive type `FnIdx (cond b 0 1)`; both sides are
-- normalized to the same `dite'` (same sort requirement as `DIteProj_4`).
#testOptimize [ "DIteProj_5" ]
  ∀ (b : Bool), (mkPack b).v = mkFn b ===> True

/-! Test cases to validate projection over match propagation (`matchProj?`). -/

-- ∀ (k : Nat) (w : FnIdx k) (x : Nat), (fnPack k w).m = x ===>
-- ∀ (k : Nat) (w : FnIdx k) (x : Nat),
--   x = fnPack.match_1 (fun (n : Nat) (_ : FnIdx n) => Nat) k w
--       (fun (_ : Unit) => 1)
--       (fun (_ : Unit) => 2)
-- NOTE: indexed inductive datatype in the discriminators (dependent binder `v : FnIdx n` kept in the
-- motive) and closed return type `Pack 0`.
#testOptimize [ "MatchProj_1" ] (norm-result: 1)
  ∀ (k : Nat) (w : FnIdx k) (x : Nat), (fnPack k w).m = x ===>
  ∀ (k : Nat) (w : FnIdx k) (x : Nat),
    x = match k, w with
        | .(0), .z => 1
        | .(1), .s => 2

-- ∀ (k : Nat) (w : FnIdx k) (y : FnIdx 0), (fnPack k w).v = y ===> ∀ (y : FnIdx 0), FnIdx.z = y
-- NOTE: the pushed projection gives the same value `FnIdx.z` in each alternative, the match is eliminated.
#testOptimize [ "MatchProj_2" ] (norm-result: 1)
  ∀ (k : Nat) (w : FnIdx k) (y : FnIdx 0), (fnPack k w).v = y ===>
  ∀ (y : FnIdx 0), FnIdx.z = y

-- ∀ (k : Nat) (w : FnIdx k) (x : Nat), (fnPackD k w).m = x ===>
-- ∀ (k : Nat) (w : FnIdx k) (x : Nat),
--   x = fnPack.match_1 (fun (n : Nat) (_ : FnIdx n) => Nat) k w
--       (fun (_ : Unit) => 1)
--       (fun (_ : Unit) => 2)
-- NOTE: the return type of the match depends on a discriminator (`Pack n`), the projected field type is closed.
#testOptimize [ "MatchProj_3" ] (norm-result: 1)
  ∀ (k : Nat) (w : FnIdx k) (x : Nat), (fnPackD k w).m = x ===>
  ∀ (k : Nat) (w : FnIdx k) (x : Nat),
    x = match k, w with
        | .(0), .z => 1
        | .(1), .s => 2

-- ∀ (k : Nat) (w : FnIdx k), (fnPackD k w).v = w ===>
-- ∀ (k : Nat) (w : FnIdx k),
--   w = fnPack.match_1 (fun (n : Nat) (_ : FnIdx n) => FnIdx n) k w
--       (fun (_ : Unit) => FnIdx.z)
--       (fun (_ : Unit) => FnIdx.s)
-- NOTE: the projected field type `FnIdx k` depends on the discriminator `k`, which is abstracted by the
-- motive's own binder (`FnIdx n`), as done by Lean's `match` elaborator.
#testOptimize [ "MatchProj_4" ]
  ∀ (k : Nat) (w : FnIdx k), (fnPackD k w).v = w ===>
  ∀ (k : Nat) (w : FnIdx k),
    w = match (generalizing := false) k, w with
        | .(0), .z => FnIdx.z
        | .(1), .s => FnIdx.s

-- ∀ (k : Nat) (w : FnIdx k), dupFn (fnPackD k w).v = w ===>
-- ∀ (k : Nat) (w : FnIdx k),
--   w = fnPack.match_1 (fun (n : Nat) (_ : FnIdx n) => FnIdx n) k w
--       (fun (_ : Unit) => dupFn FnIdx.z)
--       (fun (_ : Unit) => dupFn FnIdx.s)
-- NOTE: the pushed projection is then propagated over the function `dupFn` (match over function
-- propagation), the return type `FnIdx k` of the function application is abstracted as well.
#testOptimize [ "MatchProj_5" ] (norm-result: 1)
  ∀ (k : Nat) (w : FnIdx k), dupFn (fnPackD k w).v = w ===>
  ∀ (k : Nat) (w : FnIdx k),
    w = match (generalizing := false) k, w with
        | .(0), .z => dupFn FnIdx.z
        | .(1), .s => dupFn FnIdx.s

-- ∀ (o : Option Nat) (x : Nat), (pkO o).m = x ===>
-- ∀ (o : Option Nat) (x : Nat),
--   x = idxO.match_1 (fun (_ : Option Nat) => Nat) o (fun (_ : Unit) => 1) (fun (j : Nat) => j)
-- NOTE: the return type of the match depends on the discriminator through a function (`Pack (idxO o)`).
#testOptimize [ "MatchProj_6" ] (norm-result: 1)
  ∀ (o : Option Nat) (x : Nat), (pkO o).m = x ===>
  ∀ (o : Option Nat) (x : Nat),
    x = match o with
        | none => 1
        | some j => j

-- ∀ (o : Option Nat) (y : FnIdx (idxO o)), (pkO o).v = y ===>
-- ∀ (o : Option Nat) (y : FnIdx (idxO.match_1 (fun (_ : Option Nat) => Nat) o (fun _ => 0) (fun _ => 1))),
--   y = idxO.match_1 (fun (o : Option Nat) => FnIdx (idxO.match_1 (fun _ => Nat) o (fun _ => 0) (fun _ => 1))) o
--       (fun (_ : Unit) => FnIdx.z)
--       (fun (_ : Nat) => FnIdx.s)
-- NOTE: the projected field type `FnIdx (idxO o)` is abstracted by the motive's own binder, `idxO o`
-- being unfolded to its match in both the binder type and the motive.
#testOptimize [ "MatchProj_7" ] (norm-result: 1)
  ∀ (o : Option Nat) (y : FnIdx (idxO o)), (pkO o).v = y ===>
  ∀ (o : Option Nat) (y : FnIdx (match o with | none => 0 | some _ => 1)),
    y = match (generalizing := false) o with
        | none => FnIdx.z
        | some _ => FnIdx.s

-- ∀ (k : Nat) (w : FnIdx k) (x : Nat), (fnD k w).n = x ===>
-- ∀ (k : Nat) (w : FnIdx k) (x : Nat),
--   x = fnPack.match_1 (fun (n : Nat) (_ : FnIdx n) => Nat) k w (fun (_ : Unit) => 0) (fun (_ : Unit) => 1)
#testOptimize [ "MatchProj_8" ] (norm-result: 1)
  ∀ (k : Nat) (w : FnIdx k) (x : Nat), (fnD k w).n = x ===>
  ∀ (k : Nat) (w : FnIdx k) (x : Nat),
    x = match k, w with
        | .(0), .z => 0
        | .(1), .s => 1

-- ∀ (k : Nat) (w : FnIdx k) (y : FnIdx (fnD k w).n), (fnD k w).v = y ===>
-- ∀ (k : Nat) (w : FnIdx k) (y : FnIdx (fnPack.match_1 (fun (n : Nat) (_ : FnIdx n) => Nat) k w (fun _ => 0) (fun _ => 1))),
--   y = fnPack.match_1
--       (fun (n : Nat) (v : FnIdx n) => FnIdx (fnPack.match_1 (fun (n : Nat) (_ : FnIdx n) => Nat) n v (fun _ => 0) (fun _ => 1)))
--       k w (fun (_ : Unit) => FnIdx.z) (fun (_ : Unit) => FnIdx.s)
-- NOTE: the projected field type depends on the first field (`FnIdx (fnD k w).n`), whose projection is
-- itself pushed in the match; the discriminators `k`, `w` are abstracted in the resulting type.
#testOptimize [ "MatchProj_9" ] (norm-result: 1)
  ∀ (k : Nat) (w : FnIdx k) (y : FnIdx (fnD k w).n), (fnD k w).v = y ===>
  ∀ (k : Nat) (w : FnIdx k) (y : FnIdx (match k, w with | .(0), .z => 0 | .(1), .s => 1)),
    y = match (generalizing := false) k, w with
        | .(0), .z => FnIdx.z
        | .(1), .s => FnIdx.s

end Tests.ProjectionPropagation
