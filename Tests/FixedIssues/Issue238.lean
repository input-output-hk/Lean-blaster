import Tests.Utils

namespace Tests.FixedIssues.Issue238

section Collections
attribute [local blaster_keep_choices] List Option Prod

#testOptimize ["KeepChoiceInConstructor"] (norm-result: 1)
  (fun b : Bool => some (if b then (3 : Nat) else 4)) ===>
  (fun b : Bool => some (Blaster.dite' (true = b) (fun _ => 3) (fun _ => 4)))

#testOptimize ["ConsumeConstructorChoice"]
  (∀ b : Bool, (some (if b then (3 : Nat) else 4)).getD 5 = (if b then 3 else 4)) ===> True

#blaster (gen-cex: 0)
  [∀ b c : Bool, ((if b then (3 : Nat) else 4), (if c then (5 : Nat) else 6)).1 = (if b then 3 else 4)]

#blaster (gen-cex: 0) (solve-result: 1)
  [∀ b c : Bool, ((if b then (3 : Nat) else 4), (if c then (5 : Nat) else 6)).1 = 3]

-- Independent fields must not create one context for every Boolean assignment.
-- This checks growth, not a machine-dependent wall-clock threshold.
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let e ← Tests.parseTerm (← `(fun (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool) =>
    [if b0 then (1 : Nat) else 0, if b1 then 1 else 0, if b2 then 1 else 0,
     if b3 then 1 else 0, if b4 then 1 else 0, if b5 then 1 else 0,
     if b6 then 1 else 0, if b7 then 1 else 0, if b8 then 1 else 0,
     if b9 then 1 else 0, if b10 then 1 else 0, if b11 then 1 else 0]))
  let (_, env) ← Blaster.Optimize.command default e
  unless env.optEnv.options.nextCtxId < 100 && env.optEnv.hashConsCache.size < 5000 do
    throwError "Independent choices expanded: contexts={env.optEnv.options.nextCtxId}, hashcons={env.optEnv.hashConsCache.size}"

end Collections

section Values
inductive Datum where
  | nat : Nat → Datum

attribute [local blaster_keep_choices] Datum

#testOptimize ["KeepChoicesInValueContainers"] (norm-result: 1)
  (fun b : Bool => [if b then Datum.nat 3 else Datum.nat 4]) ===>
  (fun b : Bool => [Blaster.dite' (true = b) (fun _ => Datum.nat 3) (fun _ => Datum.nat 4)])

#testOptimize ["UnmarkedControlStillHoists"] (norm-result: 1)
  (fun b : Bool => some (if b then (3 : Nat) else 4)) ===>
  (fun b : Bool => Blaster.dite' (true = b) (fun _ => some 3) (fun _ => some 4))
end Values

end Tests.FixedIssues.Issue238
