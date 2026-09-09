import Blaster

/-!
# Unit tests for SmtTerm.shareLets (SharingBlowup Pathology A)

`shareLets` binds pointer-shared subterms as SMT `(let …)` prefixes so query
TEXT is DAG-sized. Tests are structural (substring/length asserts), not full
pinned dumps — printer whitespace must stay free to change.
-/

namespace Tests.Issue231

open Blaster.Smt

private def v (s : String) : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol s))
private def add (a b : SmtTerm) : SmtTerm :=
  .AppTerm (.SimpleIdent (.ReservedSymbol "+")) #[a, b]
private def ge0 (a : SmtTerm) : SmtTerm :=
  .AppTerm (.SimpleIdent (.ReservedSymbol "<=")) #[.NumTerm 0, a]

/-- `chain n` = the dupChain shape: level 0 = x+x, level i+1 = level_i + level_i.
    Linear as a DAG, `2^(n+1)` leaves as a tree. -/
private def chain : Nat → SmtTerm
  | 0 => add (v "x") (v "x")
  | n + 1 => let c := chain n; add c c

-- 1. Depth 20: tree text is ≥ 2^21 chars; shared text must be tiny and linear.
#guard (toString ((ge0 (chain 20)).shareLets (minSize := 1))).length < 2000

-- 1b. Same, at the DEFAULT minSize (16, not the artificially low 1 above) —
--     measured 578 chars; bound gives ~2× headroom.
#guard (toString ((ge0 (chain 20)).shareLets)).length < 1200

-- 2. Sharing fires: bindings appear, with the generated `$s` prefix.
#guard ((toString ((ge0 (chain 3)).shareLets (minSize := 1))).splitOn "(let ").length > 2
#guard ((toString ((ge0 (chain 3)).shareLets (minSize := 1))).splitOn "$s0").length > 1

-- 3. minSize threshold: duplicated-but-small subterms stay inline (chain 2's
--    largest shareable node is 7 nodes < the default 16).
#guard toString ((ge0 (chain 2)).shareLets) == toString (ge0 (chain 2))

-- 4. Taint: a duplicated subterm mentioning a quantifier-bound symbol is NOT
--    lifted — output is textually unchanged.
private def y : SmtTerm := v "y"
private def boundDup : SmtTerm :=
  .ForallTerm #[(.NormalSymbol "y", .SymbolSort (.NormalSymbol "Int"))]
    (add (add y y) (add y y))
#guard toString (boundDup.shareLets (minSize := 1)) == toString boundDup

-- 5. Untainted subterm UNDER a binder is lifted above it (it mentions no bound
--    symbol, so binding it at the root is legal).
private def freeDupUnderBinder : SmtTerm :=
  .ForallTerm #[(.NormalSymbol "y", .SymbolSort (.NormalSymbol "Int"))]
    (add (add (v "x") (v "x")) (add (v "x") (v "x")))
#guard ((toString (freeDupUnderBinder.shareLets (minSize := 1))).splitOn "(let ").length > 1

/-- Collect the binder symbols of the nested-`let` prefix, outermost first. -/
private def letSpine : SmtTerm → Array SmtSymbol
  | .LetTerm bs body => bs.map (·.1) ++ letSpine body
  | _ => #[]

-- 6. Freshness: an existing `$s0` symbol pushes generated names past it — no
--    generated `let` may ever BIND the pre-existing `$s0` symbol. Checked
--    structurally (via `letSpine`), independent of printer whitespace and of
--    the single-binding-per-group shape `shareLets` happens to emit today.
private def collide : SmtTerm := add (add (v "$s0") (v "$s0")) (add (v "$s0") (v "$s0"))
#guard !((letSpine (collide.shareLets (minSize := 1))).contains (.NormalSymbol "$s0"))

-- 7. SmtCommand.shareLets rewrites assert, define-fun, and define-funs-rec
--    bodies (default minSize 16: chain 5's top two levels are 63- and
--    31-node duplicates), and leaves other commands alone.
#guard ((toString (SmtCommand.shareLets (.assertTerm (ge0 (chain 5))))).splitOn "(let ").length > 2

private def defineFunCmd : SmtCommand :=
  .defineFun false (.NormalSymbol "f") #[] (.SymbolSort (.NormalSymbol "Int")) (ge0 (chain 5))
#guard ((toString (SmtCommand.shareLets defineFunCmd)).splitOn "(let ").length > 2

-- Cross-body pointer aliasing of `sharedBody` is irrelevant here — each body
-- is `shareLets`'d independently (its own `shareCommon` pass, its own
-- counters), so one body's sharing can't leak into another's. What matters is
-- that EACH body internally carries the 63-/31-node chain-5 duplicates, and
-- that EVERY body in the array actually gets visited (not just the first).
-- `#[]` decls are irrelevant to the transform itself — real emission
-- requires `decls.size == bodies.size`, but this is a transform unit test.
private def sharedBody : SmtTerm := ge0 (chain 5)
private def defineFunsRecCmd : SmtCommand :=
  .defineFunsRec #[] #[sharedBody, sharedBody]
#guard match SmtCommand.shareLets defineFunsRecCmd with
  | .defineFunsRec _ bs => bs.all (fun b => (letSpine b).size ≥ 2)
  | _ => false

#guard toString (SmtCommand.shareLets .checkSat) == toString SmtCommand.checkSat

-- 8. Nesting order: `$s1`'s definition references `$s0`, so `$s0`'s `let` must
--    be the OUTER one (i.e. earlier in the spine) — an inner binding's
--    definition is evaluated outside its own let, so a reversed nesting
--    leaves `$s0` unbound where `$s1` is defined. Checked structurally via
--    `letSpine` position, independent of printer whitespace.
private def chain3Spine : Array SmtSymbol := letSpine ((ge0 (chain 3)).shareLets (minSize := 1))
private def s0Idx : Option Nat := chain3Spine.idxOf? (.NormalSymbol "$s0")
private def s1Idx : Option Nat := chain3Spine.idxOf? (.NormalSymbol "$s1")
#guard s0Idx.isSome && s1Idx.isSome
#guard match s0Idx, s1Idx with
  | some i0, some i1 => i0 < i1
  | _, _ => false

-- End-to-end checks keep the residual duplicated after Lean let expansion.
-- The two settings must give the same verdict; the large rung exercises
-- the default sharing path without emitting an exponential query in CI.
open Lean in
macro "issue231Chain%" n:num seed:term : term => do
  let depth := n.getNat
  if depth == 0 then Macro.throwError "depth must be positive"
  let ids := (Array.range depth).map fun i => mkIdent (Name.mkSimple s!"a{i}")
  let mut e : Term ← `(0 ≤ $(ids[depth-1]!))
  for i in (List.range depth).reverse do
    let v : Term ← if i == 0 then `(($seed : Int) + $seed)
      else `($(ids[i-1]!) + $(ids[i-1]!))
    e ← `(let $(ids[i]!) := $v; $e)
  return e

#blaster (share-smt: 0) (timeout: 5)
  [∀ x : Int, 0 ≤ x → issue231Chain% 12 x]
#blaster (share-smt: 1) (timeout: 5)
  [∀ x : Int, 0 ≤ x → issue231Chain% 12 x]
#blaster (share-smt: 1) (timeout: 5)
  [∀ x : Int, 0 ≤ x → issue231Chain% 80 x]
#blaster (share-smt: 0) (timeout: 5) (gen-cex: 0) (solve-result: 1)
  [∀ x : Int, issue231Chain% 12 x]
#blaster (share-smt: 1) (timeout: 5) (gen-cex: 0) (solve-result: 1)
  [∀ x : Int, issue231Chain% 12 x]

end Tests.Issue231
