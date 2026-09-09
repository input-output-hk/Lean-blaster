import Blaster

namespace Tests.Issue232
open Blaster.Smt

private def add (a b : SmtTerm) : SmtTerm :=
  .AppTerm (.SimpleIdent (.ReservedSymbol "+")) #[a, b]
private def intSort : SortExpr := .SymbolSort (.ReservedSymbol "Int")
private def ref (s : SmtSymbol) : SmtTerm := .SmtIdent (.SimpleIdent s)

-- The two constructors print the same SMT identifier. Scope analysis must
-- recognize both orientations for every binder, including let bodies.
private def keepsScope (binder occurrence : SmtSymbol) : Bool := Id.run do
  let y := ref occurrence
  let body := add (add y y) (add y y)
  let proposition := SmtTerm.AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[body, .NumTerm 0]
  let terms := #[SmtTerm.ForallTerm #[(binder, intSort)] proposition,
    .ExistsTerm #[(binder, intSort)] proposition,
    .LambdaTerm #[(binder, intSort)] body,
    .LetTerm #[(binder, .NumTerm 1)] body]
  return terms.all fun t => toString (t.shareLets (minSize := 1)) == toString t

#guard keepsScope (.ReservedSymbol "y") (.NormalSymbol "y")
#guard keepsScope (.NormalSymbol "y") (.ReservedSymbol "y")
#guard keepsScope (.ReservedSymbol "|y|") (.NormalSymbol "y")
#guard keepsScope (.NormalSymbol "y") (.ReservedSymbol "|y|")

-- A quoted free identifier must also reserve the corresponding fresh name.
private def quotedCollision : SmtTerm :=
  let x := ref (.NormalSymbol "x")
  let duplicate := add (add x x) (add x x)
  add (ref (.ReservedSymbol "|$s0|")) (add duplicate duplicate)
#guard ((toString (quotedCollision.shareLets (minSize := 1))).splitOn "(let (($s0").length == 1

-- Exercise the default submission path with quantified function arguments.
#blaster (share-smt: 1) (timeout: 5)
  [∀ f : Int → Int, (∀ x, f x = x + x) → f 3 = 6]
#blaster (share-smt: 1) (timeout: 5) (gen-cex: 0) (solve-result: 1)
  [∀ f : Int → Int, (∀ x, f x = x + x) → f 3 = 7]

end Tests.Issue232
