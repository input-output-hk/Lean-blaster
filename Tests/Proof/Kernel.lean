import Blaster

/-! `kernel%` (`Blaster/Proof/Export/Term.lean`) reads a term exactly as
written, given as syntax or as text. Each check elaborates a term with
`kernel%` both ways and requires the term Lean's own elaborator builds (or,
where `kernel%` builds the kernel's form, such as a projection, the same term
both ways). A chain of 100,000 `let`s must be read without exhausting the
stack. -/

open Lean Meta Elab Term

/-- `kernel% t`, `kernel% "t"` and `t` (elaborated as usual) are the same term. -/
elab "#same " t:term " ; " text:str : command => Command.liftTermElabM do
  let viaSyntax ← instantiateMVars (← elabTerm (← `(kernel% $t)) none)
  let viaText ← instantiateMVars (← elabTerm (← `(kernel% $text)) none)
  let ordinary ← instantiateMVars (← elabTerm t none)
  unless viaSyntax == ordinary do throwError "kernel% differs from the elaborator:\n{viaSyntax}\nvs\n{ordinary}"
  unless viaText == ordinary do throwError "kernel% of the text differs:\n{viaText}\nvs\n{ordinary}"

/-- `kernel% t` and `kernel% "t"` are the same term. -/
elab "#sameText " t:term " ; " text:str : command => Command.liftTermElabM do
  let viaSyntax ← instantiateMVars (← elabTerm (← `(kernel% $t)) none)
  let viaText ← instantiateMVars (← elabTerm (← `(kernel% $text)) none)
  unless viaText == viaSyntax do throwError "kernel% of the text differs:\n{viaText}\nvs\n{viaSyntax}"

#same fun (x : Nat) (y : Nat) => @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) x y ;
  "fun (x : Nat) (y : Nat) => @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) x y"
#same ∀ (x : Nat), @Eq.{1} Nat x x → ∀ (y : Nat), @Eq.{1} Nat y x ;
  "∀ (x : Nat), @Eq.{1} Nat x x → ∀ (y : Nat), @Eq.{1} Nat y x"
-- a chain of binders and `let`s through nested `fun`s
#same fun (x : Nat) => let a : Nat := x; let b : Nat := a; fun (z : Nat) => let c : Nat := z; @Prod.mk.{0, 0} Nat Nat b c ;
  "fun (x : Nat) => let a : Nat := x; let b : Nat := a; fun (z : Nat) => let c : Nat := z; @Prod.mk.{0, 0} Nat Nat b c"
-- the innermost binder of a name; out of its scope, the outer one again
#same fun (x : Nat) => @Prod.mk.{0, 0} Nat (Nat → Nat) x (fun (x : Nat) => x) ;
  "fun (x : Nat) => @Prod.mk.{0, 0} Nat (Nat → Nat) x (fun (x : Nat) => x)"
#same fun (x : Nat) => @Prod.mk.{0, 0} (Nat → Nat) Nat (fun (x : Nat) => x) x ;
  "fun (x : Nat) => @Prod.mk.{0, 0} (Nat → Nat) Nat (fun (x : Nat) => x) x"
#same fun {α : Type} [inst : Inhabited.{1} α] ⦃a : α⦄ => @Prod.mk.{0, 0} α (Inhabited.{1} α) a inst ;
  "fun {α : Type} [inst : Inhabited.{1} α] ⦃a : α⦄ => @Prod.mk.{0, 0} α (Inhabited.{1} α) a inst"
#same have h : @Eq.{1} Nat (2 : Nat) (2 : Nat) := @rfl.{1} Nat (2 : Nat); h ;
  "have h : @Eq.{1} Nat (2 : Nat) (2 : Nat) := @rfl.{1} Nat (2 : Nat); h"
-- a projection is the kernel's `Expr.proj`; a negative numeral `Neg.neg` of `OfNat.ofNat`
#sameText fun (p : Prod.{0, 0} Nat Bool) => p.1 ;
  "fun (p : Prod.{0, 0} Nat Bool) => p.1"
#sameText fun (n : Nat) => @Prod.mk.{0, 0} Int Nat (-5 : Int) n ;
  "fun (n : Nat) => @Prod.mk.{0, 0} Int Nat (-5 : Int) n"

/-- A `let` without a type has its value's. -/
elab "#untypedLet" : command => Command.liftTermElabM do
  let typed ← instantiateMVars (← elabTerm (← `(kernel% fun (x : Nat) => let a : Nat := x;
    let p : Prod.{0, 0} Nat Nat := @Prod.mk.{0, 0} Nat Nat a x; p.2)) none)
  let viaSyntax ← instantiateMVars (← elabTerm (← `(kernel% fun (x : Nat) => let a := x;
    let p := @Prod.mk.{0, 0} Nat Nat a x; p.2)) none)
  let viaText ← instantiateMVars (← elabTerm (← `(kernel%
    "fun (x : Nat) => let a := x; let p := @Prod.mk.{0, 0} Nat Nat a x; p.2")) none)
  unless viaSyntax == typed && viaText == typed do
    throwError "an untyped let differs:\n{viaSyntax}\n{viaText}\nvs\n{typed}"
#untypedLet

/-- A projection is the kernel's: `Expr.proj` of the structure. -/
elab "#projection" : command => Command.liftTermElabM do
  let e ← instantiateMVars (← elabTerm (← `(kernel% fun (p : Prod.{0, 0} Nat Bool) => p.1)) none)
  let pair := mkApp2 (mkConst ``Prod [levelZero, levelZero]) (mkConst ``Nat) (mkConst ``Bool)
  unless e == .lam `p pair (.proj ``Prod 0 (.bvar 0)) .default do throwError "a projection differs: {e}"
#projection

/-- `fun x0 => let x1 := x0; …; x(n-1)`, read from text. -/
elab "#chain " n:num : command => Command.liftTermElabM do
  let n := n.getNat
  let mut text := "fun (x0 : Nat) => "
  for i in [1:n] do text := text ++ s!"let x{i} := x{i - 1}; "
  text := text ++ s!"x{n - 1}"
  let e ← instantiateMVars (← elabTerm (← `(kernel% $(Syntax.mkStrLit text))) none)
  unless ← isDefEq (← inferType e) (← mkArrow (mkConst ``Nat) (mkConst ``Nat)) do
    throwError "the chain has the wrong type"
#chain 100000
