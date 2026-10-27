import Tests.Utils

open Lean Meta Blaster.Optimize

namespace Tests.Issue126Chars

-- Check the actual optimizer output, including the dependent validity proof.
-- This covers both sides of the surrogate gap, the SMT alphabet boundary,
-- Lean's maximum scalar, and inputs that Char.ofNat maps to NUL.
run_meta do
  for n in [0, 97, 0xD7FF, 0xD800, 0xDFFF, 0xE000, 0x2FFFF, 0x30000, 0x10FFFF, 0x110000] do
    let input := mkApp (mkConst ``Char.ofNat) (mkRawNatLit n)
    let (result, _) ← Blaster.Optimize.command {} input
    check result
    let scalar ← whnf (mkApp (mkConst ``Char.toNat) result)
    unless scalar == mkRawNatLit (Char.ofNat n).toNat do
      throwError "Char.ofNat {n}: optimizer changed the Unicode scalar value"
    if Nat.isValidChar n then
      -- Literal character patterns use ofNatAux directly in Lean 4.35.
      let proof ← mkDecideProof (mkApp (mkConst ``Nat.isValidChar) (mkRawNatLit n))
      let input := mkApp2 (mkConst ``Char.ofNatAux) (mkRawNatLit n) proof
      let (result, _) ← Blaster.Optimize.command {} input
      check result
      let scalar ← whnf (mkApp (mkConst ``Char.toNat) result)
      unless scalar == mkRawNatLit n do
        throwError "Char.ofNatAux {n}: optimizer changed the Unicode scalar value"

-- Keep the first alternative undecided so literal-pattern unification runs.
def charPattern (m : Nat) (xs : List Char) : Nat :=
  match m, xs with
  | 5, _ => 100
  | _, 'a' :: tail => m + tail.length
  | _, _ => 0

run_meta do
  withLocalDeclD `m (mkConst ``Nat) fun m => do
    let input := mkApp2 (mkConst ``charPattern) m (toExpr (['a', 'b'] : List Char))
    let (result, _) ← Blaster.Optimize.command {} input
    check result

-- Dependent pattern proofs follow the same rule for types other than Char.
def finPattern (m : Nat) (xs : List (Fin 10)) : Nat :=
  match m, xs with
  | 5, _ => 100
  | _, ⟨3, _⟩ :: tail => m + tail.length
  | _, _ => 0

run_meta do
  withLocalDeclD `m (mkConst ``Nat) fun m => do
    let input := mkApp2 (mkConst ``finPattern) m (toExpr ([3, 4] : List (Fin 10)))
    let (result, _) ← Blaster.Optimize.command {} input
    check result

end Tests.Issue126Chars
