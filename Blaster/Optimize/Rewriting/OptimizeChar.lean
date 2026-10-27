import Lean
import Blaster.Optimize.Rewriting.Utils

open Lean Meta

namespace Blaster.Optimize

/-- Build a character with a kernel-checked validity witness. Keep the proof
    opaque so later rewriting cannot change its dependent decision instances. -/
private def mkCharLiteral (c : Char) : TranslateEnvT Expr := do
  let value ← reduce (mkApp (mkConst ``UInt32.ofNat) (mkRawNatLit c.toNat))
  let validType := mkApp (mkConst ``UInt32.isValidChar) value
  let proof ← mkDecideProof validType
  let proof ← mkAuxTheorem validType proof (kind? := some `blaster_char_validity)
  mkApp2Expr (← mkExpr (mkConst ``Char.mk)) (← hashcons value) (← hashcons proof)

/-- Fold literal character conversions using Lean's scalar semantics, including
    the NUL result for invalid Char.ofNat inputs. Symbolic conversions keep the
    ordinary unfolding path; these rules introduce no SMT character encoding. -/
def optimizeChar? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  match f, args with
  | .const ``Char.ofNat _, #[.lit (.natVal n)] =>
      return some (← mkCharLiteral (Char.ofNat n))
  | .const ``Char.ofNatAux _, #[.lit (.natVal n), _] =>
      unless Nat.isValidChar n do
        throwEnvError "Char.ofNatAux: invalid Unicode scalar"
      return some (← mkCharLiteral (Char.ofNat n))
  | _, _ => return none

end Blaster.Optimize
