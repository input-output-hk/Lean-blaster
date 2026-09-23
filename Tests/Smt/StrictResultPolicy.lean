import Blaster.Smt.Env

namespace Test.StrictResultPolicy

open Blaster.Options Blaster.Smt

private def expectedUndetermined : BlasterOptions :=
  { solveResult := .ExpectedUndetermined }

private def cvc5Allowance : BlasterOptions :=
  { allowCvc5Undetermined := true }

private def expectedWithCvc5Allowance : BlasterOptions :=
  { solveResult := .ExpectedUndetermined, allowCvc5Undetermined := true }

private def strictCvc5RejectsUnexpected : Bool :=
  undeterminedAction default (some .cvc5) true == .strictError

private def nonstrictCvc5WarnsOnUnexpected : Bool :=
  undeterminedAction default (some .cvc5) false == .warning

private def strictFlagDoesNotAffectZ3 : Bool :=
  undeterminedAction default (some .z3) true == .warning

private def declaredUndeterminedWinsInStrictMode : Bool :=
  undeterminedAction expectedUndetermined (some .cvc5) true == .expected

private def cvc5AllowanceWinsInStrictMode : Bool :=
  undeterminedAction cvc5Allowance (some .cvc5) true == .allowed

private def cvc5AllowanceDoesNotApplyToZ3 : Bool :=
  undeterminedAction cvc5Allowance (some .z3) true == .warning

private def declaredUndeterminedAppliesToZ3 : Bool :=
  undeterminedAction expectedUndetermined (some .z3) true == .expected

private def nonstrictCvc5AllowanceIsAccepted : Bool :=
  undeterminedAction cvc5Allowance (some .cvc5) false == .allowed

private def declarationPrecedesCvc5Allowance : Bool :=
  undeterminedAction expectedWithCvc5Allowance (some .cvc5) true == .expected

#guard strictCvc5RejectsUnexpected
#guard nonstrictCvc5WarnsOnUnexpected
#guard strictFlagDoesNotAffectZ3
#guard declaredUndeterminedWinsInStrictMode
#guard cvc5AllowanceWinsInStrictMode
#guard cvc5AllowanceDoesNotApplyToZ3
#guard declaredUndeterminedAppliesToZ3
#guard nonstrictCvc5AllowanceIsAccepted
#guard declarationPrecedesCvc5Allowance

private def strictTacticIntegrationSource : String :=
  "import Blaster.Command.Tactic\n\n" ++
  "open Blaster.Tactic\n\n" ++
  "/--\n" ++
  "error: ❌ Unexpected Undetermined\n" ++
  "-/\n" ++
  "#guard_msgs in\n" ++
  "example (α : Type) (xs : List α) : xs = List.map (fun x => x) xs := by\n" ++
  "  blaster (solver: cvc5) (only-optimize: 1) <;> simp\n"

private def strictTacticIntegrationGuard : IO Unit :=
  IO.FS.withTempFile fun handle path => do
    handle.putStr strictTacticIntegrationSource
    handle.flush
    let output ← IO.Process.output {
      cmd := (← IO.appPath).toString
      args := #[path.toString]
      env := #[("BLASTER_STRICT_CVC5_RESULTS", some "1")]
    }
    unless output.exitCode == 0 do
      throw <| IO.userError <|
        "strict tactic integration guard failed\n" ++ output.stdout ++ output.stderr

#eval strictTacticIntegrationGuard

end Test.StrictResultPolicy
