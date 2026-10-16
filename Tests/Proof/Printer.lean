import Blaster

/-! The printer of exported proofs (`Blaster/Proof/Export/Print.lean`): a
declaration printed as an exported file prints it, then read back with
`kernel%`, is definitionally the declaration (the text differs only by the
`let`s of its shared subterms). A wrongly named variable can still give a
well-typed term, so each check compares the values, not only their types. -/

open Lean Meta Elab Command Blaster.Proof.Export

/-- Print the definition `c`, elaborate the text as `c.printed`, and require
its value to be definitionally equal to `c`'s. -/
elab "#roundTrip " id:ident : command => do
  let c ← liftCoreM (realizeGlobalConstNoOverload id)
  let info ← getConstInfo c
  let printed := c ++ `printed
  let params := if info.levelParams.isEmpty then ""
    else ".{" ++ ", ".intercalate (info.levelParams.map toString) ++ "}"
  let names : Names := {globalName := `PrinterTest, globalRef := "PrinterTest."}
  let ((globals, text), _) :=
    ((printDecl s!"noncomputable def {printed}{params}" info.type info.value!).run names).run {}
  for cmd in globals.push text do
    match Parser.runParserCategory (← getEnv) `command cmd with
    | .ok stx => elabCommand stx
    | .error e => throwError "the printed text does not parse: {e}\n{cmd}"
  let levels := info.levelParams.map mkLevelParam
  liftTermElabM do
    unless ← isDefEq (mkConst printed levels) (mkConst c levels) do
      throwError "the printed {c} is another term:\n{text}"

/- `fun a => ⟨B, fun c => B⟩` with `B = fun x => ⟨S + S, PUnit.unit⟩` and
`S = x * a + a * x`. `B` mentions the universe `u`, so it is not shared: it is
printed twice, with `a` one and two binders away. `S` is shared, as a `let`
after the binder of `x` in each: the `let` must name `a`, not `c`. -/
run_meta do
  let u := mkLevelParam `u
  let nat := mkConst ``Nat
  let value ← withLocalDeclD `a nat fun a => do
    let b ← withLocalDeclD `x nat fun x => do
      let s := mkApp2 (mkConst ``Nat.add) (mkApp2 (mkConst ``Nat.mul) x a)
        (mkApp2 (mkConst ``Nat.mul) a x)
      let body ← mkAppM ``PProd.mk #[mkApp2 (mkConst ``Nat.add) s s, mkConst ``PUnit.unit [u]]
      mkLambdaFVars #[x] body
    let twice ← withLocalDeclD `c nat fun c => mkLambdaFVars #[c] b
    mkLambdaFVars #[a] (← mkAppM ``PProd.mk #[b, twice])
  let type ← inferType value
  addDecl (.defnDecl {name := `PrinterTest.unsharedBinder, levelParams := [`u], type, value,
                      hints := .opaque, safety := .safe})

#roundTrip PrinterTest.unsharedBinder

/-- A shared subterm under binders and through a projection and a numeral. -/
def PrinterTest.shared (p : Nat × Nat) (n : Nat) : Nat :=
  let q := p.1 * n + p.2 * n + 7
  q + q + (fun (m : Nat) => p.1 * n + p.2 * n + 7 + m) 3

#roundTrip PrinterTest.shared
