import Blaster
import Blaster.StateMachine

namespace Test.Cvc5FunctionValues

open Blaster.Options Blaster.Optimize Blaster.Smt Blaster.StateMachine

/-! ## Test objectives to validate function values on the cvc5 backend

    Blaster encodes Lean function values as SMT `Array`s (`lambda`, `select`).
    cvc5 receives the higher-order rendering of that encoding under `HO_ALL`
    (see `SmtCommand.toHigherOrder`); z3 receives it unchanged. Each encoded
    construct is covered by a valid goal (unsat) and a falsified goal (sat):
     - canonicalization (`@canon…`) and application of quantified functions,
       over `Int` and over the restricted `Nat` domain;
     - multi-argument functions;
     - function equality and extensionality;
     - Lean `lambda` terms passed as arguments;
     - function-typed structure fields;
     - polymorphic functions;
     - `solver-mode: first` and `solver-mode: agree`, where z3 gets the
       canonical encoding and cvc5 the higher-order rendering of the same
       query;
     - incremental `check-sat-assuming` checks (`#bmc`) over a function-valued
       input, where cvc5 switches to `HO_ALL` in the middle of the query.
    Function counterexample values are solver-invented `lambda` terms, so they
    are not pinned; `solve-result: 1` asserts the Falsified verdict and that
    `get-value` on function terms succeeds.

    The last section checks that cvc5 rejections are still reported as errors:
    the rendering does not hide or fall back on queries cvc5 cannot parse. -/

structure FunBox where
  fn : Int → Int
  k : Int

/-! # Canonicalization and application -/

#blaster (solver: cvc5) (timeout: 10) [∀ (f : Int → Int) (x : Int), f x = f x]
#blaster (solver: cvc5) (timeout: 10) (gen-cex: 1) (solve-result: 1) [∀ (f : Int → Int) (x : Int), f x = f (x + 1)]

#blaster (solver: cvc5) (timeout: 10) [∀ (f : Nat → Nat) (x : Nat), f x ≥ 0]
#blaster (solver: cvc5) (timeout: 10) (gen-cex: 1) (solve-result: 1) [∀ (f : Nat → Nat) (x : Nat), f x > 0]

#blaster (solver: cvc5) (timeout: 10) [∀ (f : Int → Int → Int) (x y : Int), f x y = f x y]
#blaster (solver: cvc5) (timeout: 10) (gen-cex: 1) (solve-result: 1) [∀ (f : Int → Int → Int) (x y : Int), f x y = f y x]

/-! # Function equality -/

#blaster (solver: cvc5) (timeout: 10) [∀ (f g : Int → Int), f = g → f 3 = g 3]
#blaster (solver: cvc5) (timeout: 10) (gen-cex: 1) (solve-result: 1) [∀ (f g : Int → Int), f 3 = g 3 → f = g]
#blaster (solver: cvc5) (timeout: 10) [∀ (f g : Int → Int), (∀ x, f x = g x) → f = g]
#blaster (solver: cvc5) (timeout: 10) [∀ (f g : Nat → Nat), (∀ x, f x = g x) → f = g]

/-! # Lambda terms -/

#blaster (solver: cvc5) (timeout: 10) [∀ (g : (Int → Int) → Int), g (fun y => y + 1) = g (fun y => 1 + y)]
#blaster (solver: cvc5) (timeout: 10) [∀ (g : (Int → Int) → Int) (c : Int), g (fun y => y + c) = g (fun y => c + y)]
#blaster (solver: cvc5) (timeout: 10) (gen-cex: 1) (solve-result: 1) [∀ (g : (Int → Int) → Int), g (fun y => y + 1) = g (fun y => y + 2)]

/-! # Function-typed structure fields -/

#blaster (solver: cvc5) (timeout: 10) [∀ (s : FunBox) (x : Int), s.fn x = s.fn x]
#blaster (solver: cvc5) (timeout: 10) (gen-cex: 1) (solve-result: 1) [∀ (s : FunBox) (x : Int), s.fn x = x]

/-! # Polymorphic functions -/

#blaster (solver: cvc5) (timeout: 10) [∀ (α : Type) (f : α → α) (x : α), f x = f x]
#blaster (solver: cvc5) (timeout: 10) (gen-cex: 1) (solve-result: 1) [∀ (α : Type) (f : α → α) (x : α), f x = x]

/-! # Concurrent modes -/

#blaster (solver-mode: first) (timeout: 10) [∀ (f g : Int → Int), f = g → f 3 = g 3]
#blaster (solver-mode: agree) (timeout: 10) [∀ (f g : Int → Int), f = g → f 3 = g 3]
#blaster (solver-mode: first) (timeout: 10) (gen-cex: 1) (solve-result: 1) [∀ (f : Int → Int) (x : Int), f x = f (x + 1)]
#blaster (solver-mode: agree) (timeout: 10) (gen-cex: 1) (solve-result: 1) [∀ (f : Int → Int) (x : Int), f x = f (x + 1)]
#blaster (solver-mode: agree) (timeout: 10) [∀ (g : (Int → Int) → Int), g (fun y => y + 1) = g (fun y => 1 + y)]
#blaster (solver-mode: agree) (timeout: 10) (gen-cex: 1) (solve-result: 1) [∀ (g : (Int → Int) → Int), g (fun y => y + 1) = g (fun y => y + 2)]

/-! # Incremental checks with a function-valued input -/

instance applyMachine : StateMachine (Int → Int) Int where
  init _ := 0
  next f s := if f s ≥ s then f s else s
  assumptions _ _ := True
  invariants _ s := 0 ≤ s

#bmc (solver: cvc5) (max-depth: 3) [applyMachine]
#bmc (solver-mode: first) (max-depth: 3) [applyMachine]
#bmc (solver-mode: agree) (max-depth: 3) [applyMachine]

/-! # cvc5 rejections stay visible errors

    `(_ as-array g)` is z3-only syntax that the rendering deliberately leaves
    alone. Submitting it to a live cvc5 session (after a function value has
    switched it to `HO_ALL`) must raise the cvc5 submission error. -/

/-- info: true -/
#guard_msgs in
#eval show Lean.MetaM Bool from do
  let sOpts : BlasterOptions := { solver := some .cvc5, timeout := some 10 }
  let env : TranslateEnv := default
  let env := { env with optEnv.options.solverOptions := sOpts }
  let g := mkNormalSymbol "g"
  let a := mkNormalSymbol "a"
  let funSort := arraySort #[intSort, intSort]
  let (message, _) ← (withSmtSessionOwner do
    setBlasterProcess
    try
      declareFun g #[intSort] intSort
      declareConst a funSort
      assertTerm (eqSmt (smtSimpleVarId a) (asArraySmt (.SimpleIdent g)))
      pure "cvc5 accepted an unsupported command"
    catch error => error.toMessageData.toString).run env
  return (message.splitOn "solver=cvc5; stage=command submission").length > 1 &&
    (message.splitOn "as-array").length > 1

end Test.Cvc5FunctionValues
