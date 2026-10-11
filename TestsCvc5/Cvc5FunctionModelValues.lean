import Blaster
import Blaster.StateMachine

namespace Test.Cvc5FunctionModelValues

open Lean Elab Command Blaster.Smt Blaster.StateMachine

-- `#blaster` options are identifiers, which quotations must not rename.
set_option hygiene false

/-! ## Test objectives to validate function values in cvc5 counterexamples

    cvc5 1.4.1 does not return reliable `get-value` results for function
    values stored in datatype fields: the value of `s : FunBox` can be
    `(FunBox.mk (FunBox.mk.0 $0) 1)`, which refers to `s` itself. Blaster
    therefore retrieves such values type-directed, one selector term at a time
    (see `retrieveTypedValue`).

    `solve-result: 1` only pins the verdict. The tests below also check the
    displayed values: each command is elaborated with its messages captured,
    every displayed value is parsed and evaluated (`lambda`, `ite`, integer
    arithmetic, z3's `store` and constant arrays, constructors), and the
    falsified goal is checked on these values. A self-referential value
    cannot be evaluated, so it fails these tests. Function values are invented
    by the solver, so their spelling is not pinned.

    Covered:
     - function-valued inputs: plain, constrained, and with a datatype domain;
     - function-typed structure fields: plain, constrained, nested
       structures, two function fields, and `Option`;
     - a function returning a structure with a function field, for which cvc5
       only provides a value containing such datatype values: the
       counterexample is explicitly unavailable, with a warning naming the
       raw value, and the verdict stays Falsified;
     - `solver-mode: first` and `solver-mode: agree` on the same goals. In
       `agree`, the displayed counterexample is z3's (complete evidence ties
       are broken in favor of z3), so the absence of warnings is what pins
       the cvc5 retrieval;
     - `#bmc` with a function-valued input in single cvc5, `first` and
       `agree` modes. -/

structure FunBox where
  fn : Int → Int
  k : Int

structure Outer where
  inner : FunBox
  b : Int

structure Two where
  f : Int → Int
  g : Int → Int

/-! # Evaluating displayed counterexample values -/

/-- A displayed counterexample value. Function values are closures: a
    `lambda` with its environment, a constant array, or a `store` update. -/
inductive Val where
  | int (n : Int)
  | bool (b : Bool)
  | ctor (name : String) (args : Array Val)
  | lam (params : Array String) (body : Sexp) (env : List (String × Val))
  | const (v : Val)
  | store (f : Val) (idx : Array Val) (v : Val)

instance : Inhabited Val := ⟨.int 0⟩

partial def Val.toString : Val → String
  | .int n => s!"{n}"
  | .bool b => s!"{b}"
  | .ctor c args => if args.isEmpty then c else s!"({c} {String.intercalate " " (args.toList.map Val.toString)})"
  | _ => "<function>"

instance : ToString Val := ⟨Val.toString⟩

partial def Val.beq? : Val → Val → Except String Bool
  | .int a, .int b => pure (a == b)
  | .bool a, .bool b => pure (a == b)
  | .ctor c as, .ctor d bs =>
      if c != d || as.size != bs.size then pure false
      else (as.zip bs).allM fun (a, b) => Val.beq? a b
  | a, b => throw s!"cannot compare {a} and {b}"

def Val.asInt : Val → Except String Int
  | .int n => pure n
  | v => throw s!"expected an integer, got {v}"

def Val.asBool : Val → Except String Bool
  | .bool b => pure b
  | v => throw s!"expected a Boolean, got {v}"

/-- Field `i` of a value of constructor `ctor`. -/
def Val.field (v : Val) (ctor : String) (i : Nat) : Except String Val :=
  match v with
  | .ctor c args =>
      if c == ctor then
        match args[i]? with
        | some a => pure a
        | none => throw s!"{v} has no field {i}"
      else throw s!"expected constructor {ctor}, got {v}"
  | _ => throw s!"expected constructor {ctor}, got {v}"

private def isCtorName (a : String) : Bool :=
  match a.toList with
  | c :: _ => c.isUpper
  | [] => false

mutual

/-- Apply a function value to `args`. -/
partial def Val.apply (f : Val) (args : Array Val) : Except String Val :=
  match f with
  | .lam names body env =>
      if args.size != names.size then throw "arity mismatch"
      else eval ((names.zip args).toList ++ env) body
  | .const v => pure v
  | .store g idx v => do
      if ← (idx.zip args).allM fun (i, x) => Val.beq? i x then pure v else g.apply args
  | v => throw s!"expected a function value, got {v}"

/-- Evaluate a closed value term. Bound variables are looked up in `env`;
    any other unknown symbol is an error. -/
partial def eval (env : List (String × Val)) : Sexp → Except String Val
  | .atom a =>
      match env.lookup a with
      | some v => pure v
      | none =>
          if a == "true" then pure (.bool true)
          else if a == "false" then pure (.bool false)
          else match a.toInt? with
            | some n => pure (.int n)
            | none => if isCtorName a then pure (.ctor a #[]) else throw s!"unknown symbol {a}"
  | .app #[.atom "lambda", .app params, body] => do
      let names ← params.mapM fun
        | .app #[.atom x, _] => pure x
        | p => throw s!"malformed binder {Sexp.toRaw p}"
      pure (.lam names body env)
  | .app #[.atom "as", c, _] => eval env c
  | .app #[.app #[.atom "as", .atom "const", _], v] => return .const (← eval env v)
  | .app #[.atom "ite", c, a, b] => do
      if ← (← eval env c).asBool then eval env a else eval env b
  | .app #[.atom "not", a] => return .bool !(← (← eval env a).asBool)
  | .app #[.atom "=", a, b] => return .bool (← Val.beq? (← eval env a) (← eval env b))
  | .app #[.atom "-", a] => return .int (-(← (← eval env a).asInt))
  -- A parenthesized display argument, e.g. `(-1)`.
  | .app #[e] => eval env e
  | .app elems => do
      let args ← (elems.extract 1).mapM (eval env)
      let head : Option String := match (elems[0]? : Option Sexp) with
        | some (.atom h) => some h
        | _ => none
      let some head := head | do
        -- Application of a function value.
        (← eval env elems[0]!).apply args
      let ints := fun () => args.mapM Val.asInt
      let cmp (op : Int → Int → Bool) : Except String Val := do
        let xs ← ints ()
        let some a := xs[0]? | throw s!"{head} without arguments"
        let some b := xs[1]? | throw s!"{head} with one argument"
        return .bool (op a b)
      match head with
      | "and" => return .bool (← args.allM Val.asBool)
      | "or" => return .bool (← args.anyM Val.asBool)
      | "+" => return .int ((← ints ()).foldl (· + ·) 0)
      | "*" => return .int ((← ints ()).foldl (· * ·) 1)
      | "-" =>
          let xs ← ints ()
          return .int (xs.extract 1 |>.foldl (· - ·) xs[0]!)
      | "<" => cmp (· < ·)
      | "<=" => cmp (· ≤ ·)
      | ">" => cmp (· > ·)
      | ">=" => cmp (· ≥ ·)
      | "@" =>
          let some f := args[0]? | throw "@ without arguments"
          f.apply (args.extract 1)
      | "store" =>
          let some f := args[0]? | throw "store without arguments"
          let some v := args.back? | throw "store without a value"
          return .store f (args.extract 1 (args.size - 1)) v
      | _ =>
          match env.lookup head with
          | some f => f.apply args
          | none =>
              if isCtorName head then pure (.ctor head args)
              else throw s!"cannot evaluate {Sexp.toRaw (.app elems)}"

end

/-- Evaluate a displayed counterexample value (`C a b` displays `(C a b)`,
    and negative integers display as `-n`). -/
def parseDisplay (text : String) : Except String Val := do
  match Sexp.parseMany s!"({text})" with
  | .ok #[.app #[e]] => eval [] e
  | .ok #[e] => eval [] e
  | .ok _ => throw s!"cannot parse {text}"
  | .error e => throw s!"cannot parse {text}: {e}"

/-- Messages logged by one captured command. -/
structure Run where
  infos : Array String := #[]
  warnings : Array String := #[]
  errors : Array String := #[]

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

/-- Elaborate `cmd` and return its messages, including those of its
    asynchronous `#blaster` task (as `#guard_msgs` does). They are removed
    from the log, so the expected `#bmc` counterexample errors do not fail
    this file. -/
def capture (cmd : Syntax) : CommandElabM Run := do
  let savedMessages := (← get).messages
  let savedTasks := (← get).snapshotTasks
  modify fun s => { s with messages := {}, snapshotTasks := #[] }
  withReader ({ · with snap? := none }) do
    elabCommandTopLevel cmd
  let messages := (← get).messages ++
    (← get).snapshotTasks.foldl (· ++ ·.get.getAll.foldl (· ++ ·.diagnostics.msgLog) {}) {}
  modify fun s => { s with messages := savedMessages, snapshotTasks := savedTasks }
  let mut run : Run := {}
  for m in messages.toList do
    let text ← m.data.toString
    match m.severity with
    | .information => run := { run with infos := run.infos.push text }
    | .warning => run := { run with warnings := run.warnings.push text }
    | .error => run := { run with errors := run.errors.push text }
  return run

/-- Displayed value of counterexample variable `name` (a line ` - name: v`). -/
def Run.value (run : Run) (name : String) : Except String Val := do
  let lines := run.infos ++ run.errors
  let some line := lines.find? fun l => contains l s!"{name}: "
    | throw s!"no counterexample value for {name} in {lines}"
  let text := (line.splitOn s!"{name}: ").drop 1 |> String.intercalate s!"{name}: "
  if contains text "<counterexample unavailable>" then
    throw s!"counterexample value of {name} is unavailable: {run.warnings}"
  parseDisplay text.trim

def check (cond : Bool) (message : String) : Except String Unit :=
  unless cond do throw message

def runCheck (result : Except String Unit) : CommandElabM Unit :=
  match result with
  | .ok () => pure ()
  | .error e => throwError e

/-- Elaborate `cmd`, require the expected Falsified verdict and complete
    evidence (no warning), and check `goal` on the displayed values. -/
def expectFalsified (cmd : Syntax) (goal : Run → Except String Unit) : CommandElabM Unit := do
  let run ← capture cmd
  runCheck do
    check (run.errors.isEmpty) s!"unexpected errors: {run.errors}"
    check (run.warnings.isEmpty) s!"unexpected warnings: {run.warnings}"
    check (run.infos.any (contains · "Expected Falsified")) s!"verdict is not Falsified: {run.infos}"
    goal run

/-! # Function-valued inputs -/

run_cmd expectFalsified (← `(command|
  #blaster (solver: cvc5) (timeout: 10) (gen-cex: 1) (solve-result: 1)
    [∀ (f : Int → Int) (x : Int), f x = f (x + 1)])) fun run => do
  let f ← run.value "f"; let x ← (← run.value "x").asInt
  check (!(← Val.beq? (← f.apply #[.int x]) (← f.apply #[.int (x + 1)]))) "f x = f (x + 1)"

run_cmd expectFalsified (← `(command|
  #blaster (solver: cvc5) (timeout: 10) (gen-cex: 1) (solve-result: 1)
    [∀ (f : Int → Int), f 1 = 5 → f 2 = 6 → f 3 = 7])) fun run => do
  let f ← run.value "f"
  check ((← (← f.apply #[.int 1]).asInt) == 5) "f 1 ≠ 5"
  check ((← (← f.apply #[.int 2]).asInt) == 6) "f 2 ≠ 6"
  check ((← (← f.apply #[.int 3]).asInt) != 7) "f 3 = 7"

-- A function over a datatype holding a function value.
run_cmd expectFalsified (← `(command|
  #blaster (solver: cvc5) (timeout: 10) (gen-cex: 1) (solve-result: 1)
    [∀ (h : FunBox → Int) (b : FunBox), h b = b.k])) fun run => do
  let h ← run.value "h"; let b ← run.value "b"
  let k ← (← b.field "Test.Cvc5FunctionModelValues.FunBox.mk" 1).asInt
  check ((← (← h.apply #[b]).asInt) != k) "h b = b.k"

/-! # Function-typed structure fields -/

private def funBoxMk := "Test.Cvc5FunctionModelValues.FunBox.mk"

run_cmd expectFalsified (← `(command|
  #blaster (solver: cvc5) (timeout: 10) (gen-cex: 1) (solve-result: 1)
    [∀ (s : FunBox) (x : Int), s.fn x = x])) fun run => do
  let s ← run.value "s"; let x ← (← run.value "x").asInt
  let fn ← s.field funBoxMk 0
  check ((← (← fn.apply #[.int x]).asInt) != x) "s.fn x = x"

run_cmd expectFalsified (← `(command|
  #blaster (solver: cvc5) (timeout: 10) (gen-cex: 1) (solve-result: 1)
    [∀ (s : FunBox), s.fn 1 = 5 → s.fn 2 = 6 → s.k = s.fn 3])) fun run => do
  let s ← run.value "s"
  let fn ← s.field funBoxMk 0
  let k ← (← s.field funBoxMk 1).asInt
  check ((← (← fn.apply #[.int 1]).asInt) == 5) "s.fn 1 ≠ 5"
  check ((← (← fn.apply #[.int 2]).asInt) == 6) "s.fn 2 ≠ 6"
  check ((← (← fn.apply #[.int 3]).asInt) != k) "s.k = s.fn 3"

run_cmd expectFalsified (← `(command|
  #blaster (solver: cvc5) (timeout: 10) (gen-cex: 1) (solve-result: 1)
    [∀ (s : Outer) (x : Int), s.inner.fn x = x + s.b])) fun run => do
  let s ← run.value "s"; let x ← (← run.value "x").asInt
  let inner ← s.field "Test.Cvc5FunctionModelValues.Outer.mk" 0
  let b ← (← s.field "Test.Cvc5FunctionModelValues.Outer.mk" 1).asInt
  let fn ← inner.field funBoxMk 0
  discard <| (← inner.field funBoxMk 1).asInt
  check ((← (← fn.apply #[.int x]).asInt) != x + b) "s.inner.fn x = x + s.b"

run_cmd expectFalsified (← `(command|
  #blaster (solver: cvc5) (timeout: 10) (gen-cex: 1) (solve-result: 1)
    [∀ (s : Two), s.f 0 = s.g 0])) fun run => do
  let s ← run.value "s"
  let f ← s.field "Test.Cvc5FunctionModelValues.Two.mk" 0
  let g ← s.field "Test.Cvc5FunctionModelValues.Two.mk" 1
  check (!(← Val.beq? (← f.apply #[.int 0]) (← g.apply #[.int 0]))) "s.f 0 = s.g 0"

run_cmd expectFalsified (← `(command|
  #blaster (solver: cvc5) (timeout: 10) (gen-cex: 1) (solve-result: 1)
    [∀ (o : Option (Int → Int)), o.isSome → ∀ x, (o.getD id) x = x])) fun run => do
  let o ← run.value "o"; let x ← (← run.value "x").asInt
  let f ← o.field "Option.some" 0
  check ((← (← f.apply #[.int x]).asInt) != x) "(o.getD id) x = x"

/-! # Unavailable function values

    cvc5 only provides the value of `f : Int → FunBox` as a `lambda` whose
    body contains `FunBox` values; the one returned here also refers to `f`
    itself. It is not displayed: the counterexample is explicitly unavailable,
    the warning keeps the raw value, and the verdict stays Falsified. -/

private def unavailableWarning (run : Run) : Bool :=
  run.warnings.any fun w =>
    contains w "Counterexample unavailable from cvc5; the Falsified verdict is preserved" &&
    contains w "contains datatype values holding function values" &&
    contains w "raw value: (lambda"

run_cmd do
  let run ← capture (← `(command|
    #blaster (solver: cvc5) (timeout: 10) (gen-cex: 1) (solve-result: 1)
      [∀ (f : Int → FunBox), (f 1).fn 2 = (f 1).k]))
  runCheck do
    check run.errors.isEmpty s!"unexpected errors: {run.errors}"
    check (run.infos.any (contains · "Expected Falsified")) s!"verdict is not Falsified: {run.infos}"
    check (run.infos.any (contains · " - f: <counterexample unavailable>")) s!"f is displayed: {run.infos}"
    check (unavailableWarning run) s!"missing unavailable-evidence warning: {run.warnings}"

/-! # Concurrent modes -/

run_cmd expectFalsified (← `(command|
  #blaster (solver-mode: first) (timeout: 10) (gen-cex: 1) (solve-result: 1)
    [∀ (s : FunBox), s.fn 1 = 5 → s.fn 2 = 6 → s.k = s.fn 3])) fun run => do
  let s ← run.value "s"
  let fn ← s.field funBoxMk 0
  let k ← (← s.field funBoxMk 1).asInt
  check ((← (← fn.apply #[.int 1]).asInt) == 5) "s.fn 1 ≠ 5"
  check ((← (← fn.apply #[.int 2]).asInt) == 6) "s.fn 2 ≠ 6"
  check ((← (← fn.apply #[.int 3]).asInt) != k) "s.k = s.fn 3"

-- No warning: the cvc5 evidence (type-directed) is complete too.
run_cmd expectFalsified (← `(command|
  #blaster (solver-mode: agree) (timeout: 10) (gen-cex: 1) (solve-result: 1)
    [∀ (s : FunBox), s.fn 1 = 5 → s.fn 2 = 6 → s.k = s.fn 3])) fun run => do
  let s ← run.value "s"
  let fn ← s.field funBoxMk 0
  let k ← (← s.field funBoxMk 1).asInt
  check ((← (← fn.apply #[.int 1]).asInt) == 5) "s.fn 1 ≠ 5"
  check ((← (← fn.apply #[.int 2]).asInt) == 6) "s.fn 2 ≠ 6"
  check ((← (← fn.apply #[.int 3]).asInt) != k) "s.k = s.fn 3"

run_cmd expectFalsified (← `(command|
  #blaster (solver-mode: agree) (timeout: 10) (gen-cex: 1) (solve-result: 1)
    [∀ (s : Outer) (x : Int), s.inner.fn x = x + s.b])) fun run => do
  let s ← run.value "s"; let x ← (← run.value "x").asInt
  let inner ← s.field "Test.Cvc5FunctionModelValues.Outer.mk" 0
  let b ← (← s.field "Test.Cvc5FunctionModelValues.Outer.mk" 1).asInt
  let fn ← inner.field funBoxMk 0
  check ((← (← fn.apply #[.int x]).asInt) != x + b) "s.inner.fn x = x + s.b"

-- Whichever solver wins, its evidence is either correct or explicitly unavailable.
run_cmd do
  let run ← capture (← `(command|
    #blaster (solver-mode: first) (timeout: 10) (gen-cex: 1) (solve-result: 1)
      [∀ (f : Int → FunBox), (f 1).fn 2 = (f 1).k]))
  runCheck do
    check run.errors.isEmpty s!"unexpected errors: {run.errors}"
    check (run.infos.any (contains · "Expected Falsified")) s!"verdict is not Falsified: {run.infos}"
    if run.infos.any (contains · " - f: <counterexample unavailable>") then
      check (unavailableWarning run) s!"missing unavailable-evidence warning: {run.warnings}"
    else
      check run.warnings.isEmpty s!"unexpected warnings: {run.warnings}"
      let b ← (← run.value "f").apply #[.int 1]
      let fn ← b.field funBoxMk 0
      check (!(← Val.beq? (← fn.apply #[.int 2]) (← b.field funBoxMk 1))) "(f 1).fn 2 = (f 1).k"

-- cvc5 evidence fails (warning and agreement artifacts); z3's complete
-- evidence is displayed and the verdict stays Falsified.
run_cmd do
  let run ← capture (← `(command|
    #blaster (solver-mode: agree) (timeout: 10) (gen-cex: 1) (solve-result: 1)
      [∀ (f : Int → FunBox), (f 1).fn 2 = (f 1).k]))
  runCheck do
    check run.errors.isEmpty s!"unexpected errors: {run.errors}"
    check (run.infos.any (contains · "Expected Falsified")) s!"verdict is not Falsified: {run.infos}"
    check (unavailableWarning run) s!"missing unavailable-evidence warning: {run.warnings}"
    check (run.warnings.any (contains · "Agreement diagnostics saved")) s!"missing agreement artifacts: {run.warnings}"
    let b ← (← run.value "f").apply #[.int 1]
    let fn ← b.field funBoxMk 0
    check (!(← Val.beq? (← fn.apply #[.int 2]) (← b.field funBoxMk 1))) "(f 1).fn 2 = (f 1).k"

/-! # Incremental checks with a function-valued input

    The invariant fails at depth 1 exactly when `f 0 > 1`. -/

instance applyMachine : StateMachine (Int → Int) Int where
  init _ := 0
  next f s := f s
  assumptions _ _ := True
  invariants _ s := s ≤ 1

def expectBmcCounterexample (cmd : Syntax) : CommandElabM Unit := do
  let run ← capture cmd
  runCheck do
    check (run.warnings.isEmpty) s!"unexpected warnings: {run.warnings}"
    check (run.errors.any (contains · "Falsified")) s!"#bmc did not fail: {run.errors}"
    check (run.errors.any (contains · "Counterexample detected at Depth 1")) s!"no counterexample at depth 1: {run.errors}"
    let f ← run.value "input@1»"
    check ((← (← f.apply #[.int 0]).asInt) > 1) "f 0 ≤ 1"

run_cmd expectBmcCounterexample (← `(command| #bmc (solver: cvc5) (max-depth: 3) [applyMachine]))
run_cmd expectBmcCounterexample (← `(command| #bmc (solver-mode: first) (max-depth: 3) [applyMachine]))
run_cmd expectBmcCounterexample (← `(command| #bmc (solver-mode: agree) (max-depth: 3) [applyMachine]))

end Test.Cvc5FunctionModelValues
