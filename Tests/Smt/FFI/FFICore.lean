import Blaster.Smt.FFI
open Blaster.Smt.FFI Blaster.Smt

/-- info: env-empty -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  let st ← BuildState.mk ctx
  IO.println s!"env-{if st.sorts.isEmpty then "empty" else "nonempty"}"

/-- info: sorts-ok -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  BuildM.run ctx do
    let _ ← buildSort Blaster.Smt.intSort
    let _ ← buildSort Blaster.Smt.boolSort
    let _ ← buildSort (Blaster.Smt.arraySort #[Blaster.Smt.intSort, Blaster.Smt.boolSort])
    IO.println "sorts-ok"

/-- info: uninterp-ok -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  BuildM.run ctx do
    let _ ← buildSort (.SymbolSort (Blaster.Smt.mkNormalSymbol "MySort"))
    let _ ← buildSort (.SymbolSort (Blaster.Smt.mkNormalSymbol "MySort"))
    IO.println "uninterp-ok"

/-- info: lits-ok -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  BuildM.run ctx do
    let _ ← buildTerm (.NumTerm 42)
    let _ ← buildTerm (.BoolTerm true)
    let _ ← buildTerm (.StrTerm "\"hi\"")
    IO.println "lits-ok"

/-- info: decl-ok -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  BuildM.run ctx do
    runCommand (.declareConst (.NormalSymbol "x") Blaster.Smt.intSort)
    let _ ← buildTerm (.SmtIdent (.SimpleIdent (.NormalSymbol "x")))
    -- also exercise a declared function application
    runCommand (.declareFun (.NormalSymbol "f") #[Blaster.Smt.intSort] Blaster.Smt.intSort)
    let _ ← buildTerm (.AppTerm (.SimpleIdent (.NormalSymbol "f")) #[.NumTerm 3])
    -- also exercise an uninterpreted sort declaration
    runCommand (.declareSort (.NormalSymbol "S") 0)
    IO.println "decl-ok"

/-- info: ops-ok -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  BuildM.run ctx do
    runCommand (.declareConst (.NormalSymbol "x") Blaster.Smt.intSort)
    runCommand (.declareConst (.NormalSymbol "s") Blaster.Smt.stringSort)
    runCommand (.declareConst (.NormalSymbol "a")
      (Blaster.Smt.arraySort #[Blaster.Smt.intSort, Blaster.Smt.intSort]))
    let x : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "x"))
    let s : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "s"))
    let a : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "a"))
    let op (o : String) (as : Array SmtTerm) : SmtTerm :=
      .AppTerm (.SimpleIdent (.ReservedSymbol o)) as
    -- Build a term, then confirm Z3 flagged no error building it. The context uses a
    -- no-op error handler, so a sort mismatch would otherwise pass silently; Z3 resets
    -- the error code at the start of every API call, so we check immediately after.
    let chk (label : String) (t : SmtTerm) : BuildM Unit := do
      let _ ← buildTerm t
      let ec ← ctx.errorCode
      if ec != 0 then throw (IO.userError s!"{label}: z3 error {ec} ({← ctx.errorMsg ec})")
    -- One operator per `chk`, with the operator under test OUTERMOST: `buildTerm`
    -- constructs args first, and Z3 resets its error code at the head of each API
    -- call, so only the head operator's construction is what `errorCode` reflects.
    -- integer arithmetic: unary -, binary -, +, *, div, mod, abs, ^, to_int
    chk "neg" (op "-" #[x])
    chk "sub" (op "-" #[x, .NumTerm 1])
    chk "add" (op "+" #[x, .NumTerm 2])
    chk "mul" (op "*" #[x, .NumTerm 2])
    chk "div" (op "div" #[x, .NumTerm 3])
    chk "mod" (op "mod" #[x, .NumTerm 4])
    chk "abs" (op "abs" #[x])
    chk "pow" (op "^" #[x, .NumTerm 2])
    chk "to_int" (op "to_int" #[op "^" #[x, .NumTerm 2]])
    -- boolean / core: <, <=, =, not, =>, or, and, ite
    chk "lt"   (op "<" #[x, .NumTerm 0])
    chk "le"   (op "<=" #[.NumTerm 0, x])
    chk "eq"   (op "=" #[x, .NumTerm 0])
    chk "not"  (op "not" #[op "=" #[x, .NumTerm 1]])
    chk "impl" (op "=>" #[op "<" #[x, .NumTerm 0], op "<" #[x, .NumTerm 1]])
    chk "or"   (op "or" #[op "<" #[x, .NumTerm 0], op "<=" #[.NumTerm 0, x]])
    chk "and"  (op "and" #[op "<" #[x, .NumTerm 0], op "<=" #[.NumTerm 0, x]])
    chk "ite"  (op "ite" #[op "<" #[x, .NumTerm 0], .NumTerm 1, .NumTerm 2])
    -- arrays: select
    chk "select" (op "select" #[a, x])
    -- strings: str.len, str.++, str.<, str.<=, str.replace
    chk "strlen" (op "str.len" #[s])
    chk "strcat" (op "str.++" #[s, s])
    chk "strlt"  (op "str.<" #[s, s])
    chk "strle"  (op "str.<=" #[s, s])
    chk "strrep" (op "str.replace" #[s, s, s])
    IO.println "ops-ok"

open Blaster.Smt in
/-- info: r1=valid r2=falsified cex=x: 1 -/
#guard_msgs in
#eval do
  -- Valid: ¬(x = x) is unsat
  let s1 ← Z3Session.create
  s1.runCommand (.declareConst (.NormalSymbol "x") intSort)
  let x : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "x"))
  s1.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "not")) #[
    .AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[x, x]])
  let r1 ← s1.checkSat #[] false
  -- Falsified: (x = 1) is sat; extract the model (genCex := true) for x.
  let s2 ← Z3Session.create
  s2.runCommand (.declareConst (.NormalSymbol "x") intSort)
  s2.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[x, .NumTerm 1])
  let topVars : Array (List TopLevelVar) := #[[⟨.NormalSymbol "x", `x, Lean.mkConst ``Int, ⟨`x⟩⟩]]
  let r2 ← s2.checkSat topVars true
  let showR := fun r => match r with | Result.Valid => "valid" | Result.Falsified _ => "falsified" | Result.Undetermined => "undet"
  let cex := match r2 with | Result.Falsified c => c.messages | _ => []
  IO.println s!"r1={showR r1} r2={showR r2} cex={String.intercalate ", " cex}"

open Blaster.Smt in
/-- info: quant r1=valid r2=falsified r3=valid multi=valid lam=valid pat=valid -/
#guard_msgs in
#eval do
  let xref : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "x"))
  let yref : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "y"))
  let eqOp  := fun (a b : SmtTerm) => SmtTerm.AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[a, b]
  let addOp := fun (a b : SmtTerm) => SmtTerm.AppTerm (.SimpleIdent (.ReservedSymbol "+")) #[a, b]
  let notOp := fun (a : SmtTerm)   => SmtTerm.AppTerm (.SimpleIdent (.ReservedSymbol "not")) #[a]
  let showR := fun r => match r with | Result.Valid => "valid" | Result.Falsified _ => "falsified" | Result.Undetermined => "undet"
  -- Build `t` in the session and fail loudly on any silent Z3 error. The context uses a
  -- no-op error handler, so a rejected quantifier/lambda/pattern AST (bad Z3_to_app, a
  -- pattern missing a bound var, a 0-binder lambda) would otherwise pass sat/unsat silently.
  let chk := fun (sess : Z3Session) (label : String) (t : SmtTerm) => do
    let _ ← sess.run (buildTerm t)
    let ec ← sess.ctx.errorCode
    if ec != 0 then throw (IO.userError s!"{label}: z3 error {ec} ({← sess.ctx.errorMsg ec})")
  -- r1: ∀x. x=x is valid ⇒ ¬∀ unsat ⇒ Valid
  let s1 ← Z3Session.create
  let fa : SmtTerm := .ForallTerm #[(.NormalSymbol "x", intSort)] (eqOp xref xref)
  chk s1 "r1" (notOp fa)
  s1.assert (notOp fa)
  let r1 ← s1.checkSat #[] false
  -- r2: ∃x. 100 < x is sat ⇒ Falsified
  let s2 ← Z3Session.create
  let ex : SmtTerm := .ExistsTerm #[(.NormalSymbol "x", intSort)]
    (.AppTerm (.SimpleIdent (.ReservedSymbol "<")) #[.NumTerm 100, xref])
  chk s2 "r2" ex
  s2.assert ex
  let r2 ← s2.checkSat #[] false
  -- r3: nested shadowing ∀x.(∀x. x=x) must BUILD without Z3-level collision (fresh consts)
  -- and stay valid ⇒ ¬ unsat ⇒ Valid. The chk errorCode check is what makes this bite.
  let s3 ← Z3Session.create
  let outerFa : SmtTerm := .ForallTerm #[(.NormalSymbol "x", intSort)] fa
  chk s3 "r3" (notOp outerFa)
  s3.assert (notOp outerFa)
  let r3 ← s3.checkSat #[] false
  -- multi: ∀x y. x+y = y+x  ⇒ ¬ unsat ⇒ Valid  (exercises >1 binder + the shrink pop)
  let s4 ← Z3Session.create
  let comm : SmtTerm := .ForallTerm #[(.NormalSymbol "x", intSort), (.NormalSymbol "y", intSort)]
    (eqOp (addOp xref yref) (addOp yref xref))
  chk s4 "multi" (notOp comm)
  s4.assert (notOp comm)
  let rMulti ← s4.checkSat #[] false
  -- lam: (select (λx. x+1) 5) = 6  ⇒ ¬ unsat ⇒ Valid  (exercises mkLambdaConst / Z3_to_app)
  let s5 ← Z3Session.create
  let lam : SmtTerm := .LambdaTerm #[(.NormalSymbol "x", intSort)] (addOp xref (.NumTerm 1))
  let lapp : SmtTerm := .AppTerm (.SimpleIdent (.ReservedSymbol "select")) #[lam, .NumTerm 5]
  chk s5 "lam" (notOp (eqOp lapp (.NumTerm 6)))
  s5.assert (notOp (eqOp lapp (.NumTerm 6)))
  let rLam ← s5.checkSat #[] false
  -- pat: ∀x {f(x)}. f(x)=f(x)  ⇒ ¬ unsat ⇒ Valid  (exercises Z3_mk_pattern + patternsOf)
  let s6 ← Z3Session.create
  s6.runCommand (.declareFun (.NormalSymbol "f") #[intSort] intSort)
  let fx : SmtTerm := .AppTerm (.SimpleIdent (.NormalSymbol "f")) #[xref]
  let pq : SmtTerm := .AnnotatedTerm
    (.ForallTerm #[(.NormalSymbol "x", intSort)] (eqOp fx fx)) #[.Pattern #[fx]]
  chk s6 "pat" (notOp pq)
  s6.assert (notOp pq)
  let rPat ← s6.checkSat #[] false
  IO.println s!"quant r1={showR r1} r2={showR r2} r3={showR r3} multi={showR rMulti} lam={showR rLam} pat={showR rPat}"

-- mkForallTerm emits the pattern on the quantifier body, as SMT-LIB requires.
-- Check the actual libz3 AST because satisfiability alone cannot detect a
-- silently dropped e-matching pattern.
open Blaster.Smt in
/-- info: body-pattern-ok -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  let ast ← BuildM.run ctx do
    runCommand (.declareFun (.NormalSymbol "f") #[intSort] intSort)
    let x : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "x"))
    let fx : SmtTerm := .AppTerm (.SimpleIdent (.NormalSymbol "f")) #[x]
    buildTerm (mkForallTerm none #[(.NormalSymbol "x", intSort)]
      (.AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[fx, fx])
      (some #[mkPattern #[fx]]))
  let rendered ← ctx.astToString ast
  if (rendered.splitOn ":pattern").length < 2 then
    throw (IO.userError s!"native quantifier lost body pattern: {rendered}")
  IO.println "body-pattern-ok"

-- The SMT-LIB parser drops a pattern that omits one of the bound variables.
-- The native constructor must do the same instead of silently losing the axiom.
open Blaster.Smt in
/-- info: invalid-pattern-dropped -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  let ast ← BuildM.run ctx do
    runCommand (.declareFun (.NormalSymbol "f") #[intSort] intSort)
    let x : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "x"))
    let y : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "y"))
    let fx : SmtTerm := .AppTerm (.SimpleIdent (.NormalSymbol "f")) #[x]
    buildTerm (mkForallTerm none #[(.NormalSymbol "x", intSort), (.NormalSymbol "y", intSort)]
      (.AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[x, y])
      (some #[mkPattern #[fx]]))
  let rendered ← ctx.astToString ast
  if (rendered.splitOn ":pattern").length > 1 then
    throw (IO.userError s!"invalid native pattern was retained: {rendered}")
  IO.println "invalid-pattern-dropped"

open Blaster.Smt in
/-- info: let-ok -/
#guard_msgs in
#eval do
  let s ← Z3Session.create
  s.runCommand (.declareConst (.NormalSymbol "x") intSort)
  let x : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "x"))
  -- (let ((y (+ x 1))) (= y (+ x 1))) is valid ⇒ assert its negation ⇒ unsat ⇒ Valid
  let lt : SmtTerm := .LetTerm #[(.NormalSymbol "y", .AppTerm (.SimpleIdent (.ReservedSymbol "+")) #[x, .NumTerm 1])]
    (.AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[
      .SmtIdent (.SimpleIdent (.NormalSymbol "y")),
      .AppTerm (.SimpleIdent (.ReservedSymbol "+")) #[x, .NumTerm 1]])
  s.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "not")) #[lt])
  let r ← s.checkSat #[] false
  IO.println s!"let-{if r matches Result.Valid then "ok" else "BAD"}"

open Blaster.Smt in
/-- info: dt r1=valid r2=falsified -/
#guard_msgs in
#eval do
  -- datatype `Pair` with ctor `mk`, selectors `fst`,`snd` : Int, recognizer `is-mk`.
  let mkDecl : SmtDatatypeDecl := { params := none, ctors := #[
    (.NormalSymbol "mk", some #[(.NormalSymbol "fst", intSort), (.NormalSymbol "snd", intSort)]) ] }
  let mk34 : SmtTerm := .AppTerm (.SimpleIdent (.NormalSymbol "mk")) #[.NumTerm 3, .NumTerm 4]
  let app := fun (nm : SmtSymbol) (args : Array SmtTerm) => SmtTerm.AppTerm (.SimpleIdent nm) args
  let notOp := fun t => app (.ReservedSymbol "not") #[t]
  -- r1: (and (= (fst mk34) 3) (= (snd mk34) 4) (is-mk mk34)) is valid ⇒ assert ¬ ⇒ Valid.
  --     Exercises constructor + BOTH accessors (field order → fst=.0, snd=.1) + recognizer.
  let s1 ← Z3Session.create
  s1.runCommand (.declareDataType (.NormalSymbol "Pair") mkDecl)
  let goal1 : SmtTerm := app (.ReservedSymbol "and") #[
    app (.ReservedSymbol "=") #[app (.NormalSymbol "fst") #[mk34], .NumTerm 3],
    app (.ReservedSymbol "=") #[app (.NormalSymbol "snd") #[mk34], .NumTerm 4],
    app (.NormalSymbol "is-mk") #[mk34]]
  s1.assert (notOp goal1)
  let r1 ← s1.checkSat #[] false
  -- r2: (fst mk34) = 4 is false ⇒ ¬ is true ⇒ assert ¬ ⇒ sat ⇒ Falsified.
  let s2 ← Z3Session.create
  s2.runCommand (.declareDataType (.NormalSymbol "Pair") mkDecl)
  let goal2 : SmtTerm := app (.ReservedSymbol "=") #[app (.NormalSymbol "fst") #[mk34], .NumTerm 4]
  s2.assert (notOp goal2)
  let r2 ← s2.checkSat #[] false
  let showR := fun r => match r with | Result.Valid => "valid" | Result.Falsified _ => "falsified" | Result.Undetermined => "undet"
  IO.println s!"dt r1={showR r1} r2={showR r2}"

open Blaster.Smt in
/-- info: def r1=valid r2=valid r3=valid -/
#guard_msgs in
#eval do
  -- (1) non-recursive inline: (define-fun inc ((x Int)) Int (+ x 1)); (inc 5) = 6 valid
  let s1 ← Z3Session.create
  s1.runCommand (.defineFun false (.NormalSymbol "inc") #[(.NormalSymbol "x", intSort)] intSort
    (.AppTerm (.SimpleIdent (.ReservedSymbol "+")) #[.SmtIdent (.SimpleIdent (.NormalSymbol "x")), .NumTerm 1]))
  s1.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "not")) #[
    .AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[
      .AppTerm (.SimpleIdent (.NormalSymbol "inc")) #[.NumTerm 5], .NumTerm 6]])
  let r1 ← s1.checkSat #[] false
  -- (2) qualifier-shaped macro: (define-fun isNat ((x Int)) Bool (<= 0 x)); (isNat 3) valid
  let s2 ← Z3Session.create
  s2.runCommand (.defineFun false (.NormalSymbol "isNat") #[(.NormalSymbol "x", intSort)] boolSort
    (.AppTerm (.SimpleIdent (.ReservedSymbol "<=")) #[.NumTerm 0, .SmtIdent (.SimpleIdent (.NormalSymbol "x"))]))
  s2.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "not")) #[
    .AppTerm (.SimpleIdent (.NormalSymbol "isNat")) #[.NumTerm 3]])
  let r2 ← s2.checkSat #[] false
  -- (3) recursive rec-def (concrete eval):
  --     (define-fun-rec f ((n Int)) Int (ite (<= n 0) 0 (+ n (f (- n 1))))); f 0 = 0 valid
  let s3 ← Z3Session.create
  let nref : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "n"))
  s3.runCommand (.defineFun true (.NormalSymbol "f") #[(.NormalSymbol "n", intSort)] intSort
    (.AppTerm (.SimpleIdent (.ReservedSymbol "ite")) #[
      .AppTerm (.SimpleIdent (.ReservedSymbol "<=")) #[nref, .NumTerm 0],
      .NumTerm 0,
      .AppTerm (.SimpleIdent (.ReservedSymbol "+")) #[nref,
        .AppTerm (.SimpleIdent (.NormalSymbol "f")) #[.AppTerm (.SimpleIdent (.ReservedSymbol "-")) #[nref, .NumTerm 1]]]]))
  -- The context uses a no-op error handler, so a rejected rec-def AST (bad arity,
  -- args that aren't the body's free consts, sort mismatch) would pass silently.
  -- Fail loudly if Z3 flagged an error building the definition.
  let ec ← s3.ctx.errorCode
  if ec != 0 then throw (IO.userError s!"rec-def: z3 error {ec} ({← s3.ctx.errorMsg ec})")
  s3.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "not")) #[
    .AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[.AppTerm (.SimpleIdent (.NormalSymbol "f")) #[.NumTerm 0], .NumTerm 0]])
  let r3 ← s3.checkSat #[] false
  let showR := fun r => match r with | Result.Valid => "valid" | Result.Falsified _ => "falsified" | Result.Undetermined => "undet"
  IO.println s!"def r1={showR r1} r2={showR r2} r3={showR r3}"

open Blaster.Smt in
/-- info: alias-ok -/
#guard_msgs in
#eval do
  let s ← Z3Session.create
  s.runCommand (.defineSort (.NormalSymbol "MyInt") none intSort)
  s.runCommand (.declareConst (.NormalSymbol "z") (.SymbolSort (.NormalSymbol "MyInt")))
  s.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[
    .SmtIdent (.SimpleIdent (.NormalSymbol "z")), .NumTerm 5])
  let r ← s.checkSat #[] false
  IO.println s!"alias-{if r matches Result.Falsified _ then "ok" else "BAD"}"

open Blaster.Smt in
/-- info: assume r1=valid r2=falsified -/
#guard_msgs in
#eval do
  -- After each checkAssuming, verify Z3 flagged no error. The context uses a no-op
  -- error handler, so a rejected assumption would otherwise map to unknown/.Undetermined
  -- silently instead of throwing.
  let ecChk := fun (sess : Z3Session) (label : String) => do
    let ec ← sess.ctx.errorCode
    if ec != 0 then throw (IO.userError s!"{label}: z3 error {ec} ({← sess.ctx.errorMsg ec})")
  -- r1: assert (=> flag (not (x = x))); check assuming [flag] ⇒ flag forces ¬(x=x) ⇒ unsat ⇒ Valid
  let s1 ← Z3Session.create
  s1.runCommand (.declareConst (.NormalSymbol "flag") boolSort)
  s1.runCommand (.declareConst (.NormalSymbol "x") intSort)
  let flag : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "flag"))
  let x : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "x"))
  s1.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "=>")) #[flag,
    .AppTerm (.SimpleIdent (.ReservedSymbol "not")) #[.AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[x, x]]])
  let r1 ← s1.checkAssuming #[flag] #[] false
  ecChk s1 "r1"
  -- r2: assert (=> flag (x = 1)); check assuming [flag] ⇒ sat ⇒ Falsified
  let s2 ← Z3Session.create
  s2.runCommand (.declareConst (.NormalSymbol "flag") boolSort)
  s2.runCommand (.declareConst (.NormalSymbol "x") intSort)
  s2.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "=>")) #[flag,
    .AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[x, .NumTerm 1]])
  let r2 ← s2.checkAssuming #[flag] #[] false
  ecChk s2 "r2"
  let showR := fun r => match r with | Result.Valid => "valid" | Result.Falsified _ => "falsified" | Result.Undetermined => "undet"
  IO.println s!"assume r1={showR r1} r2={showR r2}"

open Blaster.Smt in
/-- info: lifecycle base=valid step=valid deact=falsified -/
#guard_msgs in
#eval do
  -- Exercises the exact BMC/K-induction assumption-flag lifecycle (BMC.lean:92,95;
  -- KInduction.lean:138,143,148): a guarded constraint activated by an assumption flag,
  -- a COMPOUND `(not flag)` assumption literal (KInduction step case), and permanent
  -- deactivation via `assert (not flag)` so a later check sees the constraint gone.
  let s ← Z3Session.create
  s.runCommand (.declareConst (.NormalSymbol "iflag") boolSort)
  s.runCommand (.declareConst (.NormalSymbol "dflag") boolSort)
  s.runCommand (.declareConst (.NormalSymbol "x") intSort)
  let iflag : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "iflag"))
  let dflag : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "dflag"))
  let x : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "x"))
  let app := fun (o : String) (as : Array SmtTerm) => SmtTerm.AppTerm (.SimpleIdent (.ReservedSymbol o)) as
  let notOp := fun t => app "not" #[t]
  let ecChk := fun (label : String) => do
    let ec ← s.ctx.errorCode
    if ec != 0 then throw (IO.userError s!"{label}: z3 error {ec} ({← s.ctx.errorMsg ec})")
  -- dflag guards a contradiction ¬(x=x); iflag guards x=7
  s.assert (app "=>" #[dflag, notOp (app "=" #[x, x])])
  s.assert (app "=>" #[iflag, app "=" #[x, .NumTerm 7]])
  -- base-case-like: assume [iflag, dflag] ⇒ dflag active ⇒ ¬(x=x) ⇒ unsat ⇒ Valid
  let base ← s.checkAssuming #[iflag, dflag] #[] false
  ecChk "base"
  -- step-case-like: assume [(not iflag), dflag] (COMPOUND literal) ⇒ dflag still active ⇒ Valid
  let step ← s.checkAssuming #[notOp iflag, dflag] #[] false
  ecChk "step"
  -- deactivate dflag permanently, then re-check without it ⇒ contradiction gone ⇒ sat ⇒ Falsified
  s.assert (notOp dflag)
  let deact ← s.checkAssuming #[notOp iflag] #[] false
  ecChk "deact"
  let showR := fun r => match r with | Result.Valid => "valid" | Result.Falsified _ => "falsified" | Result.Undetermined => "undet"
  IO.println s!"lifecycle base={showR base} step={showR step} deact={showR deact}"

open Blaster.Smt in
/-- info: cancel-path r1=valid r2=falsified -/
#guard_msgs in
#eval do
  -- No-token path: `runCheckCancellable` calls the check DIRECTLY (no task/poll), so the
  -- verdicts must match the plain `checkSat`. r1: ¬(x=x) unsat ⇒ Valid; r2: x=1 sat ⇒ Falsified.
  let s1 ← Z3Session.create
  s1.runCommand (.declareConst (.NormalSymbol "x") intSort)
  let x : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "x"))
  s1.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "not")) #[.AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[x,x]])
  let r1 ← s1.checkSatCancel none #[] false
  let s2 ← Z3Session.create
  s2.runCommand (.declareConst (.NormalSymbol "x") intSort)
  s2.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[x, .NumTerm 1])
  let r2 ← s2.checkSatCancel none #[] false
  let showR := fun r => match r with | Result.Valid => "valid" | Result.Falsified _ => "falsified" | Result.Undetermined => "undet"
  IO.println s!"cancel-path r1={showR r1} r2={showR r2}"

open Blaster.Smt in
/-- info: cancel-live r=falsified cex=x: 1 ec=0 -/
#guard_msgs in
#eval do
  -- A token that is present but not set starts a polling task. The check and model
  -- extraction stay on the caller's thread; the task only calls the cross-thread-safe
  -- interrupt API if the token is set. Check for silent Z3 errors as well.
  let s ← Z3Session.create
  s.runCommand (.declareConst (.NormalSymbol "x") intSort)
  let x : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "x"))
  s.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[x, .NumTerm 1])
  let tk ← IO.CancelToken.new
  let topVars : Array (List TopLevelVar) := #[[⟨.NormalSymbol "x", `x, Lean.mkConst ``Int, ⟨`x⟩⟩]]
  let r ← s.checkSatCancel (some tk) topVars true
  let ec ← s.ctx.errorCode
  let showR := fun r => match r with | Result.Valid => "valid" | Result.Falsified _ => "falsified" | Result.Undetermined => "undet"
  let cex := match r with | Result.Falsified c => c.messages | _ => []
  IO.println s!"cancel-live r={showR r} cex={String.intercalate ", " cex} ec={ec}"

open Blaster.Smt in
/-- info: assume-cancel r1=valid r2=falsified -/
#guard_msgs in
#eval do
  -- checkAssumingCancel with a live polling task (token present, not set) exercises
  -- assumption AST construction and the direct check on the caller's thread.
  -- Mirrors the "assume" test: r1 flag ⇒ ¬(x=x) unsat ⇒ Valid; r2 flag ⇒ x=1 sat ⇒ Falsified.
  let ecChk := fun (sess : Z3Session) (label : String) => do
    let ec ← sess.ctx.errorCode
    if ec != 0 then throw (IO.userError s!"{label}: z3 error {ec} ({← sess.ctx.errorMsg ec})")
  let s1 ← Z3Session.create        -- IO action first, so the do-block monad is IO
  let tk ← IO.CancelToken.new
  s1.runCommand (.declareConst (.NormalSymbol "flag") boolSort)
  s1.runCommand (.declareConst (.NormalSymbol "x") intSort)
  let flag : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "flag"))
  let x : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "x"))
  s1.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "=>")) #[flag,
    .AppTerm (.SimpleIdent (.ReservedSymbol "not")) #[.AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[x, x]]])
  let r1 ← s1.checkAssumingCancel #[flag] (some tk) #[] false
  ecChk s1 "r1"
  let s2 ← Z3Session.create
  s2.runCommand (.declareConst (.NormalSymbol "flag") boolSort)
  s2.runCommand (.declareConst (.NormalSymbol "x") intSort)
  s2.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "=>")) #[flag,
    .AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[x, .NumTerm 1]])
  let r2 ← s2.checkAssumingCancel #[flag] (some tk) #[] false
  ecChk s2 "r2"
  let showR := fun r => match r with | Result.Valid => "valid" | Result.Falsified _ => "falsified" | Result.Undetermined => "undet"
  IO.println s!"assume-cancel r1={showR r1} r2={showR r2}"

open Blaster.Smt in
/-- info: pre-cancel-path-ran -/
#guard_msgs in
#eval do
  -- A pre-set token returns unknown before the check begins, without touching the
  -- Z3 context from another thread.
  let s ← Z3Session.create
  s.runCommand (.declareConst (.NormalSymbol "x") intSort)
  s.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[.SmtIdent (.SimpleIdent (.NormalSymbol "x")), .NumTerm 1])
  let tk ← IO.CancelToken.new
  tk.set
  let _ ← s.checkSatCancel (some tk) #[] false
  IO.println "pre-cancel-path-ran"

open Blaster.Smt in
/-- info: sticky-probe pre=falsified post-interrupt=falsified -/
#guard_msgs in
#eval do
  -- Deterministic probe of whether `Z3_solver_interrupt` leaves the solver in a sticky
  -- cancelled state (no task race here: interrupt + check are both synchronous). `x=1` is
  -- sat, so `pre` is Falsified. Then a DIRECT `solver.interrupt` (no check in flight),
  -- then a fresh check on the SAME solver. OBSERVED on this Z3 (4.x): `post` is Falsified —
  -- i.e. the interrupt flag is NOT sticky; a stray interrupt does not poison later checks.
  -- Independently, the Env-level `throwInterruptException` aborts elaboration on a real
  -- cancel, so the interrupted (Undetermined) verdict is never consumed as a result anyway.
  let s ← Z3Session.create
  s.runCommand (.declareConst (.NormalSymbol "x") intSort)
  s.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[.SmtIdent (.SimpleIdent (.NormalSymbol "x")), .NumTerm 1])
  let pre ← s.checkSatCancel none #[] false
  s.solver.interrupt
  let post ← s.checkSatCancel none #[] false
  let showR := fun r => match r with | Result.Valid => "valid" | Result.Falsified _ => "falsified" | Result.Undetermined => "undet"
  IO.println s!"sticky-probe pre={showR pre} post-interrupt={showR post}"

open Blaster.Smt in
/-- info: dtrec r1=valid r2=falsified -/
#guard_msgs in
#eval do
  -- SINGLE RECURSIVE datatype `IntTree ::= leaf(val:Int) | node(l:IntTree, r:IntTree)`.
  -- The `l`/`r` fields are self-references (`.SymbolSort itName`, the SAME symbol
  -- passed to declareDataType), so the sort_ref path must fire; otherwise Z3 would
  -- get a Bool placeholder as the field sort and the round-trips below would break.
  let itName : SmtSymbol := .NormalSymbol "IntTree"
  let itSort : SortExpr := .SymbolSort itName
  -- `tip` is a NULLARY ctor (`none` fields) — exercises the `[ctor, recog]` (no
  -- accessor) slice of the flat layout, the most common recursive-datatype shape.
  let itDecl : SmtDatatypeDecl := { params := none, ctors := #[
    (.NormalSymbol "leaf", some #[(.NormalSymbol "val", intSort)]),
    (.NormalSymbol "node", some #[(.NormalSymbol "l", itSort), (.NormalSymbol "r", itSort)]),
    (.NormalSymbol "tip", none) ] }
  let app := fun (nm : SmtSymbol) (args : Array SmtTerm) => SmtTerm.AppTerm (.SimpleIdent nm) args
  let notOp := fun t => app (.ReservedSymbol "not") #[t]
  let leaf1 := app (.NormalSymbol "leaf") #[.NumTerm 1]
  let leaf2 := app (.NormalSymbol "leaf") #[.NumTerm 2]
  let tree  := app (.NormalSymbol "node") #[leaf1, leaf2]
  let tipT  := app (.NormalSymbol "tip") #[]
  let showR := fun r => match r with | Result.Valid => "valid" | Result.Falsified _ => "falsified" | Result.Undetermined => "undet"
  -- r1: accessor round-trip THROUGH the recursive field + recognizers, all valid ⇒ ¬ ⇒ Valid.
  --     (l tree) = leaf1  AND  (val (l tree)) = 1  AND  (is-node tree)  AND
  --     (is-tip tip)  AND  ¬(is-tip tree)
  let s1 ← Z3Session.create
  s1.runCommand (.declareDataType itName itDecl)
  let ec1 ← s1.ctx.errorCode
  if ec1 != 0 then throw (IO.userError s!"dtrec declare: z3 error {ec1} ({← s1.ctx.errorMsg ec1})")
  let goal1 : SmtTerm := app (.ReservedSymbol "and") #[
    app (.ReservedSymbol "=") #[app (.NormalSymbol "l") #[tree], leaf1],
    app (.ReservedSymbol "=") #[app (.NormalSymbol "val") #[app (.NormalSymbol "l") #[tree]], .NumTerm 1],
    app (.NormalSymbol "is-node") #[tree],
    app (.NormalSymbol "is-tip") #[tipT],
    notOp (app (.NormalSymbol "is-tip") #[tree])]
  s1.assert (notOp goal1)
  let r1 ← s1.checkSat #[] false
  -- r2: (val (l tree)) = 2 is FALSE (it is 1) ⇒ ¬ is sat ⇒ Falsified.
  let s2 ← Z3Session.create
  s2.runCommand (.declareDataType itName itDecl)
  let goal2 : SmtTerm := app (.ReservedSymbol "=") #[app (.NormalSymbol "val") #[app (.NormalSymbol "l") #[tree]], .NumTerm 2]
  s2.assert (notOp goal2)
  let r2 ← s2.checkSat #[] false
  IO.println s!"dtrec r1={showR r1} r2={showR r2}"

open Blaster.Smt in
/-- info: dtmut r1=valid r2=falsified -/
#guard_msgs in
#eval do
  -- MUTUAL datatypes `A ::= mkA(Int) | wrapB(theB:B)` and `B ::= mkB(Int) | wrapA(theA:A)`.
  -- wrapB's field references B (group index 1 ⇒ ref 2) and wrapA's references A
  -- (index 0 ⇒ ref 1). Field-sort symbols are the SAME values as the sort names.
  let aName : SmtSymbol := .NormalSymbol "A"
  let bName : SmtSymbol := .NormalSymbol "B"
  let declA : SmtDatatypeDecl := { params := none, ctors := #[
    (.NormalSymbol "mkA", some #[(.NormalSymbol "getA", intSort)]),
    (.NormalSymbol "wrapB", some #[(.NormalSymbol "theB", .SymbolSort bName)]) ] }
  let declB : SmtDatatypeDecl := { params := none, ctors := #[
    (.NormalSymbol "mkB", some #[(.NormalSymbol "getB", intSort)]),
    (.NormalSymbol "wrapA", some #[(.NormalSymbol "theA", .SymbolSort aName)]) ] }
  let nms  : Array SmtSortDecl := #[{name := aName, arity := 0}, {name := bName, arity := 0}]
  let app := fun (nm : SmtSymbol) (args : Array SmtTerm) => SmtTerm.AppTerm (.SimpleIdent nm) args
  let notOp := fun t => app (.ReservedSymbol "not") #[t]
  let mkB7  := app (.NormalSymbol "mkB") #[.NumTerm 7]        -- : B
  let wrap  := app (.NormalSymbol "wrapB") #[mkB7]            -- : A, holds a B recursively
  let showR := fun r => match r with | Result.Valid => "valid" | Result.Falsified _ => "falsified" | Result.Undetermined => "undet"
  -- r1: (theB wrap) = (mkB 7)  AND  (getB (theB wrap)) = 7  AND  (is-wrapB wrap)  ⇒ valid ⇒ ¬ ⇒ Valid.
  let s1 ← Z3Session.create
  s1.runCommand (.declareMutualDataTypes nms #[declA, declB])
  let ec1 ← s1.ctx.errorCode
  if ec1 != 0 then throw (IO.userError s!"dtmut declare: z3 error {ec1} ({← s1.ctx.errorMsg ec1})")
  let goal1 : SmtTerm := app (.ReservedSymbol "and") #[
    app (.ReservedSymbol "=") #[app (.NormalSymbol "theB") #[wrap], mkB7],
    app (.ReservedSymbol "=") #[app (.NormalSymbol "getB") #[app (.NormalSymbol "theB") #[wrap]], .NumTerm 7],
    app (.NormalSymbol "is-wrapB") #[wrap]]
  s1.assert (notOp goal1)
  let r1 ← s1.checkSat #[] false
  -- r2: (getB (theB wrap)) = 8 is FALSE (it is 7) ⇒ ¬ is sat ⇒ Falsified.
  let s2 ← Z3Session.create
  s2.runCommand (.declareMutualDataTypes nms #[declA, declB])
  let goal2 : SmtTerm := app (.ReservedSymbol "=") #[app (.NormalSymbol "getB") #[app (.NormalSymbol "theB") #[wrap]], .NumTerm 8]
  s2.assert (notOp goal2)
  let r2 ← s2.checkSat #[] false
  IO.println s!"dtmut r1={showR r1} r2={showR r2}"

open Blaster.Smt in
/-- info: dtparam r1=valid r2=falsified r3=valid -/
#guard_msgs in
#eval do
  -- PARAMETRIC (self-recursive) datatype, declared via `Z3_mk_polymorphic_datatype`:
  --   @List α = List.nil | List.cons (List.cons.0 : α) (List.cons.1 : @List α)
  -- `List.cons.1`'s field is the datatype at its OWN param ⇒ the self-recursive
  -- sort_ref path (NULL sort + ref 0) must fire, exactly as the non-parametric
  -- recursive path does. Terms are built the way the translator emits them:
  -- constructors QUALIFIED with the instantiated sort (`(as List.nil (@List Int))`,
  -- `(List.cons … : (@List Int))`), accessors/recognizers as bare SimpleIdents whose
  -- instantiated func_decl is recovered from the argument's own sort.
  let aSym   : SmtSymbol := .NormalSymbol "@α"
  let listNm : SmtSymbol := .NormalSymbol "@List"
  let listDecl : SmtDatatypeDecl := {
    params := some #[aSym],
    ctors := #[
      (.NormalSymbol "List.nil", none),
      (.NormalSymbol "List.cons", some #[
        (.NormalSymbol "List.cons.0", .SymbolSort aSym),
        (.NormalSymbol "List.cons.1", .ParamSort listNm #[.SymbolSort aSym]) ]) ] }
  let listInt : SortExpr := .ParamSort listNm #[intSort]
  let app := fun (nm : SmtSymbol) (args : Array SmtTerm) => SmtTerm.AppTerm (.SimpleIdent nm) args
  let notOp := fun t => app (.ReservedSymbol "not") #[t]
  -- nullary ctor via `(as List.nil (@List Int))`; applied ctor via qualified `List.cons`
  let nilI : SmtTerm := .SmtIdent (.QualifiedIdent (.NormalSymbol "List.nil") listInt)
  let consI := fun (h t : SmtTerm) =>
    SmtTerm.AppTerm (.QualifiedIdent (.NormalSymbol "List.cons") listInt) #[h, t]
  let l3 := consI (.NumTerm 3) nilI
  let showR := fun r => match r with
    | Result.Valid => "valid" | Result.Falsified _ => "falsified" | Result.Undetermined => "undet"
  -- r1 (Valid): accessor round-trip (incl. the recursive `List.cons.1` field) + BOTH
  -- recognizers, all concrete ⇒ ¬ unsat ⇒ Valid.
  let s1 ← Z3Session.create
  s1.runCommand (.declareDataType listNm listDecl)
  let ec1 ← s1.ctx.errorCode
  if ec1 != 0 then throw (IO.userError s!"dtparam declare: z3 error {ec1} ({← s1.ctx.errorMsg ec1})")
  let goal1 : SmtTerm := app (.ReservedSymbol "and") #[
    app (.ReservedSymbol "=") #[app (.NormalSymbol "List.cons.0") #[l3], .NumTerm 3],
    app (.ReservedSymbol "=") #[app (.NormalSymbol "List.cons.1") #[l3], nilI],
    app (.NormalSymbol "is-List.cons") #[l3],
    app (.NormalSymbol "is-List.nil") #[nilI],
    notOp (app (.NormalSymbol "is-List.nil") #[l3]) ]
  s1.assert (notOp goal1)
  let r1 ← s1.checkSat #[] false
  -- r2 (Falsified): (List.cons.0 l3) = 4 is FALSE (it is 3) ⇒ ¬ sat ⇒ Falsified.
  let s2 ← Z3Session.create
  s2.runCommand (.declareDataType listNm listDecl)
  let goal2 : SmtTerm := app (.ReservedSymbol "=") #[app (.NormalSymbol "List.cons.0") #[l3], .NumTerm 4]
  s2.assert (notOp goal2)
  let r2 ← s2.checkSat #[] false
  -- r3 (Valid): (cons 3 nil) ≠ nil (constructor distinctness) ⇒ ¬ unsat ⇒ Valid.
  let s3 ← Z3Session.create
  s3.runCommand (.declareDataType listNm listDecl)
  let goal3 : SmtTerm := notOp (app (.ReservedSymbol "=") #[l3, nilI])
  s3.assert (notOp goal3)
  let r3 ← s3.checkSat #[] false
  IO.println s!"dtparam r1={showR r1} r2={showR r2} r3={showR r3}"

open Blaster.Smt in
/-- info: either r1=valid r2=falsified -/
#guard_msgs in
#eval do
  -- TWO-PARAM (non-recursive) parametric datatype, to pin type-param ORDERING (a
  -- single-param test cannot distinguish correct ordering from a `tvMap` that works
  -- only because it has one entry):
  --   @Either α β = Either.Left (Either.Left.0 : α) | Either.Right (Either.Right.0 : β)
  -- Instantiated at `(@Either Int Bool)`, `Either.Left.0` MUST monomorphize to Int
  -- (param 0) and `Either.Right.0` to Bool (param 1); a swapped map would make the
  -- concrete goal below an `Int = Bool` sort error rather than Valid.
  let aSym : SmtSymbol := .NormalSymbol "@α"
  let bSym : SmtSymbol := .NormalSymbol "@β"
  let eNm  : SmtSymbol := .NormalSymbol "@Either"
  let eitherDecl : SmtDatatypeDecl := {
    params := some #[aSym, bSym],
    ctors := #[
      (.NormalSymbol "Either.Left",  some #[(.NormalSymbol "Either.Left.0",  .SymbolSort aSym)]),
      (.NormalSymbol "Either.Right", some #[(.NormalSymbol "Either.Right.0", .SymbolSort bSym)]) ] }
  let eIB : SortExpr := .ParamSort eNm #[intSort, boolSort]
  let app := fun (nm : SmtSymbol) (args : Array SmtTerm) => SmtTerm.AppTerm (.SimpleIdent nm) args
  let notOp := fun t => app (.ReservedSymbol "not") #[t]
  let left3  : SmtTerm := .AppTerm (.QualifiedIdent (.NormalSymbol "Either.Left")  eIB) #[.NumTerm 3]
  let rightT : SmtTerm := .AppTerm (.QualifiedIdent (.NormalSymbol "Either.Right") eIB) #[.BoolTerm true]
  let showR := fun r => match r with
    | Result.Valid => "valid" | Result.Falsified _ => "falsified" | Result.Undetermined => "undet"
  -- r1 (Valid): Left.0 : Int (param 0) AND Right.0 : Bool (param 1) + recognizers.
  let s1 ← Z3Session.create
  s1.runCommand (.declareDataType eNm eitherDecl)
  let ec ← s1.ctx.errorCode
  if ec != 0 then throw (IO.userError s!"either declare: z3 error {ec} ({← s1.ctx.errorMsg ec})")
  let goal1 : SmtTerm := app (.ReservedSymbol "and") #[
    app (.ReservedSymbol "=") #[app (.NormalSymbol "Either.Left.0")  #[left3],  .NumTerm 3],
    app (.ReservedSymbol "=") #[app (.NormalSymbol "Either.Right.0") #[rightT], .BoolTerm true],
    app (.NormalSymbol "is-Either.Left")  #[left3],
    app (.NormalSymbol "is-Either.Right") #[rightT],
    notOp (app (.NormalSymbol "is-Either.Left") #[rightT]) ]
  s1.assert (notOp goal1)
  let r1 ← s1.checkSat #[] false
  -- r2 (Falsified): (Either.Left.0 (Left 3)) = 4 is FALSE (it is 3) ⇒ ¬ sat ⇒ Falsified.
  let s2 ← Z3Session.create
  s2.runCommand (.declareDataType eNm eitherDecl)
  let goal2 : SmtTerm := app (.ReservedSymbol "=") #[app (.NormalSymbol "Either.Left.0") #[left3], .NumTerm 4]
  s2.assert (notOp goal2)
  let r2 ← s2.checkSat #[] false
  IO.println s!"either r1={showR r1} r2={showR r2}"
