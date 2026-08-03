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
  let topVars : Array (List (SmtSymbol × Lean.Name)) := #[[(.NormalSymbol "x", `x)]]
  let r2 ← s2.checkSat topVars true
  let showR := fun r => match r with | Result.Valid => "valid" | Result.Falsified _ => "falsified" | Result.Undetermined => "undet"
  let cex := match r2 with | Result.Falsified c => c | _ => []
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
