import Lean

/-!
# Invariant search by candidate elimination (Houdini)

Every relation of a Horn query gets candidate conjuncts over its arguments,
built from what the arguments observe (`Kind`), never from the program's
function names. Each clause is checked with z3 under the current candidates:
the head candidates that a model of the clause's premises falsifies are
dropped, and the clauses whose premises use that relation are checked again,
until nothing changes. If the goal clauses then hold, the candidates they
depend on (through unsat cores) are returned.

The result is only a proposal: the caller proves every obligation it implies,
so a wrong answer of this search, or of z3 here, cannot make a proof succeed.

Houdini's own SMT symbols start with `p` (`p3` is argument 3 of a clause's
head, `pr2` the invariant of relation 2, …): the query must not use such
symbols.
-/
namespace Blaster.Proof.Explore.Houdini
open Lean

/-! ## Queries -/

/-- The sort of a relation argument. -/
inductive ArgSort where
  | int | bool | data
  deriving BEq, Hashable, Inhabited

/-- How an observation varies during a run. -/
inductive Role where
  /-- The observation reads only roots: it is fixed for the whole run. -/
  | root
  /-- The observation is fixed for a procedure call. -/
  | ghost
  /-- The observation varies. -/
  | var
  deriving BEq, Hashable, Inhabited

/-- What a relation argument observes. -/
structure Kind where
  sort : ArgSort
  /-- The observer's head function (its last name component): `var` for a
  program value itself, `decide` for a comparison with a root. -/
  head : String
  role : Role
  /-- The variables the observation reads. -/
  ids : Array Name
  deriving BEq, Hashable, Inhabited

/-- An unknown relation of the query: what its arguments are. -/
structure Relation where
  /-- The SMT sorts of the arguments. -/
  sorts : Array String
  /-- What each argument observes. -/
  kinds : Array Kind
  /-- The number of leading arguments that are a procedure's entry
  observations: fixed per call, like ghosts. -/
  entry : Nat := 0
  deriving Inhabited

/-- An application of the relation `rel`, an index into `Query.relations`. -/
structure App where
  rel : Nat
  args : Array String
  deriving Inhabited

/-- The conclusion of a clause. -/
inductive Head where
  | app (a : App)
  /-- A goal clause: the head is a formula. -/
  | goal (formula : String)
  deriving Inhabited

/-- `∀ vars, premises ∧ facts → head`. -/
structure Clause where
  vars : Array (String × String)
  premises : Array App
  facts : Array String
  head : Head
  deriving Inhabited

/-- A Horn query: relations, and clauses over them. -/
structure Query where
  /-- Declarations of the sorts, datatypes and functions the clauses use. -/
  preamble : String
  relations : Array Relation
  clauses : Array Clause

/-! ## Candidates

A candidate is SMT text over the placeholders `p0`, `p1`, … for the arguments
of its relation. -/

/-- The tokens of an s-expression: parentheses and atoms. -/
private def tokens (s : String) : Array String := Id.run do
  let mut out := #[]
  let mut it := s.iter
  while !it.atEnd do
    let c := it.curr
    if c == '(' || c == ')' then
      out := out.push c.toString
      it := it.next
    else if c.isWhitespace then it := it.next
    else
      let start := it.pos
      while !it.atEnd && !(it.curr == '(' || it.curr == ')' || it.curr.isWhitespace) do it := it.next
      out := out.push (s.extract start it.pos)
  return out

/-- Tokens as text: `(op a b)`. -/
private def render (ts : Array String) : String := Id.run do
  let mut out := ""
  let mut space := false
  for t in ts do
    if t != ")" && space then out := out.push ' '
    out := out ++ t
    space := t != "("
  return out

/-- The argument position of a placeholder token `pI`. -/
private def placeholder? (t : String) : Option Nat :=
  if t.startsWith "p" then (t.drop 1).toNat? else none

/-- `c` with each placeholder `pI` replaced by `f I`. -/
private def instantiate (c : String) (f : Nat → String) : String :=
  render ((tokens c).map fun t => (placeholder? t).elim t f)

private def mentions (c : String) (ps : Array Nat) : Bool :=
  (tokens c).any fun t => (placeholder? t).any ps.contains

/-- Facts about the whole query that candidates refer to. -/
private structure Context where
  /-- The root variables themselves. -/
  roots : Std.HashSet Name
  /-- The goal's keys: the compared roots that every root quantity reading a
  compared root reads (the currency and token of an observed asset, say). -/
  keys : Array Name

/-- The root that a comparison of a program value with a root compares with. -/
private def comparedRoot (cx : Context) (k : Kind) : Option Name :=
  if k.head == "decide" && k.ids.size == 2 && cx.roots.contains k.ids[1]! then some k.ids[1]!
  else none

private def context (q : Query) : Context := Id.run do
  let kinds := q.relations.flatMap (·.kinds)
  let roots := kinds.foldl (init := {}) fun acc k =>
    if k.role == .root && k.ids.size == 1 then acc.insert k.ids[0]! else acc
  let cx : Context := {roots, keys := #[]}
  let compared := kinds.foldl (init := ({} : Std.HashSet Name)) fun acc k =>
    match comparedRoot cx k with
    | some r => acc.insert r
    | none => acc
  -- the compared roots each keyed root quantity reads
  let keyed := kinds.filterMap fun k =>
    if k.sort == .int && k.head != "var" && k.role == .root then
      let read := k.ids.filter compared.contains
      if read.isEmpty then none else some read
    else none
  let keys := match keyed[0]? with
    | some first => first.filter fun r => keyed.all (·.contains r)
    | none => #[]
  return {cx with keys}

/-- The candidates of one relation (see each rule's comment), with the
placeholders of the original argument positions. -/
private def candidates (cx : Context) (rel : Relation) : Array String := Id.run do
  let n := rel.sorts.size
  let kind := fun (i : Nat) =>
    let k := rel.kinds[i]?.getD {sort := .data, head := "?", role := .var, ids := #[]}
    if i < rel.entry then {k with role := .ghost} else k
  let sort := fun (i : Nat) => rel.sorts[i]!
  let head := fun (i : Nat) => (kind i).head
  let fixed := fun (i : Nat) => (kind i).role != .var
  let raw := fun (i : Nat) => head i == "var"
  let all := (List.range n).toArray
  let ints := all.filter (sort · == "Int")
  let bools := all.filter (sort · == "Bool")
  let pairs := fun (xs : Array Nat) => Id.run do
    let mut out := #[]
    for a in [0:xs.size] do
      for b in [a + 1:xs.size] do out := out.push (xs[a]!, xs[b]!)
    return out
  let mut cands : Array String := #[]
  for i in bools do cands := cands.push s!"p{i}" |>.push s!"(not p{i})"
  for i in ints do cands := cands.push s!"(>= p{i} 0)" |>.push s!"(= p{i} 0)"
  -- quantities: the program's own integers and the integer observations read
  -- at the goal's keys, one per observed kind
  let mut qty := #[]
  let mut seen : Std.HashSet Kind := {}
  for i in ints do
    if raw i && fixed i || !raw i && !cx.keys.all (kind i).ids.contains then continue
    unless seen.contains (kind i) do
      seen := seen.insert (kind i)
      qty := qty.push i
  let totals := qty.filter fixed
  let parts := qty.filter (!fixed ·)
  for (i, j) in pairs qty do
    cands := cands.push s!"(= p{i} p{j})"
    if head i == head j then cands := cands.push s!"(<= p{i} p{j})" |>.push s!"(<= p{j} p{i})"
  -- a total is the sum of two parts, or two totals are a part
  for r in totals do
    for a in [0:parts.size] do
      for b in [a:parts.size] do cands := cands.push s!"(= p{r} (+ p{parts[a]!} p{parts[b]!}))"
    for a in parts do
      for t in totals do
        if t != r then cands := cands.push s!"(= (+ p{r} p{t}) p{a})"
  let mut sums := #[]
  for (r, t) in pairs totals do
    for u in totals do
      if u != r && u != t then sums := sums.push s!"(<= (+ p{r} p{t}) p{u})" |>.push s!"(<= p{u} (+ p{r} p{t}))"
  cands := cands ++ sums
  -- a Boolean program value (a check's result so far) implies an inequality
  -- between totals, or another Boolean observation
  let checks := bools.filter fun i => raw i && !fixed i
  for b in checks do
    for k in [0:sums.size:2] do
      cands := cands.push s!"(or (not p{b}) {sums[k]!})" |>.push s!"(or p{b} {sums[k]!})"
    for x in bools do
      if x != b && !fixed x then
        cands := cands.push s!"(or (not p{b}) p{x})" |>.push s!"(or (not p{b}) (not p{x}))"
  -- a program value observed like a fixed value (same observer) equals or
  -- implies it; a check result implies a fixed Boolean observation
  for r in bools.filter fun i => fixed i && !raw i && head i != "decide" do
    for x in bools do
      if x != r && !fixed x && head x == head r then
        cands := cands.push s!"(= p{x} p{r})" |>.push s!"(or (not p{x}) p{r})"
    for b in checks do cands := cands.push s!"(or (not p{b}) p{r})"
  for b in checks do
    for x in bools do
      if x != b && !fixed x && !raw x then cands := cands.push s!"(= p{b} p{x})"
  for (i, j) in pairs all do
    if sort i == sort j && sort i != "Int" && sort i != "Bool" && head i == head j && !raw i &&
        fixed i != fixed j then
      cands := cands.push s!"(= p{i} p{j})"
  let observed := bools.filter fun i => !fixed i && !raw i && head i != "decide"
  for (x, y) in pairs observed do
    if head x == head y then cands := cands.push s!"(= p{x} p{y})"
  -- not both: a comparison with a root and a check of an element of a root
  let elements := bools.filter fun i => !raw i && head i != "decide" &&
    (kind i).ids.any cx.roots.contains && (kind i).ids.any (!cx.roots.contains ·)
  let elementRoots := elements.foldl (init := ({} : Std.HashSet Name)) fun acc i =>
    (kind i).ids.foldl (init := acc) fun acc x => if cx.roots.contains x then acc.insert x else acc
  for a in bools do
    if let some r := comparedRoot cx (kind a) then
      if elementRoots.contains r then
        for b in elements do cands := cands.push s!"(or (not p{a}) (not p{b}))"
  -- comparisons of program values with the keys guard what the program
  -- extracts from a collection it walks: at the observed keys its amounts are
  -- the observed quantities or an element's contribution, elsewhere the
  -- observed totals cancel
  let amounts := ints.filter fun i => raw i && !fixed i
  let mut comparisons : Array (Name × Array Nat) := #[]
  for i in bools do
    if let some r := comparedRoot cx (kind i) then
      if cx.keys.contains r then
        comparisons := match comparisons.findIdx? (·.1 == r) with
          | some k => comparisons.modify k fun (r, xs) => (r, xs.push i)
          | none => comparisons.push (r, #[i])
  unless amounts.isEmpty do
    let readings := cands.filter fun c =>
      c.startsWith "(= " && mentions c amounts && mentions c totals
    -- (what a walk reads at its cursor is keyed by some of the keys)
    let cursor := ints.filter fun i => !raw i && !fixed i && cx.keys.any (kind i).ids.contains
    let mut contributions := parts.map (s!"(= p{·} 0)")
    for a in amounts do
      for c in cursor do contributions := contributions.push s!"(= p{a} p{c})"
    for w in parts do
      for c in cursor do
        if w < c then contributions := contributions.push s!"(= p{w} p{c})"
    let byKey := comparisons.qsort (·.1.toString < ·.1.toString)
    for x in [0:byKey.size] do
      for y in [x + 1:byKey.size] do
        for a in byKey[x]!.2.extract 0 4 do
          for b in byKey[y]!.2.extract 0 4 do
            cands := cands ++ readings.map (s!"(or (not p{a}) (not p{b}) {·})")
            -- (two different program values compared with the keys)
            if (kind a).ids[0]! != (kind b).ids[0]! then
              cands := cands ++ contributions.map (s!"(or (not p{a}) (not p{b}) {·})")
    for (_, ds) in comparisons do
      for d in ds do
        for (r, t) in pairs totals do cands := cands.push s!"(or p{d} (= (+ p{r} p{t}) 0))"
  let datas := all.filter fun i => raw i && sort i != "Int" && sort i != "Bool"
  for (i, j) in pairs datas do
    if sort i == sort j then cands := cands.push s!"(= p{i} p{j})"
  return cands

/-- Observations often encode identically (record projections, wrapper
functions, duplicate root readings). Map each argument position to the first
position that agrees with it syntactically in every application. -/
private def aliases (q : Query) : Array (Array Nat) := Id.run do
  let mut reps := q.relations.map fun r => Array.replicate r.sorts.size 0
  let refine := fun (old : Array Nat) (args : Array String) => Id.run do
    let mut groups : Std.HashMap (Nat × String) Nat := {}
    let mut out := #[]
    for i in [0:old.size] do
      let key := (old[i]!, args[i]?.getD "")
      match groups[key]? with
      | some j => out := out.push j
      | none =>
        groups := groups.insert key i
        out := out.push i
    return out
  for cl in q.clauses do
    for a in cl.premises do reps := reps.modify a.rel (refine · a.args)
    if let .app a := cl.head then reps := reps.modify a.rel (refine · a.args)
  return reps

/-- `c` over the representative positions `rep`, with the arguments of a sum
or of an equality between two placeholders in order; `none` for `(= pI pI)`. -/
private def canonical (rep : Array Nat) (c : String) : Option String := Id.run do
  let mut ts := (tokens c).map fun t => match placeholder? t with
    | some i => s!"p{rep[i]!}"
    | none => t
  for k in [0:ts.size] do
    if k + 4 < ts.size && ts[k]! == "(" && (ts[k + 1]! == "+" || ts[k + 1]! == "=") &&
        ts[k + 4]! == ")" then
      if let (some i, some j) := (placeholder? ts[k + 2]!, placeholder? ts[k + 3]!) then
        if j < i then ts := (ts.set! (k + 2) s!"p{j}").set! (k + 3) s!"p{i}"
  if ts.size == 5 && ts[1]! == "=" && ts[2]! == ts[3]! && (placeholder? ts[2]!).isSome then
    return none
  return some (render ts)

/-- Candidates per relation, after aliasing and without duplicates. -/
private def initialCandidates (q : Query) : Array (Array String) :=
  let cx := context q
  let reps := aliases q
  -- (one task per relation)
  let tasks := q.relations.mapIdx fun r rel => Task.spawn fun _ => Id.run do
    let mut seen : Std.HashSet String := {}
    let mut out := #[]
    for c in candidates cx rel do
      if let some c := canonical reps[r]! c then
        unless seen.contains c do
          seen := seen.insert c
          out := out.push c
    return out
  tasks.map Task.get

/-! ## Solvers -/

private abbrev Z3 := IO.Process.Child ⟨.piped, .piped, .null⟩

private def spawnZ3 : IO Z3 :=
  -- a solver running out of memory answers `unknown` (its head's candidates
  -- are then dropped); without a bound one query can take the machine's memory
  IO.Process.spawn {
    cmd := "z3", args := #["-in", "-smt2", "-t:5000", "memory_max_size=1000"]
    stdin := .piped, stdout := .piped, stderr := .null }

/-- A z3 process, and when its pending answer is due (monotonic milliseconds;
0 when none is pending). -/
private structure Process where
  z3 : Z3
  due : Nat := 0

/-- z3 answers each `check-sat` within `-t` milliseconds; a process that does
not answer at all is killed by the watchdog and replaced. -/
private structure Solver where
  process : Std.Mutex Process
  /-- The clause and the key (see `check`) of the solver's assertions, when
  they can be reused. -/
  context : IO.Ref (Option (Nat × Array Nat))

private def Solver.new : IO Solver :=
  return {process := ← Std.Mutex.new {z3 := ← spawnZ3}, context := ← IO.mkRef none}

private def Solver.stop (s : Solver) : IO Unit :=
  s.process.atomically do
    let p ← get
    try p.z3.kill catch _ => pure ()
    try discard p.z3.wait catch _ => pure ()

/-- Send `cmds` and return the answer; `none` when z3 did not answer within
`limitMs` (its process is then replaced). -/
private def Solver.ask (s : Solver) (cmds : String) (limitMs : Nat := 30000) : IO (Option String) := do
  let due := (← IO.monoMsNow) + limitMs
  let z3 ← s.process.atomically (modifyGet fun p => (p.z3, {p with due}))
  let answer ← try
      z3.stdin.putStr (cmds ++ "\n(echo \"@@\")\n")
      z3.stdin.flush
      let mut out := ""
      repeat
        let line ← z3.stdout.getLine
        if line.isEmpty then throw (IO.userError "z3 exited")
        if line.trimRight == "@@" then break
        out := out ++ line
      pure (some out)
    catch _ => pure none
  -- (killing and replacing under the lock: the watchdog never kills a reaped process)
  s.process.atomically do
    if answer.isSome then modify ({· with due := 0})
    else
      let p ← get
      try p.z3.kill catch _ => pure ()
      try discard p.z3.wait catch _ => pure ()
      set ({z3 := ← spawnZ3} : Process)
  if answer.isNone then s.context.set none
  return answer

/-- Kill the z3 processes that are past their answer's due time, until `stop`. -/
private def watchdog (solvers : Array Solver) (stop : IO.Ref Bool) : IO Unit := do
  while !(← stop.get) do
    let now ← IO.monoMsNow
    for s in solvers do
      s.process.atomically do
        let p ← get
        if p.due != 0 && now > p.due then
          try p.z3.kill catch _ => pure ()
          set {p with due := 0}
    IO.sleep 100

/-- The truth values of a `get-value` answer `((ph0 true) (ph1 false) …)`, in order. -/
private def truthValues (answer : String) : Array Bool := Id.run do
  let mut out := #[]
  let mut it := answer.iter
  while !it.atEnd do
    let c := it.curr
    if c == '(' || c == ')' || c.isWhitespace then
      it := it.next
      continue
    let start := it.pos
    while !it.atEnd && !(it.curr == '(' || it.curr == ')' || it.curr.isWhitespace) do it := it.next
    let size := it.pos.byteIdx - start.byteIdx
    if size == 4 && answer.substrEq start "true" 0 4 then out := out.push true
    else if size == 5 && answer.substrEq start "false" 0 5 then out := out.push false
  return out

/-- `f` on each element of `xs`, with the solvers in parallel. -/
private def parallel (solvers : Array Solver) (xs : Array α) (f : Solver → α → IO β) :
    IO (Array β) := do
  let next ← IO.mkRef 0
  let tasks ← solvers.mapM fun s => IO.asTask (prio := .dedicated) do
    let mut out := #[]
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      let some x := xs[i]? | break
      out := out.push (i, ← f s x)
    return out
  -- (every task ends before an error is raised: none may outlive the solvers)
  let mut results : Array (Option β) := Array.replicate xs.size none
  for r in ← tasks.mapM fun t => IO.wait t do
    for (i, y) in ← IO.ofExcept r do results := results.set! i (some y)
  return results.filterMap id

/-! ## Checking a clause -/

/-- The invariant of relation `r` with the conjuncts `cs`. -/
private def define (q : Query) (r : Nat) (cs : Array String) : String :=
  let sorts := q.relations[r]!.sorts
  let params := " ".intercalate ((List.range sorts.size).map fun i => s!"(p{i} {sorts[i]!})")
  s!"(define-fun pr{r} ({params}) Bool (and true {" ".intercalate cs.toList}))"

private def apply (a : App) : String :=
  if a.args.isEmpty then s!"pr{a.rel}" else s!"(pr{a.rel} {" ".intercalate a.args.toList})"

private def header : String :=
  "(reset)(set-option :print-success false)(set-option :model.completion true)\n"

/-- Bind the arguments of the head `h` to the constants `p0`, `p1`, …, so that
its candidates can be stated verbatim. -/
private def bindHead (q : Query) (h : App) : String := Id.run do
  let sorts := q.relations[h.rel]!.sorts
  let mut out := ""
  for i in [0:h.args.size] do
    out := out ++ s!"(declare-const p{i} {sorts[i]!})(assert (= p{i} {h.args[i]!}))"
  return out

/-- Assert the premises of `cl` under the invariants `premise r`, and name the
head candidates `heads` `ph0`, `ph1`, … -/
private def contextCommands (q : Query) (cl : Clause) (premise : Nat → Array String)
    (heads : Array String) : String := Id.run do
  let mut out := header ++ q.preamble ++ "\n"
  let mut defined : Std.HashSet Nat := {}
  for a in cl.premises do
    unless defined.contains a.rel do
      defined := defined.insert a.rel
      out := out ++ define q a.rel (premise a.rel) ++ "\n"
  for (v, s) in cl.vars do out := out ++ s!"(declare-const {v} {s})"
  out := out ++ s!"(assert (and true {" ".intercalate (cl.premises.map apply ++ cl.facts).toList}))\n"
  if let .app h := cl.head then
    out := out ++ bindHead q h
    for k in [0:heads.size] do out := out ++ s!"(define-fun ph{k} () Bool {heads[k]!})"
  return out

private inductive Outcome where
  | holds
  /-- The indices of checked head candidates that a model of the premises falsifies. -/
  | falsified (ks : Array Nat)
  | unknown

/-- Check clause `ci` under the premise invariants `premise`; for a non-goal
clause, check its head candidates `heads` at the positions `alive`. The solver
keeps the clause's assertions for the next check with the same `key` (the
versions of the invariants they state); `none` for assertions not to reuse. -/
private def check (q : Query) (s : Solver) (ci : Nat) (key : Option (Array Nat))
    (premise : Nat → Array String) (heads : Array String) (alive : Array Nat) : IO Outcome := do
  let cl := q.clauses[ci]!
  if cl.head matches .app _ && alive.isEmpty then return .holds
  let names := " ".intercalate (alive.toList.map (s!"ph{·}"))
  let negated := match cl.head with
    | .goal f => f
    | .app _ => s!"(and true {names})"
  let reuse := key.isSome && (← s.context.get) == key.map (ci, ·)
  s.context.set none
  let cmds := if reuse then "" else contextCommands q cl premise heads
  let some answer ← s.ask (cmds ++ s!"(push 1)(assert (not {negated}))(check-sat)") | return .unknown
  let outcome ← if answer.trim == "unsat" then pure .holds
    else if answer.trim != "sat" then pure .unknown
    else if cl.head matches .goal _ then pure (.falsified #[])
    else match ← s.ask s!"(get-value ({names}))" with
      | none => pure .unknown
      | some values =>
        let values := truthValues values
        let dead := (alive.zip values).filterMap fun (k, v) => if v then none else some k
        -- (a model of the negation falsifies some candidate)
        pure (if values.size != alive.size || dead.isEmpty then .unknown else .falsified dead)
  -- (an unknown answer leaves the scope pushed above open)
  if outcome matches .unknown then return outcome
  let some _ ← s.ask "(pop 1)" | return .unknown
  s.context.set (key.map (ci, ·))
  return outcome

/-! ## The fixpoint -/

private structure Work where
  /-- The clauses to check, in order. -/
  queue : Array Nat
  queued : Array Bool
  /-- The relations whose clauses are being checked: a clause waits while
  another clause with its head relation is checked, which would repeat its
  eliminations. -/
  busy : Array Bool
  /-- The number of clauses being checked. -/
  active : Nat := 0

private inductive Job where
  | clause (ci : Nat)
  | wait
  | done

private structure Shared where
  /-- The version and the candidates of each relation. -/
  rels : IO.Ref (Array (Nat × Array String))
  work : IO.Ref Work
  /-- The non-goal clauses whose premises use each relation. -/
  users : Array (Array Nat)
  /-- The deadline, in monotonic milliseconds. -/
  due : Nat
  checks : IO.Ref Nat
  /-- The checks without an answer: each drops its head's candidates. -/
  unknowns : IO.Ref Nat

/-- The head relation of a non-goal clause (only those are checked in the fixpoint). -/
private def headRel (q : Query) (ci : Nat) : Nat :=
  match q.clauses[ci]!.head with
  | .app h => h.rel
  | .goal _ => 0

private def Shared.take (sh : Shared) (q : Query) : IO Job :=
  sh.work.modifyGet fun w =>
    match w.queue.findIdx? (!w.busy[headRel q ·]!) with
    | some k =>
      let ci := w.queue[k]!
      let w := {w with queue := w.queue.eraseIdx! k, queued := w.queued.set! ci false}
      (.clause ci, {w with busy := w.busy.set! (headRel q ci) true, active := w.active + 1})
    | none => if w.queue.isEmpty && w.active == 0 then (.done, w) else (.wait, w)

private def Shared.enqueue (sh : Shared) (cs : Array Nat) : IO Unit :=
  sh.work.modify fun w => cs.foldl (init := w) fun w c =>
    if w.queued[c]! then w else {w with queue := w.queue.push c, queued := w.queued.set! c true}

/-- Drop the candidates `dead` of relation `r`; its users are checked again. -/
private def Shared.remove (sh : Shared) (r : Nat) (dead : Array String) : IO Unit := do
  if dead.isEmpty then return
  let dead := Std.HashSet.ofArray dead
  let changed ← sh.rels.modifyGet fun rels =>
    let (v, cs) := rels[r]!
    let kept := cs.filter (!dead.contains ·)
    if kept.size == cs.size then (false, rels) else (true, rels.set! r (v + 1, kept))
  if changed then sh.enqueue sh.users[r]!

/-- Drop the head candidates of clause `ci` that its premises falsify. -/
private def processClause (q : Query) (sh : Shared) (s : Solver) (ci : Nat) : IO Unit := do
  let cl := q.clauses[ci]!
  let .app h := cl.head | return
  let rels ← sh.rels.get
  let heads := rels[h.rel]!.2
  -- the clause's assertions state its premises' invariants and its head candidates
  let key := (cl.premises.map (rels[·.rel]!.1)).push rels[h.rel]!.1
  -- with the head relation among the premises, the premise shrinks with the
  -- head: new assertions for every check
  let selfLoop := cl.premises.any (·.rel == h.rel)
  let mut alive := (List.range heads.size).toArray
  -- whether the clause holds for `alive` (otherwise it is checked again later)
  let mut settled := false
  let mut retried := false
  for _ in [0:30] do
    if alive.isEmpty then
      settled := true
      break
    if (← IO.monoMsNow) > sh.due then return
    sh.checks.modify (· + 1)
    let outcome ← if selfLoop then
        let current := alive.map (heads[·]!)
        let outcome ← check q s ci none (fun r => if r == h.rel then current else rels[r]!.2)
          current (List.range current.size).toArray
        pure <| match outcome with
          | .falsified ks => .falsified (ks.map (alive[·]!))
          | o => o
      else check q s ci (some key) (rels[·]!.2) heads alive
    match outcome with
    | .holds =>
      settled := true
      break
    | .unknown =>
      sh.unknowns.modify (· + 1)
      -- (z3 may have run out of time under load: one more check, then the
      -- head's candidates are dropped)
      if retried then
        alive := #[]
        settled := true
        break
      retried := true
    | .falsified dead =>
      let dead := Std.HashSet.ofArray dead
      alive := alive.filter (!dead.contains ·)
  if (← IO.monoMsNow) > sh.due then return
  let kept := Std.HashSet.ofArray alive
  sh.remove h.rel ((List.range heads.size).toArray.filterMap fun k =>
    if kept.contains k then none else some heads[k]!)
  unless settled do sh.enqueue #[ci]

private def worker (q : Query) (sh : Shared) (s : Solver) : IO Unit := do
  repeat
    match ← sh.take q with
    | .done => break
    | .wait => IO.sleep 1
    | .clause ci =>
      try processClause q sh s ci
      finally sh.work.modify fun w =>
        {w with busy := w.busy.set! (headRel q ci) false, active := w.active - 1}

/-! ## Minimization -/

/-- The candidates of `full` that clause `ci` depends on, through an unsat
core: premise candidates that imply its goal, or the head candidates `needed`. -/
private def dependencies (q : Query) (s : Solver) (full : Array (Array String)) (ci : Nat)
    (needed : Array Nat) : IO (Array (Nat × Nat)) := do
  let cl := q.clauses[ci]!
  let mut cmds := header ++ "(set-option :produce-unsat-cores true)\n" ++ q.preamble ++ "\n"
  for (v, srt) in cl.vars do cmds := cmds ++ s!"(declare-const {v} {srt})"
  for f in cl.facts do cmds := cmds ++ s!"(assert {f})\n"
  let mut names : Array (Nat × Nat) := #[]
  for j in [0:cl.premises.size] do
    let a := cl.premises[j]!
    let sorts := q.relations[a.rel]!.sorts
    for i in [0:a.args.size] do
      cmds := cmds ++ s!"(declare-const pa{j}_{i} {sorts[i]!})(assert (= pa{j}_{i} {a.args[i]!}))"
    let cs := full[a.rel]!
    for k in [0:cs.size] do
      cmds := cmds ++ s!"(assert (! {instantiate cs[k]! (s!"pa{j}_{·}")} :named pn{names.size}))\n"
      names := names.push (a.rel, k)
  let goal := match cl.head with
    | .goal f => f
    | .app h => s!"(and true {" ".intercalate (needed.toList.map (full[h.rel]![·]!))})"
  if let .app h := cl.head then cmds := cmds ++ bindHead q h
  cmds := cmds ++ s!"(assert (not {goal}))(check-sat)"
  s.context.set none
  if let some answer ← s.ask cmds then
    if answer.trim == "unsat" then
      if let some core ← s.ask "(get-unsat-core)" then
        return (tokens core).filterMap fun n => (n.drop 2).toNat? >>= (names[·]?)
  -- without a core no premise can be dropped
  return names

/-- The candidates of the inductive `full` that the goals depend on, when
they still form an inductive invariant; otherwise `full`. -/
private def minimize (q : Query) (solvers : Array Solver) (full : Array (Array String))
    (due : Nat) : IO (Array (Array String)) := do
  let mut chosen : Array (Std.HashSet Nat) := full.map fun _ => {}
  -- the clauses with each relation as their head
  let incoming := q.clauses.size.fold (init := q.relations.map fun _ => (#[] : Array Nat))
    fun ci _ acc => match q.clauses[ci]!.head with
      | .app h => acc.modify h.rel (·.push ci)
      | .goal _ => acc
  let mut queue := (List.range q.clauses.size).toArray.filter fun ci => q.clauses[ci]!.head matches .goal _
  let mut queued := Std.HashSet.ofArray queue
  while !queue.isEmpty do
    if (← IO.monoMsNow) > due then return full
    let batch := queue.extract 0 solvers.size
    queue := queue.extract solvers.size queue.size
    queued := batch.foldl (·.erase ·) queued
    let jobs := batch.map fun ci => match q.clauses[ci]!.head with
      | .app h => (ci, chosen[h.rel]!.toArray.qsort (· < ·))
      | .goal _ => (ci, #[])
    for deps in ← parallel solvers jobs (fun s (ci, needed) => dependencies q s full ci needed) do
      for (r, k) in deps do
        unless chosen[r]!.contains k do
          chosen := chosen.modify r (·.insert k)
          for j in incoming[r]! do
            unless queued.contains j do
              queued := queued.insert j
              queue := queue.push j
  let reduced := full.mapIdx fun r cs => (chosen[r]!.toArray.qsort (· < ·)).map (cs[·]!)
  -- the reduced model must still satisfy every clause
  let holds ← parallel solvers (List.range q.clauses.size).toArray fun s ci => do
    let heads := match q.clauses[ci]!.head with
      | .app h => reduced[h.rel]!
      | .goal _ => #[]
    return (← check q s ci none (reduced[·]!) heads (List.range heads.size).toArray) matches .holds
  return if holds.all id then reduced else full

/-! ## Search -/

/-- Search invariants for `q` with `jobs` solvers within `timeoutMs`: the
conjuncts of each relation's invariant, or why there are none (the goal
clauses do not hold under the candidates that survive, or the time ran out).
`log` reports the progress. -/
def search (q : Query) (jobs timeoutMs : Nat) (log : String → IO Unit) :
    IO (Except String (Array (Array String))) := do
  let start ← IO.monoMsNow
  let count := fun (xs : Array (Array String)) => xs.foldl (· + ·.size) 0
  let elapsed : IO String := do return s!"{((← IO.monoMsNow) - start) / 1000} s"
  let initial := initialCandidates q
  log s!"{count initial} candidates for {q.relations.size} relations, {q.clauses.size} clauses"
  let queue := (List.range q.clauses.size).toArray.filter fun ci => q.clauses[ci]!.head matches .app _
  let users := queue.foldl (init := q.relations.map fun _ => (#[] : Array Nat)) fun acc ci =>
    q.clauses[ci]!.premises.foldl (init := acc) fun acc a =>
      if acc[a.rel]!.contains ci then acc else acc.modify a.rel (·.push ci)
  let sh : Shared := {
    rels := ← IO.mkRef (initial.map (0, ·))
    work := ← IO.mkRef {
      queue, queued := (List.range q.clauses.size).toArray.map queue.contains
      busy := q.relations.map fun _ => false }
    users, due := start + timeoutMs, checks := ← IO.mkRef 0, unknowns := ← IO.mkRef 0 }
  let solvers ← (List.range (max 1 jobs)).toArray.mapM fun _ => Solver.new
  let stop ← IO.mkRef false
  let dog ← IO.asTask (prio := .dedicated) (watchdog solvers stop)
  try
    let tasks ← solvers.mapM fun s => IO.asTask (prio := .dedicated) (worker q sh s)
    -- (every task ends before an error is raised: none may outlive the solvers)
    for r in ← tasks.mapM fun t => IO.wait t do IO.ofExcept r
    if (← IO.monoMsNow) > sh.due then
      return .error s!"no fixpoint within {timeoutMs / 1000} s ({← sh.checks.get} checks)"
    let fixpoint := (← sh.rels.get).map (·.2)
    log s!"{count fixpoint} candidates hold after {← sh.checks.get} checks, \
      {← sh.unknowns.get} unknown ({← elapsed})"
    let goals := (List.range q.clauses.size).toArray.filter fun ci => q.clauses[ci]!.head matches .goal _
    let outcomes ← parallel solvers goals fun s ci => do
      match ← check q s ci none (fixpoint[·]!) #[] #[] with
      | .unknown => check q s ci none (fixpoint[·]!) #[] #[]
      | o => pure o
    let failing := outcomes.filter (!· matches .holds) |>.size
    if failing > 0 then
      let unknown := outcomes.filter (· matches .unknown) |>.size
      return .error s!"{failing} of {goals.size} goal clauses do not hold under the {count fixpoint} \
        surviving candidates ({unknown} without an answer)"
    let invariants ← minimize q solvers fixpoint sh.due
    log s!"{count invariants} conjuncts needed ({← elapsed})"
    return .ok invariants
  finally
    stop.set true
    discard <| IO.wait dog
    for s in solvers do s.stop

end Blaster.Proof.Explore.Houdini
