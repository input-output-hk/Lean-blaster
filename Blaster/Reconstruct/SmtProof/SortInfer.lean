import Blaster.Reconstruct.SmtProof.IR

/-!
# Sort inference on SMT proofs

Z3 prints the nullary constructors of parametric datatypes without their sorts (e.g., `List.nil` for all the instances
of `@List`), and doesn't print all the occurrences of a term as the same object (e.g., `(List.cons.0 List.nil)` printed
twice in a term, not bound by a `let`). Each conclusion is interpreted by itself (see `stepConcl`): the instances that
the step doesn't determine are defaulted, such that the occurrences of a term in different steps may be interpreted in
different instances (e.g., `(List.cons.0 List.nil)` as a pair of `Prod Data Data` in a step and of `Prod Unit Unit` in
another), which breaks the syntactic comparisons of the replay (e.g., the paths of `trans*`).

The sorts are inferred here on the whole proof: one sort per term object (the occurrences of a term object, shared by
the expansion of `let`, are the same term of the solver), with the constraints of all the steps (the signatures of the
query, the sorts of the arguments of equalities and conditionals, ...). The inferred instances of the constructor
applications that their arguments don't determine (e.g., `List.nil`, possibly partially, e.g., `(@List (@Prod Data ?))`)
are hints for their interpretation (see `Interp.withSortHint`).
-/

namespace Blaster.Reconstruct.SmtProof.SortInfer

/-- SMT sort with unification variables. -/
inductive SSort where
  | var (i : Nat)
  | con (name : String) (args : Array SSort)
  deriving Inhabited, BEq, Repr

/-- Signature of a function symbol: type parameters (of the constructors, selectors and testers of parametric
    datatypes), sorts of the arguments and of the result. -/
structure Sig where
  params : Array String := #[]
  args : Array SExpr
  result : SExpr
  deriving Inhabited

/-- The signatures of the symbols of a query and of a proof (see `signatures`). -/
structure Signatures where
  funs : Std.HashMap String Sig := {}
  /-- constructors of parametric datatypes whose instances are not determined by their arguments (e.g., `List.nil`,
      `Sum.inl`): their applications get hints -/
  hinted : Std.HashSet String := {}
  /-- sort aliases (`define-sort` without parameters) -/
  aliases : Std.HashMap String SExpr := {}
  deriving Inhabited

/-- Sorted variables `((x S) ...)`. -/
private def sortedVars (e : SExpr) : Array (String × SExpr) :=
  match e with
  | .list vs => vs.filterMap fun v => match v with
    | .list #[.atom x, s] => some (x, s)
    | _ => none
  | _ => #[]

/-- Whether the atom `p` occurs in the sort `s`. -/
private partial def occursIn (p : String) (s : SExpr) : Bool :=
  match s with
  | .atom a => a == p
  | .list xs => xs.any (occursIn p)
  | _ => false

/-- Signatures of the symbols declared by the commands `cmds` and of the functions `defs` defined by the proof. -/
def signatures (cmds : Array SExpr) (defs : Array FunDef) : Signatures := Id.run do
  let mut sigs : Signatures := {}
  let addDatatype (sigs : Signatures) (n : String) (decl : SExpr) : Signatures := Id.run do
    let (params, ctors) := match decl with
      | .list #[.atom "par", .list ps, .list cs] => (ps.filterMap SExpr.atom?, cs)
      | .list cs => (#[], cs)
      | _ => (#[], #[])
    let dt := if params.isEmpty then SExpr.atom n else .list (#[.atom n] ++ params.map .atom)
    let mut sigs := sigs
    for c in ctors do
      let (cname, fields) := match c with
        | .atom a => (a, #[])
        | .list xs => ((xs[0]? >>= SExpr.atom?).getD "", xs.extract 1 xs.size)
        | _ => ("", #[])
      if cname.isEmpty then continue
      let fieldSorts := fields.filterMap fun f => match f with
        | .list #[_, s] => some s
        | _ => none
      let mut funs := sigs.funs.insert cname { params, args := fieldSorts, result := dt }
        |>.insert s!"is-{cname}" { params, args := #[dt], result := .atom "Bool" }
      for f in fields do
        if let .list #[.atom sel, s] := f then funs := funs.insert sel { params, args := #[dt], result := s }
      sigs := { sigs with funs }
      if params.any (fun p => !fieldSorts.any (occursIn p)) then
        sigs := { sigs with hinted := sigs.hinted.insert cname }
    return sigs
  for c in cmds do
    let some xs := c.list? | continue
    match xs[0]?.bind SExpr.atom?, (xs[1]? : Option SExpr) with
    | some "define-sort", some (.atom n) =>
        if let some (SExpr.list #[]) := xs[2]? then
          if let some s := xs[3]? then sigs := { sigs with aliases := sigs.aliases.insert n s }
    | some "declare-const", some (.atom n) =>
        if let some s := xs[2]? then sigs := { sigs with funs := sigs.funs.insert n { args := #[], result := s } }
    | some "declare-fun", some (.atom n) =>
        if let (some (SExpr.list ss), some r) := ((xs[2]? : Option SExpr), (xs[3]? : Option SExpr)) then
          sigs := { sigs with funs := sigs.funs.insert n { args := ss, result := r } }
    | some "define-fun", some (.atom n) | some "define-fun-rec", some (.atom n) =>
        if let (some ps, some r) := ((xs[2]? : Option SExpr), (xs[3]? : Option SExpr)) then
          sigs := { sigs with funs := sigs.funs.insert n { args := (sortedVars ps).map (·.2), result := r } }
    | some "define-funs-rec", some (.list decls) =>
        for d in decls do
          if let SExpr.list #[.atom n, ps, r] := d then
            sigs := { sigs with funs := sigs.funs.insert n { args := (sortedVars ps).map (·.2), result := r } }
    | some "declare-datatype", some (.atom n) =>
        if let some d := xs[2]? then sigs := addDatatype sigs n d
    | some "declare-datatypes", some (.list sorts) =>
        let some (SExpr.list decls) := xs[2]? | continue
        for (s, d) in sorts.zip decls do
          if let some (SExpr.atom n) := s.list? >>= (·[0]?) then sigs := addDatatype sigs n d
    | _, _ => pure ()
  for d in defs do
    sigs := { sigs with funs := sigs.funs.insert d.name { args := d.params.map (·.2), result := d.sort } }
  return sigs

/-- The state of the inference: the sort variables, the sorts of the term objects and the hinted terms. -/
structure State where
  /-- bindings of the sort variables -/
  binds : Array (Option SSort) := #[]
  /-- sorts of the term objects -/
  sorts : TermCache SSort := {}
  /-- hinted constructor applications (see `Signatures.hinted`) -/
  hintedTerms : Array (USize × SSort) := #[]
  /-- number of unification failures (e.g., symbols of the query not interpreted as declared) -/
  conflicts : Nat := 0

/-- The monad of the inference. -/
abbrev M := StateM State

/-- A fresh sort variable. -/
def fresh : M SSort := modifyGet fun s => (.var s.binds.size, { s with binds := s.binds.push none })

/-- `s` with its bound variables substituted at the root. -/
partial def resolve (s : SSort) : M SSort := do
  match s with
  | .var i =>
      match (← get).binds[i]! with
      | some t =>
          let t' ← resolve t
          -- path compression
          modify fun st => { st with binds := st.binds.set! i (some t') }
          return t'
      | none => return s
  | _ => return s

/-- `s` with all its bound variables substituted. -/
partial def zonk (s : SSort) : M SSort := do
  match ← resolve s with
  | .con n args => return .con n (← args.mapM zonk)
  | s => return s

/-- Whether the sort variable `i` occurs in `s` (occurs check of `unify`). -/
partial def occurs (i : Nat) (s : SSort) : M Bool := do
  match ← resolve s with
  | .var j => return i == j
  | .con _ args => args.anyM (occurs i)

/-- Unify `a` and `b`; a failure is counted (and ignored). -/
partial def unify (a b : SSort) : M Unit := do
  match ← resolve a, ← resolve b with
  | .var i, .var j => if i != j then modify fun s => { s with binds := s.binds.set! i (some (.var j)) }
  | .var i, t | t, .var i =>
      if ← occurs i t then modify fun s => { s with conflicts := s.conflicts + 1 }
      else modify fun s => { s with binds := s.binds.set! i (some t) }
  | .con n as, .con m bs =>
      if n != m || as.size != bs.size then modify fun s => { s with conflicts := s.conflicts + 1 }
      else for (x, y) in as.zip bs do unify x y

/-- The sorts of the literals and of the built-in operations. -/
def boolSort : SSort := .con "Bool" #[]
def intSort : SSort := .con "Int" #[]
def stringSort : SSort := .con "String" #[]

/-- The sort `s` of the query with the type parameters `subst` and the aliases `aliases` expanded. -/
partial def ofSExpr (aliases : Std.HashMap String SExpr) (subst : Std.HashMap String SSort) (s : SExpr) : M SSort := do
  match s with
  | .atom a =>
      if let some t := subst.get? a then return t
      if let some s' := aliases.get? a then return ← ofSExpr aliases {} s'
      return .con a #[]
  | .list xs =>
      let some (SExpr.atom h) := xs[0]? | fresh
      return .con h (← (xs.extract 1 xs.size).mapM (ofSExpr aliases subst))
  | _ => fresh

/-- The sort of `t` (with the bound variables `env`), recording the sorts of its subterms. -/
partial def infer (sigs : Signatures) (env : Std.HashMap String SSort) (t : STerm) : M SSort := do
  let addr := termAddr t
  if let some s := (← get).sorts.get? addr then return s
  let s ← inferCore t
  modify fun st => { st with sorts := st.sorts.insert addr s }
  return s
where
  inferCore (t : STerm) : M SSort := do
    match t with
    | .num _ => return intSort
    | .str _ => return stringSort
    | .lit _ => fresh
    | .metadata _ => fresh
    | .annot t _ => infer sigs env t
    | .sym f => app t f #[]
    | .app f args => app t f args
    | .qual f srt args =>
        -- NOTE: no hint, the sort of the application being given
        let r ← app t f args (hint := false)
        unify r (← ofSExpr sigs.aliases {} srt)
        return r
    | .iapp f idx args =>
        let ss ← args.mapM (infer sigs env)
        if f == "is" || f.startsWith "is-" then
          let ctor := if f == "is" then (match idx[0]? with | some (STerm.sym c) => c | _ => "") else f.drop 3
          if let (some sig, some s) := (sigs.funs.get? ctor, ss[0]?) then
            let subst ← sig.params.foldlM (fun m p => return m.insert p (← fresh)) {}
            unify s (← ofSExpr sigs.aliases subst sig.result)
          return boolSort
        if f == "case-def" || ["pbge", "pble", "pbeq", "at-least", "at-most"].contains f then return boolSort
        -- indexed applications of recursive functions (e.g., `((_ @Nat.pow 0) x y)`)
        applySig f ss
    | .quant k vars body =>
        let env' ← vars.foldlM (fun m (x, s) => return m.insert x (← ofSExpr sigs.aliases {} s)) env
        discard <| infer sigs env' body
        if k == .lambda then fresh else return boolSort
  /-- Application of the symbol `f` (term `t`) to `args`, recorded as hinted when `hint` (see `Signatures.hinted`). -/
  app (t : STerm) (f : String) (args : Array STerm) (hint := true) : M SSort := do
    if args.isEmpty then
      if let some s := env.get? f then return s
    let ss ← args.mapM (infer sigs env)
    let all (s : SSort) : M Unit := ss.forM (unify · s)
    match f with
    | "true" | "false" => return boolSort
    | "not" | "and" | "or" | "=>" | "xor" =>
        all boolSort
        return boolSort
    | "=" | "distinct" =>
        if let some s := ss[0]? then all s
        return boolSort
    | "~" => return boolSort
    | "ite" =>
        let #[c, a, b] := ss | fresh
        unify c boolSort
        unify a b
        return a
    | "+" | "-" | "*" | "div" | "mod" | "abs" | "div0" | "mod0" =>
        all intSort
        return intSort
    | "<=" | "<" | ">=" | ">" =>
        all intSort
        return boolSort
    | "str.++" | "seq.++" =>
        all stringSort
        return stringSort
    | "str.len" | "seq.len" =>
        all stringSort
        return intSort
    | "str.<" | "str.<=" =>
        all stringSort
        return boolSort
    | "str.from_code" =>
        all intSort
        return stringSort
    | "seq.unit" | "seq.empty" => return stringSort
    | _ =>
        let r ← applySig f ss
        if hint && sigs.hinted.contains f then
          modify fun st => { st with hintedTerms := st.hintedTerms.push (termAddr t, r) }
        return r
  /-- Application of the declared symbol `f` to arguments of sorts `ss` (a fresh sort when `f` is unknown). -/
  applySig (f : String) (ss : Array SSort) : M SSort := do
    let some sig := sigs.funs.get? f | fresh
    let subst ← sig.params.foldlM (fun m p => return m.insert p (← fresh)) {}
    if sig.args.size == ss.size then
      for (a, s) in sig.args.zip ss do unify s (← ofSExpr sigs.aliases subst a)
    ofSExpr sigs.aliases subst sig.result

/-- Inferred sort, with `unknown` for its undetermined parts. -/
inductive Hint where
  | unknown
  | con (name : String) (args : Array Hint)
  deriving Inhabited, BEq

/-- The hint of a sort (its sort variables being unknown). -/
partial def SSort.toHint : SSort → Hint
  | .var _ => .unknown
  | .con n args => .con n (args.map SSort.toHint)

/-- The ground sort of a hint (`none` when it has unknown parts). -/
partial def Hint.toSExpr? : Hint → Option SExpr
  | .unknown => none
  | .con n args => if args.isEmpty then some (.atom n) else do
      return .list (#[.atom n] ++ (← args.mapM Hint.toSExpr?))

/-- Inferred sorts of the hinted constructor applications of the proof `p` (on term object addresses), given the
    commands of the query `cmds`; and the number of unification failures. -/
def inferHints (cmds : Array SExpr) (p : Proof) : TermCache Hint × Nat := Id.run do
  let sigs := signatures cmds p.defs
  if sigs.hinted.isEmpty then return ({}, 0)
  let run : M Unit := do
    -- NOTE: the consumers first, e.g., the conclusion of a `proof-bind` (a lambda) before the conclusion of its
    -- premise, whose free variables are its bound variables
    for i' in [:p.steps.size] do
      let step := p.steps[p.steps.size - 1 - i']!
      discard <| infer sigs {} step.concl
      for a in step.args do discard <| infer sigs {} a
  let ((), st) := run.run {}
  -- NOTE: the hints without any known part are not recorded
  let (hints, st) := (st.hintedTerms.foldlM (init := ({} : TermCache Hint)) fun m (addr, s) => do
    let h := (← zonk s).toHint
    return if h == .unknown then m else m.insert addr h : M (TermCache Hint)).run st
  return (hints, st.conflicts)

end Blaster.Reconstruct.SmtProof.SortInfer
