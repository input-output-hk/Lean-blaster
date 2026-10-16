import Lean

/-!
# Printing kernel terms as Lean source

`printDecl` prints a closed declaration as Lean source that denotes its kernel
terms exactly, for `kernel%` (`Export/Term.lean`): every constant with its
universe levels (and with `@` when it has implicit parameters), every binder
with its type; a raw literal is printed `nat_lit n`, a projection `e.i`, and
the numerals of `Nat` and `Int` as `(n : Nat)`, `(n : Int)` and `(-n : Int)`.
The only notation is `→`. Nothing is elided, so the text is a transcription of
the terms, which the kernel checks again when the file is compiled.

Proof terms built by automation are directed acyclic graphs: one subterm can
occur thousands of times, and printing every occurrence would make the text
exponentially larger than the term. A subterm that occurs more than once (and
is not tiny) is printed once instead, under a name: a closed one as a
top-level definition `term_i`, shared by all the declarations of the file; one
with bound variables as a `let` `t_i` right after the innermost binder it
refers to, which is in scope of all its occurrences. Occurrences under
different binders are recognized as the same subterm by their shape
(`canonId`), whatever the de Bruijn indices of the variables. The `let`s
change the terms only up to definitional unfolding (`zeta`), and the
definitions up to `delta`.
-/
namespace Blaster.Proof.Export
open Lean

/-! ## Sharing -/

/-- A subterm in context: its shape (`canonId`: the term up to the numbering of
its loose bound variables) and the binder instances these refer to, by
increasing de Bruijn index (see `Sharing.binders`). Equal keys denote equal
terms, wherever they occur: the same term under other binders it does not
refer to has the same key. -/
structure Key where
  shape : Nat
  /-- The binder instances (an interned array, see `Sharing.binderSets`; `0` is none). -/
  binders : Nat
  /-- The innermost of them, if any (`0` otherwise). -/
  anchor : Nat
  deriving BEq, Hashable

/-- The sharing in the terms of a declaration. A binder instance is a binding
term in its context (its `Key`), numbered: two occurrences of a key bind the
same variable. -/
structure Sharing where
  /-- The loose bound variables of the terms that have some, as bit sets. -/
  loose : Std.HashMap ExprStructEq Nat := {}
  /-- How many times each subterm occurs in the printed terms, counting the
  subterms of a repeated term once. -/
  uses : Std.HashMap Key Nat := {}
  /-- The subterms, each after its own subterms. -/
  order : Array Key := #[]
  /-- The binder instances, numbered from 1. -/
  binders : Std.HashMap Key Nat := {}
  /-- The arrays of binder instances of the keys, numbered (`0` is the empty one). -/
  binderSets : Std.HashMap (Array Nat) Nat := {(#[], 0)}
  /-- The interned arrays of binder instances, by number. -/
  binderArrays : Array (Array Nat) := #[#[]]
  /-- The shapes of terms (`canonId`), by term. -/
  shapes : Std.HashMap ExprStructEq Nat := {}
  /-- The shapes: of closed terms, by term; of the others, by their encoding. -/
  closedShapes : Std.HashMap ExprStructEq Nat := {}
  openShapes : Std.HashMap (Array Nat) Nat := {}
  /-- An occurrence of each subterm, as it occurs: a `let` of it is printed from
  this occurrence, whose subterms have the keys they were counted with. -/
  occurrence : Std.HashMap Key Expr := {}

abbrev ShareM := StateM Sharing

/-- Terms printed as they are: never named. -/
def isAtom : Expr → Bool
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => true
  | _ => false

/-- Whether `e` has more than `n` nodes (counting a repeated subterm each time). -/
partial def exceeds (e : Expr) (n : Nat) : Bool :=
  go e n |>.isNone
where
  /-- The budget left after `e`, if any. -/
  go (e : Expr) (n : Nat) : Option Nat := do
    if n == 0 then none
    match e with
    | .app f a => go a (← go f (n - 1))
    | .lam _ t b _ | .forallE _ t b _ => go b (← go t (n - 1))
    | .letE _ t v b _ => go b (← go v (← go t (n - 1)))
    | .mdata _ b | .proj _ _ b => go b (n - 1)
    | _ => some (n - 1)

/-- Subterms small enough to print at each occurrence. -/
def isSmall (e : Expr) : Bool := !exceeds e 8

/-- The loose bound variables of `e`, as a bit set. -/
partial def looseSet (e : Expr) : ShareM Nat := do
  if e.looseBVarRange == 0 then return 0
  if let some s := (← get).loose[(⟨e⟩ : ExprStructEq)]? then return s
  let s ← match e with
    | .bvar i => pure (1 <<< i)
    | .app f a => pure ((← looseSet f) ||| (← looseSet a))
    | .lam _ t b _ | .forallE _ t b _ => pure ((← looseSet t) ||| ((← looseSet b) >>> 1))
    | .letE _ t v b _ => pure ((← looseSet t) ||| (← looseSet v) ||| ((← looseSet b) >>> 1))
    | .mdata _ b | .proj _ _ b => looseSet b
    | _ => pure 0
  modify fun st => {st with loose := st.loose.insert ⟨e⟩ s}
  return s

/-- The members of a bit set, increasing. -/
partial def bits (s : Nat) (acc : Array Nat := #[]) : Array Nat :=
  if s == 0 then acc else
    let rest := s &&& (s - 1)
    bits rest (acc.push (s - rest).log2)

/-- The positions of the members of `sub` (each lowered by `cutoff`, those
below it marked `bound`) among the members of `set`; both increasing. -/
def positions (sub set : Array Nat) (cutoff bound : Nat) : Array Nat := Id.run do
  let mut out := #[]
  let mut k := 0
  for j in sub do
    if j < cutoff then out := out.push bound; continue
    while k < set.size && set[k]! < j - cutoff do k := k + 1
    out := out.push k
  return out

/-- The shape of `e`: equal for terms equal up to the numbering of their loose
bound variables (numbered by rank: the lowest is `#0`), whatever the binders
between them. It is computed from the shapes of the subterms, where each
loose variable of a subterm is among those of the term: no term is copied. -/
partial def canonId (e : Expr) : ShareM Nat := do
  if let some i := (← get).shapes[(⟨e⟩ : ExprStructEq)]? then return i
  let i ← if e.looseBVarRange == 0 then closed e else
    let set := bits (← looseSet e)
    -- (a child: its shape, and where its loose variables are among the term's)
    let part := fun (c : Expr) (cutoff : Nat) => do
      let sub := bits (← looseSet c)
      return #[← canonId c, sub.size] ++ positions sub set cutoff (set.size + 1)
    match e with
    | .bvar _ => encoded #[0]
    | .mdata _ b => canonId b
    | .app f a => encoded (#[1] ++ (← part f 0) ++ (← part a 0))
    | .lam _ t b bi => encoded (#[2, bi.ctorIdx] ++ (← part t 0) ++ (← part b 1))
    | .forallE _ t b bi => encoded (#[3, bi.ctorIdx] ++ (← part t 0) ++ (← part b 1))
    | .letE _ t v b nondep =>
      encoded (#[4, if nondep then 1 else 0] ++ (← part t 0) ++ (← part v 0) ++ (← part b 1))
    | .proj n i b => encoded (#[5, ← closed (mkConst n), i] ++ (← part b 0))
    | _ => closed e
  modify fun st => {st with shapes := st.shapes.insert ⟨e⟩ i}
  return i
where
  /-- A fresh shape number. -/
  fresh : ShareM Nat := do
    let st ← get
    return st.closedShapes.size + st.openShapes.size + 1
  closed (e : Expr) : ShareM Nat := do
    if let some i := (← get).closedShapes[(⟨e⟩ : ExprStructEq)]? then return i
    let i ← fresh
    modify fun st => {st with closedShapes := st.closedShapes.insert ⟨e⟩ i}
    return i
  encoded (code : Array Nat) : ShareM Nat := do
    if let some i := (← get).openShapes[code]? then return i
    let i ← fresh
    modify fun st => {st with openShapes := st.openShapes.insert code i}
    return i

/-- The key of `e` under the binder instances `stack` (innermost last). -/
def keyOf (e : Expr) (stack : Array Nat) : ShareM Key := do
  let binders := (bits (← looseSet e)).map fun i => stack[stack.size - 1 - i]?.getD 0
  let id ← match (← get).binderSets[binders]? with
    | some id => pure id
    | none =>
      let id := (← get).binderSets.size
      modify fun st => {st with binderSets := st.binderSets.insert binders id,
                                binderArrays := st.binderArrays.push binders}
      pure id
  return {shape := ← canonId e, binders := id, anchor := binders[0]?.getD 0}

/-- The instance number of the binder of a binding term (by its key). -/
def binderInstance (k : Key) : ShareM Nat := do
  if let some id := (← get).binders[k]? then return id
  let id := (← get).binders.size + 1
  modify fun st => {st with binders := st.binders.insert k id}
  return id

/-- Count the occurrences of the subterms of `e` (under `stack`). -/
partial def countUses (e : Expr) (stack : Array Nat := #[]) : ShareM Unit := do
  if isAtom e then return
  if let .mdata _ b := e then return ← countUses b stack
  let k ← keyOf e stack
  let n := (← get).uses.getD k 0
  modify fun st => {st with uses := st.uses.insert k (n + 1)}
  if n > 0 then return
  modify fun st => {st with occurrence := st.occurrence.insert k e}
  match e with
  | .app .. =>
    countUses e.getAppFn stack
    for a in e.getAppArgs do countUses a stack
  | .lam _ t b _ | .forallE _ t b _ =>
    countUses t stack
    countUses b (stack.push (← binderInstance k))
  | .letE _ t v b _ =>
    countUses t stack
    countUses v stack
    countUses b (stack.push (← binderInstance k))
  | .proj _ _ b => countUses b stack
  | _ => pure ()
  modify fun st => {st with order := st.order.push k}

/-- Whether a subterm is printed once, under a name. -/
def Sharing.named (s : Sharing) (k : Key) : Bool :=
  s.uses.getD k 0 ≥ 2 && (s.occurrence[k]?.any fun e => !isSmall e && !e.hasLevelParam)

/-! ## Printing -/

/-- How the constants of a declaration are printed. -/
structure Names where
  /-- The printed name of each constant. -/
  consts : Std.HashMap Name String := {}
  /-- The constants with implicit parameters (applied with `@`). -/
  explicit : Std.HashSet Name := {}
  /-- Names no binder or `let` may have: parser tokens, and the first
  components of printed constant names (which a local would capture). -/
  reserved : Std.HashSet String := {}
  /-- The top-level definitions of shared closed terms are declared as
  `globalName.term_i` and referred to as `globalRef ++ "term_i"`. -/
  globalName : Name
  globalRef : String
  /-- Whether a string is a parser token (no binder may be named so). -/
  isToken : String → Bool := fun _ => false
  /-- Terms whose text is longer than this are given to `kernel%` as string
  literals (`Export/Term.lean`: Lean's parser is slow on very large terms). -/
  textAbove : Nat := 100000

/-- The longest run of `#`s right after a `"` in `s`. -/
def hashesAfterQuote (s : String) : Nat :=
  -- (the length of the current run after a `"`, if in one, and the longest)
  let (_, longest) := s.foldl (init := ((none : Option Nat), 0)) fun (run?, longest) c =>
    match run?, c with
    | some n, '#' => (some (n + 1), max longest (n + 1))
    | _, '"' => (some 0, longest)
    | _, _ => (none, longest)
  longest

/-- `kernel% t` for the term `t`, its lines after the first indented by
`indent` spaces; its text given as a raw string literal when it is longer
than `above` (one ends at a `"` followed by as many `#`s as it starts with:
one more than the text has after a `"`). -/
def kernelText (t : Format) (above indent : Nat) : String :=
  let text := t.pretty 100
  if text.length ≤ above then
    "kernel% " ++ text.replace "\n" ("\n" ++ String.mk (List.replicate indent ' '))
  else
    let hashes := String.mk (List.replicate (hashesAfterQuote text + 1) '#')
    "kernel% r" ++ hashes ++ "\"" ++ text ++ "\"" ++ hashes

/-- The printer's state across the declarations of a file. -/
structure Printer where
  sharing : Sharing := {}
  /-- The names of the `let`-bound subterms. -/
  lets : Std.HashMap Key String := {}
  /-- The `let`-bound subterms, after the binder instance whose body starts with them. -/
  anchored : Std.HashMap Nat (Array Key) := {}
  /-- The top-level definitions of shared closed terms (numbered), by term. -/
  globals : Std.HashMap ExprStructEq Nat := {}
  /-- Definitions of shared closed terms not yet emitted. -/
  pending : Array String := #[]
  /-- The binder names of the declaration being printed (all distinct: no
  binder hides another), and the next suffix to try for each base name. -/
  binderNames : Std.HashSet String := {}
  suffixes : Std.HashMap String Nat := {}

abbrev PrintM := ReaderT Names (StateM Printer)

/-- Run a step of the sharing analysis in the printer. -/
def liftShare (x : ShareM α) : PrintM α :=
  modifyGet fun st =>
    let (a, sharing) := x.run st.sharing
    (a, {st with sharing})

/-- The binders in scope at a position. -/
structure Scope where
  /-- Binder instances (innermost last; `0` stands for a binder nothing refers to). -/
  stack : Array Nat := #[]
  names : Array String := #[]
  /-- Their types (relative to their binders). -/
  types : Array Expr := #[]
  /-- How many indented blocks enclose the position. -/
  depth : Nat := 0

/-- Whether a type's leading binders include implicit ones. -/
partial def hasImplicit : Expr → Bool
  | .forallE _ _ b bi => !bi.isExplicit || hasImplicit b
  | .mdata _ b => hasImplicit b
  | _ => false

/-- Whether `s` is `stem_i`, the form of the names the printer makes up. -/
def isNumbered (stem s : String) : Bool :=
  (stem ++ "_").isPrefixOf s && s.length > stem.length + 1 && (s.drop (stem.length + 1)).all Char.isDigit

/-- Whether `s` is the name of a shared subterm's `let` (`t_i`). -/
def isLetName (s : String) : Bool := isNumbered "t" s

/-- Lines nested more deeply than this are not indented further (proof terms are deep). -/
def maxIndentDepth : Nat := 3

/-- `f` indented one more level, up to `maxIndentDepth` levels. -/
def Scope.indent (s : Scope) (f : Format) : Format :=
  if s.depth < maxIndentDepth then Format.nest 2 f else f

/-- `s` one indentation level deeper. -/
def Scope.deeper (s : Scope) : Scope := {s with depth := s.depth + 1}

/-- The scope in which `e`, the occurrence a shared subterm is printed from,
is printed at another position, under the scope `s`: each loose variable of
`e` (`loose`, increasing) names the binder of `s` it refers to, found by its
instance (`instances`, in the same order); its other positions are binders
nothing refers to. The same binding term can be printed at positions with
different binders between it and those it refers to (a term that mentions a
universe parameter is never shared): de Bruijn indices are only valid where the
occurrence lies. `none` when an instance is not in scope. -/
def Scope.forOccurrence (s : Scope) (loose instances : Array Nat) : Option Scope := Id.run do
  let size := (loose.back?.map (· + 1)).getD 0
  let mut stack := Array.replicate size 0
  let mut names := Array.replicate size "_"
  let mut types : Array Expr := Array.replicate size (.sort .zero)
  for (j, binder) in loose.zip instances do
    -- (the innermost binder of the instance in scope)
    let mut found := none
    for q in [0:s.stack.size] do
      if s.stack[s.stack.size - 1 - q]! == binder then
        found := some (s.stack.size - 1 - q)
        break
    let some p := found | return none
    stack := stack.set! (size - 1 - j) binder
    names := names.set! (size - 1 - j) s.names[p]!
    types := types.set! (size - 1 - j) s.types[p]!
  return some {s with stack, names, types}

/-- Whether `s` is a valid identifier (without escaping). -/
def validName (s : String) : Bool :=
  !s.isEmpty && isIdFirst s.front && (s.drop 1).all isIdRest

/-- A fresh name for a binder named `n`: valid, not reserved, and distinct
from the declaration's other binder names. -/
def freshName (n : Name) : PrintM String := do
  let base := match n.eraseMacroScopes with
    | .str _ str => if validName str then str else "x"
    | _ => "x"
  -- (`t_i` and `term_i` are the names of shared subterms)
  let base := if base == "t" || base == "term" then base ++ "'" else base
  let names ← read
  let st ← get
  let ok := fun (c : String) => !st.binderNames.contains c && !names.reserved.contains c &&
    !isLetName c && !isNumbered "term" c && !names.isToken c
  let mut name := base
  let mut i := st.suffixes.getD base 1
  if !ok base then
    while !ok s!"{base}_{i}" do i := i + 1
    name := s!"{base}_{i}"
    i := i + 1
  modify fun st => {st with binderNames := st.binderNames.insert name, suffixes := st.suffixes.insert base i}
  return name

/-- `s` with a binder of instance `id`, named `name`. -/
def Scope.bind (s : Scope) (id : Nat) (name : String) (type : Expr) : Scope :=
  {s with stack := s.stack.push id, names := s.names.push name, types := s.types.push type}

/-- A universe level, as `kernel%` reads it. -/
partial def levelFmt : Level → Format
  | .zero => "0"
  | .param n => n.toString
  | .mvar _ => "_"
  | l@(.succ _) =>
    match l.toNat with
    | some n => toString n
    | none =>
      let (base, k) := succs l 0
      atomLevel base ++ "+" ++ toString k
  | .max a b => "max " ++ atomLevel a ++ " " ++ atomLevel b
  | .imax a b => "imax " ++ atomLevel a ++ " " ++ atomLevel b
where
  succs : Level → Nat → Level × Nat
    | .succ l, k => succs l (k + 1)
    | l, k => (l, k)
  atomLevel (l : Level) : Format :=
    match l with
    | .zero | .param _ | .mvar _ => levelFmt l
    | .succ _ => if l.toNat.isSome then levelFmt l else Format.paren (levelFmt l)
    | _ => Format.paren (levelFmt l)

/-- The sort at level `l`: `Prop`, `Type`, `Type u` or `Sort u`. -/
def sortFmt (l : Level) : Format :=
  match l with
  | .zero => "Prop"
  | .succ .zero => "Type"
  | .succ u => "Type " ++ levelFmt.atomLevel u
  | _ => "Sort " ++ levelFmt.atomLevel l

/-- A constant (with `@` when `explicit`). -/
def constFmt (n : Name) (ls : List Level) (explicit : Bool) : PrintM Format := do
  let names ← read
  let name := names.consts[n]?.getD n.toString
  let at_ := if explicit && names.explicit.contains n then "@" else ""
  if ls.isEmpty then return at_ ++ name
  return at_ ++ name ++ ".{" ++ Format.joinSep (ls.map levelFmt) ", " ++ "}"

/-- `e` as a numeral of `Nat` or `Int`, `(n : Nat)`, `(n : Int)` or
`(-n : Int)`, if it is one exactly as Lean elaborates those. -/
def numeral? (e : Expr) : Option String := do
  if e.isAppOfArity ``Neg.neg 3 then
    let args := e.getAppArgs
    guard (args[0]!.isConstOf ``Int && args[1]!.isConstOf ``Int.instNegInt)
    let n ← natural? args[2]! ``Int
    guard (n > 0)
    return s!"(-{n} : Int)"
  if let some n := natural? e ``Nat then return s!"({n} : Nat)"
  return s!"({← natural? e ``Int} : Int)"
where
  natural? (e : Expr) (type : Name) : Option Nat := do
    guard (e.isAppOfArity ``OfNat.ofNat 3)
    let args := e.getAppArgs
    guard (args[0]!.isConstOf type)
    let .lit (.natVal n) := args[1]! | none
    let inst := if type == ``Nat then mkApp (mkConst ``instOfNatNat) (mkRawNatLit n)
      else mkApp (mkConst ``instOfNat) (mkRawNatLit n)
    guard (args[2]! == inst)
    return n

/-- A `let` value, parenthesized unless atomic: inside parentheses Lean's parser
lifts the indentation requirement a `let` puts on the lines of its value. -/
def letValue (e : Expr) (f : Format) : Format :=
  match e.consumeMData with
  | .bvar .. | .const .. | .sort .. | .lit (.strVal _) => f
  | _ => Format.paren f

mutual

/-- Print `e` under the binders `s`; `defining` is the shared subterm whose
definition is being printed (printed in full, not by its name). -/
partial def term (e : Expr) (s : Scope) (defining : Option Key := none) : PrintM Format := do
  match e with
  | .bvar i => return s.names[s.names.size - 1 - i]?.getD s!"#{i}"
  | .const n ls => constFmt n ls true
  | .sort l => return sortFmt l
  | .lit (.natVal n) => return s!"nat_lit {n}"
  | .lit (.strVal str) => return str.quote
  | .mdata _ b => term b s defining
  | .fvar id => return s!"«fvar {id.name}»"
  | .mvar id => return s!"«mvar {id.name}»"
  | _ =>
    if let some n := numeral? e then return n
    let k ← liftShare (keyOf e s.stack)
    if defining != some k then
      if let some name ← reference? k then return name
    match e with
    | .app .. => application e s
    | .lam .. => binders e s true
    | .forallE .. => pi e s
    | .letE n t v b nondep =>
      let id ← liftShare (binderInstance k)
      let tf ← term t s.deeper
      let vf ← term v s.deeper
      let name ← freshName n
      let s' := s.bind id name t
      let (lets, s') ← letsAt id s'
      -- (a chain of `let`s stays at one indentation)
      let body ← term b s'
      return (if nondep then "have " else "let ") ++ name ++ " : " ++ letValue t tf ++ " :=" ++
        s.indent (Format.line ++ letValue v vf) ++ ";" ++ Format.line ++ lets ++ body
    | .proj _ i b => return (← argument b s) ++ "." ++ toString (i + 1)
    | _ => return "?"

/-- The name of a shared subterm, if it has one: a `let` in scope or a
top-level definition (emitted on first use). -/
partial def reference? (k : Key) : PrintM (Option Format) := do
  if k.binders == 0 then
    let names ← read
    let some e := (← get).sharing.occurrence[k]? | return none
    if let some i := (← get).globals[(⟨e⟩ : ExprStructEq)]? then return some s!"{names.globalRef}term_{i}"
    unless (← get).sharing.named k do return none
    let i := (← get).globals.size + 1
    let name := s!"{names.globalRef}term_{i}"
    modify fun st => {st with globals := st.globals.insert ⟨e⟩ i}
    let value ← term e {depth := 1} (defining := some k)
    let decl := s!"noncomputable def {(`_root_ ++ names.globalName ++ .mkSimple s!"term_{i}")} :=\n  " ++
      kernelText value names.textAbove 2
    modify fun st => {st with pending := st.pending.push decl}
    return some name
  unless (← get).sharing.named k do return none
  return (← get).lets[k]?.map fun (name : String) => (name : Format)

/-- An argument: parenthesized unless atomic. -/
partial def argument (e : Expr) (s : Scope) : PrintM Format := do
  match e with
  | .bvar _ | .lit (.strVal _) => term e s
  | .sort .zero | .sort (.succ .zero) => term e s
  | .const n _ => if (← read).explicit.contains n then return Format.paren (← term e s) else term e s
  | .mdata _ b => argument b s
  | .proj .. => term e s
  | _ =>
    if numeral? e |>.isSome then return ← term e s
    if !isAtom e then
      let k ← liftShare (keyOf e s.stack)
      if let some name ← reference? k then return name
    return Format.paren (← term e s)

/-- An application: its head (with `@` when it has implicit parameters) and arguments. -/
partial def application (e : Expr) (s : Scope) : PrintM Format := do
  let f := e.getAppFn
  let args := e.getAppArgs
  let head ← match f with
    | .const n ls => constFmt n ls true
    | .bvar i =>
      let explicit := s.types[s.types.size - 1 - i]?.any hasImplicit
      pure ((if explicit then "@" else "") ++ (← term f s))
    | _ =>
      if isAtom f then argument f s else
      let k ← liftShare (keyOf f s.stack)
      match ← reference? k with
      | some name => pure ("@" ++ name)
      | none => pure (Format.paren (← term f s))
  let mut out := head
  for a in args do
    out := out ++ Format.line ++ (← argument a s.deeper)
  return Format.fill (s.indent out)

/-- The `let`s of the subterms anchored at binder instance `id`, which `s` has
just bound: their text, and the scope with their names. -/
partial def letsAt (id : Nat) (s : Scope) : PrintM (Format × Scope) := do
  let some keys := (← get).anchored[id]? | return (.nil, s)
  let mut s := s
  let mut out := Format.nil
  for k in keys do
    let name ← match (← get).lets[k]? with
      | some name => pure name
      | none =>
        let mut i := (← get).lets.size + 1
        while (← read).reserved.contains s!"t_{i}" do i := i + 1
        let name := s!"t_{i}"
        modify fun st => {st with lets := st.lets.insert k name}
        pure name
    -- (printed from an occurrence, whose variables are the binders in scope it refers to)
    let some e := (← get).sharing.occurrence[k]? | continue
    let loose := bits (← liftShare (looseSet e))
    let instances := (← get).sharing.binderArrays[k.binders]?.getD #[]
    let value ← match s.forOccurrence loose instances with
      | some scope => term e scope.deeper (defining := some k)
      -- (cannot happen: the anchor and the binders outside it are in scope;
      -- the text then fails to compile instead of meaning another term)
      | none => pure "«kernel%: a shared term refers to a binder out of scope»"
    out := out ++ "let " ++ name ++ " :=" ++ s.indent (Format.line ++ letValue e value) ++ ";" ++
      Format.line
  return (out, s)

/-- A run of lambdas (`lam`) or of dependent `∀`s. -/
partial def binders (e : Expr) (s : Scope) (lam : Bool) : PrintM Format := do
  let mut e := e
  let mut s := s
  let mut group : Array Format := #[]
  let mut lets := Format.nil
  repeat
    let (n, t, b, bi) ← match e, lam with
      | .lam n t b bi, true => pure (n, t, b, bi)
      | .forallE n t b bi, false =>
        -- (a non-dependent explicit `∀` is printed as an arrow)
        if bi.isExplicit && !b.hasLooseBVar 0 then break
        pure (n, t, b, bi)
      | _, _ => break
    let k ← liftShare (keyOf e s.stack)
    if !group.isEmpty then
      if (← reference? k).isSome then break
    let id ← liftShare (binderInstance k)
    let tf ← term t s.deeper
    let name ← freshName n
    let binder : Format := name ++ " : " ++ tf
    group := group.push (match bi with
      | .implicit => "{" ++ binder ++ "}"
      | .instImplicit => "[" ++ binder ++ "]"
      | .strictImplicit => "⦃" ++ binder ++ "⦄"
      | .default => Format.paren binder)
    s := s.bind id name t
    e := b
    let (l, s') ← letsAt id s
    s := s'
    if !l.isEmpty then
      lets := l
      break
  let body ← term e s.deeper
  let head := (if lam then "fun " else "∀ ") ++ Format.joinSep group.toList Format.line
  let sep := if lam then " =>" else ","
  return Format.group (s.indent (head ++ sep ++ Format.line ++ lets ++ body))

/-- A `∀`: an arrow when it is non-dependent and explicit, else binders. -/
partial def pi (e : Expr) (s : Scope) : PrintM Format := do
  let .forallE _ t b bi := e | term e s
  unless bi.isExplicit && !b.hasLooseBVar 0 do return ← binders e s false
  -- an arrow: the body is under a binder nothing refers to
  let k ← liftShare (keyOf e s.stack)
  let id ← liftShare (binderInstance k)
  let dom ← match t with
    | .forallE .. | .lam .. | .letE .. => pure (Format.paren (← term t s.deeper))
    | _ => term t s.deeper
  -- (a chain of arrows stays at one indentation)
  let body ← term b (s.bind id "_" t)
  return Format.group (dom ++ " →" ++ Format.line ++ body)

end

/-- `e` without metadata, which the kernel ignores and the printer does not
print: subterms that differ only in their metadata are then shared as one. -/
partial def stripMData (e : Expr) : Expr :=
  e.replace fun t => if let .mdata _ b := t then some (stripMData b) else none

/-- Print a declaration: its header, type and value (or the text `value?`); and
the top-level definitions of the shared terms it introduces, to come before it. -/
def printDecl (header : String) (type value : Expr) (value? : Option String := none) :
    PrintM (Array String × String) := do
  let type := stripMData type
  let value := if value?.isNone then stripMData value else value
  modify fun st => {st with sharing := {}, lets := {}, anchored := {}, binderNames := {},
                            suffixes := {}}
  -- the sharing of the type and the value
  liftShare do
    countUses type
    if value?.isNone then countUses value
  let st ← get
  -- the `let`s after each binder
  let mut anchored : Std.HashMap Nat (Array Key) := {}
  for k in st.sharing.order do
    if st.sharing.named k && k.binders != 0 then
      anchored := anchored.insert k.anchor ((anchored.getD k.anchor #[]).push k)
  modify fun st => {st with anchored}
  let above := (← read).textAbove
  let typeText := kernelText (← term type {depth := 2}) above 4
  let valueText ← match value? with
    | some v => pure v
    | none => pure (kernelText (← term value {depth := 1}) above 2)
  let pending := (← get).pending
  modify fun st => {st with pending := #[], sharing := {}, lets := {}, anchored := {}}
  return (pending, header ++ " :\n    " ++ typeText ++ " :=\n  " ++ valueText)

end Blaster.Proof.Export
