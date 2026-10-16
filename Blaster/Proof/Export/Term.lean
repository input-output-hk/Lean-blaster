import Lean

/-!
# `kernel% t`: a term exactly as written

`kernel% t` elaborates the term `t` as written: each name to the constant or
local it denotes, each application, binder and `let` to the same kernel term
node, `nat_lit n` to a raw literal and `e.i` to a projection. Nothing is
inferred, inserted or checked (no implicit argument, coercion or unification):
the kernel checks the result, as it checks every declaration. The files that
`blaster.induction.export` writes state their declarations this way, so that
the kernel, not the elaborator, checks their proofs: those can rely on
conversions the elaborator does not try, such as unfolding a matcher applied
to variables.

It accepts the terms `Printer` writes: identifiers (also with `@` and explicit
universes), applications, `fun` and `∀` with typed binders, `→`, `let` and
`have` (a `let` without a type has its value's), `Prop`, `Type`, `Sort`, string
literals, `nat_lit n`, numerals `(n : Nat)`, `(n : Int)` and `(-n : Int)`, and
projections `e.i`; or such a term's text, as a string literal (see "Terms given
as text" below).

A term is built with de Bruijn indices, as the kernel stores it (see `KernelScope`):
reading takes time linear in the size of the term, and a chain of binders and
`let`s (proofs hold chains of thousands) is read in a loop, not by recursion.
-/
namespace Blaster.Proof.Export
open Lean Meta Elab Term

/-- `t` exactly as written (see the module documentation). -/
syntax (name := kernelTerm) "kernel% " term : term

/-- The elaborator of `kernel%`, which Lean reaches without introducing the
implicit binders of the expected type (as it does for most terms). -/
syntax (name := kernelTermCore) "kernel_term% " term : term

macro_rules
  | `(kernel% $t) => `(no_implicit_lambda% (kernel_term% $t))

/-! ## Scopes -/

/-- The binders in scope where a term is read. A name such a binder binds is
read as its bound variable (the term is built with de Bruijn indices), so that
nothing is abstracted when the binders are applied. Each binder also has a
local in `lctx`, with its type and value over the locals before it, for the
types `kernel%` infers: of a `let` without a type, of the structure of a
projection. -/
structure KernelScope where
  /-- The locals of the binders in scope, outermost first. -/
  locals : Array Expr := #[]
  /-- The innermost binder in scope with each name: its position in `locals`. -/
  byName : PersistentHashMap Name Nat := {}
  /-- The position of each local in `locals` (also of binders out of scope). -/
  positions : Std.HashMap FVarId Nat := {}
  /-- The context of the locals: that of the elaboration, extended. -/
  lctx : LocalContext

abbrev KernelM := StateRefT KernelScope TermElabM

/-- A binder of a chain, with its type and value relative to the binders
before it. -/
inductive Link where
  | lam (name : Name) (type : Expr) (info : BinderInfo)
  | pi (name : Name) (type : Expr) (info : BinderInfo)
  | letE (name : Name) (type value : Expr) (nondep : Bool)

/-- `body` under the binder `l`. -/
def Link.bind (l : Link) (body : Expr) : Expr :=
  match l with
  | .lam n t bi => .lam n t body bi
  | .pi n t bi => .forallE n t body bi
  | .letE n t v nondep => .letE n t v body nondep

/-- Bring a binder into scope, with its type and value relative to the scope;
one no name refers to (the binder of an arrow) is not `named`. -/
def pushBinder (name : Name) (type : Expr) (info : BinderInfo := .default)
    (value? : Option Expr := none) (nondep := false) (named := true) : KernelM Unit := do
  let id ← mkFreshFVarId
  modify fun s =>
    let type := type.instantiateRev s.locals
    let lctx := match value? with
      | some value => s.lctx.mkLetDecl id name type (value.instantiateRev s.locals) nondep
      | none => s.lctx.mkLocalDecl id name type info
    let i := s.locals.size
    {s with locals := s.locals.push (.fvar id), lctx, positions := s.positions.insert id i,
            byName := if named then s.byName.insert name i else s.byName}

/-- Leave the binders after the first `size` (`byName` as it was then). -/
def restoreScope (size : Nat) (byName : PersistentHashMap Name Nat) : KernelM Unit :=
  modify fun s => {s with locals := s.locals.shrink size, byName}

/-- `e`, over the locals of the binders in scope, relative to the scope: each
local as the bound variable of its binder. -/
def abstractScoped (s : KernelScope) (e : Expr) : Expr :=
  if !e.hasFVar then e else (go e 0).run' {}
where
  /-- (a subterm that occurs repeatedly is visited once at each depth) -/
  go (e : Expr) (offset : Nat) : StateM (Std.HashMap (Expr × Nat) Expr) Expr := do
    if !e.hasFVar then return e
    if let some r := (← get)[(e, offset)]? then return r
    let r ← match e with
      | .fvar id => pure <| match s.positions[id]? with
        | some i => if s.locals[i]? == some e then .bvar (offset + s.locals.size - 1 - i) else e
        | none => e
      | .app f a => pure (e.updateApp! (← go f offset) (← go a offset))
      | .lam _ t b _ => pure (e.updateLambdaE! (← go t offset) (← go b (offset + 1)))
      | .forallE _ t b _ => pure (e.updateForallE! (← go t offset) (← go b (offset + 1)))
      | .letE _ t v b _ => pure (e.updateLetE! (← go t offset) (← go v offset) (← go b (offset + 1)))
      | .mdata _ b => pure (e.updateMData! (← go b offset))
      | .proj _ _ b => pure (e.updateProj! (← go b offset))
      | _ => pure e
    modify (·.insert (e, offset) r)
    return r

/-- The type of `e` (relative to the scope), relative to the scope. -/
def inferScoped (e : Expr) : KernelM Expr := do
  let s ← get
  let type ← withLCtx s.lctx {} (inferType (e.instantiateRev s.locals))
  return abstractScoped s type

/-- The structure of the type of `e` (relative to the scope): what `e.i` projects. -/
def structureOf (e : Expr) : KernelM Name := do
  let s ← get
  let type ← withLCtx s.lctx {} do whnf (← inferType (e.instantiateRev s.locals))
  let .const name _ := type.getAppFn
    | throwError "kernel%: a projection of a term whose type is not a structure"
  return name

/-- The local `n` denotes, or the constant `resolve` finds, at universe
`levels`. A local is a binder in scope, else one of the elaboration around
the `kernel%` term. -/
def identifier (n : Name) (levels : List Level) (resolve : TermElabM Name) : KernelM Expr := do
  if levels.isEmpty then
    let s ← get
    if let some i := s.byName.find? n then return .bvar (s.locals.size - 1 - i)
    if let some d := (← getLCtx).findFromUserName? n then return d.toExpr
  let c ← resolve
  let info ← getConstInfo c
  unless info.levelParams.length == levels.length do
    throwError "kernel%: `{c}` needs {info.levelParams.length} universe levels"
  return mkConst c levels

/-- The numeral `(n : type)`, or `(-n : type)`, as Lean elaborates those of
`Nat` and `Int`. -/
def numeral (type : Name) (n : Nat) (negative : Bool) : MetaM Expr := do
  if type == `Nat && !negative then return mkNatLit n
  unless type == `Int do throwError "kernel%: unsupported numeral type {type}"
  let int := mkApp3 (mkConst ``OfNat.ofNat [levelZero]) (mkConst ``Int) (mkRawNatLit n)
    (mkApp (mkConst ``instOfNat) (mkRawNatLit n))
  if negative then return mkApp3 (mkConst ``Neg.neg [levelZero]) (mkConst ``Int) (mkConst ``Int.instNegInt) int
  return int

/-! ## Terms given as syntax -/

/-- A binder of `fun` or `∀`: its names, type syntax and kind. -/
def binderParts (stx : Syntax) : Option (Array Syntax × Syntax × BinderInfo) :=
  let k := stx.getKind
  if k == ``Parser.Term.typeAscription then
    -- `(x : T)` in a `fun`
    some (#[stx[1]], stx[3][0], .default)
  else if k == ``Parser.Term.explicitBinder then some (stx[1].getArgs, stx[2][1], .default)
  else if k == ``Parser.Term.implicitBinder then some (stx[1].getArgs, stx[2][1], .implicit)
  else if k == ``Parser.Term.strictImplicitBinder then some (stx[1].getArgs, stx[2][1], .strictImplicit)
  else if k == ``Parser.Term.instBinder then some (#[stx[1][0]], stx[2], .instImplicit)
  else none

mutual

/-- The kernel term `stx` denotes, exactly: a chain of `fun` and `∀` binders,
`let`s, `have`s and arrows, read in a loop, then the term they bind. -/
partial def kernelExpr (stx : Syntax) : KernelM Expr := do
  let size := (← get).locals.size
  let byName := (← get).byName
  let mut links : Array Link := #[]
  let mut stx := stx
  repeat
    let k := stx.getKind
    if k == ``Parser.Term.fun then
      links ← kernelBinders links stx[1][0].getArgs true
      stx := stx[1][3]
    else if k == ``Parser.Term.forall then
      links ← kernelBinders links stx[1].getArgs false
      stx := stx[4]
    else if k == ``Parser.Term.arrow then
      let type ← kernelExpr stx[0]
      -- (its binder: no name refers to it)
      pushBinder `a type (named := false)
      links := links.push (.pi `a type .default)
      stx := stx[2]
    else if k == ``Parser.Term.let || k == ``Parser.Term.have then
      links := links.push (← kernelLet stx (k == ``Parser.Term.have))
      stx := stx[4]
    else break
  let body ← kernelAtom stx
  restoreScope size byName
  return links.foldr Link.bind body

/-- The binders of a `fun` (`lam`) or `∀`, brought into scope after `links`. -/
partial def kernelBinders (links : Array Link) (binders : Array Syntax) (lam : Bool) :
    KernelM (Array Link) := do
  let mut links := links
  for binder in binders do
    let some (names, typeStx, info) := binderParts binder
      | withRef binder do throwError "kernel%: unsupported binder"
    let type ← kernelExpr typeStx
    for (name, i) in names.zipIdx do
      -- (the type of each name lies under the names before it)
      let type := type.liftLooseBVars 0 i
      pushBinder name.getId type info
      links := links.push (if lam then .lam name.getId type info else .pi name.getId type info)
  return links

/-- `let x : T := v; …` or `have …`: its binder, brought into scope (a
missing type is the value's). -/
partial def kernelLet (stx : Syntax) (nondep : Bool) : KernelM Link := withRef stx do
  let decl := stx[2][0]
  unless decl.isOfKind ``Parser.Term.letIdDecl && decl[1].getNumArgs == 0 do
    throwError "kernel%: unsupported local definition"
  let name := decl[0][0].getId
  let value ← kernelExpr decl[4]
  let type ← match decl[2].getArgs[0]? with
    | some spec => kernelExpr spec[1]
    | none => inferScoped value
  pushBinder name type (value? := some value) (nondep := nondep)
  return .letE name type value nondep

/-- A term that binds nothing: an identifier, application, projection, sort,
literal or numeral (or a parenthesized term). -/
partial def kernelAtom (stx : Syntax) : KernelM Expr := withRef stx do
  if stx.isIdent then return ← identifier stx.getId [] (realizeGlobalConstNoOverload stx)
  if let some s := stx.isStrLit? then return mkStrLit s
  let k := stx.getKind
  if k == ``Parser.Term.paren || k == ``Parser.Term.explicit then kernelExpr stx[1]
  else if k == ``Parser.Term.explicitUniv then
    identifier stx[0].getId (← stx[2].getSepArgs.toList.mapM fun l => do elabLevel l)
      (realizeGlobalConstNoOverload stx[0])
  else if k == ``Parser.Term.app then
    return mkAppN (← kernelExpr stx[0]) (← stx[1].getArgs.mapM kernelExpr)
  else if k == ``Parser.Term.proj then
    let e ← kernelExpr stx[0]
    let some i := stx[2].isFieldIdx? | throwError "kernel%: unsupported projection"
    return .proj (← structureOf e) (i - 1) e
  else if k == ``Parser.Term.prop then return mkSort .zero
  else if k == ``Parser.Term.type then
    match stx[1].getArgs[0]? with
    | some l => return mkSort (.succ (← elabLevel l))
    | none => return mkSort levelOne
  else if k == ``Parser.Term.sort then
    match stx[1].getArgs[0]? with
    | some l => return mkSort (← elabLevel l)
    | none => return mkSort .zero
  else if k == `rawNatLit then
    let some n := stx[1].isNatLit? | throwError "kernel%: unsupported literal"
    return mkRawNatLit n
  else if k == ``Parser.Term.typeAscription && stx[3][0].isIdent then
    -- a numeral `(n : Nat)`, `(n : Int)` or `(-n : Int)`
    let (negative, literal) := if stx[1].isOfKind ``«term-_» then (true, stx[1][1]) else (false, stx[1])
    let some n := literal.isNatLit? | throwError "kernel%: unsupported numeral"
    numeral stx[3][0].getId n negative
  else throwError "kernel%: unsupported syntax {stx}"

end

/-! ## Terms given as text

Lean's parser takes time quadratic in the size of a command, so a very large
term is given to `kernel%` as a string literal (`kernel% r#"…"#`) holding the
same text, which `readKernel` reads in linear time: the terms `Printer` writes
need no backtracking. -/

/-- A token of a term given as text. -/
inductive Token where
  | ident (n : Name)
  | num (n : Nat)
  | str (s : String)
  /-- `.n` after a term: a projection. -/
  | field (n : Nat)
  | sym (s : String)
  deriving BEq, Inhabited

/-- The tokens of `s`. -/
partial def tokens (s : String) : Except String (Array Token) := do
  let mut out := #[]
  let mut it := s.iter
  while !it.atEnd do
    let c := it.curr
    if c.isWhitespace then it := it.next; continue
    if c.isDigit then
      let (n, it') := number it 0
      out := out.push (.num n)
      it := it'
    else if c == '"' then
      let start := it.pos
      it := it.next
      while !it.atEnd && it.curr != '"' do
        it := if it.curr == '\\' then it.next.next else it.next
      it := it.next
      let some lit := Lean.Syntax.decodeStrLit (s.extract start it.pos) | throw "invalid string literal"
      out := out.push (.str lit)
    else if c == '.' && it.next.curr.isDigit then
      let (n, it') := number it.next 0
      out := out.push (.field n)
      it := it'
    else if c == '.' && it.next.curr == '{' then
      out := out.push (.sym ".{")
      it := it.next.next
    else if isIdFirst c || c == '«' then
      let (n, it') ← ident it .anonymous
      out := out.push (.ident n)
      it := it'
    else
      let two := s!"{c}{it.next.curr}"
      if two == ":=" || two == "=>" then
        out := out.push (.sym two)
        it := it.next.next
      else
        out := out.push (.sym c.toString)
        it := it.next
  return out
where
  number (it : String.Iterator) (n : Nat) : Nat × String.Iterator :=
    if !it.atEnd && it.curr.isDigit then number it.next (10 * n + (it.curr.toNat - '0'.toNat)) else (n, it)
  /-- A dotted identifier: its components, escaped (`«…»`) or not. -/
  ident (it : String.Iterator) (acc : Name) : Except String (Name × String.Iterator) := do
    let (part, it) ← if it.curr == '«' then
        let start := it.next
        let mut j := start
        while !j.atEnd && j.curr != '»' do j := j.next
        pure (start.extract j, j.next)
      else
        let start := it
        let mut j := it
        while !j.atEnd && isIdRest j.curr do j := j.next
        pure (start.extract j, j)
    let acc := Name.str acc part
    -- (a dot continues the name when a component follows it)
    if !it.atEnd && it.curr == '.' && (isIdFirst it.next.curr || it.next.curr == '«') then
      ident it.next acc
    else return (acc, it)

/-- The reader of a term given as text: the tokens, the position and the scope. -/
abbrev ReadM := ReaderT (Array Token) (StateRefT Nat KernelM)

/-- The next token, if any. -/
def peek : ReadM (Option Token) := do return (← read)[← get]?

/-- Move past the next token. -/
def advance : ReadM Unit := modify (· + 1)

/-- Skip the symbol `s`, which must come next. -/
def expect (s : String) : ReadM Unit := do
  unless (← peek) == some (.sym s) do throwError "kernel%: expected `{s}`"
  advance

/-- Whether `t` is a keyword the reader knows. -/
def isKeyword (t : Option Token) : Bool :=
  match t with
  | some (.ident n) => n == `fun || n == `let || n == `have || n == `nat_lit
  | _ => false

mutual

/-- A term: a chain of `fun` and `∀` binders, `let`s, `have`s and arrows,
read in a loop, then the term they bind. -/
partial def readTerm : ReadM Expr := do
  let size := (← getThe KernelScope).locals.size
  let byName := (← getThe KernelScope).byName
  let mut links : Array Link := #[]
  let mut body : Expr := default
  repeat
    match ← peek with
    | some (.ident `fun) => advance; links ← readBinders links true
    | some (.sym "∀") => advance; links ← readBinders links false
    | some (.ident `let) => advance; links := links.push (← readLet false)
    | some (.ident `have) => advance; links := links.push (← readLet true)
    | _ =>
      let e ← readApp
      unless (← peek) == some (.sym "→") do
        body := e
        break
      advance
      -- (the binder of an arrow: no name refers to it)
      pushBinder `a e (named := false)
      links := links.push (.pi `a e .default)
  restoreScope size byName
  return links.foldr Link.bind body

/-- After `fun` or `∀`: binders `(x : T)`, `{x : T}`, `[x : T]`, `⦃x : T⦄`,
each brought into scope after `links`, then `=>` or `,`. -/
partial def readBinders (links : Array Link) (lam : Bool) : ReadM (Array Link) := do
  let mut links := links
  repeat
    let (close, info) ← match ← peek with
      | some (.sym "(") => pure (")", BinderInfo.default)
      | some (.sym "{") => pure ("}", .implicit)
      | some (.sym "[") => pure ("]", .instImplicit)
      | some (.sym "⦃") => pure ("⦄", .strictImplicit)
      | _ => break
    advance
    let some (.ident name) ← peek | throwError "kernel%: expected a binder name"
    advance
    expect ":"
    let type ← readTerm
    expect close
    pushBinder name type info
    links := links.push (if lam then .lam name type info else .pi name type info)
  expect (if lam then "=>" else ",")
  return links

/-- After `let` or `have`: `x : T := v;` (the type may be omitted, then it is
the value's), brought into scope. -/
partial def readLet (nondep : Bool) : ReadM Link := do
  let some (.ident name) ← peek | throwError "kernel%: expected a name"
  advance
  let type? ← if (← peek) == some (.sym ":") then advance; some <$> readTerm else pure none
  expect ":="
  let value ← readTerm
  expect ";"
  let type ← match type? with
    | some type => pure type
    | none => inferScoped value
  pushBinder name type (value? := some value) (nondep := nondep)
  return .letE name type value nondep

/-- An application: atoms. -/
partial def readApp : ReadM Expr := do
  let mut e ← readAtom
  repeat
    if !(← startsAtom) then break
    e := mkApp e (← readAtom (argument := true))
  return e

/-- Whether an atom starts at the next token. -/
partial def startsAtom : ReadM Bool := do
  let t ← peek
  if isKeyword t && t != some (.ident `nat_lit) then return false
  return match t with
    | some (.ident _) | some (.str _) | some (.sym "@") | some (.sym "(") => true
    | _ => false

/-- An atom, and the projections after it. A universe level follows `Type`
only outside arguments (an argument `Type u` is parenthesized). -/
partial def readAtom (argument := false) : ReadM Expr := do
  let e ← match ← peek with
    | some (.sym "@") => advance; readAtom argument
    | some (.sym "(") => advance; readParen
    | some (.str s) => advance; pure (mkStrLit s)
    | some (.ident `nat_lit) =>
      advance
      let some (.num n) ← peek | throwError "kernel%: expected a literal"
      advance
      pure (mkRawNatLit n)
    | some (.ident `Prop) => advance; pure (mkSort .zero)
    | some (.ident `Type) =>
      advance
      if !argument && (← startsLevel) then pure (mkSort (.succ (← readLevelAtom)))
      else pure (mkSort levelOne)
    | some (.ident `Sort) => advance; pure (mkSort (← readLevelAtom))
    | some (.ident n) =>
      advance
      let levels ← if (← peek) == some (.sym ".{") then advance; readLevels else pure []
      identifier n levels (realizeGlobalConstNoOverloadCore n)
    | _ => throwError "kernel%: unexpected token"
  projections e
where
  projections (e : Expr) : ReadM Expr := do
    let mut e := e
    repeat
      let some (.field i) ← peek | break
      advance
      e := .proj (← structureOf e) (i - 1) e
    return e

/-- After `(`: a numeral `(n : Nat)`, `(n : Int)` or `(-n : Int)`, or a term. -/
partial def readParen : ReadM Expr := do
  let toks ← read
  let i ← get
  let numeral? : Option (Bool × Nat × Name) := match toks[i]?, toks[i+1]?, toks[i+2]?, toks[i+3]?, toks[i+4]? with
    | some (.num n), some (.sym ":"), some (.ident t), some (.sym ")"), _ => some (false, n, t)
    | some (.sym "-"), some (.num n), some (.sym ":"), some (.ident t), some (.sym ")") => some (true, n, t)
    | _, _, _, _, _ => none
  if let some (negative, n, type) := numeral? then
    set (i + if negative then 5 else 4)
    return ← numeral type n negative
  let e ← readTerm
  expect ")"
  return e

/-- Whether a universe level starts at the next token. -/
partial def startsLevel : ReadM Bool := do
  return match ← peek with
    | some (.num _) | some (.sym "(") => true
    | some (.ident n) => n != `fun && n != `let && n != `have
    | _ => false

/-- `.{l, …}` after `.{`. -/
partial def readLevels : ReadM (List Level) := do
  let mut ls := #[]
  repeat
    ls := ls.push (← readLevel)
    if (← peek) == some (.sym ",") then advance else break
  expect "}"
  return ls.toList

/-- A universe level: `max a b`, `imax a b`, or an atom, possibly `+ k`. -/
partial def readLevel : ReadM Level := do
  let l ← match ← peek with
    | some (.ident `max) => advance; pure (Level.max (← readLevelAtom) (← readLevelAtom))
    | some (.ident `imax) => advance; pure (Level.imax (← readLevelAtom) (← readLevelAtom))
    | _ => readLevelAtom
  if (← peek) == some (.sym "+") then
    advance
    let some (.num k) ← peek | throwError "kernel%: expected a number"
    advance
    return l.addOffset k
  return l

/-- A universe level that is a numeral, a parameter or parenthesized. -/
partial def readLevelAtom : ReadM Level := do
  match ← peek with
  | some (.num n) => advance; return Level.ofNat n
  | some (.ident n) => advance; return .param n
  | some (.sym "(") => advance; let l ← readLevel; expect ")"; return l
  | _ => throwError "kernel%: expected a universe level"

end

/-- The term `text` denotes (the syntax `kernelExpr` reads, given as text). -/
def readKernel (text : String) : KernelM Expr := do
  let toks ← match tokens text with
    | .ok toks => pure toks
    | .error msg => throwError "kernel%: {msg}"
  let (e, i) ← (readTerm.run toks).run 0
  unless i == toks.size do throwError "kernel%: unexpected text after the term"
  return e

/-- A proof is given its expected type by a hint (`id`): the elaborator then
has nothing to check, and the kernel checks the proof against the type. -/
@[term_elab kernelTermCore] def elabKernelTerm : TermElab := fun stx expectedType? => do
  let read := match stx[1].isStrLit? with
    | some text => readKernel text
    | none => kernelExpr stx[1]
  let e ← read.run' {lctx := ← getLCtx}
  let some type := expectedType? | return e
  let type := (← instantiateMVars type).consumeMData
  if type.hasMVar || !(← isProp type) then return e
  mkExpectedTypeHint e type

end Blaster.Proof.Export
