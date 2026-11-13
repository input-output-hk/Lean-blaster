import Blaster.Reconstruct.SmtProof.IR

/-!
# Z3 proofs

Adapter for Z3's (legacy) proof objects, as printed by `(get-proof)` with `:produce-proofs true`.
A proof is a term whose applications of proof rules have their premises as first arguments and
their conclusion as last argument, e.g., `(mp p₁ p₂ φ)`. Rule arguments are given as indices, e.g.,
`((_ quant-inst t₁ t₂) φ)` or `((_ th-lemma arith farkas 1 1) p₁ p₂ φ)`.
-/

namespace Blaster.Reconstruct.SmtProof.Z3

/-- Proof rules of Z3 (see `Z3_decl_kind` in Z3's API). -/
def proofRules : Std.HashSet String := Std.HashSet.ofList [
  "true-axiom", "asserted", "goal", "mp", "refl", "symm", "trans", "trans*", "monotonicity",
  "quant-intro", "bind", "distributivity", "and-elim", "not-or-elim", "rewrite", "rewrite*",
  "pull-quant", "pull-quant*", "push-quant", "elim-unused", "der", "quant-inst", "hypothesis",
  "lemma", "unit-resolution", "iff-true", "iff-false", "commutativity", "def-axiom",
  "assumption-add", "lemma-add", "redundant-del", "clause-trail", "def-intro", "intro-def", "apply-def",
  "iff~", "nnf-pos", "nnf-neg", "nnf*", "cnf*", "sk", "mp~", "th-lemma", "hyper-res",
  "proof-bind"]

def isProofTerm (t : STerm) : Bool :=
  match t with
  | .app f _ | .iapp f _ _ => proofRules.contains f
  | _ => false

structure ConvState where
  steps : Array Step := #[]
  cache : TermCache Nat := {}

abbrev ConvM := StateT ConvState (Except String)

/-- Convert the proof term `t` to steps, returning the index of the step concluding `t`. -/
partial def convert (t : STerm) : ConvM Nat := do
  let addr := termAddr t
  if let some i := (← get).cache.get? addr then return i
  let (rule, idx, args) ← match t with
    | .app f args => pure (f, #[], args)
    | .iapp f idx args => pure (f, idx, args)
    | _ => throw s!"proof term expected: {t}"
  if !proofRules.contains rule then throw s!"unknown proof rule: {rule}"
  let step ← do
    if rule == "proof-bind" then
      -- `(proof-bind (lambda (vars) p))`: proof of the body of a quantifier rewrite (see `quant-intro`);
      -- the conclusion is the conclusion of `p` (with free variables).
      let some (STerm.quant .lambda vars p) := args[0]? | throw s!"ill-formed proof-bind: {t}"
      let i ← convert p
      let c := (← get).steps[i]!.concl
      pure { rule, premises := #[i], concl := .quant .lambda vars c : Step }
    else
      if args.isEmpty then throw s!"proof rule without conclusion: {t}"
      let concl := args.back!
      let mut premises := #[]
      let mut targs := #[]
      for a in args.pop do
        if isProofTerm a then premises := premises.push (← convert a)
        else targs := targs.push a
      -- indexed arguments that are terms (e.g., the instantiation of `quant-inst`)
      let mut attrs := #[]
      if rule == "quant-inst" then targs := targs ++ idx
      else attrs := idx.map STerm.toSExpr
      pure { rule, premises, args := targs, attrs, concl : Step }
  modify fun s => { s with steps := s.steps.push step }
  let i := (← get).steps.size - 1
  modify fun s => { s with cache := s.cache.insert addr i }
  return i

/-- The proof term `p` of the first `(proof p)` occurring in `e` (at most at depth `depth`, e.g., in a list wrapping
    the proof: the proof terms may be deeply nested). -/
def findProof? (e : SExpr) (depth := 4) : Option SExpr :=
  match e, depth with
  | .list #[.atom "proof", x], _ => some x
  | .list xs, depth + 1 => xs.findSome? (findProof? · depth)
  | _, _ => none

/-- Sorted variables `((x S) ...)`. -/
def sortedVars (e : SExpr) : Except String (Array (String × SExpr)) := do
  let some vs := e.list? | throw s!"ill-formed parameters: {e}"
  vs.mapM fun v => match v with
    | .list #[.atom x, s] => pure (x, s)
    | _ => throw s!"ill-formed sorted variable: {v}"

/-- Function definitions of the proof output: `(define-funs-rec ((f params sort) ...) (body ...))`,
    `(define-fun-rec f params sort body)` and `(define-fun f params sort body)`, at the top level or in the
    list wrapping the proof (e.g., the recursive functions of the query and Z3's auxiliary `fold-rec-n`
    functions, which name subterms of their bodies). -/
def parseDefs (es : Array SExpr) : Except String (Array FunDef) := do
  let items := es.foldl (fun acc e => match e with
    | .list xs => if (xs[0]?.bind SExpr.list?).isSome then acc ++ xs else acc.push e
    | e => acc.push e) #[]
  let mut defs := #[]
  for c in items do
    match c with
    | .list #[.atom "define-funs-rec", .list decls, .list bodies] =>
        for (d, b) in decls.zip bodies do
          let .list #[.atom f, ps, s] := d | throw s!"ill-formed declaration: {d}"
          defs := defs.push { name := f, params := ← sortedVars ps, sort := s, body := ← STerm.ofSExpr {} b }
    | .list #[.atom "define-fun-rec", .atom f, ps, s, b] | .list #[.atom "define-fun", .atom f, ps, s, b] =>
        defs := defs.push { name := f, params := ← sortedVars ps, sort := s, body := ← STerm.ofSExpr {} b }
    | _ => pure ()
  return defs

/-- Parse the output of `(get-proof)`, e.g., `((proof p))` or `(proof p)` or `p`. -/
def parseProof (out : String) : Except String Proof := do
  let es ← parseSExprs out
  -- the proof term `(proof p)`, possibly preceded by declarations (e.g., skolem constants,
  -- `define-funs-rec` of recursive functions) and wrapped in a list
  let some p := es.findSome? findProof? <|> (es.back?.bind fun e => match e with
      | .list #[x] => some x
      | e => some e)
    | throw "empty proof output"
  let pt ← STerm.ofSExpr {} p
  let (root, st) ← (convert pt).run {}
  -- NOTE: definitions that can't be parsed are ignored (their symbols are then unknown to the replay)
  let defs := (parseDefs es).toOption.getD #[]
  return { backend := "z3", steps := st.steps, root, defs }

end Blaster.Reconstruct.SmtProof.Z3
