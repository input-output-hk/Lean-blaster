import Lean

/-!
# Propositional reasoning with proof terms

A small refutation procedure used to replay propositional steps of SMT proofs (e.g., Z3's `def-axiom`,
`not-or-elim`, `and-elim`, propositional rewrites, resolution with non-unit literals). Facts (propositions
with proofs) are saturated with unit rules on `¬`, `∧`, `∨`, `→`, `ite` over propositions and equality of
propositions, until a contradiction is found. Atoms are kept opaque, such that the procedure doesn't depend
on the theory of the atoms. No case split is performed (Tseitin axioms are refuted by unit propagation).
-/

open Lean Meta

namespace Blaster.Reconstruct.SmtProof.PropEngine

structure State where
  /-- proved propositions -/
  facts : Std.HashMap Expr Expr := {}
  /-- facts to process -/
  todo : Array Expr := #[]
  conflict : Option Expr := none

abbrev M := StateRefT State MetaM

def isProp' (e : Expr) : MetaM Bool := do
  try isProp e catch _ => return false

/-- Add fact `t` with proof `p`, detecting conflicts with `¬ t` (or `t = ¬ a` with `a`). -/
def addFact (t p : Expr) : M Unit := do
  let s ← get
  if s.conflict.isSome || s.facts.contains t then return
  if t.isConstOf ``False then
    modify fun s => { s with conflict := some p }
    return
  if let some a := t.not? then
    if let some pa := s.facts.get? a then
      modify fun s => { s with conflict := some (mkApp p pa) }
      return
  if let some pn := s.facts.get? (mkNot t) then
    modify fun s => { s with conflict := some (mkApp pn p) }
    return
  modify fun s => { s with facts := s.facts.insert t p, todo := s.todo.push t }

def get? (t : Expr) : M (Option Expr) := return (← get).facts.get? t

/-- `fun h : t => b h` built under the binder: `b` places its argument as is (a loose bound variable), the other
    subterms of its result having no loose bound variables (e.g., terms over the local hypotheses of the engine), such
    that the proofs of the facts are not traversed again by an abstraction at each derivation (quadratic in the length
    of the derivations, e.g., on the clauses of CEK evaluations). -/
@[inline] def lam1 (n : Name) (t : Expr) (b : Expr → Expr) : Expr := .lam n t (b (.bvar 0)) .default

/-- Proof of `¬ t` if known (as `¬ t`, or `t := ¬ a` with `a` known). -/
def getNeg? (t : Expr) : M (Option Expr) := do
  if let some p ← get? (mkNot t) then return some p
  if let some a := t.not? then
    if let some pa ← get? a then
      return some (lam1 `h t fun h => mkApp h pa)
  return none

/-- `propext (Iff.intro ab ba) : a = b`. -/
def mkPropext (a b ab ba : Expr) : Expr :=
  mkApp3 (mkConst ``propext) a b (mkApp4 (mkConst ``Iff.intro) a b ab ba)

/-- `Classical.byContradiction (fun h : ¬ t => k h)` (see `lam1`). -/
def byContra (t : Expr) (k : Expr → Expr) : Expr :=
  mkApp2 (mkConst ``Classical.byContradiction) t (lam1 `h (mkNot t) k)

/-- Derive the consequences of fact `t` (with proof `p`) and of the facts it unlocks. -/
def process (t p : Expr) : M Unit := do
  -- ¬¬a
  if let some na := t.not? then
    if let some a := na.not? then
      addFact a (byContra a fun h => mkApp p h)
    -- ¬(a ∧ b)
    if let some (a, b) := na.and? then
      if let some pa ← get? a then
        addFact (mkNot b) (lam1 `h b fun h => mkApp p (mkApp4 (mkConst ``And.intro) a b pa h))
      if let some pb ← get? b then
        addFact (mkNot a) (lam1 `h a fun h => mkApp p (mkApp4 (mkConst ``And.intro) a b h pb))
    -- ¬(a ∨ b)
    if let some (a, b) := na.app2? ``Or then
      addFact (mkNot a) (lam1 `h a fun h => mkApp p (mkApp3 (mkConst ``Or.inl) a b h))
      addFact (mkNot b) (lam1 `h b fun h => mkApp p (mkApp3 (mkConst ``Or.inr) a b h))
    -- ¬(a → b)
    if na.isArrow then
      let a := na.bindingDomain!
      let b := na.bindingBody!
      if (← isProp' a) && !b.hasLooseBVars then
        addFact a (byContra a fun hna =>
          mkApp p (lam1 `ha a fun ha =>
            mkApp2 (mkConst ``False.elim [levelZero]) b (mkApp (hna.liftLooseBVars 0 1) ha)))
        addFact (mkNot b) (lam1 `hb b fun hb => mkApp p (lam1 `ha a fun _ => hb.liftLooseBVars 0 1))
    -- ¬(ite c a b) (propositions) with `c` (resp. `¬ c`) known: ¬a (resp. ¬b)
    if na.isAppOfArity ``ite 5 && (na.getArg! 0).isProp then
      let args := na.getAppArgs
      let (c, a, b) := (args[1]!, args[3]!, args[4]!)
      if let some pc ← get? c then
        let eq ← mkAppOptM ``if_pos #[c, args[2]!, pc, none, a, b]
        -- `eq : ite c a b = a`
        addFact (mkNot a) (lam1 `ha a fun ha => mkApp p (mkApp4 (mkConst ``Eq.mpr [levelZero]) na a eq ha))
      if let some nc ← getNeg? c then
        let eq ← mkAppOptM ``if_neg #[c, args[2]!, nc, none, a, b]
        addFact (mkNot b) (lam1 `hb b fun hb => mkApp p (mkApp4 (mkConst ``Eq.mpr [levelZero]) na b eq hb))
    -- ¬(ite c a b = t) with `c` (resp. `¬ c`) known and `t` syntactically `a` (resp. `b`)
    if let some (_, x, y) := na.eq? then
      for (it, other, flip) in [(x, y, false), (y, x, true)] do
        if it.isAppOfArity ``ite 5 then
          let args := it.getAppArgs
          let (c, a, b) := (args[1]!, args[3]!, args[4]!)
          let mut eq? : Option Expr := none
          if other == a then
            if let some pc ← get? c then eq? := some (← mkAppOptM ``if_pos #[c, args[2]!, pc, args[0]!, a, b])
          if other == b && eq?.isNone then
            if let some nc ← getNeg? c then eq? := some (← mkAppOptM ``if_neg #[c, args[2]!, nc, args[0]!, a, b])
          if let some e := eq? then
            let e ← if flip then mkEqSymm e else pure e
            modify fun st => if st.conflict.isNone then { st with conflict := some (mkApp p e) } else st
            return
    -- ¬(a = b) for propositions
    if let some (ty, a, b) := na.eq? then
      if ty.isProp then
        if let some pa ← get? a then
          -- b → (a = b)
          let nb := lam1 `hb b fun hb =>
            mkApp p (mkPropext a b (lam1 `x a fun _ => hb.liftLooseBVars 0 1) (lam1 `x b fun _ => pa))
          addFact (mkNot b) nb
        if let some pna ← getNeg? a then
          -- ¬ b → (a = b)
          let pb := byContra b fun hnb =>
            let ab := lam1 `x a fun x => mkApp2 (mkConst ``False.elim [levelZero]) b (mkApp pna x)
            let ba := lam1 `x b fun x => mkApp2 (mkConst ``False.elim [levelZero]) a (mkApp (hnb.liftLooseBVars 0 1) x)
            mkApp p (mkPropext a b ab ba)
          addFact b pb
    return
  -- a ∧ b
  if let some (a, b) := t.and? then
    addFact a (mkApp3 (mkConst ``And.left) a b p)
    addFact b (mkApp3 (mkConst ``And.right) a b p)
    return
  -- a ∨ b
  if let some (a, b) := t.app2? ``Or then
    if let some na ← getNeg? a then addFact b (← mkAppM ``Or.resolve_left #[p, na])
    if let some nb ← getNeg? b then addFact a (← mkAppM ``Or.resolve_right #[p, nb])
    return
  -- a → b
  if t.isArrow then
    let a := t.bindingDomain!
    let b := t.bindingBody!
    if (← isProp' a) && !b.hasLooseBVars then
      if let some pa ← get? a then addFact b (mkApp p pa)
      if let some nb ← getNeg? b then
        addFact (mkNot a) (lam1 `h a fun h => mkApp nb (mkApp p h))
    return
  -- ite c a b (propositions)
  if t.isAppOfArity ``ite 5 then
    let args := t.getAppArgs
    let (c, a, b) := (args[1]!, args[3]!, args[4]!)
    if let some pc ← get? c then
      addFact a (← mkEqMP (← mkAppOptM ``if_pos #[c, args[2]!, pc, none, a, b]) p)
    if let some nc ← getNeg? c then
      addFact b (← mkEqMP (← mkAppOptM ``if_neg #[c, args[2]!, nc, none, a, b]) p)
    return
  -- a = b (propositions)
  if let some (ty, a, b) := t.eq? then
    if ty.isProp then
      if let some pa ← get? a then addFact b (← mkEqMP p pa)
      if let some pb ← get? b then addFact a (← mkEqMPR p pb)
      if let some na ← getNeg? a then
        -- `p : a = b`
        addFact (mkNot b) (lam1 `h b fun h => mkApp na (mkApp4 (mkConst ``Eq.mpr [levelZero]) a b p h))
      if let some nb ← getNeg? b then
        addFact (mkNot a) (lam1 `h a fun h => mkApp nb (mkApp4 (mkConst ``Eq.mp [levelZero]) a b p h))

/-- Saturate the facts until a conflict is found (at most `fuel` rounds).
    NOTE: a round decomposes one level of the nested connectives (e.g., the literals of wide clauses `l₁ ∨ ... ∨ lₙ`
    need `n` rounds); the saturation stops when a round derives no new fact. -/
partial def saturate (fuel : Nat := 64) : M (Option Expr) := do
  for _ in [0:fuel] do
    if let some c := (← get).conflict then return some c
    let todo := (← get).todo
    if todo.isEmpty then
      -- facts may unlock rules on facts processed earlier: process all facts again
      let facts := (← get).facts.toArray
      let before := (← get).facts.size
      for (t, p) in facts do
        process t p
        if (← get).conflict.isSome then break
      if (← get).facts.size == before && (← get).todo.isEmpty then break
      continue
    modify fun s => { s with todo := #[] }
    for t in todo do
      if let some p := (← get).facts.get? t then process t p
      if (← get).conflict.isSome then break
  return (← get).conflict

/-- Conditions of the `ite` on propositions occurring in `e` that are not known in the facts (candidates for a
    case split). -/
partial def iteConds (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if e.isAppOfArity ``ite 5 && (e.getArg! 0).isProp then
    let c := e.getArg! 1
    iteConds (e.getArg! 4) (iteConds (e.getArg! 3) (if acc.contains c then acc else acc.push c))
  else if e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 || e.isAppOfArity ``Iff 2 then
    iteConds e.appArg! (iteConds e.appFn!.appArg! acc)
  else if e.isAppOfArity ``Not 1 then iteConds e.appArg! acc
  else if e.isAppOfArity ``Eq 3 && (e.getArg! 0).isProp then iteConds e.appArg! (iteConds e.appFn!.appArg! acc)
  else match e with
    | .forallE _ t b _ => if b.hasLooseBVars then acc else iteConds b (iteConds t acc)
    | _ => acc

/-- Prove `goal` from `hyps` (propositions and proofs) by refutation, or return `none`. Propositional
    equalities in the goal are proved with `propext` from both implications. When unit propagation does not
    find a contradiction, the conditions of `ite` on propositions are split (at most `splits` times). -/
partial def prove (hyps : Array (Expr × Expr)) (goal : Expr) (splits := 2) : MetaM (Option Expr) := do
  -- `a = b` between propositions: both directions
  if let some (ty, a, b) := goal.eq? then
    if ty.isProp then
      let some ab ← withLocalDeclD `h a fun h => do
          match ← prove (hyps.push (a, h)) b splits with
          | some p => some <$> mkLambdaFVars #[h] p
          | none => pure none
        | return none
      let some ba ← withLocalDeclD `h b fun h => do
          match ← prove (hyps.push (b, h)) a splits with
          | some p => some <$> mkLambdaFVars #[h] p
          | none => pure none
        | return none
      return some (mkPropext a b ab ba)
  let r ← withLocalDeclD `hn (mkNot goal) fun hn => do
    let act : M (Option Expr) := do
      addFact (mkConst ``True) (mkConst ``True.intro)
      for (t, p) in hyps do addFact t p
      addFact (mkNot goal) hn
      saturate
    let (c?, _) ← act.run {}
    match c? with
    | some c => some <$> mkLambdaFVars #[hn] c
    | none => pure none
  if let some r := r then return some (mkApp2 (mkConst ``Classical.byContradiction) goal r)
  if splits == 0 then return none
  -- case split on a condition of an `ite`
  let conds := hyps.foldl (fun acc (t, _) => iteConds t acc) (iteConds goal)
  for c in conds.extract 0 2 do
    let pos ← withLocalDeclD `hc c fun hc => do
      match ← prove (hyps.push (c, hc)) goal (splits - 1) with
      | some p => some <$> mkLambdaFVars #[hc] p
      | none => pure none
    let some pos := pos | continue
    let neg ← withLocalDeclD `hc (mkNot c) fun hc => do
      match ← prove (hyps.push (mkNot c, hc)) goal (splits - 1) with
      | some p => some <$> mkLambdaFVars #[hc] p
      | none => pure none
    let some neg := neg | continue
    return some (mkApp6 (mkConst ``Or.elim) c (mkNot c) goal (mkApp (mkConst ``Classical.em) c) pos neg)
  return none

end Blaster.Reconstruct.SmtProof.PropEngine
