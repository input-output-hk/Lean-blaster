import Blaster.Reconstruct.SmtProof.NlArith
import Blaster.Reconstruct.SmtProof.IR
import Blaster.Reconstruct.Certificate.IntFarkas

/-!
# Certificate-directed arithmetic replay

Z3's Farkas hints select a weighted sum of arithmetic literals. The metaprogram
only translates that data: it does not search for coefficients or call a tactic.
`check_sound` checks the resulting polynomial identity and sign contradiction
inside Lean. Unsupported hints return `none` to the caller.
-/

open Lean Meta

namespace Blaster.Reconstruct.SmtProof.Farkas

open Z3Certificate.IntFarkas

/-! ## Untrusted certificate translation -/

structure Coefficient where
  num : Int
  den : Nat := 1

/-- Exact integer, finite decimal, signed or rational coefficient. -/
partial def coefficient? : SExpr → Option Coefficient
  | .atom s => do
      if let some n := s.toInt? then return ⟨n, 1⟩
      let [a, b] := s.splitOn "." | none
      if b.isEmpty || !b.toList.all Char.isDigit then none else do
        let whole ← a.toInt?
        let frac ← b.toNat?
        let den : Nat := 10 ^ b.length
        let sign : Int := if s.startsWith "-" then -1 else 1
        return ⟨whole * (den : Int) + sign * frac, den⟩
  | .list #[.atom "-", a] => do
      let c ← coefficient? a
      return { c with num := -c.num }
  | .list #[.atom "/", a, b] => do
      let a ← coefficient? a
      let b ← coefficient? b
      if b.num == 0 then none else
        return ⟨a.num * b.den * (if b.num < 0 then -1 else 1), a.den * b.num.natAbs⟩
  | _ => none

/-- Clear denominators once; the sign convention for inequalities is normalized
    below. Equalities retain their signed multiplier. -/
def coefficients? (attrs : Array SExpr) : Option (Array Int) := do
  let cs ← (attrs.extract 2 attrs.size).mapM coefficient?
  let den := cs.foldl (fun d c => Nat.lcm d c.den) 1
  if den == 0 || den.log2 > 4096 then none else
    return cs.map fun c => c.num * (den / c.den)

/-- Normalize a proved arithmetic literal to `0 ≤ e`, `0 < e`, or `e = 0`.
    No facts are introduced beyond the supplied proof. -/
partial def literal (p h : Expr) : MetaM NlArith.Lit := do
  if p.isAppOfArity ``Not 1 then
    let a := p.appArg!
    if a.isAppOfArity ``Not 1 then
      let h ← mkAppM ``NlArith.of_not_not #[h]
      return ← literal a.appArg! h
    if a.isAppOfArity ``LE.le 4 && (a.getArg! 0).isConstOf ``Int then
      let h ← mkAppM ``Int.lt_of_not_ge #[h]
      return (← NlArith.addLit {} .pos (a.getArg! 3) (a.getArg! 2) h).lits[0]!
    if a.isAppOfArity ``LT.lt 4 && (a.getArg! 0).isConstOf ``Int then
      let h ← mkAppM ``Int.le_of_not_gt #[h]
      return (← NlArith.addLit {} .nonneg (a.getArg! 3) (a.getArg! 2) h).lits[0]!
    throwError "Farkas: unsupported negated literal"
  if p.isAppOfArity ``LE.le 4 && (p.getArg! 0).isConstOf ``Int then
    return (← NlArith.addLit {} .nonneg (p.getArg! 2) (p.getArg! 3) h).lits[0]!
  if p.isAppOfArity ``LT.lt 4 && (p.getArg! 0).isConstOf ``Int then
    return (← NlArith.addLit {} .pos (p.getArg! 2) (p.getArg! 3) h).lits[0]!
  if p.isAppOfArity ``Eq 3 && (p.getArg! 0).isConstOf ``Int then
    return (← NlArith.addLit {} .zero (p.getArg! 1) (p.getArg! 2) h).lits[0]!
  throwError "Farkas: expected an integer arithmetic literal"

theorem not_or_left {a b : Prop} (h : ¬(a ∨ b)) : ¬a := fun ha => h (Or.inl ha)
theorem not_or_right {a b : Prop} (h : ¬(a ∨ b)) : ¬b := fun hb => h (Or.inr hb)

/-- The assumptions obtained by negating a clause, in literal order. -/
partial def negatedClause (p h : Expr) : MetaM (Array (Expr × Expr)) := do
  if let some (a, b) := p.app2? ``Or then
    return (← negatedClause a (← mkAppM ``not_or_left #[h])) ++
      (← negatedClause b (← mkAppM ``not_or_right #[h]))
  return #[(mkNot p, h)]

def termExpr (r : RExpr) (strict : Bool) : Expr :=
  mkApp2 (mkConst ``Term.mk) (NlArith.rexprToExpr r) (toExpr strict)

/-- Compile the weighted literals to data, and apply only the checker soundness
    theorem. The separate polynomial computation merely proposes the constant. -/
def refute (facts : Array (Expr × Expr)) (weights : Array Int) : MetaM Expr := do
  unless facts.size == weights.size do throwError "Farkas: coefficient count mismatch"
  let mut terms := #[]
  let mut proofs := #[]
  let mut total := NlArith.Poly.const 0
  let mut atoms : NlArith.Atoms := {}
  let mut strictSum := false
  for ((p, h), weight) in facts.zip weights do
    if weight == 0 then continue
    let lit ← literal p h
    let k := if lit.kind == .zero then weight else (weight.natAbs : Int)
    let strict := lit.kind == .pos
    strictSum := strictSum || strict
    let pf ← match lit.kind with
      | .zero => mkAppM ``scale_zero #[mkIntLit k, lit.pf]
      | .nonneg => mkAppM ``scale_nonneg #[mkIntLit k,
          ← mkDecideProof (mkIntLE (mkIntLit 0) (mkIntLit k)), lit.pf]
      | .pos => mkAppM ``scale_pos #[mkIntLit k,
          ← mkDecideProof (← mkAppM ``LT.lt #[mkIntLit 0, mkIntLit k]), lit.pf]
    let ((poly, r), next) ← (NlArith.reify lit.e).run atoms
    atoms := next
    total := total.add (poly.scale k)
    terms := terms.push (termExpr (.mul (.num k) r) strict)
    proofs := proofs.push pf
  unless total.all (·.1.isEmpty) do throwError "Farkas: weighted polynomial is not constant"
  let constant := total.foldl (fun c t => c + t.2) 0
  unless (if strictSum then constant ≤ 0 else constant < 0) do
    throwError "Farkas: the weighted constant does not contradict its sign"
  let ctx ← NlArith.ringContext atoms.atoms
  let ts ← mkListLit (mkConst ``Z3Certificate.IntFarkas.Term) terms.toList
  let mut tail ← mkListLit (mkConst ``Z3Certificate.IntFarkas.Term) []
  let mut hs := mkConst ``True.intro
  for (t, pf) in (terms.zip proofs).reverse do
    hs ← mkAppM ``And.intro #[pf, hs]
    tail := mkApp3 (mkConst ``List.cons [levelZero]) (mkConst ``Z3Certificate.IntFarkas.Term) t tail
    hs ← mkExpectedTypeHint hs (mkApp2 (mkConst ``Holds) ctx tail)
  let refl := mkEqRefl (mkConst ``Bool.true)
  let checked ← mkExpectedTypeHint (← refl) (← mkEq (mkApp2 (mkConst ``Z3Certificate.IntFarkas.check) ts (mkIntLit constant)) (mkConst ``Bool.true))
  mkAppM ``check_sound #[ctx, ts, mkIntLit constant, hs, checked]

/-- A candidate proof built from a Farkas hint, or an unsupported/invalid hint.
    Its caller still checks it against the original conclusion. -/
def replay? (step : Step) (ps : Array (Expr × Expr)) (concl : Expr) : MetaM (Option Expr) := do
  if step.rule != "th-lemma" || step.attrs[0]? != some (.atom "arith") ||
      step.attrs[1]? != some (.atom "farkas") then return none
  let some weights := coefficients? step.attrs | return none
  tryCatchRuntimeEx (do
    if concl.isConstOf ``False then return some (← refute ps weights)
    let p ← withLocalDeclD `hneg (mkNot concl) fun h => do
      let proof ← refute (ps ++ (← negatedClause concl h)) weights
      mkLambdaFVars #[h] proof
    return some (mkApp2 (mkConst ``Classical.byContradiction) concl p)) fun _ => pure none

end Blaster.Reconstruct.SmtProof.Farkas
