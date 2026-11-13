import Lean

/-!
# Interpretation of Blaster's polymorphic encoding

Blaster encodes the sort variables of a goal (e.g., `α β : Type`) as values of an SMT sort `@Type`, and the values of
all the types they denote as values of a single SMT sort `@Instance`, with membership predicates `@isInstance v α`
(see `Blaster.Smt.generateSortInstDecl`). SMT sorts being non-empty, `@Instance` can't be interpreted as one of the
sort variables when several of them occur, nor when the sort variable may denote an empty type (e.g., for the skolem
constants of sort `@Instance`). The general interpretation is:
 - `@Type` (for the sort variables of `Sort u`) is `Sort u`, and the sort variables are interpreted as themselves;
 - `@Instance` is `Univ.{u}`, the values of all the types of `Sort u` (and `none`, such that it is inhabited);
 - a Lean value `x : T` is related to its interpretation by a *world* `w : T → D` (where `D` is the interpretation of
   the SMT sort of `x`): `inj α` for the sort variables, `List.map w` for lists, `liftFun wa wb dflt` for functions
   (applied to their interpreted arguments, `dflt` outside of their domain), ... (see `mkWorld`);
 - Blaster's membership predicates (`@isInstance`, `@isFun`, `@isList`, ...) are the images of the worlds (`Img`),
   such that the extensionality axioms of the encoding hold: the functions of the encoding are determined by their
   values on their domain;
 - the polymorphic Lean functions instantiated at sort variables (e.g., `@List.zipWith α β γ`, translated as SMT
   functions on `@Instance` shared by all the instantiations of a universe) are interpreted at the universe (e.g.,
   `@List.zipWith Univ Univ Univ`, see `instantiateUniv`), such that their definitional axioms hold on the whole
   universe; their applications in the goal are related to their interpretations by naturality lemmas (see
   `blaster_poly_nat`);
 - the lambda terms of the encoding, whose definitions are guarded by the membership predicates of their parameters,
   are interpreted with the same guards (`fun x => if Img w x then b else dflt x`, see `Driver.guardedLambda`), such
   that they are images of Lean functions whatever their bodies outside of their domain (e.g., constant functions);
 - the values of the other inductive types over sort variables (e.g., `Either α β`, or `Term (List α)` for a nested
   datatype of the user) are mapped by worlds defined with their recursors (see `mkIndWorld`), with the equations and
   images of their constructors (see `IndWorldLemmas`).

NOTE: naturality only holds for parametric functions: the axioms and opaque functions at sort variables (e.g.,
`hash : α → String`), and the functions with instance arguments that can't be synthesized at the universe (e.g.,
`BEq Univ`), are only interpreted when `@Instance` is interpreted as the sort variable. Likewise, the datatypes whose
proof fields mention the sort variables (e.g., properties of function fields) have no world.
-/

open Lean Meta Elab Tactic

namespace Blaster.Reconstruct.SmtProof.Poly

/-- Values of the types of `Sort u`: interpretation of the SMT sort `@Instance` of the sort variables of `Sort u`.
    Inhabited (`none`), also when all the types are empty. -/
def Univ : Type u := Option (PSigma fun (α : Sort u) => α)

instance : Inhabited Univ.{u} := ⟨(none : Option _)⟩

/-- The value `x : α` in the universe. -/
def inj (α : Sort u) (x : α) : Univ.{u} := some ⟨α, x⟩

theorem inj_injective (α : Sort u) : Function.Injective (inj α) := by
  intro x y h
  have h' : (⟨α, x⟩ : PSigma fun (α : Sort u) => α) = ⟨α, y⟩ := Option.some.inj h
  cases h'; rfl

/-- The values of `D` in the image of the world `w : T → D` (interpretation of Blaster's membership predicates,
    e.g., `@isInstance v α` is `Img (inj α) v`). -/
def Img {T : Sort u} {D : Sort v} (w : T → D) (d : D) : Prop := ∃ x, d = w x

theorem img_self {T : Sort u} {D : Sort v} (w : T → D) (x : T) : Img w (w x) := ⟨x, rfl⟩

/-- The value of the universe of a value `x : D` of the type `T` by the world `w` (the preimage of `x`), e.g., the
    conversion `@coerce` from the sort of `T` to the sort `@Instance` when `T` is used as a value (see
    `Blaster.Smt.translateIndTypeExpr?`). -/
noncomputable def coerceWorld {T : Sort u} {D : Sort v} (w : T → D) (x : D) : Univ.{u} :=
  open Classical in if h : Img w x then inj T (Classical.choose h) else none

theorem img_coerceWorld {T : Sort u} {D : Sort v} {w : T → D} {x : D} (h : Img w x) :
    Img (inj T) (coerceWorld w x) := by
  unfold coerceWorld; rw [dif_pos h]; exact img_self _ _

/-! Images of the worlds of the functors (definitions of the membership predicates of their sorts, e.g., `@isList`). -/

theorem img_list_nil {α : Type u} {β : Type v} (w : α → β) : Img (List.map w) [] := ⟨[], rfl⟩

theorem img_list_cons {α : Type u} {β : Type v} {w : α → β} {x : β} {xs : List β} :
    Img (List.map w) (x :: xs) ↔ Img w x ∧ Img (List.map w) xs := by
  constructor
  · intro ⟨l, hl⟩
    cases l with
    | nil => cases hl
    | cons a l => cases hl; exact ⟨⟨a, rfl⟩, ⟨l, rfl⟩⟩
  · intro ⟨⟨a, ha⟩, ⟨l, hl⟩⟩; exact ⟨a :: l, by rw [ha, hl]; rfl⟩

theorem img_option_none {α : Type u} {β : Type v} (w : α → β) : Img (Option.map w) none := ⟨none, rfl⟩

theorem img_option_some {α : Type u} {β : Type v} {w : α → β} {x : β} : Img (Option.map w) (some x) ↔ Img w x := by
  constructor
  · intro ⟨l, hl⟩
    cases l with
    | none => cases hl
    | some a => cases hl; exact ⟨a, rfl⟩
  · intro ⟨a, ha⟩; exact ⟨some a, by rw [ha]; rfl⟩

theorem img_prod {α₁ : Type u₁} {α₂ : Type u₂} {β₁ : Type v₁} {β₂ : Type v₂} {w₁ : α₁ → α₂} {w₂ : β₁ → β₂}
    {x : α₂} {y : β₂} : Img (Prod.map w₁ w₂) (x, y) ↔ Img w₁ x ∧ Img w₂ y := by
  constructor
  · intro ⟨⟨a, b⟩, h⟩; cases h; exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  · intro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; exact ⟨(a, b), by rw [ha, hb]; rfl⟩

/-- The function `f : A → B` on the interpretations `D` and `C` of its domain and codomain (worlds `wa : A → D`,
    `wb : B → C`), `dflt` outside of the image of `wa`. -/
noncomputable def liftFun {A : Sort a} {B : Sort b} {D : Sort d} {C : Sort c}
    (wa : A → D) (wb : B → C) (dflt : D → C) (f : A → B) (x : D) : C :=
  @dite C (Img wa x) (Classical.propDecidable _) (fun h => wb (f (Classical.choose h))) (fun _ => dflt x)

theorem liftFun_apply {A : Sort a} {B : Sort b} {D : Sort d} {C : Sort c}
    {wa : A → D} (hw : Function.Injective wa) (wb : B → C) (dflt : D → C) (f : A → B) (x : A) :
    liftFun wa wb dflt f (wa x) = wb (f x) := by
  have h : Img wa (wa x) := ⟨x, rfl⟩
  unfold liftFun
  rw [dif_pos h]
  exact congrArg (fun y => wb (f y)) (hw (Classical.choose_spec h)).symm

theorem liftFun_out {A : Sort a} {B : Sort b} {D : Sort d} {C : Sort c}
    (wa : A → D) (wb : B → C) (dflt : D → C) (f : A → B) {x : D} (h : ¬ Img wa x) :
    liftFun wa wb dflt f x = dflt x := by
  unfold liftFun; rw [dif_neg h]

theorem liftFun_injective {A : Sort a} {B : Sort b} {D : Sort d} {C : Sort c}
    {wa : A → D} (hwa : Function.Injective wa) {wb : B → C} (hwb : Function.Injective wb) (dflt : D → C) :
    Function.Injective (liftFun wa wb dflt) := by
  intro f g h
  funext x
  apply hwb
  rw [← liftFun_apply hwa wb dflt f x, ← liftFun_apply hwa wb dflt g x, h]

theorem natCast_injective : Function.Injective (@Nat.cast Int instNatCastInt) :=
  fun _ _ h => Int.ofNat.inj h

theorem boolTrue_injective : Function.Injective (fun (b : Bool) => b = true) := by
  intro x y h
  cases x <;> cases y <;> simp_all

theorem id_injective (α : Sort u) : Function.Injective (@id α) := fun _ _ h => h

theorem listMap_injective {α : Type u} {β : Type v} {w : α → β} (hw : Function.Injective w) :
    Function.Injective (List.map w) := by
  intro xs ys h
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons => simp at h
  | cons x xs ih => cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [hw h.1, ih h.2]

theorem optionMap_injective {α : Type u} {β : Type v} {w : α → β} (hw : Function.Injective w) :
    Function.Injective (Option.map w) := by
  intro x y h
  cases x <;> cases y <;> simp_all
  exact hw h

theorem prodMap_injective {α₁ : Type u₁} {α₂ : Type u₂} {β₁ : Type v₁} {β₂ : Type v₂}
    {w₁ : α₁ → α₂} {w₂ : β₁ → β₂} (h₁ : Function.Injective w₁) (h₂ : Function.Injective w₂) :
    Function.Injective (Prod.map w₁ w₂) := by
  intro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Prod.map, Prod.mk.injEq] at h
  rw [h₁ h.1, h₂ h.2]

/-! ## Bridge lemmas (see `Bridge.lean`) -/

theorem eq_world {T : Sort u} {D : Sort v} {w : T → D} (hw : Function.Injective w) {x y : T} {x' y' : D}
    (hx : w x = x') (hy : w y = y') : (x = y) = (x' = y') := by
  subst hx hy
  exact propext ⟨fun h => h ▸ rfl, fun h => hw h⟩

theorem forall_world {T : Sort u} {D : Sort v} (w : T → D) {P : T → Prop} {Q : D → Prop}
    (h : ∀ x, P x = Q (w x)) : (∀ x, P x) = (∀ y, Img w y → Q y) := by
  apply propext; constructor
  · intro hp y ⟨x, hx⟩; subst hx; rw [← h]; exact hp x
  · intro hq x; rw [h]; exact hq (w x) ⟨x, rfl⟩

theorem exists_world {T : Sort u} {D : Sort v} (w : T → D) {P : T → Prop} {Q : D → Prop}
    (h : ∀ x, P x = Q (w x)) : (∃ x, P x) = (∃ y, Img w y ∧ Q y) := by
  apply propext; constructor
  · intro ⟨x, hx⟩; exact ⟨w x, ⟨x, rfl⟩, h x ▸ hx⟩
  · intro ⟨y, ⟨x, hx⟩, hq⟩; subst hx; exact ⟨x, (h x).symm ▸ hq⟩

theorem app_world {A : Sort a} {B : Sort b} {D : Sort d} {C : Sort c}
    {wa : A → D} (hw : Function.Injective wa) {wb : B → C} {dflt : D → C} {f : A → B} {F : D → C} {x : A} {X : D}
    (hf : liftFun wa wb dflt f = F) (hx : wa x = X) : wb (f x) = F X := by
  subst hf hx; exact (liftFun_apply hw wb dflt f x).symm

theorem lam_world {A : Sort a} {B : Sort b} {D : Sort d} {C : Sort c}
    {wa : A → D} (hw : Function.Injective wa) {wb : B → C} {dflt : D → C} {f : A → B} {F : D → C}
    (h : ∀ x, wb (f x) = F (wa x)) (hout : ∀ y, ¬ Img wa y → dflt y = F y) : liftFun wa wb dflt f = F := by
  funext y
  by_cases hy : Img wa y
  · obtain ⟨x, rfl⟩ := hy; rw [liftFun_apply hw, h]
  · rw [liftFun_out _ _ _ _ hy, hout y hy]

/-- Lambda terms guarded by the membership predicates of their parameters (see `guardedLambda`). -/
theorem lam_world_ite {A : Sort a} {B : Sort b} {D : Sort d} {C : Sort c}
    {wa : A → D} (hw : Function.Injective wa) {wb : B → C} {dflt : D → C} {f : A → B} {F : D → C}
    (h : ∀ x, wb (f x) = F (wa x)) :
    liftFun wa wb dflt f = fun y => @ite C (Img wa y) (Classical.propDecidable _) (F y) (dflt y) := by
  funext y
  by_cases hy : Img wa y
  · rw [if_pos hy]; obtain ⟨x, rfl⟩ := hy; rw [liftFun_apply hw, h]
  · rw [if_neg hy, liftFun_out _ _ _ _ hy]

theorem ite_world {T : Sort u} {D : Sort v} (w : T → D) {c c' : Prop} [h : Decidable c] {x y : T} {x' y' : D}
    (hc : c = c') (hx : c → w x = x') (hy : ¬ c → w y = y') :
    w (@ite T c h x y) = @ite D c' (Classical.propDecidable c') x' y' := by
  subst hc
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]; exact hx hc
  · rw [if_neg hc, if_neg hc]; exact hy hc

/-- Case analyses (testers and selectors, see `Bridge.walkPolyCasesOn`) on lists in the world `List.map w`, with the
    world `wr` of their results. -/
theorem list_casesOn_world {A : Type u} {B : Type v} {w : A → B} {C : Sort x} {C' : Sort y} (wr : C → C')
    {d : List A} {D : List B} (hd : List.map w d = D) {n : C} {n' : C'} {c : A → List A → C}
    {c' : B → List B → C'} (hn : d = [] → wr n = n') (hc : ∀ h t, d = h :: t → wr (c h t) = c' (w h) (List.map w t)) :
    wr (@List.casesOn A (fun _ => C) d n c) = @List.casesOn B (fun _ => C') D n' c' := by
  subst hd
  cases d with
  | nil => exact hn rfl
  | cons h t => exact hc h t rfl

theorem option_casesOn_world {A : Type u} {B : Type v} {w : A → B} {C : Sort x} {C' : Sort y} (wr : C → C')
    {d : Option A} {D : Option B} (hd : Option.map w d = D) {n : C} {n' : C'} {c : A → C} {c' : B → C'}
    (hn : d = none → wr n = n') (hc : ∀ v, d = some v → wr (c v) = c' (w v)) :
    wr (@Option.casesOn A (fun _ => C) d n c) = @Option.casesOn B (fun _ => C') D n' c' := by
  subst hd
  cases d with
  | none => exact hn rfl
  | some v => exact hc v rfl

/-! ## Axioms of the encoding -/

theorem img_liftFun {A : Sort a} {B : Sort b} {D : Sort d} {C : Sort c}
    {wa : A → D} (hw : Function.Injective wa) {wb : B → C} {dflt : D → C} {F : D → C} {y : D}
    (hF : Img (liftFun wa wb dflt) F) (hy : Img wa y) : Img wb (F y) := by
  obtain ⟨f, rfl⟩ := hF
  obtain ⟨x, rfl⟩ := hy
  rw [liftFun_apply hw]; exact ⟨f x, rfl⟩

theorem ext_liftFun {A : Sort a} {B : Sort b} {D : Sort d} {C : Sort c}
    {wa : A → D} {wb : B → C} {dflt : D → C} {F G : D → C}
    (hF : Img (liftFun wa wb dflt) F) (hG : Img (liftFun wa wb dflt) G) (h : ∀ y, Img wa y → F y = G y) : F = G := by
  obtain ⟨f, rfl⟩ := hF
  obtain ⟨g, rfl⟩ := hG
  funext y
  by_cases hy : Img wa y
  · exact h y hy
  · rw [liftFun_out _ _ _ _ hy, liftFun_out _ _ _ _ hy]

theorem ext_liftFun₂ {A₁ : Sort a₁} {A₂ : Sort a₂} {B : Sort b} {D₁ : Sort d₁} {D₂ : Sort d₂} {C : Sort c}
    {w₁ : A₁ → D₁} (hw₁ : Function.Injective w₁) {w₂ : A₂ → D₂} {wb : B → C} {dflt₁ : D₁ → D₂ → C}
    {dflt₂ : D₂ → C} {F G : D₁ → D₂ → C}
    (hF : Img (liftFun w₁ (liftFun w₂ wb dflt₂) dflt₁) F) (hG : Img (liftFun w₁ (liftFun w₂ wb dflt₂) dflt₁) G)
    (h : ∀ y₁ y₂, Img w₁ y₁ → Img w₂ y₂ → F y₁ y₂ = G y₁ y₂) : F = G := by
  obtain ⟨f, rfl⟩ := hF
  obtain ⟨g, rfl⟩ := hG
  funext y₁
  by_cases hy₁ : Img w₁ y₁
  · obtain ⟨x₁, rfl⟩ := hy₁
    rw [liftFun_apply hw₁, liftFun_apply hw₁]
    funext y₂
    by_cases hy₂ : Img w₂ y₂
    · have := h (w₁ x₁) y₂ ⟨x₁, rfl⟩ hy₂
      rwa [liftFun_apply hw₁, liftFun_apply hw₁] at this
    · rw [liftFun_out _ _ _ _ hy₂, liftFun_out _ _ _ _ hy₂]
  · rw [liftFun_out _ _ _ _ hy₁, liftFun_out _ _ _ _ hy₁]

theorem img_liftFun₂ {A₁ : Sort a₁} {A₂ : Sort a₂} {B : Sort b} {D₁ : Sort d₁} {D₂ : Sort d₂} {C : Sort c}
    {w₁ : A₁ → D₁} (hw₁ : Function.Injective w₁) {w₂ : A₂ → D₂} (hw₂ : Function.Injective w₂) {wb : B → C}
    {dflt₁ : D₁ → D₂ → C} {dflt₂ : D₂ → C} {F : D₁ → D₂ → C} {y₁ : D₁} {y₂ : D₂}
    (hF : Img (liftFun w₁ (liftFun w₂ wb dflt₂) dflt₁) F) (hy₁ : Img w₁ y₁) (hy₂ : Img w₂ y₂) : Img wb (F y₁ y₂) :=
  img_liftFun hw₂ (img_liftFun hw₁ hF hy₁) hy₂

theorem img_id {T : Sort u} {D : Sort v} {w : T → D} (hw : Function.Injective w) :
    Img (liftFun w w (fun x => x)) (fun x => x) :=
  ⟨fun x => x, (lam_world hw (fun _ => rfl) (fun _ _ => rfl)).symm⟩

/-- One level of case analysis on the variables `fvs` of `g`. -/
partial def casesVars (g : MVarId) (fvs : List FVarId) : MetaM (List MVarId) := do
  match fvs with
  | [] => return [g]
  | fv :: rest =>
      if !(← g.withContext do return (← getLCtx).contains fv) then return ← casesVars g rest
      let sgs ← try g.cases fv catch _ => return ← casesVars g rest
      let mut acc := []
      for sg in sgs do
        let rest' := rest.map fun f => match sg.subst.get f with | .fvar f' => f' | _ => f
        acc := acc ++ (← casesVars sg.mvarId rest')
      return acc

syntax (name := blasterPolyCases) "blaster_poly_cases" : tactic

/-- One level of case analysis on the variables of datatypes (e.g., in the catch-all cases of a functional
    induction, whose hypotheses exclude the other patterns). -/
@[tactic blasterPolyCases] def evalBlasterPolyCases : Tactic := fun _ => do
  let g ← getMainGoal
  let fvs ← g.withContext do
    let mut acc := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← whnfR d.type
      let .const n _ := ty.getAppFn | continue
      if (← isProp ty) || (← isClass? ty).isSome then continue
      let some (.inductInfo info) := (← getEnv).find? n | continue
      if info.numIndices != 0 then continue
      acc := acc.push d.fvarId
    return acc
  replaceMainGoal (← casesVars g fvs.toList)

/-! ## Worlds -/

/-- A default value of `t` (inhabited types and functions to inhabited types). -/
partial def mkDefault (t : Expr) : MetaM Expr := do
  let t ← whnfR t
  if let .forallE n d b bi := t then
    if !b.hasLooseBVars then
      return mkLambda n bi d (← mkDefault b)
  let u ← getLevel t
  try
    let inst ← synthInstance (mkApp (mkConst ``Inhabited [u]) t)
    return mkApp2 (mkConst ``Inhabited.default [u]) t inst
  catch _ =>
    let inst ← synthInstance (mkApp (mkConst ``Nonempty [u]) t)
    return mkApp2 (mkConst ``Classical.ofNonempty [u]) t inst

/-- Whether `t` is (or contains) the universe of the interpretation. -/
def hasUniv (t : Expr) : Bool := (t.find? fun s => s.isConstOf ``Univ).isSome

/-- `w x`, β-reduced. -/
def applyWorld (w x : Expr) : Expr := (mkApp w x).headBeta

/-! ## Worlds of inductive types

The values of the inductive types over sort variables (e.g., `Term (List α)` for a datatype `Term` of the user,
possibly nested or mutual) are mapped to the instance of their type at the universe (e.g., `Term (List Univ)`) by a
function defined with the recursor of the type (see `mkIndWorld`): each constructor is mapped to itself, with its fields
mapped by their worlds (see `mkWorld`) and its recursive fields (including the nested occurrences, e.g.,
`List (Term α)`) by the recursor. The maps of the types of a mutual block and the proofs of their injectivity are
auxiliary declarations, per instance closed over its free variables, with the lemmas used by the bridge (see
`IndWorldLemmas`).

NOTE: there is no world for the types with indices, with proof fields whose propositions differ in the two instances
(e.g., properties of function fields, whose proofs would have to be transported), with dependent fields mapped by a
world, or with recursive fields of function types. -/

/-- The worlds of the types of the fields of the constructors (`field t d` for the type `t` interpreted as `d`, see
    `mkWorld`), with the proofs of their injectivity (`none` when there is none). -/
abbrev FieldWorld := Expr → Expr → MetaM (Option (Expr × Expr))

/-- Map of a field of a constructor (see `mkIndWorld`). -/
inductive FieldMap where
  /-- same type in both instances -/
  | same
  /-- recursive field, mapped by the inductive hypothesis of index `ih` among the binders of the minor premise -/
  | recursive (ih : Nat)
  /-- field mapped by the world `w`, with the proof `inj` of its injectivity -/
  | world (w inj : Expr)
  deriving Inhabited

/-- Minor premise of the recursor of an inductive type (see `mkIndWorld`): the index of its motive, its number of
    binders, the positions of the fields of the constructor among them, and the maps of the fields. -/
structure MinorMap where
  motive : Nat
  numBinders : Nat
  fields : Array Nat
  maps : Array FieldMap
  deriving Inhabited

/-- A block of inductive types (`I as` to `I bs`) mapped by its recursors (see `mkIndWorld`). -/
structure Block where
  info : InductiveVal
  us : List Level
  vs : List Level
  as : Array Expr
  bs : Array Expr
  /-- level of the sort of the target types -/
  lvl : Level
  /-- domains of the motives (the types of the block and their nested occurrences) in both instances -/
  ds : Array Expr
  dt : Array Expr
  /-- motives and minor premises of the maps -/
  motives : Array Expr
  minorVals : Array Expr
  minors : Array MinorMap
  /-- recursor of each motive (`T.rec` for the types of the block, `T.rec_i` for their nested occurrences) -/
  recs : Array Name

/-- The recursor of the `k`-th motive of the block at the level `lvl`, applied to the motives `ms`, the minor premises
    `mns` and `x`. -/
def Block.recApp (b : Block) (k : Nat) (lvl : Level) (ms mns : Array Expr) (x : Expr) : Expr :=
  mkAppN (mkConst b.recs[k]! (lvl :: b.us)) (b.as ++ ms ++ mns |>.push x)

/-- The map of the `k`-th motive of the block applied to `x`. -/
def Block.map (b : Block) (k : Nat) (x : Expr) : Expr := b.recApp k b.lvl b.motives b.minorVals x

/-- Proofs of the minor premises of the recursors of the block for the motives `props` (into `Prop`), by `prove` from
    the type of each minor premise and its map. -/
def Block.minorProofs (b : Block) (props : Array Expr) (prove : Expr → MinorMap → MetaM Expr) :
    MetaM (Array Expr) := do
  let recName := mkRecName b.info.all.head!
  let mut ty ← instantiateForall ((← getConstInfo recName).instantiateTypeLevelParams (levelZero :: b.us))
    (b.as ++ props)
  let mut proofs := #[]
  for mi in b.minors do
    let .forallE _ mt body _ := ty | throwError "mkIndWorld: minor premise expected"
    let p ← prove (← Core.betaReduce mt) mi
    proofs := proofs.push p
    ty := body.instantiate1 p
  return proofs

/-- Lemmas of the world `W` of an inductive type (see `mkIndWorld`), closed over the arguments of `W` (its free
    variables): its injectivity and, per constructor `C` (`C'` in the target instance), the equation
    `∀ xs, W (C xs) = C' (Ŵ xs)` where `Ŵ` are the worlds of the fields (see `mkWorld`, e.g., `List.map W` for the
    nested occurrences `List (T α)`), and the image `∀ ys, Img W (C' ys) = (Img Ŵᵢ yᵢ ∧ …)` (`True` without fields
    mapped by a world). -/
structure IndWorldLemmas where
  inj : Expr
  eqns : Array (Name × Expr) := #[]
  imgs : Array (Name × Expr) := #[]
  /-- the theorems (universally quantified over the arguments of the world), for `simp` -/
  thms : Array Expr := #[]
  deriving Inhabited

/-- Worlds of the inductive types (see `mkIndWorld`), per instance closed over its free variables: the worlds and the
    proofs of their injectivity, closed over the same variables, in the environment branches where they were declared
    (`#blaster` commands are elaborated concurrently): the first one declared in the current environment is reused,
    such that the worlds of a replay coincide. -/
initialize indWorldCache : IO.Ref (Std.HashMap Expr (Array (Expr × Expr))) ← IO.mkRef {}

/-- The instances without a world (see `indWorldCache`). -/
initialize noIndWorld : IO.Ref (Std.HashSet Expr) ← IO.mkRef {}

/-- Lemmas of the worlds of the inductive types (see `IndWorldLemmas`), per world. -/
initialize indWorldLemmasCache : IO.Ref (Std.HashMap Name IndWorldLemmas) ← IO.mkRef {}

/-- The lemmas of the world `w` (an application of the map of an inductive type, see `mkIndWorld`), instantiated with
    its arguments. -/
def indWorldLemmas? (w : Expr) : MetaM (Option IndWorldLemmas) := do
  let .const n _ := w.getAppFn | return none
  let some l := (← indWorldLemmasCache.get).get? n | return none
  let env ← getEnv
  if !env.contains n then return none
  let args := w.getAppArgs
  let inst (e : Expr) : Option Expr := if e.getUsedConstants.all env.contains then some (e.beta args) else none
  let some inj := inst l.inj | return none
  return some { inj, eqns := l.eqns.filterMap fun (c, e) => (c, ·) <$> inst e,
                imgs := l.imgs.filterMap fun (c, e) => (c, ·) <$> inst e,
                thms := l.thms.filter (·.getUsedConstants.all env.contains) }

/-- `C a₁ … aₙ = C b₁ … bₙ` (`lhs` and `rhs`, applications of the same constructor up to reduction) from proofs of
    `aᵢ = bᵢ` given by `arg` (when they are not definitionally equal). -/
def congrCtor (lhs rhs : Expr) (arg : Expr → Expr → MetaM (Option Expr)) : MetaM (Option Expr) := do
  let l ← whnf lhs
  let r ← whnf rhs
  let .const c _ := l.getAppFn | return none
  if !r.getAppFn.isConstOf c || l.getAppNumArgs != r.getAppNumArgs then return none
  let some (.ctorInfo info) := (← getEnv).find? c | return none
  let (la, ra) := (l.getAppArgs, r.getAppArgs)
  for i in [:info.numParams] do
    if !(← isDefEq la[i]! ra[i]!) then return none
  let mut pf ← mkEqRefl (mkAppN l.getAppFn (la.extract 0 info.numParams))
  for i in [info.numParams:la.size] do
    let p ← if ← isDefEq la[i]! ra[i]! then mkEqRefl la[i]! else
      let some p ← arg la[i]! ra[i]! | return none
      pure p
    pf ← mkCongr pf p
  return some (← mkExpectedTypeHint pf (← mkEq lhs rhs))

/-- `⟨x, h⟩ : Img w a` for `h : a = w x`. -/
def mkImgIntro (w a x h : Expr) : MetaM Expr := do
  let p ← withLocalDeclD `x (← inferType x) fun z => do mkLambdaFVars #[z] (← mkEq a (mkApp w z))
  mkExpectedTypeHint (← mkAppOptM ``Exists.intro #[← inferType x, p, x, h]) (← mkAppM ``Img #[w, a])

/-- The world of the values of the instance `t := I as` of a non-indexed (possibly nested or mutual) inductive type `I`
    interpreted as `d := I bs`, with a proof of its injectivity: auxiliary definitions mapping the types of the block
    with their recursors, where the fields that are not recursive are mapped by `field` (the worlds of their types,
    `none` when there is none). The lemmas of the worlds (see `IndWorldLemmas`) are proved once the worlds of the
    block are known (e.g., `List.map W` for the nested occurrences). -/
partial def mkIndWorld (t d : Expr) (field : FieldWorld) : MetaM (Option (Expr × Expr)) := do
  let .const I us := t.getAppFn | return none
  let .const I' vs := d.getAppFn | return none
  if I != I' then return none
  let some (.inductInfo info) := (← getEnv).find? I | return none
  if info.numIndices != 0 || info.isUnsafe || t.getAppNumArgs != info.numParams || d.getAppNumArgs != info.numParams
  then return none
  if ← isProp t then return none
  -- the instance closed over its free variables
  let fvs := (← sortFVarIds (collectFVars {} (mkApp t d)).fvarIds).map mkFVar
  let closed (e : Expr) : MetaM (Option Expr) := do
    let e ← mkLambdaFVars fvs e
    return if e.hasFVar || e.hasMVar then none else some e
  let cacheKey (t d : Expr) : MetaM (Option Expr) := closed (mkApp2 (mkConst `_blaster_world) t d)
  let some key ← cacheKey t d | return none
  let env ← getEnv
  if (← noIndWorld.get).contains key then return none
  for (w, h) in (← indWorldCache.get).getD key #[] do
    if w.getUsedConstants.all env.contains && h.getUsedConstants.all env.contains then
      return some (w.beta fvs, h.beta fvs)
  let r ← try some <$> build field info us vs t.getAppArgs d.getAppArgs (← getLevel d) catch _ => pure none
  let some (blk, worlds) := r | noIndWorld.modify (·.insert key); return none
  -- the worlds of the types of the block, then their lemmas
  for (n, w, h) in info.all.toArray.zip worlds do
    let some k ← cacheKey (mkAppN (mkConst n us) blk.as) (mkAppN (mkConst n vs) blk.bs) | continue
    if let (some cw, some ch) := (← closed w, ← closed h) then
      indWorldCache.modify fun m => m.insert k ((m.getD k #[]).push (cw, ch))
  let auxEqns ← try auxEquations field blk catch _ => pure #[]
  for h : i in [:worlds.size] do
    let (w, inj) := worlds[i]
    let .const n _ := w.getAppFn | continue
    let args := w.getAppArgs
    if !args.all (·.isFVar) then continue
    let mut lemmas : IndWorldLemmas := { inj := ← mkLambdaFVars args inj, thms := #[inj.getAppFn] }
    for c in (← getConstInfoInduct info.all[i]!).ctors do
      let some (eqn, img) ← (try ctorLemmas field blk i w auxEqns c catch _ => pure none) | continue
      lemmas := { lemmas with eqns := lemmas.eqns.push (c, ← mkLambdaFVars args eqn),
                              imgs := lemmas.imgs.push (c, ← mkLambdaFVars args img),
                              thms := lemmas.thms ++ #[eqn.getAppFn, img.getAppFn] }
    indWorldLemmasCache.modify (·.insert n lemmas)
  return worlds[info.all.idxOf I]?
where
  /-- The block of `info` (`I as` to `I bs`, where `lvl` is the level of the sort of the target types), with the
      worlds of its types and the proofs of their injectivity. -/
  build (field : FieldWorld) (info : InductiveVal) (us vs : List Level) (as bs : Array Expr) (lvl : Level) :
      MetaM (Block × Array (Expr × Expr)) := do
    let env ← getEnv
    let recName := mkRecName info.all.head!
    let some (.recInfo rinfo) := env.find? recName | throwError "mkIndWorld: no recursor"
    if rinfo.levelParams.length != us.length + 1 then throwError "mkIndWorld: no large elimination"
    let recType (n : Name) (lvls : List Level) (ps : Array Expr) : MetaM Expr := do
      instantiateForall ((← getConstInfo n).instantiateTypeLevelParams lvls) ps
    -- the domains of the motives (the types of the block and their nested occurrences), in both instances
    let motiveDoms (ty : Expr) : MetaM (Array Expr) :=
      forallBoundedTelescope ty rinfo.numMotives fun ms _ => ms.mapM fun m => do
        let dom := (← inferType m).bindingDomain!
        if dom.hasAnyFVar (ms.contains <| mkFVar ·) then throwError "mkIndWorld: dependent motive"
        return dom
    let ds ← motiveDoms (← recType recName (lvl :: us) as)
    let dt ← motiveDoms (← recType recName (lvl :: vs) bs)
    if ds.size != dt.size || ds.size != rinfo.numMotives then throwError "mkIndWorld: motives"
    for t in dt do
      if !(← isLevelDefEq (← getLevel t) lvl) then throwError "mkIndWorld: universe levels"
    let motives := (ds.zip dt).map fun (a, b) => mkLambda `x .default a b
    -- the minor premises of the maps
    let (minorVals, minors) ← forallBoundedTelescope (← recType recName (lvl :: us) as) rinfo.numMotives fun ms b => do
      forallBoundedTelescope b rinfo.numMinors fun mns _ => do
        let mut vals := #[]
        let mut infos := #[]
        for mn in mns do
          let (v, i) ← forallTelescope (← inferType mn) fun xs concl => minor field ms dt xs concl
          vals := vals.push (← mkLambdaFVars ms v)
          infos := infos.push i
        return (vals, infos)
    let minorVals ← minorVals.mapM fun v => Core.betaReduce (v.beta motives)
    let recs := (List.range ds.size).toArray.map fun k =>
      if h : k < info.all.length then mkRecName info.all[k]
      else Name.str info.all.head! s!"rec_{k + 1 - info.all.length}"
    for k in [:ds.size] do
      if !env.contains recs[k]! then throwError "mkIndWorld: recursor {recs[k]!}"
    let blk : Block := { info, us, vs, as, bs, lvl, ds, dt, motives, minorVals, minors, recs }
    -- injectivity: `∀ x y, map_k x = map_k y → x = y`, by the recursors (case analysis on `y` and injection)
    let props ← (List.range ds.size).toArray.mapM fun k =>
      withLocalDeclD `x ds[k]! fun x => withLocalDeclD `y ds[k]! fun y => do
        mkLambdaFVars #[x] (← mkForallFVars #[y] (← mkArrow (← mkEq (blk.map k x) (blk.map k y)) (← mkEq x y)))
    let proofs ← blk.minorProofs props proveMinor
    let mut res := #[]
    for i in [:info.all.length] do
      let value ← withLocalDeclD `x ds[i]! fun x => do mkLambdaFVars #[x] (blk.map i x)
      let w ← mkAuxDefinition (← mkAuxDeclName (kind := `_blaster_world)) (← mkArrow ds[i]! dt[i]!) value
        (compile := false)
      let stmt ← mkAppM ``Function.Injective #[w]
      let pf ← withLocalDeclD `x ds[i]! fun x => do mkLambdaFVars #[x] (blk.recApp i levelZero props proofs x)
      res := res.push (w, ← mkAuxTheorem stmt (← mkExpectedTypeHint pf stmt))
    return (blk, res)
  /-- The minor premise of the map for the constructor of `concl` (`motive_k (C ps fs)`, where the `ms` are the
      motives, `xs` the binders of the minor premise and `dt` the target types of the motives). -/
  minor (field : FieldWorld) (ms dt xs : Array Expr) (concl : Expr) : MetaM (Expr × MinorMap) := do
    let some k := ms.findIdx? (· == concl.getAppFn) | throwError "mkIndWorld: motive expected"
    let app := concl.appArg!
    let .const c _ := app.getAppFn | throwError "mkIndWorld: constructor expected"
    let some (.ctorInfo cinfo) := (← getEnv).find? c | throwError "mkIndWorld: constructor expected"
    let fs := app.getAppArgs.extract cinfo.numParams app.getAppNumArgs
    if fs.size != cinfo.numFields || !fs.all xs.contains then throwError "mkIndWorld: fields"
    -- the inductive hypotheses: binders of type `motive_j f` (recursive fields)
    let mut ihOf : Std.HashMap FVarId Nat := {}
    for h : i in [:xs.size] do
      let ty ← inferType xs[i]
      if ms.contains ty.getAppFn then
        if !ty.appArg!.isFVar then throwError "mkIndWorld: recursive field of function type"
        ihOf := ihOf.insert ty.appArg!.fvarId! i
      else if ← forallTelescope ty fun _ b => return ms.contains b.getAppFn then
        throwError "mkIndWorld: recursive field of function type"
    -- the constructor in the target instance
    let tgt ← whnf dt[k]!
    let .const J ls := tgt.getAppFn | throwError "mkIndWorld: inductive type expected"
    if J != cinfo.induct then throwError "mkIndWorld: inductive type expected"
    let ctor := mkAppN (mkConst c ls) tgt.getAppArgs
    let mut cty ← inferType ctor
    let mut args := #[]
    let mut maps := #[]
    for f in fs do
      let .forallE _ g b _ ← whnf cty | throwError "mkIndWorld: field expected"
      let ft ← inferType f
      let (v, m) ← if let some i := ihOf.get? f.fvarId! then pure (xs[i]!, FieldMap.recursive i)
        else if ← isDefEq ft g then pure (f, .same)
        else if ← isProp ft then throwError "mkIndWorld: proof field"
        else match ← field ft g with
          | some (w, h) => pure (applyWorld w f, .world w h)
          | none => throwError "mkIndWorld: no world for {ft}"
      args := args.push v
      maps := maps.push m
      cty := b.instantiate1 v
    let fields := fs.filterMap fun f => xs.idxOf? f
    return (← mkLambdaFVars xs (mkAppN ctor args), { motive := k, numBinders := xs.size, fields, maps })
  /-- Proof of the minor premise `mt` of the injectivity of the maps: `∀ fs ihs y, map_k (C fs) = map_k y → C fs = y`,
      by case analysis on `y` and injection (the equations of the fields give the equations of their values by the
      inductive hypotheses and the injectivity of the worlds of the fields). -/
  proveMinor (mt : Expr) (mi : MinorMap) : MetaM Expr :=
    forallBoundedTelescope mt mi.numBinders fun xs goal => do
      let g ← mkFreshExprSyntheticOpaqueMVar goal
      let (y, g') ← g.mvarId!.intro1P
      let (h, g') ← g'.intro1P
      for sg in ← g'.cases y do
        let g := sg.mvarId
        let .fvar h := sg.subst.get h | throwError "mkIndWorld: injection"
        -- both sides as constructor applications
        let g ← g.withContext do
          let some (_, a, b) := (← h.getType).eq? | throwError "mkIndWorld: equation expected"
          g.replaceLocalDeclDefEq h (← mkEq (← whnf a) (← whnf b))
        match ← injection g h with
        | .solved => pure ()
        | .subgoal g eqs _ =>
            -- the equations of the fields that are not proofs, in order
            let nonProof ← g.withContext do
              (List.range mi.fields.size).toArray.filterM fun j => do return !(← isProof xs[mi.fields[j]!]!)
            if eqs.size != nonProof.size then throwError "mkIndWorld: injection"
            let pfs ← g.withContext do (eqs.zip nonProof).mapM fun (e, j) => do
              let x := xs[mi.fields[j]!]!
              let y := sg.fields[j]!
              let p := match mi.maps[j]! with
                | .same => mkFVar e
                | .recursive i => mkApp2 xs[i]! y (mkFVar e)
                | .world _ inj => mkApp3 inj x y (mkFVar e)
              return (p, ← mkEq x y)
            let mut g := g
            for (p, t) in pfs do
              let (fv, g') ← g.note `h p t
              g ← subst g' fv
            g.refl
      mkLambdaFVars xs (← instantiateMVars g)
  /-- Equations of the maps of the nested occurrences: `∀ l, map_j l = E_j l` where `E_j` is the world of the type of
      `l` (e.g., `List.map W` for `List (T α)`, see `mkWorld`), by the recursor of the block. -/
  auxEquations (field : FieldWorld) (blk : Block) : MetaM (Array (Nat × Expr)) := do
    let n := blk.info.all.length
    if blk.ds.size == n then return #[]
    let mut ws : Array (Option Expr) := #[]
    for k in [:blk.ds.size] do
      if k < n then ws := ws.push none
      else ws := ws.push ((← field blk.ds[k]! blk.dt[k]!).map (·.1))
    let props ← (List.range blk.ds.size).toArray.mapM fun k =>
      withLocalDeclD `x blk.ds[k]! fun x => do
        match ws[k]! with
        | some w => mkLambdaFVars #[x] (← mkEq (blk.map k x) (applyWorld w x))
        | none => mkLambdaFVars #[x] (mkConst ``True)
    let proofs ← blk.minorProofs props fun mt mi =>
      forallBoundedTelescope mt mi.numBinders fun xs goal => do
        if goal.isConstOf ``True then return ← mkLambdaFVars xs (mkConst ``True.intro)
        let some (_, lhs, rhs) := goal.eq? | throwError "mkIndWorld: equation expected"
        -- the inductive hypotheses of the nested fields
        let some p ← congrCtor lhs rhs (fun a b => do
            for x in xs do
              let some (_, l, r) := (← inferType x).eq? | continue
              if (← isDefEq l a) && (← isDefEq r b) then return some x
            return none)
          | throwError "mkIndWorld: equation of a nested occurrence"
        mkLambdaFVars xs p
    let mut res := #[]
    for k in [n:blk.ds.size] do
      if ws[k]!.isNone then continue
      let stmt ← withLocalDeclD `x blk.ds[k]! fun x => do mkForallFVars #[x] (props[k]!.beta #[x])
      let pf ← withLocalDeclD `x blk.ds[k]! fun x => do mkLambdaFVars #[x] (blk.recApp k levelZero props proofs x)
      res := res.push (k, ← mkAuxTheorem stmt pf)
    return res
  /-- The equation and the image of the constructor `c` of the `i`-th type of the block in its world `w` (see
      `IndWorldLemmas`). -/
  ctorLemmas (field : FieldWorld) (blk : Block) (i : Nat) (w : Expr) (auxEqns : Array (Nat × Expr)) (c : Name) :
      MetaM (Option (Expr × Expr)) := do
    let tgt ← whnf blk.dt[i]!
    let src := mkAppN (mkConst c blk.us) blk.as
    let ctor' := mkAppN (mkConst c tgt.getAppFn.constLevels!) tgt.getAppArgs
    let some (eqn, ws) ← ctorEquation field blk w auxEqns src ctor' | return none
    return some (eqn, ← ctorImage w c src ctor' eqn ws)
  /-- The equation `∀ xs, W (C xs) = C' (Ŵ xs)` of the constructor `src` (`ctor'` in the target instance) in the
      world `w`, with the worlds `Ŵ` of its fields (`none` for the fields of the same type in both instances). -/
  ctorEquation (field : FieldWorld) (blk : Block) (w : Expr) (auxEqns : Array (Nat × Expr)) (src ctor' : Expr) :
      MetaM (Option (Expr × Array (Option Expr))) := do
    forallTelescope (← inferType src) fun xs _ => do
      let mut cty ← inferType ctor'
      let mut args := #[]
      let mut ws := #[]
      for x in xs do
        let .forallE _ g b _ ← whnf cty | return none
        let ft ← inferType x
        let (v, wi) ← if ← isDefEq ft g then pure (x, none)
          else if ft.hasAnyFVar (xs.contains <| mkFVar ·) then return none
          else match ← field ft g with
            | some (wx, _) => pure (applyWorld wx x, some wx)
            | none => return none
        args := args.push v
        ws := ws.push wi
        cty := b.instantiate1 v
      let lhs := applyWorld w (mkAppN src xs)
      let rhs := mkAppN ctor' args
      let some p ← congrCtor lhs rhs (fun a b => do
          for (k, e) in auxEqns do
            let pe := mkApp e a.appArg!
            let some (_, l, r) := (← inferType pe).eq? | continue
            if a.getAppFn.isConstOf blk.recs[k]! && (← isDefEq l a) && (← isDefEq r b) then return some pe
          return none)
        | return none
      return some (← mkAuxTheorem (← mkForallFVars xs (← mkEq lhs rhs)) (← mkLambdaFVars xs p), ws)
  /-- The image `∀ ys, Img W (C' ys) = (Img Ŵᵢ yᵢ ∧ …)` of the constructor `c` (`src` in the source instance,
      `ctor'` in the target instance) in the world `w`, from its equation `eqn` and the worlds `ws` of its fields (see
      `ctorEquation`). -/
  ctorImage (w : Expr) (c : Name) (src ctor' eqn : Expr) (ws : Array (Option Expr)) : MetaM Expr := do
    forallTelescope (← inferType ctor') fun ys _ => do
      if ys.size != ws.size then throwError "mkIndWorld: fields"
      let imgs ← (ys.zip ws).filterMapM fun (y, wi) => wi.mapM fun wx => mkAppM ``Img #[wx, y]
      let conj := if imgs.isEmpty then mkConst ``True else imgs.pop.foldr mkAnd imgs.back!
      let lhs ← mkAppM ``Img #[w, mkAppN ctor' ys]
      let mkConj (pfs : Array Expr) : MetaM Expr := do
        if pfs.isEmpty then return mkConst ``True.intro
        let mut acc := pfs.back!
        for p in pfs.pop.reverse do acc ← mkAppM ``And.intro #[p, acc]
        return acc
      -- `→`: the preimage is an application of `C` (injection), whose fields are the preimages of the `yᵢ`
      let mp ← withLocalDeclD `h (← whnfD lhs) fun h => do
        let g ← mkFreshExprSyntheticOpaqueMVar conj
        let #[sg] ← g.mvarId!.cases h.fvarId! | throwError "mkIndWorld: image"
        let #[x, hx] := sg.fields | throwError "mkIndWorld: image"
        for sg' in ← sg.mvarId.cases x.fvarId! do
          let .fvar hx := sg'.subst.get hx.fvarId! | throwError "mkIndWorld: image"
          let (hx, g) ← sg'.mvarId.withContext do
            let some (_, a, b) := (← hx.getType).eq? | throwError "mkIndWorld: equation expected"
            let (p, t) ← if sg'.ctorName == c then do
                let p ← mkEqTrans (mkFVar hx) (mkAppN eqn sg'.fields)
                pure (p, ← inferType p)
              else pure (mkFVar hx, ← mkEq a (← whnf b))
            sg'.mvarId.note `hx p t
          match ← injection g hx with
          | .solved => pure ()
          | .subgoal g eqs _ => g.withContext do
              -- the equations `yⱼ = Ŵⱼ xⱼ` of the fields that are not proofs, in order
              let nonProof ← (List.range ys.size).toArray.filterM fun j => do return !(← isProof ys[j]!)
              if eqs.size != nonProof.size then throwError "mkIndWorld: image"
              let mut pfs := #[]
              for (e, j) in eqs.zip nonProof do
                if let some wx := ws[j]! then
                  pfs := pfs.push (← mkImgIntro wx ys[j]! sg'.fields[j]! (mkFVar e))
              if pfs.size != imgs.size then throwError "mkIndWorld: image"
              g.assign (← mkConj pfs)
        mkLambdaFVars #[h] (← instantiateMVars g)
      -- `←`: the preimages `xᵢ` of the fields give the preimage `C xs`
      let mpr ← withLocalDeclD `h conj fun h => do
        -- the hypotheses `Img Ŵᵢ yᵢ`
        let mut hs := #[]
        let mut rest := h
        for k in [:imgs.size] do
          if k + 1 == imgs.size then hs := hs.push rest
          else
            hs := hs.push (← mkAppM ``And.left #[rest])
            rest ← mkAppM ``And.right #[rest]
        let rec elim (j k : Nat) (xs : Array Expr) (es : Array (Nat × Expr)) : MetaM Expr := do
          if h : j < ys.size then
            let some wx := ws[j]! | elim (j + 1) k (xs.push ys[j]) es
            let some (srcTy, _) := (← whnfD (← inferType hs[k]!)).app2? ``Exists | throwError "mkIndWorld: image"
            withLocalDeclD `x srcTy fun x => do
            withLocalDeclD `e (← mkEq ys[j] (applyWorld wx x)) fun e => do
              let b ← elim (j + 1) (k + 1) (xs.push x) (es.push (j, e))
              let p := mkLambda `x .default srcTy (← mkEq ys[j] (applyWorld wx (.bvar 0)))
              mkAppOptM ``Exists.elim #[srcTy, p, lhs, hs[k]!, ← mkLambdaFVars #[x, e] b]
          else
            -- `C' ys = C' (Ŵ xs) = W (C xs)`
            let some p ← congrCtor (mkAppN ctor' ys) (← inferType (mkAppN eqn xs)).appArg! (fun a _ => do
                return (es.find? (ys[·.1]! == a)).map (·.2))
              | throwError "mkIndWorld: image"
            let p ← mkEqTrans p (← mkEqSymm (mkAppN eqn xs))
            mkImgIntro w (mkAppN ctor' ys) (mkAppN src xs) p
        mkLambdaFVars #[h] (← elim 0 0 #[] #[])
      let pf ← mkAppM ``propext #[← mkAppM ``Iff.intro #[mp, mpr]]
      mkAuxTheorem (← mkForallFVars ys (← mkEq lhs conj)) (← mkLambdaFVars ys pf)

/-- The world of the Lean values of type `t` interpreted with type `d`, with a proof of its injectivity: `none` when
    `t` and `d` are the same type (worlds `Nat → Int` and `Bool → Prop` only occur below the type constructors, as
    in `α → Nat`; they are handled by the bridge otherwise). The construction is syntactic, such that the worlds
    of the interpretation (e.g., of the membership predicates) and of the bridge coincide. -/
partial def mkWorld (t d : Expr) : MetaM (Option (Expr × Expr)) := do
  if !hasUniv d then return none
  go t d
where
  /-- whether `t` is interpreted as itself -/
  same (t d : Expr) : MetaM Bool := do
    if t == d then return true
    withReducible (isDefEq t d)
  /-- the world of `t`, `@id t` when `t` is interpreted as itself -/
  goId (t d : Expr) : MetaM (Option (Expr × Expr)) := do
    if ← same t d then
      let u ← getLevel t
      return some (mkApp (mkConst ``id [u]) t, mkApp (mkConst ``id_injective [u]) t)
    go t d
  go (t d : Expr) : MetaM (Option (Expr × Expr)) := do
    if ← same t d then return none
    if let .const ``Univ [u] := d then
      if ← isDefEq (← inferType t) (mkSort u) then
        return some (mkApp (mkConst ``inj [u]) t, mkApp (mkConst ``inj_injective [u]) t)
      return none
    let t' ← whnfR t
    let d' ← whnfR d
    if t'.isConstOf ``Nat && d'.isConstOf ``Int then
      return some (mkApp2 (mkConst ``Nat.cast [levelZero]) (mkConst ``Int) (mkConst ``instNatCastInt),
                   mkConst ``natCast_injective)
    if t'.isConstOf ``Bool && d'.isProp then
      return some (mkLambda `b .default (mkConst ``Bool)
          (mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool) (.bvar 0) (mkConst ``Bool.true)),
        mkConst ``boolTrue_injective)
    match t', d' with
    | .forallE _ a b _, .forallE _ da c _ =>
        if b.hasLooseBVars || c.hasLooseBVars then return none
        let some (wa, ha) ← goId a da | return none
        let some (wb, hb) ← goId b c | return none
        -- outside of the domain: the identity for the functions of a sort into itself (e.g., `fun x => x`
        -- for the lambda terms of the encoding), a default value otherwise
        let dflt ← if (← same da c) then pure (mkLambda `x .default da (.bvar 0))
          else pure (mkLambda `x .default da (← mkDefault c))
        let w ← mkAppM ``liftFun #[wa, wb, dflt]
        let h ← mkAppM ``liftFun_injective #[ha, hb, dflt]
        return some (w, h)
    | _, _ => pure ()
    let functor (n : Name) (map : Name) (lem : Name) : MetaM (Option (Expr × Expr)) := do
      if !(t'.isAppOfArity n 1 && d'.isAppOfArity n 1) then return none
      let some (w, h) ← go t'.appArg! d'.appArg! | return none
      return some (← mkAppM map #[w], ← mkAppM lem #[h])
    if let some r ← functor ``List ``List.map ``listMap_injective then return some r
    if let some r ← functor ``Option ``Option.map ``optionMap_injective then return some r
    if t'.isAppOfArity ``Prod 2 && d'.isAppOfArity ``Prod 2 then
      let some (w₁, h₁) ← goId (t'.getArg! 0) (d'.getArg! 0) | return none
      let some (w₂, h₂) ← goId (t'.getArg! 1) (d'.getArg! 1) | return none
      return some (← mkAppM ``Prod.map #[w₁, w₂], ← mkAppM ``prodMap_injective #[h₁, h₂])
    -- other inductive types (e.g., datatypes of the user)
    if let some r ← mkIndWorld t' d' go then return some r
    -- definitions (e.g., `def Sequence α := List α`)
    let t'' ← whnfD t'
    let d'' ← whnfD d'
    if t'' != t' || d'' != d' then return ← go t'' d''
    return none

/-! ## Polymorphic functions

The Lean functions of the translation instantiated at sort variables (e.g., `@List.zipWith α β γ`) are translated as
SMT functions on `@Instance`, shared by all the instantiations at the sort variables of a universe. They are
interpreted at the universe (e.g., `@List.zipWith Univ Univ Univ`), such that their definitional axioms hold on all
the values of the universe (outside of the images of the worlds too). Their applications in the goal are related to
their interpretations by *naturality* lemmas proved once per function and instantiation (see `blaster_poly_nat` and
`Bridge.walkPolyApp`), e.g., `List.zipWith (liftFun (inj α) (liftFun (inj β) (inj γ) _) _ f) (List.map (inj α) xs)
(List.map (inj β) ys) = List.map (inj γ) (List.zipWith f xs ys)`.

NOTE: naturality only holds for parametric functions (e.g., not for axioms such as `hash : α → String`). -/

/-- Number of generic parameters of the Lean function `e` of the translation (abstracted over its generic parameters,
    see `Blaster.Optimize.getInstApp`), given the arity of its SMT function: the leading parameters that are not
    arguments of the SMT function. -/
def genericParams (e : Expr) (arity : Nat) : MetaM Nat :=
  lambdaTelescope e fun ps b => do
    let explicit ← forallTelescope (← inferType b) fun xs _ =>
      xs.filterM fun x => return (← x.fvarId!.getBinderInfo).isExplicit
    return ps.size + explicit.size - arity

/-- `e` with fresh universe level metavariables for the levels of its constants and of its sorts (except `Prop`),
    and the original levels. -/
def freshLevels (e : Expr) : StateT (Array (LMVarId × Level)) MetaM Expr :=
  Core.transform e (pre := fun s => do
    let fresh (l : Level) : StateT (Array (LMVarId × Level)) MetaM Level := do
      let m ← mkFreshLevelMVar
      modify (·.push (m.mvarId!, l))
      return m
    match s with
    | .const n ls => return .done (.const n (← ls.mapM fresh))
    | .sort l => if l.isZero then return .done s else return .done (.sort (← fresh l))
    | _ => return .continue)

/-- The Lean function `e` of the translation at the universe: its first `n` (generic) parameters are instantiated with
    `Univ.{u}` for the sort parameters of `Sort u`, and with synthesized instances for the instance parameters (`e`
    itself when an instance can't be synthesized, e.g., `BEq Univ`). The universe levels of the instance are inferred
    by type checking (e.g., `@List.zipWith.{u+1} Univ.{u+1}` for `@List.zipWith.{u} α` with `α : Type u`), the
    original levels otherwise. -/
def instantiateUniv (e : Expr) (n : Nat) : MetaM Expr := do
  let e := e.headBeta
  let mut binders := #[]
  let mut body := e
  for _ in [:n] do
    let .lam _ t b _ := body | break
    binders := binders.push t
    body := b
  if binders.isEmpty then return e
  try
    let (r, origs) ← (do
      let body ← freshLevels body
      let mut vals := #[]
      for t in binders do
        let t := t.instantiateRev vals
        if let .sort u := ← whnfR t then
          if u.isZero then throwError "instantiateUniv: proposition"
          vals := vals.push (mkConst ``Univ [u])
        else
          let t ← freshLevels t
          Meta.check t
          vals := vals.push (← synthInstance (← instantiateMVars t))
      let r := body.instantiateRev vals
      Meta.check r
      return r : StateT (Array (LMVarId × Level)) MetaM Expr).run #[]
    for (m, l) in origs do
      if !(← isLevelMVarAssigned m) then assignLevelMVar m l
    let r ← instantiateMVars r
    Meta.check r
    return r.headBeta
  catch _ => return e

/-- Proof of the injectivity of the world `w` (see `mkWorld`). -/
partial def worldInjective? (w : Expr) : MetaM (Option Expr) := do
  if let .lam _ (.const ``Bool _) (.app (.app (.app (.const ``Eq _) _) (.bvar 0)) (.const ``Bool.true _)) _ := w then
    return some (mkConst ``boolTrue_injective)
  let args := w.getAppArgs
  match w.getAppFn with
  | .const ``inj [u] => if args.size == 1 then return some (mkApp (mkConst ``inj_injective [u]) args[0]!)
  | .const ``id [u] => if args.size == 1 then return some (mkApp (mkConst ``id_injective [u]) args[0]!)
  | .const ``Nat.cast _ => if args.size == 2 then return some (mkConst ``natCast_injective)
  | .const ``liftFun _ =>
      if args.size == 7 then
        let some ha ← worldInjective? args[4]! | return none
        let some hb ← worldInjective? args[5]! | return none
        return some (← mkAppM ``liftFun_injective #[ha, hb, args[6]!])
  | .const ``List.map _ =>
      if args.size == 3 then
        if let some h ← worldInjective? args[2]! then return some (← mkAppM ``listMap_injective #[h])
  | .const ``Option.map _ =>
      if args.size == 3 then
        if let some h ← worldInjective? args[2]! then return some (← mkAppM ``optionMap_injective #[h])
  | .const ``Prod.map _ =>
      if args.size == 6 then
        let some h₁ ← worldInjective? args[4]! | return none
        let some h₂ ← worldInjective? args[5]! | return none
        return some (← mkAppM ``prodMap_injective #[h₁, h₂])
  | _ => pure ()
  return (← indWorldLemmas? w).map (·.inj)

/-- The theorems of the worlds of the inductive types occurring in `e` (see `IndWorldLemmas`), as terms for `simp`. -/
def indWorldSimpTerms (e : Expr) : TermElabM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := do
  let cache ← indWorldLemmasCache.get
  let env ← getEnv
  let mut res := #[]
  for n in e.getUsedConstants do
    let some l := cache.get? n | continue
    for t in l.thms do
      if t.getUsedConstants.all env.contains then
        res := res.push (← `(Lean.Parser.Tactic.simpLemma| $(← Term.exprToSyntax t):term))
  return res

/-- The theorems of the worlds of the inductive types occurring in the main goal (target and hypotheses), see
    `indWorldSimpTerms`. -/
def goalIndWorldSimpTerms : TacticM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := withMainContext do
  let mut e ← instantiateMVars (← getMainTarget)
  for d in ← getLCtx do
    if !d.isImplementationDetail then e := mkApp e (← instantiateMVars d.type)
  indWorldSimpTerms e

/-- Whether one of the tactics `attempts` (tried in order, the state being restored after each failure) closes all
    the goals. -/
def closeWithFirst (attempts : Array (TSyntax `tactic)) : TacticM Bool := do
  for t in attempts do
    let s ← saveState
    try
      evalTactic t
      if (← getGoals).isEmpty then return true
    catch _ => pure ()
    s.restore
  return false

syntax (name := blasterPolyInj) "blaster_poly_inj" : tactic

/-- Proofs of the injectivity of worlds (`Function.Injective w`, see `worldInjective?`). -/
@[tactic blasterPolyInj] def evalBlasterPolyInj : Tactic := fun _ => do
  let g ← getMainGoal
  let t ← whnfR (← instantiateMVars (← g.getType))
  if !t.isAppOfArity ``Function.Injective 3 then throwError "blaster_poly_inj: injectivity expected"
  let w := t.appArg!
  let some p ← worldInjective? (← instantiateMVars w) | throwError "blaster_poly_inj: unknown world {w}"
  g.assign p
  replaceMainGoal []

syntax (name := blasterPolySimp) "blaster_poly_simp" : tactic

/-- Simplification of the naturality statements (see `blaster_poly_nat`), with the lemmas of the worlds of the
    inductive types of the goal (see `IndWorldLemmas`). -/
@[tactic blasterPolySimp] def evalBlasterPolySimp : Tactic := fun _ => withMainContext do
  let extra ← goalIndWorldSimpTerms
  evalTactic (← `(tactic| simp_all [liftFun_apply, inj_injective, liftFun_injective, listMap_injective,
    optionMap_injective, prodMap_injective, id_injective, natCast_injective, boolTrue_injective, $extra,*]))

syntax (name := blasterPolyNat) "blaster_poly_nat" : tactic

/-- Proofs of the naturality statements `∀ αs xs, f Univ (W xs) = W (f αs xs)` (see `Bridge.walkPolyApp`): functional
    induction on `f αs xs` (the right-hand side), and simplification with the lemmas on the worlds. -/
@[tactic blasterPolyNat] def evalBlasterPolyNat : Tactic := fun _ => do
  evalTactic (← `(tactic| intros))
  let (app, f) ← withMainContext do
    let t ← instantiateMVars (← getMainTarget)
    let some (_, lhs, rhs) := t.eq? | throwError "blaster_poly_nat: equation expected"
    let some f := lhs.getAppFn.constName? | throwError "blaster_poly_nat: application expected"
    let some app := rhs.find? (·.isAppOf f) | throwError "blaster_poly_nat: application expected"
    return (app, f)
  let stx ← withMainContext (Term.exprToSyntax app)
  let fId := mkIdent f
  let attempts : Array (TSyntax `tactic) := #[
    ← `(tactic| (fun_induction $stx <;> blaster_poly_simp)),
    ← `(tactic| (fun_induction $stx <;> (try blaster_poly_simp) <;> blaster_poly_cases <;> blaster_poly_simp)),
    ← `(tactic| (fun_induction $stx <;> (try simp_all [$fId:ident]) <;> (try blaster_poly_cases) <;>
          blaster_poly_simp)),
    ← `(tactic| blaster_poly_simp)]
  if !(← closeWithFirst attempts) then throwError "blaster_poly_nat: failed"

syntax (name := blasterPoly) "blaster_poly" : tactic

/-- Proofs of the axioms of the encoding on the interpretation (e.g., the co-domain constraints and the
    extensionality of the functions of the encoding, the membership of the declared constants). -/
@[tactic blasterPoly] def evalBlasterPoly : Tactic := fun _ => do
  evalTactic (← `(tactic| intros))
  -- the lemmas of the worlds of the inductive types of the goal (see `IndWorldLemmas`)
  let extra ← goalIndWorldSimpTerms
  let attempts : Array (TSyntax `tactic) := #[
    ← `(tactic| exact img_self _ _),
    ← `(tactic| exact img_id (inj_injective _)),
    ← `(tactic| (apply ext_liftFun <;> assumption)),
    ← `(tactic| (apply ext_liftFun₂ (inj_injective _) <;> assumption)),
    ← `(tactic| (subst_vars; rfl)),
    ← `(tactic| (apply img_liftFun₂ (inj_injective _) (inj_injective _) <;> assumption)),
    ← `(tactic| (apply img_liftFun (inj_injective _) <;> assumption)),
    -- definitions of the membership predicates of the functors (e.g., `@isList`), on the cases of their arguments
    ← `(tactic| (blaster_poly_cases <;> simp_all [img_list_nil, img_list_cons, img_option_none, img_option_some,
          img_prod, img_self, liftFun_apply, inj_injective, listMap_injective, optionMap_injective, prodMap_injective,
          $extra,*])),
    -- the worlds of inductive types (see `mkIndWorld`)
    ← `(tactic| (apply img_id <;> blaster_poly_inj)),
    ← `(tactic| ((apply ext_liftFun₂ <;> try assumption) <;> blaster_poly_inj)),
    ← `(tactic| ((apply img_liftFun₂ <;> try assumption) <;> blaster_poly_inj)),
    ← `(tactic| ((apply img_liftFun <;> try assumption) <;> blaster_poly_inj))]
  if ← closeWithFirst attempts then return
  -- membership hypotheses on variables: the variables are substituted by their witnesses
  for _ in [0:16] do
    let h? ← withMainContext do
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let t ← instantiateMVars d.type
        if t.isAppOfArity ``Img 4 && t.appArg!.isFVar && !t.appFn!.containsFVar t.appArg!.fvarId! then
          return some d.toExpr
      return none
    let some h := h? | break
    let hs ← withMainContext <| Term.exprToSyntax h
    -- NOTE: `rfl` patterns are not recognized in quotations (hygiene)
    evalTactic (← `(tactic| (obtain ⟨_, h⟩ := $hs; subst h)))
  evalTactic (← `(tactic| (simp only [liftFun_apply, inj_injective, listMap_injective, optionMap_injective,
    id_injective, natCast_injective, boolTrue_injective, img_self, $extra,*] <;>
      first | done | omega | rfl | simp_all | grind)))

end Blaster.Reconstruct.SmtProof.Poly
