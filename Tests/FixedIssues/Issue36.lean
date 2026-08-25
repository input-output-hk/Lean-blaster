import Lean
import Blaster

namespace Tests.Issue35

-- Issue: createPredQualifierAppAux: predicate declaration expected for Lean.Expr.app
--          (Lean.Expr.app (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
--            (Lean.Expr.const `String []))
--          (Lean.Expr.const `Tests.Issue35.MyNat [])
--
--        Raised whenever an `abbrev` appears anywhere in the return type of a function
--        Blaster cannot unfold -- an `opaque`, typically. Nothing is falsified and no
--        goal is returned: translation aborts.
--
-- Diagnosis: `generateUndeclaredFun` (Smt/Translate/Application.lean) normalizes the
--            return type inconsistently between the two uses it makes of it.
--
--            To build the declared sort it goes through `translateFunLambdaParamType`
--            -> `translateType`, which resolves abbreviations first
--            (Smt/Translate/Quantifier.lean:1354, `removeTypeAbbrev`), so the sort and
--            its well-formedness predicate are registered under the *reduced* type.
--
--            To assert the codomain constraint it then calls
--            `createPredQualifierAppAux f_applyTerm retType` with the *raw* `retType`
--            (Application.lean:767, and :772 for the nullary case). The lookup key no
--            longer matches what was registered, `getPredicateDeclaration` returns none
--            and Quantifier.lean:635 throws.
--
--            `createPredQualifierAppAux`'s own docstring states the precondition those
--            two call sites violate:
--              "Assume that there is no type abbreviation in `t`, i.e., call to
--               removeTypeAbbrev has been applied."
--
--            Argument types are unaffected -- they only ever go through `translateType`,
--            which reduces (see `argAbbrevIsFine` below).
--
--            Application.lean:402 (`toType`) and :829 (`t`) pass types through the same
--            entry point and are worth auditing alongside the fix.

set_option warn.sorry false

abbrev MyNat := Nat

structure Pt where
  a : Nat
  b : Nat

abbrev MyPt := Pt

inductive Wrap (α : Type)
  | box : α → Wrap α
  | nil

-- Every declaration below is an `opaque`, i.e. one Blaster has to declare rather than
-- unfold. Only the return type differs.
opaque viaExcept  (b : Nat)   : Except String MyNat := .error "x"
opaque viaBare    (b : Nat)   : MyNat               := 0
opaque viaOption  (b : Nat)   : Option MyNat        := none
opaque viaUserInd (b : Nat)   : Wrap MyNat          := .nil
opaque viaStruct  (b : Nat)   : Except String MyPt  := .error "x"
opaque viaArg     (b : MyNat) : Except String Nat   := .error "x"

-- Reference point: the same type reached through a binder rather than through an
-- undeclared function's codomain translates, so the type itself is fully supported and
-- the defect is confined to the codomain-constraint lookup.
#blaster (gen-cex: 0) (solve-result: 1)
  [∀ (r : Except String MyNat), match r with | .ok _ => True | .error _ => False]

-- An abbrev in an *argument* is fine.
#blaster (gen-cex: 0) (solve-result: 1)
  [∀ b, match viaArg b with | .ok _ => True | .error _ => False]

-- Spelling the abbrev out in the return type is the workaround, and is what makes the
-- five commands below the only difference from a working translation.
opaque spelledOut (b : Nat) : Except String Nat := .error "x"

#blaster (gen-cex: 0) (solve-result: 1)
  [∀ b, match spelledOut b with | .ok _ => True | .error _ => False]

-- The bug is invisible when both match branches agree: the optimizer collapses the term
-- to `True` and nothing is ever translated. A repro has to make the branches differ.
#blaster [∀ b, match viaExcept b with | .ok _ => True | .error _ => True]

-- The five failing shapes. Each aborts with the error quoted above; the expectations
-- below are the post-fix ones.
#blaster (gen-cex: 0) (solve-result: 1)
  [∀ b, match viaExcept b with | .ok _ => True | .error _ => False]

#blaster (gen-cex: 0) (solve-result: 1) [∀ b, viaBare b = 0]

#blaster (gen-cex: 0) (solve-result: 1)
  [∀ b, match viaOption b with | some _ => True | none => False]

#blaster (gen-cex: 0) (solve-result: 1)
  [∀ b, match viaUserInd b with | .box _ => True | .nil => False]

#blaster (gen-cex: 0) (solve-result: 1)
  [∀ b, match viaStruct b with | .ok _ => True | .error _ => False]

end Tests.Issue35
