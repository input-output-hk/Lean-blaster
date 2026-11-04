import Lean
import Blaster.Optimize.Rewriting.Utils
import Blaster.Optimize.Env
import Blaster.Optimize.Lemmas.LemmasProp

open Lean Meta Elab
namespace Blaster.Optimize

/-- Apply the following COI reduction rule on `Exists`.
     - ∃ (n : t), e ===> e (if isSortOrInhabited t ∧ ¬ e.hasLooseBVar e 0). [proof: Blaster.exists_coi]
    Note that `∃ (n : t), e` is internally represented as `app (app Exists t) (lam n t e _)`.
    Assmes that f := Expr.const ``Exists
    An error is trigerred if args.size ≠ 2.
-/
def coiExists (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if args.size != 2 then throwEnvError "coiExists: two arguments expected but got {reprStr args}"
  match args[1]! with
  | Expr.lam _n t e _bi =>
      if (← (isSortOrInhabited t (existsQuantifier := true)) <&&> (pure !(e.hasLooseBVar 0))) then
        if let Expr.const _ [u] := f then
          -- when no instance is built here the replay synthesizes `Nonempty t`
          let inst ← nullaryCtorNonempty? u t
          pushProofStep (.rewrite (mkAppN (mkConst ``Blaster.exists_coi [u]) (#[t, e] ++ inst.toArray)))
        return e
      return mkAppN f args
  | _ => throwEnvError "coiExists: lambda expression expected but got {reprStr args[1]!}"


/-- Apply simplification/normalization rules on `Exists`. -/
def optimizeExists? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
  match f with
  | Expr.const ``Exists _ => coiExists f args
  | _ => pure none

end Blaster.Optimize
