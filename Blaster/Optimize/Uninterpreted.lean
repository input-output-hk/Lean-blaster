import Lean

/-! Invocation-local uninterpreted functions, used by the automatic induction
of `Blaster.Proof`. The optimizer and the SMT translation treat such a function
as an arbitrary function of its type (one symbol per instantiation of its
implicit arguments). Lean's definitions are untouched and no axiom is
introduced: a proof found this way holds for the real function, while a
countermodel may be spurious. -/

namespace Blaster.Optimize
open Lean

private def uninterpretedOption (name : Name) : Name :=
  `Blaster.uninterpreted ++ name

private def equationsOption (name : Name) : Name :=
  `Blaster.uninterpretedEquations ++ name

/-- Keep `names` uninterpreted while running `action`. -/
def withUninterpretedFunctions [Monad m] [MonadWithOptions m] (names : Array Name)
    (action : m α) : m α :=
  withOptions (fun options => names.foldl
    (fun current name => current.setBool (uninterpretedOption name) true) options) action

/-- Keep the recursive definitions `names` uninterpreted, except for their
constructor equations: a call whose structural argument is a constructor is
unfolded by one step (`get? k [] = none`). One symbol then stands for the
definition everywhere, including under binders, without losing the base cases
a solver-level case split reveals. -/
def withUninterpretedRecursion [Monad m] [MonadWithOptions m] (names : Array Name)
    (action : m α) : m α :=
  withOptions (fun options => names.foldl
    (fun current name =>
      (current.setBool (uninterpretedOption name) true).setBool (equationsOption name) true)
    options) action

/-- Whether `name` is kept uninterpreted here. -/
def isUninterpreted (name : Name) : CoreM Bool :=
  return (← getOptions).getBool (uninterpretedOption name) false

/-- Whether the uninterpreted `name` keeps its constructor equations. -/
def hasConstructorEquations (name : Name) : CoreM Bool :=
  return (← getOptions).getBool (equationsOption name) false

end Blaster.Optimize
