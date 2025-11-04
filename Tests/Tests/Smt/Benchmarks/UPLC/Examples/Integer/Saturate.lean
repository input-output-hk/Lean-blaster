import PlutusCore.Integer
import Tests.Smt.Benchmarks.UPLC.Builtins
import Tests.Smt.Benchmarks.UPLC.CekValue
import Tests.Smt.Benchmarks.UPLC.Examples.Utils
import Tests.Smt.Benchmarks.UPLC.Uplc
import Solver.Command.Syntax

namespace Tests.Uplc.Saturate
open PlutusCore.Integer (Integer)
open UPLC.CekMachine
open UPLC.Uplc

/-! # Test cases with Valid result expected -/

def saturate : Program :=
    Program.Program (Version.Version 1 1 0)
    (Term.Apply
      (Term.Lam "go" (Term.Lam "x" (Term.Apply (Term.Apply (Term.Var "go") (Term.Var "x"))
                                   (Term.Const (Const.Integer 0)))))
      (Term.Apply
        (Term.Lam "s" (Term.Apply (Term.Var "s") (Term.Var "s")))
        (Term.Lam "s"
          (Term.Lam "n"
            (Term.Lam "count"
              (Term.Force
                (Term.Force
                  (Term.Apply
                    (Term.Apply
                      (Term.Apply
                        (Term.Force (Term.Builtin BuiltinFun.IfThenElse))
                        (Term.Apply (Term.Apply (Term.Builtin BuiltinFun.LessThanEqualsInteger) (Term.Var "n"))
                                    (Term.Const (Const.Integer 0)))
                      )
                      (Term.Delay (Term.Delay (Term.Var "count")))
                    )
                   (Term.Delay
                     (Term.Delay
                       (Term.Apply
                         (Term.Apply (Term.Lam "x" (Term.Apply (Term.Apply (Term.Var "s") (Term.Var "s"))
                                                               (Term.Var "x")))
                          (Term.Apply (Term.Apply (Term.Builtin BuiltinFun.SubtractInteger) (Term.Var "n"))
                                      (Term.Const (Const.Integer 1)))
                         )
                         (Term.Apply
                           (Term.Apply (Term.Builtin BuiltinFun.AddInteger) (Term.Var "count"))
                           (Term.Apply (Term.Apply (Term.Builtin BuiltinFun.MultiplyInteger)
                                                   (Term.Const (Const.Integer 2)))
                                       (Term.Var "n"))
                         )
                     )
                   )
                  )
                )
              )
            )
          )
        )
      )
     )
   )



def executeSaturate (x : Integer) : Option Int :=
  executeIntProgram saturate [integerToBuiltin x] 7100

-- NOTE: remove commented test cases once performance issue resolved.
-- /-- info: some 10100 -/
-- #guard_msgs in
--  #eval executeSaturate 100

-- /-- info: some 65792 -/
-- #guard_msgs in
--  #eval executeSaturate 256
#solve [∀ (x r : Integer), x ≥ 0 → executeSaturate x = some r → r = x * (x + 1)]


end Tests.Uplc.Saturate
