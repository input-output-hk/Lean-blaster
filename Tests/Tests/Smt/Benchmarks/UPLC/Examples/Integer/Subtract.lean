import PlutusCore.Integer
import Tests.Smt.Benchmarks.UPLC.Builtins
import Tests.Smt.Benchmarks.UPLC.CekValue
import Tests.Smt.Benchmarks.UPLC.Examples.Utils
import Tests.Smt.Benchmarks.UPLC.Uplc
import Solver.Command.Syntax

namespace Tests.Uplc.SubtractInteger
open PlutusCore.Integer (Integer)
open UPLC.CekMachine
open UPLC.Uplc

/-! # Test cases with Valid result expected -/

def subtractInteger: Program :=
    (Program.Program (Version.Version 1 1 0)
    (Term.Lam "x"
      (Term.Lam "y"
        (Term.Apply
          (Term.Apply (Term.Builtin BuiltinFun.SubtractInteger) (Term.Var "x"))
          (Term.Var "y")
        )
      )
    ))

def executeSubtract (x : Integer) (y : Integer) : Option Integer :=
  executeIntProgram subtractInteger (intArgs2 x y) 20

#solve [executeSubtract 55 11 = some 44]

#solve [executeSubtract 55 75 = some (-20)]

#solve [executeSubtract 55 55 = some 0]

#solve [∀ (x y r : Integer), x < y → executeSubtract x y = some r → r < 0]

#solve [∀ (x y r : Integer), x ≥ y → executeSubtract x y = some r → r ≥ 0]

#solve [∀ (x y r : Integer), x = y → executeSubtract x y = some r → r = 0]

#solve [∀ (x y z r : Integer), x = z + y → executeSubtract x y = some r → r = z]

def absInteger : Program :=
  (Program.Program (Version.Version 1 1 0)
    (Term.Lam "n"
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Force (Term.Builtin BuiltinFun.IfThenElse))
            (Term.Apply
              (Term.Apply (Term.Builtin BuiltinFun.LessThanInteger) (Term.Var "n"))
              (Term.Const (Const.Integer 0))
            )
          )
          (Term.Apply
            (Term.Apply (Term.Builtin BuiltinFun.SubtractInteger) (Term.Const (Const.Integer 0)))
            (Term.Var "n")
          )
        )
        (Term.Var "n")
      )
    )
)

def executeAbs (x : Integer) : Option Integer :=
  executeIntProgram absInteger [integerToBuiltin x] 37

#solve [executeAbs (-127) = some 127]
#solve [executeAbs 1200 = some 1200]
#solve [executeAbs 0 = some 0]

#solve [∀ (x r : Integer), x > 0 → executeAbs x = some r → r = x]
#solve [∀ (x r : Integer), x ≤ 0 → executeAbs x = some r → r = -x]


def subOfSub: Program :=
    Program.Program (Version.Version 1 1 0)
    (Term.Lam "x"
      (Term.Lam "y"
        (Term.Lam "z"
          (Term.Apply
             (Term.Apply (Term.Builtin BuiltinFun.SubtractInteger)
               (Term.Apply
                 (Term.Apply (Term.Builtin BuiltinFun.SubtractInteger) (Term.Var "x"))
                 (Term.Var "y")
               )
             )
             (Term.Var "z")
          )
        )
      )
    )

def subOfAdd: Program :=
    Program.Program (Version.Version 1 1 0)
    (Term.Lam "x"
      (Term.Lam "y"
        (Term.Lam "z"
          (Term.Apply
             (Term.Apply (Term.Builtin BuiltinFun.SubtractInteger) (Term.Var "x"))
             (Term.Apply
               (Term.Apply (Term.Builtin BuiltinFun.AddInteger) (Term.Var "y"))
               (Term.Var "z")
             )
          )
        )
      )
    )

/-! equivalence between two uplc programs. -/
#solve [∀ (x y z : Integer),
          executeIntProgram subOfSub (intArgs3 x y z) 33 =
          executeIntProgram subOfAdd (intArgs3 x y z) 33
       ]


/-! # Test cases with Falsified result expected -/

#solve (gen-cex:0) (solve-result: 1) [∀ (x y : Integer), executeSubtract x y < x]

#solve (gen-cex:0) (solve-result: 1) [∀ (x y : Integer), executeSubtract x y > x]

def subOfMul: Program :=
    Program.Program (Version.Version 1 1 0)
    (Term.Lam "x"
      (Term.Lam "y"
        (Term.Lam "z"
          (Term.Apply
             (Term.Apply (Term.Builtin BuiltinFun.SubtractInteger) (Term.Var "x"))
             (Term.Apply
               (Term.Apply (Term.Builtin BuiltinFun.MultiplyInteger) (Term.Var "y"))
               (Term.Var "z")
             )
          )
        )
      )
    )

#solve (gen-cex: 0) (solve-result: 1)
  [∀ (x y z : Integer),
    executeIntProgram subOfSub (intArgs3 x y z) 33 =
    executeIntProgram subOfMul (intArgs3 x y z) 33
  ]

end Tests.Uplc.SubtractInteger
