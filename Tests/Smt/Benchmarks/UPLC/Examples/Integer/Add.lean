import PlutusCore.Integer
import Tests.Smt.Benchmarks.UPLC.Builtins
import Tests.Smt.Benchmarks.UPLC.CekValue
import Tests.Smt.Benchmarks.UPLC.Examples.Utils
import Tests.Smt.Benchmarks.UPLC.Uplc
import Solver.Command.Syntax

namespace Tests.Uplc.AddInteger
open PlutusCore.Integer (Integer)
open UPLC.CekMachine
open UPLC.Uplc

/-! # Test cases with Valid result expected -/

def addInteger: Program :=
    Program.Program (Version.Version 1 1 0)
    (Term.Lam "x"
      (Term.Lam "y"
        (Term.Apply
          (Term.Apply (Term.Builtin BuiltinFun.AddInteger) (Term.Var "x"))
          (Term.Var "y")
        )
      )
    )

def executeAdd (x : Integer) (y : Integer) : Option Int :=
  executeIntProgram addInteger (intArgs2 x y) 20

#solve [executeAdd 55 110 = some 165]

#solve [executeAdd (-55) 75 = some 20]

#solve [executeAdd (-124) 124 = some 0]

#solve [∀ (x y r : Integer), y ≥ 0 → executeAdd x y = some r → r >= x]

#solve [∀ (x y r : Integer), x ≥ 0 → executeAdd x y = some r → r >= y]

#solve [∀ (x y : Integer), executeAdd x y = executeAdd y x]

def mulDistr: Program :=
   Program.Program (Version.Version 1 1 0)
    (Term.Lam "x"
      (Term.Lam "y"
        (Term.Lam "z"
          (Term.Apply
             ( Term.Apply (Term.Builtin BuiltinFun.AddInteger)
                (Term.Apply
                  (Term.Apply (Term.Builtin BuiltinFun.MultiplyInteger) (Term.Var "x"))
                  (Term.Var "y")
                )
              )
              (Term.Apply
                (Term.Apply (Term.Builtin BuiltinFun.MultiplyInteger) (Term.Var "x"))
                (Term.Var "z")
              )
           )
         )
       )
     )

#solve [ ∀ (x y z : Integer),
           executeIntProgram mulDistr (intArgs3 x y z) 41 = some (x * (y + z))
       ]


def mulOverAdd: Program :=
   Program.Program (Version.Version 1 1 0)
    (Term.Lam "x"
      (Term.Lam "y"
        (Term.Lam "z"
          (Term.Apply
             (Term.Apply (Term.Builtin BuiltinFun.MultiplyInteger) (Term.Var "x"))
             (Term.Apply
               (Term.Apply (Term.Builtin BuiltinFun.AddInteger) (Term.Var "z"))
               (Term.Var "y")
             )
          )
        )
     )
   )

/-! equivalence between two uplc programs -/
#solve [ ∀ (x y z : Integer),
           executeIntProgram mulDistr (intArgs3 x y z) 41 =
           executeIntProgram mulOverAdd (intArgs3 x y z) 33
       ]

/-! # Test cases with Falsified result expected -/

#solve (gen-cex:0) (solve-result: 1) [∀ (x y : Integer), executeAdd x y < x]

#solve (gen-cex:0) (solve-result: 1) [∀ (x y : Integer), executeAdd x y > x]

def mulOverSub: Program :=
   Program.Program (Version.Version 1 1 0)
    (Term.Lam "x"
      (Term.Lam "y"
        (Term.Lam "z"
          (Term.Apply
             (Term.Apply (Term.Builtin BuiltinFun.MultiplyInteger) (Term.Var "x"))
             (Term.Apply
               (Term.Apply (Term.Builtin BuiltinFun.SubtractInteger) (Term.Var "z"))
               (Term.Var "y")
             )
          )
        )
     )
   )

#solve (gen-cex:0) (solve-result: 1)
  [ ∀ (x y z : Integer),
       executeIntProgram mulDistr (intArgs3 x y z) 41 =
       executeIntProgram mulOverSub (intArgs3 x y z) 33
  ]


end Tests.Uplc.AddInteger
