import PlutusCore.Integer
import Tests.Smt.Benchmarks.UPLC.Builtins
import Tests.Smt.Benchmarks.UPLC.CekValue
import Tests.Smt.Benchmarks.UPLC.Examples.Utils
import Tests.Smt.Benchmarks.UPLC.Uplc
import Solver.Command.Syntax

namespace Tests.Uplc.Case
open PlutusCore.Integer (Integer)
open UPLC.CekMachine
open UPLC.Uplc

/-! # Test cases with Valid result expected -/

def verifyElem : Program :=
   Program.Program (Version.Version 1 1 0)
     (Term.Apply
       (Term.Lam "s" (Term.Apply (Term.Var "s") (Term.Var "s")))
       (Term.Lam "s"
         (Term.Lam "x"
           (Term.Lam "xs"
             (Term.Apply
               (Term.Apply
                 (Term.Apply
                   (Term.Apply (Term.Force (Term.Force (Term.Builtin BuiltinFun.ChooseList))) (Term.Var "xs"))
                   (Term.Lam "ds" (Term.Const (Const.Integer 0)))
                 )
                 (Term.Lam "ds"
                   (Term.Apply
                     (Term.Lam "hd"
                       (Term.Apply
                         (Term.Lam "tl"
                           (Term.Force
                             (Term.Force
                               (Term.Apply
                                 (Term.Apply
                                   (Term.Apply
                                     (Term.Force (Term.Builtin BuiltinFun.IfThenElse))
                                     (Term.Apply
                                       (Term.Apply (Term.Builtin BuiltinFun.EqualsInteger) (Term.Var "x"))
                                       (Term.Var "hd")
                                     )
                                    )
                                    (Term.Delay (Term.Delay (Term.Const (Const.Integer 1))))
                                  )
                                 (Term.Delay
                                   (Term.Delay
                                     (Term.Apply
                                       (Term.Apply (Term.Apply (Term.Var "s") (Term.Var "s")) (Term.Var "x"))
                                       (Term.Var "tl")
                                     )
                                   )
                                 )
                                )
                               )
                             )
                           )
                          (Term.Apply (Term.Force (Term.Builtin BuiltinFun.TailList)) (Term.Var "xs"))
                         )
                       )
                       (Term.Apply (Term.Force (Term.Builtin BuiltinFun.HeadList)) (Term.Var "xs"))
                     )
                   )
                 )
                 (Term.Constr 0 [])
               )
             )
           )
         )
       )

def verifyArgs (x : Integer) (xs : List Integer) : List Term :=
  let l := List.map (Const.Integer) xs
  [Term.Const (Const.Integer x), Term.Const (Const.ConstList l)]

def executeVerifier (x : Integer) (xs : List Integer) : Option Int :=
  executeIntProgram verifyElem (verifyArgs x xs) 1000

/-- info: some 0 -/
#guard_msgs in
  #eval executeVerifier 10 [3, 4]

/-- info: some 1 -/
#guard_msgs in
  #eval executeVerifier 10 [1, 3, 5, 10, 4]


end Tests.Uplc.Case
