import Tests.Smt.Benchmarks.UPLC.Builtins
import Tests.Smt.Benchmarks.UPLC.CekValue
import Tests.Smt.Benchmarks.UPLC.Examples.Utils
import Tests.Smt.Benchmarks.UPLC.Examples.Onchain.OrderPredicates
import Tests.Smt.Benchmarks.UPLC.PreProcess
import Tests.Smt.Benchmarks.UPLC.Uplc
import Solver.Command.Syntax

namespace Tests.Uplc.Onchain.ProcessSCOrder
open UPLC.CekMachine
open UPLC.CekValue (CekValue)
open UPLC.Uplc
open Tests.Uplc.Onchain

def processSCOrder : UPLC.Uplc.Program :=
  UPLC.Uplc.Program.Program (UPLC.Uplc.Version.Version 1 1 0)
    (
  UPLC.Uplc.Term.Lam "scMinRatio" (
    UPLC.Uplc.Term.Lam "scMinOperatorFee" (
      UPLC.Uplc.Term.Lam "scMaxOperatorFee" (
        UPLC.Uplc.Term.Lam "scOperatorFeeRatio" (
          UPLC.Uplc.Term.Lam "scBaseFeeBSC" (
            UPLC.Uplc.Term.Lam "scBaseFeeSSC" (
              UPLC.Uplc.Term.Lam "ds" (
                UPLC.Uplc.Term.Lam "minAdaTransfer" (
                  UPLC.Uplc.Term.Lam "@ds_1" (
                    UPLC.Uplc.Term.Case (
                      UPLC.Uplc.Term.Var "ds") [
                      (
                        UPLC.Uplc.Term.Lam "@ds_2" (
                          UPLC.Uplc.Term.Lam "@ds_3" (
                            UPLC.Uplc.Term.Lam "@ds_4" (
                              UPLC.Uplc.Term.Lam "@ds_5" (
                                UPLC.Uplc.Term.Lam "@ds_6" (
                                  UPLC.Uplc.Term.Lam "@ds_7" (
                                    UPLC.Uplc.Term.Case (
                                      UPLC.Uplc.Term.Var "@ds_1") [
                                      (
                                        UPLC.Uplc.Term.Lam "@ds_8" (
                                          UPLC.Uplc.Term.Lam "@ds_9" (
                                            UPLC.Uplc.Term.Lam "@ds_10" (
                                              UPLC.Uplc.Term.Apply (
                                                UPLC.Uplc.Term.Lam "nt" (
                                                  UPLC.Uplc.Term.Apply (
                                                    UPLC.Uplc.Term.Lam "cse" (
                                                      UPLC.Uplc.Term.Apply (
                                                        UPLC.Uplc.Term.Lam "f_buy" (
                                                          UPLC.Uplc.Term.Case (
                                                            UPLC.Uplc.Term.Apply (
                                                              UPLC.Uplc.Term.Apply (
                                                                UPLC.Uplc.Term.Apply (
                                                                  UPLC.Uplc.Term.Apply (
                                                                    UPLC.Uplc.Term.Force (
                                                                      UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                                    UPLC.Uplc.Term.Var "f_buy")) (
                                                                  UPLC.Uplc.Term.Lam "@ds_11" (
                                                                    UPLC.Uplc.Term.Case (
                                                                      UPLC.Uplc.Term.Var "scBaseFeeBSC") [
                                                                      (
                                                                        UPLC.Uplc.Term.Lam "n" (
                                                                          UPLC.Uplc.Term.Lam "d" (
                                                                            UPLC.Uplc.Term.Case (
                                                                              UPLC.Uplc.Term.Var "nt") [
                                                                              (
                                                                                UPLC.Uplc.Term.Lam "n'" (
                                                                                  UPLC.Uplc.Term.Lam "d'" (
                                                                                    UPLC.Uplc.Term.Constr 0 [
                                                                                      (
                                                                                        UPLC.Uplc.Term.Apply (
                                                                                          UPLC.Uplc.Term.Apply (
                                                                                            UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                            UPLC.Uplc.Term.Var "n")) (
                                                                                          UPLC.Uplc.Term.Var "n'")),
                                                                                      (
                                                                                        UPLC.Uplc.Term.Apply (
                                                                                          UPLC.Uplc.Term.Apply (
                                                                                            UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                            UPLC.Uplc.Term.Var "d")) (
                                                                                          UPLC.Uplc.Term.Var "d'")),
                                                                                    ]))),
                                                                            ]))),
                                                                    ]))) (
                                                                UPLC.Uplc.Term.Lam "@ds_12" (
                                                                  UPLC.Uplc.Term.Case (
                                                                    UPLC.Uplc.Term.Var "scBaseFeeSSC") [
                                                                    (
                                                                      UPLC.Uplc.Term.Lam "@n_1" (
                                                                        UPLC.Uplc.Term.Lam "@d_1" (
                                                                          UPLC.Uplc.Term.Case (
                                                                            UPLC.Uplc.Term.Var "nt") [
                                                                            (
                                                                              UPLC.Uplc.Term.Lam "@n'_1" (
                                                                                UPLC.Uplc.Term.Lam "@d'_1" (
                                                                                  UPLC.Uplc.Term.Constr 0 [
                                                                                    (
                                                                                      UPLC.Uplc.Term.Apply (
                                                                                        UPLC.Uplc.Term.Apply (
                                                                                          UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                          UPLC.Uplc.Term.Var "@n_1")) (
                                                                                        UPLC.Uplc.Term.Var "@n'_1")),
                                                                                    (
                                                                                      UPLC.Uplc.Term.Apply (
                                                                                        UPLC.Uplc.Term.Apply (
                                                                                          UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                          UPLC.Uplc.Term.Var "@d_1")) (
                                                                                        UPLC.Uplc.Term.Var "@d'_1")),
                                                                                  ]))),
                                                                          ]))),
                                                                  ]))) (
                                                              UPLC.Uplc.Term.Const UPLC.Uplc.Const.Unit)) [
                                                            (
                                                              UPLC.Uplc.Term.Lam "ipv" (
                                                                UPLC.Uplc.Term.Lam "@ipv_1" (
                                                                  UPLC.Uplc.Term.Apply (
                                                                    UPLC.Uplc.Term.Apply (
                                                                      UPLC.Uplc.Term.Apply (
                                                                        UPLC.Uplc.Term.Apply (
                                                                          UPLC.Uplc.Term.Force (
                                                                            UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                                          UPLC.Uplc.Term.Var "f_buy")) (
                                                                        UPLC.Uplc.Term.Lam "@ds_13" (
                                                                          UPLC.Uplc.Term.Apply (
                                                                            UPLC.Uplc.Term.Lam "@nt_1" (
                                                                              UPLC.Uplc.Term.Apply (
                                                                                UPLC.Uplc.Term.Apply (
                                                                                  UPLC.Uplc.Term.Apply (
                                                                                    UPLC.Uplc.Term.Apply (
                                                                                      UPLC.Uplc.Term.Force (
                                                                                        UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                                                      UPLC.Uplc.Term.Apply (
                                                                                        UPLC.Uplc.Term.Apply (
                                                                                          UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.LessThanInteger) (
                                                                                          UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 1000000000000000000))) (
                                                                                        UPLC.Uplc.Term.Var "@nt_1"))) (
                                                                                    UPLC.Uplc.Term.Lam "@ds_14" (
                                                                                      UPLC.Uplc.Term.Constr 0 [
                                                                                        (
                                                                                          UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Data (PlutusCore.Data.Data.Constr 7 []))),
                                                                                      ]))) (
                                                                                  UPLC.Uplc.Term.Lam "@ds_15" (
                                                                                    UPLC.Uplc.Term.Apply (
                                                                                      UPLC.Uplc.Term.Lam "conrep" (
                                                                                        UPLC.Uplc.Term.Apply (
                                                                                          UPLC.Uplc.Term.Lam "@nt_2" (
                                                                                            UPLC.Uplc.Term.Case (
                                                                                              UPLC.Uplc.Term.Var "@ds_4") [
                                                                                              (
                                                                                                UPLC.Uplc.Term.Lam "@n_2" (
                                                                                                  UPLC.Uplc.Term.Lam "@d_2" (
                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                      UPLC.Uplc.Term.Lam "@conrep_1" (
                                                                                                        UPLC.Uplc.Term.Case (
                                                                                                          UPLC.Uplc.Term.Var "scMinRatio") [
                                                                                                          (
                                                                                                            UPLC.Uplc.Term.Lam "@n'_2" (
                                                                                                              UPLC.Uplc.Term.Lam "@d'_2" (
                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                  UPLC.Uplc.Term.Lam "@conrep_2" (
                                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                                      UPLC.Uplc.Term.Lam "@conrep_3" (
                                                                                                                        UPLC.Uplc.Term.Apply (
                                                                                                                          UPLC.Uplc.Term.Apply (
                                                                                                                            UPLC.Uplc.Term.Apply (
                                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                                UPLC.Uplc.Term.Force (
                                                                                                                                  UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                                                    UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.LessThanInteger) (
                                                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                                                      UPLC.Uplc.Term.Apply (
                                                                                                                                        UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                                                                        UPLC.Uplc.Term.Var "@conrep_3")) (
                                                                                                                                      UPLC.Uplc.Term.Var "@nt_2"))) (
                                                                                                                                  UPLC.Uplc.Term.Var "@conrep_2"))) (
                                                                                                                              UPLC.Uplc.Term.Lam "@ds_16" (
                                                                                                                                UPLC.Uplc.Term.Constr 0 [
                                                                                                                                  (
                                                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                                                      UPLC.Uplc.Term.Apply (
                                                                                                                                        UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.ConstrData) (
                                                                                                                                        UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 0))) (
                                                                                                                                      UPLC.Uplc.Term.Apply (
                                                                                                                                        UPLC.Uplc.Term.Apply (
                                                                                                                                          UPLC.Uplc.Term.Force (
                                                                                                                                            UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MkCons)) (
                                                                                                                                          UPLC.Uplc.Term.Apply (
                                                                                                                                            UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IData) (
                                                                                                                                            UPLC.Uplc.Term.Apply (
                                                                                                                                              UPLC.Uplc.Term.Lam "r" (
                                                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                                                                      UPLC.Uplc.Term.Apply (
                                                                                                                                                        UPLC.Uplc.Term.Force (
                                                                                                                                                          UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                                                                                                                        UPLC.Uplc.Term.Apply (
                                                                                                                                                          UPLC.Uplc.Term.Apply (
                                                                                                                                                            UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.LessThanInteger) (
                                                                                                                                                            UPLC.Uplc.Term.Apply (
                                                                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                                                                UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                                                                                                UPLC.Uplc.Term.Var "@conrep_3")) (
                                                                                                                                                              UPLC.Uplc.Term.Var "r"))) (
                                                                                                                                                          UPLC.Uplc.Term.Var "@conrep_2"))) (
                                                                                                                                                      UPLC.Uplc.Term.Lam "@ds_17" (
                                                                                                                                                        UPLC.Uplc.Term.Apply (
                                                                                                                                                          UPLC.Uplc.Term.Apply (
                                                                                                                                                            UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.AddInteger) (
                                                                                                                                                            UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 1))) (
                                                                                                                                                          UPLC.Uplc.Term.Var "r")))) (
                                                                                                                                                    UPLC.Uplc.Term.Lam "@ds_18" (
                                                                                                                                                      UPLC.Uplc.Term.Var "r"))) (
                                                                                                                                                  UPLC.Uplc.Term.Const UPLC.Uplc.Const.Unit))) (
                                                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                                                  UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.QuotientInteger) (
                                                                                                                                                  UPLC.Uplc.Term.Var "@conrep_2")) (
                                                                                                                                                UPLC.Uplc.Term.Var "@conrep_3"))))) (
                                                                                                                                        UPLC.Uplc.Term.Apply (
                                                                                                                                          UPLC.Uplc.Term.Apply (
                                                                                                                                            UPLC.Uplc.Term.Force (
                                                                                                                                              UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MkCons)) (
                                                                                                                                            UPLC.Uplc.Term.Apply (
                                                                                                                                              UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IData) (
                                                                                                                                              UPLC.Uplc.Term.Var "@nt_2"))) (UPLC.Uplc.Term.Const (UPLC.Uplc.Const.ConstDataList []))))),
                                                                                                                                ]))) (
                                                                                                                            UPLC.Uplc.Term.Lam "@ds_19" (
                                                                                                                              UPLC.Uplc.Term.Constr 1 [
                                                                                                                                (
                                                                                                                                  UPLC.Uplc.Term.Constr 0 [
                                                                                                                                    (
                                                                                                                                      UPLC.Uplc.Term.Var "@nt_2"),
                                                                                                                                    (
                                                                                                                                      UPLC.Uplc.Term.Var "@nt_1"),
                                                                                                                                    (
                                                                                                                                      UPLC.Uplc.Term.Var "@ds_10"),
                                                                                                                                  ]),
                                                                                                                              ]))) (
                                                                                                                          UPLC.Uplc.Term.Const UPLC.Uplc.Const.Unit))) (
                                                                                                                      UPLC.Uplc.Term.Apply (
                                                                                                                        UPLC.Uplc.Term.Apply (
                                                                                                                          UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                                                          UPLC.Uplc.Term.Var "@d_2")) (
                                                                                                                        UPLC.Uplc.Term.Var "@d'_2")))) (
                                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                                      UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                                                      UPLC.Uplc.Term.Var "@conrep_1")) (
                                                                                                                    UPLC.Uplc.Term.Var "@n'_2"))))),
                                                                                                        ])) (
                                                                                                      UPLC.Uplc.Term.Apply (
                                                                                                        UPLC.Uplc.Term.Apply (
                                                                                                          UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                                          UPLC.Uplc.Term.Var "@nt_1")) (
                                                                                                        UPLC.Uplc.Term.Var "@n_2"))))),
                                                                                            ])) (
                                                                                          UPLC.Uplc.Term.Apply (
                                                                                            UPLC.Uplc.Term.Apply (
                                                                                              UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.AddInteger) (
                                                                                              UPLC.Uplc.Term.Var "@ds_8")) (
                                                                                            UPLC.Uplc.Term.Apply (
                                                                                              UPLC.Uplc.Term.Lam "@r_1" (
                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                      UPLC.Uplc.Term.Apply (
                                                                                                        UPLC.Uplc.Term.Force (
                                                                                                          UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                                                                        UPLC.Uplc.Term.Apply (
                                                                                                          UPLC.Uplc.Term.Apply (
                                                                                                            UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.LessThanInteger) (
                                                                                                            UPLC.Uplc.Term.Apply (
                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                                                UPLC.Uplc.Term.Var "@ipv_1")) (
                                                                                                              UPLC.Uplc.Term.Var "@r_1"))) (
                                                                                                          UPLC.Uplc.Term.Var "conrep"))) (
                                                                                                      UPLC.Uplc.Term.Lam "@ds_20" (
                                                                                                        UPLC.Uplc.Term.Apply (
                                                                                                          UPLC.Uplc.Term.Apply (
                                                                                                            UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.AddInteger) (
                                                                                                            UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 1))) (
                                                                                                          UPLC.Uplc.Term.Var "@r_1")))) (
                                                                                                    UPLC.Uplc.Term.Lam "@ds_21" (
                                                                                                      UPLC.Uplc.Term.Var "@r_1"))) (
                                                                                                  UPLC.Uplc.Term.Const UPLC.Uplc.Const.Unit))) (
                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                  UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.QuotientInteger) (
                                                                                                  UPLC.Uplc.Term.Var "conrep")) (
                                                                                                UPLC.Uplc.Term.Var "@ipv_1")))))) (
                                                                                      UPLC.Uplc.Term.Apply (
                                                                                        UPLC.Uplc.Term.Apply (
                                                                                          UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                          UPLC.Uplc.Term.Var "cse")) (
                                                                                        UPLC.Uplc.Term.Var "ipv"))))) (
                                                                                UPLC.Uplc.Term.Const UPLC.Uplc.Const.Unit))) (
                                                                            UPLC.Uplc.Term.Apply (
                                                                              UPLC.Uplc.Term.Apply (
                                                                                UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.AddInteger) (
                                                                                UPLC.Uplc.Term.Var "@ds_9")) (
                                                                              UPLC.Uplc.Term.Var "cse"))))) (
                                                                      UPLC.Uplc.Term.Lam "@ds_22" (
                                                                        UPLC.Uplc.Term.Apply (
                                                                          UPLC.Uplc.Term.Apply (
                                                                            UPLC.Uplc.Term.Apply (
                                                                              UPLC.Uplc.Term.Apply (
                                                                                UPLC.Uplc.Term.Force (
                                                                                  UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                                                UPLC.Uplc.Term.Apply (
                                                                                  UPLC.Uplc.Term.Apply (
                                                                                    UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.LessThanInteger) (
                                                                                    UPLC.Uplc.Term.Var "@ds_9")) (
                                                                                  UPLC.Uplc.Term.Apply (
                                                                                    UPLC.Uplc.Term.Apply (
                                                                                      UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.SubtractInteger) (
                                                                                      UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 0))) (
                                                                                    UPLC.Uplc.Term.Var "cse")))) (
                                                                              UPLC.Uplc.Term.Lam "@ds_23" (UPLC.Uplc.Term.Error))) (
                                                                            UPLC.Uplc.Term.Lam "@ds_24" (
                                                                              UPLC.Uplc.Term.Apply (
                                                                                UPLC.Uplc.Term.Lam "@nt_3" (
                                                                                  UPLC.Uplc.Term.Apply (
                                                                                    UPLC.Uplc.Term.Lam "@nt_4" (
                                                                                      UPLC.Uplc.Term.Apply (
                                                                                        UPLC.Uplc.Term.Lam "@nt_5" (
                                                                                          UPLC.Uplc.Term.Apply (
                                                                                            UPLC.Uplc.Term.Lam "@nt_6" (
                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                      UPLC.Uplc.Term.Force (
                                                                                                        UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                                                                      UPLC.Uplc.Term.Apply (
                                                                                                        UPLC.Uplc.Term.Apply (
                                                                                                          UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.EqualsInteger) (
                                                                                                          UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 0))) (
                                                                                                        UPLC.Uplc.Term.Var "@nt_6"))) (
                                                                                                    UPLC.Uplc.Term.Lam "@ds_25" (
                                                                                                      UPLC.Uplc.Term.Constr 0 [
                                                                                                        (
                                                                                                          UPLC.Uplc.Term.Apply (
                                                                                                            UPLC.Uplc.Term.Apply (
                                                                                                              UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.ConstrData) (
                                                                                                              UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 10))) (
                                                                                                            UPLC.Uplc.Term.Apply (
                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                UPLC.Uplc.Term.Force (
                                                                                                                  UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MkCons)) (
                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                  UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IData) (
                                                                                                                  UPLC.Uplc.Term.Var "@nt_4"))) (
                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                  UPLC.Uplc.Term.Force (
                                                                                                                    UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MkCons)) (
                                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                                    UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IData) (
                                                                                                                    UPLC.Uplc.Term.Var "@nt_5"))) (UPLC.Uplc.Term.Const (UPLC.Uplc.Const.ConstDataList []))))),
                                                                                                      ]))) (
                                                                                                  UPLC.Uplc.Term.Lam "@ds_26" (
                                                                                                    UPLC.Uplc.Term.Constr 1 [
                                                                                                      (
                                                                                                        UPLC.Uplc.Term.Constr 0 [
                                                                                                          (
                                                                                                            UPLC.Uplc.Term.Apply (
                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.AddInteger) (
                                                                                                                UPLC.Uplc.Term.Var "@ds_8")) (
                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                  UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.QuotientInteger) (
                                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                                      UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                                                      UPLC.Uplc.Term.Var "@nt_6")) (
                                                                                                                    UPLC.Uplc.Term.Var "ipv"))) (
                                                                                                                UPLC.Uplc.Term.Var "@ipv_1"))),
                                                                                                          (
                                                                                                            UPLC.Uplc.Term.Apply (
                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.AddInteger) (
                                                                                                                UPLC.Uplc.Term.Var "@ds_9")) (
                                                                                                              UPLC.Uplc.Term.Var "@nt_6")),
                                                                                                          (
                                                                                                            UPLC.Uplc.Term.Var "@ds_10"),
                                                                                                        ]),
                                                                                                    ]))) (
                                                                                                UPLC.Uplc.Term.Const UPLC.Uplc.Const.Unit))) (
                                                                                            UPLC.Uplc.Term.Apply (
                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                    UPLC.Uplc.Term.Force (
                                                                                                      UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                      UPLC.Uplc.Term.Apply (
                                                                                                        UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.LessThanInteger) (
                                                                                                        UPLC.Uplc.Term.Var "@nt_5")) (
                                                                                                      UPLC.Uplc.Term.Var "@nt_4"))) (
                                                                                                  UPLC.Uplc.Term.Lam "@ds_27" (
                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                      UPLC.Uplc.Term.Apply (
                                                                                                        UPLC.Uplc.Term.Apply (
                                                                                                          UPLC.Uplc.Term.Apply (
                                                                                                            UPLC.Uplc.Term.Force (
                                                                                                              UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                                                                            UPLC.Uplc.Term.Apply (
                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.LessThanEqualsInteger) (
                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                                    UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                                                    UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 1))) (
                                                                                                                  UPLC.Uplc.Term.Var "scMinOperatorFee"))) (
                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                  UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                                                  UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 1))) (
                                                                                                                UPLC.Uplc.Term.Var "@nt_5")))) (
                                                                                                          UPLC.Uplc.Term.Lam "@ds_28" (
                                                                                                            UPLC.Uplc.Term.Apply (
                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                                    UPLC.Uplc.Term.Force (
                                                                                                                      UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                                      UPLC.Uplc.Term.Apply (
                                                                                                                        UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.LessThanInteger) (
                                                                                                                        UPLC.Uplc.Term.Apply (
                                                                                                                          UPLC.Uplc.Term.Apply (
                                                                                                                            UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                                                            UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 0))) (
                                                                                                                          UPLC.Uplc.Term.Var "@ipv_1"))) (
                                                                                                                      UPLC.Uplc.Term.Apply (
                                                                                                                        UPLC.Uplc.Term.Apply (
                                                                                                                          UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                                                          UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 1))) (
                                                                                                                        UPLC.Uplc.Term.Var "ipv")))) (
                                                                                                                  UPLC.Uplc.Term.Lam "@ds_29" (
                                                                                                                    UPLC.Uplc.Term.Case (
                                                                                                                      UPLC.Uplc.Term.Var "scOperatorFeeRatio") [
                                                                                                                      (
                                                                                                                        UPLC.Uplc.Term.Lam "@n'_3" (
                                                                                                                          UPLC.Uplc.Term.Lam "@d'_3" (
                                                                                                                            UPLC.Uplc.Term.Apply (
                                                                                                                              UPLC.Uplc.Term.Lam "@conrep_4" (
                                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                                  UPLC.Uplc.Term.Lam "@conrep_5" (
                                                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                                                      UPLC.Uplc.Term.Apply (
                                                                                                                                        UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.SubtractInteger) (
                                                                                                                                        UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 0))) (
                                                                                                                                      UPLC.Uplc.Term.Case (
                                                                                                                                        UPLC.Uplc.Term.Apply (
                                                                                                                                          UPLC.Uplc.Term.Apply (
                                                                                                                                            UPLC.Uplc.Term.Apply (
                                                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                                                UPLC.Uplc.Term.Force (
                                                                                                                                                  UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                                                                    UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.EqualsInteger) (
                                                                                                                                                    UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 0))) (
                                                                                                                                                  UPLC.Uplc.Term.Var "@conrep_4"))) (
                                                                                                                                              UPLC.Uplc.Term.Lam "@ds_30" (UPLC.Uplc.Term.Error))) (
                                                                                                                                            UPLC.Uplc.Term.Lam "@ds_31" (
                                                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                                                                      UPLC.Uplc.Term.Force (
                                                                                                                                                        UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                                                                                                                      UPLC.Uplc.Term.Apply (
                                                                                                                                                        UPLC.Uplc.Term.Apply (
                                                                                                                                                          UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.LessThanInteger) (
                                                                                                                                                          UPLC.Uplc.Term.Var "@conrep_4")) (
                                                                                                                                                        UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 0)))) (
                                                                                                                                                    UPLC.Uplc.Term.Lam "@ds_32" (
                                                                                                                                                      UPLC.Uplc.Term.Constr 0 [
                                                                                                                                                        (
                                                                                                                                                          UPLC.Uplc.Term.Apply (
                                                                                                                                                            UPLC.Uplc.Term.Apply (
                                                                                                                                                              UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.SubtractInteger) (
                                                                                                                                                              UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 0))) (
                                                                                                                                                            UPLC.Uplc.Term.Var "@conrep_5")),
                                                                                                                                                        (
                                                                                                                                                          UPLC.Uplc.Term.Apply (
                                                                                                                                                            UPLC.Uplc.Term.Apply (
                                                                                                                                                              UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.SubtractInteger) (
                                                                                                                                                              UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 0))) (
                                                                                                                                                            UPLC.Uplc.Term.Var "@conrep_4")),
                                                                                                                                                      ]))) (
                                                                                                                                                  UPLC.Uplc.Term.Lam "@ds_33" (
                                                                                                                                                    UPLC.Uplc.Term.Constr 0 [
                                                                                                                                                      (
                                                                                                                                                        UPLC.Uplc.Term.Var "@conrep_5"),
                                                                                                                                                      (
                                                                                                                                                        UPLC.Uplc.Term.Var "@conrep_4"),
                                                                                                                                                    ]))) (
                                                                                                                                                UPLC.Uplc.Term.Const UPLC.Uplc.Const.Unit)))) (
                                                                                                                                          UPLC.Uplc.Term.Const UPLC.Uplc.Const.Unit)) [
                                                                                                                                        (
                                                                                                                                          UPLC.Uplc.Term.Lam "@n'_4" (
                                                                                                                                            UPLC.Uplc.Term.Lam "@d'_4" (
                                                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                                                  UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.QuotientInteger) (
                                                                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                                                                      UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                                                                                      UPLC.Uplc.Term.Var "@nt_5")) (
                                                                                                                                                    UPLC.Uplc.Term.Var "@n'_4"))) (
                                                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                                                                    UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                                                                                    UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 1))) (
                                                                                                                                                  UPLC.Uplc.Term.Var "@d'_4"))))),
                                                                                                                                      ]))) (
                                                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                                                      UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                                                                      UPLC.Uplc.Term.Var "@ipv_1")) (
                                                                                                                                    UPLC.Uplc.Term.Var "@d'_3")))) (
                                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                                  UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                                                                  UPLC.Uplc.Term.Var "ipv")) (
                                                                                                                                UPLC.Uplc.Term.Var "@n'_3"))))),
                                                                                                                    ]))) (
                                                                                                                UPLC.Uplc.Term.Lam "@ds_34" (
                                                                                                                  UPLC.Uplc.Term.Var "cse"))) (
                                                                                                              UPLC.Uplc.Term.Const UPLC.Uplc.Const.Unit)))) (
                                                                                                        UPLC.Uplc.Term.Lam "@ds_35" (
                                                                                                          UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 0)))) (
                                                                                                      UPLC.Uplc.Term.Const UPLC.Uplc.Const.Unit)))) (
                                                                                                UPLC.Uplc.Term.Lam "@ds_36" (
                                                                                                  UPLC.Uplc.Term.Var "cse"))) (
                                                                                              UPLC.Uplc.Term.Const UPLC.Uplc.Const.Unit)))) (
                                                                                        UPLC.Uplc.Term.Apply (
                                                                                          UPLC.Uplc.Term.Apply (
                                                                                            UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.SubtractInteger) (
                                                                                            UPLC.Uplc.Term.Var "@ds_7")) (
                                                                                          UPLC.Uplc.Term.Var "minAdaTransfer")))) (
                                                                                    UPLC.Uplc.Term.Case (
                                                                                      UPLC.Uplc.Term.Var "scOperatorFeeRatio") [
                                                                                      (
                                                                                        UPLC.Uplc.Term.Lam "@n_3" (
                                                                                          UPLC.Uplc.Term.Lam "@d_3" (
                                                                                            UPLC.Uplc.Term.Apply (
                                                                                              UPLC.Uplc.Term.Lam "@conrep_6" (
                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                  UPLC.Uplc.Term.Lam "@r_2" (
                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                      UPLC.Uplc.Term.Lam "@nt_7" (
                                                                                                        UPLC.Uplc.Term.Apply (
                                                                                                          UPLC.Uplc.Term.Apply (
                                                                                                            UPLC.Uplc.Term.Apply (
                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                UPLC.Uplc.Term.Force (
                                                                                                                  UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                                    UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.LessThanInteger) (
                                                                                                                    UPLC.Uplc.Term.Var "@nt_7")) (
                                                                                                                  UPLC.Uplc.Term.Var "scMinOperatorFee"))) (
                                                                                                              UPLC.Uplc.Term.Lam "@ds_37" (
                                                                                                                UPLC.Uplc.Term.Var "scMinOperatorFee"))) (
                                                                                                            UPLC.Uplc.Term.Lam "@ds_38" (
                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                                    UPLC.Uplc.Term.Force (
                                                                                                                      UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                                      UPLC.Uplc.Term.Apply (
                                                                                                                        UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.LessThanInteger) (
                                                                                                                        UPLC.Uplc.Term.Var "@nt_7")) (
                                                                                                                      UPLC.Uplc.Term.Var "scMaxOperatorFee"))) (
                                                                                                                  UPLC.Uplc.Term.Var "@nt_7")) (
                                                                                                                UPLC.Uplc.Term.Var "scMaxOperatorFee")))) (
                                                                                                          UPLC.Uplc.Term.Const UPLC.Uplc.Const.Unit))) (
                                                                                                      UPLC.Uplc.Term.Apply (
                                                                                                        UPLC.Uplc.Term.Apply (
                                                                                                          UPLC.Uplc.Term.Apply (
                                                                                                            UPLC.Uplc.Term.Apply (
                                                                                                              UPLC.Uplc.Term.Force (
                                                                                                                UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                  UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.LessThanInteger) (
                                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                                      UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                                                      UPLC.Uplc.Term.Var "@d_3")) (
                                                                                                                    UPLC.Uplc.Term.Var "@r_2"))) (
                                                                                                                UPLC.Uplc.Term.Var "@conrep_6"))) (
                                                                                                            UPLC.Uplc.Term.Lam "@ds_39" (
                                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                                  UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.AddInteger) (
                                                                                                                  UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 1))) (
                                                                                                                UPLC.Uplc.Term.Var "@r_2")))) (
                                                                                                          UPLC.Uplc.Term.Lam "@ds_40" (
                                                                                                            UPLC.Uplc.Term.Var "@r_2"))) (
                                                                                                        UPLC.Uplc.Term.Const UPLC.Uplc.Const.Unit)))) (
                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                      UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.QuotientInteger) (
                                                                                                      UPLC.Uplc.Term.Var "@conrep_6")) (
                                                                                                    UPLC.Uplc.Term.Var "@d_3")))) (
                                                                                              UPLC.Uplc.Term.Apply (
                                                                                                UPLC.Uplc.Term.Apply (
                                                                                                  UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                                  UPLC.Uplc.Term.Apply (
                                                                                                    UPLC.Uplc.Term.Apply (
                                                                                                      UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.SubtractInteger) (
                                                                                                      UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 0))) (
                                                                                                    UPLC.Uplc.Term.Var "@nt_3"))) (
                                                                                                UPLC.Uplc.Term.Var "@n_3"))))),
                                                                                    ]))) (
                                                                                UPLC.Uplc.Term.Apply (
                                                                                  UPLC.Uplc.Term.Apply (
                                                                                    UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.QuotientInteger) (
                                                                                    UPLC.Uplc.Term.Apply (
                                                                                      UPLC.Uplc.Term.Apply (
                                                                                        UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                        UPLC.Uplc.Term.Var "cse")) (
                                                                                      UPLC.Uplc.Term.Var "ipv"))) (
                                                                                  UPLC.Uplc.Term.Var "@ipv_1"))))) (
                                                                          UPLC.Uplc.Term.Const UPLC.Uplc.Const.Unit)))) (
                                                                    UPLC.Uplc.Term.Const UPLC.Uplc.Const.Unit)))),
                                                          ])) (
                                                        UPLC.Uplc.Term.Apply (
                                                          UPLC.Uplc.Term.Apply (
                                                            UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.LessThanEqualsInteger) (
                                                            UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 0))) (
                                                          UPLC.Uplc.Term.Var "cse")))) (
                                                    UPLC.Uplc.Term.Case (
                                                      UPLC.Uplc.Term.Case (
                                                        UPLC.Uplc.Term.Var "@ds_2") [
                                                        (
                                                          UPLC.Uplc.Term.Lam "m" (
                                                            UPLC.Uplc.Term.Lam "@n_4" (
                                                              UPLC.Uplc.Term.Lam "@ds_41" (
                                                                UPLC.Uplc.Term.Constr 0 [
                                                                  (
                                                                    UPLC.Uplc.Term.Var "m"),
                                                                  (
                                                                    UPLC.Uplc.Term.Var "@n_4"),
                                                                ])))),
                                                        (
                                                          UPLC.Uplc.Term.Lam "@m_1" (
                                                            UPLC.Uplc.Term.Lam "@n_5" (
                                                              UPLC.Uplc.Term.Constr 0 [
                                                                (
                                                                  UPLC.Uplc.Term.Var "@m_1"),
                                                                (
                                                                  UPLC.Uplc.Term.Var "@n_5"),
                                                              ]))),
                                                        (
                                                          UPLC.Uplc.Term.Lam "@n_6" (
                                                            UPLC.Uplc.Term.Lam "@ds_42" (
                                                              UPLC.Uplc.Term.Constr 0 [
                                                                (
                                                                  UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 0)),
                                                                (
                                                                  UPLC.Uplc.Term.Var "@n_6"),
                                                              ]))),
                                                        (
                                                          UPLC.Uplc.Term.Lam "@n_7" (
                                                            UPLC.Uplc.Term.Lam "@ds_43" (
                                                              UPLC.Uplc.Term.Constr 0 [
                                                                (
                                                                  UPLC.Uplc.Term.Var "@n_7"),
                                                                (
                                                                  UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 0)),
                                                              ]))),
                                                      ]) [
                                                      (
                                                        UPLC.Uplc.Term.Lam "@n_8" (
                                                          UPLC.Uplc.Term.Lam "@ds_44" (
                                                            UPLC.Uplc.Term.Var "@n_8"))),
                                                    ]))) (
                                                UPLC.Uplc.Term.Apply (
                                                  UPLC.Uplc.Term.Apply (
                                                    UPLC.Uplc.Term.Apply (
                                                      UPLC.Uplc.Term.Apply (
                                                        UPLC.Uplc.Term.Force (
                                                          UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                        UPLC.Uplc.Term.Apply (
                                                          UPLC.Uplc.Term.Apply (
                                                            UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.EqualsInteger) (
                                                            UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 0))) (
                                                          UPLC.Uplc.Term.Var "@ds_9"))) (
                                                      UPLC.Uplc.Term.Lam "@ds_45" (
                                                        UPLC.Uplc.Term.Var "@ds_4"))) (
                                                    UPLC.Uplc.Term.Lam "@ds_46" (
                                                      UPLC.Uplc.Term.Case (
                                                        UPLC.Uplc.Term.Apply (
                                                          UPLC.Uplc.Term.Apply (
                                                            UPLC.Uplc.Term.Apply (
                                                              UPLC.Uplc.Term.Apply (
                                                                UPLC.Uplc.Term.Force (
                                                                  UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                                UPLC.Uplc.Term.Apply (
                                                                  UPLC.Uplc.Term.Apply (
                                                                    UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.EqualsInteger) (
                                                                    UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 0))) (
                                                                  UPLC.Uplc.Term.Var "@ds_10"))) (
                                                              UPLC.Uplc.Term.Lam "@ds_47" (
                                                                UPLC.Uplc.Term.Constr 0 [
                                                                  (
                                                                    UPLC.Uplc.Term.Var "@ds_8"),
                                                                  (
                                                                    UPLC.Uplc.Term.Var "@ds_9"),
                                                                ]))) (
                                                            UPLC.Uplc.Term.Lam "@ds_48" (
                                                              UPLC.Uplc.Term.Case (
                                                                UPLC.Uplc.Term.Var "scBaseFeeBSC") [
                                                                (
                                                                  UPLC.Uplc.Term.Lam "@n_9" (
                                                                    UPLC.Uplc.Term.Lam "@d_4" (
                                                                      UPLC.Uplc.Term.Apply (
                                                                        UPLC.Uplc.Term.Lam "@conrep_7" (
                                                                          UPLC.Uplc.Term.Constr 0 [
                                                                            (
                                                                              UPLC.Uplc.Term.Apply (
                                                                                UPLC.Uplc.Term.Apply (
                                                                                  UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                  UPLC.Uplc.Term.Var "@ds_8")) (
                                                                                UPLC.Uplc.Term.Var "@d_4")),
                                                                            (
                                                                              UPLC.Uplc.Term.Var "@conrep_7"),
                                                                          ])) (
                                                                        UPLC.Uplc.Term.Apply (
                                                                          UPLC.Uplc.Term.Apply (
                                                                            UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                            UPLC.Uplc.Term.Var "@ds_9")) (
                                                                          UPLC.Uplc.Term.Var "@n_9"))))),
                                                              ]))) (
                                                          UPLC.Uplc.Term.Const UPLC.Uplc.Const.Unit)) [
                                                        (
                                                          UPLC.Uplc.Term.Lam "@ipv_2" (
                                                            UPLC.Uplc.Term.Lam "@ipv_3" (
                                                              UPLC.Uplc.Term.Apply (
                                                                UPLC.Uplc.Term.Apply (
                                                                  UPLC.Uplc.Term.Apply (
                                                                    UPLC.Uplc.Term.Apply (
                                                                      UPLC.Uplc.Term.Force (
                                                                        UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                                      UPLC.Uplc.Term.Case (
                                                                        UPLC.Uplc.Term.Var "@ds_4") [
                                                                        (
                                                                          UPLC.Uplc.Term.Lam "@n_10" (
                                                                            UPLC.Uplc.Term.Lam "@d_5" (
                                                                              UPLC.Uplc.Term.Apply (
                                                                                UPLC.Uplc.Term.Apply (
                                                                                  UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.LessThanInteger) (
                                                                                  UPLC.Uplc.Term.Apply (
                                                                                    UPLC.Uplc.Term.Apply (
                                                                                      UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                      UPLC.Uplc.Term.Var "@n_10")) (
                                                                                    UPLC.Uplc.Term.Var "@ipv_3"))) (
                                                                                UPLC.Uplc.Term.Apply (
                                                                                  UPLC.Uplc.Term.Apply (
                                                                                    UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                    UPLC.Uplc.Term.Var "@ipv_2")) (
                                                                                  UPLC.Uplc.Term.Var "@d_5"))))),
                                                                      ])) (
                                                                    UPLC.Uplc.Term.Lam "@ds_49" (
                                                                      UPLC.Uplc.Term.Var "@ds_4"))) (
                                                                  UPLC.Uplc.Term.Lam "@ds_50" (
                                                                    UPLC.Uplc.Term.Apply (
                                                                      UPLC.Uplc.Term.Apply (
                                                                        UPLC.Uplc.Term.Apply (
                                                                          UPLC.Uplc.Term.Apply (
                                                                            UPLC.Uplc.Term.Force (
                                                                              UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.IfThenElse)) (
                                                                            UPLC.Uplc.Term.Apply (
                                                                              UPLC.Uplc.Term.Apply (
                                                                                UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.EqualsInteger) (
                                                                                UPLC.Uplc.Term.Const (UPLC.Uplc.Const.Integer 0))) (
                                                                              UPLC.Uplc.Term.Var "@ds_10"))) (
                                                                          UPLC.Uplc.Term.Lam "@ds_51" (
                                                                            UPLC.Uplc.Term.Constr 0 [
                                                                              (
                                                                                UPLC.Uplc.Term.Var "@ds_8"),
                                                                              (
                                                                                UPLC.Uplc.Term.Var "@ds_9"),
                                                                            ]))) (
                                                                        UPLC.Uplc.Term.Lam "@ds_52" (
                                                                          UPLC.Uplc.Term.Case (
                                                                            UPLC.Uplc.Term.Var "scBaseFeeBSC") [
                                                                            (
                                                                              UPLC.Uplc.Term.Lam "@n_11" (
                                                                                UPLC.Uplc.Term.Lam "@d_6" (
                                                                                  UPLC.Uplc.Term.Apply (
                                                                                    UPLC.Uplc.Term.Lam "@conrep_8" (
                                                                                      UPLC.Uplc.Term.Constr 0 [
                                                                                        (
                                                                                          UPLC.Uplc.Term.Apply (
                                                                                            UPLC.Uplc.Term.Apply (
                                                                                              UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                              UPLC.Uplc.Term.Var "@ds_8")) (
                                                                                            UPLC.Uplc.Term.Var "@d_6")),
                                                                                        (
                                                                                          UPLC.Uplc.Term.Var "@conrep_8"),
                                                                                      ])) (
                                                                                    UPLC.Uplc.Term.Apply (
                                                                                      UPLC.Uplc.Term.Apply (
                                                                                        UPLC.Uplc.Term.Builtin UPLC.Uplc.BuiltinFun.MultiplyInteger) (
                                                                                        UPLC.Uplc.Term.Var "@ds_9")) (
                                                                                      UPLC.Uplc.Term.Var "@n_11"))))),
                                                                          ]))) (
                                                                      UPLC.Uplc.Term.Const UPLC.Uplc.Const.Unit)))) (
                                                                UPLC.Uplc.Term.Const UPLC.Uplc.Const.Unit)))),
                                                      ]))) (
                                                  UPLC.Uplc.Term.Const UPLC.Uplc.Const.Unit)))))),
                                    ]))))))),
                    ]))))))))))


#prep_uplc "compiledProcessSCOrder" processSCOrder [ProcessSCInput] orderInputToParams 5000


-- set_option pp.deepTerms.threshold 50000 in
-- set_option pp.deepTerms true in
-- set_option pp.maxSteps 50000 in
-- set_option trace.Translate.optExpr true in

-- STO7: Successful Buying Stablecoin Order
-- NOTE: Only one STO7 will be required once splitting of subgoals is implemented
def sto7_part1 (x : ProcessSCInput) : Prop :=
   isBuySCOrder x →
   validOrderInput x →
   x.state.crN_RC = 0 →
   successfulOrderImpliesPredicate (fromHaltState $ compiledProcessSCOrder x) (validBuySC x)

#solve [ ∀ (x : ProcessSCInput), sto7_part1 x ]

def sto7_part2 (x : ProcessSCInput) : Prop :=
   isBuySCOrder x →
   validOrderInput x →
   x.state.crN_RC ≠ 0 →
   successfulOrderImpliesPredicate (fromHaltState $ compiledProcessSCOrder x) (validBuySC x)

#solve [ ∀ (x : ProcessSCInput), sto7_part2 x ]

-- STO14: Min Ratio Violation for Buying Stablecoin Order
-- NOTE: Only one STO14 once splitting of subgoals is implemented
def sto14_part1 (x : ProcessSCInput) : Prop :=
  isBuySCOrder x →
  validOrderInput x →
  x.state.crN_SC = 0 →
  isInvalidMinReserveStatus (fromHaltState $ compiledProcessSCOrder x) →
  validMinRatioViolation x

#solve [ ∀ (x : ProcessSCInput), sto14_part1 x ]

def sto14_part2 (x : ProcessSCInput) : Prop :=
  isBuySCOrder x →
  validOrderInput x →
  x.state.crN_SC ≠ 0 →
  x.state.crN_RC ≠ 0 →
  isInvalidMinReserveStatus (fromHaltState $ compiledProcessSCOrder x) →
  validMinRatioViolation x

#solve  (random-seed: 2) [ ∀ (x : ProcessSCInput), sto14_part2 x ]

def sto14_part3 (x : ProcessSCInput) : Prop :=
  isBuySCOrder x →
  validOrderInput x →
  x.state.crN_SC ≠ 0 →
  x.state.crN_RC = 0 →
  x.orderRate < mkRatio x.state.crReserve x.state.crN_SC →
  isInvalidMinReserveStatus (fromHaltState $ compiledProcessSCOrder x) →
  validMinRatioViolation x

#solve [ ∀ (x : ProcessSCInput), sto14_part3 x ]

def sto14_part4 (x : ProcessSCInput) : Prop :=
  let totalPrice := fromInteger x.nbTokens * (priceSC x * x.scBaseFeeBSC)
  isBuySCOrder x →
  validOrderInput x →
  x.state.crN_SC ≠ 0 →
  x.state.crN_RC = 0 →
  x.orderRate ≥ mkRatio x.state.crReserve x.state.crN_SC →
  (ceil $ totalPrice) > (truncate $ totalPrice) →
  isInvalidMinReserveStatus (fromHaltState $ compiledProcessSCOrder x) →
  validMinRatioViolation x

#solve [ ∀ (x : ProcessSCInput), sto14_part4 x ]

def sto14_part5 (x : ProcessSCInput) : Prop :=
  let totalPrice := fromInteger x.nbTokens * (priceSC x * x.scBaseFeeBSC)
  isBuySCOrder x →
  validOrderInput x →
  x.state.crN_SC ≠ 0 →
  x.state.crN_RC = 0 →
  x.orderRate ≥ mkRatio x.state.crReserve x.state.crN_SC →
  (ceil $ totalPrice) ≤ (truncate $ totalPrice) →
  isInvalidMinReserveStatus (fromHaltState $ compiledProcessSCOrder x) →
  validMinRatioViolation x

#solve [ ∀ (x : ProcessSCInput), sto14_part5 x ]


-- STO35: Maximum Minting Violation for Buying Stablecoin Order
-- NOTE: Proved only with optimization rules
def sto35 (x : ProcessSCInput) : Prop :=
  isBuySCOrder x →
  validOrderInput x →
  isMaxStablecoinMintingReachedStatus (fromHaltState $ compiledProcessSCOrder x) →
  validMaxMintingViolation x

-- Proved only with optimization rules
#solve (only-optimize: 1) [ ∀ (x : ProcessSCInput), sto35 x ]

-- STO8: Successful Selling Stablecoin Order
def sto8 (x : ProcessSCInput) : Prop :=
  isSellSCOrder x →
  validOrderInput x →
  successfulOrderImpliesPredicate (fromHaltState $ compiledProcessSCOrder x) (validSellSC x)

#solve (only-optimize: 1) (solve-result: 2) [ ∀ (x : ProcessSCInput), sto8 x ]


-- STO45: Insufficient Operator’s Fees Violation for Selling Stablecoin Order
def sto45 (x : ProcessSCInput) : Prop :=
  isSellSCOrder x →
  validOrderInput x →
  isInsufficientOperatorFees (fromHaltState $ compiledProcessSCOrder x) →
  validInsufficientFeesForSellSC x

#solve (only-optimize: 1) (solve-result: 2) [ ∀ (x : ProcessSCInput), sto45 x ]

-- STO1: Non-Negative Djed Reserve (for successful orders)
-- STO2: Non-Negative N_SC
-- STO3: Non-Negative N_RC
-- STO4: Djed Reserve Backing Stablecoins
-- STO5: Djed Reserve Backing Reservecoins
def sto1_to_3_part1 (x : ProcessSCInput) : Prop :=
  validOrderInput x →
  x.nbTokens ≥ 0 →
  successfulOrderImpliesPredicate (fromHaltState $ compiledProcessSCOrder x) validReserve

#solve [ ∀ (x : ProcessSCInput), sto1_to_3_part1 x ]

def sto1_to_3_part2 (x : ProcessSCInput) : Prop :=
  validOrderInput x →
  x.nbTokens < 0 →
  successfulOrderImpliesPredicate (fromHaltState $ compiledProcessSCOrder x) validReserve

#solve (only-optimize: 1) (solve-result: 2) [ ∀ (x : ProcessSCInput), sto1_to_3_part2 x ]

-- Error is only triggered when:
--  - We have a selling order for N tokens;
--  - N > number of SC in circulation.
#solve [ ∀ (x : ProcessSCInput),
          validOrderInput x →
          isErrorState (compiledProcessSCOrder x) →
          -x.nbTokens > x.state.crN_SC
       ]

-- Function either triggers a error or terminates within the provided budget
#solve [ ∀ (x : ProcessSCInput),
          let res := compiledProcessSCOrder x
          validOrderInput x →
          isErrorState res ∨ isHaltState res
       ]

end Tests.Uplc.Onchain.ProcessSCOrder
