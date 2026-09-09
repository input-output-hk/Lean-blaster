import Blaster.Optimize.Env.Instantiate
import Tests.Utils

open Lean Meta Elab Command Blaster.Optimize

namespace Tests.Issue227

-- Compare with Lean's native substitution, including open terms, unused/outer
-- variables, empty and nonzero ranges, and the same node at different depths.
run_cmd liftTermElabM do
  let check : TranslateEnvT Unit := do
    let nat ← hashcons (mkConst ``Nat)
    let closed ← (#[10, 20, 30] : Array Nat).mapM fun n => hashcons (mkRawNatLit n)
    let openArgs ← (#[.bvar 0, .bvar 2, .app (mkConst ``Nat.succ) (.bvar 1)] : Array Expr).mapM hashcons
    for args in #[closed, openArgs] do
      for start in [:args.size + 1] do
        for stop in [start:args.size + 1] do
          for idx in [:6] do
            let v ← mkBVarExpr idx
            let mut e := v
            for depth in [:5] do
              let inputs := #[e, Expr.app e v,
                Expr.forallE `x nat e .default,
                Expr.letE `x nat v e false,
                Expr.mdata {} e, Expr.proj ``Prod 0 e]
              for input in inputs do
                let input ← hashcons input
                let actual ← instantiateSharedRevRange input start stop args
                let expected := input.instantiateRevRange start stop args
                unless actual == expected do
                  throwError "shared substitution disagrees with Lean at range [{start}, {stop}), index {idx}, depth {depth}:\nactual: {repr actual}\nexpected: {repr expected}"
              e ← mkLambdaExpr `x .default nat e
    -- Beta reduction must consume only the requested argument slice, including
    -- when there are fewer lambdas than arguments (remaining arguments apply).
    let v ← mkBVarExpr 0
    let id ← mkLambdaExpr `x .default nat v
    let const ← mkLambdaExpr `x .default nat (← mkLambdaExpr `y .default nat (← mkBVarExpr 1))
    for f in #[id, const] do
      for args in #[closed, openArgs] do
        for start in [:args.size + 1] do
          for stop in [start:args.size + 1] do
            let actual ← betaLambdaSharedRange f start stop args
            let expected := f.beta (args.extract start stop)
            unless actual == expected do
              throwError "shared beta reduction disagrees with Lean at range [{start}, {stop}):\nactual: {repr actual}\nexpected: {repr expected}"
  check.run' (default : TranslateEnv)

#testOptimize ["BetaUnderBinders"]
  (fun x y : Nat => (fun a b : Nat => a + b) y x) ===>
  (fun x y : Nat => Nat.add x y)

#testOptimize ["BetaPreservesOuterVariable"]
  (fun x : Nat => (fun _y : Nat => fun _z : Nat => x) 10) ===>
  (fun x _z : Nat => x)

#blaster [∀ x y : Nat, (fun a b : Nat => a + b) y x = x + y]

end Tests.Issue227
