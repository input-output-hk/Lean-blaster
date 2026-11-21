import Tests.Utils

namespace Tests.SolverOptions

/-- info: default solver options ✅ Success! -/
#guard_msgs in
#testOptimize ["default solver options"] True ===> True

-- Invalid options must be parsed instead of silently ignored.
/--
error: unexpected syntax
  #testOptimize["invalid solver option"](verbose:7)(only-optimize:2)True===>True
-/
#guard_msgs in
#testOptimize ["invalid solver option"] (verbose: 7) (only-optimize: 2)
  True ===> True

/-- info: supplied solver options ✅ Success! -/
#guard_msgs in
#testOptimize ["supplied solver options"] (verbose: 7) (unfold-depth: 3) (norm-result: 1)
  1 + 1 ===> 2

open Lean Elab Command Blaster.Syntax in
elab "#checkOptimizerOptions" : command => do
  let stx ← `(command| #testOptimize ["options"] (verbose: 7) (unfold-depth: 3) True ===> True)
  let opts ← parseSolveOptions stx.raw[2].getArgs default
  let (_, env) ← runTermElabM fun _ =>
    Blaster.Optimize.command opts (mkConst ``True)
  let actual := env.optEnv.options.solverOptions
  unless actual.verbose == 7 && actual.unfoldDepth == 3 do
    throwError "optimizer did not receive the requested solver options"

#checkOptimizerOptions

end Tests.SolverOptions
