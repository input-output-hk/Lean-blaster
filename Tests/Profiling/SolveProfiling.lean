import Lean
import PlutusCore.Integer
import Solver.Smt.Translate
import Solver.StateMachine.BMC
import Tests.Smt.Benchmarks.UPLC.Examples.Integer.Saturate
import Tests.Smt.Benchmarks.UPLC.Examples.Onchain.ProcessSCOrder
import Tests.StateMachine.Counter02

open Lean Elab Command Term Meta Solver.Options Solver.Optimize
open Tests.Uplc.Saturate (executeSaturate)
open Tests.Uplc.Onchain
open Tests.Uplc.Onchain.ProcessSCOrder
open PlutusCore.Integer (Integer)
open Test.Counter02 (counterStateMachine)


def runProcessOrder : CoreM Unit := do
  liftCommandElabM $ runTermElabM fun _ => do
   let stx ← `(∀ (x : ProcessSCInput), sto8 x)
   let opts := { (default : SolverOptions) with onlySmtLib := true, verbose := 2 }
   withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 500000000 }) $ do
     Solver.Smt.command opts stx.raw

def runSaturate : CoreM Unit := do
  liftCommandElabM $ runTermElabM fun _ => do
   let stx ← `(∀ (x r : Integer), x ≥ 0 → executeSaturate x = some r → r = x * (x + 1))
   let opts := { (default : SolverOptions) with verbose := 2 }
   withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 500000000 }) $ do
     Solver.Smt.command opts stx.raw

def bmcCounter02 : CoreM Unit := do
   liftCommandElabM $ runTermElabM fun _ => do
     let opts := { (default : SolverOptions) with maxDepth := 15, verbose := 2 }
     Solver.StateMachine.bmcCommand opts (← `(counterStateMachine)).raw

def failWith (msg : String) (exitCode : UInt8 := 1) : IO α := do
  (← IO.getStderr).putStrLn msg
  IO.Process.exit exitCode


def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  match args with
  | [ "saturate" ] =>
      let env ← importModules (loadExts := true) #[`Tests.Smt.Benchmarks.UPLC.Examples.Integer.Saturate] {}
      discard <| runSaturate |>.toIO { fileName := "<RunSolve>", fileMap := default } { env }
      IO.println "done"

  | [ "processOrder" ] =>
      let env ← importModules (loadExts := true) #[`Tests.Smt.Benchmarks.UPLC.Examples.Onchain.ProcessSCOrder] {}
      discard <| runProcessOrder |>.toIO { fileName := "<RunSolve>", fileMap := default } { env }
      IO.println "done"

  | [ "counter02" ] =>
      let env ← importModules (loadExts := true) #[{ module := `Tests.StateMachine.Counter02 }] {}
      discard <| bmcCounter02 |>.toIO { fileName := "<RunSolve>", fileMap := default } { env }
      IO.println "done"

  | _ => failWith "valid options := [saturate | processOrder | counter02]"

