import Lean
import Blaster.Command.Syntax
import Blaster.Smt.Env
import Blaster.Smt.Term

open Lean Elab Command Term Meta Blaster.Syntax Blaster.Smt Blaster.Optimize Blaster.Options

namespace Blaster.StateMachine

/-- Internal Invariant representation for state machine -/
structure Invariant (α : Type) (β : Type) where
  /-- property to be satisified -/
  property : α → β → Prop
  /-- property label -/
  label : String
  /-- property status -/
  status : Result


/-- Internal state machine representation where:
      - α : specifies the input type
      - β : specifies the state type
-/
class StateMachine (α : Type) (β : Type) where
  /-- function to define the initial state -/
  init : α → β

  /-- function to define the next state -/
  next : α → β → β

  /-- function to define any assumption about the input events and state -/
  assumptions: α → β → Prop

  /-- function to define any properties to be satisfied -/
  invariants : α → β → Prop

open StateMachine

structure StateMachineEnv where
  inputType : Expr
  stateType : Expr
  smName : Name
  initFlag : Option SmtTerm -- init flag only used for k-induction
deriving Inhabited

abbrev StateMachineEnvT := StateRefT StateMachineEnv TranslateEnvT


/-- Return `StateMachine` const expression and cache result. -/
def mkStateMachineConst : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.StateMachine.StateMachine [levelZero])

/-- Return `Blaster.StateMachine.StateMachine.invariants` const expression and cache result. -/
def mkInvariants : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.StateMachine.StateMachine.invariants)

/-- Return `Blaster.StateMachine.StateMachine.assumptions` const expression and cache result. -/
def mkAssumptions : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.StateMachine.StateMachine.assumptions)

/-- Return `Blaster.StateMachine.StateMachine.init` const expression and cache result. -/
def mkInit : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.StateMachine.StateMachine.init)

/-- Return `Blaster.StateMachine.StateMachine.next` const expression and cache result. -/
def mkNext : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.StateMachine.StateMachine.next)


/-- Increment analysis depth -/
def incDepth : TranslateEnvT Unit := do
 modify (fun env => {env with optEnv.options.mcDepth := env.optEnv.options.mcDepth + 1})

def maxDepthReached : TranslateEnvT Bool := do
  let env ← get
  return env.optEnv.options.mcDepth > env.optEnv.options.solverOptions.maxDepth

def getMaxDepth : TranslateEnvT Nat := do
  return (← get).optEnv.options.solverOptions.maxDepth

def nameAtDepth (smName : Name) (suffix : String) : TranslateEnvT Name := do
  pure $ Name.mkStr1 (s!"{smName}.{suffix}@{← getCurrentDepth}")

def logDepthProgress (header : String) : TranslateEnvT Unit := do
  if (← get).optEnv.options.solverOptions.verbose > 0 then
    let d ← getCurrentDepth
    Blaster.emitProgress s!"{header} at Depth {d}" (some d)

def defineSmtInitFlag : TranslateEnvT SmtTerm := do
  let dflag := mkReservedSymbol s!"_InitFlag"
  declareConst dflag boolSort
  return (smtSimpleVarId dflag)

def defineInvAtDepth (inv : SmtTerm) : TranslateEnvT SmtTerm := do
  let invId := mkReservedSymbol s!"_inv@{← getCurrentDepth}"
  defineFun invId #[] boolSort inv
  return (smtSimpleVarId invId)

def defineSmtDepthFlag : TranslateEnvT SmtTerm := do
  let dflag := mkReservedSymbol s!"_DepthFlag.{← getCurrentDepth}"
  declareConst dflag boolSort
  return (smtSimpleVarId dflag)

def logNotInductiveAtDepth : TranslateEnvT Unit := do
  let sOpts := (← get).optEnv.options.solverOptions
  let ref ← blankRef
  let maxD ← getMaxDepth
  let d ← getCurrentDepth
  let msg := s!"Failed to establish induction up to Depth {maxD}"
  if isExpectedUndetermined sOpts.solveResult then
    Blaster.emitInfo ref s!"✅ Expected {msg}"
      [("type", .str "warning"), ("message", .str s!"Expected {msg}")] (some d)
  else
    Blaster.emitWarning ref s!"⚠️ {msg}"
      [("type", .str "warning"), ("message", .str msg)] (some d)
  -- dump smt commands submitted to backend solver when `dumpSmtLib` option is set.
  logSmtQuery
  discard $ exitSmt

def logNoCexAtDepth : TranslateEnvT Unit := do
  let maxD ← getMaxDepth
  let d ← getCurrentDepth
  let ref ← blankRef
  let msg := s!"No counterexample up to Depth {maxD}"
  Blaster.emitInfo ref s!"✅ {msg}"
    [("type", .str "result"), ("status", .str "no_cex"),
     ("message", .str msg)] (some d)
  discard $ exitSmt

def logUndeterminedAtDepth : TranslateEnvT Unit := do
  let d ← getCurrentDepth
  let ref ← blankRef
  let msg := s!"Undetermined at Depth {d}"
  Blaster.emitWarning ref s!"⚠️ {msg}"
    [("type", .str "warning"), ("message", .str msg)] (some d)
  discard $ exitSmt

def logCexAtDepth (r : Result) : TranslateEnvT Unit := do
  let d ← getCurrentDepth
  discard $ exitSmt
  logResult r (cexLabel := s!"Counterexample detected at Depth {d}") (depth := some d)
  (← IO.getStdout).flush

def logCtiAtDepth (r : Result) : TranslateEnvT Unit := do
  let sOpts := (← get).optEnv.options.solverOptions
  let d ← getCurrentDepth
  unless !sOpts.generateCex do
    logResult r
      (isCTI := true)
      (indLabel := s!"⚠️ Induction failed at Depth {d}")
      (cexLabel := s!"Counterexample to Induction")
      (depth := some d)
    (← IO.getStdout).flush

def logContradictionAtDepth : TranslateEnvT Unit := do
  -- dump smt commands submitted to backend solver when `dumpSmtLib` option is set.
  logSmtQuery
  discard $ exitSmt
  let d ← getCurrentDepth
  let ref ← blankRef
  let msg := s!"Contradictory context at Depth {d}"
  Blaster.emitError ref s!"❌ {msg}"
    [("type", .str "error"), ("message", .str msg)] (some d)


/-- Determine if `smInst` corresponds to a `StateMachine` instance
    and return a `StateMachineEnv` instance as result.
    Trigger an error when `smInst` is not a `StateMachine` instance.
-/
def getSMTypes (smInst : Expr) : TranslateEnvT StateMachineEnv := do
  let Expr.const n _ := smInst.getAppFn' | throwEnvError "StateMachine instance name expression expected !!!"
  let ConstantInfo.defnInfo info ← getConstEnvInfo n
    | throwEnvError "StateMachine instance definition expected !!!"
  let inst := if info.value.isLambda then betaLambda info.value smInst.getAppArgs else info.value
  Expr.withApp inst fun f args => do
   let Expr.const `Blaster.StateMachine.StateMachine.mk _ := f
     | throwEnvError "StateMachine instance expected but got {reprStr f} !!!"
   return {inputType := args[0]!, stateType := args[1]!, smName := n, initFlag := none}

/-- Given `smInst` an instance of `StateMachine`, `iVar` input at step k and `state` at step k,
     - assert `assumptions iVar state`
     - check if current smt context is contradictory
    Return `true` if context is contradictory
-/
def assertAssumptions (smInst : Expr) (iVar : Expr) (state : Expr) : StateMachineEnvT Bool := do
 let env ← get
 let currDepth ← getCurrentDepth
 translateAxioms currDepth
 let assumeExpr := mkApp5 (← mkAssumptions) env.inputType env.stateType smInst iVar state
 let optExpr ←
   profileTask
     s!"Optimizing assumptions at Depth {currDepth}"
     (Optimize.optimizeExpr assumeExpr)
     (verboseLevel := 2)
 trace[Translate.optExpr] "Optimizing assumptions at Depth {currDepth}: {← ppExpr optExpr}"
 match (toResult optExpr) with
 | .Undetermined =>
    let st ←
      profileTask
        s!"Translating assumptions at Depth {currDepth}"
        (translateExpr optExpr (topLevel := false))
        (verboseLevel := 2)
    -- assert assumption
    assertTerm st
    -- check for contradiction
    let res ←
      profileTask
        s!"Checking contradiction at Depth {currDepth}"
        (checkContradiction env.initFlag)
        (verboseLevel := 2)
    if isValidResult res then
      logContradictionAtDepth
      return true
    else return false
 | .Valid => return false
 | .Falsified .. =>
     logContradictionAtDepth
     return true

 where
   /-- Translate local axioms only when current depth is zero -/
   translateAxioms (currDepth) : TranslateEnvT Unit := do
     unless (currDepth != 0) do
      let axioms ← findLocalAxioms
      if !axioms.isEmpty then
        profileTask
          s!"Translating axioms at Depth {currDepth}"
          ( axioms.forM
            (fun e => do
              let st ← translateExpr (← Optimize.optimizeExpr e) (topLevel := false)
              assertTerm st
            ) )

   checkContradiction (initFlag : Option SmtTerm) : TranslateEnvT Result := do
     match initFlag with
     | none => checkSat
     | some iflag => checkSatAssuming #[iflag]

end Blaster.StateMachine
