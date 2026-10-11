-- Root of the opt-in cvc5 test library (`lake build TestsCvc5`).
-- Every module here needs a cvc5 executable on PATH; the concurrent-mode
-- modules additionally need Z3. `CounterexampleSpike` is a diagnostic artifact
-- and intentionally not imported (see `COUNTEREXAMPLE_SPIKE.md`).
import TestsCvc5.Cvc5Capabilities
import TestsCvc5.Cvc5Floor
import TestsCvc5.SmtSolverCvc5
import TestsCvc5.SolverSelection
import TestsCvc5.ConcurrentSolvers
import TestsCvc5.ConcurrentDump
