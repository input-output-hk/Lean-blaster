
import Tests.Smt.SmtNat.SmtNatAdd
import Tests.Smt.SmtNat.SmtNatDiv
-- SmtNatMod excluded from the suite: its mod queries do not terminate on z3 4.15.4
-- (a solver-version issue, unrelated to the backend). Re-enable on a newer z3.
-- import Tests.Smt.SmtNat.SmtNatMod
import Tests.Smt.SmtNat.SmtNatMul
import Tests.Smt.SmtNat.SmtNatPow
import Tests.Smt.SmtNat.SmtNatSub
