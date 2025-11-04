import Solver.Command.Syntax
import Tests.Smt.Benchmarks.ValidatorsExamples.PlutusLedgerAPI.VDummy
import Tests.Smt.Benchmarks.ValidatorsExamples.Vesting.Types

open Tests.ValidatorsExamples.PlutusLedgerAPI

namespace Tests.ValidatorsExamples.Vesting

def validScriptContext : POSIXTime -> ScriptContext -> Bool :=
    fun time sc =>
        (sc.transaction.validity_range.lower_bound <= time.time && time.time <= sc.transaction.validity_range.upper_bound)
        && (sc.transaction.validity_range.lower_bound <= sc.transaction.validity_range.upper_bound)

def buggy_check_keys : List VerificationKeyHash -> VerificationKeyHash -> Nat -> Bool :=
    fun keys key checked =>
        match checked with
        | 10 => True
        | _ => match keys with
                | [] => false
                | hd_key :: rest =>
                    if (hd_key.hash == key.hash) then true
                                                 else buggy_check_keys rest key (checked + 1)

def signed_by : List VerificationKeyHash ->  VerificationKeyHash -> Demo -> Bool :=
    fun keys key demo =>
        match demo.buggy with
        | true =>  -- Check only if it is in the first 10 keys, if not found return True
            buggy_check_keys keys key 0
        | false => -- Check if it is in the keys
            keys.contains key

def time_elapsed : ValidityRange -> POSIXTime -> Bool :=
    fun range time =>
        range.lower_bound >= time.time

def validator : Demo -> VestingDatum -> VestingRedeemer -> ScriptContext -> Bool :=
    fun demo datum _ sc =>
        let transaction := sc.transaction;
        let purpose := sc.purpose;
        let signatories := transaction.signatories;
        let v_range := transaction.validity_range
        (purpose == Purpose.Spending) && (signed_by signatories datum.beneficiary demo) && (time_elapsed v_range datum.lock_until)

def validator' : Demo -> VestingDatum -> VestingRedeemer -> ScriptContext -> Bool :=
    fun demo d _r sc =>
        (sc.purpose == Purpose.Spending) && (signed_by sc.transaction.signatories d.beneficiary demo)

theorem only_accept_if_signatory_and_time_elapsed :
        ∀ (datum: VestingDatum) (redeemer: VestingRedeemer) (c : ScriptContext) (time: POSIXTime),

            ((validator (Demo.mk false) datum redeemer c)
            &&
            (validScriptContext time c))

            →

            (c.transaction.signatories.contains datum.beneficiary
            &&
            time.time ≥ datum.lock_until.time) :=

            by
                intros datum _redeemer sc h1
                simp [validator, validScriptContext, signed_by, time_elapsed]
                intros _ sc_signatories lock_lb lb_time _ _
                constructor
                . exact sc_signatories
                . exact Nat.le_trans lock_lb lb_time

theorem only_accept_if_signatory_and_time_elapsed_bugged :
        ∀ (datum: VestingDatum) (redeemer: VestingRedeemer) (c : ScriptContext) (time: POSIXTime),

            ((validator (Demo.mk true) datum redeemer c)
            &&
            (validScriptContext time c))

            →

            (c.transaction.signatories.contains datum.beneficiary
            &&
            time.time ≥ datum.lock_until.time)  :=

            by
                intros d r sc t
                simp [validator, validScriptContext, signed_by, time_elapsed]
                intros h_purpose h_signatories h_dtime_lb h_lb_time h_time_ub h_time_lb_ub
                constructor
                . sorry -- This is the buggy case
                . exact Nat.le_trans h_dtime_lb h_lb_time

theorem reject_other_purposes :
        ∀ (datum: VestingDatum) (redeemer: VestingRedeemer) (c : ScriptContext) (demo : Demo),
            !(c.purpose == Purpose.Spending)
            →
            !(validator demo datum redeemer c):=

            by
                simp [validator]
                intros _ _ _ _ h1
                constructor
                simp [h1]

theorem if_accepted_then_purpose_spend :
        ∀ (datum: VestingDatum) (redeemer: VestingRedeemer) (c : ScriptContext) (demo : Demo),
            validator demo datum redeemer c
            →
            c.purpose == Purpose.Spending :=

            by
                simp [validator]
                intros _ _ _ _ h1 _ _
                exact h1

#solve [if_accepted_then_purpose_spend]

#solve [reject_other_purposes]

#solve [only_accept_if_signatory_and_time_elapsed]

#solve (gen-cex: 0) (solve-result: 1) [only_accept_if_signatory_and_time_elapsed_bugged]

end Tests.ValidatorsExamples.Vesting
