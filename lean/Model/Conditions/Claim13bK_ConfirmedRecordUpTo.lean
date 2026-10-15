import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedRecordUpTo

/-!
# The latest stable and confirmed blocks as ancestors of the honest heads, up to a slot

The conditions `RecordsAncestorOfHonestHeadsTo` and `RecordsSettledAtActionTicksTo`, over the slots
up to `sEnd`, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- At the configuration after `k` steps, every honest active member of the committee of every slot
    from `slot(x[k].time) + 2` to `sEnd` votes there for a descendant of `v`'s `latest_stable`, and
    for a descendant of `v`'s `latest_confirmed`. -/
def RecordsAncestorOfHonestHeadsTo (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (k : Nat) (sEnd : Slot) : Prop :=
  Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[k][v].st).st.core.latest_stable
      (S.E.slotOf (x[k].time : Int) + 2) sEnd ∧
    Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[k][v].st).st.core.latest_confirmed
      (S.E.slotOf (x[k].time : Int) + 2) sEnd

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- For every round `r` after the switch round, every tick step `n` at round `r`'s action time, and
    every member `v` of `HonRound` for round `r` such that `r` is the round after the switch round
    or `v` was asleep just before round `r − 1`'s action time, `v`'s `latest_stable` and
    `latest_confirmed` after `n + 1` steps are ancestors of every honest head from slot
    `slot(S.a r) + 2` to slot `sEnd`. -/
def RecordsSettledAtActionTicksTo (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (sEnd : Slot) : Prop :=
  ∀ (r : Round) (n : Nat) (v : V), Restated.switchRound M S tE + 1 ≤ r →
    Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r)) → v ∈ Restated.HonRound M S Sched r →
    (r = Restated.switchRound M S tE + 1 ∨ v ∉ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S (r - 1)) - 1)) →
    Restated.RecordsAncestorOfHonestHeadsTo M S Sched x v (n + 1) sEnd

end

end DecoupledConsensusModel.Sts.Restated
