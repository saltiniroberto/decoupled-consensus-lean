import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedRecord

/-!
# The latest stable and confirmed blocks as ancestors of the honest heads

The conditions `RecordsAncestorOfHonestHeads` and `RecordsSettledAtActionTicks`, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- At the configuration after `k` steps, every honest active member of the committee of every slot
    from `slot(x[k].time) + 2` on votes there for a descendant of `v`'s `latest_stable`, and for a
    descendant of `v`'s `latest_confirmed`. -/
def RecordsAncestorOfHonestHeads (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (k : Nat) : Prop :=
  Restated.AncestorOfHonestHeadsFrom M S Sched x (x[k][v].st).st.core.latest_stable
      (S.E.slotOf (x[k].time : Int) + 2) ∧
    Restated.AncestorOfHonestHeadsFrom M S Sched x (x[k][v].st).st.core.latest_confirmed
      (S.E.slotOf (x[k].time : Int) + 2)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- For every round `r` after the switch round, every tick step `n` at round `r`'s action time, and
    every member `v` of `HonRound` for round `r` such that `r` is the round after the switch round
    or `v` was asleep just before round `r − 1`'s action time, `v`'s `latest_stable` and
    `latest_confirmed` after `n + 1` steps are ancestors of every honest head from slot
    `slot(S.a r) + 2` on. -/
def RecordsSettledAtActionTicks (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) : Prop :=
  ∀ (r : Round) (n : Nat) (v : V), Restated.switchRound M S tE + 1 ≤ r →
    Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r)) → v ∈ Restated.HonRound M S Sched r →
    (r = Restated.switchRound M S tE + 1 ∨ v ∉ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S (r - 1)) - 1)) →
    Restated.RecordsAncestorOfHonestHeads M S Sched x v (n + 1)

end

end DecoupledConsensusModel.Sts.Restated
