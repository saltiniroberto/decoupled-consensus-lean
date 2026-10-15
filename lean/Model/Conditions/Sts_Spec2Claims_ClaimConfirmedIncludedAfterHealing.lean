import Model.Sts.Spec2Claims.ClaimConfirmedIncludedAfterHealing
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Record.Wiring

/-!
# Inclusion into confirmed outputs after healing

The inclusion of honest proposals in the confirmed outputs after a phase, the monotonicity of those
outputs, and the statement that both hold, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every slot `s` with proposal instant at or after `tE` whose proposer is not held up to `s`'s
    vote instant: if the proposer is awake from `M.proposal_wake_start S s` to the proposal instant,
    it sends a block of slot `s` at that instant; and every block it sent by `s`'s vote instant is
    an ancestor of the confirmed output of every validator honest through its read and awake
    throughout the vote window of its read's slot, at every read from the proposal instant plus the
    confirmation delay on. -/
def ConfirmedIncludedAfterHealing (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) : Prop :=
  ∀ s : Slot,
    tE ≤ M.proposal_time S.E s →
    HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s) →
    (S.E.proposer s ∈ Sched.awakeThroughout (M.proposal_wake_start S s)
        (M.proposal_time S.E s) →
      ∃ (i : Nat) (B : Block V), Restated.proposedBlockAtStep M S x i s B ∧
        (x[i].time : Int) = M.proposal_time S.E s) ∧
    ∀ (i : Nat) (B : Block V), Restated.proposedBlockAtStep M S x i s B →
      (x[i].time : Int) ≤ M.vote_time S.E s →
      ∀ (v : V) (j : Nat), Restated.HonestThrough M Sched x j v →
        M.proposal_time S.E s + confirmedInclusionDelay S ≤ (x[j].time : Int) →
        v ∈ activeAtW S Sched (S.E.slotOf (x[j].time : Int)) →
        Block.Preceq B (Restated.Read.confirmed M x[j][v].st)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- From `tE` on, a validator honest through the later of two reads holds, at the later read, a
    confirmed output that is a descendant of the one it held at the earlier read, whether or not it
    is awake at either. -/
def ConfirmedOnlyExtendsAfterHealing (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) : Prop :=
  ∀ (v : V) (i j : Nat), i ≤ j →
    Restated.HonestThrough M Sched x j v →
    tE ≤ (x[i].time : Int) →
    Block.Preceq (Restated.Read.confirmed M x[i][v].st)
      (Restated.Read.confirmed M x[j][v].st)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every `gap` with `gap + 2 ≤ S.cfg.K` there is a `tHeal ≥ 0` such that every execution
    meeting the premises listed over a phase `[tGAT, tAwakeEnd]` of length at least `tHeal`
    satisfies `ConfirmedIncludedAfterHealing` and `ConfirmedOnlyExtendsAfterHealing` at `tAwakeEnd`. -/
def claimConfirmedIncludedAfterHealingStatement (M : Record.Model V) (S : Setup V) (Sched : Schedule V) : Prop :=
  ∀ gap : Nat, gap + 2 ≤ S.cfg.K →
  ∃ tHeal : Int, 0 ≤ tHeal ∧
  ∀ (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tAwakeEnd : Int),
    tGAT + tHeal ≤ tAwakeEnd →
    S.E.t_GST ≤ tGAT →
    Sched.MonotoneCorruption →
    Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x →
    Restated.SynchronyFromWake M S x →
    AwakeAtMultiples S Sched →
    Restated.WakesAtActionInstants M S Sched →
    Restated.SleepsAfterActionInstants M S Sched →
    Restated.CatchUpOnWake M S x →
    Restated.TimeDiverges M x →
    Restated.HonestCommittees M S Sched (Restated.interface M S Sched) →
    (∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) →
    (∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) →
    Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap →
    sleepinessW S Sched tAwakeEnd →
    Restated.roundSleepinessW M S Sched tAwakeEnd →
    Restated.committeeSleepinessW M S Sched tAwakeEnd →
    Restated.ConfirmedIncludedAfterHealing M S Sched x tAwakeEnd ∧
      Restated.ConfirmedOnlyExtendsAfterHealing M S Sched x tAwakeEnd

end

end DecoupledConsensusModel.Sts.Restated
