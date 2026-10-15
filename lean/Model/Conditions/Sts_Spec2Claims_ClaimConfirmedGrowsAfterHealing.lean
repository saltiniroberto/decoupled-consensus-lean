import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Record.Wiring

/-!
# Growth of confirmed outputs after healing

The recurrence of honest awake proposers, the growth delay, the growth of honest confirmed outputs
after a phase, and the statement that it holds, stated over a model `M : Record.Model V`.
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

/-- From every instant `t ≥ t₀`, some slot `s` has its proposal instant strictly after `t` and at
    most `gapP` periods after `t`, with a proposer not held by the adversary at any instant up to
    `s`'s vote instant and awake at every instant from `M.proposal_wake_start S s` to `s`'s proposal
    instant. -/
def honestAwakeProposersRecurFrom (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (t₀ : Int)
    (gapP : Nat) : Prop :=
  ∀ t : Int, t₀ ≤ t →
    ∃ s : Slot, t < M.proposal_time S.E s ∧
      M.proposal_time S.E s ≤ t + (gapP : Int) * (Restated.constants M S).period ∧
      HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s) ∧
      S.E.proposer s ∈ Sched.awakeThroughout (M.proposal_wake_start S s)
        (M.proposal_time S.E s)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The growth delay of the confirmed output: `gapP` periods plus `confirmedInclusionDelay S`. -/
noncomputable def confirmedGrowthDelay (M : Record.Model V) (S : Setup V) (gapP : Nat) : Int :=
  (gapP : Int) * (Restated.constants M S).period + confirmedInclusionDelay S

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every instant `t ≥ tE` and every step `i` at `t`, some slot `s` proposed strictly after `t`,
    whose proposer is not held up to `s`'s vote instant, has a block that proposer sent by that vote
    instant which is a strict descendant of the confirmed output of every validator honest through
    step `i`, and an ancestor of the confirmed output of every validator honest through its read and
    awake throughout the vote window of its read's slot, at every read from `t` plus the growth
    delay on. -/
def ConfirmedGrowsAfterHealing (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (gapP : Nat) : Prop :=
  ∀ t : Int, tE ≤ t →
    ∀ i : Nat, (x[i].time : Int) = t →
    ∃ (s : Slot) (k : Nat) (B : Block V),
      t < M.proposal_time S.E s ∧
      HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s) ∧
      Restated.proposedBlockAtStep M S x k s B ∧
      (x[k].time : Int) ≤ M.vote_time S.E s ∧
      (∀ v : V, Restated.HonestThrough M Sched x i v →
        Block.Prec (Restated.Read.confirmed M x[i][v].st) B) ∧
      (∀ (v : V) (j : Nat), Restated.HonestThrough M Sched x j v →
        t + Restated.confirmedGrowthDelay M S gapP ≤ (x[j].time : Int) →
        v ∈ activeAtW S Sched (S.E.slotOf (x[j].time : Int)) →
        Block.Preceq B (Restated.Read.confirmed M x[j][v].st))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every `gap` with `gap + 2 ≤ S.cfg.K` there is a `tHeal ≥ 0` such that every execution
    meeting the premises listed over a phase `[tGAT, tAwakeEnd]` of length at least `tHeal`, with
    honest awake proposers recurring within every `gapP` periods from `tAwakeEnd` on, satisfies
    `ConfirmedGrowsAfterHealing`. -/
def claimConfirmedGrowsAfterHealingStatement (M : Record.Model V) (S : Setup V) (Sched : Schedule V) : Prop :=
  ∀ gap : Nat, gap + 2 ≤ S.cfg.K →
  ∃ tHeal : Int, 0 ≤ tHeal ∧
  ∀ (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tAwakeEnd : Int) (gapP : Nat),
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
    Restated.honestAwakeProposersRecurFrom M S Sched tAwakeEnd gapP →
    Restated.ConfirmedGrowsAfterHealing M S Sched x tAwakeEnd gapP

end

end DecoupledConsensusModel.Sts.Restated
