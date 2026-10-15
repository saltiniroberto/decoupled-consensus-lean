import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Record.Wiring

/-!
# Finality liveness after healing

The finality startup, deadline and growth delay, the inclusion of honest proposals in finalized
blocks and the growth of finalized blocks after a phase, and the statement that they hold, stated
over a model `M : Record.Model V`.
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

/-- The finality startup: `2 · gap + timeoutDelay / R + 3` periods. -/
noncomputable def finalityStartupDirect (M : Record.Model V) (S : Setup V) (gap : Nat) : Int :=
  ((2 * gap + S.cfg.timeoutDelay / S.hc.R + 3 : Nat) : Int) * (Restated.constants M S).period

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The finality deadline from an honest proposal to its finalization at every honest store:
    `3 · gap + timeoutDelay / R − 6` periods, the subtraction truncated at zero, plus `9Δ`. -/
noncomputable def finalityDeadlineDirect (M : Record.Model V) (S : Setup V) (gap : Nat) : Int :=
  ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 6 : Nat) : Int) * (Restated.constants M S).period + 9 * S.E.Δ

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- How long after an honest proposal the bounded premises must continue:
    `(3 · gap + timeoutDelay / R − 6) + 1` periods, the subtraction truncated at zero, plus `14Δ`. -/
noncomputable def finalityPremisesContinueDirect (M : Record.Model V) (S : Setup V) (gap : Nat) : Int :=
  ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 6 + 1 : Nat) : Int) * (Restated.constants M S).period +
    14 * S.E.Δ

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The start of the liveness window: `tAwakeEnd` plus `finalityStartupDirect S gap`. -/
noncomputable def finalityLiveStart (M : Record.Model V) (S : Setup V) (tAwakeEnd : Int) (gap : Nat) : Int :=
  tAwakeEnd + Restated.finalityStartupDirect M S gap

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The growth delay: `gap` periods plus `finalityDeadlineDirect S gap`. -/
noncomputable def finalityGrowthDelay (M : Record.Model V) (S : Setup V) (gap : Nat) : Int :=
  (gap : Int) * (Restated.constants M S).period + Restated.finalityDeadlineDirect M S gap

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every slot `s` whose proposal instant is at or after the start of the liveness window and at
    least `finalityPremisesContinueDirect S gap` before `tLive`, and whose proposer is not held up
    to `s`'s vote instant, every block that proposer sent by that vote instant is an ancestor of the
    finalized block of every validator honest through its read, at every read from the proposal
    instant plus the finality deadline on. -/
def FinalityIncludedAfterHealing (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tAwakeEnd tLive : Int) (gap : Nat) : Prop :=
  ∀ s : Slot,
    Restated.finalityLiveStart M S tAwakeEnd gap ≤ M.proposal_time S.E s →
    M.proposal_time S.E s + Restated.finalityPremisesContinueDirect M S gap ≤ tLive →
    HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s) →
    ∀ (i : Nat) (B : Block V), Restated.proposedBlockAtStep M S x i s B →
    (x[i].time : Int) ≤ M.vote_time S.E s →
    ∀ (v : V) (j : Nat), Restated.HonestThrough M Sched x j v →
      M.proposal_time S.E s + Restated.finalityDeadlineDirect M S gap ≤ (x[j].time : Int) →
      Block.Preceq B (Restated.Read.finalized M x[j][v].st)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every instant `t` from the start of the liveness window with `t` plus `gap` periods plus
    `finalityPremisesContinueDirect S gap` at most `tLive`, and every step `i` at `t` or later, some
    slot after `t` has a proposer not held up to its vote instant and a block that proposer sent by
    then which is a strict descendant of the finalized block of every validator honest through step
    `i`, and an ancestor of the finalized block of every validator honest through any read from `t`
    plus the growth delay on. -/
def FinalityGrowsAfterHealing (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tAwakeEnd tLive : Int) (gap : Nat) : Prop :=
  ∀ t : Int,
    Restated.finalityLiveStart M S tAwakeEnd gap ≤ t →
    t + ((gap : Int) * (Restated.constants M S).period + Restated.finalityPremisesContinueDirect M S gap) ≤ tLive →
    ∀ i : Nat, (x[i].time : Int) = t →
    ∃ (s : Slot) (k : Nat) (B : Block V),
      t < M.proposal_time S.E s ∧
      HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s) ∧
      Restated.proposedBlockAtStep M S x k s B ∧
      (x[k].time : Int) ≤ M.vote_time S.E s ∧
      (∀ v : V, Restated.HonestThrough M Sched x i v → Block.Prec (Restated.Read.finalized M x[i][v].st) B) ∧
      (∀ (v : V) (j : Nat), Restated.HonestThrough M Sched x j v →
        t + Restated.finalityGrowthDelay M S gap ≤ (x[j].time : Int) →
        Block.Preceq B (Restated.Read.finalized M x[j][v].st))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every `gap` with `gap + 2 ≤ S.cfg.K` there is a `tHeal ≥ 0` such that every execution
    meeting the premises listed over a phase `[tGAT, tAwakeEnd]` of length at least `tHeal`, with
    the adversary bound, the awake premise and the proposer recurrence continued to `tLive`,
    satisfies `FinalityIncludedAfterHealing` and `FinalityGrowsAfterHealing`. -/
def claimFinalityLiveAfterHealingStatement (M : Record.Model V) (S : Setup V) (Sched : Schedule V) : Prop :=
  ∀ gap : Nat, gap + 2 ≤ S.cfg.K →
  ∃ tHeal : Int, 0 ≤ tHeal ∧
  ∀ (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tAwakeEnd tLive : Int),
    tGAT + tHeal ≤ tAwakeEnd →
    tAwakeEnd ≤ tLive →
    S.E.t_GST ≤ tGAT →
    Sched.MonotoneCorruption →
    Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x →
    Restated.SynchronyFromWake M S x →
    AwakeAtMultiples S Sched →
    Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT →
    Restated.TimeDiverges M x →
    Restated.HonestCommittees M S Sched (Restated.interface M S Sched) →
    -- the adversary bound, the awake premise and the proposer recurrence, continued to `tLive`
    (∀ t : Int, t ≤ tLive →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) →
    (∀ t : Int, tGAT ≤ t → t ≤ tLive →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) →
    Restated.strongOpeningsRecurFrom M S Sched tGAT tLive gap →
    sleepinessW S Sched tAwakeEnd →
    Restated.roundSleepinessW M S Sched tAwakeEnd →
    Restated.committeeSleepinessW M S Sched tAwakeEnd →
    Restated.FinalityIncludedAfterHealing M S Sched x tAwakeEnd tLive gap ∧
      Restated.FinalityGrowsAfterHealing M S Sched x tAwakeEnd tLive gap

end

end DecoupledConsensusModel.Sts.Restated
