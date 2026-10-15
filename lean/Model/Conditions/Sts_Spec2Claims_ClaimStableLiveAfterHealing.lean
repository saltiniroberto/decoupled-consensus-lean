import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedGrowsAfterHealing
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedIncludedAfterHealing
import Model.Record.Wiring

/-!
# Stable outputs after healing

The stable inclusion and growth delays, the inclusion of honest proposals in stable outputs after a
phase, their monotonicity and growth, and the statement that these hold, stated over a model
`M : Record.Model V`.
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

/-- The delay from a slot's proposal instant to the instant from which the block is in the stable
    output of every reader awake throughout the vote window of its read's slot: two periods and four
    delays. -/
noncomputable def stableInclusionDelay (M : Record.Model V) (S : Setup V) : Int := 2 * (Restated.constants M S).period + 4 * S.E.Δ

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The growth delay of the stable output: `gapP` periods plus `stableInclusionDelay`. -/
noncomputable def stableGrowthDelay (M : Record.Model V) (S : Setup V) (gapP : Nat) : Int :=
  (gapP : Int) * (Restated.constants M S).period + Restated.stableInclusionDelay M S

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every slot `s` with proposal instant at or after `tE` whose proposer is not held up to `s`'s
    vote instant: if the proposer is awake from `M.proposal_wake_start S s` to the proposal instant,
    it sends a block of slot `s` at that instant; and every block it sent by `s`'s vote instant is
    an ancestor of the stable output of every validator honest through its read that ran, at or
    after the proposal instant plus the stable inclusion delay and at or before its read, a
    confirmation while awake throughout that confirmation's grade-2 window
    (`awakeThroughConfirmationWindow`), at every read from the proposal instant plus the stable
    inclusion delay on. -/
def StableIncludedAfterHealing (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
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
        M.proposal_time S.E s + Restated.stableInclusionDelay M S ≤ (x[j].time : Int) →
        Restated.awakeThroughConfirmationWindow M S Sched
          (M.proposal_time S.E s + Restated.stableInclusionDelay M S) (x[j].time : Int) v →
        Block.Preceq B (Restated.Read.stable M x[j][v].st)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- From `tE` on, a validator honest through the later of two reads holds, at the later read, a
    stable output that is a descendant of the one it held at the earlier read, whether or not it is
    awake at either. -/
def StableOnlyExtendsAfterHealing (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) : Prop :=
  ∀ (v : V) (i j : Nat), i ≤ j →
    Restated.HonestThrough M Sched x j v →
    tE ≤ (x[i].time : Int) →
    Block.Preceq (Restated.Read.stable M x[i][v].st)
      (Restated.Read.stable M x[j][v].st)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every instant `t ≥ tE` and every step `i` at `t`, some slot `s` proposed strictly after `t`,
    whose proposer is not held up to `s`'s vote instant, has a block that proposer sent by that vote
    instant which is a strict descendant of the stable output of every validator honest through step
    `i`, and an ancestor of the stable output of every validator honest through its read that ran,
    at or after `t` plus the stable growth delay and at or before its read, a confirmation while
    awake throughout that confirmation's grade-2 window (`awakeThroughConfirmationWindow`), at every
    read from `t` plus the stable growth delay on. -/
def StableGrowsAfterHealing (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (gapP : Nat) : Prop :=
  ∀ t : Int, tE ≤ t →
    ∀ i : Nat, (x[i].time : Int) = t →
    ∃ (s : Slot) (k : Nat) (B : Block V),
      t < M.proposal_time S.E s ∧
      HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s) ∧
      Restated.proposedBlockAtStep M S x k s B ∧
      (x[k].time : Int) ≤ M.vote_time S.E s ∧
      (∀ v : V, Restated.HonestThrough M Sched x i v →
        Block.Prec (Restated.Read.stable M x[i][v].st) B) ∧
      (∀ (v : V) (j : Nat), Restated.HonestThrough M Sched x j v →
        t + Restated.stableGrowthDelay M S gapP ≤ (x[j].time : Int) →
        Restated.awakeThroughConfirmationWindow M S Sched
          (t + Restated.stableGrowthDelay M S gapP) (x[j].time : Int) v →
        Block.Preceq B (Restated.Read.stable M x[j][v].st))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every `gap` with `gap + 2 ≤ S.cfg.K` there is a `tHeal ≥ 0` such that every execution
    meeting the premises listed over a phase `[tGAT, tAwakeEnd]` of length at least `tHeal`
    satisfies `StableIncludedAfterHealing` and `StableOnlyExtendsAfterHealing` at `tAwakeEnd`, and
    `StableGrowsAfterHealing` for every `gapP` with which honest awake proposers recur from
    `tAwakeEnd` on. -/
def claimStableLiveAfterHealingStatement (M : Record.Model V) (S : Setup V) (Sched : Schedule V) : Prop :=
  ∀ gap : Nat, gap + 2 ≤ S.cfg.K →
  ∃ tHeal : Int, 0 ≤ tHeal ∧
  ∀ (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tAwakeEnd : Int),
    tGAT + tHeal ≤ tAwakeEnd →
    S.E.t_GST ≤ tGAT →
    Sched.MonotoneCorruption →
    Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x →
    Restated.SynchronyFromWake M S x →
    AwakeAtMultiples S Sched →
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
    Restated.StableIncludedAfterHealing M S Sched x tAwakeEnd ∧
      Restated.StableOnlyExtendsAfterHealing M S Sched x tAwakeEnd ∧
      ∀ gapP : Nat, Restated.honestAwakeProposersRecurFrom M S Sched tAwakeEnd gapP →
        Restated.StableGrowsAfterHealing M S Sched x tAwakeEnd gapP

end

end DecoupledConsensusModel.Sts.Restated
