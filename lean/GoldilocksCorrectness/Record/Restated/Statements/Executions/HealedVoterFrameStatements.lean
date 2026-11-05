module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HealedVoterFrame
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HealedVoterFrameStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/HealedVoterFrameStatements.lean`,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the voter frame
after the hand-over, namely a block on the honest chain before slot `s` held by every honest active
voter of slot `s` before the view freeze of slot `s − 1`, and `VoterFrameOnChainAt` for every honest
active voter of slot `s`; each is the theorem of the same name of
`Record/Restated/Proofs/Executions/HealedVoterFrame.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff viewFreeze)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **A block on the honest chain before `s` reaches every honest active voter of `s` before the
view freeze of slot `s − 1`.** Under synchrony from `GST`, with `w` honest and active at slot `s`
and its finalized block before that freeze compatible with the block.

Why: the block is an ancestor of, or equal to, the confirmation `C` of a slot `μ < s` saved by an
updater `u`, which held `C` before the support cutoff of slot `μ`; when `w`'s finalized block is
an ancestor of the block, the network delivers `C` to `w`, awake and honest from the support cutoff
of slot `s − 1` to the view freeze of slot `s − 1` (inside its duty window of slot `s`), within one
delay; otherwise the block is an ancestor of `w`'s finalized block, which `w` holds.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the first slot of the chain; `s`: the slot; `w`: the voter; `B`:
  the block.



Roots name blocks until `M.viewFreeze S.C (s - 1)`: the confirmation the updater holds reaches `w`
by the view freeze of slot `s − 1`, one delay after the support cutoff of slot `s − 1`.

 The updater serves its own confirmation when its tick to
that support cutoff is within that delay of the view freeze, staying active for `Δs` after its tick to the support
cutoff of the next slot; otherwise the validator `hHold` names serves it.

Read aloud: an honest active voter holds the honest chain so far when its voter tree is frozen. -/
theorem chain_block_held_before_freeze (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ s : ℕ) (w : V) (B : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.viewFreeze S.C (s - 1)))))
    (hParent : ParentHeldAtDelivery M x)
    -- the recovery delay after `GST` has elapsed by the view freeze of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C (s - 1))
    -- for every confirmation an updater saved for a slot `μ` before `s − 1` whose updater ticked to
    -- the support cutoff of `μ` more than the recovery delay before the view freeze of slot `s − 1`
    --, some validator active at
    -- the window start, honest at its last step before it, holds it with a compatible finalized
    -- block; that validator is active at every step at a real time from the window start to one
    -- sync delay after it (, applies)
    (hHold : ∀ μ : ℕ, s₀ ≤ μ → μ + 1 < s →
      ∀ u ∈ updaterAt M S A x μ,
      (x.time (x.tickStep u (M.supportCutoff S.C μ)) : ℝ) + max (Δ S) Δs < M.viewFreeze S.C (s - 1) →
      ∀ C : Block V,
      (x.tickOutput u (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C →
      ∃ v : V, v ∈ A.activeThroughout x ((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ)
          (((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) ∧
        v ∉ A.corrupted (x.stepBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs)) ∧
        C ∈ (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).tree ∧
        (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).finalized.compatible C = true)
    -- every updater of a slot from the healed slot `s₀` to `s − 2` is active for the sync delay after the real time
    -- of its own tick to the support cutoff of the next slot
    (hStay : ∀ σ : ℕ, s₀ ≤ σ → σ + 1 < s → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hw : w ∈ honestActiveAt M S A x s)
    (hB : OnHonestChainBefore M S A x s₀ s B)
    (hF : (x.tickInput w (M.viewFreeze S.C (s - 1))).finalized.compatible B = true) :
    B ∈ (x.tickInput w (M.viewFreeze S.C (s - 1))).tree :=
  (GoldilocksCorrectness.Record.Proofs.Executions.chain_block_held_before_freeze M F U) S A x R
    GST s₀ s w B E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hHold hStay hw hB hF

/-- **The voter frame after the hand-over.** With the confirmations of the slots before `s`
forming one chain, the old attestations at most `H`, the caches from `i₂`, fewer than a quorum ever
corrupted, the view freeze of slot `s − 1` after `x[i₂].time`, and `w` honest and active at slot
`s`: `w`'s frame before the vote time of slot `s` follows the honest chain before `s`.

Why: the root of `w`'s fork choice is on the chain before `s` (Lemma 91 (f)), so compatible with
every block `B` of it. When the root is `B` or an ancestor of `B`, the state is not contested and
its `head_height_floor` (the least chain-state height a viable block may have) is the greatest
chain-state height minus one (Lemma 91 (d)); some block `E` of the chain before `s` has a
chain-state height at least the greatest chain-state height minus one (the justified block when the
greatest chain-state height is at most `H + 1`; otherwise the entry named by the progress
certificate at the greatest chain-state height minus one of the block that raised the chain, Lemma
67); the later of `B` and `E` is held before the view freeze of slot `s − 1`
(`chain_block_held_before_freeze`), so it is in the voter tree and a viable head.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `i₂`: the step from which the caches are on the
  chain; `H`: the threshold; `s`: the slot of the vote; `w`: the voter.



Roots name blocks until `M.voteTime S.C s`: the proof reads `w`'s state before the vote time of slot
`s`, and the blocks of the chain `w` holds by the view freeze of slot `s − 1`.

Read aloud: after the hand-over, an honest active voter's fork-choice root is compatible with the
honest chain before its slot, and, when the root is a block of that chain or an ancestor of one,
some block of its voter tree that is that block or a descendant of it is a viable head.

 -/
theorem voterFrame_after_handover (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ i₂ H s : ℕ) (w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to the later of the real time of `w`'s tick to
    -- `M.voteTime S.C s` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time (x.tickStep w (M.voteTime S.C s))) (M.supportCutoff S.C (s₀ + 1))))
    -- the recovery delay after `GST` has elapsed by the view freeze of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C (s - 1))
    -- for every confirmation an updater saved for a slot `μ` before `s − 1` whose updater ticked to
    -- the support cutoff of `μ` more than the recovery delay before the view freeze of slot `s − 1`
    --, some validator active at
    -- the window start, honest at its last step before it, holds it with a compatible finalized
    -- block; that validator is active at every step at a real time from the window start to one
    -- sync delay after it (, applies)
    (hHold : ∀ μ : ℕ, s₀ ≤ μ → μ + 1 < s →
      ∀ u ∈ updaterAt M S A x μ,
      (x.time (x.tickStep u (M.supportCutoff S.C μ)) : ℝ) + max (Δ S) Δs < M.viewFreeze S.C (s - 1) →
      ∀ C : Block V,
      (x.tickOutput u (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C →
      ∃ v : V, v ∈ A.activeThroughout x ((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ)
          (((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) ∧
        v ∉ A.corrupted (x.stepBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs)) ∧
        C ∈ (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).tree ∧
        (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).finalized.compatible C = true)
    -- every updater of a slot from the healed slot `s₀` to `s − 2` is active for the sync delay after the real time
    -- of its own tick to the support cutoff of the next slot
    (hStay : ∀ σ : ℕ, s₀ ≤ σ → σ + 1 < s → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches at every step at a real time after `x[i₂].time`
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₂ < x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    -- the view freeze of slot `s − 1`, where the voter tree is read, is after `x[i₂].time`
    (hs : x.time i₂ < M.viewFreeze S.C (s - 1))
    (hChain : ConfirmationsChainBefore M S A x s₀ s)
    (hw : w ∈ honestActiveAt M S A x s) :
    VoterFrameOnChainAt M S A x s₀ s w :=
  (GoldilocksCorrectness.Record.Proofs.Executions.voterFrame_after_handover M F U Fx) S A x R GST
    s₀ i₂ H s w E hNet hSkew hRedeliver Sy hΔs hRoots hParent hAdvQ hGST hHold hStay hOld hCaches hs hChain hw

/-- **The voter frame after the hand-over.** With the confirmations of the slots before `s` forming
one chain, the old attestations at most `H`, the caches from `i₂` to the vote time of slot `s`,
fewer than a quorum ever corrupted, the view freeze of slot `s − 1` after `x[i₂].time`, and `w`
honest and active at slot `s`: `w`'s frame before the vote time of slot `s` follows the honest chain
before `s`.

Why: the root of `w`'s fork choice is on the chain before `s` (Lemma 91 (f)), so compatible with
every block `B` of it. When the root is `B` or an ancestor of `B`, the state is not contested and
its `head_height_floor` (the least chain-state height a viable block may have) is the greatest
chain-state height minus one (Lemma 91 (d)); some block `E` of the chain before `s` has a
chain-state height at least the greatest chain-state height minus one (the justified block when the
greatest chain-state height is at most `H + 1`; otherwise the entry named by the progress
certificate at the greatest chain-state height minus one of the block that raised the chain, Lemma
67); the later of `B` and `E` is held before the view freeze of slot `s − 1`
(`chain_block_held_before_freeze`), so it is in the voter tree and a viable head.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `i₂`: the step from which the caches are on the
  chain; `H`: the threshold; `s`: the slot of the vote; `w`: the voter.



Roots name blocks until `M.voteTime S.C s`: the proof reads `w`'s state before the vote time of slot
`s`, and the blocks of the chain `w` holds by the view freeze of slot `s − 1`.

Read aloud: after the hand-over, an honest active voter's fork-choice root is compatible with the
honest chain before its slot, and, when the root is a block of that chain or an ancestor of one,
some block of its voter tree that is that block or a descendant of it is a viable head.

Caches and `hAdvQ` up to the real time of `w`'s tick to the vote time of slot `s`: the proof reads `w`'s state at that tick.


 -/
theorem voterFrame_after_handover_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ i₂ H s : ℕ) (w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to the later of the real time of `w`'s tick to
    -- `M.voteTime S.C s` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time (x.tickStep w (M.voteTime S.C s))) (M.supportCutoff S.C (s₀ + 1))))
    -- the recovery delay after `GST` has elapsed by the view freeze of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C (s - 1))
    -- for every confirmation an updater saved for a slot `μ` before `s − 1` whose updater ticked to
    -- the support cutoff of `μ` more than the recovery delay before the view freeze of slot `s − 1`
    --, some validator active at
    -- the window start, honest at its last step before it, holds it with a compatible finalized
    -- block; that validator is active at every step at a real time from the window start to one
    -- sync delay after it (, applies)
    (hHold : ∀ μ : ℕ, s₀ ≤ μ → μ + 1 < s →
      ∀ u ∈ updaterAt M S A x μ,
      (x.time (x.tickStep u (M.supportCutoff S.C μ)) : ℝ) + max (Δ S) Δs < M.viewFreeze S.C (s - 1) →
      ∀ C : Block V,
      (x.tickOutput u (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C →
      ∃ v : V, v ∈ A.activeThroughout x ((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ)
          (((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) ∧
        v ∉ A.corrupted (x.stepBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs)) ∧
        C ∈ (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).tree ∧
        (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).finalized.compatible C = true)
    -- every updater of a slot from the healed slot `s₀` to `s − 2` is active for the sync delay after the real time
    -- of its own tick to the support cutoff of the next slot
    (hStay : ∀ σ : ℕ, s₀ ≤ σ → σ + 1 < s → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches at every step at a real time after `x[i₂].time`
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₂ < x.time j → x.time j ≤ x.time (x.tickStep w (M.voteTime S.C s)) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    -- the view freeze of slot `s − 1`, where the voter tree is read, is after `x[i₂].time`
    (hs : x.time i₂ < M.viewFreeze S.C (s - 1))
    (hChain : ConfirmationsChainBefore M S A x s₀ s)
    (hw : w ∈ honestActiveAt M S A x s) :
    VoterFrameOnChainAt M S A x s₀ s w :=
  (GoldilocksCorrectness.Record.Proofs.Executions.voterFrame_after_handover_until M F U Fx) S A
    x R GST s₀ i₂ H s w E hNet hSkew hRedeliver Sy hΔs hRoots hParent hAdvQ hGST hHold hStay hOld hCaches hs hChain hw

end GoldilocksCorrectness.Record.Statements.Executions

