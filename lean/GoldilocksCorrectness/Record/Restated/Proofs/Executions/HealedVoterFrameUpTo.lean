module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HealedVoterFrame
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89CountJUpTo
public import GoldilocksCorrectness.Proofs.Executions.HealedVoterFrame
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma89CountJUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HealedVoterFrameUpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/HealedVoterFrameUpTo.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the voter frame after the
hand-over with the delivery premises up to a bound, namely a block on the honest chain before slot
`s` held by every honest active voter of slot `s` before the view freeze of slot `s − 1`, and
`VoterFrameOnChainAt` for every honest active voter of slot `s`. The page's routine-level theorems
are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff one_le_Δ
  slot_le_of_supportCutoff_lt supportCutoff_mono times_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Proofs.Executions (mem_awakeThroughout_iff)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-- **A block on the honest chain before `s` is held by an honest active voter of `s` before the
view freeze of slot `s − 1`.** The proof; the audited statement is in
`Statements/Executions/HealedVoterFrameStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the first slot of the chain; `s`: the slot; `w`: the voter; `B`:
  the block.

Roots name blocks until `M.viewFreeze S.C (s - 1)`: the confirmation the updater holds reaches `w`
by the view freeze of slot `s − 1`, one delay after the support cutoff of slot `s − 1`
(`mem_T_before_add_delay_of_held_at`).

Restated with the delivery premises up to `M.viewFreeze S.C (s - 1)`: the bound of its roots
`hRoots`; the confirmation the updater holds reaches `w` one delay after the support cutoff of slot
`s − 1` (`mem_T_before_add_delay_of_held_at_upTo`).

 The updater serves its own confirmation when its tick to
that support cutoff is within that delay of the view freeze, staying active for `Δs` after its tick to the support
cutoff of the next slot; otherwise the validator `hHold` names serves it.

Read aloud: an honest active voter holds the honest chain so far when its voter tree is frozen, with
the delivery premises up to the view freeze of slot `s − 1`. -/
theorem chain_block_held_before_freeze_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ s : ℕ) (w : V) (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.viewFreeze S.C (s - 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.viewFreeze S.C (s - 1)))
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
    B ∈ (x.tickInput w (M.viewFreeze S.C (s - 1))).tree := by
  exact (chain_block_held_before_freeze_core M F U) S A x R GST s₀ s w B E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST
    hHold hStay hw hB hF

/-- **The voter frame after the hand-over.** The proof; the audited statement is in
`Statements/Executions/HealedVoterFrameStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `i₂`: the step from which the caches are on the
  chain; `H`: the threshold; `s`: the slot of the vote; `w`: the voter.

Roots name blocks until `M.voteTime S.C s`: the proof reads `w`'s state before the vote time of slot
`s` (Lemma 91f, and the entry the certificate names against `w`'s justified block), and the blocks
of the chain `w` holds by the view freeze of slot `s − 1`.

Caches and `hAdvQ` up to the real time of `w`'s tick to the vote time of slot `s`: the proof reads `w`'s state at that tick
(Lemma 91 (d) and (f) there).

Restated with the delivery premises up to `M.voteTime S.C s`: the bound of its roots `hRoots`; the
one delivery its proof reads is `chain_block_held_before_freeze_upTo`'s, due by the view freeze of
slot `s − 1`, before it.

Read aloud: after the hand-over, an honest active voter's fork-choice root is compatible with the
honest chain before its slot, and, when the root is a block of that chain or an ancestor of one,
some block of its voter tree that is that block or a descendant of it is a viable head, with the
delivery premises up to the vote time of slot `s`.

 -/
theorem voterFrame_after_handover_until_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ i₂ H s : ℕ) (w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.voteTime S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.voteTime S.C s))
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
    VoterFrameOnChainAt M S A x s₀ s w := by
  intro B hB
  have hs1 : 1 ≤ s := by obtain ⟨μ, hμ, -⟩ := hB; omega
  obtain ⟨hvs, -, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
  obtain ⟨-, -, hfs1, hss1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s - 1)
  rw [show s - 1 + 1 = s by omega] at hss1
  have hle : M.viewFreeze S.C (s - 1) ≤ M.voteTime S.C s := by omega
  exact (voterFrame_after_handover_core M F U Fx) S A x R GST s₀ i₂ H s w (E.mono hle) hNet hSkew hRedeliver (Sy.mono hle)
    hΔs hRoots hParent hAdvQ hGST hHold hStay hOld hCaches hs hChain hw B hB

end GoldilocksCorrectness.Record.Proofs.Executions

