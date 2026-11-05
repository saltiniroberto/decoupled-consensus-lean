module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89Stability
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.DeliveryStatementsUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Stability
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89StabilityUpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89StabilityUpTo.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: a block delivered within one
delay, and a confirmation saved when a voter majority votes on the chain of the updater's finalized
block, with the delivery premises up to the bound the theorems read.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ
  slotStart_eq supportCutoff_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

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
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **An honest update saves a confirmation when a voter majority votes on the chain of the
updater's finalized block.** Lemma 78's hypotheses with `B` the finalized block of `v` before the
support cutoff `c` of slot `s + 1`: when `GST` is at most the vote time of slot `s`; every member of
`Hs` is in the slot-`s` committee, honest through `c`, sent its slot-`s` vote for `H u`, a block it
holds that is `v`'s finalized block or a descendant of it; the validators with a slot-`s` vote in
`v`'s pool before `c` are fewer than twice `Hs`; and `v` is awake and honest from the duty window's
start of slot `s + 1` to `c` — then `v` holds right after `c` some confirmation of slot `s`.

Why: Lemma 78's first case: Lemma 12 delivers every member's vote to `v`, held early, so each is an
early supporter of `v`'s finalized block, and `update_confirmation_saves`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the votes; `Hs`: the honest voters; `H`: the block each
  voter's vote is for; `v`: the updater.

Roots name blocks until the real time of `v`'s own tick to `M.supportCutoff S.C s`: Lemma 12 at slot `s`
(`lem12_honest_vote_delivered_until_of_steps_upTo`). The voters are outside the adversary set at `v`'s tick to the
support cutoff of slot `s + 1`, and active through the sync delay after Lemma 12's read time.

Restated with the delivery premises up to `M.supportCutoff S.C s`, the bound of Lemma 12 at slot `s`.

Read aloud: an honest update saves a confirmation when a voter majority votes on the chain of the
updater's finalized block, with the delivery premises up to the bound. -/
theorem confirmation_saved_of_votes_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (v : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧
      (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq (H u))
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
      2 * Hs.card)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1))) :
    ∃ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C' := by
  have hΔ := one_le_Δ S
  have hc₁ : M.supportCutoff S.C s = M.voteTime S.C s + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have hv₁ : M.voteTime S.C s = M.slotStart S.C s + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hv₂ : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hc₂ : M.supportCutoff S.C (s + 1) = M.voteTime S.C (s + 1) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  -- `v`'s tick to the support cutoff of slot `s + 1`, and the state it reads
  obtain ⟨kc, hkc, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have hkcs : x.tickStep v (M.supportCutoff S.C (s + 1)) = kc := (tickStep_eq_of_lbl M) x E hkc
  have hti : x.tickInput v (M.supportCutoff S.C (s + 1)) = x.st kc v := by
    unfold Trace.tickInput; rw [hkcs]
  -- an outcome of that tick, the update it ran, and the saved confirmation it leaves
  obtain ⟨n'', sent, hrun, hAwake, hSv, -, -, -⟩ := (update_state_of_tick M F U) S A x R s v E hkc
    ((tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hv
      ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout
        F.sched U) S (s + 1)))
  have hUpdate := (confirmationUpdated_of_cutoff_tickInput M F U) x R s v n'' sent hrun hAwake
  -- Lemma 12 at `v`'s tick: every voter's vote is held early
  have hHeld : ∀ u ∈ Hs, HeldEarlyVoteFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) s (H u) u :=
    (lem12_honest_vote_delivered_until_of_steps_upTo M F U) S A x R GST s (M.supportCutoff S.C (s + 1)) Hs H v
      E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST (by omega) kc hkc
      (fun u hu => ⟨(hHs u hu).1, hkcs ▸ (hHs u hu).2.1, (hHs u hu).2.2.1, (hHs u hu).2.2.2.1⟩)
      hHold ((updater_reader_gives_core_window M F U) x R E hΔs hSkew hv)
      (fun u hu => (hHs u hu).2.2.2.2)
  have hRoots₂ : RootsNameBlocksIn (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree := by
    rw [hti]
    exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E kc v
  -- every voter is an early supporter of the finalized block
  have hSup : ∀ u ∈ Hs, GoldilocksCorrectness.Record.Statements.Routines.EarlySupporterOf M S.C
      (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1 - 1)
      (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).F u :=
    fun u hu => (heldEarlyVoteFor_earlySupporterOf M F) S.C _ s _ (H u) u (hHeld u hu)
      (by rw [(GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]; exact (hHs u hu).2.2.2.2)
  have hSlot : ∀ vote ∈ M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1 - 1),
      vote.slot = s + 1 - 1 := by
    rw [hti]
    exact (GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_exec M F) S A x R E kc v s
  have h := (GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_saves F) Hs
    (Nat.le_add_left 1 s) hRoots₂ hSup hSlot hVoters hUpdate
  rw [Nat.add_sub_cancel] at h
  rw [hSv]
  exact h

end GoldilocksCorrectness.Record.Proofs.Executions

