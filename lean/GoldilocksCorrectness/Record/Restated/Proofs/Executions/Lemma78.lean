module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.DeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickUpdateState
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickWindowKit
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.SupporterDefs
public import GoldilocksCorrectness.Proofs.Executions.Lemma78
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma78, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma78.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: a vote held early for a descendant of a block
makes its voter an early supporter of that block's chain, and Lemma 78, an honest confirmation
update over a voter majority's chain. The page's routine-level theorems are the facts' fields or
have their twins in phase A.
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

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (EarlySupporterOf)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

omit [RootOrder] in
/-- A vote held early as the delivery lemma says (`HeldEarlyVoteFor`) for a block `H_u` that is
`B` or a descendant of `B` makes its voter an early supporter of `B`'s chain (`EarlySupporterOf`).

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `n`: the node state;
- `s`: the slot of the vote; `B`: the block whose chain the vote supports; `H_u`: the block the
  vote is for; `u`: the voter.

Read aloud: a vote of `u` for `H_u` held early in `n`, with `H_u` being `B` or a descendant of `B`,
makes `u` an early supporter of `B`'s chain in `n`. -/
theorem heldEarlyVoteFor_earlySupporterOf (C : Config) (n : M.N) (s : Slot)
    (B H_u : Block V) (u : V)
    -- `n` holds `u`'s slot-`s` vote for `H_u`, early, as its only slot-`s` vote
    (h : HeldEarlyVoteFor M C n s H_u u)
    -- `H_u` is `B` or a descendant of `B`
    (hBH : B.AncestorEq H_u) :
    EarlySupporterOf M C n s B u := by
  obtain ⟨hp, -, hT, hres, huniq⟩ := h
  exact ⟨_, hp, rfl, ⟨H_u, hT, rfl, hBH⟩, hres, huniq⟩

/-- Lemma 78, an honest confirmation update over a voter majority's chain. Its reading is on the
statement page, `GoldilocksCorrectness/Statements/Executions/HonestChainStatements.lean`.

Roots name blocks until the real time of `v`'s own tick to `M.supportCutoff S.C s`: the bound of the Lemma 12 call at slot `s` it
passes the premise to.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the confirmation of slot `s` that `v` saves at the support cutoff of slot `s + 1` is `B`
or a descendant of `B`, when the honest voters of `Hs`, who vote for `B` or descendants of `B`, are
more than half of the voters `v` counts. -/
theorem lem78_update_confirmation_extends_voter_majority_chain (U : UniformSchedule M.toSlotLayout)
    (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (B : Block V) (v : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ B.AncestorEq (H u))
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
      2 * Hs.card)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (hF : (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.compatible B = true) :
    ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C' →
      B.AncestorEq C' := by
  intro C' hC'
  -- the times
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
  -- the outcome of that tick that saves `C'`, and the update it ran
  obtain ⟨n'', sent, hrun, hAwake, hsave⟩ :=
    (update_of_saved_confirmation_of_updater M F U) S A x R s v C' E hv hC'
  have hUpdate := (confirmationUpdated_of_cutoff_tickInput M F U) x R s v n'' sent hrun hAwake
  rcases (compatible_iff _ _).1 hF with hFB | hBF
  · -- the finalized block is `B` or an ancestor of `B`: Lemma 12 at `v`'s tick, then Lemma 77
    have hHeld : ∀ u ∈ Hs, HeldEarlyVoteFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) s (H u) u :=
      (lem12_honest_vote_delivered_until_of_steps M F U) S A x R GST s (M.supportCutoff S.C (s + 1)) Hs H v
        E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST (by omega) kc hkc
        (fun u hu => ⟨(hHs u hu).1, hkcs ▸ (hHs u hu).2.1, (hHs u hu).2.2.1, (hHs u hu).2.2.2.1⟩)
        hHold ((updater_reader_gives_core_window M F U) x R E hΔs hSkew hv)
        (fun u hu => ancestorEq_trans hFB (hHs u hu).2.2.2.2)
    obtain ⟨u₀, hu₀⟩ : Hs.Nonempty := Finset.card_pos.1 (by omega)
    have hRoots₂ : RootsNameBlocksIn (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree := by
      rw [hti]
      exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E kc v
    have hH₀ := (hHeld u₀ hu₀).2.2.1
    have hPathF : ∀ P' : Block V, (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).F.AncestorEq P' →
        P'.AncestorEq B → P' ∈ (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree := by
      rw [hti] at hH₀ ⊢
      exact fun P' h1 h2 => (GoldilocksCorrectness.Record.Statements.Executions.frame_path_of_exec M F) S A x R E kc v
        (H u₀) P' hH₀ h1 (ancestorEq_trans h2 (hHs u₀ hu₀).2.2.2.2)
    have hSup : ∀ u ∈ Hs, EarlySupporterOf M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1 - 1) B u :=
      fun u hu => (heldEarlyVoteFor_earlySupporterOf M F) S.C _ s B (H u) u (hHeld u hu)
        (hHs u hu).2.2.2.2
    have hSlot : ∀ vote ∈ M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1 - 1),
        vote.slot = s + 1 - 1 := by
      rw [hti]
      exact (GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_exec M F) S A x R E kc v s
    have h77 :=
      (GoldilocksCorrectness.Record.Statements.Routines.lem77_update_confirmation_extends_voter_majority_chain F)
        B Hs (Nat.le_add_left 1 s) hRoots₂
        (by rw [(GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]; exact hFB) hPathF hSup hSlot
        hVoters hUpdate
    rw [Nat.add_sub_cancel] at h77
    exact h77 C' hsave
  · -- `B` is an ancestor of the finalized block: the saved block descends from it
    have h := GoldilocksCorrectness.Record.Statements.Routines.saved_confirmation_F_ancestorEq
      (Nat.le_add_left 1 s) hUpdate
    rw [Nat.add_sub_cancel] at h
    exact ancestorEq_trans hBF (by rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]; exact h C' hsave)

end GoldilocksCorrectness.Record.Proofs.Executions

