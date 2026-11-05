module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma78UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.VoteDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.NetworkUpTo
public import GoldilocksCorrectness.Proofs.Executions.VoteDelivery
public import GoldilocksCorrectness.Proofs.Routines.Lemma77Compat
public import GoldilocksCorrectness.Proofs.Executions.Lemma78UpTo
public import GoldilocksCorrectness.Proofs.Executions.VoteDeliveryUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma78Compat, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma78Compat.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 78c, an honest confirmation update
over a majority whose votes are compatible with `B`, and its form with the delivery premises up to a
bound. The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ
  slotStart_eq slot_eq_of_mem supportCutoff_cast supportCutoff_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (expireLocks_keepsVotes)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery EnvFactsDeliveryUpTo SyncedWithin SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  compatible_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **The common step of Lemma 78c.** For `v` ticking to the support cutoff of slot `s + 1`, awake and
honest from the duty window of slot `s + 1` up to that tick, with its finalized block at that tick's input
compatible with `B`: when, in the case that finalized block is `B` or an ancestor of `B`, `v`'s state at
that tick's input holds every member `u` of `Hs`'s slot-`s` vote for `H u` early, as `u`'s only slot-`s`
vote, with `H u` in its tree (`HeldEarlyVoteFor`, Lemma 12's conclusion at that tick), every `H u` is
compatible with `B`, and fewer than twice `Hs` validators have a slot-`s` vote in `v`'s pool there, the
confirmation `v`'s update at that tick saves for `s` is compatible with `B`.

 the earlier text read them before the real time `M.supportCutoff S.C s` and
the voters' honesty at the real time `M.supportCutoff S.C (s + 1)`, from which a voter's single vote at `v`'s
tick, possibly later than that real time, does not follow.

Why: the update at the tick saves the confirmation of `s` (`update_of_saved_confirmation_of_updater`,
`confirmationUpdated_of_cutoff_tickInput`). When the finalized block is `B` or an ancestor of `B`, each vote
is stamped before `S.C.t_ s + 2 · S.C.Δ`, so before the late cutoff `S.C.t_ s + 6 · S.C.Δ`; it is its voter's
only vote of the slot; a block of `v`'s frame tree named by its head is `H u` (no two blocks of a node's tree
share a root); then Lemma 77c. Otherwise `B` is an ancestor of the finalized block, of which the saved
confirmation is a descendant.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, its run facts; `s`: the slot of the votes;
  `Hs`: the voters; `H`: their blocks; `B`: the block; `v`: the validator whose update it is.

Read aloud: the confirmation `v`'s update at the support cutoff of slot `s + 1` saves for slot `s`
is compatible with `B`, when `v` holds the early votes of the members of `Hs` for blocks compatible with
`B` at that update and they are more than half of the voters `v` counts. -/
theorem lem78c_of_delivered (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (Hs : Finset V) (H : V → Block V) (B : Block V)
    (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- when `v`'s finalized block at its update tick's input is `B` or an ancestor of `B`, that input holds
    -- every member's slot-`s` vote for its block, stamped before `S.C.t_ s + 2 · S.C.Δ`, as its only slot-`s` vote,
    -- with the block in its node tree (the clauses of `lem12_vote_held_at_tick_core_compat`; re-check 79 (a))
    (hHeld : (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B → ∀ u ∈ Hs,
      GoldfishVote.mk u s (H u).root ∈ M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s ∧
      (∃ τ : Stamp, (x.tickInput v (M.supportCutoff S.C (s + 1))).voteStamp (GoldfishVote.mk u s (H u).root) =
          some τ ∧ τ < ((S.C.t_ s + 2 * S.C.Δ : Time) : Stamp)) ∧
      H u ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).tree ∧ (H u).slot ≤ s ∧
      (∃ τH : Stamp, (x.tickInput v (M.supportCutoff S.C (s + 1))).blockStamp (H u) = some τH ∧
        τH < ((S.C.t_ s + 2 * S.C.Δ : Time) : Stamp)) ∧
      ∀ vote' ∈ M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s, vote'.val_index = u →
        vote' = GoldfishVote.mk u s (H u).root)
    (hHB : ∀ u ∈ Hs, (H u).compatible B = true)
    (hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
      2 * Hs.card)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (hF : (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.compatible B = true) :
    ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C' →
      C'.compatible B = true := by
  intro C' hC'
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
  · -- the finalized block is `B` or an ancestor of `B`: Lemma 77c at the tick's input
    have hHeld' := hHeld hFB
    have hRoots₂ : RootsNameBlocksIn (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree := by
      rw [hti]
      exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E kc v
    have hΔpos : (0 : Int) < S.C.Δ := S.C.Δ_pos
    have hlt26 : ((S.C.t_ s + 2 * S.C.Δ : Time) : Stamp) <
        ((S.C.t_ s + 6 * S.C.Δ : Time) : Stamp) :=
      WithBot.coe_lt_coe.2 (Int.add_lt_add_left (Int.mul_lt_mul_of_pos_right (by decide) hΔpos) _)
    have hHs77 : ∀ u ∈ Hs, ∃ vote ∈ M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1 - 1),
        vote.val_index = u ∧
        (∃ τ : Stamp, (x.tickInput v (M.supportCutoff S.C (s + 1))).voteStamp vote = some τ ∧
          τ < ((S.C.t_ (s + 1 - 1) + 6 * S.C.Δ : Time) : Stamp)) ∧
        (∀ vote' ∈ M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1 - 1),
          vote'.val_index = u → vote' = vote) ∧
        ∀ D ∈ (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree, D.root = vote.head →
          D.compatible B = true := by
      rw [Nat.add_sub_cancel]
      intro u hu
      obtain ⟨hvote, ⟨τ, hτ, hτlt⟩, hHT, -, -, huniq⟩ := hHeld' u hu
      refine ⟨GoldfishVote.mk u s (H u).root, hvote, rfl, ⟨τ, hτ, lt_trans hτlt hlt26⟩, huniq,
        fun D hD hDr => ?_⟩
      -- the block of `v`'s frame tree named by the vote's head is `H u`: no two blocks of `v`'s node tree share a
      -- root (the node invariant at `v`'s tick, `v` honest there)
      have hRootsN : RootsNameBlocksIn (x.tickInput v (M.supportCutoff S.C (s + 1))).tree := by
        rw [hti]
        exact F.nd.nodeInv_rootsNameBlocksIn
          ((lem11_node_invariant M F) S A x R E kc v (E.not_mem_corrupted_of_tick hkc)).1
      have hDT : D ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).tree :=
        (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hD).1
      rw [hRootsN D hDT (H u) hHT hDr]
      exact hHB u hu
    have h77 :=
      (GoldilocksCorrectness.Record.Proofs.Routines.lem77c_update_confirmation_compatible_of_majority F)
        B Hs (Nat.le_add_left 1 s) hRoots₂ hHs77
        (by rw [Nat.add_sub_cancel]; exact hVoters) hUpdate
    rw [Nat.add_sub_cancel] at h77
    exact h77 C' hsave
  · -- `B` is an ancestor of the finalized block: the saved block descends from it
    have h := GoldilocksCorrectness.Record.Statements.Routines.saved_confirmation_F_ancestorEq
      (Nat.le_add_left 1 s) hUpdate
    rw [Nat.add_sub_cancel] at h
    exact (compatible_iff _ _).2 (Or.inr (ancestorEq_trans hBF
      (by rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]; exact h C' hsave)))

/-- The receiver's side of the deliveries: when `v`'s finalized block before `c` is `B` or an
ancestor of `B`, its finalized block one delay after the vote time of `s` is compatible with every
block compatible with `B`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `B`: the block; `v`:
  the receiver; `D`: the block compatible with `B`.

Read aloud: `v`'s finalized block one delay after the vote time of slot `s` is compatible with `D`,
when `D` is compatible with `B` and `v`'s finalized block before the support cutoff of slot `s + 1`
is `B` or an ancestor of `B`. -/
theorem F_compatible_of_le_ancestorEq (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (B : Block V) (v : V) (D : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hFB : (x.stateBefore (M.supportCutoff S.C (s + 1)) v).finalized.AncestorEq B)
    (hDB : D.compatible B = true) :
    (x.stateBefore (M.voteTime S.C s + Δ S) v).finalized.compatible D = true := by
  have hle : M.voteTime S.C s + Δ S ≤ M.supportCutoff S.C (s + 1) := by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
    have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
    have h4 : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
    omega
  have hFe := ancestorEq_trans ((stateBefore_grows M F) x R E v hle).2.1 hFB
  rcases (compatible_iff _ _).1 hDB with hDB' | hBD
  · exact (compatible_iff _ _).2 (ancestorEq_compatible hFe hDB')
  · exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFe hBD))

/-- **Lemma 78c, an honest confirmation update over a majority whose votes are compatible with
`B`.** The proof; the audited statement is in
`Statements/Executions/ConfirmationCompatStatements.lean`. `lem78c_of_delivered`, with each
member's vote delivered into `v`'s pool (`unique_vote_of_owner`)
and its block into `v`'s tree (`mem_T_before_add_delay`) before the support cutoff of `s`, as
Lemma 12's steps 2 to 4.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the votes; `Hs`: the voters; `H`: their blocks; `B`:
  the block; `v`: the validator whose update it is.

Read aloud: the confirmation `v` saves for slot `s` at the support cutoff of slot `s + 1` is
compatible with `B`, when the honest voters of `Hs`, who voted for blocks compatible with `B`, are
more than half of the voters `v` counts and `v`'s finalized block is compatible with `B`. -/
theorem lem78c_update_confirmation_compatible_of_voter_majority
    (U : UniformSchedule M.toSlotLayout)
    (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (B : Block V) (v : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    -- the window of one delay or one sync delay before the support cutoff of `s` is in the synchronous period
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ (H u).compatible B = true)
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
      C'.compatible B = true := by
  -- the slot layout: the support cutoff of `s` is before that of `s + 1`
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
  -- `v`'s tick to the support cutoff of slot `s + 1`
  obtain ⟨kc, hkc, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have hkcs : x.tickStep v (M.supportCutoff S.C (s + 1)) = kc := (tickStep_eq_of_lbl M) x E hkc
  refine (lem78c_of_delivered M F U) S A x R s Hs H B v E ?_ (fun u hu => (hHs u hu).2.2.2.2) hVoters hv hF
  -- when `v`'s finalized block is `B` or an ancestor of `B`, it is compatible with every voter's block (one compatible
  -- with `B`), and Lemma 12 at `v`'s tick gives the votes
  intro hFB
  refine (lem12_honest_vote_delivered_until_of_steps_compat M F U) S A x R GST s (M.supportCutoff S.C (s + 1)) Hs H v
    E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST (by omega) kc hkc
    (fun u hu => ⟨(hHs u hu).1, hkcs ▸ (hHs u hu).2.1, (hHs u hu).2.2.1, (hHs u hu).2.2.2.1⟩)
    hHold ((updater_reader_gives_core_window M F U) x R E hΔs hSkew hv) (fun u hu => ?_)
  rcases (compatible_iff _ _).1 (hHs u hu).2.2.2.2 with hHB | hBH
  · exact (compatible_iff _ _).2 (ancestorEq_compatible hFB hHB)
  · exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFB hBH))

theorem lem78c_update_confirmation_compatible_of_voter_majority_upTo
    (U : UniformSchedule M.toSlotLayout)
    (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (B : Block V) (v : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    -- the window of one delay or one sync delay before the support cutoff of `s` is in the synchronous period
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ (H u).compatible B = true)
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
      C'.compatible B = true := by
  -- the slot layout: the support cutoff of `s` is before that of `s + 1`
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
  -- `v`'s tick to the support cutoff of slot `s + 1`
  obtain ⟨kc, hkc, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have hkcs : x.tickStep v (M.supportCutoff S.C (s + 1)) = kc := (tickStep_eq_of_lbl M) x E hkc
  refine (lem78c_of_delivered M F U) S A x R s Hs H B v E ?_ (fun u hu => (hHs u hu).2.2.2.2) hVoters hv hF
  -- when `v`'s finalized block is `B` or an ancestor of `B`, it is compatible with every voter's block (one compatible
  -- with `B`), and Lemma 12 at `v`'s tick gives the votes
  intro hFB
  refine (lem12_honest_vote_delivered_until_of_steps_upTo_compat M F U) S A x R GST s (M.supportCutoff S.C (s + 1)) Hs H v
    E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST (by omega) kc hkc
    (fun u hu => ⟨(hHs u hu).1, hkcs ▸ (hHs u hu).2.1, (hHs u hu).2.2.1, (hHs u hu).2.2.2.1⟩)
    hHold ((updater_reader_gives_core_window M F U) x R E hΔs hSkew hv) (fun u hu => ?_)
  rcases (compatible_iff _ _).1 (hHs u hu).2.2.2.2 with hHB | hBH
  · exact (compatible_iff _ _).2 (ancestorEq_compatible hFB hHB)
  · exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFB hBH))

end GoldilocksCorrectness.Record.Proofs.Executions

