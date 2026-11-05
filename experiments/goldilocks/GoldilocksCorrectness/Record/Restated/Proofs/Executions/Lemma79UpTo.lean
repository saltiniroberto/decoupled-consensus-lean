module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma79
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.NextSlotVoteStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma78UpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma79
public import GoldilocksCorrectness.Statements.Executions.NextSlotVoteStatementsUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma78UpTo
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma79UpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma79UpTo.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: Lemmas 79a, 79c and 79, the step of the
slot invariant restricted to a block, with the delivery premises up to a bound. The page's
routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono dutyWindowStart_succ_le_slotStart
  one_le_Δ slotStart_eq supportCutoff_eq voteTime_eq voteTime_succ)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor VoterTreeAt)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

open Classical in
/-- Lemma 79a, the first clause of the step. The proof; the audited statement is in
`Statements/Executions/HonestChainStatements.lean`.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C s'`: Lemma 26b,
which the proof calls at slot `s'`, takes them up to the voter's own tick to that cutoff, which can come after
its real time.

Restated with the delivery premises up to `M.supportCutoff S.C s'`: the slot-`s'` votes reach every
voter of slot `s' + 1` by then (`lem26b_goldfish_vote_extends_voter_majority_block_held_upTo`).

The variables:
- `M`: the model; `F`: its facts.

Read aloud: under the invariant at slot `s'`, the members' votes of slot `s' + 1` are for blocks
they hold on `B`'s chain. -/
theorem lem79a_honestChainExtends_votes_step_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s' : ℕ) (Hon : Finset V) (Hs : Finset V) (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s')) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s'))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s'`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s' →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s')
    (hInv : HonestChainExtends M S A x Hon B s')
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughout x (M.dutyWindowStart S.C (s' + 1)) (M.voteTime S.C (s' + 1)))
    -- no member is in the adversary set at a step where a validator outside it ticks to the vote time of slot
    -- `s' + 1` (the second honesty read,; Lemma 26b reads the voters' honesty at the member's tick)
    (hHonTick : ∀ u ∈ Hon, u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.voteTime S.C (s' + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    (hHs : ∀ u ∈ Hs, u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    (hVotersW : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s' + 1))) (s' + 1) votes
        support_votes →
      M.voters_count votes < 2 * Hs.card)
    (hF2 : ∀ w ∈ Hon,
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.compatible B = true)
    (hF3 : ∀ w ∈ Hon,
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.AncestorEq B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s' + 1)))
          (S.C.t_ ((s' + 1) - 1) + 3 * S.C.Δ) (s' + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).viable_heads ∧
        B.AncestorEq W) :
    ∀ u ∈ Hon, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).tree,
        vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ B.AncestorEq H_u := by
  intro w hw vote hSend
  -- the times
  have hΔ := one_le_Δ S
  have hdw : M.dutyWindowStart S.C (s' + 1) ≤ M.slotStart S.C s' := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S s'
  have hv₁ : M.voteTime S.C s' = M.slotStart S.C s' + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s'
  have hc₁ : M.supportCutoff S.C s' = M.voteTime S.C s' + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s'
  have hv₂ : M.voteTime S.C (s' + 1) = M.voteTime S.C s' + 4 * Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S s'
  -- each voter of slot `s'` voted for a block it holds on `B`'s chain (clause 1)
  have hvote : ∀ u ∈ Hs, ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s' H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree ∧ B.AncestorEq H_u := by
    intro u hu
    obtain ⟨huHon, -, vote', -, -, hsent⟩ := hHs u hu
    obtain ⟨H_u, hHT, hvt, hBH⟩ := hInv.1 u huHon vote' hsent
    subst hvt
    exact ⟨H_u, hsent, hHT, hBH⟩
  choose H hH using hvote
  let H' : V → Block V := fun u => if h : u ∈ Hs then H u h else B
  have hH' : ∀ u (hu : u ∈ Hs), H' u = H u hu := fun u hu => dif_pos hu
  -- Lemma 12's receiver window for `w` and holder window for each voter, from the members' window
  have hwin := fun u (hu : u ∈ Hon) => (dutyWindow_gives_core_window_and_hold M F U) x R E hΔs hSkew
    hGST (hHon u hu)
  obtain ⟨kR, hkR, -⟩ := (hwin w hw).1
  have hkRs : x.tickStep w (M.supportCutoff S.C s') = kR := (tickStep_eq_of_lbl M) x E hkR
  exact (GoldilocksCorrectness.Record.Statements.Executions.lem26b_goldfish_vote_extends_voter_majority_block_held_upTo M F U)
    S A x R GST s' Hs H' B w vote E hNet hSkew hRedeliver Sy hΔs (by rw [hkRs]; exact hRoots kR w _ hkR le_rfl)
    hParent hOwner hGST
    (fun u hu => by
      rw [hH' u hu]
      exact ⟨(hHs u hu).2.1,
        (not_mem_corrupted_tickStep_of_outside_at_honest_ticks_of_lbl M F) x E hSend.choose_spec.1
          (hHonTick u (hHs u hu).1),
        (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
    (hVotersW w hw) (fun u hu => (hwin u (hHs u hu).1).2) (hwin w hw).1 (hF2 w hw) (hF3 w hw)
    (hInv.2.1 w hw) hSend

open Classical in
/-- Lemma 79c, the third clause of the step. The proof; the audited statement is in
`Statements/Executions/HonestChainStatements.lean`.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C (s' + 1)`: Lemma 78,
which the proof calls at slot `s' + 1`, reads them at each member's own tick to that cutoff.

Restated with the delivery premises up to `M.supportCutoff S.C (s' + 1)`: the slot-`(s' + 1)` votes
reach every updater by then (`lem78_update_confirmation_extends_voter_majority_chain_upTo`).

The variables:
- `M`: the model; `F`: its facts.

Read aloud: when the members' votes of slot `s' + 1` are on `B`'s chain, their confirmations of slot
`s' + 1` are too. -/
theorem lem79c_honestChainExtends_confirmations_step_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s' : ℕ) (Hon : Finset V) (Hs : Finset V) (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s' + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s' + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s' + 1`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s' + 1))
    (hVotes : ∀ u ∈ Hon, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).tree,
        vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ B.AncestorEq H_u)
    -- each member runs the update of slot `s' + 1`: it ticks to the support cutoff of slot `s' + 2`, active up to that
    -- tick from a tick at or before the duty window's start of slot `s' + 2`
    (hHon : ∀ v ∈ Hon, v ∈ updaterAt M S A x (s' + 1))
    -- no member is in the adversary set at a step where a validator outside it ticks to the support cutoff of
    -- slot `s' + 2` (, the second honesty read of)
    (hHonTick : ∀ u ∈ Hon, u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 2)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    (hHs : ∀ u ∈ Hs, u ∈ Hon ∧ u ∈ S.P.committee (s' + 1) ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' + 1 ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    (hVotersV : ∀ v ∈ Hon,
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 2))) (s' + 1)) <
        2 * Hs.card)
    (hFv : ∀ v ∈ Hon,
      (x.tickInput v (M.supportCutoff S.C (s' + 2))).finalized.compatible B = true) :
    ∀ v ∈ Hon, ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 2))).savedConfirmation (s' + 1) = some C' →
      B.AncestorEq C' := by
  intro v hv
  -- each voter of slot `s' + 1` voted for a block it holds on `B`'s chain
  have hvote : ∀ u ∈ Hs, ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s' + 1) H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H_u ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).tree ∧ B.AncestorEq H_u := by
    intro u hu
    obtain ⟨huHon, -, vote', -, -, hsent⟩ := hHs u hu
    obtain ⟨H_u, hHT, hvt, hBH⟩ := hVotes u huHon vote' hsent
    subst hvt
    exact ⟨H_u, hsent, hHT, hBH⟩
  choose H hH using hvote
  let H' : V → Block V := fun u => if h : u ∈ Hs then H u h else B
  have hH' : ∀ u (hu : u ∈ Hs), H' u = H u hu := fun u hu => dif_pos hu
  -- `v`'s tick to the support cutoff of slot `s' + 1`, inside its reader, for the roots
  obtain ⟨kR, hkR, -⟩ := (updater_reader_gives_core_window M F U) x R E hΔs hSkew (hHon v hv)
  exact (lem78_update_confirmation_extends_voter_majority_chain_upTo M F U) S A x R GST (s' + 1) Hs H' B v
    E hNet hSkew hRedeliver Sy hΔs ((roots_at_own_tick_of_per_tick M F) x E hRoots hkR) hParent hOwner hGST
    (fun u hu => by
      rw [hH' u hu]
      exact ⟨(hHs u hu).2.1,
        (not_mem_corrupted_tickStep_of_outside_at_honest_ticks M F) x E (hHon v hv) (hHonTick u (hHs u hu).1),
        (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
    (fun u hu => (holder_window_of_updater_reader M F U) x R E hΔs hSkew hGST (hHon u (hHs u hu).1))
    (hVotersV v hv) (hHon v hv) (hFv v hv)

open Classical in
/-- Lemma 79, the step of the restricted slot invariant. The proof; the audited statement is in
`Statements/Executions/HonestChainStatements.lean`.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C (s' + 1)`: Lemma 79c,
which the proof calls, reads them there; Lemma 79a reads them up to the support cutoff of slot `s'`.

Restated with the delivery premises up to `M.supportCutoff S.C (s' + 1)`: the slot-`(s' + 1)` votes
reach every updater by then (`lem79c_honestChainExtends_confirmations_step_upTo`).

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the invariant at slot `s'` gives the invariant at slot `s' + 1`, when the members stay
awake and honest through the next slot, the honest voters of each slot are a majority of the voters
the members count, and the members' finalized blocks and fork-choice roots are compatible with `B`.
-/
theorem lem79_honestChainExtends_step_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s' : ℕ) (Hon : Finset V) (Hs : ℕ → Finset V) (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s' + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s' + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s' + 1`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s')
    (hInv : HonestChainExtends M S A x Hon B s')
    -- the members of `Hon` are active at every real time from the duty window's start of slot `s' + 1` to its vote
    -- time (Lemma 79a's read), and each runs the update of slot `s' + 1`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughout x (M.dutyWindowStart S.C (s' + 1)) (M.voteTime S.C (s' + 1)))
    (hHonUpd : ∀ v ∈ Hon, v ∈ updaterAt M S A x (s' + 1))
    -- no member is in the adversary set at a step where a validator outside it ticks to the support cutoff of
    -- slot `s' + 2` (, the second honesty read of)
    (hHonTick : ∀ u ∈ Hon, u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 2)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    (hHs : ∀ s₀ : ℕ, s₀ = s' ∨ s₀ = s' + 1 → ∀ u ∈ Hs s₀, u ∈ Hon ∧ u ∈ S.P.committee s₀ ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s₀ ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s₀) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    (hVotersW : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s' + 1))) (s' + 1) votes
        support_votes →
      M.voters_count votes < 2 * (Hs s').card)
    (hVotersV : ∀ v ∈ Hon,
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 2))) (s' + 1)) <
        2 * (Hs (s' + 1)).card)
    (hF2 : ∀ w ∈ Hon,
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.compatible B = true)
    (hF3 : ∀ w ∈ Hon,
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.AncestorEq B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s' + 1)))
          (S.C.t_ ((s' + 1) - 1) + 3 * S.C.Δ) (s' + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).viable_heads ∧
        B.AncestorEq W)
    (hFv : ∀ v ∈ Hon,
      (x.tickInput v (M.supportCutoff S.C (s' + 2))).finalized.compatible B = true) :
    HonestChainExtends M S A x Hon B (s' + 1) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  -- the times
  obtain ⟨hv0, hc0, -, hs0, -, hk8, hΔ⟩ := (slot_times M F U) S s'
  obtain ⟨hv1, hc1, -, hs1, -, -, -⟩ := (slot_times M F U) S (s' + 1)
  obtain ⟨hv2, hc2, -, hs2, -, -, -⟩ := (slot_times M F U) S (s' + 2)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s'
  have hdw2 := duty_window_start_real S (s' + 2)
  push_cast at hdw2
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hv1R : ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 5 * Δ S := by
    rw [hv1, hs0, hss]; push_cast; ring
  have hv2R : ((M.voteTime S.C (s' + 2) : ℕ) : ℝ) = 4 * Δ S * s' + 9 * Δ S := by
    rw [hv2, show s' + 2 = s' + 1 + 1 by omega, hs1, hs0, hss]; push_cast; ring
  have hc2R : ((M.supportCutoff S.C (s' + 2) : ℕ) : ℝ) = 4 * Δ S * s' + 10 * Δ S := by
    rw [hc2, show s' + 2 = s' + 1 + 1 by omega, hs1, hs0, hss]; push_cast; ring
  have hcc : M.supportCutoff S.C s' ≤ M.supportCutoff S.C (s' + 1) := by omega
  -- clause 1 (Lemma 79a), with the roots per tick up to the support cutoff of slot `s'`
  have h1 := (lem79a_honestChainExtends_votes_step_upTo M F U) S A x R GST s' Hon (Hs s') B (E.mono hcc) hNet hSkew hRedeliver (Sy.mono hcc) hΔs
    (fun k u c hk hc => hRoots k u c hk (le_trans hc hcc)) hParent hOwner hGST hInv hHon
    (fun u hu => (outside_at_honest_ticks_of_mem_activeThroughoutToTick M F) x R E (hHonUpd u hu)
      (by
        have hv1c2 : ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) + 5 * Δ S = ((M.supportCutoff S.C (s' + 2) : ℕ) : ℝ) := by
          rw [hv1R, hc2R]; ring
        linarith))
    (hHs s' (Or.inl rfl)) hVotersW hF2 hF3
  -- every member ticks to the vote time of slot `s' + 1`, active up to that tick from its tick to a
  -- clock value at most the duty window's start of slot `s' + 2`: its reader of slot `s' + 1`
  have hwin : ∀ w ∈ Hon, w ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (s' + 2) : ℕ) : ℤ) (M.voteTime S.C (s' + 1)) :=
    fun w hw => (reader_from_updater_under_skew M F U) S A x R s' w E hSkew (hHonUpd w hw)
  refine ⟨h1, ?_, ?_⟩
  · -- clause 2 (Lemma 79b), on the revocation the outcome of a member's tick to the vote time of slot `s' + 2` ran
    -- from its tick input (the field `tick_voteTime_locks_of_core` of `F.tk2`)
    intro w hw n' sent hrun hAwake e he hlive
    have hsl : S.C.slot ((M.voteTime S.C (s' + 1 + 1) : ℕ) : Int) = s' + 1 + 1 := by
      rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
        ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
      exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
        (by rw [show s' + 1 + 1 = s' + 2 by omega]; omega) (by rw [show s' + 1 + 1 = s' + 2 by omega]; omega)
    have hInvW := (lem11_node_invariantCore_of_run M F S x R (x.tickStep w (M.voteTime S.C (s' + 1 + 1))) w).1
    have hRevoke := F.tk2.tick_voteTime_locks_of_core S.C S.P S.X _ _ n' sent hrun hInvW
      (by
        rw [hsl]
        exact (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U) S (s' + 1 + 1))
      (by rw [hsl]; exact hAwake)
    rw [hsl] at hRevoke
    exact (lem79b_honestChainExtends_locks_step M F U) S A x R s' Hon B E hInv hwin w hw n' hRevoke e he hlive
  · -- clause 3 (Lemma 79c)
    exact (lem79c_honestChainExtends_confirmations_step_upTo M F U) S A x R GST s' Hon (Hs (s' + 1)) B E hNet hSkew
      hRedeliver Sy hΔs hRoots hParent hOwner
      (le_trans hGST hcc) h1 hHonUpd hHonTick (hHs (s' + 1) (Or.inr rfl)) hVotersV hFv

end GoldilocksCorrectness.Record.Proofs.Executions

