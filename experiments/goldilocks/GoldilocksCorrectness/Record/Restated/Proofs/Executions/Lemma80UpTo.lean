module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma80
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.NextSlotVoteStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma79UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.NetworkUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ProposalWalkUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundBaseUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma80
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.NextSlotVoteStatementsUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma79UpTo
public import GoldilocksCorrectness.Proofs.Executions.NetworkUpTo
public import GoldilocksCorrectness.Proofs.Executions.ProposalWalkUpTo
public import GoldilocksCorrectness.Proofs.Executions.RoundBaseUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma80UpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma80UpTo.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: the steps of Lemma 80, the slot invariant
carried from slot to slot over two sets and through the round, the attestations of the round in the
pools, the proposal's extension and the round's height advance, with the delivery premises up to a
bound. The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono dutyWindowStart_succ_le_slotStart
  one_le_Δ slotStart_eq slotStart_le_of_le slot_add_two_le_of_delivery supportCutoff_eq
  supportCutoff_le_slotStart_succ voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (on_attestation_pool)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated LocksRevoked
  VoterTreeAt)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes FrameShape
  ProposalCountedVotes)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_of_parent? compatible_of_ancestorEq_compatible)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

open Classical in
/-- **Kit theorem, Lemma 79a over two sets.** As Lemma 79a, with the voters of slot `s'` in `Hon`
(where the invariant is read) and the votes of slot `s' + 1` read at the members of `Hon' ⊆ Hon M`:
if `HonestChainExtends M S Sched x (Hon M) B s'` holds, every member of `Hs` is a member of `Hon`
voting at slot `s'` and honest at the vote time of slot `s' + 1` and active through the sync delay after Lemma 12's read time at slot `s'`, and every member `w` of `Hon'` is
awake and honest from the duty window's start of slot `s' + 1` to its vote time, counts fewer than
twice `Hs`, has its fork-choice root compatible with `B` and, when that root is `B` or an ancestor
of `B`, a viable head of its voter tree on `B`'s chain — then every slot-`(s' + 1)` vote of a member
of `Hon'` is for a block it holds on `B`'s chain.

Why: Lemma 26b at each member of `Hon'`, the voters' blocks from the invariant's first clause and
the member's locks from its second clause.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `s'`: the slot; `Hon`, `Hon'`: the two sets; `Hs`: the honest voters of slot
  `s'`; `B`: the block.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C s'`: Lemma 26b, which
the proof calls at slot `s'`, reads them at each member's own tick to that cutoff.

Restated with the delivery premises up to `M.supportCutoff S.C s'`: Lemma 26b at slot `s'` reads
deliveries due by then (`lem26b_goldfish_vote_extends_voter_majority_block_held_upTo`).

Read aloud: when the honest chain extends `B` at slot `s'` for `Hon`, every slot-`(s' + 1)` vote of
a member of `Hon'` is for a block it holds on `B`'s chain, with the delivery premises up to the
bound. -/
theorem lem79a_votes_step_sets_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s' : ℕ) (Hon Hon' Hs : Finset V) (B : Block V)
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
    (hSub : Hon' ⊆ Hon)
    -- no voter of `Hs` is in the adversary set at a step where a validator outside it ticks to the vote time of slot
    -- `s' + 1` (Lemma 26b reads the voters' honesty at the member's tick)
    (hHsHon : ∀ u ∈ Hs, u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.voteTime S.C (s' + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- every member of `Hon'` ticks to the support cutoff of slot `s'` and is active at every step from Lemma 12's read
    -- time `supportCutoff s' − max (2 * Δ S) Δs` up to that tick (Lemma 12's receiver window, all the proof reads of
    -- the members' activity;)
    (hCore' : ∀ v ∈ Hon', ∃ kR : ℕ, x.lbl kR = Event.tick v (M.supportCutoff S.C s') ∧
      ∀ i : ℕ, ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time i → i ≤ kR → v ∈ A.active i)
    (hHs : ∀ u ∈ Hs, u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- every voter of `Hs` is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s' − max (2 * Δ S) Δs` (: Lemma 26b's holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hVotersW : ∀ w ∈ Hon', ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s' + 1)))
        (s' + 1) votes support_votes →
      M.voters_count votes < 2 * Hs.card)
    (hF2 : ∀ w ∈ Hon',
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.compatible B = true)
    (hF3 : ∀ w ∈ Hon',
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.AncestorEq B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s' + 1)))
        (S.C.t_ ((s' + 1) - 1) + 3 * S.C.Δ) (s' + 1) W ∧ W ∈
          (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).viable_heads ∧
          B.AncestorEq W) :
    ∀ u ∈ Hon', ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).tree,
        vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ B.AncestorEq H_u := by
  intro w hw vote hSend
  -- each voter of slot `s'` voted for a block it holds on `B`'s chain (clause 1 of the invariant at `Hon`)
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
  -- Lemma 12's receiver window for `w` (the row `hCore'`;)
  obtain ⟨kR, hkR, -⟩ := hCore' w hw
  have hkRs : x.tickStep w (M.supportCutoff S.C s') = kR := (tickStep_eq_of_lbl M) x E hkR
  exact (GoldilocksCorrectness.Record.Statements.Executions.lem26b_goldfish_vote_extends_voter_majority_block_held_upTo M F U)
    S A x R GST s' Hs H' B w vote E hNet hSkew hRedeliver Sy hΔs (by rw [hkRs]; exact hRoots kR w _ hkR le_rfl)
    hParent hOwner hGST
    (fun u hu => by
      rw [hH' u hu]
      exact ⟨(hHs u hu).2.1,
        (not_mem_corrupted_tickStep_of_outside_at_honest_ticks_of_lbl M F) x E hSend.choose_spec.1 (hHsHon u hu),
        (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
    (hVotersW w hw) hHold (hCore' w hw) (hF2 w hw) (hF3 w hw)
    (hInv.2.1 w (hSub hw)) hSend

open Classical in
/-- **Kit theorem, Lemma 79's step from one slot's set to the next.** As Lemma 79, with the voters
of slot `s'` in `Hon`, awake and honest from the duty window's start of slot `s'` to the support
cutoff of slot `s' + 1`, and the voters of slot `s' + 1` and the members in `Hon' ⊆ Hon M`, awake
and honest from the duty window's start of slot `s' + 1` to the support cutoff of slot `s' + 2`; the
counting and frame conditions are read at the members of `Hon'` — then
`HonestChainExtends M S Sched x (Hon M) B s'` gives
`HonestChainExtends M S Sched x Hon' B (s' + 1)`.

Why: `lem79a_votes_step_sets`; Lemma 79b at `Hon'` with the invariant restricted
(`honestChainExtends_mono`); Lemma 79c at `Hon'`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `s'`: the slot; `Hon`, `Hon'`: the sets of slots `s'` and `s' + 1`; `Hs`: the
  honest voters of each slot; `B`: the block.

Read aloud: each slot's voters need to be honest only through their own slot's update.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C (s' + 1)`: Lemma 79c,
which the proof calls at slot `s'`, reads them there; `lem79a_votes_step_sets` reads them up to the support cutoff
of slot `s'`.

Restated with the delivery premises up to `M.supportCutoff S.C (s' + 1)`: Lemma 79c at slot `s'`
reads deliveries due by then (`lem79c_honestChainExtends_confirmations_step_upTo`); Lemma 79a reads
earlier. -/
theorem lem79_step_sets_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s' : ℕ) (Hon Hon' : Finset V) (Hs : ℕ → Finset V) (B : Block V)
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
    (hSub : Hon' ⊆ Hon)
    -- each member of `Hon` runs the update of slot `s'`
    (hHon : ∀ v ∈ Hon, v ∈ updaterAt M S A x s')
    -- the members of `Hon'` tick to the vote time of slot `s' + 1`, active up to that tick from the trace's start or
    -- from their own tick to a clock value at most the duty window's start of slot `s' + 1`, each runs
    -- the update of slot `s' + 1`, and none is in the adversary set at a step where a validator outside it ticks to the
    -- support cutoff of slot `s' + 2`
    (hHon' : ∀ v ∈ Hon', v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s' + 1)) (M.voteTime S.C (s' + 1)))
    (hHonUpd' : ∀ v ∈ Hon', v ∈ updaterAt M S A x (s' + 1))
    (hHonTick' : ∀ u ∈ Hon', u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 2)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    (hHs : ∀ u ∈ Hs s', u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    (hHs' : ∀ u ∈ Hs (s' + 1), u ∈ Hon' ∧ u ∈ S.P.committee (s' + 1) ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' + 1 ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    (hVotersW : ∀ w ∈ Hon', ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s' + 1)))
        (s' + 1) votes support_votes →
      M.voters_count votes < 2 * (Hs s').card)
    (hVotersV : ∀ v ∈ Hon',
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 2))) (s' + 1)) <
        2 * (Hs (s' + 1)).card)
    (hF2 : ∀ w ∈ Hon',
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.compatible B = true)
    (hF3 : ∀ w ∈ Hon',
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.AncestorEq B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s' + 1)))
        (S.C.t_ ((s' + 1) - 1) + 3 * S.C.Δ) (s' + 1) W ∧ W ∈
          (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).viable_heads ∧
          B.AncestorEq W)
    (hFv : ∀ v ∈ Hon',
      (x.tickInput v (M.supportCutoff S.C (s' + 2))).finalized.compatible B = true) :
    HonestChainExtends M S A x Hon' B (s' + 1) := by
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
  have hc1R : ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 6 * Δ S := by
    rw [hc1, hs0, hss]; push_cast; ring
  have hv2R : ((M.voteTime S.C (s' + 2) : ℕ) : ℝ) = 4 * Δ S * s' + 9 * Δ S := by
    rw [hv2, show s' + 2 = s' + 1 + 1 by omega, hs1, hs0, hss]; push_cast; ring
  have hc2R : ((M.supportCutoff S.C (s' + 2) : ℕ) : ℝ) = 4 * Δ S * s' + 10 * Δ S := by
    rw [hc2, show s' + 2 = s' + 1 + 1 by omega, hs1, hs0, hss]; push_cast; ring
  have hcc : M.supportCutoff S.C s' ≤ M.supportCutoff S.C (s' + 1) := by omega
  have hInv' := (honestChainExtends_mono M F) S A x Hon Hon' B s' hSub hInv
  -- clause 1 (`lem79a_votes_step_sets`): the voters of slot `s'`, updaters of slot `s'`, are honest at the vote time
  -- of slot `s' + 1`, before their ticks to the support cutoff of slot `s' + 1`
  have h1 := (lem79a_votes_step_sets_upTo M F U) S A x R GST s' Hon Hon' (Hs s') B (E.mono hcc) hNet hSkew hRedeliver (Sy.mono hcc) hΔs
    (fun k u c hk hc => hRoots k u c hk (le_trans hc hcc)) hParent hOwner hGST hInv hSub
    (fun u hu => (outside_at_honest_ticks_of_mem_activeThroughoutToTick M F) x R E (hHon u (hHs u hu).1)
      (by rw [hv1R, hc1R]; linarith))
    (fun v hv => (core_window_of_dutyWindow_reader M F U) x R E hΔs hSkew hGST (hHon' v hv)) hHs
    (fun u hu => (holder_window_of_updater_reader M F U) x R E hΔs hSkew hGST (hHon u (hHs u hu).1))
    hVotersW hF2 hF3
  -- every member of `Hon'` ticks to the vote time of slot `s' + 1`, active up to that tick from its tick to a
  -- clock value at most the duty window's start of slot `s' + 2`: its reader of slot `s' + 1`
  have hwin : ∀ w ∈ Hon', w ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (s' + 2) : ℕ) : ℤ) (M.voteTime S.C (s' + 1)) :=
    fun w hw => (reader_from_updater_under_skew M F U) S A x R s' w E hSkew (hHonUpd' w hw)
  refine ⟨h1, ?_, ?_⟩
  · -- clause 2 (Lemma 79b at `Hon'`), on the revocation the outcome of a member's tick to the vote time of slot
    -- `s' + 2` ran from its tick input (the field `tick_voteTime_locks_of_core` of `F.tk2`)
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
    exact (lem79b_honestChainExtends_locks_step M F U) S A x R s' Hon' B E hInv' hwin w hw n' hRevoke e he hlive
  · -- clause 3 (Lemma 79c at `Hon'`)
    exact (lem79c_honestChainExtends_confirmations_step_upTo M F U) S A x R GST s' Hon' (Hs (s' + 1)) B E hNet hSkew
      hRedeliver Sy hΔs hRoots hParent hOwner (le_trans hGST hcc) h1 hHonUpd' hHonTick' hHs' hVotersV hFv

open Classical in
/-- **Kit theorem, the slot invariant through the round, over per-slot sets.** With the member
sets `Hon M s'` shrinking from slot to slot, each awake and honest through its slot's update and not
past the start of slot `s₂ + 2`, the honest voters of each slot in its set, the counts of each slot
read at its set, `StepFrameAt` relative to `B` at the members of `Hon M (s' + 1)` for every slot
`s'` with `s' + 3 ≤ s₂ + 2`, and the voter's fork choice of slot `s₂ + 1` at the members of
`Hon M (s₂ + 1)`: from `HonestChainExtends M S Sched x (Hon M s) B s`, the invariant holds at slot
`s₂` for `Hon M s₂`, and every slot-`(s₂ + 1)` vote of a member of `Hon M (s₂ + 1)` is for a block
it holds on `B`'s chain.

Why: `lem79_step_sets` at each slot from `s` to `s₂ − 1`, then `lem79a_votes_step_sets` at `s₂`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `s`: the first slot; `s₂`: the last slot the invariant is carried to; `Hon`: the
  member sets; `Hs`: the honest voters of each slot; `B`: the proposal.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C s₂`:
`lem79a_votes_step_sets`, which the proof calls at slot `s₂`, reads them there; the steps before it read them up to
earlier cutoffs.

Restated with the delivery premises up to `M.supportCutoff S.C s₂`: the step at the last slot
`s₂ − 1` reads deliveries due by then (`lem79_step_sets_upTo`), the vote clause at `s₂` likewise
(`lem79a_votes_step_sets_upTo`).

Read aloud: the honest chain extends `B` at every slot of the round for that slot's members, and the
votes of the round's last slot are on `B`'s chain, with the delivery premises up to the bound. -/
theorem round_honestChainExtends_steps_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s s₂ : ℕ) (Hon Hs : ℕ → Finset V) (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s₂)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s₂))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s₂`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s₂ →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hs₂ : s ≤ s₂)
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s₂ + 2 → Hon (s' + 1) ⊆ Hon s')
    -- the members of slot `s'` tick to its vote time, active up to that tick from the trace's start or from their own
    -- tick to a clock value at most the duty window's start of slot `s'`
    (hHon : ∀ s', s ≤ s' → s' < s₂ + 2 → ∀ v ∈ Hon s',
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C s') (M.voteTime S.C s'))
    -- for every slot `s'` before the last, each member of slot `s'` runs the update of slot `s'`, and none is in the
    -- adversary set at a step where a validator outside it ticks to the support cutoff of slot `s' + 1`
    (hHonUpd : ∀ s', s ≤ s' → s' + 1 < s₂ + 2 → ∀ v ∈ Hon s', v ∈ updaterAt M S A x s')
    (hHonTick : ∀ s', s ≤ s' → s' + 1 < s₂ + 2 → ∀ u ∈ Hon s', u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    (hHs : ∀ s', s ≤ s' → s' < s₂ + 2 → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    (hVoters : ∀ s', s ≤ s' → s' < s₂ + 2 → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s₂ + 2 → ∀ w ∈ Hon (s' + 1), StepFrameAt M S A x B s' w)
    (hStepLast : ∀ w ∈ Hon (s₂ + 1),
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s₂ + 1)))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (s₂ + 1)))).fc_root.AncestorEq B →
        ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s₂ + 1)))
          (S.C.t_ ((s₂ + 1) - 1) + 3 * S.C.Δ) (s₂ + 1) W ∧ W ∈
            (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s₂ + 1)))).viable_heads ∧
            B.AncestorEq W))
    (hBase : HonestChainExtends M S A x (Hon s) B s) :
    HonestChainExtends M S A x (Hon s₂) B s₂ ∧
    ∀ u ∈ Hon (s₂ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s₂ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s₂ + 1))).tree,
        vote = GoldfishVote.mk u (s₂ + 1) H_u.root ∧ B.AncestorEq H_u := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hv : ∀ k, M.voteTime S.C k = M.slotStart S.C k + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
  have hc : ∀ k, M.supportCutoff S.C k = M.voteTime S.C k + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
  -- the induction
  have key : ∀ d, s + d ≤ s₂ → HonestChainExtends M S A x (Hon (s + d)) B (s + d) := by
    intro d
    induction d with
    | zero => intro _; exact hBase
    | succ d ih =>
        intro hd
        have hcut : M.supportCutoff S.C (s + d + 1) ≤ M.supportCutoff S.C s₂ :=
          (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
        exact (lem79_step_sets_upTo M F U) S A x R GST (s + d) (Hon (s + d)) (Hon (s + d + 1)) Hs B (E.mono hcut) hNet hSkew hRedeliver
          (Sy.mono hcut) hΔs
          (fun k u c hk hc' => hRoots k u c hk (le_trans hc' hcut))
          hParent hOwner
          (le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
            (Nat.le_add_right s d))) (ih (by omega))
          (hHonMono (s + d) (by omega) (by omega))
          (hHonUpd (s + d) (by omega) (by omega))
          (hHon (s + d + 1) (by omega) (by omega))
          (hHonUpd (s + d + 1) (by omega) (by omega))
          (hHonTick (s + d + 1) (by omega) (by omega))
          (hHs (s + d) (by omega) (by omega)) (hHs (s + d + 1) (by omega) (by omega))
          (fun w hw => (hVoters (s + d) (by omega) (by omega) w
            (hHonMono (s + d) (by omega) (by omega) hw)).1)
          (fun v hv' => (hVoters (s + d + 1) (by omega) (by omega) v hv').2)
          (fun w hw => (hStep (s + d) (by omega) (by omega) w hw).1)
          (fun w hw => (hStep (s + d) (by omega) (by omega) w hw).2.1)
          (fun v hv' => (hStep (s + d) (by omega) (by omega) v hv').2.2)
  obtain ⟨d, rfl⟩ : ∃ d, s₂ = s + d := ⟨s₂ - s, by omega⟩
  have hInv := key d le_rfl
  have hv1 := hv (s + d + 1)
  have hc1 := hc (s + d + 1)
  refine ⟨hInv, ?_⟩
  exact (lem79a_votes_step_sets_upTo M F U) S A x R GST (s + d) (Hon (s + d)) (Hon (s + d + 1)) (Hs (s + d))
    B E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner
    (le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (Nat.le_add_right s d))) hInv
    (hHonMono (s + d) (by omega) (by omega))
    -- the voters of slot `s₂`, updaters of slot `s₂`, are honest at the vote time of slot `s₂ + 1`, before their
    -- ticks to the support cutoff of slot `s₂ + 1`
    (fun u hu => (outside_at_honest_ticks_of_mem_activeThroughoutToTick M F) x R E
      (hHonUpd (s + d) (by omega) (by omega) u (hHs (s + d) (by omega) (by omega) u hu).1)
      (by
        have hR : ((M.voteTime S.C (s + d + 1) : ℕ) : ℝ) + Δ S = ((M.supportCutoff S.C (s + d + 1) : ℕ) : ℝ) := by
          exact_mod_cast (show M.voteTime S.C (s + d + 1) + Δ S = M.supportCutoff S.C (s + d + 1) by omega)
        have hsk := hSkew
        have hB0 := E.behind_nonneg
        linarith))
    (fun v hv => (core_window_of_dutyWindow_reader M F U) x R E hΔs hSkew
      (le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (Nat.le_add_right s d)))
      (hHon (s + d + 1) (by omega) (by omega) v hv))
    (hHs (s + d) (by omega) (by omega))
    (fun u hu => (holder_window_of_updater_reader M F U) x R E hΔs hSkew
      (le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (Nat.le_add_right s d)))
      (hHonUpd (s + d) (by omega) (by omega) u (hHs (s + d) (by omega) (by omega) u hu).1))
    (fun w hw => (hVoters (s + d) (by omega) (by omega) w
      (hHonMono (s + d) (by omega) (by omega) hw)).1)
    (fun w hw => (hStepLast w hw).1) (fun w hw => (hStepLast w hw).2)

/-- **Kit theorem, an honest tick's attestation reaches a validator active from `tq`, under the promises up to `c₁`.** An
attestation that `v`, honest at the time `t' ≤ tsend` of its tick, put on the wire at that tick is
held by `q` before `c₁`, when `q` is active from `tq` through `c₁`, `GST ≤ tsend`,
`tsend + Δ_F ≤ c₁`, and `c₁` is at least one FG delay or one sync delay after both `GST` and `tq`;
when the tick is before `tq`, `v` is also active through the sync delay `Δs_F` after `tq` and still serves the attestation there
(its justified height just before `tq` at most the attestation's height).

Why: when `tq ≤ t'`, synchrony from the send delivers it by `max t' GST + Δ_F`
(`delivered_before_stepBefore_of_honest_send_sync`), to `q`, active since the send. When `t' < tq`,
`v` holds the attestation from its tick on (`tick_holds_sent`), serves it at `tq`, and the sync fact
read at `tq` delivers it before `c₁`. The pool admits a
well-formed attestation, and only grows.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `GST`: the time from
  which the network is synchronous; `tsend`: the bound on the time of the send; `c₁`: the time the
  pool is read before; `tq`: the time from which `q` is active; `q`: the receiver; `E`, `E_F`: the
  delivery promises (`E_F` up to `c₁`); `Sy_F`: the sync fact for attestations up to `c₁`, with the sync delay `Δs_F`; `hWS`: the
  trace is wake-shaped;
- `j`, `t'`: the step and the time of the send; `v`: the sender; `a`: the attestation.

Read at `q`'s own tick: `kQ` is `q`'s tick to the clock value `c₁`, `q` is active
at every step from the real time `tq` up to it, and the case split is on the real time
`x.time j` of the send, the one time the delivery promise speaks of.

Read aloud: an attestation an honest validator sent at its tick is in the pool, before `c₁`, of
every validator active from `tq` to `c₁`, when the sender still serves it at `tq` in case it sent it
earlier. -/
theorem attestation_in_pool_of_tick_send_upTo (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tsend c₁ tq : ℕ) (q : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST release fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks c₁) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs_F : ℕ} (Sy_F : SyncedWithinUpTo A x (servesMin M S.C) fgObject release ΔRedeliver Δs_F GST c₁)
    (hGST : GST ≤ tsend) (ht₁ : tsend + Δ_F S ≤ c₁)
    -- `c₁` is at least one FG delay or one sync delay after `GST` and after `tq`
    (hGSTq : GST + max (Δ_F S) Δs_F ≤ c₁) (htq : tq + max (Δ_F S) Δs_F ≤ c₁)
    (kQ : ℕ) (hkQ : x.lbl kQ = Event.tick q c₁)
    (hwin : ∀ i : ℕ, (tq : ℝ) ≤ x.time i → i ≤ kQ → q ∈ A.active i)
    (j t' : ℕ) (v : V) (a : Attestation V)
    (hl : x.lbl j = Event.tick v t') (ht' : t' ≤ tsend)
    (hsent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j)
    -- when the tick is before `tq`: `v` is active through the sync delay after `tq` (the sync fact's holder
    -- premise,) and serves `a` there
    (hvq : x.time j < tq → v ∈ A.activeThroughout x tq (tq + Δs_F))
    (hselq : x.time j < tq → M.justifiedHeight (x.stateBefore tq v) ≤ a.h) :
    a ∈ (x.st kQ q).attestationsHeld := by
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hhon : v ∉ A.corrupted j := E.not_mem_corrupted_of_tick hl
  have hkeep : x.time (j + 1) = x.time j := R.time_keep j (by rw [hl]; exact nofun)
  obtain ⟨⟨-, hTj⟩, -, hTj1⟩ := (time_of_lbl_tick M) x R E hl
  have hkQt := (E.tick_active kQ q c₁ hkQ).2.1
  have hmx1 := le_max_left (Δ_F S) Δs_F
  have hmx2 := le_max_right (Δ_F S) Δs_F
  have ht'R : (t' : ℝ) ≤ tsend := by exact_mod_cast ht'
  have ht₁R : (tsend : ℝ) + Δ_F S ≤ c₁ := by exact_mod_cast ht₁
  have hGSTR : (GST : ℝ) ≤ tsend := by exact_mod_cast hGST
  have htqF : ((tq : ℕ) : ℝ) + Δ_F S ≤ c₁ := by exact_mod_cast (show tq + Δ_F S ≤ c₁ by omega)
  have hWF := (tick_attestation_well_formed M F) S A x R E j t' v a hl hsent
  -- a delivery of the attestation to `q` before `kQ` puts it in `q`'s pool at `kQ`
  have hpool : ∀ d : ℕ, d < kQ → x.lbl d = Event.deliver q ⟨v, NamedObject.attest a⟩ →
      a ∈ (x.st kQ q).attestationsHeld := by
    intro d hd hld
    obtain ⟨-, hstep⟩ := (deliver_step_state M F) x R E hld
    have hin : a ∈ (x.st (d + 1) q).attestationsHeld := by
      rw [hstep]
      exact F.rcv.receive_attestation_held S.C S.P S.X _ a hWF
    exact (pool_grows_of_le M F) x R E q hd a hin
  by_cases hdel : ∃ d₀ : ℕ, d₀ < kQ ∧ x.lbl d₀ = Event.deliver q ⟨v, NamedObject.attest a⟩
  · obtain ⟨d₀, h1, h2⟩ := hdel
    exact hpool d₀ h1 h2
  by_cases hlate : (tq : ℝ) ≤ x.time j
  · -- the send at a real time from `tq` on: the delivery promise, `q` active from the send by `hwin`
    have hjk : j < kQ := (lt_of_time_lt M) x R (by linarith)
    have hmax : max (x.time (j + 1)) (GST : ℝ) ≤ (tsend : ℝ) + ΔClockBehind :=
      max_le (by linarith) (by linarith)
    obtain ⟨d, -, hdk', hld, -, -⟩ := E_F.delivered j kQ q ⟨v, NamedObject.attest a⟩ c₁
      (max (x.time (j + 1)) (GST : ℝ) + (ΔNet_F : ℝ)) ⟨hsent, hhon⟩
      (show fgObject (NamedObject.attest a) from trivial) hkQ hjk
      (fun i h1 h2 => hwin i (le_trans hlate (htime (show j ≤ i by omega))) h2)
      (GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.2 ⟨by linarith, rfl⟩) (by linarith)
      (fun _ j₀ _ _ _ _ hl₀ _ hj₀k₁ hk₁k _ _ _ => absurd ⟨j₀, by omega, hl₀⟩ hdel)
    exact hpool d hdk' hld
  · -- the send before `tq`: `v` holds `a` from its tick on, serves it at its last step before `tq`, and the sync
    -- fact read at `tq` (its holder premise from `hvq`,) delivers it before `kQ`, or `q` holds it already
    push_neg at hlate
    have h0 : (0 : ℝ) ≤ x.time j := (time_nonneg M) x R j
    have htq1 : 1 ≤ tq := by
      have : (0 : ℝ) < (tq : ℝ) := lt_of_le_of_lt h0 hlate
      exact_mod_cast this
    obtain ⟨hk1, hk2⟩ := (stepBefore_time M) x R E htq1
    have hΔs0 : (0 : ℝ) ≤ Δs_F := Nat.cast_nonneg _
    obtain ⟨hvat, hhold⟩ := holder_row_of_window A x htime tq Δs_F hΔs0 (hvq hlate)
    have hu : v ∈ A.active (x.stepBefore tq) := Activity.mem_activeAtTime.1 hvat _ hk1.le hk2
    obtain ⟨n', sent, hok, hst, hsentL⟩ := R.tick j v t' hl
    have hmem : NamedObject.attest a ∈ sent := by
      rw [hsentL, add_tsub_cancel_left] at hsent
      obtain ⟨m', hm', heq⟩ := Multiset.mem_map.1 hsent
      injection heq with _ hmo
      subst hmo
      exact Multiset.mem_coe.1 hm'
    have hInv := (lem11_node_invariant M F S A x R E j v hhon).1
    have hok' : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.st j v) (t' : Int) := hok
    have hheld : a ∈ (x.st (j + 1) v).attestationsHeld := by
      rw [hst]
      exact (F.tk3.tick_holds_sent S.C S.P S.X (x.st j v) (t' : Int) n' sent hok' hInv).2 a hmem
    have hjq : j < x.stepBefore tq := ((lt_stepBefore_iff M) x R E).2 (by rw [hkeep]; exact hlate)
    have hheldq : a ∈ (x.st (x.stepBefore tq) v).attestationsHeld :=
      (pool_grows_of_le M F) x R E v (by omega) a hheld
    have hdl : max tq GST + Δs_F ≤ c₁ := by
      rcases le_total tq GST with h | h
      · rw [max_eq_right h]; omega
      · rw [max_eq_left h]; omega
    have hkk : x.stepBefore tq ≤ kQ := by
      by_contra hc
      have := htime (show kQ ≤ x.stepBefore tq by omega)
      have hsk := hSkew_F
      linarith
    rcases Sy_F (tq : ℝ) (x.stepBefore tq) v q (NamedObject.attest a) (max tq GST + Δs_F) c₁ kQ hk1 hk2 hu
        ⟨hheldq, hselq hlate⟩ (show fgObject (NamedObject.attest a) from trivial)
        (by rw [Nat.ceil_natCast]; exact fun i h1 h2 => hhold i h1 (by exact_mod_cast h2))
        (by rw [Nat.ceil_natCast]; exact GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.2 ⟨hdl, rfl⟩)
        hkQ hdl
        (fun i h1 h2 => hwin i h1 h2)
        -- the re-delivery premise needs a delivery of the attestation to `q` before `kQ`, which there is not
        (fun _ j₀ _ _ _ hl₀ _ hj₀k₁ hk₁k _ _ _ => absurd ⟨j₀, by omega, hl₀⟩ hdel) with
      hqA | ⟨d, -, -, -, -, hld, hdk, -, -⟩
    · exact (pool_grows_of_le M F) x R E q hkk a hqA.1
    · exact hpool d hdk hld

/-- **Kit theorem, the round's attestations reach the next proposer.** Write `a` for the support
cutoff of slot `s + 1`, and `H`, `T` for the height of `B`'s chain state and the root of its `T_h`.
In an execution where every time is reached, corruption is permanent and attestations are delivered
within `Δ_F` after `GST`: if `GST` is at most `a`, `a + Δ_F` is at most `c₁`, `B` is of slot `s`;
and for every member `v` of `Q`: `v` is awake and honest from the duty window's start of slot
`s + 1` to `a`, every outcome of its tick at `a`, from its state awake for slot `s + 1`, saves `B`
as the confirmation of slot `s` with `B` among its fast blocks, every live lock entry an outcome of
its tick at the vote time of slot `s + 1` leaves, from its state awake for that slot, is compatible
with `B`, its frame before `a` has the root `ρ v`, `B` or an ancestor of `B`, and the
`head_height_floor` `φ v`, at most `H`, it holds `B` before `a`, and its cache `h_j` is less than
`H`, or no lock at `H`, or its lock at `H` is `T`; and `q` is awake and honest from `tq` to `c₁`,
with `tq + Δ_F ≤ c₁` — then `q`'s pool before `c₁` holds an attestation of every member of `Q` at
`H` naming `T`; and when no member's record before `a` holds anything sent at `H`, a target of each.

Why: Lemma 61 at each member; an attestation already sent is traced to the tick that sent it
(`record_content_sent`); with nothing sent at `H`, Lemma 55's corollary. Each reaches `q` by
synchrony or by the catch-up on `q`'s last wake (`delivered_before_stepBefore_of_honest_send`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `r`: the round; `s`: its first slot; `c₁`: the time of the next proposal; `tq`:
  the time from which `q` is awake and honest;
- `Q`: the quorum; `B`: the proposal; `q`: the next proposer; `φ v`, `ρ v`: the
  `head_height_floor` and the root of member `v`'s frame before `a`.

Restated with the delivery premises up to `c₁`: each member's attestation, sent by the support
cutoff of slot `s + 1` and from `tq` on, reaches `q` one delay later, by `c₁`.

Read at the validators' own ticks: each member's update, locks, frame, tree and
record are read in the state its tick to the support cutoff of slot `s + 1` (its locks: to the
vote time of slot `s + 1`) starts from, each member ticks to that cutoff active from the trace's
start or from its own tick to a clock value at most `duty_window_start S.C (s + 1)`, and `q`'s
pool is read in the state its tick `kQ` to the clock value `c₁` starts from, `q` active at every
step from the real time `tq` up to that tick.

Read aloud: every member of `Q` attests for `B`'s height and `T_h` root, and the attestation is in
the next honest proposer's pool before its slot starts, with the delivery premises up to the bound.
-/
theorem round_attestations_in_pool_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST r s c₁ tq : ℕ) (Q : Finset V) (B : Block V) (q : V)
    (φ : V → Height) (ρ : V → Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the two clock bounds together are less than one delay (: the members' lock entries at their ticks,
    -- `update_lock_entries_ancestorEq`)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST release fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks c₁) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S) {Δs_F : ℕ}
    (Sy_F : SyncedWithinUpTo A x (servesMin M S.C) fgObject release ΔRedeliver Δs_F GST c₁)
    (hs : s = r * S.C.R)
    (hGST : GST ≤ M.supportCutoff S.C (s + 1))
    (ht₁ : M.supportCutoff S.C (s + 1) + Δ_F S ≤ c₁)
    (hBslot : B.slot = s)
    (hv : ∀ v ∈ Q, v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (hUpd : ∀ v ∈ Q, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1) →
      M.savedConfirmation n' s = some B ∧ B ∈ M.fastBlocks n')
    (hLocks : ∀ v ∈ Q, ∀ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n'',
        M.is_live (x.tickInput v (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true)
    (hShape : ∀ v ∈ Q, FrameShape M (x.tickInput v (M.supportCutoff S.C (s + 1))) (ρ v) (φ v))
    (hRoot : ∀ v ∈ Q, (ρ v).AncestorEq B)
    (hBin : ∀ v ∈ Q, B ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).tree)
    (hLockBox : ∀ v ∈ Q,
      (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight < (M.chainStateOf S.C B).h ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
        some (M.chainStateOf S.C B).T_h.root)
    (hBHeight : ∀ v ∈ Q, φ v ≤ (M.chainStateOf S.C B).h)
    -- `c₁` is at least one FG delay or one sync delay after `GST` and after `tq`
    (hGSTq : GST + max (Δ_F S) Δs_F ≤ c₁)
    (htq : tq + max (Δ_F S) Δs_F ≤ c₁)
    (kQ : ℕ) (hkQ : x.lbl kQ = Event.tick q c₁)
    (hwin : ∀ i : ℕ, (tq : ℝ) ≤ x.time i → i ≤ kQ → q ∈ A.active i)
    -- every member is active through the sync delay after `tq` (the sync fact's holder premise,;
    --, and its justified height just before `tq` is at most `H`
    (hvq : ∀ v ∈ Q, v ∈ A.activeThroughout x tq (tq + Δs_F))
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore tq v) ≤ (M.chainStateOf S.C B).h) :
    (∀ u ∈ Q, ∃ a ∈ (x.st kQ q).attestationsHeld,
      a.val_index = u ∧ a.h = (M.chainStateOf S.C B).h ∧ a.T = (M.chainStateOf S.C B).T_h.root) ∧
    ((∀ u ∈ Q, ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      ∀ u ∈ Q, ∃ a ∈ (x.st kQ q).attestationsHeld,
        a.val_index = u ∧ a.h = (M.chainStateOf S.C B).h ∧
        a.T = (M.chainStateOf S.C B).T_h.root ∧ a.τ = false) := by
  -- an attestation a member sent at a tick to a clock value at most the support cutoff of slot `s + 1`, at `H`, is
  -- in `q`'s pool at its tick `kQ` (the holder row `hvq`,)
  have hDeliver : ∀ (j t' : ℕ) (v : V) (a : Attestation V), v ∈ Q → a.h = (M.chainStateOf S.C B).h →
      x.lbl j = Event.tick v t' → t' ≤ M.supportCutoff S.C (s + 1) →
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j →
      a ∈ (x.st kQ q).attestationsHeld := by
    intro j t' v a hvQ hah hl ht' hsent
    exact (attestation_in_pool_of_tick_send_upTo M F) S A x R GST (M.supportCutoff S.C (s + 1)) c₁ tq q
      E E_F hNet_F hSkew_F Sy_F hGST ht₁ hGSTq htq kQ hkQ hwin j t' v a hl ht' hsent
      (fun _ => hvq v hvQ) (fun _ => by rw [hah]; exact hselq v hvQ)
  -- an outcome of each member's tick to the support cutoff of slot `s + 1`, from its state awake for that slot (the
  -- member's reader from `duty_window_start S.C (s + 1)`)
  have hDuty : duty_window_start S.C (s + 1) < ((M.supportCutoff S.C (s + 1) : ℕ) : Int) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout F.sched U) S (s + 1)
  have hOut : ∀ u ∈ Q, ∃ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput u (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) ∧
      AwakeFor M S.C (x.tickInput u (M.supportCutoff S.C (s + 1))) (s + 1) := by
    intro u hu
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 (hv u hu)
    obtain ⟨n'', sent, hrun, hAw, -⟩ := (update_state_of_tick M F U) S A x R s u E hk
      ((tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E (hv u hu) hDuty)
    exact ⟨n'', sent, hrun, hAw⟩
  refine ⟨fun u hu => ?_, fun hFresh u hu => ?_⟩
  · obtain ⟨n', sent, hrun, hA⟩ := hOut u hu
    obtain ⟨hS, hF⟩ := hUpd u hu n' sent hrun hA
    have hLk := (update_lock_entries_ancestorEq M F U) S A x R s B u E hSkew (hv u hu) n' sent
      hrun hA hS hBslot (hLocks u hu)
    rcases (lem61_honest_validator_attests_frame M F U) S A x R r s B u (ρ u) (φ u) E hs (hv u hu)
        n' sent hrun hA hS hF hLk (hShape u hu) (hRoot u hu) (hBHeight u hu) (hBin u hu) (hLockBox u hu)
      with ⟨i, a, hl, hsent, hav, hah, haT⟩ | ⟨b, hb, hbh, hbT⟩
    · exact ⟨a, hDeliver i _ u a hu hah hl le_rfl hsent, hav, hah, haT⟩
    · obtain ⟨j, t', a, hl, ht', -, hsent, hav, hac, -⟩ := (record_content_sent M F) S A x R _ u b E hb
      have hah' : a.h = (M.chainStateOf S.C B).h := by rw [← hbh, ← hac]; rfl
      refine ⟨a, hDeliver j t' u a hu hah' hl ht'.le hsent, hav, hah', ?_⟩
      rw [← hbT, ← hac]
      rfl
  · obtain ⟨n', sent, hrun, hA⟩ := hOut u hu
    obtain ⟨hS, hF⟩ := hUpd u hu n' sent hrun hA
    have hLk := (update_lock_entries_ancestorEq M F U) S A x R s B u E hSkew (hv u hu) n' sent
      hrun hA hS hBslot (hLocks u hu)
    -- Lemma 55's viable-tree and record hypotheses at `u`'s tick input (as `lem61_honest_validator_attests_frame`)
    have hViable : B ∈ M.viable_tree (M.fg_to_ac (x.tickInput u (M.supportCutoff S.C (s + 1))))
        (M.fg_to_ac (x.tickInput u (M.supportCutoff S.C (s + 1)))).tree := by
      refine (GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_of_frameShape_of_core M F) S.C S.P S.X _
        (lem11_node_invariantCore_of_run M F S x R (x.tickStep u (M.supportCutoff S.C (s + 1))) u).1 (ρ u) (φ u) B
        (hShape u hu) ?_ (hRoot u hu) (hBin u hu) (hBHeight u hu)
      rw [← (hShape u hu).1]
      exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E _ u
    have hRecord : (x.tickInput u (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
        ((x.tickInput u (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
            some (M.chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
            b.h = (M.chainStateOf S.C B).h → b.T = (M.chainStateOf S.C B).T_h.root) := by
      rcases hLockBox u hu with hlt | hnone | hlock
      · exact Or.inl ((GoldilocksCorrectness.Record.Statements.Executions.lock_none_of_h_j_lt_of_exec M F) S A x R E _ u _ hlt)
      · exact Or.inl hnone
      · exact Or.inr ⟨hlock, (GoldilocksCorrectness.Record.Statements.Executions.lockNamesSent_of_exec M F) S A x R E _ u _ _
          hlock⟩
    obtain ⟨i, a, hl, hsent, hav, hah, haT, hτ⟩ := (lem55_target_of_fresh_height M F U) S A x R r s B u E hs
      (hv u hu) n' sent hrun hA hS hF hLk hViable hRecord (hFresh u hu)
    exact ⟨a, hDeliver i _ u a hu hah hl le_rfl hsent, hav, hah, haT, hτ⟩

/-- **Kit theorem, the next honest proposal extends the round's proposal.** Write `t₁` for the
start of slot `s₂ + 2`. In an execution with the eight execution assumptions: if `GST` is at most
the vote time of slot `s₂ + 1`; `HonestChainExtends M S Sched x (Hon M) B s₂` holds; every
slot-`(s₂ + 1)` vote of a member of `Hon` is for a block it holds on `B`'s chain; `q` is a member,
awake and honest from the duty window's start of slot `s₂ + 1` to `t₁`; every member of `Hs` is a
member of `Hon` and of the slot-`(s₂ + 1)` committee voting at that slot; every member is honest at
`t₁`; the slot-`(s₂ + 1)` voters `q`'s proposal counts are fewer than twice `Hs`; `q`'s fork-choice
root before `t₁` is compatible with `B` and, when it is `B` or an ancestor of `B`, a block of `q`'s
frame tree that is `B` or a descendant of `B` is a viable head; and `q` put `B'` on the wire at its
tick at `t₁` — then `B` is `B'`'s parent or an ancestor of it.

Why: `q`'s anchor is compatible with `B` (Lemma 6: its live locks by the invariant, its root by
hypothesis) and is `B'`'s parent or an ancestor of it. When the anchor is an ancestor of `B`, the
slot-`(s₂ + 1)` majority's votes, all on `B`'s chain, take `q`'s walk past `B`
(`proposal_parent_extends_majority_block`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `s₂`: the slot of the invariant; `Hon`: the members; `Hs`: the honest voters of
  slot `s₂ + 1`; `B`: the round's proposal; `B'`: `q`'s proposal; `q`: its proposer.

Roots name blocks until `M.supportCutoff S.C (s₂ + 1)`: `proposal_parent_extends_majority_block`,
which the proof calls at slot `s₂ + 1`, takes blocks as held up to the support cutoff of slot
`s₂ + 1`.

Restated with the delivery premises up to `M.supportCutoff S.C (s₂ + 1)`:
`proposal_parent_extends_majority_block_upTo` at slot `s₂ + 1` reads deliveries due by then.

Read aloud: the next honest proposal's parent is `B` or a descendant of `B`, with the delivery
premises up to the bound. -/
theorem round_proposal_extends_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₂ : ℕ) (Hon Hs : Finset V) (B B' : Block V)
      (q : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s₂ + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s₂ + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep q (M.supportCutoff S.C (s₂ + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s₂ + 1))
    (hInv : HonestChainExtends M S A x Hon B s₂)
    (hVotes : ∀ u ∈ Hon, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s₂ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s₂ + 1))).tree,
        vote = GoldfishVote.mk u (s₂ + 1) H_u.root ∧ B.AncestorEq H_u)
    (hq : q ∈ Hon)
    (hqUpd : q ∈ updaterAt M S A x s₂)
    (hHs : ∀ u ∈ Hs, u ∈ Hon ∧ u ∈ S.P.committee (s₂ + 1) ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s₂ + 1 ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s₂ + 1)) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C (s₂ + 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s₂ + 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHonest : ∀ u ∈ Hs, u ∉ A.corrupted (x.tickStep q (M.slotStart S.C (s₂ + 2))))
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C (s₂ + 2)))
        (s₂ + 1) votes support_votes →
      M.voters_count votes < 2 * Hs.card)
    (hFrameQ :
        (M.fg_to_ac (x.tickInput q (M.slotStart S.C (s₂ + 2)))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput q (M.slotStart S.C (s₂ + 2)))).fc_root.AncestorEq B →
        ∃ W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C (s₂ + 2)))).tree,
          W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C (s₂ + 2)))).viable_heads ∧
            B.AncestorEq W))
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C (s₂ + 2)) ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B'.parent := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hss₂ : M.slotStart S.C (s₂ + 2) = M.slotStart S.C (s₂ + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s₂ + 1), show s₂ + 2 = s₂ + 1 + 1 from rfl, Nat.mul_add,
      Nat.mul_one]
  have hv₁ : M.voteTime S.C (s₂ + 1) = M.slotStart S.C (s₂ + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₂ + 1)
  have hv₂ : M.voteTime S.C (s₂ + 2) = M.slotStart S.C (s₂ + 2) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₂ + 2)
  have hc₁ : M.supportCutoff S.C (s₂ + 1) = M.voteTime S.C (s₂ + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₂ + 1)
  obtain ⟨i, hl, hsent⟩ := hPropose'
  have hAnc := (get_anchor_ancestorEq_proposal_parent M F) S A x R E (s₂ + 2) i B' q hl hsent
  -- `q`'s tick to the vote time of slot `s₂ + 1`, inside its update reader
  have hqR := (vote_reader_from_updater_under_skew M F U) S A x R s₂ q E hSkew hqUpd
  -- `q`'s anchor at its tick input is compatible with `B`
  have hAC : (M.get_anchor (x.tickInput q (M.slotStart S.C (s₂ + 2)))
      ((M.slotStart S.C (s₂ + 2) : ℕ) : Int)).compatible B = true := by
    refine (GoldilocksCorrectness.Record.Statements.Routines.lem6_get_anchor_compatible M F) _ _ B
      (fun e he hlive => ?_) hFrameQ.1
    refine (live_locks_compatible_of_honestChainExtends_tick M F U) S A x R Hon B s₂ (M.slotStart S.C (s₂ + 2))
      q E hInv hq hqR (by omega) (by omega) e he ?_
    simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hlive
    exact hlive.1
  rcases (compatible_iff _ _).1 hAC with hAB | hBA
  · -- the anchor is an ancestor of `B`: the majority's walk passes `B`
    have hchoose : ∀ u : V, ∃ Hu : Block V, u ∈ Hs →
        (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s₂ + 1)) ∧
          (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s₂ + 1) Hu.root)⟩ :
            SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
        Hu ∈ (x.tickInput u (M.voteTime S.C (s₂ + 1))).tree ∧ B.AncestorEq Hu := by
      intro u
      by_cases hu : u ∈ Hs
      · obtain ⟨huH, -, vote, -, -, i', hl', hs'⟩ := hHs u hu
        obtain ⟨Hu, hHuT, hvote, hBH⟩ := hVotes u huH vote ⟨i', hl', hs'⟩
        rw [hvote] at hs'
        exact ⟨Hu, fun _ => ⟨⟨i', hl', hs'⟩, hHuT, hBH⟩⟩
      · exact ⟨B, fun h => absurd h hu⟩
    choose Hf hHf using hchoose
    have hρB : (M.fg_to_ac (x.tickInput q (M.slotStart S.C (s₂ + 2)))).fc_root.AncestorEq B :=
      ancestorEq_trans ((GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_get_anchor M F) _ _) hAB
    exact ((proposal_parent_extends_majority_block_upTo M F U) S A x R GST (s₂ + 1) i Hs Hf B B' q E hNet hSkew
      hRedeliver Sy hΔs hRoots hParent hOwner hGST
      (fun u hu => ⟨(hHs u hu).2.1, hHonest u hu, (hHf u hu).1, (hHf u hu).2.1, (hHf u hu).2.2⟩)
      hVotersQ hHold ((updater_reader_gives_own_core_window M F U) x R E hΔs hSkew hqUpd)
      hl hsent (hFrameQ.2 hρB) hAB).1
  · exact ancestorEq_trans hBA hAnc

open Classical in
/-- Lemma 80 over per-slot member sets, with the frames read at the first slot's three reading
points, the step conditions per slot after the action time, and `q`'s fork choice before its
proposal. The proof; the audited statement is in `Statements/Executions/RoundStatements.lean`.

Roots name blocks until `M.supportCutoff S.C (s'' - 1)`: `round_proposal_extends`, which the proof
calls at the slot `s'' - 2`, takes blocks as held up to the support cutoff of slot `s'' - 1`;
the base and the invariant through the round read earlier.

Restated with the delivery premises up to `M.supportCutoff S.C (s'' - 1)`, the attestations' up to
`M.slotStart S.C s''`: the blocks and Goldfish votes the proof reads are due by the support cutoff
of slot `s'' − 1` (`round_proposal_extends_upTo`), the attestations by the start of slot `s''`
(`round_attestations_in_pool_upTo`).

Beside the hypotheses of `lem80wq_round_height_advances_steps`, two the attestations' sync route reads: `hGSTF`, the attestations' sync delay has elapsed after `GST` by the start of slot
`s''`; and `hselq`, no member of `Q` has justified past the height of `B`'s chain state before the later of the
duty window's start of slot `s` and `GST`.

The proposer's window `hp` starts `max (Δ S) Δs` before the support cutoff of slot `s − 1` and ends at the start
of slot `s`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the round theorem asks of each slot's committee majority honesty through its own slot's
update only, reads the frames of the first slot at its three reading points, the chain's step
conditions after the action time, and the next proposer's fork choice at its proposal; then the next
honest proposal is on the round's proposal's chain with the height risen or the progress quorum on
chain, with the delivery premises up to the bound. -/
theorem lem80wq_round_height_advances_steps_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST r s s'' : ℕ) (Hon : ℕ → Finset V) (Q : Finset V) (Hs : ℕ → Finset V)
    (H : V → Block V) (X B B' : Block V) (p q : V) (φ : Height) (φw φv : V → Height)
    (ρp : Block V) (ρw ρv : V → Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s'' - 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s'' - 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    -- attestations are delivered within `Δ_F S` after `GST`
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.slotStart S.C s'')) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S) {Δs_F : ℕ}
    (Sy_F : SyncedWithinUpTo A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST (M.slotStart S.C s''))
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s)
      (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    -- the attestations' sync delay has elapsed after `GST` by the start of slot `s''`
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- for every slot `s'` before the last: the members of slot `s'` tick to its vote time, active up to that tick from
    -- the trace's start or from their own tick to a clock value at most the duty window's start of slot `s'`
    --, each runs the update of slot `s'`, and none is in the adversary set at a step where a
    -- validator outside it ticks to the support cutoff of slot `s' + 1`
    (hHon : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s',
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C s') (M.voteTime S.C s'))
    (hHonUpd : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s', v ∈ updaterAt M S A x s')
    (hHonTick : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ u ∈ Hon s', u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- the members of the last slot `s'' − 1` tick to the start of slot `s''`, active up to that tick from the trace's start
    -- or from their own tick to a clock value at most the duty window's start of that slot
    (hHonLast : ∀ v ∈ Hon (s'' - 1),
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s'' - 1)) (M.slotStart S.C s''))
    -- the voters of the last slot `s'' − 1` are outside the adversary set at `q`'s tick to the start of slot `s''`,
    -- where `q`'s proposal counts their votes
    (hHonestQ : ∀ u ∈ Hs (s'' - 1), u ∉ A.corrupted (x.tickStep q (M.slotStart S.C s'')))
    -- the members of the round's first slot `s` are active in every configuration in force at a real time of the sync
    -- delay after `M.supportCutoff S.C (s + 1) - max (Δ S) Δs`, where Lemma 42 reads the sync fact for their blocks
    --
    (hHold42 : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members are active through the sync delay after `M.viewFreeze S.C s - max (Δ S) Δs` (Lemma 42's holder
    -- row `hv₀`;)
    (hHoldV : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members of the round's first slot are active through the attestations' sync delay after the later of
    -- the duty window's start of slot `s` and `GST`, where the attestations' sync fact is read
    --
    (hHoldF : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    -- the proposer is active from the recovery delay before the support cutoff of slot `s − 1`
    -- through the start of slot `s`
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`; the proposer
    -- ticks to the start of slot `s`, active up to that tick from the trace's start or from its own tick to a clock value
    -- at most `tStart`, and is active through the sync delay after `M.slotStart S.C s - max (Δ S) Δs` (: the
    -- amended rows of the `_frame` theorems, under)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hp : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon s, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u))
    -- the previous slot's voters are active through the sync delay after Lemma 12's read time of slot `s − 1`
    -- ( under)
    (hHold : ∀ u ∈ Hs (s - 1), u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- at every member of `Hon s`, the voters its vote of slot `s` counts are fewer than twice
    -- `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX :
        (M.get_anchor (x.tickInput p (M.slotStart S.C s))
            ((M.slotStart S.C s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon s, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C s)).tree, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root ≠ B.root)
    -- the honest voters of slot `s'` are members of `Hon s'` and of the slot's committee
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- the counts of slot `s'`, read at the members of `Hon s'`: the voters counted by a vote of
    -- slot `s' + 1` and the slot-`s'` voters of the pool at its tick to the support cutoff of slot
    -- `s' + 1` are fewer than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C s''))
        (s'' - 1) votes support_votes →
      M.voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- the frames at the three reading points of slot `s`: `p`'s before the start of slot `s`,
    -- each member's before the vote time of slot `s` and before the action time `a`, with their
    -- roots and `head_height_floor` values
    (hShapeP : FrameShape M (x.tickInput p (M.slotStart S.C s)) ρp φ)
    (hShapeW : ∀ w ∈ Hon s, FrameShape M (x.tickInput w (M.voteTime S.C s)) (ρw w) (φw w))
    (hShapeV : ∀ v ∈ Hon s,
      FrameShape M (x.tickInput v (M.supportCutoff S.C (s + 1))) (ρv v) (φv v))
    -- each member's `head_height_floor` before the vote time is at least the proposer's and at
    -- most the chain-state height of `B`'s parent; before `a`, at most that of `B`
    (hFloorW : ∀ w ∈ Hon s, φ ≤ φw w ∧ φw w ≤ (M.chainStateOf S.C B.parent).h)
    (hFloorV : ∀ v ∈ Hon s, φv v ≤ (M.chainStateOf S.C B).h)
    -- the roots: before the vote time on `B`'s parent's chain, before `a` on `B`'s chain
    (hRootW : ∀ w ∈ Hon s, (ρw w).AncestorEq B.parent)
    (hRootAr : ∀ v ∈ Hon s, (ρv v).AncestorEq B)
    -- some block of `p`'s tree, on `X`'s and `ρp`'s chains, reaches `φ`
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ ρp.AncestorEq W ∧ φ ≤ (M.chainStateOf S.C W).h)
    -- after the action time, at the members of the next slot: `StepFrameAt` relative to `B` for
    -- every slot `s'` with `s' + 3 ≤ s''`; for the last slot `s'' − 1`, the voter's fork choice
    -- before its vote time (the first two conjuncts of `StepFrameAt S Sched x B (s'' − 2) w`)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt M S A x B s' w)
    (hStepLast : ∀ w ∈ Hon (s'' - 1),
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.AncestorEq B →
        ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s'' - 1)))
          (S.C.t_ ((s'' - 1) - 1) + 3 * S.C.Δ) (s'' - 1) W ∧ W ∈
            (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).viable_heads ∧
            B.AncestorEq W))
    -- the quorum attests at `a`, inside slot `s`'s active window
    (hQ : Q ⊆ Hon s) (hQuorum : quorum V ≤ Q.card)
    -- the record of every member of `Q` before `a`: the cache `h_j` is less than `H`, or no lock
    -- at `H`, or the lock at `H` is `T`
    (hLockBox : ∀ v ∈ Q,
      (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight < (M.chainStateOf S.C B).h ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
        some (M.chainStateOf S.C B).T_h.root)
    -- no member of `Q` has justified past the height of `B`'s chain state before the later of the
    -- duty window's start of slot `s` and `GST`
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C s) GST) v) ≤
      (M.chainStateOf S.C B).h)
    -- the next proposer is a member of the last slot's set
    (hq : q ∈ Hon (s'' - 1))
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    -- `q`'s fork-choice root before the start of slot `s''` is compatible with `B`, and when it
    -- is `B` or an ancestor of `B`, a block of `q`'s frame tree that is `B` or a descendant of `B`
    -- is a viable head
    (hFrameQ : (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.AncestorEq B →
        ∃ W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).tree,
          W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).viable_heads ∧ B.AncestorEq W))
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) := by
  -- the slots: `s'' = s₂ + 2`, with `s ≤ s₂`
  have hR := S.C.R_ge_two
  have hs2 := (GoldilocksCorrectness.Record.Proofs.Routines.slot_add_two_le_of_delivery M.toSlotLayout F.sched) S hs''
  obtain ⟨s₂, rfl⟩ : ∃ s₂, s'' = s₂ + 2 := ⟨s'' - 2, by omega⟩
  rw [show s₂ + 2 - 1 = s₂ + 1 by omega] at hVotersQ hStepLast hq hRoots hHonLast hHonestQ E Sy
  -- the times
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hss : ∀ k, M.slotStart S.C (k + 1) = M.slotStart S.C k + 4 * Δ S := fun k => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hsE : ∀ k, M.slotStart S.C k = 4 * Δ S * k :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S
  have hv : ∀ k, M.voteTime S.C k = M.slotStart S.C k + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
  have hc : ∀ k, M.supportCutoff S.C k = M.voteTime S.C k + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
  have hsm : s - 1 + 1 = s := by omega
  have hk8 := (slot_times M F U S s).2.2.2.2.2.1
  have hkm := slot_bound_nat_of_hΔs M F S hA0 hB0 hΔs
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  -- the bound `hΔs` with the read time `max (2 * Δ S) Δs` of Lemma 12
  have hm2R : ((max (2 * Δ S) Δs : ℕ) : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k := by
    rcases le_total (2 * Δ S) Δs with h2 | h2
    · rw [max_eq_right h2]
      have : max ((Δ S : ℕ) : ℝ) (Δs : ℝ) = Δs := max_eq_right (by exact_mod_cast (show Δ S ≤ Δs by omega))
      have h' := hΔs
      push_cast at h' ⊢
      rw [this] at h'
      exact h'
    · rw [max_eq_left h2]
      push_cast
      linarith
  have hm2 : max (2 * Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have h' : ((max (2 * Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by push_cast; push_cast at hm2R; linarith
    exact_mod_cast h'
  have hm2s := le_max_right (2 * Δ S) Δs
  have hm2l := le_max_left (2 * Δ S) Δs
  have hvs0 := hv (s - 1)
  have hss0 : M.slotStart S.C s = M.slotStart S.C (s - 1) + 4 * Δ S := by rw [← hss (s - 1), hsm]
  have hvs := hv s
  have hss1 := hss s
  have hvs1 := hv (s + 1)
  have hcs1 := hc (s + 1)
  have hm2' := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_of_le M.toSlotLayout F.sched) S (show s + 2 ≤ s₂ + 2 by omega)
  have ha : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C (s₂ + 2) := hs''
  have hcut₁ : M.supportCutoff S.C (s + 1) ≤ M.supportCutoff S.C (s₂ + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  have hcut₂ : M.supportCutoff S.C s₂ ≤ M.supportCutoff S.C (s₂ + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  -- `B` is of slot `s`
  have hPropose₀ : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s - 1 + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i := by
    rw [hsm]
    exact hPropose
  obtain ⟨i₀, hl₀, hsent₀⟩ := hPropose₀
  have hBslot : B.slot = s := by
    rw [← hsm]
    exact ((proposal_parent_walk_end M F U) S A x R E (s - 1) i₀ B p hl₀ hsent₀).1
  -- step 1: the base, at the first slot's set, with the reader start `max tStart (duty_window_start S.C s)`: the
  -- members' readers open at the duty window's start of slot `s`, the proposer's at `tStart`
  have hdwle : duty_window_start S.C s ≤ max tStart (duty_window_start S.C s) := le_max_right _ _
  have htStart' : ((max tStart (duty_window_start S.C s) : ℤ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) := by
    rcases le_total tStart (duty_window_start S.C s) with h | h
    · -- the duty window's start `st(s) + Δ − 4Δk` is more than both clock bounds before Lemma 12's read time of
      -- slot `s − 1`, truncated at `0` or not
      rw [max_eq_right h, duty_window_start_real S s]
      have i3A := E.ahead_nonneg
      have i3B := E.behind_nonneg
      have i3D : (0 : ℝ) ≤ Δ S := by positivity
      have i3k8 : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast (slot_times M F U S s).2.2.2.2.2.1
      have i3sE := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S
      have i3vT := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
      have i3c := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
      have i3s : (s - 1 : ℕ) + 1 = s := by omega
      have i3ss : M.slotStart S.C (s - 1) + 4 * Δ S = M.slotStart S.C s := by
        rw [i3sE, i3sE, ← i3s, Nat.mul_add, Nat.mul_one, i3s]
      have i3cs : M.supportCutoff S.C (s - 1) + 2 * Δ S = M.slotStart S.C s := by
        have := i3c (s - 1); have := i3vT (s - 1); omega
      have i3cR : ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) + 2 * Δ S = 4 * (Δ S : ℝ) * (s : ℝ) := by
        have h' : ((M.supportCutoff S.C (s - 1) + 2 * Δ S : ℕ) : ℝ) = ((M.slotStart S.C s : ℕ) : ℝ) := by
          rw [i3cs]
        rw [i3sE s] at h'; push_cast at h'; linarith
      have i3mx : (Δs : ℝ) ≤ max (Δ S : ℝ) (Δs : ℝ) := le_max_right _ _
      have i3m : ((max (2 * Δ S) Δs : ℕ) : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k := by
        rcases le_total (2 * Δ S) Δs with h2 | h2
        · rw [max_eq_right h2]; linarith
        · rw [max_eq_left h2]; push_cast; linarith
      rcases le_total (max (2 * Δ S) Δs) (M.supportCutoff S.C (s - 1)) with hle | hle
      · rw [Nat.cast_sub hle]; linarith
      · rw [Nat.sub_eq_zero_of_le hle]
        have hleR : ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) ≤ ((max (2 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hle
        push_cast
        linarith
    · rw [max_eq_left h]
      exact htStart
  obtain ⟨hHeld, hBase, hUpd⟩ := (round_base_steps_upTo M F U) S A x R GST s (Hon s) (Hs s) (Hs (s - 1)) H X
    B p φ φw ρp ρw (E.mono hcut₁) hNet hSkew hRedeliver (Sy.mono hcut₁) hΔs
    (fun k u c hl hcl => hRoots k u c hl (le_trans hcl hcut₁)) hParent hOwner hs1
    hGST (hHonUpd s le_rfl (by omega)) (hHonTick s le_rfl (by omega)) (max tStart (duty_window_start S.C s)) htStart'
    (Activity.mem_activeThroughoutToTick_of_le (le_max_left tStart (duty_window_start S.C s)) hp) hHoldP
    (fun w hw => Activity.mem_activeThroughoutToTick_of_le hdwle (hHon s le_rfl (by omega) w hw)) hPropose
    hHsPrev hHold hVotersPrev hApX hLocksW hOnly hRootNew (hHs s le_rfl (by omega))
    (fun v hv' => (hVoters s le_rfl (by omega) v hv').2) hHalf hShapeP hShapeW hFloorW
    hRootW (fun v hv => ancestorEq_trans (by rw [← (hShapeV v hv).1]; exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E _ v) (hRootAr v hv))
    hHeadP
  -- step 2: the invariant through the round, from one slot's set to the next; the members of slot `s₂ + 1` read to
  -- their tick to its vote time inside their update reader of slot `s₂`
  obtain ⟨hInv, hVotes⟩ := (round_honestChainExtends_steps_upTo M F U) S A x R GST s s₂ Hon Hs B (E.mono hcut₂) hNet hSkew hRedeliver (Sy.mono hcut₂) hΔs
    (fun k u c hl hcl => hRoots k u c hl (le_trans hcl hcut₂)) hParent hOwner
    (le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.sub_le s 1)))
    (by omega) hHonMono
    (by
      intro s' h1 h2 v hv'
      by_cases hs' : s' + 1 < s₂ + 2
      · exact hHon s' h1 hs' v hv'
      · have he : s' = s₂ + 1 := by omega
        subst he
        have hU := hHonUpd s₂ (by omega) (by omega) v (hHonMono s₂ (by omega) (by omega) hv')
        have hvt := hv (s₂ + 1)
        have hct := hc (s₂ + 1)
        have hdr := duty_window_start_real S (s₂ + 1)
        have hsR : ((M.slotStart S.C (s₂ + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * ((s₂ + 1 : ℕ) : ℝ) := by
          exact_mod_cast hsE (s₂ + 1)
        have hvR : ((M.voteTime S.C (s₂ + 1) : ℕ) : ℝ) = (M.slotStart S.C (s₂ + 1) : ℝ) + Δ S := by exact_mod_cast hvt
        have hcR : ((M.supportCutoff S.C (s₂ + 1) : ℕ) : ℝ) = (M.voteTime S.C (s₂ + 1) : ℝ) + Δ S := by exact_mod_cast hct
        push_cast at hsR hdr
        refine (mem_activeThroughoutToTick_of_le_end_int M x) R E (by omega) ?_ ?_ hU
        · linarith
        · linarith)
    (fun s' h1 h2 => hHonUpd s' h1 h2) (fun s' h1 h2 => hHonTick s' h1 h2) hHs
    hVoters hStep hStepLast hBase
  -- step 3: the attestations in `q`'s pool at its tick `kQ` to the start of slot `s''`, read from
  -- `tq := max (M.dutyWindowStart S.C s) GST`
  have hmxF1 := le_max_left (Δ_F S) Δs_F
  have hmxF2 := le_max_right (Δ_F S) Δs_F
  have hmxΔ := le_max_left (Δ S) Δs
  have hcm1 := hc (s - 1)
  have hvm1 := hv (s - 1)
  have hdws := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S s
  have hssE := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hΔsF : Δs_F ≤ Δ_F S ∨ Δs_F + 3 * Δ S ≤ 4 * Δ S * S.C.k := by
    rcases hΔs_F with h | h
    · left
      exact_mod_cast (show (Δs_F : ℝ) ≤ Δ_F S by linarith)
    · right
      exact_mod_cast (show ((Δs_F + 3 * Δ S : ℕ) : ℝ) ≤ ((4 * Δ S * S.C.k : ℕ) : ℝ) by push_cast; linarith)
  have htqF : max (M.dutyWindowStart S.C s) GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C (s₂ + 2) := by
    rcases hdws with h | ⟨h, -⟩
    · have := le_max_left (M.dutyWindowStart S.C s) GST
      have := le_max_right (M.dutyWindowStart S.C s) GST
      rcases max_cases (M.dutyWindowStart S.C s) GST with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      rcases max_cases (Δ_F S) Δs_F with ⟨h2, -⟩ | ⟨h2, -⟩ <;> rw [h1, h2] <;> omega
    · rw [h, Nat.zero_max]
      exact hGSTF
  -- `q` ticks to the start of slot `s''` (its reader `hHonLast`)
  obtain ⟨kQ0, hkQ0, -⟩ := Activity.mem_activeThroughoutToTick.1 (hHonLast q hq)
  have hkQ : x.lbl (x.tickStep q (M.slotStart S.C (s₂ + 2))) = Event.tick q (M.slotStart S.C (s₂ + 2)) := by
    rw [(tickStep_eq_of_lbl M) x E hkQ0]
    exact hkQ0
  -- each member of `Q` ticks to the vote time of slot `s` before its tick to the support cutoff of slot `s + 1`,
  -- and keeps `B`
  have hBin : ∀ v ∈ Q, B ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).tree := by
    intro v hvQ
    obtain ⟨k1, hk1, -⟩ := Activity.mem_activeThroughoutToTick.1 (hHon s le_rfl (by omega) v (hQ hvQ))
    obtain ⟨k2, hk2, -⟩ := Activity.mem_activeThroughoutToTick.1 (hHonUpd s le_rfl (by omega) v (hQ hvQ))
    have h12 := (tick_lt_of_clock_lt M) x E hk1 hk2 (by omega)
    have hB1 := hHeld v (hQ hvQ)
    unfold Trace.tickInput at hB1 ⊢
    rw [(tickStep_eq_of_lbl M) x E hk1] at hB1
    rw [(tickStep_eq_of_lbl M) x E hk2]
    exact ((grows_of_le M F) x R E v h12.le).1 hB1
  obtain ⟨hPool, hPoolT⟩ := (round_attestations_in_pool_upTo M F U) S A x R GST r s (M.slotStart S.C (s₂ + 2))
    (max (M.dutyWindowStart S.C s) GST) Q B q φv ρv E hSkew E_F hNet_F hSkew_F Sy_F hs
    (by omega) ha hBslot
    (fun v hv' => hHonUpd s le_rfl (by omega) v (hQ hv'))
    (fun v hv' => hUpd v (hQ hv')) (fun v hv' => hBase.2.1 v (hQ hv'))
    (fun v hv' => hShapeV v (hQ hv')) (fun v hv' => hRootAr v (hQ hv'))
    hBin hLockBox
    (fun v hv' => hFloorV v (hQ hv')) hGSTF htqF
    (x.tickStep q (M.slotStart S.C (s₂ + 2))) hkQ hqWin
    (fun v hv' => hHoldF v (hQ hv'))
    hselq
  -- step 4: `q`'s proposal is on `B`'s chain
  have hss₂ : M.slotStart S.C (s₂ + 2) = M.slotStart S.C (s₂ + 1) + 4 * Δ S := hss (s₂ + 1)
  have hqUpd := hHonUpd s₂ (by omega) (by omega) q (hHonMono s₂ (by omega) (by omega) hq)
  obtain ⟨kc, hkc, -⟩ := Activity.mem_activeThroughoutToTick.1 hqUpd
  have hRootsQ : RootsNameBlocksUntil M A x (x.time (x.tickStep q (M.supportCutoff S.C (s₂ + 1)))) := by
    rw [(tickStep_eq_of_lbl M) x E hkc]
    exact hRoots kc q _ hkc le_rfl
  -- the voters of slot `s₂ + 1` are active through the sync delay after Lemma 12's read time of slot `s₂ + 1`,
  -- inside their reader to the start of slot `s''`
  have hHoldQ : ∀ u ∈ Hs (s₂ + 1), u ∈ A.activeThroughout x
      ((M.supportCutoff S.C (s₂ + 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s₂ + 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) := by
    intro u hu
    have huH := ((hHs (s₂ + 1) (by omega) (by omega)) u hu).1
    have hct := hc (s₂ + 1)
    have hvt := hv (s₂ + 1)
    have hst := hss (s₂ + 1)
    have hsR : ((M.slotStart S.C (s₂ + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * ((s₂ + 1 : ℕ) : ℝ) := by
      exact_mod_cast hsE (s₂ + 1)
    have hdr := duty_window_start_real S (s₂ + 1)
    have hle : max (2 * Δ S) Δs ≤ M.supportCutoff S.C (s₂ + 1) := by
      have := le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show s - 1 ≤ s₂ + 1 by omega))
      have := le_max_right (Δ S) Δs
      rcases le_total (2 * Δ S) Δs with h2 | h2
      · rw [max_eq_right h2]; omega
      · rw [max_eq_left h2]; omega
    have hcR : ((M.supportCutoff S.C (s₂ + 1) : ℕ) : ℝ) = (M.slotStart S.C (s₂ + 1) : ℝ) + 2 * Δ S := by
      exact_mod_cast (show M.supportCutoff S.C (s₂ + 1) = M.slotStart S.C (s₂ + 1) + 2 * Δ S by omega)
    have hs2R : ((M.slotStart S.C (s₂ + 2) : ℕ) : ℝ) = (M.slotStart S.C (s₂ + 1) : ℝ) + 4 * Δ S := by
      exact_mod_cast hst
    have hΔsm : (Δs : ℝ) ≤ ((max (2 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hm2s
    have h := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E (hHonLast u huH)
      (a' := M.supportCutoff S.C (s₂ + 1) - max (2 * Δ S) Δs)
      (e := M.supportCutoff S.C (s₂ + 1) - max (2 * Δ S) Δs + Δs)
      (by push_cast [Nat.cast_sub hle] at hdr hsR hm2R hΔsm hcR ⊢; linarith)
      (by push_cast [Nat.cast_sub hle] at hsR hm2R hΔsm hcR hs2R ⊢; linarith)
    rw [Nat.cast_add] at h
    exact h
  have hBB'p := (round_proposal_extends_upTo M F U) S A x R GST s₂ (Hon (s₂ + 1)) (Hs (s₂ + 1)) B B' q
    E hNet hSkew hRedeliver Sy hΔs hRootsQ hParent hOwner
    (le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show s - 1 ≤ s₂ + 1 by omega)))
    ((honestChainExtends_mono M F) S A x (Hon s₂) (Hon (s₂ + 1)) B s₂
      (hHonMono s₂ (by omega) (by omega)) hInv) hVotes hq hqUpd
    (hHs (s₂ + 1) (by omega) (by omega)) hHoldQ
    hHonestQ
    hVotersQ hFrameQ hPropose'
  obtain ⟨i', hl', hsent'⟩ := id hPropose'
  obtain ⟨-, -, hB'par?, -⟩ := (proposal_parent_walk_end M F U) S A x R E (s₂ + 1) i' B' q hl' hsent'
  have hB'p : B'.parent.AncestorEq B' := ancestorEq_of_parent? hB'par?
  have hBB' := ancestorEq_trans hBB'p hB'p
  -- step 5: the certificate
  have hd1 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B'.parent).2.2.2.1 hBB'p
  have hd2 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B'.parent B').2.2.2.1 hB'p
  by_cases heq : (M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h
  · have hT : (M.chainStateOf S.C B'.parent).T_h = (M.chainStateOf S.C B).T_h :=
      (((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B'.parent).2.2.2.2 hBB'p heq.symm).symm
    have hPool' : ∀ u ∈ Q, ∃ a ∈ (x.tickInput q (M.slotStart S.C (s₂ + 2))).attestationsHeld,
        a.val_index = u ∧ a.h = (M.chainStateOf S.C B'.parent).h ∧
        a.T = (M.chainStateOf S.C B'.parent).T_h.root := by
      rw [heq, hT]
      exact hPool
    obtain ⟨h53a, h53b⟩ := (lem53_next_honest_proposal_carries_certificate M F U Fx) S A x R E (s₂ + 2) q B'
      B'.parent Q hPropose' rfl hQuorum hPool'
    rw [heq, hT] at h53a h53b
    refine ⟨hBB', ?_, fun hFresh => ?_⟩
    · rcases h53a with h | h
      · exact Or.inl (by unfold Height at *; omega)
      · exact Or.inr h
    · obtain ⟨h1, h2⟩ := h53b (hPoolT hFresh)
      exact ⟨by unfold Height at *; omega, fun _ => h2⟩
  · have hlt : (M.chainStateOf S.C B).h < (M.chainStateOf S.C B'.parent).h := by
      unfold Height at *
      omega
    have hge : (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h := by
      unfold Height at *
      omega
    exact ⟨hBB', Or.inl hge, fun _ => ⟨hge, fun h => absurd h heq⟩⟩

end GoldilocksCorrectness.Record.Proofs.Executions

