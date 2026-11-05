module
public import GoldilocksCorrectness.Proofs.Executions.Lemma80
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.NextSlotVoteStatementsUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma79UpTo
public import GoldilocksCorrectness.Proofs.Executions.NetworkUpTo
public import GoldilocksCorrectness.Proofs.Executions.ProposalWalkUpTo
public import GoldilocksCorrectness.Proofs.Executions.RoundBaseUpTo

@[expose] public section

/-!
# `Lemma80.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma80.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `lem79a_votes_step_sets`, `lem79_step_sets`, `round_honestChainExtends_steps`,
  `round_attestations_in_pool`, `round_proposal_extends`, `lem80wq_round_height_advances_steps`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono dutyWindowStart_succ_le_slotStart
  one_le_Δ slotStart_eq slotStart_le_of_le slot_add_two_le_of_delivery supportCutoff_eq
  supportCutoff_le_slotStart_succ voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (on_attestation_pool)

open GoldilocksCorrectness.Proofs.Routines (is_live_iff)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks CountedVotes ProposalCountedVotes
  FrameShape lem56_frame_of_shape)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_of_parent? compatible_of_ancestorEq_compatible fc_root_ancestorEq_get_anchor)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Kit theorem, Lemma 79a over two sets.** As Lemma 79a, with the voters of slot `s'` in `Hon`
(where the invariant is read) and the votes of slot `s' + 1` read at the members of `Hon' ⊆ Hon`:
if `HonestChainExtends S Sched x Hon B s'` holds, every member of `Hs` is a member of `Hon` voting at
slot `s'` and honest at the vote time of slot `s' + 1`, and every member `w` of `Hon'` is awake and
honest from the duty window's start of slot `s' + 1` to its vote time, counts fewer than twice `Hs`,
has its fork-choice root compatible with `B` and, when that root is `B` or an ancestor of `B`, a
viable head of its voter tree on `B`'s chain — then every slot-`(s' + 1)` vote of a member of
`Hon'` is for a block it holds on `B`'s chain.

Why: Lemma 26b at each member of `Hon'`, the voters' blocks from the invariant's first clause and
the member's locks from its second clause.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `s'`: the slot; `Hon`, `Hon'`: the two sets; `Hs`: the honest voters of slot
  `s'`; `B`: the block.

Roots name blocks until `supportCutoff S s'`: Lemma 26b, which the proof calls at slot `s'`,
takes blocks as held up to the support cutoff of slot `s'`.

Restated with the delivery premises up to `supportCutoff S s'`: Lemma 26b at slot `s'` reads deliveries due by then (`lem26b_goldfish_vote_extends_voter_majority_block_held_upTo`). -/
theorem lem79a_votes_step_sets_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s' : ℕ) (Hon Hon' Hs : Finset V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s'))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s'))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s'))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s')
    (hInv : HonestChainExtends S Sched x Hon B s')
    (hSub : Hon' ⊆ Hon)
    (hHsHon : ∀ u ∈ Hs, u ∉ Sched.adv (voteTime S (s' + 1) : Int))
    (hHon' : ∀ v ∈ Hon', ∀ t : ℕ, dutyWindowStart S (s' + 1) ≤ t → t ≤ voteTime S (s' + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hHs : ∀ u ∈ Hs, u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    (hVotersW : ∀ w ∈ Hon', ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S) (s' + 1) votes support_votes →
      voters_count votes < 2 * Hs.card)
    (hF2 : ∀ w ∈ Hon',
      (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).fc_root.compatible B = true)
    (hF3 : ∀ w ∈ Hon',
      (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).fc_root.AncestorEq B →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s' + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S) (s' + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).viable_heads ∧
          B.AncestorEq W) :
    ∀ u ∈ Hon', ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s' + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S (s' + 1)) u).S.T,
        vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ B.AncestorEq H_u := by
  intro w hw vote hSend
  have hΔ := one_le_Δ S
  have hdw : dutyWindowStart S (s' + 1) ≤ slotStart S s' := dutyWindowStart_succ_le_slotStart S s'
  have hv₁ : voteTime S s' = slotStart S s' + Δ S := voteTime_eq S s'
  have hc₁ : supportCutoff S s' = voteTime S s' + Δ S := supportCutoff_eq S s'
  have hv₂ : voteTime S (s' + 1) = voteTime S s' + 4 * Δ S := voteTime_succ S s'
  have hvote : ∀ u ∈ Hs, ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s' H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H_u ∈ (stateBefore x (voteTime S s') u).S.T ∧ B.AncestorEq H_u := by
    intro u hu
    obtain ⟨huHon, -, vote', -, -, hsent⟩ := hHs u hu
    obtain ⟨H_u, hHT, hvt, hBH⟩ := hInv.1 u huHon vote' hsent
    subst hvt
    exact ⟨H_u, hsent, hHT, hBH⟩
  choose H hH using hvote
  let H' : V → Block V := fun u => if h : u ∈ Hs then H u h else B
  have hH' : ∀ u (hu : u ∈ Hs), H' u = H u hu := fun u hu => dif_pos hu
  exact GoldilocksCorrectness.Statements.Executions.lem26b_goldfish_vote_extends_voter_majority_block_held_upTo
    S Sched x GST s' Hs H' B w vote hDiv hMono hSync hCatch hRoots hParent hOwner hGST
    (fun u hu => by
      rw [hH' u hu]
      exact ⟨(hHs u hu).2.1, hHsHon u hu, (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
    (hVotersW w hw) (fun t h1 h2 => hHon' w hw t (by omega) (by omega)) (hF2 w hw) (hF3 w hw)
    (hInv.2.1 w (hSub hw)) hSend

/-- **Kit theorem, Lemma 79's step from one slot's set to the next.** As Lemma 79, with the voters
of slot `s'` in `Hon`, awake and honest from the duty window's start of slot `s'` to the support
cutoff of slot `s' + 1`, and the voters of slot `s' + 1` and the members in `Hon' ⊆ Hon`, awake and
honest from the duty window's start of slot `s' + 1` to the support cutoff of slot `s' + 2`; the
counting and frame conditions are read at the members of `Hon'` — then
`HonestChainExtends S Sched x Hon B s'` gives `HonestChainExtends S Sched x Hon' B (s' + 1)`.

Why: `lem79a_votes_step_sets`; Lemma 79b at `Hon'` with the invariant restricted
(`honestChainExtends_mono`); Lemma 79c at `Hon'`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `s'`: the slot; `Hon`, `Hon'`: the sets of slots `s'` and `s' + 1`; `Hs`: the
  honest voters of each slot; `B`: the block.

Read aloud: each slot's voters need to be honest only through their own slot's update.

Roots name blocks until `supportCutoff S (s' + 1)`: Lemma 79c, which the proof calls at slot
`s'`, takes blocks as held up to the support cutoff of slot `s' + 1`; `lem79a_votes_step_sets`
reads earlier.

Restated with the delivery premises up to `supportCutoff S (s' + 1)`: Lemma 79c at slot `s'` reads deliveries due by then (`lem79c_honestChainExtends_confirmations_step_upTo`); Lemma 79a reads earlier. -/
theorem lem79_step_sets_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s' : ℕ) (Hon Hon' : Finset V) (Hs : ℕ → Finset V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s' + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s' + 1)))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s')
    (hInv : HonestChainExtends S Sched x Hon B s')
    (hSub : Hon' ⊆ Hon)
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S s' ≤ t → t ≤ supportCutoff S (s' + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hHon' : ∀ v ∈ Hon', ∀ t : ℕ, dutyWindowStart S (s' + 1) ≤ t → t ≤ supportCutoff S (s' + 2) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hHs : ∀ u ∈ Hs s', u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    (hHs' : ∀ u ∈ Hs (s' + 1), u ∈ Hon' ∧ u ∈ S.P.committee (s' + 1) ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' + 1 ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s' + 1)) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    (hVotersW : ∀ w ∈ Hon', ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S) (s' + 1) votes support_votes →
      voters_count votes < 2 * (Hs s').card)
    (hVotersV : ∀ v ∈ Hon',
      voters_count ((stateBefore x (supportCutoff S (s' + 2)) v).A.pool (s' + 1)) <
        2 * (Hs (s' + 1)).card)
    (hF2 : ∀ w ∈ Hon',
      (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).fc_root.compatible B = true)
    (hF3 : ∀ w ∈ Hon',
      (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).fc_root.AncestorEq B →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s' + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S) (s' + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).viable_heads ∧
          B.AncestorEq W)
    (hFv : ∀ v ∈ Hon',
      (stateBefore x (supportCutoff S (s' + 2)) v).S.F.compatible B = true) :
    HonestChainExtends S Sched x Hon' B (s' + 1) := by
  have hΔ := one_le_Δ S
  have hdw : dutyWindowStart S s' ≤ dutyWindowStart S (s' + 1) := dutyWindowStart_mono S (by omega)
  have hdw' : dutyWindowStart S (s' + 1) ≤ slotStart S s' := dutyWindowStart_succ_le_slotStart S s'
  have hdw₂ : dutyWindowStart S (s' + 1) ≤ dutyWindowStart S (s' + 2) :=
    dutyWindowStart_mono S (by omega)
  have hv₀ : voteTime S s' = slotStart S s' + Δ S := voteTime_eq S s'
  have hv₁ : voteTime S (s' + 1) = voteTime S s' + 4 * Δ S := voteTime_succ S s'
  have hv₂ : voteTime S (s' + 2) = voteTime S (s' + 1) + 4 * Δ S := voteTime_succ S (s' + 1)
  have hc₁ : supportCutoff S (s' + 1) = voteTime S (s' + 1) + Δ S := supportCutoff_eq S (s' + 1)
  have hc₂ : supportCutoff S (s' + 2) = voteTime S (s' + 2) + Δ S := supportCutoff_eq S (s' + 2)
  have hInv' := honestChainExtends_mono S Sched x Hon Hon' B s' hSub hInv
  have hVotes := lem79a_votes_step_sets_upTo S Sched x GST s' Hon Hon' (Hs s') B hDiv hMono (hSync.mono (by have := supportCutoff_eq S s'; omega)) (hCatch.mono (by have := supportCutoff_eq S s'; omega))
    (hRoots.mono (by have := supportCutoff_eq S s'; omega)) hParent hOwner hGST hInv hSub
    (fun u hu => (hHon u (hHs u hu).1 (voteTime S (s' + 1)) (by omega) (by omega)).2)
    (fun v hv t h1 h2 => hHon' v hv t h1 (by omega)) hHs hVotersW hF2 hF3
  refine ⟨hVotes, ?_, ?_⟩
  · exact lem79b_honestChainExtends_locks_step S Sched x s' Hon' B hDiv hInv'
      (fun v hv t h1 h2 => hHon' v hv t (le_trans (dutyWindowStart_mono S (by omega)) h1) (by omega))
  · exact lem79c_honestChainExtends_confirmations_step_upTo S Sched x GST s' Hon' (Hs (s' + 1)) B hDiv
      hMono hSync hCatch hRoots hParent hOwner (by omega) hVotes
      (fun v hv t h1 h2 => hHon' v hv t (by omega) h2) hHs' hVotersV hFv

/-- **Kit theorem, the slot invariant through the round, over per-slot sets.** With the member
sets `Hon s'` shrinking from slot to slot, each awake and honest through its slot's update and not
past the start of slot `s₂ + 2`, the honest voters of each slot in its set, the counts of each slot
read at its set, `StepFrameAt` relative to `B` at the members of `Hon (s' + 1)` for every slot `s'`
with `s' + 3 ≤ s₂ + 2`, and the voter's fork choice of slot `s₂ + 1` at the members of
`Hon (s₂ + 1)`: from `HonestChainExtends S Sched x (Hon s) B s`, the invariant holds at slot `s₂`
for `Hon s₂`, and every slot-`(s₂ + 1)` vote of a member of `Hon (s₂ + 1)` is for a block it holds
on `B`'s chain.

Why: `lem79_step_sets` at each slot from `s` to `s₂ − 1`, then `lem79a_votes_step_sets` at `s₂`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `s`: the first slot; `s₂`: the last slot the invariant is carried to; `Hon`: the
  member sets; `Hs`: the honest voters of each slot; `B`: the proposal.

Roots name blocks until `supportCutoff S s₂`: `lem79a_votes_step_sets`, which the proof calls at
slot `s₂`, takes blocks as held up to the support cutoff of slot `s₂`; the steps before it read
earlier.

Restated with the delivery premises up to `supportCutoff S s₂`: the step at the last slot `s₂ − 1` reads deliveries due by then (`lem79_step_sets_upTo`), the vote clause at `s₂` likewise (`lem79a_votes_step_sets_upTo`). -/
theorem round_honestChainExtends_steps_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s s₂ : ℕ) (Hon Hs : ℕ → Finset V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s₂))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s₂))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s₂))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hs₂ : s ≤ s₂)
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s₂ + 2 → Hon (s' + 1) ⊆ Hon s')
    (hHon : ∀ s', s ≤ s' → s' < s₂ + 2 → ∀ v ∈ Hon s', ∀ t : ℕ,
      dutyWindowStart S s' ≤ t → t ≤ supportCutoff S (s' + 1) → t ≤ slotStart S (s₂ + 2) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hHs : ∀ s', s ≤ s' → s' < s₂ + 2 → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    (hVoters : ∀ s', s ≤ s' → s' < s₂ + 2 → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) v).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) v).S) (s' + 1) votes support_votes →
        voters_count votes < 2 * (Hs s').card) ∧
      voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') < 2 * (Hs s').card)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s₂ + 2 → ∀ w ∈ Hon (s' + 1), StepFrameAt S Sched x B s' w)
    (hStepLast : ∀ w ∈ Hon (s₂ + 1),
      (fg_to_ac (stateBefore x (voteTime S (s₂ + 1)) w).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (voteTime S (s₂ + 1)) w).S).fc_root.AncestorEq B →
        ∀ tree : Finset (Block V),
          voter_block_tree S.C (stateBefore x (voteTime S (s₂ + 1)) w).A
            (fg_to_ac (stateBefore x (voteTime S (s₂ + 1)) w).S) (s₂ + 1) = .ok tree →
          ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s₂ + 1)) w).S).viable_heads ∧
            B.AncestorEq W))
    (hBase : HonestChainExtends S Sched x (Hon s) B s) :
    HonestChainExtends S Sched x (Hon s₂) B s₂ ∧
    ∀ u ∈ Hon (s₂ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s₂ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S (s₂ + 1)) u).S.T,
        vote = GoldfishVote.mk u (s₂ + 1) H_u.root ∧ B.AncestorEq H_u := by
  have hΔ := one_le_Δ S
  have hss : ∀ k, slotStart S (k + 1) = slotStart S k + 4 * Δ S := fun k => by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv : ∀ k, voteTime S k = slotStart S k + Δ S := voteTime_eq S
  have hc : ∀ k, supportCutoff S k = voteTime S k + Δ S := supportCutoff_eq S
  -- the induction
  have key : ∀ d, s + d ≤ s₂ → HonestChainExtends S Sched x (Hon (s + d)) B (s + d) := by
    intro d
    induction d with
    | zero => intro _; exact hBase
    | succ d ih =>
        intro hd
        have hm0 := slotStart_le_of_le S (show s ≤ s + d by omega)
        have hm3 := slotStart_le_of_le S (show s + d + 3 ≤ s₂ + 2 by omega)
        have hss1 := hss (s + d)
        have hss2 : slotStart S (s + d + 2) = slotStart S (s + d + 1) + 4 * Δ S := hss (s + d + 1)
        have hss3 : slotStart S (s + d + 3) = slotStart S (s + d + 2) + 4 * Δ S := hss (s + d + 2)
        have hss2' : slotStart S (s + d + 1 + 1) = slotStart S (s + d + 1) + 4 * Δ S :=
          hss (s + d + 1)
        have hv0 := hv (s + d)
        have hv1 := hv (s + d + 1)
        have hv2 : voteTime S (s + d + 2) = slotStart S (s + d + 2) + Δ S := hv (s + d + 2)
        have hv2' : voteTime S (s + d + 1 + 1) = slotStart S (s + d + 1 + 1) + Δ S := hv _
        have hc1 := hc (s + d + 1)
        have hc2 : supportCutoff S (s + d + 2) = voteTime S (s + d + 2) + Δ S := hc (s + d + 2)
        have hc2' : supportCutoff S (s + d + 1 + 1) = voteTime S (s + d + 1 + 1) + Δ S := hc _
        have hvs := hv s
        have hcut : supportCutoff S (s + d + 1) ≤ supportCutoff S s₂ := by
          have h1 := slotStart_le_of_le S (show s + d + 1 ≤ s₂ by omega)
          have h2 := hc s₂
          have h3 := hv s₂
          omega
        exact lem79_step_sets_upTo S Sched x GST (s + d) (Hon (s + d)) (Hon (s + d + 1)) Hs B hDiv
          hMono (hSync.mono hcut) (hCatch.mono hcut) (hRoots.mono hcut) hParent hOwner (by omega) (ih (by omega))
          (hHonMono (s + d) (by omega) (by omega))
          (fun v hv' t h1 h2 => hHon (s + d) (by omega) (by omega) v hv' t h1 h2 (by omega))
          (fun v hv' t h1 h2 => hHon (s + d + 1) (by omega) (by omega) v hv' t h1 h2 (by omega))
          (hHs (s + d) (by omega) (by omega)) (hHs (s + d + 1) (by omega) (by omega))
          (fun w hw => (hVoters (s + d) (by omega) (by omega) w
            (hHonMono (s + d) (by omega) (by omega) hw)).1)
          (fun v hv' => (hVoters (s + d + 1) (by omega) (by omega) v hv').2)
          (fun w hw => (hStep (s + d) (by omega) (by omega) w hw).1)
          (fun w hw => (hStep (s + d) (by omega) (by omega) w hw).2.1)
          (fun v hv' => (hStep (s + d) (by omega) (by omega) v hv').2.2)
  obtain ⟨d, rfl⟩ : ∃ d, s₂ = s + d := ⟨s₂ - s, by omega⟩
  have hInv := key d le_rfl
  have hm0 := slotStart_le_of_le S (show s ≤ s + d by omega)
  have hss1 := hss (s + d)
  have hss2 : slotStart S (s + d + 2) = slotStart S (s + d + 1) + 4 * Δ S := hss (s + d + 1)
  have hss2' : slotStart S (s + d + 1 + 1) = slotStart S (s + d + 1) + 4 * Δ S := hss (s + d + 1)
  have hv0 := hv (s + d)
  have hv1 := hv (s + d + 1)
  have hc1 := hc (s + d + 1)
  have hc2' : supportCutoff S (s + d + 1 + 1) = voteTime S (s + d + 1 + 1) + Δ S := hc _
  have hv2' : voteTime S (s + d + 1 + 1) = slotStart S (s + d + 1 + 1) + Δ S := hv _
  have hvs := hv s
  have hdw : dutyWindowStart S (s + d) ≤ dutyWindowStart S (s + d + 1) :=
    dutyWindowStart_mono S (by omega)
  have hdw' : dutyWindowStart S (s + d + 1) ≤ slotStart S (s + d) :=
    dutyWindowStart_succ_le_slotStart S (s + d)
  refine ⟨hInv, ?_⟩
  exact lem79a_votes_step_sets_upTo S Sched x GST (s + d) (Hon (s + d)) (Hon (s + d + 1)) (Hs (s + d))
    B hDiv hMono hSync hCatch hRoots hParent hOwner (by omega) hInv
    (hHonMono (s + d) (by omega) (by omega))
    (fun u hu => (hHon (s + d) (by omega) (by omega) u (hHs (s + d) (by omega) (by omega) u hu).1
      (voteTime S (s + d + 1)) (by omega) (by omega) (by omega)).2)
    (fun v hv' t h1 h2 => hHon (s + d + 1) (by omega) (by omega) v hv' t h1 (by omega) (by omega))
    (hHs (s + d) (by omega) (by omega))
    (fun w hw => (hVoters (s + d) (by omega) (by omega) w
      (hHonMono (s + d) (by omega) (by omega) hw)).1)
    (fun w hw => (hStepLast w hw).1) (fun w hw => (hStepLast w hw).2)

/-- **Kit theorem, the round's attestations reach the next proposer.** Write `a` for the support
cutoff of slot `s + 1`, and `H`, `T` for the height of `B`'s chain state and the root of its `T_h`.
In an execution where every time is reached, corruption is permanent and attestations are delivered
within `Δ_F` after `GST`: if `GST` is at most `a`, `a + Δ_F` is at most `t₁`, `B` is of slot `s`;
and for every member `v` of `Q`: `v` is awake and honest from the duty window's start of slot
`s + 1` to `a`, its update of slot `s + 1` at `a` saves `B` as the confirmation of slot `s` with
`B` among its fast blocks, every live lock entry its revocation of slot `s + 1` leaves is compatible
with `B`, its frame before `a` has the root `ρ v`, `B` or an ancestor of `B`, and the
`head_height_floor` `φ v`, at most `H`, it holds `B` before `a`, and its cache `h_j` is less than
`H`, or no lock at `H`, or its lock at `H` is `T`; and `q` is awake and honest from `tq` to `t₁`,
with `tq + Δ_F ≤ t₁` — then `q`'s pool before `t₁` holds an attestation of every member of `Q` at
`H` naming `T`; and when no member's record before `a` holds anything sent at `H`, a target of each.

Why: Lemma 61 at each member; an attestation already sent is traced to the tick that sent it
(`record_content_sent`); with nothing sent at `H`, Lemma 55's corollary. Each reaches `q` by
synchrony or by the catch-up on `q`'s last wake (`delivered_before_stepBefore_of_honest_send`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `r`: the round; `s`: its first slot; `t₁`: the time of the next proposal; `tq`:
  the time from which `q` is awake and honest;
- `Q`: the quorum; `B`: the proposal; `q`: the next proposer; `φ v`, `ρ v`: the
  `head_height_floor` and the root of member `v`'s frame before `a`.

Restated with the delivery premises up to `t₁`: each member's attestation, sent by the support cutoff of slot `s + 1` and from `tq` on, reaches `q` one delay later, by `t₁` (`delivered_before_stepBefore_of_honest_send_upTo`). -/
theorem round_attestations_in_pool_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST r s t₁ tq : ℕ) (Q : Finset V) (B : Block V) (q : V)
    (φ : V → Height) (ρ : V → Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSyncF : SynchronyFromWakeUpTo S Sched x (Δ_F S) GST fgObject t₁)
    (hCatchF : CatchUpOnWakeUpTo S Sched x (Δ_F S) GST fgObject t₁)
    (hs : s = r * S.C.R)
    (hGST : GST ≤ supportCutoff S (s + 1))
    (ht₁ : supportCutoff S (s + 1) + Δ_F S ≤ t₁)
    (hBslot : B.slot = s)
    (hv : ∀ v ∈ Q, ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hUpd : ∀ v ∈ Q, ∃ A' : ACState V,
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A' ∧
      A'.saved_confirmation s = some B ∧ B ∈ A'.fast_blocks)
    (hLocks : ∀ v ∈ Q, ∀ A'' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) v).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) v).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A'' →
      ∀ e ∈ A''.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) v).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true)
    (hShape : ∀ v ∈ Q, FrameShape (stateBefore x (supportCutoff S (s + 1)) v).S (ρ v) (φ v))
    (hRoot : ∀ v ∈ Q, (ρ v).AncestorEq B)
    (hBin : ∀ v ∈ Q, B ∈ (stateBefore x (supportCutoff S (s + 1)) v).S.T)
    (hLockBox : ∀ v ∈ Q,
      (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
        some (chainStateOf S.C B).T_h.root)
    (hBHeight : ∀ v ∈ Q, φ v ≤ (chainStateOf S.C B).h)
    (htq : tq + Δ_F S ≤ t₁)
    (hqAwake : ∀ t : ℕ, tq ≤ t → t ≤ t₁ →
      q ∈ Sched.awake (t : Int) ∧ q ∉ Sched.adv (t : Int)) :
    (∀ u ∈ Q, ∃ a ∈ (stateBefore x t₁ q).S.attestations,
      a.val_index = u ∧ a.h = (chainStateOf S.C B).h ∧ a.T = (chainStateOf S.C B).T_h.root) ∧
    ((∀ u ∈ Q, ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
        b.h ≠ (chainStateOf S.C B).h) →
      ∀ u ∈ Q, ∃ a ∈ (stateBefore x t₁ q).S.attestations,
        a.val_index = u ∧ a.h = (chainStateOf S.C B).h ∧
        a.T = (chainStateOf S.C B).T_h.root ∧ a.τ = false) := by
  -- an attestation an honest validator sent by `a` is in `q`'s pool before `t₁`
  have hDeliver : ∀ (j t' : ℕ) (v : V) (a : Attestation V),
      x.lbl j = AtomicAction.tickAllAwake t' → t' ≤ supportCutoff S (s + 1) →
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[j + 1].sent - x[j].sent →
      v ∉ Sched.adv (t' : Int) → a ∈ (stateBefore x t₁ q).S.attestations := by
    intro j t' v a hl ht' hsent hhon
    have hm1 : max t' GST ≤ supportCutoff S (s + 1) := max_le ht' hGST
    have hm2 : max (max t' GST) tq + Δ_F S ≤ t₁ := by
      have := le_max_left (max t' GST) tq
      have := le_max_right (max t' GST) tq
      omega
    obtain ⟨hT1, hT2⟩ := time_of_lbl_tickAllAwake x hl
    have hhon' : v ∉ Sched.adv (x[j].time : Int) := fun h =>
      hhon (hMono _ _ (by exact_mod_cast (by omega : x[j].time ≤ t')) h)
    obtain ⟨d, -, hld, hd⟩ := delivered_before_stepBefore_of_honest_send_upTo x hDiv
      (hSyncF.mono hm2) (hCatchF.mono hm2)
      hMono (sm := ⟨v, NamedObject.attest a⟩) ⟨hsent, hhon'⟩ trivial
      (le_trans (by omega : x[j + 1].time ≤ t') (le_trans (le_max_left t' GST) (le_max_left _ tq)))
      (le_trans (le_max_right t' GST) (le_max_left _ tq))
      (fun t'' h1 h2 => hqAwake t'' (le_trans (le_max_right _ _) h1) (by omega))
    obtain ⟨-, -, hstep⟩ := deliver_step_state x hld
    have hin : a ∈ (x[d + 1][q].st).S.attestations := by
      rw [hstep]
      exact (on_attestation_pool _ a).2 (tick_attestation_well_formed S Sched x j t' v a hl hsent)
    have hin' : a ∈ (stateBefore x (max (max t' GST) tq + Δ_F S) q).S.attestations :=
      pool_grows_of_le x q hd a hin
    exact pool_grows_of_le x q (stepBefore_mono x hDiv hm2) a hin'
  have hDuty : ∀ v ∈ Q, dutyWindowStart S (s + 1) ≤ supportCutoff S (s + 1) := by
    intro v _
    have hΔ := one_le_Δ S
    have h1 := dutyWindowStart_succ_le_slotStart S s
    have h2 : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    rw [supportCutoff_eq, voteTime_eq]
    omega
  refine ⟨fun u hu => ?_, fun hFresh u hu => ?_⟩
  · obtain ⟨A', hU, hS, hF⟩ := hUpd u hu
    have hLk := update_lock_entries_ancestorEq S Sched x s B u A' hDiv hMono (hv u hu) hU
      hS hBslot (hLocks u hu)
    rcases lem61_honest_validator_attests_frame S Sched x r s B u A' (ρ u) (φ u) hDiv hMono
        hs (hv u hu) hU hS hF hLk (hShape u hu) (hRoot u hu) (hBHeight u hu) (hBin u hu)
        (hLockBox u hu)
      with ⟨i, a, hl, hsent, hav, hah, haT⟩ | ⟨b, hb, hbh, hbT⟩
    · exact ⟨a, hDeliver i _ u a hl le_rfl hsent (hv u hu _ (hDuty u hu) le_rfl).2, hav, hah, haT⟩
    · obtain ⟨j, t', a, hl, ht', -, hadv, hsent, hav, hac, -⟩ :=
        record_content_sent S Sched x _ u b hDiv hb
      refine ⟨a, hDeliver j t' u a hl ht'.le hsent hadv, hav, ?_, ?_⟩
      · rw [← hbh, ← hac]
        rfl
      · rw [← hbT, ← hac]
        rfl
  · obtain ⟨A', hU, hS, hF⟩ := hUpd u hu
    have hLk := update_lock_entries_ancestorEq S Sched x s B u A' hDiv hMono (hv u hu) hU
      hS hBslot (hLocks u hu)
    obtain ⟨hViable, hRecord⟩ := lem61_frame_hypotheses S Sched x s B u (ρ u) (φ u) (hShape u hu)
      (hRoot u hu) (hBHeight u hu) (hBin u hu) (hLockBox u hu)
    obtain ⟨i, a, hl, hsent, hav, hah, haT, hτ⟩ := lem55_target_of_fresh_height S Sched x r s B u
      A' hDiv hMono hs (hv u hu) hU hS hF hLk hViable hRecord (hFresh u hu)
    exact ⟨a, hDeliver i _ u a hl le_rfl hsent (hv u hu _ (hDuty u hu) le_rfl).2, hav, hah, haT,
      hτ⟩

/-- **Kit theorem, the next honest proposal extends the round's proposal.** Write `t₁` for the
start of slot `s₂ + 2`. In an execution with the eight execution assumptions: if `GST` is at most
the vote time of slot `s₂ + 1`; `HonestChainExtends S Sched x Hon B s₂` holds; every
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
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `s₂`: the slot of the invariant; `Hon`: the members; `Hs`: the honest voters of
  slot `s₂ + 1`; `B`: the round's proposal; `B'`: `q`'s proposal; `q`: its proposer.

Roots name blocks until `supportCutoff S (s₂ + 1)`: `proposal_parent_extends_majority_block`,
which the proof calls at slot `s₂ + 1`, takes blocks as held up to the support cutoff of slot
`s₂ + 1`.

Restated with the delivery premises up to `supportCutoff S (s₂ + 1)`: `proposal_parent_extends_majority_block_upTo` at slot `s₂ + 1` reads deliveries due by then. -/
theorem round_proposal_extends_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₂ : ℕ) (Hon Hs : Finset V) (B B' : Block V) (q : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s₂ + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s₂ + 1)))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s₂ + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S (s₂ + 1))
    (hInv : HonestChainExtends S Sched x Hon B s₂)
    (hVotes : ∀ u ∈ Hon, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s₂ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S (s₂ + 1)) u).S.T,
        vote = GoldfishVote.mk u (s₂ + 1) H_u.root ∧ B.AncestorEq H_u)
    (hq : q ∈ Hon)
    (hqw : ∀ t : ℕ, dutyWindowStart S (s₂ + 1) ≤ t → t ≤ slotStart S (s₂ + 2) →
      q ∈ Sched.awake (t : Int) ∧ q ∉ Sched.adv (t : Int))
    (hHs : ∀ u ∈ Hs, u ∈ Hon ∧ u ∈ S.P.committee (s₂ + 1) ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s₂ + 1 ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s₂ + 1)) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    (hHonest : ∀ u ∈ Hon, u ∉ Sched.adv (slotStart S (s₂ + 2) : Int))
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S (s₂ + 2)) q).A
        (fg_to_ac (stateBefore x (slotStart S (s₂ + 2)) q).S) (s₂ + 1) votes support_votes →
      voters_count votes < 2 * Hs.card)
    (hFrameQ : (fg_to_ac (stateBefore x (slotStart S (s₂ + 2)) q).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (slotStart S (s₂ + 2)) q).S).fc_root.AncestorEq B →
        ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S (s₂ + 2)) q).S).tree,
          W ∈ (fg_to_ac (stateBefore x (slotStart S (s₂ + 2)) q).S).viable_heads ∧
            B.AncestorEq W))
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s₂ + 2)) ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    B.AncestorEq B'.parent := by
  have hΔ := one_le_Δ S
  have hss₁ : slotStart S (s₂ + 1) = slotStart S s₂ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss₂ : slotStart S (s₂ + 2) = slotStart S (s₂ + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s₂ + 1), show s₂ + 2 = s₂ + 1 + 1 from rfl, Nat.mul_add,
      Nat.mul_one]
  have hv₁ : voteTime S (s₂ + 1) = slotStart S (s₂ + 1) + Δ S := voteTime_eq S (s₂ + 1)
  have hv₂ : voteTime S (s₂ + 2) = slotStart S (s₂ + 2) + Δ S := voteTime_eq S (s₂ + 2)
  have hc₁ : supportCutoff S (s₂ + 1) = voteTime S (s₂ + 1) + Δ S := supportCutoff_eq S (s₂ + 1)
  have hdw : dutyWindowStart S (s₂ + 1) ≤ slotStart S s₂ := dutyWindowStart_succ_le_slotStart S s₂
  obtain ⟨i, hl, hsent⟩ := hPropose'
  have hAnc := get_anchor_ancestorEq_proposal_parent S Sched x (s₂ + 2) i B' q hl hsent
  -- `q`'s anchor is compatible with `B`
  have hAC : (get_anchor (stateBefore x (slotStart S (s₂ + 2)) q).A
      (fg_to_ac (stateBefore x (slotStart S (s₂ + 2)) q).S)
      ((slotStart S (s₂ + 2) : ℕ) : Int)).compatible B = true := by
    refine GoldilocksCorrectness.Statements.Routines.lem6_get_anchor_compatible _ _ _ B
      (fun e he hlive => ?_) hFrameQ.1
    refine live_locks_compatible_of_honestChainExtends S Sched x Hon B s₂ (slotStart S (s₂ + 2))
      q hDiv hInv hq (fun t h1 h2 => hqw t (le_trans (dutyWindowStart_mono S (by omega)) h1) h2) (by omega) (by omega) e he ?_
    simp only [is_live_iff] at hlive
    exact hlive.1
  rcases (compatible_iff _ _).1 hAC with hAB | hBA
  · -- the anchor is an ancestor of `B`: the majority's walk passes `B`
    have hchoose : ∀ u : V, ∃ Hu : Block V, u ∈ Hs →
        (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s₂ + 1)) ∧
          (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s₂ + 1) Hu.root)⟩ :
            SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
        Hu ∈ (stateBefore x (voteTime S (s₂ + 1)) u).S.T ∧ B.AncestorEq Hu := by
      intro u
      by_cases hu : u ∈ Hs
      · obtain ⟨huH, -, vote, -, -, i', hl', hs'⟩ := hHs u hu
        obtain ⟨Hu, hHuT, hvote, hBH⟩ := hVotes u huH vote ⟨i', hl', hs'⟩
        rw [hvote] at hs'
        exact ⟨Hu, fun _ => ⟨⟨i', hl', hs'⟩, hHuT, hBH⟩⟩
      · exact ⟨B, fun h => absurd h hu⟩
    choose Hf hHf using hchoose
    have hρB : (fg_to_ac (stateBefore x (slotStart S (s₂ + 2)) q).S).fc_root.AncestorEq B :=
      ancestorEq_trans (fc_root_ancestorEq_get_anchor _ _ _) hAB
    exact (proposal_parent_extends_majority_block_upTo S Sched x GST (s₂ + 1) i Hs Hf B B' q hDiv hMono
      hSync hCatch hRoots hParent hOwner hGST
      (fun u hu => ⟨(hHs u hu).2.1, hHonest u (hHs u hu).1, (hHf u hu).1, (hHf u hu).2.1,
        (hHf u hu).2.2⟩)
      hVotersQ (fun t h1 h2 => hqw t (by omega) (by omega)) hl hsent (hFrameQ.2 hρB) hAB).1
  · exact ancestorEq_trans hBA hAnc

/-- Lemma 80 over per-slot member sets, with the frames read at the first slot's three reading
points, the step conditions per slot after the action time, and `q`'s fork choice before its
proposal. The proof; the audited statement is in `Statements/Executions/RoundStatements.lean`.

Roots name blocks until `supportCutoff S (s'' - 1)`: `round_proposal_extends`, which the proof
calls at the slot `s'' - 2`, takes blocks as held up to the support cutoff of slot `s'' - 1`;
the base and the invariant through the round read earlier.

Restated with the delivery premises up to `supportCutoff S (s'' - 1)`, the attestations' up to `slotStart S s''`: the blocks and Goldfish votes the proof reads are due by the support cutoff of slot `s'' − 1` (`round_proposal_extends_upTo`), the attestations by the start of slot `s''` (`round_attestations_in_pool_upTo`). -/
theorem lem80wq_round_height_advances_steps_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST r s s'' : ℕ) (Hon : ℕ → Finset V) (Q : Finset V) (Hs : ℕ → Finset V)
    (H : V → Block V) (X B B' : Block V) (p q : V) (φ : Height) (φw φv : V → Height)
    (ρp : Block V) (ρw ρv : V → Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s'' - 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s'' - 1)))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    -- attestations are delivered within `Δ_F S` after `GST`
    (hSyncF : SynchronyFromWakeUpTo S Sched x (Δ_F S) GST fgObject (slotStart S s''))
    (hCatchF : CatchUpOnWakeUpTo S Sched x (Δ_F S) GST fgObject (slotStart S s''))
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s) (hs'' : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST ≤ voteTime S (s - 1))
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- the members of slot `s'` are awake and honest from the duty window's start of slot `s'` to
    -- the support cutoff of slot `s' + 1`, and not past the start of slot `s''`
    (hHon : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s', ∀ t : ℕ,
      dutyWindowStart S s' ≤ t → t ≤ supportCutoff S (s' + 1) → t ≤ slotStart S s'' →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- the proposer: awake and honest from the vote time of slot `s − 1` to the start of slot `s`
    (hp : ∀ t : ℕ, voteTime S (s - 1) ≤ t → t ≤ slotStart S s →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      u ∉ Sched.adv (voteTime S s : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S (s - 1)) u).S.T ∧ X.AncestorEq (H u))
    -- at every member of `Hon s`, the voters its vote of slot `s` counts are fewer than twice
    -- `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S s) w).A
        (fg_to_ac (stateBefore x (voteTime S s) w).S) s votes support_votes →
      voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon s, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S s) w).A
        ((voteTime S s : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S s) w).S)
        ((voteTime S s : ℕ) : Int) s = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S s) w).S) ((voteTime S s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (stateBefore x (voteTime S s) w).S.T, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root ≠ B.root)
    -- the honest voters of slot `s'` are members of `Hon s'` and of the slot's committee
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    -- the counts of slot `s'`, read at the members of `Hon s'`: the voters counted by a vote of
    -- slot `s' + 1` and the slot-`s'` voters of the pool before the support cutoff of slot
    -- `s' + 1` are fewer than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) v).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) v).S) (s' + 1) votes support_votes →
        voters_count votes < 2 * (Hs s').card) ∧
      voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') < 2 * (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S s'') q).A
        (fg_to_ac (stateBefore x (slotStart S s'') q).S) (s'' - 1) votes support_votes →
      voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- the frames at the three reading points of slot `s`: `p`'s before the start of slot `s`,
    -- each member's before the vote time of slot `s` and before the action time `a`, with their
    -- roots and `head_height_floor` values
    (hShapeP : FrameShape (stateBefore x (slotStart S s) p).S ρp φ)
    (hShapeW : ∀ w ∈ Hon s, FrameShape (stateBefore x (voteTime S s) w).S (ρw w) (φw w))
    (hShapeV : ∀ v ∈ Hon s,
      FrameShape (stateBefore x (supportCutoff S (s + 1)) v).S (ρv v) (φv v))
    -- each member's `head_height_floor` before the vote time is at least the proposer's and at
    -- most the chain-state height of `B`'s parent; before `a`, at most that of `B`
    (hFloorW : ∀ w ∈ Hon s, φ ≤ φw w ∧ φw w ≤ (chainStateOf S.C B.parent).h)
    (hFloorV : ∀ v ∈ Hon s, φv v ≤ (chainStateOf S.C B).h)
    -- the roots: before the vote time on `B`'s parent's chain, before `a` on `B`'s chain
    (hRootW : ∀ w ∈ Hon s, (ρw w).AncestorEq B.parent)
    (hRootAr : ∀ v ∈ Hon s, (ρv v).AncestorEq B)
    -- some block of `p`'s tree, on `X`'s and `ρp`'s chains, reaches `φ`
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ ρp.AncestorEq W ∧ φ ≤ (chainStateOf S.C W).h)
    -- after the action time, at the members of the next slot: `StepFrameAt` relative to `B` for
    -- every slot `s'` with `s' + 3 ≤ s''`; for the last slot `s'' − 1`, the voter's fork choice
    -- before its vote time (the first two conjuncts of `StepFrameAt S Sched x B (s'' − 2) w`)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt S Sched x B s' w)
    (hStepLast : ∀ w ∈ Hon (s'' - 1),
      (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).fc_root.AncestorEq B →
        ∀ tree : Finset (Block V),
          voter_block_tree S.C (stateBefore x (voteTime S (s'' - 1)) w).A
            (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S) (s'' - 1) = .ok tree →
          ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).viable_heads ∧
            B.AncestorEq W))
    -- the quorum attests at `a`, inside slot `s`'s active window
    (hQ : Q ⊆ Hon s) (hQuorum : quorum V ≤ Q.card)
    -- the record of every member of `Q` before `a`: the cache `h_j` is less than `H`, or no lock
    -- at `H`, or the lock at `H` is `T`
    (hLockBox : ∀ v ∈ Q,
      (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
        some (chainStateOf S.C B).T_h.root)
    -- the next proposer is a member of the last slot's set
    (hq : q ∈ Hon (s'' - 1))
    -- `q`'s fork-choice root before the start of slot `s''` is compatible with `B`, and when it
    -- is `B` or an ancestor of `B`, a block of `q`'s frame tree that is `B` or a descendant of `B`
    -- is a viable head
    (hFrameQ : (fg_to_ac (stateBefore x (slotStart S s'') q).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (slotStart S s'') q).S).fc_root.AncestorEq B →
        ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S s'') q).S).tree,
          W ∈ (fg_to_ac (stateBefore x (slotStart S s'') q).S).viable_heads ∧ B.AncestorEq W))
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        Q ⊆ (chainStateOf S.C B').progress ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
        b.h ≠ (chainStateOf S.C B).h) →
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
        ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
          (chainStateOf S.C B').J = (chainStateOf S.C B).T_h)) := by
  -- the slots: `s'' = s₂ + 2`, with `s ≤ s₂`
  have hR := S.C.R_ge_two
  have hs2 := slot_add_two_le_of_delivery S hs''
  obtain ⟨s₂, rfl⟩ : ∃ s₂, s'' = s₂ + 2 := ⟨s'' - 2, by omega⟩
  rw [show s₂ + 2 - 1 = s₂ + 1 by omega] at hVotersQ hStepLast hq hRoots hSync hCatch
  -- the times
  have hΔ := one_le_Δ S
  have hss : ∀ k, slotStart S (k + 1) = slotStart S k + 4 * Δ S := fun k => by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv : ∀ k, voteTime S k = slotStart S k + Δ S := voteTime_eq S
  have hc : ∀ k, supportCutoff S k = voteTime S k + Δ S := supportCutoff_eq S
  have hsm : s - 1 + 1 = s := by omega
  have hvs0 := hv (s - 1)
  have hss0 : slotStart S s = slotStart S (s - 1) + 4 * Δ S := by rw [← hss (s - 1), hsm]
  have hvs := hv s
  have hss1 := hss s
  have hvs1 := hv (s + 1)
  have hcs1 := hc (s + 1)
  have hm2 := slotStart_le_of_le S (show s + 2 ≤ s₂ + 2 by omega)
  have hss2 : slotStart S (s + 2) = slotStart S (s + 1) + 4 * Δ S := hss (s + 1)
  have ha : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S (s₂ + 2) := hs''
  have hdw₁ : dutyWindowStart S s ≤ dutyWindowStart S (s + 1) := dutyWindowStart_mono S (by omega)
  have hdwS : dutyWindowStart S s ≤ slotStart S (s - 1) := by
    have h := dutyWindowStart_succ_le_slotStart S (s - 1)
    rw [hsm] at h
    exact h
  have hc2' : supportCutoff S (s₂ + 1 + 1) = voteTime S (s₂ + 1 + 1) + Δ S := hc _
  have hv2' : voteTime S (s₂ + 1 + 1) = slotStart S (s₂ + 1 + 1) + Δ S := hv _
  have hss2' : slotStart S (s₂ + 1 + 1) = slotStart S (s₂ + 2) := rfl
  have hcut₁ : supportCutoff S (s + 1) ≤ supportCutoff S (s₂ + 1) := by
    have h1 := slotStart_le_of_le S (show s + 1 ≤ s₂ + 1 by omega)
    have h2 := hc (s₂ + 1)
    have h3 := hv (s₂ + 1)
    omega
  have hcut₂ : supportCutoff S s₂ ≤ supportCutoff S (s₂ + 1) := by
    have h1 := hss s₂
    have h2 := hc s₂
    have h3 := hv s₂
    have h4 := hc (s₂ + 1)
    have h5 := hv (s₂ + 1)
    omega
  -- `B` is of slot `s`
  have hPropose₀ : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s - 1 + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent := by
    rw [hsm]
    exact hPropose
  obtain ⟨i₀, hl₀, hsent₀⟩ := hPropose₀
  have hBslot : B.slot = s := by
    rw [← hsm]
    exact (proposal_parent_walk_end S Sched x (s - 1) i₀ B p hl₀ hsent₀).1
  -- step 1: the base, at the first slot's set
  obtain ⟨hHeld, hBase, hUpd⟩ := round_base_steps_upTo S Sched x GST s (Hon s) (Hs s) (Hs (s - 1)) H X
    B p φ φw φv ρp ρw ρv hDiv hMono (hSync.mono hcut₁) (hCatch.mono hcut₁) (hRoots.mono hcut₁) hParent hOwner hs1
    hGST (fun v hv' t h1 h2 => hHon s le_rfl (by omega) v hv' t h1 h2 (by omega)) hp hPropose
    hHsPrev
    hVotersPrev hApX hLocksW hOnly hRootNew (hHs s le_rfl (by omega))
    (fun v hv' => (hVoters s le_rfl (by omega) v hv').2) hHalf hShapeP hShapeW hShapeV hFloorW
    hRootW hRootAr hHeadP
  -- step 2: the invariant through the round, from one slot's set to the next
  obtain ⟨hInv, hVotes⟩ := round_honestChainExtends_steps_upTo S Sched x GST s s₂ Hon Hs B hDiv hMono
    (hSync.mono hcut₂) (hCatch.mono hcut₂) (hRoots.mono hcut₂) hParent hOwner (by omega) (by omega) hHonMono hHon hHs
    hVoters hStep hStepLast hBase
  -- the next proposer is awake and honest from the duty window's start of slot `s` to `t_{s''}`
  have hqWin : ∀ t : ℕ, dutyWindowStart S s ≤ t → t ≤ slotStart S (s₂ + 2) →
      q ∈ Sched.awake (t : Int) ∧ q ∉ Sched.adv (t : Int) := by
    intro t h1 h2
    have hd : s + (s₂ + 1 - s) = s₂ + 1 := by omega
    have hsc := supportCutoff_le_slotStart_succ S (s₂ + 2)
    have hc2 : supportCutoff S (s₂ + 2) = voteTime S (s₂ + 2) + Δ S := hc (s₂ + 2)
    have hv2 : voteTime S (s₂ + 2) = slotStart S (s₂ + 2) + Δ S := hv (s₂ + 2)
    refine members_window_of_sets S Sched s (s₂ + 2) Hon hHonMono hHon (s₂ + 1 - s) (by omega) q
      (by rw [hd]; exact hq) t h1 (by rw [hd]; omega) h2
  -- step 3: the attestations in `q`'s pool
  obtain ⟨hPool, hPoolT⟩ := round_attestations_in_pool_upTo S Sched x GST r s (slotStart S (s₂ + 2))
    (dutyWindowStart S s) Q B q φv ρv hDiv hMono hSyncF hCatchF hs (by omega) ha hBslot
    (fun v hv' t h1 h2 => hHon s le_rfl (by omega) v (hQ hv') t (by omega) h2 (by omega))
    (fun v hv' => hUpd v (hQ hv')) (fun v hv' => hBase.2.1 v (hQ hv'))
    (fun v hv' => hShapeV v (hQ hv')) (fun v hv' => hRootAr v (hQ hv'))
    (fun v hv' => (stateBefore_grows x hDiv v (by omega)).1 (hHeld v (hQ hv'))) hLockBox
    (fun v hv' => hFloorV v (hQ hv')) (by omega) hqWin
  -- step 4: `q`'s proposal is on `B`'s chain
  have hss₂ : slotStart S (s₂ + 2) = slotStart S (s₂ + 1) + 4 * Δ S := hss (s₂ + 1)
  have hss₃ := hss s₂
  have hdw₂ : dutyWindowStart S (s₂ + 1) ≤ slotStart S s₂ := dutyWindowStart_succ_le_slotStart S s₂
  have hsc₂ := supportCutoff_le_slotStart_succ S (s₂ + 2)
  have hc₂ : supportCutoff S (s₂ + 2) = voteTime S (s₂ + 2) + Δ S := hc (s₂ + 2)
  have hv₂ : voteTime S (s₂ + 2) = slotStart S (s₂ + 2) + Δ S := hv (s₂ + 2)
  have hm3 := slotStart_le_of_le S (show s ≤ s₂ by omega)
  have hBB'p := round_proposal_extends_upTo S Sched x GST s₂ (Hon (s₂ + 1)) (Hs (s₂ + 1)) B B' q
    hDiv hMono hSync hCatch hRoots hParent hOwner (by rw [hv (s₂ + 1)]; omega)
    (honestChainExtends_mono S Sched x (Hon s₂) (Hon (s₂ + 1)) B s₂
      (hHonMono s₂ (by omega) (by omega)) hInv) hVotes hq
    (fun t h1 h2 => hHon (s₂ + 1) (by omega) (by omega) q hq t h1 (by omega) h2)
    (hHs (s₂ + 1) (by omega) (by omega))
    (fun u hu => (hHon (s₂ + 1) (by omega) (by omega) u hu _ (by omega) (by omega) le_rfl).2)
    hVotersQ hFrameQ hPropose'
  obtain ⟨i', hl', hsent'⟩ := id hPropose'
  obtain ⟨-, -, hB'par?, -⟩ := proposal_parent_walk_end S Sched x (s₂ + 1) i' B' q hl' hsent'
  have hB'p : B'.parent.AncestorEq B' := ancestorEq_of_parent? hB'par?
  have hBB' := ancestorEq_trans hBB'p hB'p
  -- step 5: the certificate
  have hd1 := (lem47_chain_state_heights S.C B B'.parent).2.2.2.1 hBB'p
  have hd2 := (lem47_chain_state_heights S.C B'.parent B').2.2.2.1 hB'p
  by_cases heq : (chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h
  · have hT : (chainStateOf S.C B'.parent).T_h = (chainStateOf S.C B).T_h :=
      ((lem47_chain_state_heights S.C B B'.parent).2.2.2.2 hBB'p heq.symm).symm
    have hPool' : ∀ u ∈ Q, ∃ a ∈ (stateBefore x (slotStart S (s₂ + 2)) q).S.attestations,
        a.val_index = u ∧ a.h = (chainStateOf S.C B'.parent).h ∧
        a.T = (chainStateOf S.C B'.parent).T_h.root := by
      rw [heq, hT]
      exact hPool
    obtain ⟨h53a, h53b⟩ := lem53_next_honest_proposal_carries_certificate S Sched x (s₂ + 2) q B'
      B'.parent Q hPropose' rfl hQuorum hPool'
    rw [heq, hT] at h53a h53b
    refine ⟨hBB', ?_, fun hFresh => ?_⟩
    · rcases h53a with h | h
      · exact Or.inl (by unfold Height at *; omega)
      · exact Or.inr h
    · obtain ⟨h1, h2⟩ := h53b (hPoolT hFresh)
      exact ⟨by unfold Height at *; omega, fun _ => h2⟩
  · have hlt : (chainStateOf S.C B).h < (chainStateOf S.C B'.parent).h := by
      unfold Height at *
      omega
    have hge : (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h := by
      unfold Height at *
      omega
    exact ⟨hBB', Or.inl hge, fun _ => ⟨hge, fun h => absurd h heq⟩⟩

end GoldilocksCorrectness.Proofs.Executions

