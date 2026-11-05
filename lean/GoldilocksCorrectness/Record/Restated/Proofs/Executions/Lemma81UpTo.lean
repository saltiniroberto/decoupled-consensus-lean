module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.NextSlotVoteStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ConfirmationCompatibilityStatementsUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.HonestChainStatementsUpTo
public import GoldilocksCorrectness.Statements.Executions.NextSlotVoteStatementsUpTo
public import GoldilocksCorrectness.Statements.Executions.ConfirmationCompatibilityStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma81UpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma81UpTo.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 81's chain step, Lemma 81 (b) and
the slot invariant it carries from slot to slot, with the delivery premises up to a bound. The
page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq slotStart_mono slot_eq_of_mem
  supportCutoff_cast supportCutoff_eq supportCutoff_lt_of_lt viewFreeze_cast viewFreeze_eq
  voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated CountedVotes
  CountedVotesAt EarlySupporterOf LocksRevoked TreeClosed VoterTree VoterTreeAt)

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
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  compatible_iff compatible_of_ancestorEq_compatible mem_voter_block_tree_iff)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **Lemma 21, the held form.** Lemma 21's conclusion, naming the block: `vote` is `w`'s
slot-`(s + 1)` vote for a block `H_w` of `w`'s tree at its tick to the vote time of slot `s + 1`, and
`H_w` is `B` or a descendant of `B`.

Why: Lemma 21's proof, keeping the walk's end. Lemma 14 gives the vote's validator and slot (the
validator of the tick's input state is `w`, Lemma 11) and the walk; its end is a block of the
viable tree of `w`'s voter tree or the walk's start, the anchor, which is in `w`'s tree
(`get_anchor_mem_T`); Lemma 64 puts it on `B`'s chain.

Read at the validators' own ticks (T-RC8-2, the shape Lemma 42 takes): `v` from `tStart` up to its
tick to the support cutoff of slot `s + 1`, `w` from `tStartW` up to its tick to the view freeze of
slot `s`, the holders `v` and `w` for the sync delay after the sync fact's read times,
the roots until the latest real time of `w`'s tick to the view freeze of slot `s` (T-R51's form).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `GST`: the time from which the network is
  synchronous; `s`: the slot of the eligibility;
- `Sup`: the early supporters; `B`: the eligible block; `v`: the validator finding it eligible;
  `w`: the voter of slot `s + 1`; `vote`: its Goldfish vote; `tStart`, `tStartW`: the starts of `v`'s
  and `w`'s windows.

Restated with the delivery premises up to `M.supportCutoff S.C (s + 1)`: Lemma 64 reads the votes
due one delay after the vote time of slot `s + 1`.

Read aloud: under Lemma 21's hypotheses read at the validators' ticks, with the delivery premises up to
the bound, `w`'s vote is its
slot-`(s + 1)` vote for a block `w` holds at its tick to that vote time that is `B` or a descendant of
`B`. -/
theorem lem21b_goldfish_vote_extends_eligible_block_held_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Sup : Finset V) (B : Block V) (v w : V)
    (vote : GoldfishVote V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- a root names one block among what honest validators hold, until the latest real time of `w`'s tick
    -- to the view freeze of slot `s`, the one receiver of a block (T-RC8-2, T-R42's form)
    (hRoots : RootsNameBlocksUntil M A x ((M.viewFreeze S.C s : ℝ) + ΔClockBehind))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s)
    -- `v`'s window starts at `tStart`, more than both clock bounds before the support cutoff of slot `s + 1`
    -- less six delays or one sync delay, whichever is longer
    (tStart : ℤ) (htStart :
      (tStart : ℝ) + ΔClockAhead + ΔClockBehind < ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ))
    -- `v` is active from `tStart` up to its tick to the support cutoff of slot `s + 1`
    (hv : v ∈ A.activeThroughoutToTick x tStart (M.supportCutoff S.C (s + 1)))
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    -- `w` is active from `tStartW` up to its tick to the view freeze of slot `s`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.viewFreeze S.C s))
    -- the holders: `v` active for the sync delay after the view freeze of slot `s` less one
    -- delay or one sync delay, whichever is longer; `w` for the sync delay after the support cutoff of
    -- slot `s + 1` less the same
    (hv₀ : v ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hSup : ∀ u ∈ Sup,
      EarlySupporterOf M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) s B u)
    (hEligible :
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
        2 * Sup.card)
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible B = true)
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
          (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧ B.AncestorEq W)
    (hLocks : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    ∃ H_w ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ B.AncestorEq H_w := by
  letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  -- the times
  have hΔ := one_le_Δ S
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hss2 : M.slotStart S.C (s + 2) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1), Nat.mul_add, Nat.mul_add]
    omega
  have hss' : M.slotStart S.C (s + 1 + 1) = M.slotStart S.C (s + 1) + 4 * Δ S := hss2
  have hv₃ : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hv₁ : M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hc : M.supportCutoff S.C s = M.voteTime S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have ht₂ : M.supportCutoff S.C (s + 1) = M.voteTime S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have hfr : M.viewFreeze S.C s = M.slotStart S.C s + 3 * Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hfr' : M.supportCutoff S.C s + Δ S = M.viewFreeze S.C s := by omega
  have ht₂' : M.voteTime S.C (s + 1) + Δ S = M.supportCutoff S.C (s + 1) := ht₂.symm
  have hm1 := le_max_left (Δ S) Δs
  have hm2 := le_max_right (Δ S) Δs
  have hm6 : max (6 * Δ S) Δs ≥ 6 * Δ S := le_max_left _ _
  have hm6' : max (6 * Δ S) Δs ≥ Δs := le_max_right _ _
  have hm3 : max (3 * Δ S) Δs ≥ 3 * Δ S := le_max_left _ _
  have hm3' : max (3 * Δ S) Δs ≥ Δs := le_max_right _ _
  have hslot₃ : S.C.slot ((M.voteTime S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
      (by omega) (by omega)
  -- `v`'s tick `k_v` to the support cutoff of slot `s + 1`, active from the support cutoff of slot `s` less
  -- `ΔClockAhead`
  have hslR : ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) ≤ (M.supportCutoff S.C s : ℝ) := by
    exact_mod_cast (show M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs ≤ M.supportCutoff S.C s by omega)
  obtain ⟨k_v, hk_v, hwinv⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv
    (t₀ := (M.supportCutoff S.C s : ℝ) - ΔClockAhead) (by linarith)
  have hk_vT := (E.tick_active k_v v _ hk_v).2.1
  have hcR : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = (M.supportCutoff S.C s : ℝ) + 4 * Δ S := by
    have : M.supportCutoff S.C (s + 1) = M.supportCutoff S.C s + 4 * Δ S := by omega
    rw [this]; push_cast; ring
  rw [hcR] at hk_vT
  -- `v`'s tick `kₑ` to the support cutoff of slot `s`
  obtain ⟨kₑ, hkₑ, -, -⟩ := E.tick_of_active (M.supportCutoff S.C s) (by omega) v fun j hj1 hj2 => by
    refine hwinv j hj1 ?_
    exact ((lt_of_time_lt M) x R (by linarith)).le
  -- `w`'s tick `k_f` to the view freeze of slot `s`
  have hslW : ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ) ≤ (M.viewFreeze S.C s : ℝ) := by
    exact_mod_cast Nat.sub_le _ _
  obtain ⟨k_f, hk_f, -⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hw
    (t₀ := (M.viewFreeze S.C s : ℝ)) (by linarith)
  -- `w`'s run and walk: Lemma 14 over the record, from the input state of its tick to the vote time of
  -- slot `s + 1` (`w` is active at that step, Lemma 11)
  obtain ⟨i, hl, hm⟩ := hSend
  have hTI : x.tickInput w (M.voteTime S.C (s + 1)) = x.st i w := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  obtain ⟨hact, n', sent, hrun, hvote⟩ := (tick_send_of_honestSendAt M F R E) hl hm
  have hInv11 := (lem11_node_invariant M F S A x R E i w) (Activity.not_mem_corrupted_of_mem_active hact)
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1))) := by
    rw [hTI]
    exact hInv11.1
  obtain ⟨-, hvi, hvs, -, hAwake, H_w, ⟨votes, support_votes, hCounted, hWalk⟩, hhead⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem14_tick_vote_walk F) S.C S.P S.X _ n' _ sent
      vote hrun hInvT hvote
  rw [hslot₃] at hvs hAwake hCounted hWalk
  rw [Nat.add_sub_cancel] at hWalk
  -- the vote is `w`'s slot-`(s + 1)` vote for `H_w` (the validator of the tick's input state is `w`)
  rw [hTI, hInv11.2.1] at hvi
  have hvote' : vote = GoldfishVote.mk w (s + 1) H_w.root := by
    rw [← hvi, ← hvs, ← hhead]
  -- the walk's end is a block `w` holds: a block of the viable part of the voter's tree, or the
  -- anchor, which is the fgroot (the justified or the finalized block) or a block of the viable tree
  have hHwT : H_w ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree := by
    have hmemT : ∀ D ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree,
        D ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree :=
      fun D hD => (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hD).1
    rcases GoldilocksCorrectness.Proofs.Routines.walkEnd_mem_tree_or_eq hWalk with h | h
    · rw [h]
      rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M
          (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries
          ((M.voteTime S.C (s + 1) : ℕ) : Int) with h' | h'
      · rw [h', (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F),
          F.ndAdded.get_fc_root_eq hInvT]
        split
        · exact F.nd.nodeInv_justifiedInTree hInvT
        · exact F.nd.nodeInv_finalized_mem_tree hInvT
      · exact hmemT _ (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1
          h').1
    · have h1 := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h).1
      exact hmemT _ ((GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _
        (s + 1) H_w).1 h1).1
  -- the spec's cutoffs are the reading points, cast; `w`'s voter's tree is the record's `VoterTree`,
  -- whose members are the blocks `VoterTreeAt` names
  have hCountedAt : CountedVotesAt M (x.tickInput w (M.voteTime S.C (s + 1)))
      ((M.viewFreeze S.C s : ℕ) : Int) (s + 1) votes support_votes := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_cast M.toSlotLayout F.sched U)]
    exact hCounted
  have hvbtAt : ∀ B' : Block V,
      B' ∈ VoterTree M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) ↔
        VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1))) ((M.viewFreeze S.C s : ℕ) : Int)
          (s + 1) B' := by
    intro B'
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_cast M.toSlotLayout F.sched U)]
    simp only [VoterTree, Finset.mem_filter, Nat.add_sub_cancel]
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  have hSupAt : ∀ u ∈ Sup, EarlySupporterAt M (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C s : ℕ) : Int) s B u := by
    intro u hu
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U)]
    exact hSup u hu
  have hF3' : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq B →
      ∃ W ∈ VoterTree M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1),
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧
          B.AncestorEq W := by
    intro hR
    obtain ⟨W, hW, hWv, hBW⟩ := hF3 hR
    refine ⟨W, ?_, hWv, hBW⟩
    simp only [VoterTree, Finset.mem_filter]
    exact ⟨hW.1, hW⟩
  -- Lemma 64 at the spec's times, with `t_e := c`, `t_f := freeze`, `t_w := t₃`, `t_v := t₂`; the anchor over
  -- the lock entries `n'` leaves (the lock clause of the vote time at the outcome `n'` of `w`'s tick)
  exact ⟨H_w, hHwT, hvote',
    (lem64_goldfish_vote_extends_eligible_block_at M F U) S A x R GST s (M.supportCutoff S.C s)
      (M.viewFreeze S.C s) (M.voteTime S.C (s + 1)) (M.supportCutoff S.C (s + 1))
      (M.supportCutoff S.C (s + 1)) Sup B v w n'.lockEntries votes support_votes
      (VoterTree M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1)) H_w
      E hNet hSkew hRedeliver Sy
      (by rw [hfr']; exact hRoots) hParent (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
      tStartW (by rw [hfr']; exact (lt_natSub_max_of_le (m := Δ S) (by omega) htStartW))
      (by
        have : ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ) ≤ (M.slotStart S.C s : ℝ) := by
          exact_mod_cast (show M.viewFreeze S.C s - max (3 * Δ S) Δs ≤ M.slotStart S.C s by omega)
        linarith)
      (by rw [hfr']; exact hw)
      tStart (by rw [ht₂']; exact (lt_natSub_max_of_le (m := Δ S) (by omega) htStart))
      (by
        have : ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) ≤ (M.slotStart S.C s : ℝ) := by
          exact_mod_cast (show M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs ≤ M.slotStart S.C s by omega)
        linarith)
      (by rw [ht₂']; exact hv)
      (by rw [hfr']; exact hv₀) (by rw [ht₂']; exact hw₀)
      kₑ hkₑ k_f hk_f i hl k_v hk_v hSupAt hEligible hCountedAt hvbtAt hWalk hF2 hF3'
      (fun e he hlive => hLocks n' sent hrun hAwake e he hlive) (by omega)⟩

/-- **Lemma 36b, a confirmed block is extended by the next slot's honest votes, the held form.**
The proof; the audited statement is in
`Statements/Executions/HonestChainAfterHealingStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot whose confirmation `v`'s update of slot `s + 1` saves;
- `C'`: the saved confirmation; `v`: the validator whose update saves it; `n'`: the node state that
  update leaves; `w`: the voter of slot `s + 1`; `vote`: its Goldfish vote.

Roots name blocks until `M.supportCutoff S.C (s + 1)`: Lemma 21b, which the proof calls, takes
blocks as held up to one delay after `w`'s vote time of slot `s + 1`.

Restated with the delivery premises up to `M.supportCutoff S.C (s + 1)`: Lemma 21b at slot `s` reads
deliveries due by then (`lem21b_goldfish_vote_extends_eligible_block_held_upTo`).

Read aloud: under Lemma 36a's hypotheses, `w`'s vote is its slot-`(s + 1)` vote for a block of its
own tree before that vote time that is `C'` or a descendant of `C'`, with the delivery premises up
to the bound. -/
theorem lem36b_confirmed_block_extended_held_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (C' : Block V) (v w : V) (n' : M.N)
    (vote : GoldfishVote V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s)
    -- `v`, awake and honest from the duty window's start of slot `s + 1` up to its tick to that
    -- slot's support cutoff
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    -- `w` is active from `tStartW` up to its tick to the view freeze of slot `s`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.viewFreeze S.C s))
    -- `w` is active for the sync delay after the support cutoff of slot `s + 1` less one delay or one sync
    -- delay, whichever is longer (the holder's window,: Lemma 21b reads `w` as a holder through
    -- Lemma 64)
    (hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hUpdate : ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n')
    (hSaved : n'.savedConfirmation s = some C')
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible C' = true)
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq C' →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
          (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧
          C'.AncestorEq W)
    (hLocks : ∀ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n'',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible C' = true)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    ∃ H_w ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ C'.AncestorEq H_w := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hs1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  obtain ⟨htStart, hv₀'⟩ := (lem21b_reads_of_dutyWindow M F U) S R E hSkew hΔs (le_of_add_le_right hGST) htStartW hv
  -- `v`'s tick `k_v` to the support cutoff of slot `s + 1`, active from that cutoff less `ΔClockAhead`
  have hslR : ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) ≤ (M.supportCutoff S.C (s + 1) : ℝ) := by
    exact_mod_cast Nat.sub_le _ _
  have hdle := (duty_window_start_le_real M F U) S (s + 1)
  obtain ⟨k_v, hk_v, hwinv⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv
    (t₀ := (M.supportCutoff S.C (s + 1) : ℝ) - ΔClockAhead) (by linarith)
  have hti_v : x.tickInput v (M.supportCutoff S.C (s + 1)) = x.st k_v v := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_v]
  have hRootsΦv : GoldilocksCorrectness.Statements.Routines.RootsNameBlocksIn
      (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree := by
    rw [hti_v]
    exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E _ v
  -- Lemma 36 at `C'` itself, on `v`'s pool at its tick to the support cutoff of slot `s + 1`
  obtain ⟨Sup, hSup, hElig, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem36_confirmed_ancestor_early_supporters F)
      C' C' hs1 hRootsΦv
      (by
        rw [Nat.add_sub_cancel, hti_v]
        exact (pool_vote_late_of_tick M F U) S A x R s v E k_v hk_v hwinv)
      hUpdate (by rw [Nat.add_sub_cancel]; exact hSaved) (GoldilocksCorrectness.Proofs.Routines.ancestorEq_refl C')
  simp only [Nat.add_sub_cancel] at hSup hElig
  -- the roots until the latest real time of `w`'s tick to the view freeze of slot `s`
  have hRoots' : RootsNameBlocksUntil M A x ((M.viewFreeze S.C s : ℝ) + ΔClockBehind) := by
    have hB0 := E.behind_nonneg
    have hA0 := E.ahead_nonneg
    have hss1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1)
    have hss0 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
    have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
    have hsc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
    have hfr := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
    refine (RootsNameBlocksUntil.mono M) ?_ hRoots
    have : (M.supportCutoff S.C (s + 1) : ℝ) = (M.viewFreeze S.C s : ℝ) + 3 * Δ S := by
      have h : M.supportCutoff S.C (s + 1) = M.viewFreeze S.C s + 3 * Δ S := by
        rw [hsc, hvt, hfr, hss1, hss0]; ring
      rw [h]; push_cast; ring
    rw [this]
    have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast one_le_Δ S
    linarith
  -- Lemma 21, the held form, at `C'`
  exact (lem21b_goldfish_vote_extends_eligible_block_held_upTo M F U) S A x R GST s Sup C' v w vote E hNet hSkew hRedeliver Sy hΔs hRoots' hParent
    hGST (duty_window_start S.C (s + 1)) htStart hv tStartW htStartW hw hv₀' hw₀ hSup hElig hF2 hF3 hLocks hSend

/-- **The updaters' confirmations extend the chain family.** In an execution where every time is
reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`,
a root names one block among what honest validators hold, a block
reaches a validator only once it holds the parent, and nobody votes in an honest validator's name:
if `GST` is at most the vote time of slot `s`; `Hon` is a set of honest active validators of slot
`s` with more than half of the committee of slot `s`; `ChainInvFor M S Sched x Hon 𝓒 s` holds; `v`
is an updater of slot `s`; and `v`'s finalized block before the support cutoff of slot `s + 1` is
compatible with every block of `𝓒` — then every block of `𝓒` is an ancestor of, or equal to, the
confirmation of slot `s` that `v` holds right after that cutoff.

Why: Lemma 78 at `v`, with the honest voters `S.P.committee s ∩ Hon`, each voting for a block it
holds on the block's chain (the first clause of the invariant), and the voters of `v`'s pool from
the committee (the node invariant).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot; `Hon`: the voters; `𝓒`: the family; `v`: the updater.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C s`: Lemma 78,
which the proof calls at slot `s`, reads them up to the real time of `v`'s own tick to that cutoff.

Restated with the delivery premises up to `M.supportCutoff S.C s`: Lemma 78 at slot `s` reads
deliveries due by then (`lem78_update_confirmation_extends_voter_majority_chain_upTo`).

Read aloud: every block of the family is an ancestor of, or equal to, the confirmation of slot `s`
an updater holds right after the support cutoff of slot `s + 1`, with the delivery premises up to
the bound. -/
theorem chainInvFor_updater_confirmation_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hon : Finset V) (𝓒 : Block V → Prop)
    (v : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHon : Hon ⊆ honestActiveAt M S A x s)
    (hCommittee : |S.P.committee s| < 2 * |S.P.committee s ∩ Hon|)
    (hInv : ChainInvFor M S A x Hon 𝓒 s)
    (hv : v ∈ updaterAt M S A x s)
    (hF : ∀ C : Block V, 𝓒 C →
      (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.compatible C = true) :
    ∀ C : Block V, 𝓒 C → ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C' →
      C.AncestorEq C' := by
  intro C hC
  -- the voters: the committee members of `Hon`, each voting for a block it holds on `C`'s chain
  obtain ⟨H, hH⟩ := (voters_of_votes_clause M F U) S A x R s (S.P.committee s ∩ Hon) C E hSkew
    (fun u hu => ⟨hHon (Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hu).1⟩)
    (fun u hu => (hInv C hC).1 u (Finset.mem_inter.1 hu).2)
  -- `v`'s tick to the support cutoff of slot `s` (inside its reader), for the roots
  obtain ⟨kR, hkR, -⟩ := (updater_reader_gives_core_window M F U) x R E hΔs hSkew hv
  -- each voter is awake and honest from the duty window's start of slot `s + 1` up to its tick to the support cutoff
  -- of slot `s + 1` (its reader of `activeAt`, moved later)
  have hUpdU : ∀ u ∈ S.P.committee s ∩ Hon, u ∈ updaterAt M S A x s := fun u hu =>
    Activity.mem_activeThroughoutToTick_of_le (GoldilocksCorrectness.Proofs.Routines.duty_window_start_mono S (Nat.le_succ s))
      (E.mem_activeThroughoutToTick_of_awakeThroughoutToTick
        (Finset.mem_sdiff.1 (hHon (Finset.mem_inter.1 hu).2)).1)
  exact (GoldilocksCorrectness.Record.Statements.Executions.lem78_update_confirmation_extends_voter_majority_chain_upTo M F U)
    S A x R GST s (S.P.committee s ∩ Hon) H C v E hNet hSkew hRedeliver Sy hΔs
    ((roots_at_own_tick_of_per_tick M F) x E hRoots hkR) hParent hOwner hGST
    (fun u hu => ⟨(Finset.mem_inter.1 hu).1,
      (not_mem_corrupted_tickStep_of_outside_at_honest_ticks M F) x E hv
        (fun hX => (Finset.mem_sdiff.1 (hHon (Finset.mem_inter.1 hu).2)).2 (Finset.mem_union_right _ hX)),
      (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
    (fun u hu => (holder_window_of_updater_reader M F U) x R E hΔs hSkew hGST (hUpdU u hu))
    (by
      unfold Trace.tickInput
      exact (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
        ((GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_exec M F) S A x R E _ v s)
        ((committee_sdiff_lt M F) _ _ hCommittee))
    hv (hF C hC)

/-- **The chain step.** The proof; the audited statement is in
`Statements/Executions/HonestChainAfterHealingStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s'`: the slot of the step;
- `Hon`: the voters of slot `s'`; `Hon'`: the members of slot `s' + 1`; `Upd`: the updaters whose
  confirmations of slot `s'` join the family; `𝓒`: the family.

Roots name blocks until `M.supportCutoff S.C (s' + 1)`, where Lemma 36b reads them, and up to every
validator's tick to a clock value at most that cutoff: Lemmas 78 and
32 read them up to the updaters' own ticks to the cutoff, which can come after its real time; Lemma 26b
reads them up to the voter's tick to the support cutoff of slot `s'`.

Restated with the delivery premises up to `M.supportCutoff S.C (s' + 1)`: Lemmas 36b and 78, which
the proof calls at the slots `s'` and `s' + 1`, read deliveries due by then; Lemmas 26b and 32 read
earlier.

Read aloud: the honest chain grows by the confirmations of slot `s'`: when the voters of slot `s'`
satisfy the invariant for every block of the family and their live locks are on its chain, the
members of slot `s' + 1` satisfy it for every block of the family and every block of a new
confirmation's chain, with the delivery premises up to the bound. -/
theorem lem89s_chain_step_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s' : ℕ) (Hon Hon' Upd : Finset V)
    (𝓒 : Block V → Prop)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s' + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s' + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s' + 1)))
    -- roots name blocks also up to every validator's tick to a clock value at most the support cutoff of slot `s' + 1`
    -- ('s shape: Lemmas 78 and 32 read them up to the updaters' own ticks to that cutoff)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s')
    (hHon : Hon ⊆ honestActiveAt M S A x s')
    (hHon' : Hon' ⊆ honestActiveAt M S A x (s' + 1))
    (hUpd : Upd ⊆ updaterAt M S A x s')
    (hHonUpd : Hon' ⊆ Upd)
    (hCommittee : |S.P.committee s'| < 2 * |S.P.committee s' ∩ Hon|)
    (hCommittee' : |S.P.committee (s' + 1)| < 2 * |S.P.committee (s' + 1) ∩ Hon'|)
    (hInv : ChainInvFor M S A x Hon 𝓒 s')
    (hNew : ∀ u ∈ Hon', u ∈ Hon ∨
      ∀ e ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).lockEntries,
        M.is_live (x.tickInput u (M.voteTime S.C (s' + 1)))
          ((M.voteTime S.C (s' + 1) : ℕ) : Int) e = false)
    (hLocks : ∀ u ∈ Hon, LiveLocksOnFamilyAt M S A x 𝓒 s' u)
    (hConfExt : ∀ C : Block V, 𝓒 C → ∀ v ∈ Upd, ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' →
      C.AncestorEq C')
    (hStep : ∀ C : Block V, (𝓒 C ∨ ∃ v ∈ Upd,
        (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C) →
      ∀ w ∈ Hon', StepFrameAt M S A x C s' w) :
    ChainInvFor M S A x Hon' (fun C => 𝓒 C ∨ ∃ v ∈ Upd, ∃ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' ∧
      C.AncestorEq C') (s' + 1) := by
  -- the blocks of the family and the new confirmations themselves; their ancestors follow
  suffices hcore : ∀ B : Block V, (𝓒 B ∨ ∃ v ∈ Upd,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some B) →
      HonestChainExtends M S A x Hon' B (s' + 1) by
    rintro B (hB | ⟨v, hv, C', hsv, hBC'⟩)
    · exact hcore B (Or.inl hB)
    · exact (honestChainExtends_of_ancestorEq M F) S A x Hon' C' B (s' + 1) hBC'
        (hcore C' (Or.inr ⟨v, hv, hsv⟩))
  intro B hB0
  have hB : 𝓒 B ∨ ∃ v ∈ Upd, ∃ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' ∧
      B.AncestorEq C' :=
    hB0.imp id (fun ⟨v, hv, hsv⟩ => ⟨v, hv, B, hsv, ancestorEq_refl B⟩)
  -- the times, as reals
  have hA0 := E.ahead_nonneg
  have hB0' := E.behind_nonneg
  obtain ⟨hv0, hc0, hf0, hs0, -, hk8, hΔ⟩ := (slot_times M F U) S s'
  obtain ⟨hv1, hc1, -, hs1, -, -, -⟩ := (slot_times M F U) S (s' + 1)
  obtain ⟨hv2, hc2, -, -, -, -, -⟩ := (slot_times M F U) S (s' + 1 + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s'
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hc0R : ((M.supportCutoff S.C s' : ℕ) : ℝ) = 4 * Δ S * s' + 2 * Δ S := by
    rw [hc0, hss]; push_cast; ring
  have hf0R : ((M.viewFreeze S.C s' : ℕ) : ℝ) = 4 * Δ S * s' + 3 * Δ S := by
    rw [hf0, hss]; push_cast; ring
  have hv1R : ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 5 * Δ S := by
    rw [hv1, hs0, hss]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 6 * Δ S := by
    rw [hc1, hs0, hss]; push_cast; ring
  have hv2R : ((M.voteTime S.C (s' + 1 + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 9 * Δ S := by
    rw [hv2, hs1, hs0, hss]; push_cast; ring
  have hc2R : ((M.supportCutoff S.C (s' + 1 + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 10 * Δ S := by
    rw [hc2, hs1, hs0, hss]; push_cast; ring
  have hcc0 : M.supportCutoff S.C s' ≤ M.supportCutoff S.C (s' + 1) := by omega
  have hcc32 : M.supportCutoff S.C s' + Δ S ≤ M.supportCutoff S.C (s' + 1) := by omega
  have hdw1 := duty_window_start_real S (s' + 1)
  push_cast at hdw1
  have hdw2 := duty_window_start_real S (s' + 1 + 1)
  push_cast at hdw2
  have hdle2 := (duty_window_start_le_real M F U) S (s' + 1 + 1)
  have hdN2 : M.dutyWindowStart S.C (s' + 1 + 1) ≤ M.slotStart S.C (s' + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S (s' + 1)
  have hdN2R : ((M.dutyWindowStart S.C (s' + 1 + 1) : ℕ) : ℝ) ≤ 4 * Δ S * s' + 4 * Δ S := by
    have : ((M.dutyWindowStart S.C (s' + 1 + 1) : ℕ) : ℝ) ≤ ((M.slotStart S.C (s' + 1) : ℕ) : ℝ) := by
      exact_mod_cast hdN2
    rw [hs0, hss] at this; push_cast at this; linarith
  have hmΔ : (Δ S : ℝ) ≤ (max (Δ S) Δs : ℝ) := le_max_left _ _
  have hmΔs : (Δs : ℝ) ≤ (max (Δ S) Δs : ℝ) := le_max_right _ _
  -- `hGST` bounds the sync delay by the support cutoff of slot `s'`
  have hΔsle : Δs ≤ M.supportCutoff S.C s' := by have := le_max_right (Δ S) Δs; omega
  have hΔsleR : (Δs : ℝ) ≤ 4 * Δ S * s' + 2 * Δ S := by
    rw [← hc0R]; exact_mod_cast hΔsle
  have hmax1 : max (Δ S) Δs ≤ M.supportCutoff S.C (s' + 1) := by
    have := le_max_right (Δ S) Δs; have := le_max_left (Δ S) Δs
    rcases max_choice (Δ S) Δs with h | h <;> rw [h] <;> omega
  have hmaxR : ((max (Δ S) Δs : ℕ) : ℝ) = (max (Δ S) Δs : ℝ) := by push_cast; rfl
  -- the windows
  have hHonW : ∀ u ∈ Hon, u ∈ A.activeThroughoutToTick x (duty_window_start S.C s')
      (M.supportCutoff S.C (s' + 1)) := fun u hu => (honestActiveAt_window M F) S A s' u E (hHon hu)
  have hHon'W : ∀ u ∈ Hon', u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s' + 1))
      (M.supportCutoff S.C (s' + 1 + 1)) := fun u hu => (honestActiveAt_window M F) S A (s' + 1) u E (hHon' hu)
  have hHonU : ∀ u ∈ Hon, u ∈ updaterAt M S A x s' := fun u hu =>
    Activity.mem_activeThroughoutToTick_of_le (GoldilocksCorrectness.Proofs.Routines.duty_window_start_mono S (Nat.le_succ s')) (hHonW u hu)
  have hHon'U : ∀ u ∈ Hon', u ∈ updaterAt M S A x (s' + 1) := fun u hu =>
    Activity.mem_activeThroughoutToTick_of_le (GoldilocksCorrectness.Proofs.Routines.duty_window_start_mono S (Nat.le_succ (s' + 1))) (hHon'W u hu)
  have hRootsN : ∀ {k : ℕ} {u : V} {c : ℕ}, x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time (x.tickStep u c)) := fun {k u c} hk hc => by
    rw [(tickStep_eq_of_lbl M) x E hk]; exact hRootsTick k u c hk hc
  -- the live locks of a member after its revocation of slot `s' + 1`
  have hLk : ∀ u ∈ Hon', ∀ (n₃ : M.N) (sent₃ : List (NamedObject V)),
      .ok (n₃, sent₃) ∈ M.tick S.C S.P S.X (x.tickInput u (M.voteTime S.C (s' + 1)))
        ((M.voteTime S.C (s' + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput u (M.voteTime S.C (s' + 1))) (s' + 1) →
      ∀ e ∈ M.lockEntries n₃,
        M.is_live (x.tickInput u (M.voteTime S.C (s' + 1)))
          ((M.voteTime S.C (s' + 1) : ℕ) : Int) e = true →
        (∀ C : Block V, 𝓒 C → e.B.compatible C = true) ∧ ∃ D : Block V, 𝓒 D ∧ e.B.AncestorEq D := by
    intro u hu n₃ sent₃ hR hA e he hl
    rcases hNew u hu with hu0 | hfree
    · exact ⟨fun C hC => (hInv C hC).2.1 u hu0 n₃ sent₃ hR hA e he hl,
        hLocks u hu0 n₃ sent₃ hR hA e he hl⟩
    · exact ((revoke_locks_empty_of_lockFree M F) S A x _ (s' + 1) _ n₃ (Nat.le_add_left 1 s')
        hfree ((locksRevoked_of_voteTime_outcome M F U) S A x R E (s' + 1) u n₃ sent₃ hR hA) e
        he).elim
  -- the first clause at slot `s' + 1`
  have hClause1 : ∀ u ∈ Hon', ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).tree,
        vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ B.AncestorEq H_u := by
    intro u hu vote hSend
    obtain ⟨iS, hiS, -⟩ := id hSend
    have hF := hStep B hB0 u hu
    rcases hB with hBold | ⟨v, hv, C', hsv, hBC'⟩
    · -- a block of the family: Lemma 26b over the voters of slot `s'`
      obtain ⟨H, hH⟩ := (voters_of_votes_clause M F U) S A x R s' (S.P.committee s' ∩ Hon) B E hSkew
        (fun u' hu' => ⟨hHon (Finset.mem_inter.1 hu').2, (Finset.mem_inter.1 hu').1⟩)
        (fun u' hu' => (hInv B hBold).1 u' (Finset.mem_inter.1 hu').2)
      obtain ⟨kR, hkR, hkRw⟩ := (updater_reader_gives_core_window M F U) x R E hΔs hSkew
        (hUpd (hHonUpd hu))
      exact (GoldilocksCorrectness.Record.Statements.Executions.lem26b_goldfish_vote_extends_voter_majority_block_held_upTo M F U)
        S A x R GST s' (S.P.committee s' ∩ Hon) H B u vote (E.mono hcc0) hNet hSkew hRedeliver (Sy.mono hcc0) hΔs
        (hRootsN hkR (by omega)) hParent hOwner hGST
        (fun u' hu' => ⟨(Finset.mem_inter.1 hu').1,
          (not_mem_corrupted_tickStep_of_outside_at_honest_ticks_of_lbl M F) x E hiS
            ((outside_at_honest_ticks_of_mem_activeThroughoutToTick M F) x R E
              (hHonW u' (Finset.mem_inter.1 hu').2) (by rw [hv1R, hc1R]; linarith)),
          (hH u' hu').1, (hH u' hu').2.1, (hH u' hu').2.2⟩)
        (fun votes sv hC => by
          unfold Trace.tickInput at hC
          exact (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
            ((countedVotes_committee_st M F) S A x R E _ s' u votes sv hC) ((committee_sdiff_lt M F) _ _ hCommittee))
        (fun u' hu' => (holder_window_of_updater_reader M F U) x R E hΔs hSkew hGST
          (hHonU u' (Finset.mem_inter.1 hu').2))
        ⟨kR, hkR, hkRw⟩ hF.1 hF.2.1
        (fun n₃ sent₃ hR hA e he hl => (hLk u hu n₃ sent₃ hR hA e he hl).1 B hBold) hSend
    · -- a block of a new confirmation: Lemma 36b at that confirmation
      obtain ⟨n'', sent'', hrun'', hAw'', hsave⟩ :=
        (update_of_saved_confirmation_of_updater M F U) S A x R s' v C' E (hUpd hv) hsv
      have hUp := (confirmationUpdated_of_cutoff_tickInput M F U) x R s' v n'' sent'' hrun'' hAw''
      have hFC' := hStep C' (Or.inr ⟨v, hv, hsv⟩) u hu
      have hwVF : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s' + 1)) (M.viewFreeze S.C s') :=
        (mem_activeThroughoutToTick_of_inside M F) R E (hHon'W u hu) (by omega)
          (by rw [hdw1, hf0R]; linarith) (by rw [hf0R, hc2R]; linarith)
      have hw₀ : u ∈ A.activeThroughout x ((M.supportCutoff S.C (s' + 1) - max (Δ S) Δs : ℕ) : ℝ)
          (((M.supportCutoff S.C (s' + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
        have h := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E (hHon'W u hu)
          (a' := M.supportCutoff S.C (s' + 1) - max (Δ S) Δs)
          (e := M.supportCutoff S.C (s' + 1) - max (Δ S) Δs + Δs)
          (by rw [hdw1, Nat.cast_sub hmax1, hmaxR, hc1R]; linarith)
          (by
            have hle : M.supportCutoff S.C (s' + 1) - max (Δ S) Δs + Δs ≤ M.supportCutoff S.C (s' + 1) := by
              have := le_max_right (Δ S) Δs; omega
            have hleR : ((M.supportCutoff S.C (s' + 1) - max (Δ S) Δs + Δs : ℕ) : ℝ) ≤
                ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) := by exact_mod_cast hle
            rw [hc1R] at hleR; rw [hc2R]; linarith)
        push_cast at h
        exact h
      obtain ⟨H_u, hHT, hvt, hCH⟩ := (lem36b_confirmed_block_extended_held_upTo M F U) S A x R GST s' C' v u
        n'' vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent (by omega) (hUpd hv)
        (duty_window_start S.C (s' + 1))
        (by
          have h3 : max (3 * Δ S) Δs ≤ M.viewFreeze S.C s' := by
            rcases max_choice (3 * Δ S) Δs with h | h <;> rw [h] <;> omega
          rw [Nat.cast_sub h3, hdw1, hf0R]
          rcases max_choice (3 * Δ S) Δs with h | h <;> rw [h] <;> push_cast
          · linarith
          · linarith)
        hwVF hw₀ hUp hsave hFC'.1 hFC'.2.1
        (fun n₃ sent₃ hR hA e he hl => by
          obtain ⟨D, hD, heD⟩ := (hLk u hu n₃ sent₃ hR hA e he hl).2
          exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans heD (hConfExt D hD v hv C' hsv))))
        hSend
      exact ⟨H_u, hHT, hvt, ancestorEq_trans hBC' hCH⟩
  -- the second clause at slot `s' + 1`
  have hrefl : ∀ X : Block V, X.compatible X = true :=
    fun X => (compatible_iff _ _).2 (Or.inl (ancestorEq_refl X))
  have hClause2 : ∀ w ∈ Hon', ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s' + 1 + 1)))
        ((M.voteTime S.C (s' + 1 + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s' + 1 + 1))) (s' + 1 + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s' + 1 + 1)))
          ((M.voteTime S.C (s' + 1 + 1) : ℕ) : Int) e = true → e.B.compatible B = true := by
    intro w hw n' sent hrun hA e he _
    have hR := (locksRevoked_of_voteTime_outcome M F U) S A x R E (s' + 1 + 1) w n' sent hrun hA
    -- `w` is active from the duty window's start of slot `s' + 2` up to its tick to that slot's vote time
    have hwV : w ∈ A.activeThroughoutToTick x (M.dutyWindowStart S.C (s' + 1 + 1) : ℤ) (M.voteTime S.C (s' + 1 + 1)) := by
      have h1 := (mem_activeThroughoutToTick_of_inside M F) R E (hHon'W w hw) (c := M.voteTime S.C (s' + 1 + 1))
        (by omega) (by rw [hdw1, hv2R]; linarith) (by rw [hv2R, hc2R]; linarith)
      refine Activity.mem_activeThroughoutToTick_of_le ?_ h1
      have : ((duty_window_start S.C (s' + 1) : ℤ) : ℝ) ≤ ((M.dutyWindowStart S.C (s' + 1 + 1) : ℕ) : ℝ) := by
        rw [hdw1]; rw [hdw2] at hdle2; linarith
      exact_mod_cast this
    rcases (revoked_lock_source M F U) S A x R s' w E hSkew hwV n' hR e he with
        ⟨Cw, hCw, heC⟩ | ⟨n₃, sent₃, hR₃, hA₃, e', he', hl', hee'⟩
    · rcases hB with hBold | ⟨v, hv, C', hsv, hBC'⟩
      · exact compatible_of_ancestorEq_both heC (hConfExt B hBold w (hHonUpd hw) Cw hCw)
          (hrefl Cw)
      · have hw1 := hUpd (hHonUpd hw)
        have hv1' := hUpd hv
        obtain ⟨kw, hkw, -⟩ := Activity.mem_activeThroughoutToTick.1 hw1
        obtain ⟨kv, hkv, -⟩ := Activity.mem_activeThroughoutToTick.1 hv1'
        have h32 := (GoldilocksCorrectness.Record.Statements.Executions.lem32_saved_confirmations_compatible_state_upTo M F U)
          S A x R GST s' w v Cw C' (E.mono hcc32) hNet hSkew hRedeliver (Sy.mono hcc32) hΔs
          (by
            rcases max_choice (x.time (x.tickStep w (M.supportCutoff S.C (s' + 1))))
                (x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)))) with h | h <;> rw [h]
            · exact hRootsN hkw le_rfl
            · exact hRootsN hkv le_rfl)
          (by omega) hw1 hv1' hCw hsv
        exact compatible_of_ancestorEq_both heC hBC' h32
    · obtain ⟨hcomp, D, hD, he'D⟩ := hLk w hw n₃ sent₃ hR₃ hA₃ e' he' hl'
      rcases hB with hBold | ⟨v, hv, C', hsv, hBC'⟩
      · exact compatible_of_ancestorEq_compatible hee' (hcomp B hBold)
      · exact compatible_of_ancestorEq_both
          (ancestorEq_trans hee' (ancestorEq_trans he'D (hConfExt D hD v hv C' hsv))) hBC'
          (hrefl C')
  -- the third clause at slot `s' + 1`
  have hClause3 : ∀ v ∈ Hon', ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1 + 1))).savedConfirmation (s' + 1) = some C' →
      B.AncestorEq C' := by
    intro v hv
    obtain ⟨H, hH⟩ := (voters_of_votes_clause M F U) S A x R (s' + 1) (S.P.committee (s' + 1) ∩ Hon') B
      E hSkew
      (fun u hu => ⟨hHon' (Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hu).1⟩)
      (fun u hu => hClause1 u (Finset.mem_inter.1 hu).2)
    obtain ⟨kv, hkv, -⟩ := Activity.mem_activeThroughoutToTick.1 (hUpd (hHonUpd hv))
    exact (GoldilocksCorrectness.Record.Statements.Executions.lem78_update_confirmation_extends_voter_majority_chain_upTo M F U)
      S A x R GST (s' + 1) (S.P.committee (s' + 1) ∩ Hon') H B v E hNet hSkew hRedeliver Sy hΔs
      (hRootsN hkv le_rfl) hParent hOwner (by omega)
      (fun u hu => ⟨(Finset.mem_inter.1 hu).1,
        (not_mem_corrupted_tickStep_of_outside_at_honest_ticks M F) x E (hHon'W v hv)
          (fun hX => (Finset.mem_sdiff.1 (hHon' (Finset.mem_inter.1 hu).2)).2 (Finset.mem_union_right _ hX)),
        (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
      (fun u hu => (holder_window_of_updater_reader M F U) x R E hΔs hSkew (GST := GST) (by omega)
        (hHon'U u (Finset.mem_inter.1 hu).2))
      (by
        unfold Trace.tickInput
        exact (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
          ((GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_exec M F) S A x R E _ v (s' + 1))
          ((committee_sdiff_lt M F) _ _ hCommittee'))
      (hHon'U v hv) (hStep B hB0 v hv).2.2
  exact ⟨hClause1, hClause2, hClause3⟩

/-- **Lemma 81b, the chain step after the healed slot.** The proof; the audited statement is in
`Statements/Executions/HonestChainAfterHealingStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the first slot of the chain; `s`: the slot of the step;
  `anchor`: the time from which committee sleepiness holds.

Roots name blocks until `M.supportCutoff S.C (s + 1)`, and up to every validator's tick to a clock value
at most that cutoff (`hRootsTick`): the chain step, which the proof calls at slot `s`, reads both.

Restated with the delivery premises up to `M.supportCutoff S.C (s + 1)`: the chain step at slot `s`
reads deliveries due by then (`lem89s_chain_step_upTo`).

Read aloud: `Inv s` and the lock invariant at slot `s` give `Inv (s + 1)`, with the delivery
premises up to the bound. -/
theorem lem81b_chain_step_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ s anchor : ℕ)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    -- roots name blocks also up to every validator's tick to a clock value at most the support cutoff of slot `s + 1`
    -- ('s shape: Lemmas 78 and 32 read them up to the updaters' own ticks to that cutoff)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hs₀ : s₀ ≤ s)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 2)))
    (hAnchor : anchor ≤ M.slotStart S.C (s + 1))
    (hInv : ChainInvFor M S A x (honestActiveAt M S A x s)
      (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hVoterFrame : ∀ w ∈ honestActiveAt M S A x (s + 1),
      VoterFrameOnChainAt M S A x s₀ (s + 1) w)
    (hUpdaterFrame : ∀ v ∈ updaterAt M S A x s, UpdaterFinalizedOnChainAt M S A x s₀ s v)
    (hUpdaterFrame' : ∀ w ∈ honestActiveAt M S A x (s + 1),
      UpdaterFinalizedOnChainAt M S A x s₀ (s + 1) w) :
    ChainInvFor M S A x (honestActiveAt M S A x (s + 1))
      (OnHonestChainBefore M S A x s₀ (s + 1)) (s + 1) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨hv0, hc0, -, hs0, -, hk8, hΔ⟩ := (slot_times M F U) S s
  obtain ⟨hv1, hc1, -, hs1, -, -, -⟩ := (slot_times M F U) S (s + 1)
  obtain ⟨-, hc2, -, -, -, -, -⟩ := (slot_times M F U) S (s + 1 + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hcs : M.supportCutoff S.C s ≤ M.supportCutoff S.C (s + 1) := by omega
  have hc0R : ((M.supportCutoff S.C s : ℕ) : ℝ) = 4 * Δ S * s + 2 * Δ S := by
    rw [hc0, hss]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 6 * Δ S := by
    rw [hc1, hs0, hss]; push_cast; ring
  have hv1R : ((M.voteTime S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 5 * Δ S := by
    rw [hv1, hs0, hss]; push_cast; ring
  have hc2R : ((M.supportCutoff S.C (s + 1 + 1) : ℕ) : ℝ) = 4 * Δ S * s + 10 * Δ S := by
    rw [hc2, hs1, hs0, hss]; push_cast; ring
  have hdw1 := duty_window_start_real S (s + 1)
  push_cast at hdw1
  have hCom := (committee_majority_of_sleepiness M F) S A x anchor s hSleepK hAnchor
    ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))
  have hCom' := (committee_majority_of_sleepiness M F) S A x anchor (s + 1) hSleepK
    (le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (Nat.le_succ (s + 1)))) le_rfl
  -- every member of slot `s + 1` ticks to the vote time of slot `s + 1`, inside its reader ( reads
  -- `VoterFrameOnChainAt` at that tick)
  have hVT : ∀ w ∈ honestActiveAt M S A x (s + 1), ∃ k : ℕ, x.lbl k = Event.tick w (M.voteTime S.C (s + 1)) := by
    intro w hw
    have h1 : 1 ≤ M.voteTime S.C (s + 1) := by omega
    have hr := (mem_activeThroughoutToTick_of_inside M F) R E ((honestActiveAt_window M F) S A (s + 1) w E hw) h1
      (by rw [hdw1, hv1R]; linarith) (by rw [hv1R, hc2R]; linarith)
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hr
    exact ⟨k, hk⟩
  have hstep := (lem89s_chain_step_upTo M F U) S A x R GST s (honestActiveAt M S A x s)
    (honestActiveAt M S A x (s + 1)) (updaterAt M S A x s) (OnHonestChainBefore M S A x s₀ s)
    E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hOwner hGST (subset_refl _) (subset_refl _)
    (subset_refl _) ((honestActiveAt_succ_subset_updaterAt M F U) S A s R E hSkew) hCom hCom' hInv
    (fun u hu => (mem_honestActiveAt_or_lockFree M F U) S A s u R E hSkew hu)
    hLocks
    (fun C hC v hv => (chainInvFor_updater_confirmation_upTo M F U) S A x R GST s (honestActiveAt M S A x s)
      (OnHonestChainBefore M S A x s₀ s) v (E.mono hcs) hNet hSkew hRedeliver (Sy.mono hcs) hΔs
      ((per_tick_roots_of_roots_until M F) x E hRoots (c₀ := M.supportCutoff S.C s)
        (by rw [hc0R]; push_cast; rw [hc1R]; linarith))
      hParent hOwner hGST (subset_refl _) hCom hInv hv (fun D hD => hUpdaterFrame v hv D hD) C hC)
    (fun C hC w hw => by
      have hC' : OnHonestChainBefore M S A x s₀ (s + 1) C := by
        rcases hC with ⟨s', hs', hAt⟩ | ⟨v, hv, hsv⟩
        · exact ⟨s', by omega, hAt⟩
        · exact ⟨s, by omega, hs₀, v, hv, C, hsv, ancestorEq_refl C⟩
      obtain ⟨k, hk⟩ := hVT w hw
      have hti : x.tickInput w (M.voteTime S.C (s + 1)) = x.st k w := by
        unfold Trace.tickInput
        rw [(tickStep_eq_of_lbl M) x E hk]
      have hVF := hVoterFrame w hw C hC' k hk
      rw [← hti] at hVF
      exact ⟨hVF.1, hVF.2, hUpdaterFrame' w hw C hC'⟩)
  intro B hB
  apply hstep B
  obtain ⟨s', hs', hAt⟩ := hB
  rcases Nat.lt_or_ge s' s with hlt | hge
  · exact Or.inl ⟨s', hlt, hAt⟩
  · have hss' : s' = s := by omega
    subst hss'
    obtain ⟨-, v, hv, C', hsv, hBC'⟩ := hAt
    exact Or.inr ⟨v, hv, C', hsv, hBC'⟩

/-- **Lemma 81's induction before a slot.** The proof; the audited statement is in
`Statements/Executions/HonestChainAfterHealingStatements.lean`. The induction of
`lem81_confirmations_chain`'s proof, stopped before the slot `n`: the frames are read only at the
slots `s` with `s₀ < s < n`, and the conclusion is for those slots.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `n`: the bound on the slots; `B₀`: the block every updater of slot `s₀`
  saved.

Roots name blocks until `M.supportCutoff S.C (n - 1)`: the conclusion at a slot `s` reads the chain
step at slot `s - 1` (`lem89s_chain_step` at `s₀`, then `lem81b_chain_step`), which takes blocks
as held up to `M.supportCutoff S.C s`, and `s ≤ n - 1`.

Restated with the delivery premises up to `M.supportCutoff S.C (n - 1)`: the conclusion at a slot
`s ≤ n − 1` reads the chain step at slot `s − 1`, whose deliveries are due by
`M.supportCutoff S.C s`.

Read aloud: from the healed slot on and before slot `n`, every honest vote, live lock and
confirmation extends the chain so far, provided roots name blocks up to the support cutoff of slot
`n − 1` and `VoterFrameOnChainAt`, `UpdaterFinalizedOnChainAt` hold at the slots before `n`, with
the delivery premises up to the bound. -/
theorem lem81_inv_before_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor n : ℕ) (B₀ : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (n - 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (n - 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (n - 1)))
    -- roots name blocks also up to the real time of every validator's tick to a clock value at most the
    -- support cutoff of slot `n − 1`
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (n - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C n))
    (hAnchor : anchor ≤ M.slotStart S.C (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt M S A x s₀,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀)
    (hVoterFrame : ∀ s : ℕ, s₀ < s → s < n → ∀ w ∈ honestActiveAt M S A x s,
      VoterFrameOnChainAt M S A x s₀ s w)
    (hUpdaterFrame : ∀ s : ℕ, s₀ < s → s < n → ∀ v ∈ updaterAt M S A x s,
      UpdaterFinalizedOnChainAt M S A x s₀ s v) :
    ∀ s : ℕ, s₀ < s → s < n →
      ChainInvFor M S A x (honestActiveAt M S A x s)
        (OnHonestChainBefore M S A x s₀ s) s ∧
      ∀ u ∈ honestActiveAt M S A x s,
        LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u := by
  -- nothing to show unless a slot lies strictly between `s₀` and `n`
  by_cases hn₀ : s₀ + 1 < n
  swap
  · intro s h1 h2; omega
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  -- the support cutoff grows with the slot
  have hcm : ∀ a b : ℕ, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun a b h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  -- the two roots rows at the support cutoff of slot `s + 1`, for every `s + 1 ≤ n − 1`
  have hRootsS : ∀ s : ℕ, s + 1 ≤ n - 1 → RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)) := fun s hs =>
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by exact_mod_cast hcm _ _ hs) hRoots
  have hRootsTickS : ∀ s : ℕ, s + 1 ≤ n - 1 → ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c →
      c ≤ M.supportCutoff S.C (s + 1) → RootsNameBlocksUntil M A x (x.time k) := fun s hs k u c hk hc =>
    hRootsTick k u c hk (le_trans hc (hcm _ _ hs))
  -- the times and the counting
  have hΔ := one_le_Δ S
  have hGSTs : ∀ s : ℕ, s₀ ≤ s → GST + max (Δ S) Δs ≤ M.supportCutoff S.C s := fun s hs =>
    le_trans hGST (hcm _ _ hs)
  have hAnch : ∀ s : ℕ, s₀ ≤ s → anchor ≤ M.slotStart S.C (s + 1) :=
    fun s hs => le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  have hCom : ∀ s : ℕ, s₀ ≤ s → s < n →
      |S.P.committee s| < 2 * |S.P.committee s ∩ honestActiveAt M S A x s| :=
    fun s hs hsn => (committee_majority_of_sleepiness M F) S A x anchor s hSleepK (hAnch s hs) (hcm _ _ (by omega))
  have hNewAt : ∀ s : ℕ, ∀ u ∈ honestActiveAt M S A x (s + 1), u ∈ honestActiveAt M S A x s ∨
      ∀ e ∈ (x.tickInput u (M.voteTime S.C (s + 1))).lockEntries,
        M.is_live (x.tickInput u (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = false :=
    fun s u hu => (mem_honestActiveAt_or_lockFree M F U) S A s u R E hSkew hu
  -- `B₀` is on the chain at slot `s₀`
  obtain ⟨u₀, hu₀⟩ : (S.P.committee s₀ ∩ honestActiveAt M S A x s₀).Nonempty :=
    Finset.card_pos.1 (by have := hCom s₀ le_rfl (by omega); omega)
  have hv₀ : u₀ ∈ updaterAt M S A x s₀ :=
    (honestActiveAt_subset_updaterAt M F) S A x R E s₀ (Finset.mem_inter.1 hu₀).2
  have hB₀chain : ∀ C : Block V, C.AncestorEq B₀ → OnHonestChainBefore M S A x s₀ (s₀ + 1) C :=
    fun C hC => ⟨s₀, Nat.lt_succ_self s₀, le_rfl, u₀, hv₀, B₀, hBaseSaved u₀ hv₀, hC⟩
  -- the invariants at the healed slot
  have hBaseInv : ChainInvFor M S A x (honestActiveAt M S A x s₀) (fun D => D.AncestorEq B₀) s₀ :=
    fun C hC => (honestChainExtends_of_ancestorEq M F) S A x _ B₀ C s₀ hC hBase
  have hBaseLocks : ∀ u ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (fun D => D.AncestorEq B₀) s₀ u :=
    fun u hu n₃ sent₃ hrun hA => (liveLocksOnFamilyAt_base M F U) S A x R s₀ B₀ u n₃ E
      hB₀slot ((locksRevoked_of_voteTime_outcome M F U) S A x R E (s₀ + 1) u n₃ sent₃ hrun hA)
      (hBase.2.1 u hu n₃ sent₃ hrun hA)
  have hBaseConf : ∀ C : Block V, C.AncestorEq B₀ → ∀ v ∈ updaterAt M S A x s₀, ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some C' →
      C.AncestorEq C' := by
    intro C hC v hv C' hC'
    rw [hBaseSaved v hv] at hC'
    cases hC'
    exact hC
  -- the slot invariant and the lock invariant at every slot after the healed one and before `n`
  have hAll : ∀ s : ℕ, s₀ + 1 ≤ s → s < n →
      ChainInvFor M S A x (honestActiveAt M S A x s)
        (OnHonestChainBefore M S A x s₀ s) s ∧
      ∀ u ∈ honestActiveAt M S A x s,
        LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base =>
      intro hn
      -- the time facts of the members' ticks to the vote time of slot `s₀ + 1`
      obtain ⟨hv1, -, -, hs1, -, -, -⟩ := (slot_times M F U) S (s₀ + 1)
      obtain ⟨-, hc2, -, -, -, -, -⟩ := (slot_times M F U) S (s₀ + 1 + 1)
      have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s₀
      obtain ⟨-, -, -, hs0, -, hk8, -⟩ := (slot_times M F U) S s₀
      have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
      have hv1R : ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) = 4 * Δ S * s₀ + 5 * Δ S := by
        rw [hv1, hs0, hss]; push_cast; ring
      have hc2R : ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) = 4 * Δ S * s₀ + 10 * Δ S := by
        rw [hc2, hs1, hs0, hss]; push_cast; ring
      have hdw1 := duty_window_start_real S (s₀ + 1)
      push_cast at hdw1
      have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
      have hVT : ∀ w ∈ honestActiveAt M S A x (s₀ + 1), ∃ k : ℕ, x.lbl k = Event.tick w (M.voteTime S.C (s₀ + 1)) := by
        intro w hw
        have h1 : 1 ≤ M.voteTime S.C (s₀ + 1) := by omega
        have hr := (mem_activeThroughoutToTick_of_inside M F) R E ((honestActiveAt_window M F) S A (s₀ + 1) w E hw) h1
          (by rw [hdw1, hv1R]; linarith) (by rw [hv1R, hc2R]; linarith)
        obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hr
        exact ⟨k, hk⟩
      refine ⟨?_, fun u hu => ?_⟩
      · have h := (lem89s_chain_step_upTo M F U) S A x R GST s₀ (honestActiveAt M S A x s₀)
          (honestActiveAt M S A x (s₀ + 1)) (updaterAt M S A x s₀) (fun D => D.AncestorEq B₀)
          (E.mono (hcm _ _ (show s₀ + 1 ≤ n - 1 by omega))) hNet hSkew hRedeliver
          (Sy.mono (hcm _ _ (show s₀ + 1 ≤ n - 1 by omega))) hΔs (hRootsS s₀ (by omega)) (hRootsTickS s₀ (by omega)) hParent hOwner hGST
          (subset_refl _) (subset_refl _) (subset_refl _)
          ((honestActiveAt_succ_subset_updaterAt M F U) S A s₀ R E hSkew)
          (hCom s₀ le_rfl (by omega)) (hCom (s₀ + 1) (by omega) (by omega)) hBaseInv (hNewAt s₀) hBaseLocks hBaseConf
          (fun C hC w hw => by
            have hC' : OnHonestChainBefore M S A x s₀ (s₀ + 1) C := by
              rcases hC with hCB | ⟨v, hv, hsv⟩
              · exact hB₀chain C hCB
              · exact ⟨s₀, Nat.lt_succ_self s₀, le_rfl, v, hv, C, hsv, ancestorEq_refl C⟩
            obtain ⟨k, hk⟩ := hVT w hw
            have hti : x.tickInput w (M.voteTime S.C (s₀ + 1)) = x.st k w := by
              unfold Trace.tickInput
              rw [(tickStep_eq_of_lbl M) x E hk]
            have hVF := hVoterFrame (s₀ + 1) (Nat.lt_succ_self s₀) hn w hw C hC' k hk
            rw [← hti] at hVF
            exact ⟨hVF.1, hVF.2, hUpdaterFrame (s₀ + 1) (Nat.lt_succ_self s₀) hn w
              ((honestActiveAt_subset_updaterAt M F) S A x R E (s₀ + 1) hw) C hC'⟩)
        intro C hC
        apply h C
        obtain ⟨s', hs', hs₀', v, hv, C', hC', hCC'⟩ := hC
        have hss : s' = s₀ := by omega
        subst hss
        exact Or.inr ⟨v, hv, C', hC', hCC'⟩
      · refine (liveLocksOnFamilyAt_of_locksRevoked M F U) S A x R E _ _ u <| (liveLocksOnFamilyAt_step M F U) S A x R
          (fun D => D.AncestorEq B₀) (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ u E hSkew
          ((lockStep_window_of_honestActiveAt M F U) S A R E hSkew s₀ hu)
          hB₀chain
          (fun C hC => ⟨s₀, Nat.lt_succ_self s₀, le_rfl, u,
            (honestActiveAt_succ_subset_updaterAt M F U) S A s₀ R E hSkew hu, C, hC, ancestorEq_refl C⟩)
          ?_
        rcases hNewAt s₀ u hu with h0 | hfree
        · exact hBaseLocks u h0
        · exact (liveLocksOnFamilyAt_of_locksRevoked M F U) S A x R E _ _ u
            ((liveLocksOnFamilyAt_of_lockFree M F) S A x _ s₀ u hfree)
    | succ s hs ih =>
      intro hn
      obtain ⟨ihInv, ihLocks⟩ := ih (by omega)
      refine ⟨(lem81b_chain_step_upTo M F U) S A x R GST s₀ s anchor (E.mono (hcm _ _ (show s + 1 ≤ n - 1 by omega))) hNet hSkew hRedeliver
          (Sy.mono (hcm _ _ (show s + 1 ≤ n - 1 by omega))) hΔs
          (hRootsS s (by omega)) (hRootsTickS s (by omega)) hParent hOwner (hGSTs s (by omega)) (by omega)
          (hSleepK.mono M (hcm _ _ (by omega))) (hAnch s (by omega)) ihInv ihLocks
          (hVoterFrame (s + 1) (by omega) hn) (hUpdaterFrame s (by omega) (by omega))
          (fun w hw => hUpdaterFrame (s + 1) (by omega) hn w
            ((honestActiveAt_subset_updaterAt M F) S A x R E (s + 1) hw)),
        fun u hu => ?_⟩
      refine (liveLocksOnFamilyAt_of_locksRevoked M F U) S A x R E _ _ u <| (liveLocksOnFamilyAt_step M F U) S A x R
        (OnHonestChainBefore M S A x s₀ s) (OnHonestChainBefore M S A x s₀ (s + 1)) s u E hSkew
        ((lockStep_window_of_honestActiveAt M F U) S A R E hSkew s hu)
        (fun C ⟨s', hs', hAt⟩ => ⟨s', by omega, hAt⟩)
        (fun C hC => ⟨s, Nat.lt_succ_self s, by omega, u,
          (honestActiveAt_succ_subset_updaterAt M F U) S A s R E hSkew hu, C, hC, ancestorEq_refl C⟩) ?_
      rcases hNewAt s u hu with h0 | hfree
      · exact ihLocks u h0
      · exact (liveLocksOnFamilyAt_of_locksRevoked M F U) S A x R E _ _ u
          ((liveLocksOnFamilyAt_of_lockFree M F) S A x _ s u hfree)
  exact fun s hs => hAll s hs

end GoldilocksCorrectness.Record.Proofs.Executions

