module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.OrderedFloorVotes
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.DeliveryStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ViableAgreementUpTo
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ProposalPropagationStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.CountAgreementStatementsUpTo
public import GoldilocksCorrectness.Proofs.Executions.OrderedFloorVotes
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatementsUpTo
public import GoldilocksCorrectness.Proofs.Executions.ViableAgreementUpTo
public import GoldilocksCorrectness.Statements.Executions.ProposalPropagationStatementsUpTo
public import GoldilocksCorrectness.Statements.Executions.CountAgreementStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# OrderedFloorVotesUpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/OrderedFloorVotesUpTo.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemmas 20, 24 and 59 when
`head_height_floor` at the proposer is at most `head_height_floor` at the voter, with the delivery
premises up to a bound. The page's routine-level theorems are the facts' fields or have their twins
in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem supportCutoff_eq
  viewFreeze_eq voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (goldfish_eligible_of_parent_not_viable
  goldfish_eligible_of_parent_viable path_test_of_test_imp)

open GoldilocksCorrectness.Proofs.Routines (block_well_formed_iff goldfish_fork_choice_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AnchorAt AwakeFor CountedVotes FrameShape
  ProposalCountedVotes VoterTree)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (StartsTowards RootsNameBlocksIn VotesOnceFor
  expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  mem_voter_block_tree_iff occurrenceBefore_eq_true_iff ancestorEq_of_parent?
  parent?_eq_some_parent parent_eq_of_parent? goldfish_eligible_answers
  goldfish_eligible_current_slot goldfish_eligible_congr path_test_of_test_agree
  ancestorEq_compatible ghost_spec ghost_reaches ghost_step_none_of_no_child ancestorEq_antisymm
  ancestorEq_node_iff)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- Lemma 20 with the viable heads along the path agreeing in one direction, and `B`'s parent viable
at `w` when it is at `p`. The proof; the audited statement is in
`Statements/Executions/OrderedFloorStatements.lean`.

Roots name blocks until the later of the real times of `p`'s and `w`'s own ticks to `M.supportCutoff S.C s`: the
bounds of the two Lemma 12 calls at slot `s` the proof passes the premise to, as Lemma 20's.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the slot-`s` votes reach `p` and
`w` by then (`lem12_honest_vote_delivered_until_upTo`).

The variables:
- `M`: the model; `F`: its facts.

Read aloud: Lemma 20 holds when, along the path from `X` to `B`'s parent past the root of `w`'s fork
choice, every viable head at `w` is one at `p`, and `B`'s parent, if a viable head at `p`, is one at
`w`. -/
theorem lem20le_goldfish_vote_names_honest_proposal_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the later of the real times of `p`'s and `w`'s own ticks to the support cutoff of
    -- slot `s`
    (hRoots : RootsNameBlocksUntil M A x (max (x.time (x.tickStep p (M.supportCutoff S.C s)))
      (x.time (x.tickStep w (M.supportCutoff S.C s)))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- the slot-`s` votes of `Hs` for `X`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ X.AncestorEq (H u))
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes_w support_w →
      M.voters_count votes_w < 2 * Hs.card)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the proposer `p` and the voter `w` each tick to the support cutoff of slot `s` at a step `kR` and are active at
    -- every step from the sync fact's read time `supportCutoff s − max (2 * Δ S) Δs` up to `kR`
    (hp : ∃ kR : ℕ, x.lbl kR = Event.tick p (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → p ∈ A.active j)
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → w ∈ A.active j)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    -- `w` holds `B` before its vote
    (hBw : B ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree)
    -- the finality-gadget condition at `p`, on its state before `slotStart S (s + 1)`
    (hF3p : ∃ W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree,
      W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads ∧ X.AncestorEq W)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (M.get_anchor (x.tickInput p (M.slotStart S.C (s + 1)))
      ((M.slotStart S.C (s + 1) : ℕ) : Int)).AncestorEq X)
    -- every live lock entry `w`'s revocation leaves is on `B` or an ancestor of `B`
    (hLocksW : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `B` is a viable head at `w`
    (hBViable : B ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads)
    -- the two validators agree on the viable heads along the path from `X` to `B`'s parent, on
    -- the blocks of it that have the root of `w`'s fork choice as an ancestor (or are that root)
    (hViableLe : ∀ Y : Block V, X.AncestorEq Y →
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq Y →
      Y.AncestorEq B.parent →
      Y ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads →
      Y ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads)
    -- `B`'s parent, when the root of `w`'s fork choice is an ancestor of it (or it), is a viable
    -- head at `w` when it is one at `p`
    (hViableEnd :
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq B.parent →
      B.parent ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads →
      B.parent ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads)
    -- the two validators count alike: the same score on every child of a block from `X` to
    -- `B`'s parent that has the root of `w`'s fork choice as an ancestor (or is that root), the
    -- same number of voters
    (hCount : ∀ votes_p support_p votes_w support_w : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput p (M.slotStart S.C (s + 1))) s votes_p support_p →
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes_w support_w →
      (∀ Y : Block V, X.AncestorEq Y →
        (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq Y →
        Y.AncestorEq B.parent →
        ∀ D : Block V, D.parent? = some Y → ∃ n : ℕ,
          goldfish_score (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))) votes_p
            support_p s D = .ok n ∧
          goldfish_score (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) votes_w
            support_w s D = .ok n) ∧
      M.voters_count votes_p = M.voters_count votes_w)
    -- every child in `w`'s viable tree of a block from `X` to `B`'s parent that has the root of
    -- `w`'s fork choice as an ancestor (or is that root), other than `B`, that `w`'s eligibility
    -- test accepts, is in `p`'s viable tree
    (hChild : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes_w support_w →
      ∀ Y : Block V, X.AncestorEq Y →
        (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq Y →
        Y.AncestorEq B.parent →
        ∀ D ∈ M.viable_tree (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1))))
            (VoterTree M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1)),
          D.parent? = some Y → D ≠ B →
          goldfish_eligible S.C (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1))))
            ((M.voteTime S.C (s + 1) : ℕ) : Int) votes_w support_w s D = .ok true →
          D ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
            (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree) :
    vote.head = B.root := by
  letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
  -- step 0: the times; the slots of `t₁` and `t₃`, read by the spec's clock (the model's slot of a
  -- natural-number time is the spec's, `U`)
  have hΔ := one_le_Δ S
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hss' : M.slotStart S.C (s + 1 + 1) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1), Nat.mul_add, Nat.mul_one]
  have hv₃ : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hv₁ : M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hc₀ : M.supportCutoff S.C s = M.voteTime S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have hslot₁ : S.C.slot ((M.slotStart S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (le_refl _) (by omega)
  have hslot₃ : S.C.slot ((M.voteTime S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (by omega) (by omega)
  have hfreeze : ∀ a d : Int, 0 < d → a + 2 * d < a + 3 * d := by
    intro a d hd
    omega
  have h23 : ((S.C.t_ s + 2 * S.C.Δ : Time) : Stamp) < ((S.C.t_ s + 3 * S.C.Δ : Time) : Stamp) :=
    WithBot.coe_lt_coe.2 (hfreeze _ _ S.C.Δ_pos)
  -- step 1: `p`'s run and proposal (Lemma 19 over the record, the field `tick_proposal` of
  -- `F.tk3`, from the tick's input state, which satisfies the node invariant: `p` is active at its
  -- tick): `p`'s walk counts its slot-`s` votes and those that resolve (`ProposalCountedVotes`), from
  -- `p`'s anchor
  obtain ⟨i₁, hl₁, hm₁⟩ := hPropose
  obtain ⟨-, n₁', sent₁, hrun₁, hB₁⟩ := (tick_send_of_honestSendAt M F R E) hl₁ hm₁
  have hpi₁ : p ∉ A.corrupted i₁ := E.not_mem_corrupted_of_tick hl₁
  have hti₁ : x.tickInput p (M.slotStart S.C (s + 1)) = x.st i₁ p := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl₁]
  have hRootsΦp : RootsNameBlocksIn (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree := by
    rw [hti₁]
    exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E i₁ p
  have hInvp : M.nodeInv S.C S.P S.X (x.tickInput p (M.slotStart S.C (s + 1))) := by
    rw [hti₁]
    exact (lem11_node_invariant M F S A x R E i₁ p hpi₁).1
  have hF2p : (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).fc_root := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F), hti₁]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E i₁ p
  obtain ⟨-, -, -, ⟨τp, hτp, -⟩, Hp, votes_pl, support_pl, -, -, hWalkP, hBdef⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n₁' _ sent₁ B hrun₁ hInvp hB₁
  rw [hslot₁, Nat.add_sub_cancel] at hWalkP
  rw [hslot₁] at hBdef
  obtain ⟨votes_p, support_p, hPCV, hWp⟩ := hWalkP
  have hBpar : B.parent = Hp := by rw [hBdef]; rfl
  have hBslot : B.slot = s + 1 := by rw [hBdef]; rfl
  have hBne : B ≠ Block.genesis := by rw [hBdef]; exact fun h => by cases h
  have hBpar? : B.parent? = some Hp := by rw [hBdef]; rfl
  -- step 2: `w`'s run and walk (Lemma 14 over the record, the field `tick_vote_head` of `F.tk3`,
  -- from the tick's input state, awake for the slot): `w`'s vote is for the end `H_w` of the walk
  -- through the viable part of `w`'s voter's tree (`VoterTree`), from the anchor over `w`'s frame with
  -- the lock entries the tick left (`AnchorAt`)
  obtain ⟨i, hl, hm⟩ := hSend
  obtain ⟨-, n', sent, hrun, hvote⟩ := (tick_send_of_honestSendAt M F R E) hl hm
  have hwi : w ∉ A.corrupted i := E.not_mem_corrupted_of_tick hl
  have hti : x.tickInput w (M.voteTime S.C (s + 1)) = x.st i w := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hRootsΦ : RootsNameBlocksIn (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree := by
    rw [hti]
    exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E i w
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1))) := by
    rw [hti]
    exact (lem11_node_invariant M F S A x R E i w hwi).1
  have hF2w : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F), hti]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E i w
  obtain ⟨-, -, -, -, ⟨τw, hτw, hτwle⟩, H_w, ⟨votes, support_votes, hCounted, hWalk⟩, hhead⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem14_tick_vote_walk F) S.C S.P S.X _ n' _ sent vote hrun hInvT hvote
  rw [hslot₃] at hτwle
  have hAwake : AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) := ⟨τw, hτw, hτwle⟩
  have hrun' := hrun
  rw [hslot₃] at hCounted hWalk
  rw [Nat.add_sub_cancel] at hWalk
  have hCv := hCounted.1
  have hCs := hCounted.2
  simp only [Nat.add_sub_cancel] at hCv hCs
  have hInvW := hInvT
  -- the two ticks: `p`'s to the start of slot `s + 1` is at a real time less than `w`'s to the vote time
  -- of slot `s + 1` (`hSkew`), so at an earlier step, and every voter outside the adversary set at `w`'s
  -- tick is outside it at `p`'s (corruption is permanent)
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hi₁i : i₁ ≤ i := by
    by_contra hlt
    have h1 := (E.tick_active i₁ p _ hl₁).2.2
    have h2 := (E.tick_active i w _ hl).2.1
    have h3 := (time_mono M) x R (show i ≤ i₁ by omega)
    have h4 : ((M.voteTime S.C (s + 1) : ℕ) : ℝ) = ((M.slotStart S.C (s + 1) : ℕ) : ℝ) + Δ S := by
      rw [hv₃]; push_cast; ring
    linarith
  have hHonW : ∀ u ∈ Hs, u ∉ A.corrupted i := fun u hu => by
    have h := (hHs u hu).2.1
    rwa [(tickStep_eq_of_lbl M) x E hl] at h
  have hHonP : ∀ u ∈ Hs, u ∉ A.corrupted i₁ := fun u hu => E.not_mem_corrupted_of_le hi₁i (hHonW u hu)
  -- the receivers' ticks to the support cutoff of slot `s`, where roots name blocks
  have hRootsP : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.supportCutoff S.C s))) :=
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (le_max_left _ _) hRoots
  have hRootsW : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))) :=
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (le_max_right _ _) hRoots
  -- step 3: the delivered votes at `p` at its tick to `t₁`; `p`'s finalized block is an ancestor of each
  -- `H u`, through the root of its fork choice, its anchor and `X`
  have hHeldP : ∀ u ∈ Hs, HeldEarlyVoteFor M S.C (x.tickInput p (M.slotStart S.C (s + 1))) s (H u) u :=
    (lem12_honest_vote_delivered_until_of_steps_upTo M F U) S A x R GST s (M.slotStart S.C (s + 1)) Hs H p
      E hNet hSkew hRedeliver Sy hΔs hRootsP hParent hOwner hGST (by omega) i₁ hl₁
      (fun u hu => ⟨(hHs u hu).1, hHonP u hu, (hHs u hu).2.2.1, (hHs u hu).2.2.2.1⟩)
      hHold hp
      (fun u hu => ancestorEq_trans hF2p (ancestorEq_trans ((GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_get_anchor M F) _ _)
        (ancestorEq_trans hApX (hHs u hu).2.2.2.2)))
  have hVotersW : M.voters_count votes < 2 * Hs.card := hVoters votes support_votes hCounted
  obtain ⟨u₀, hu₀⟩ : Hs.Nonempty := Finset.card_pos.1 (by omega)
  -- step 4: the roots name blocks at `p` and at `w` (`hRootsΦp`, `hRootsΦ`, steps 1 and 2)
  -- step 5: the two validators count alike, on the children of the blocks from `X` to `B`'s
  -- parent; so `p`'s voters are fewer than twice `Hs`, as `w`'s are
  obtain ⟨hScore, hVotersEq⟩ := hCount _ _ _ _ hPCV hCounted
  have hVotersP : M.voters_count votes_p < 2 * Hs.card := hVotersEq ▸ hVotersW
  -- the spec's voter counts, which the walk lemmas and the eligibility test read
  have hVotersEq' : voters_count votes_p = voters_count votes := by
    rw [← GoldilocksCorrectness.Record.Proofs.Routines.voters_count_eq_spec F]
    exact hVotersEq
  obtain ⟨n, hn⟩ : ∃ n : Block V → ℕ, ∀ Y : Block V, X.AncestorEq Y →
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq Y →
      Y.AncestorEq B.parent → ∀ D : Block V, D.parent? = some Y →
        goldfish_score (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))) votes_p support_p s D = .ok (n D) ∧
        goldfish_score (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) votes support_votes s D = .ok (n D) := by
    classical
    refine ⟨fun D => if h : ∃ m : ℕ,
        goldfish_score (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))) votes_p support_p s D = .ok m ∧
        goldfish_score (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) votes support_votes s D = .ok m then Classical.choose h else 0, ?_⟩
    intro Y hXY hRY hYB D hD
    have h := hScore Y hXY hRY hYB D hD
    simp only [dif_pos h]
    exact Classical.choose_spec h
  -- step 6: `p`'s start
  have hHu₀T : H u₀ ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree :=
    (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 (hHeldP u₀ hu₀).2.2.1).1
  have hStartP : StartsTowards (M.get_anchor (x.tickInput p (M.slotStart S.C (s + 1))) ((M.slotStart S.C (s + 1) : ℕ) : Int)) X (M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))) (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree) := by
    obtain ⟨W, hW, hWv, hXW⟩ := hF3p
    refine (GoldilocksCorrectness.Record.Statements.Routines.lem7_startsTowards_of_compatible M F) _ _ _ X W
      ((compatible_iff _ _).2 (Or.inl hApX)) ((GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_get_anchor M F) _ _) ?_ ⟨hW, hWv⟩
      hXW
    intro P hAP _ hPX
    have hPH : P.AncestorEq (H u₀) := ancestorEq_trans hPX (hHs u₀ hu₀).2.2.2.2
    have hPT : P ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ p _ P hHu₀T hPH
    have hFP : (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq P :=
      ancestorEq_trans hF2p (ancestorEq_trans ((GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_get_anchor M F) _ _) hAP)
    exact ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hPT, hFP⟩
  -- step 7: `p`'s walk, so `X` is `B`'s parent or an ancestor of it (Lemma 2 over the walk
  -- predicate)
  have hSupportP : support_p ⊆ votes_p := by
    intro vote' hv
    rw [hPCV.1]
    exact ((hPCV.2 vote').1 hv).1
  have hVotesP : ∀ u ∈ Hs, VotesOnceFor (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))) votes_p support_p s X u := by
    intro u hu
    obtain ⟨hpool, -, hHΦ, ⟨y, hy, -⟩, huniq⟩ := hHeldP u hu
    refine ⟨GoldfishVote.mk u s (H u).root, (hPCV.2 _).2 ⟨hpool, y, hy⟩, rfl, rfl,
      ⟨H u, hHΦ, rfl, (hHs u hu).2.2.2.2⟩, ?_⟩
    intro vote' hv' hi'
    rw [hPCV.1] at hv'
    exact huniq vote' hv' hi'
  have hXH : X.AncestorEq Hp :=
    GoldilocksCorrectness.Statements.Routines.lem2_goldfish_walkEnd_extends_majority_block
      S.C _ _ votes_p support_p s _ X Hp _ Hs hStartP hRootsΦp hSupportP hVotesP
      (by rw [← GoldilocksCorrectness.Record.Proofs.Routines.voters_count_eq_spec F]; exact hVotersP) hWp
  have hHB : Hp.AncestorEq B := ancestorEq_of_parent? hBpar?
  have hXB : X.AncestorEq B := ancestorEq_trans hXH hHB
  have hXBp : X.AncestorEq B.parent := hBpar ▸ hXH
  have hBpB : B.parent.AncestorEq B := hBpar ▸ hHB
  -- step 8: `B` is in `w`'s frame tree
  have hRB : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq B :=
    (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hInvW B).1 hBViable).2.2.1
  have hBΦ : B ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hBw, ancestorEq_trans hF2w hRB⟩
  -- every ancestor of `B` that has the root of `w`'s fork choice as an ancestor is in `w`'s frame
  -- tree
  have hAncΦ : ∀ Y : Block V, (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq Y → Y.AncestorEq B → Y ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree := by
    intro Y hRY hYB
    exact ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2
      ⟨(GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w _ Y hBw hYB, ancestorEq_trans hF2w hRY⟩
  -- step 9: `w`'s anchor is `B` or an ancestor of it, and a descendant of the root of `w`'s fork
  -- choice: it is that root, or a block of the viable tree that a live lock entry the tick left
  -- locks, and every such entry is on `B` or an ancestor of `B` (`hLocksW`)
  have hLocks := hLocksW n' sent hrun' hAwake
  have hAnchorW : (AnchorAt M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int)).AncestorEq B := by
    rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases_locked M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int) with h | ⟨-, e, he, hd, heT, hAe⟩
    · rw [h]
      exact hRB
    · have hlive : M.is_live (x.tickInput w (M.voteTime S.C (s + 1))) ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true := by
        simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)]
        exact ⟨hd, heT⟩
      exact ancestorEq_trans hAe (hLocks e he hlive)
  have hRAw : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq (AnchorAt M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int)) := by
    rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int) with h | h
    · rw [h]
      exact ancestorEq_refl _
    · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h).2.1
  -- step 10: every block of `Φ_w.tree` that is `B` or an ancestor of `B` is in the voter's tree,
  -- and in its viable part when the root of the fork choice is an ancestor of it
  have hInVbt : ∀ Y ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree, Y.AncestorEq B → Y ∈ VoterTree M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) := by
    intro Y hY hYB
    have hYT := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hY).1
    obtain ⟨τ, hτ⟩ := Option.ne_none_iff_exists'.1 (F.nd.nodeInv_treeStamped hInvW Y hYT)
    exact (GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ (s + 1) Y).2
      ⟨hY, τ, hτ, Or.inr ⟨B, hBΦ, hBslot, hYB⟩⟩
  have hInTree : ∀ Y ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree, (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq Y → Y.AncestorEq B →
      Y ∈ M.viable_tree (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) (VoterTree M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1)) := by
    intro Y hY hRY hYB
    exact ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).2 ⟨hInVbt Y hY hYB, hRY, B,
      Finset.mem_inter.2 ⟨hInVbt B hBΦ (ancestorEq_refl B), hBViable⟩, hYB⟩
  -- step 11: when `w`'s anchor is `X` or an ancestor of `X`, `w`'s walk passes `X`: Lemma 7 for
  -- the start, then Lemma 2 with `Sup := Hs` and `X` for `R`
  have hXHw_of : (AnchorAt M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int)).AncestorEq X → X.AncestorEq H_w := by
    intro hAwX
    have hFXw : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq X :=
      ancestorEq_trans hF2w (ancestorEq_trans hRAw hAwX)
    have hHeld : ∀ u ∈ Hs, HeldEarlyVoteFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) s (H u) u :=
      (lem12_honest_vote_delivered_until_of_steps_upTo M F U) S A x R GST s (M.voteTime S.C (s + 1)) Hs H w
        E hNet hSkew hRedeliver Sy hΔs hRootsW hParent hOwner hGST (by omega) i hl
        (fun u hu => ⟨(hHs u hu).1, hHonW u hu, (hHs u hu).2.2.1, (hHs u hu).2.2.2.1⟩)
        hHold hw (fun u hu => ancestorEq_trans hFXw (hHs u hu).2.2.2.2)
    have hStartW : StartsTowards (AnchorAt M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int)) X
        (M.viable_tree (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) (VoterTree M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1))) := by
      refine (GoldilocksCorrectness.Record.Statements.Routines.lem7_startsTowards_of_compatible M F) _ _ _ X B
        ((compatible_iff _ _).2 (Or.inl hAwX)) hRAw ?_
        ⟨hInVbt B hBΦ (ancestorEq_refl B), hBViable⟩ hXB
      intro P hAP _ hPX
      have hPB : P.AncestorEq B := ancestorEq_trans hPX hXB
      exact hInVbt P (hAncΦ P (ancestorEq_trans hRAw hAP) hPB) hPB
    have hBne' : ∀ B' : Block V, B'.slot = s + 1 → B' ≠ Block.genesis := by
      rintro B' hBs rfl
      exact Nat.succ_ne_zero s hBs.symm
    have hPayload : ∀ B' ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree, B'.slot = s + 1 → M.ac_valid_payload S.P B' = true := by
      intro B' hB' hBs
      have hBT := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hB').1
      have hwf := ((F.nd.nodeInv_treeClosed hInvW).2 B' hBT (hBne' B' hBs)).2.1
      exact ((F.rd.block_well_formed_iff S.P S.X B').1 hwf).1.2
    have hIncl : ∀ vote' ∈ M.included_votes (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) (s + 1), ∃ B' ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree,
        B'.slot = s + 1 ∧ vote' ∈ B'.votes ∧ vote'.slot = s := by
      intro vote' hv
      simp only [(GoldilocksCorrectness.Record.Proofs.Routines.mem_included_votes_iff M F), Nat.add_sub_cancel] at hv
      obtain ⟨B', ⟨hB', hBs⟩, hvB, hvs⟩ := hv
      exact ⟨B', hB', hBs, hvB, hvs⟩
    have hSupport : support_votes ⊆ votes := by
      intro vote' hv
      rcases (hCs vote').1 hv with ⟨hp', hτ, -⟩ | ⟨hinc, -⟩
      · exact (hCv vote').2 (Or.inl ⟨hp', hτ⟩)
      · simp only [(GoldilocksCorrectness.Record.Proofs.Routines.mem_included_support_votes_iff M F), Nat.add_sub_cancel] at hinc
        obtain ⟨B', ⟨hB', hBs⟩, hvB, hvs⟩ := hinc
        have hvB' : vote' ∈ B'.votes :=
          ((GoldilocksCorrectness.Record.Proofs.Routines.ac_valid_payload_facts M F) S.P B' (hPayload B' hB' hBs)).2.1 vote' hvB
        refine (hCv vote').2 (Or.inr ?_)
        simp only [(GoldilocksCorrectness.Record.Proofs.Routines.mem_included_votes_iff M F), Nat.add_sub_cancel]
        exact ⟨B', ⟨hB', hBs⟩, hvB', hvs⟩
    have ht₁₃ : M.voteTime S.C s ≤ M.voteTime S.C (s + 1) := by omega
    have hVotes : ∀ u ∈ Hs, VotesOnceFor (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) votes support_votes s X u := by
      intro u hu
      obtain ⟨hpool, ⟨τ, hτ, hτlt⟩, hHΦ, ⟨y, hy, hyb⟩, huniq⟩ := hHeld u hu
      obtain ⟨y', hyy', hy'lt⟩ := (occurrenceBefore_eq_true_iff _ _).1 hyb
      have hyy : y = y' := Option.some_injective _ hyy'
      refine ⟨GoldfishVote.mk u s (H u).root,
        (hCs _).2 (Or.inl ⟨hpool, ⟨τ, hτ, lt_trans hτlt h23⟩, ⟨y, hy, hyy ▸ lt_trans hy'lt h23⟩⟩),
        rfl, rfl, ⟨H u, hHΦ, rfl, (hHs u hu).2.2.2.2⟩, ?_⟩
      intro vote' hv' hi'
      rcases (hCv vote').1 hv' with ⟨hp', -⟩ | hinc
      · exact huniq vote' hp' hi'
      · obtain ⟨B', hB', hBs, hvB, hvs⟩ := hIncl vote' hinc
        obtain ⟨-, hhon, ⟨j₁, hlj₁, hsent₁⟩, -, -⟩ := hHs u hu
        exact (included_vote_eq_of_owner_st M F) S A x R _ j₁ (M.voteTime S.C s) w u B'
          _ vote' E hOwner hhon (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hB').1 (hBne' B' hBs) hvB hi'
          hlj₁ hsent₁ hvs
    exact GoldilocksCorrectness.Statements.Routines.lem2_goldfish_walkEnd_extends_majority_block
      S.C _ _ votes support_votes s _ X H_w _ Hs hStartW hRootsΦ hSupport hVotes
      (by rw [← GoldilocksCorrectness.Record.Proofs.Routines.voters_count_eq_spec F]; exact hVotersW) hWalk
  -- step 12: the merge, Lemma 9 over the walk predicate
  have hTestP := fun D : Block V => Classical.choose_spec
    (goldfish_eligible_answers S.C hRootsΦp ((M.slotStart S.C (s + 1) : ℕ) : Int) votes_p support_p s D)
  have hTestW := fun D : Block V => Classical.choose_spec
    (goldfish_eligible_answers S.C hRootsΦ ((M.voteTime S.C (s + 1) : ℕ) : Int) votes support_votes s D)
  have hSlot : S.C.slot ((M.slotStart S.C (s + 1) : ℕ) : Int) = S.C.slot ((M.voteTime S.C (s + 1) : ℕ) : Int) := hslot₁.trans hslot₃.symm
  -- no block of `w`'s tree is a child of `B`
  have hNoChildP : ∀ D ∈ M.viable_tree (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) (VoterTree M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1)), D.parent? ≠ some B := by
    intro D hD hDB
    have hDvbt := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 hD).1
    have hDΦ := ((GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ (s + 1) D).1 hDvbt).1
    have hDT := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hDΦ).1
    have hDle : D.slot ≤ s + 1 := by
      rw [hti] at hDT
      have h1 := (slot_le_clockValue_of_mem_tree M F) R E hwi hDT
      have h2 : x.clockValue i w < M.voteTime S.C (s + 1) :=
        (clockValue_lt_of_tick_awakeSince_some M F) R E hl (by omega) (hti ▸ hτw)
      have h3 := GoldilocksCorrectness.Proofs.Routines.slot_mono_int S
        (show ((x.clockValue i w : ℕ) : Int) ≤ ((M.voteTime S.C (s + 1) : ℕ) : Int) by exact_mod_cast h2.le)
      rw [hslot₃] at h3
      exact h1.trans h3
    have hDne : D ≠ Block.genesis := by
      rintro rfl
      cases hDB
    have hlt := ((F.nd.nodeInv_treeClosed hInvW).2 D hDT hDne).2.2.2
    rw [parent_eq_of_parent? hDB, hBslot] at hlt
    exact Nat.lt_irrefl _ (lt_of_lt_of_le hlt hDle)
  -- the two tests' answers, named
  obtain ⟨bp, hbp⟩ : ∃ bp : Block V → Bool, ∀ D : Block V,
      goldfish_eligible S.C (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))) ((M.slotStart S.C (s + 1) : ℕ) : Int)
        votes_p support_p s D = .ok (bp D) :=
    ⟨fun D => Classical.choose (goldfish_eligible_answers S.C hRootsΦp
      ((M.slotStart S.C (s + 1) : ℕ) : Int) votes_p support_p s D), hTestP⟩
  obtain ⟨bw, hbw⟩ : ∃ bw : Block V → Bool, ∀ D : Block V,
      goldfish_eligible S.C (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) ((M.voteTime S.C (s + 1) : ℕ) : Int)
        votes support_votes s D = .ok (bw D) :=
    ⟨fun D => Classical.choose (goldfish_eligible_answers S.C hRootsΦ
      ((M.voteTime S.C (s + 1) : ℕ) : Int) votes support_votes s D), hTestW⟩
  have hPTest' : bw B = true :=
    Except.ok.inj ((hbw B).symm.trans (goldfish_eligible_current_slot S.C _ _ _ _ s B
      (hBslot.trans hslot₃.symm)))
  -- the two tests agree on a child of a path block that is a viable head at `w`
  have hTestAgreeW : ∀ Y : Block V, X.AncestorEq Y → (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq Y →
      Y.AncestorEq B.parent → Y ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads →
      ∀ D : Block V, D.parent? = some Y → bw D = bp D := by
    intro Y hXY hRY hYB hYw D hD
    have hHeads : D.parent ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads ↔ D.parent ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads := by
      rw [parent_eq_of_parent? hD]
      exact ⟨fun _ => hYw, fun _ => hViableLe Y hXY hRY hYB hYw⟩
    have hEq := goldfish_eligible_congr S.C _ _ _ _ votes_p support_p votes
      support_votes s D (n D) hHeads hSlot (hn Y hXY hRY hYB D hD).1 (hn Y hXY hRY hYB D hD).2
      hVotersEq'
    exact Except.ok.inj ((hbw D).symm.trans (hEq.symm.trans (hbp D)))
  -- a child of a block that is not a viable head passes the test
  have hbpTrue : ∀ D : Block V, D.parent ∉ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads → bp D = true :=
    fun D hD => Except.ok.inj ((hbp D).symm.trans
      (goldfish_eligible_of_parent_not_viable S.C _ _ _ _ s D hD))
  have hbwTrue : ∀ D : Block V, D.parent ∉ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads → bw D = true :=
    fun D hD => Except.ok.inj ((hbw D).symm.trans
      (goldfish_eligible_of_parent_not_viable S.C _ _ _ _ s D hD))
  -- `p`'s test on a child of a viable head of `p`, other than a slot-`(s + 1)` block, is the
  -- majority test
  have hbpMaj : ∀ D : Block V, D.parent ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads → D.slot ≠ s + 1 →
      ∀ m : ℕ, goldfish_score (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))) votes_p support_p s D = .ok m →
      (bp D = true ↔ voters_count votes_p < 2 * m) := by
    intro D hD hDs m hm
    have hDs' : D.slot ≠ S.C.slot ((M.slotStart S.C (s + 1) : ℕ) : Int) := by
      rw [hslot₁]
      exact hDs
    have h := (hbp D).symm.trans (goldfish_eligible_of_parent_viable S.C _ _ _ _ s D m hD hDs' hm)
    rw [Except.ok.inj h]
    exact decide_eq_true_iff
  -- a block of `p`'s viable tree has a slot at most `s`
  have hslot₀ : S.C.slot ((M.slotStart S.C (s + 1) - 1 : ℕ) : Int) = s := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
      (by omega) (by omega)
  have hTreePSlot : ∀ D ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))) (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree, D.slot ≠ s + 1 := by
    intro D hD hDs
    have hDT := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1
      (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 hD).1).1
    -- `p`'s clock value at its tick to `t₁` is less than `t₁`, so at most `t₁ - 1`, whose slot is `s`
    rw [hti₁] at hDT
    have h1 := (slot_le_clockValue_of_mem_tree M F) R E hpi₁ hDT
    have h2 : x.clockValue i₁ p < M.slotStart S.C (s + 1) :=
      (clockValue_lt_of_tick_awakeSince_some M F) R E hl₁ (by omega) (hti₁ ▸ hτp)
    have h3 := GoldilocksCorrectness.Proofs.Routines.slot_mono_int S
      (show ((x.clockValue i₁ p : ℕ) : Int) ≤ ((M.slotStart S.C (s + 1) - 1 : ℕ) : Int) by
        exact_mod_cast (show x.clockValue i₁ p ≤ M.slotStart S.C (s + 1) - 1 by omega))
    rw [hDs] at h1
    rw [hslot₀] at h3
    have h4 := h1.trans h3
    exact Nat.not_succ_le_self s h4
  have hWalkPB := hWp
  rw [← hBpar] at hWalkPB
  -- Lemma 9 with the score argument over the walk predicate, at any shared block `X'` from `X` to
  -- `B`'s parent that is `w`'s anchor or a descendant of it, and `H_w` or an ancestor of it
  have hMergeAt : ∀ X' : Block V, X.AncestorEq X' → X'.AncestorEq B.parent →
      (AnchorAt M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int)).AncestorEq X' → X'.AncestorEq H_w → H_w = B := by
    intro X' hXX' hX'B hAwX' hX'H
    have hRX' : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq X' := ancestorEq_trans hRAw hAwX'
    -- `w`'s test accepts what `p`'s does on a child of a path block
    have hImp : ∀ Y : Block V, X'.AncestorEq Y → Y.AncestorEq B.parent →
        ∀ D : Block V, D.parent? = some Y → bp D = true → bw D = true := by
      intro Y hX'Y hYB D hD hb
      by_cases hYw : Y ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads
      · rw [hTestAgreeW Y (ancestorEq_trans hXX' hX'Y) (ancestorEq_trans hRX' hX'Y) hYB hYw D hD]
        exact hb
      · exact hbwTrue D (by rw [parent_eq_of_parent? hD]; exact hYw)
    -- so `w`'s test accepts every block after `X'` up to `B`'s parent: such a block is a child of
    -- a block from `X'` to `B`'s parent, and `p`'s walk passed it
    have hPathTest : ∀ Y : Block V, X'.AncestorEq Y → Y ≠ X' → Y.AncestorEq B.parent →
        bw Y = true := by
      intro Y hX'Y hYX hYP
      have hApX' := ancestorEq_trans hApX hXX'
      have hYg : Y ≠ Block.genesis := by
        rintro rfl
        exact hYX ((GoldilocksCorrectness.Proofs.Routines.ancestorEq_genesis_iff X').1 hX'Y).symm
      have hYpar := parent?_eq_some_parent hYg
      have hXQ : X'.AncestorEq Y.parent :=
        GoldilocksCorrectness.Proofs.Routines.ancestorEq_parent_of_ne hX'Y (Ne.symm hYX)
      have hQP : Y.parent.AncestorEq B.parent :=
        ancestorEq_trans (ancestorEq_of_parent? hYpar) hYP
      refine hImp Y.parent hXQ hQP Y hYpar
        (GoldilocksCorrectness.Proofs.Routines.walkEnd_visited_test_true bp hbp hWalkPB Y
          (ancestorEq_trans hApX' hX'Y) ?_ hYP)
      intro h
      exact hYX (ancestorEq_antisymm hX'Y (h ▸ hApX')).symm
    exact GoldilocksCorrectness.Statements.Routines.lem9le_walkEnd_ends_at_proposal_of_shared_block
      (X := X') (P := B) (H_w := H_w) n bp bw
      (fun Y hX'Y hYB D hD =>
        (hn Y (ancestorEq_trans hXX' hX'Y) (ancestorEq_trans hRX' hX'Y) hYB D hD).1)
      (fun Y hX'Y hYB D hD =>
        (hn Y (ancestorEq_trans hXX' hX'Y) (ancestorEq_trans hRX' hX'Y) hYB D hD).2)
      hbp hbw (parent?_eq_some_parent hBne) hWalkPB hWalk
      ⟨ancestorEq_trans hApX hXX', hX'B⟩ hAwX' hX'H
      (fun Y hX'Y _ hYB => hInTree Y (hAncΦ Y (ancestorEq_trans hRX' hX'Y)
          (ancestorEq_trans hYB hBpB))
        (ancestorEq_trans hRX' hX'Y) (ancestorEq_trans hYB hBpB))
      (hInTree B hBΦ hRB (ancestorEq_refl B))
      hPTest' hNoChildP hPathTest
      (fun Y hX'Y hYB hYne D hD hDpar hDb => by
        have hXY := ancestorEq_trans hXX' hX'Y
        have hRY := ancestorEq_trans hRX' hX'Y
        have hDB : D ≠ B := by
          rintro rfl
          rw [hBpar?] at hDpar
          exact hYne ((Option.some.inj hDpar).symm.trans hBpar.symm)
        have hDp := hChild votes support_votes hCounted Y hXY hRY hYB D hD hDpar hDB
          (by rw [hbw D, hDb])
        by_cases hYw : Y ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads
        · exact Or.inl ⟨hDp, by rw [← hTestAgreeW Y hXY hRY hYB hYw D hDpar]; exact hDb⟩
        by_cases hYp : Y ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads
        swap
        · exact Or.inl ⟨hDp, hbpTrue D (by rw [parent_eq_of_parent? hDpar]; exact hYp)⟩
        cases hbD : bp D with
        | true => exact Or.inl ⟨hDp, rfl⟩
        | false =>
          refine Or.inr (fun D' hD'p hD'par hD'B hb' => ?_)
          have hYD : D.parent ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads := by
            rw [parent_eq_of_parent? hDpar]; exact hYp
          have hYD' : D'.parent ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads := by
            rw [parent_eq_of_parent? hD'par]; exact hYp
          -- `D` is not a slot-`(s + 1)` block: `p`'s test would accept it
          have hDs : D.slot ≠ s + 1 := by
            intro hDs
            have h := (hbp D).symm.trans (goldfish_eligible_current_slot S.C _ _ _ _ s D
              (hDs.trans hslot₁.symm))
            rw [hbD] at h
            cases h
          have h1 := (hbpMaj D hYD hDs (n D) (hn Y hXY hRY hYB D hDpar).1).not.1
            (by rw [hbD]; exact Bool.false_ne_true)
          have h2 := (hbpMaj D' hYD' (hTreePSlot D' hD'p) (n D')
            (hn Y hXY hRY hYB D' hD'par).1).1 hb'
          omega)
      (fun D hD hDpar hDB hDb => by
        have hXB' := ancestorEq_trans hXX' hX'B
        have hRB' := ancestorEq_trans hRX' hX'B
        have hDp := hChild votes support_votes hCounted B.parent hXB' hRB'
          (ancestorEq_refl _) D hD hDpar hDB (by rw [hbw D, hDb])
        refine ⟨hDp, ?_⟩
        by_cases hYw : B.parent ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads
        · rw [← hTestAgreeW B.parent hXB' hRB' (ancestorEq_refl _) hYw D hDpar]
          exact hDb
        · exact hbpTrue D (by
            rw [parent_eq_of_parent? hDpar]
            exact fun h => hYw (hViableEnd hRB' h)))
  -- `w`'s anchor and `X` are both ancestors of `B` (or `B`): one is an ancestor of the other
  have hMerge : H_w = B := by
    rcases ancestorEq_compatible hAnchorW hXB with hAwX | hXAw
    · -- `w`'s anchor is `X` or an ancestor of it: the shared block is `X`
      exact hMergeAt X (ancestorEq_refl X) hXBp hAwX (hXHw_of hAwX)
    · -- `w`'s anchor is a descendant of `X`, so `B` or an ancestor of `B`'s parent
      have hAwB : AnchorAt M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int) = B ∨
          (AnchorAt M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int)).AncestorEq B.parent := by
        cases B with
        | genesis => exact absurd rfl hBne
        | node q sl r vs sp ats v => exact (ancestorEq_node_iff _ q sl r vs sp ats v).1 hAnchorW
      rcases hAwB with hAwEq | hAwBp
      · -- `w`'s anchor is `B`: `B` has no child in `w`'s tree, so the walk from `B` ends at `B`
        rw [hAwEq] at hWalk
        exact GoldilocksCorrectness.Proofs.Routines.walkEnd_eq_of_walkSteps Relation.ReflTransGen.refl
          (fun D hD hDB => absurd hDB (hNoChildP D hD)) hWalk
      · -- `w`'s anchor is on `p`'s walk from `X` to `B`'s parent, and is the shared block
        exact hMergeAt _ hXAw hAwBp (ancestorEq_refl _)
          (GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_walkSteps hWalk.1)
  rw [hhead, hMerge]

/-- Lemma 24 with `head_height_floor` at `p` at most at `w`, and `B`'s parent passing `w`'s
viability test. The
proof; the audited statement is in `Statements/Executions/OrderedFloorStatements.lean`.

Roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`: Lemma 22 and Lemma 23, which the proof calls, take
blocks as held up to `w`'s vote time of slot `s + 1`;
`lem20le_goldfish_vote_names_honest_proposal` and `child_mem_proposer_viable_tree` read earlier.

The activity rows: `p` and `w` are each active from a tick to
a clock value at most `tStart`, more than both clock bounds before the read time
`M.supportCutoff S.C s - max (2 * Δ S) Δs` at slot `s`, up to their own ticks to the start and to the
vote time of slot `s + 1`; each voter of `Hs` is active through the sync delay after that read time
(`hHold`), and `p` through the sync delay after `max (Δ S) Δs` before the start of slot `s + 1`
(`hHoldP`); the voters of `Hs` are outside the adversary set at `w`'s tick to the vote time of slot
`s + 1`.

Restated with the delivery premises up to `M.voteTime S.C (s + 1)`: the proposal of slot `s + 1`
reaches `w` by then (`lem22_proposal_held_by_voter_upTo`,
`lem23_proposer_and_voter_count_alike_upTo`).

The proposer's window `hp` starts `max (Δ S) Δs` before the support cutoff of slot `s` and ends at the start of
slot `s + 1`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: Lemma 24 holds when `head_height_floor` at the voter is at least `head_height_floor` at
the proposer, and the proposal's parent passes the voter's viability test. -/
theorem lem24le_goldfish_vote_names_honest_proposal_composed_upTo
    (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.voteTime S.C (s + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.voteTime S.C (s + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`
    --
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ X.AncestorEq (H u))
    (hVoters : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes_w support_w →
      M.voters_count votes_w < 2 * Hs.card)
    -- each voter of `Hs` is active through the sync delay after the read time at slot `s`
    --
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `p`'s and `w`'s windows start at `tStart`, more than `ΔClockAhead + ΔClockBehind` before the read
    -- time at slot `s`
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ))
    -- `p` is active from a tick to a clock value at most `tStart` up to its tick to the start of slot
    -- `s + 1`
    (hp : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C (s + 1)))
    -- `p` is active through the sync delay after `max (Δ S) Δs` before the start of slot `s + 1`
    --
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` is active from a tick to a clock value at most `tStart` up to its tick to the vote time of
    -- slot `s + 1`
    (hw : w ∈ A.activeThroughoutToTick x tStart (M.voteTime S.C (s + 1)))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hOnly : ∀ B' ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree, B'.slot = s + 1 → B' = B)
    (hRootNew : ∀ B' ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree, B'.root ≠ B.root)
    (hF3p : ∃ W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree,
      W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads ∧ X.AncestorEq W)
    (hApX : (M.get_anchor (x.tickInput p (M.slotStart S.C (s + 1)))
      ((M.slotStart S.C (s + 1) : ℕ) : Int)).AncestorEq X)
    (hF2w : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq B)
    (hLocksW : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    (hParentViable : M.is_viable (x.tickInput w (M.voteTime S.C (s + 1))) B.parent = true)
    (hFloorLe : M.head_height_floor (x.tickInput p (M.slotStart S.C (s + 1))) ≤
      M.head_height_floor (x.tickInput w (M.voteTime S.C (s + 1)))) :
    vote.head = B.root := by
  classical
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  -- the times: `t₁ = cut(s) + 2Δ`, `vt(s + 1) = t₁ + Δ`
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s, Nat.mul_add, Nat.mul_one]
  have hc₀ : M.supportCutoff S.C s = M.voteTime S.C s + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have hv₁ : M.voteTime S.C s = M.slotStart S.C s + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hv₃ : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  have hmx12 : max (Δ S) Δs ≤ max (2 * Δ S) Δs := max_le_max (by omega) le_rfl
  have hcut1 : 1 ≤ M.supportCutoff S.C s := by omega
  -- the read times: `t₀ = cut(s) − max (2Δ) Δs` (Lemma 12's), `t₀' = t₁ − max Δ Δs` (Lemma 23's), `t₀ ≤ t₀'`
  have ht₀₀' : M.supportCutoff S.C s - max (2 * Δ S) Δs ≤ M.slotStart S.C (s + 1) - max (Δ S) Δs := by
    omega
  have ht₀'1 : M.slotStart S.C (s + 1) - max (Δ S) Δs + Δs ≤ M.slotStart S.C (s + 1) := by omega
  have hcR : ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ (M.supportCutoff S.C s : ℝ) := by
    exact_mod_cast Nat.sub_le _ _
  have h₀₀'R : ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤
      ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast ht₀₀'
  have ht₁R : (M.slotStart S.C (s + 1) : ℝ) = (M.supportCutoff S.C s : ℝ) + 2 * (Δ S : ℝ) := by
    have : M.slotStart S.C (s + 1) = M.supportCutoff S.C s + 2 * Δ S := by omega
    rw [this]; push_cast; ring
  have hv₃R : (M.voteTime S.C (s + 1) : ℝ) = (M.slotStart S.C (s + 1) : ℝ) + (Δ S : ℝ) := by
    rw [hv₃]; push_cast; ring
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  -- the step forms the callees read, from the two readers (re-check 55 section 2.6)
  have hpC : ∃ kR : ℕ, x.lbl kR = Event.tick p (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → p ∈ A.active j :=
    tick_window_of_activeThroughoutToTick_int M x R E
      (mem_activeThroughoutToTick_of_le_end_int M x R E hcut1 (by linarith) (by linarith) hp) (by linarith)
  have hwC : ∃ kR : ℕ, x.lbl kR = Event.tick w (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → w ∈ A.active j :=
    tick_window_of_activeThroughoutToTick_int M x R E
      (mem_activeThroughoutToTick_of_le_end_int M x R E hcut1 (by linarith) (by linarith) hw) (by linarith)
  have hpF : ∃ kP : ℕ, x.lbl kP = Event.tick p (M.slotStart S.C (s + 1)) ∧
      ∀ j : ℕ, ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kP →
        p ∈ A.active j :=
    tick_window_of_activeThroughoutToTick_int M x R E hp (by linarith)
  have hwF : ∃ kW : ℕ, x.lbl kW = Event.tick w (M.voteTime S.C (s + 1)) ∧
      ∀ j : ℕ, ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kW →
        w ∈ A.active j :=
    tick_window_of_activeThroughoutToTick_int M x R E hw (by linarith)
  have hHoldW : w ∈ A.activeThroughout x ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
    have h := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E hw
      (a' := M.slotStart S.C (s + 1) - max (Δ S) Δs) (e := M.slotStart S.C (s + 1) - max (Δ S) Δs + Δs)
      (by push_cast; linarith) (by
        have : ((M.slotStart S.C (s + 1) - max (Δ S) Δs + Δs : ℕ) : ℝ) ≤ (M.slotStart S.C (s + 1) : ℝ) := by
          exact_mod_cast ht₀'1
        linarith)
    rw [Nat.cast_add] at h
    exact h
  have hwR := tick_window_ahead_of_activeThroughoutToTick_int M x R E hw (c := M.slotStart S.C (s + 1))
    (by linarith)
  -- the two ticks Lemma 11 reads
  obtain ⟨i, hl, hsent⟩ := id hPropose
  obtain ⟨kW, hkW, -⟩ := Activity.mem_activeThroughoutToTick.1 hw
  have hpT : p ∉ A.corrupted (x.tickStep p (M.slotStart S.C (s + 1))) := by
    rw [(tickStep_eq_of_lbl M) x E hl]
    exact E.not_mem_corrupted_of_tick hl
  have hwT : w ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) := by
    rw [(tickStep_eq_of_lbl M) x E hkW]
    exact E.not_mem_corrupted_of_tick hkW
  have hInvW : M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1))) :=
    (lem11_node_invariant M F S A x R E (x.tickStep w (M.voteTime S.C (s + 1))) w hwT).1
  -- the real times of the ticks the roots rows read
  have hkWt : (M.voteTime S.C (s + 1) : ℝ) - ΔClockAhead ≤ x.time (x.tickStep w (M.voteTime S.C (s + 1))) := by
    rw [(tickStep_eq_of_lbl M) x E hkW]
    exact (E.tick_active kW w _ hkW).2.1
  -- the finalized blocks and the fork-choice roots (Lemma 46)
  have hF2p : (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).fc_root := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E _ p
  have hFroot : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E _ w
  -- step 1: the end of `p`'s walk
  obtain ⟨-, -, hBpar?, hEnd⟩ := (proposal_parent_walk_end M F U) S A x R E s i B p hl hsent
  have hPB : B.parent.AncestorEq B := ancestorEq_of_parent? hBpar?
  have hRXp : (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).fc_root.AncestorEq X :=
    ancestorEq_trans ((GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_get_anchor M F) _ _) hApX
  have hFXp : (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq X :=
    ancestorEq_trans hF2p hRXp
  -- step 2: `B`'s parent is in `p`'s tree, and `p`'s finalized block is an ancestor of `B`
  have hParentHeld : B.parent ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree := by
    rcases hEnd with hin | heq
    · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 hin).1).1
    · obtain ⟨W, hW, -, hXW⟩ := hF3p
      refine (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ p W B.parent (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hW).1 ?_
      rw [heq]
      exact ancestorEq_trans hApX hXW
  have hFpB : (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq B := by
    refine ancestorEq_trans ?_ hPB
    rcases hEnd with hin | heq
    · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 hin).1).2
    · rw [heq]
      exact ancestorEq_trans hF2p
        ((GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_get_anchor M F) _ _)
  -- step 3: `p` holds `B` after its tick (Lemma 22a), and `w` at its vote tick (Lemma 22)
  have hBp : B ∈ (x.st (i + 1) p).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem22a_proposer_holds_own_proposal M F U) S A x R s i B p
      E hl hsent hRootNew hParentHeld ((compatible_iff _ _).2 (Or.inl hFpB))
  have hFwB : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq B :=
    ancestorEq_trans hFroot hF2w
  have hBw : B ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree :=
    (GoldilocksCorrectness.Record.Proofs.Executions.lem22_proposal_held_by_voter_upTo M F U) S A x R GST s i B p
      w E hNet hSkew hRedeliver hRoots hParent (by omega) hwR hl hsent hBp
      ((compatible_iff _ _).2 (Or.inl hFwB))
  -- step 4: `B`'s parent and `B` reach `head_height_floor` at `w`: heights grow along ancestry
  -- (Lemma 47 (d))
  have hPw : B.parent ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w _ B.parent hBw hPB
  have hPfl : M.head_height_floor (x.tickInput w (M.voteTime S.C (s + 1))) ≤ (M.chainStateOf S.C B.parent).h :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.is_viable_iff M F) S.C S.P S.X _ hInvW B.parent hPw).1 hParentViable
  have hBfl : M.head_height_floor (x.tickInput w (M.voteTime S.C (s + 1))) ≤ (M.chainStateOf S.C B).h :=
    le_trans hPfl (((GoldilocksCorrectness.Record.Statements.Routines.lem47_chain_state_heights M F) S.C B.parent B).2.2.2.1 hPB)
  have hBVH : B ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hInvW B).2
      ⟨hBw, hFwB, hF2w, hBfl⟩
  have hBΦ : B ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hBw, hFwB⟩
  -- step 5: the two validators count alike (Lemma 23)
  have hCount := (GoldilocksCorrectness.Record.Proofs.Executions.lem23_proposer_and_voter_count_alike_upTo M F U)
    S A x R GST s B p w E hNet hSkew hRedeliver Sy hRoots hParent (by omega) hpF hwF hHoldP hHoldW hPropose hBΦ
    hOnly
  -- step 6: a viable head at `w` along the path is one at `p`; `B`'s parent is a viable head at
  -- `w` when the root of `w`'s fork choice is an ancestor of it
  have hViableLe := (viable_heads_le_of_floor_le_at M F) S A x R E
    (x.tickStep p (M.slotStart S.C (s + 1))) (x.tickStep w (M.voteTime S.C (s + 1))) X B p w hParentHeld hRXp
    hFloorLe
  have hViableEnd : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq B.parent →
      B.parent ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads →
      B.parent ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads :=
    fun hRP _ => ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hInvW B.parent).2
      ⟨hPw, ancestorEq_trans hFroot hRP, hRP, hPfl⟩
  -- step 7: every child in `w`'s viable tree of a block of the path, other than `B`, is in `p`'s
  have hpTime : x.time (x.tickStep p (M.slotStart S.C (s + 1))) ≤
      x.time (x.tickStep w (M.voteTime S.C (s + 1))) := by
    rw [(tickStep_eq_of_lbl M) x E hl]
    have := (E.tick_active i p _ hl).2.2
    linarith
  have hChild := (child_mem_proposer_viable_tree_upTo M F U) S A x R GST s X B p w (E.mono (by omega)) hNet hSkew hRedeliver
    (Sy.mono (by omega))
    ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hpTime hRoots) hParent
    (by omega) hpF hwF hHoldW hOnly hEnd hApX hFloorLe
  -- step 8: Lemma 20, with roots up to the two ticks to the support cutoff of slot `s`
  obtain ⟨kpC, hkpC, -⟩ := id hpC
  obtain ⟨kwC, hkwC, -⟩ := id hwC
  have hRoots20 : RootsNameBlocksUntil M A x (max (x.time (x.tickStep p (M.supportCutoff S.C s)))
      (x.time (x.tickStep w (M.supportCutoff S.C s)))) := by
    refine (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) ?_ hRoots
    rw [(tickStep_eq_of_lbl M) x E hkpC, (tickStep_eq_of_lbl M) x E hkwC]
    have h1 := (E.tick_active kpC p _ hkpC).2.2
    have h2 := (E.tick_active kwC w _ hkwC).2.2
    exact max_le (by linarith) (by linarith)
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem20le_goldfish_vote_names_honest_proposal_upTo M F U) S
    A x R GST s Hs H X B p w vote (E.mono (by omega)) hNet hSkew hRedeliver (Sy.mono (by omega)) hΔs hRoots20 hParent hOwner hGST hHs
    hVoters hHold hpC hwC hPropose hSend hBw hF3p hApX hLocksW hBVH hViableLe hViableEnd
    (fun vp sp vw sw h₁ h₂ => ⟨fun Y hXY hRY _ D hD => (hCount vp sp vw sw h₁ h₂).1 D
        (ancestorEq_trans hFXp (ancestorEq_trans hXY (ancestorEq_of_parent? hD)))
        (ancestorEq_trans hFroot (ancestorEq_trans hRY (ancestorEq_of_parent? hD))),
      (hCount vp sp vw sw h₁ h₂).2⟩)
    (fun _ _ _ Y hXY _ hYB D hD hDpar hDB _ => hChild Y hXY hYB D hD hDpar hDB)

/-- Lemma 59 with `φ ≤ φ_w` and `φ_w` at most `B`'s parent's chain-state height, `φ` and `φ_w`
being `head_height_floor` at `p` and at `w`. The proof; the
audited statement is in `Statements/Executions/OrderedFloorStatements.lean`.

Roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`: Lemma 22 and
`lem24le_goldfish_vote_names_honest_proposal_composed`, which the proof calls, take blocks as
held up to `w`'s vote time of slot `s + 1`.

The activity rows: `p` and `w` are each active from a tick to
a clock value at most `tStart`, more than both clock bounds before the read time
`M.supportCutoff S.C s - max (2 * Δ S) Δs` at slot `s`, up to their own ticks to the start and to the
vote time of slot `s + 1`; each voter of `Hs` is active through the sync delay after that read time
(`hHold`), and `p` through the sync delay after `max (Δ S) Δs` before the start of slot `s + 1`
(`hHoldP`); the voters of `Hs` are outside the adversary set at `w`'s tick to the vote time of slot
`s + 1`.

Restated with the delivery premises up to `M.voteTime S.C (s + 1)`: the proposal of slot `s + 1`
reaches `w` by then (`lem22_proposal_held_by_voter_upTo`,
`lem23_proposer_and_voter_count_alike_upTo`).

The proposer's window `hp` starts `max (Δ S) Δs` before the support cutoff of slot `s` and ends at the start of
slot `s + 1`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: when `head_height_floor` at the voter is at least `head_height_floor` at the proposer
and at most the height of the proposal's parent, the voter's vote names the proposal. -/
theorem lem59le_goldfish_vote_names_honest_proposal_frame_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V) (ρ_p ρ_w : Block V) (φ φ_w : Height)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.voteTime S.C (s + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.voteTime S.C (s + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`
    --
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ X.AncestorEq (H u))
    (hVoters : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes_w support_w →
      M.voters_count votes_w < 2 * Hs.card)
    -- each voter of `Hs` is active through the sync delay after the read time at slot `s`
    --
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `p`'s and `w`'s windows start at `tStart`, more than `ΔClockAhead + ΔClockBehind` before the read
    -- time at slot `s`
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ))
    -- `p` is active from a tick to a clock value at most `tStart` up to its tick to the start of slot
    -- `s + 1`
    (hp : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C (s + 1)))
    -- `p` is active through the sync delay after `max (Δ S) Δs` before the start of slot `s + 1`
    --
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` is active from a tick to a clock value at most `tStart` up to its tick to the vote time of
    -- slot `s + 1`
    (hw : w ∈ A.activeThroughoutToTick x tStart (M.voteTime S.C (s + 1)))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hOnly : ∀ B' ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree, B'.slot = s + 1 → B' = B)
    (hRootNew : ∀ B' ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree, B'.root ≠ B.root)
    (hShapeP : FrameShape M (x.tickInput p (M.slotStart S.C (s + 1))) ρ_p φ)
    (hShapeW : FrameShape M (x.tickInput w (M.voteTime S.C (s + 1))) ρ_w φ_w)
    (hFloorLe : φ ≤ φ_w)
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree,
      X.AncestorEq W ∧ ρ_p.AncestorEq W ∧ φ ≤ (M.chainStateOf S.C W).h)
    (hApX : (M.get_anchor (x.tickInput p (M.slotStart S.C (s + 1)))
      ((M.slotStart S.C (s + 1) : ℕ) : Int)).AncestorEq X)
    (hRootW : ρ_w.AncestorEq B)
    (hLocksW : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    (hParentHeight : φ_w ≤ (M.chainStateOf S.C B.parent).h) :
    vote.head = B.root := by
  -- the two ticks, and the honesty Lemma 11 reads there
  obtain ⟨kW, hkW, -⟩ := Activity.mem_activeThroughoutToTick.1 hw
  obtain ⟨i, hl, hsent⟩ := id hPropose
  have hpT : p ∉ A.corrupted (x.tickStep p (M.slotStart S.C (s + 1))) := by
    rw [(tickStep_eq_of_lbl M) x E hl]
    exact E.not_mem_corrupted_of_tick hl
  have hwT : w ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) := by
    rw [(tickStep_eq_of_lbl M) x E hkW]
    exact E.not_mem_corrupted_of_tick hkW
  -- Lemma 56 at the two shapes (at the node invariant of each tick input)
  have hInvP : M.nodeInv S.C S.P S.X (x.tickInput p (M.slotStart S.C (s + 1))) :=
    (lem11_node_invariant M F S A x R E (x.tickStep p (M.slotStart S.C (s + 1))) p hpT).1
  have hInvW : M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1))) :=
    (lem11_node_invariant M F S A x R E (x.tickStep w (M.voteTime S.C (s + 1))) w hwT).1
  obtain ⟨hRp, -, hHp⟩ := (GoldilocksCorrectness.Record.Statements.Routines.lem56_frame_of_shape M F)
    S.C S.P S.X _ hInvP _ _ hShapeP
  obtain ⟨hRw, hVw, -⟩ := (GoldilocksCorrectness.Record.Statements.Routines.lem56_frame_of_shape M F)
    S.C S.P S.X _ hInvW _ _ hShapeW
  -- Lemma 46: each finalized block is its fork-choice root or an ancestor of it
  have hFρp : (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq ρ_p := by
    rw [← hShapeP.1]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E _ p
  have hFρw : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq ρ_w := by
    rw [← hShapeW.1]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E _ w
  have hF2p : (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).fc_root := by
    rw [hRp]
    exact hFρp
  have hF2w : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq B := by
    rw [hRw]
    exact hRootW
  -- a viable head of `p`'s frame that is `X` or a descendant of `X`
  have hF3p : ∃ W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree,
      W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads ∧ X.AncestorEq W := by
    obtain ⟨W, hW, hXW, hρW, hφW⟩ := hHeadP
    have hFW := ancestorEq_trans hFρp hρW
    exact ⟨W, ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hW, hFW⟩,
      (hHp W).2 ⟨hW, hFW, hρW, hφW⟩, hXW⟩
  -- `w` holds `B` at its tick input: steps 1 to 3 of Lemma 24's proof
  obtain ⟨-, -, hBpar?, hEnd⟩ := (proposal_parent_walk_end M F U) S A x R E s i B p hl hsent
  have hPB : B.parent.AncestorEq B := ancestorEq_of_parent? hBpar?
  have hParentHeld : B.parent ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree := by
    rcases hEnd with hin | heq
    · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 hin).1).1
    · obtain ⟨W, hW, -, hXW⟩ := hF3p
      refine (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ p W B.parent (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hW).1 ?_
      rw [heq]
      exact ancestorEq_trans hApX hXW
  have hFpB : (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq B := by
    refine ancestorEq_trans ?_ hPB
    rcases hEnd with hin | heq
    · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 hin).1).2
    · rw [heq]
      exact ancestorEq_trans hF2p
        ((GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_get_anchor M F) _ _)
  have hBp : B ∈ (x.st (i + 1) p).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem22a_proposer_holds_own_proposal M F U) S A x R s i B p
      E hl hsent hRootNew hParentHeld ((compatible_iff _ _).2 (Or.inl hFpB))
  have hFwB : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq B :=
    ancestorEq_trans hFρw hRootW
  -- `w`'s step form from more than both clock bounds before the start of slot `s + 1`, from its reader
  have hwR := (tick_window_ahead_of_activeThroughoutToTick_int M x R E hw (c := M.slotStart S.C (s + 1)) (by
    have hc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_le_slotStart_succ M.toSlotLayout F.sched) S s
    have h1 : ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ (M.slotStart S.C (s + 1) : ℝ) := by
      exact_mod_cast (Nat.sub_le _ _).trans hc
    linarith))
  have hBw : B ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree :=
    (GoldilocksCorrectness.Record.Proofs.Executions.lem22_proposal_held_by_voter_upTo M F U) S A x R GST s i B p
      w E hNet hSkew hRedeliver hRoots hParent
      (by have := le_max_left (Δ S) Δs
          have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
          omega) hwR hl hsent hBp
      ((compatible_iff _ _).2 (Or.inl hFwB))
  -- `B`'s parent passes `w`'s viability test: `w` holds it
  have hParentViable : M.is_viable (x.tickInput w (M.voteTime S.C (s + 1))) B.parent = true :=
    (hVw B.parent ((GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w _
      B.parent hBw hPB)).2 hParentHeight
  -- `head_height_floor` at `p` and at `w` are `φ` and `φ_w`
  have hFloorLe' : M.head_height_floor (x.tickInput p (M.slotStart S.C (s + 1))) ≤
      M.head_height_floor (x.tickInput w (M.voteTime S.C (s + 1))) := by
    rw [hShapeP.2, hShapeW.2]
    exact hFloorLe
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem24le_goldfish_vote_names_honest_proposal_composed_upTo M F U) S A x R GST s Hs H X B p w
    vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs hVoters hHold tStart htStart hp hHoldP hw hPropose hSend
    hOnly hRootNew hF3p hApX hF2w hLocksW hParentViable hFloorLe'

end GoldilocksCorrectness.Record.Proofs.Executions

