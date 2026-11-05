module
public import GoldilocksCorrectness.Proofs.Executions.OrderedFloorVotes
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatementsUpTo
public import GoldilocksCorrectness.Proofs.Executions.ViableAgreementUpTo
public import GoldilocksCorrectness.Statements.Executions.ProposalPropagationStatementsUpTo
public import GoldilocksCorrectness.Statements.Executions.CountAgreementStatementsUpTo

@[expose] public section

/-!
# `OrderedFloorVotes.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/OrderedFloorVotes.lean` that name a
delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the
deadlines. The bound of
each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in
the twin's own parameters.

* `lem20le_goldfish_vote_names_honest_proposal`,
  `lem24le_goldfish_vote_names_honest_proposal_composed`,
  `lem59le_goldfish_vote_names_honest_proposal_frame`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem supportCutoff_eq
  viewFreeze_eq voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree mem_viable_heads_iff)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

open GoldilocksCorrectness.Proofs.Routines (goldfish_eligible_of_parent_not_viable
  goldfish_eligible_of_parent_viable path_test_of_test_imp)

open GoldilocksCorrectness.Proofs.Routines (fc_root_eq mem_viable_tree_iff)

open GoldilocksCorrectness.Proofs.Routines (block_well_formed_iff goldfish_fork_choice_eq
  is_viable_iff mem_included_support_votes_iff mem_included_votes_iff)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (StartsTowards RootsNameBlocksIn VotesOnceFor
  CountedVotes ProposalCountedVotes expireLocks FrameShape)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  fc_root_ancestorEq_get_anchor mem_voter_block_tree_iff ac_valid_payload_facts
  occurrenceBefore_eq_true_iff ancestorEq_of_parent? parent?_eq_some_parent parent_eq_of_parent?
  goldfish_eligible_answers goldfish_eligible_current_slot goldfish_eligible_congr
  get_anchor_ancestorEq_of_entries proposalCountedVotes_of_lists path_test_of_test_agree
  ancestorEq_compatible ghost_spec ghost_reaches ghost_step_none_of_no_child ancestorEq_antisymm
  ancestorEq_node_iff)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Lemma 20 with the viable heads along the path agreeing in one direction, and `B`'s parent viable
at `w` when it is at `p`. The proof; the audited statement is in
`Statements/Executions/OrderedFloorStatements.lean`.

Roots name blocks until `supportCutoff S s`: the bound of the two Lemma 12 calls at slot `s` the
proof passes the premise to, as Lemma 20's.

Restated with the delivery premises up to `supportCutoff S s`: the slot-`s` votes reach `p` and `w` by then (`lem12_honest_vote_delivered_until_upTo`). -/
theorem lem20le_goldfish_vote_names_honest_proposal_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    -- the slot-`s` votes of `Hs` for `X`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (voteTime S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ X.AncestorEq (H u))
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes_w support_w →
      voters_count votes_w < 2 * Hs.card)
    -- the proposer `p` and the voter `w`
    (hp : ∀ t : ℕ, voteTime S s ≤ t → t ≤ supportCutoff S s →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    (hw : ∀ t : ℕ, voteTime S s ≤ t → t ≤ supportCutoff S s →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    -- `w` holds `B` before its vote
    (hBw : B ∈ (stateBefore x (voteTime S (s + 1)) w).S.T)
    -- the finality-gadget condition at `p`, on its state before `slotStart S (s + 1)`
    (hF3p : ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree,
      W ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads ∧ X.AncestorEq W)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      ((slotStart S (s + 1) : ℕ) : Int)).AncestorEq X)
    -- every live lock entry `w`'s revocation leaves is on `B` or an ancestor of `B`
    (hLocksW : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `B` is a viable head at `w`
    (hBViable : B ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads)
    -- the two validators agree on the viable heads along the path from `X` to `B`'s parent, on
    -- the blocks of it that have the root of `w`'s fork choice as an ancestor (or are that root)
    (hViableLe : ∀ Y : Block V, X.AncestorEq Y →
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq Y →
      Y.AncestorEq B.parent →
      Y ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads →
      Y ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads)
    -- `B`'s parent, when the root of `w`'s fork choice is an ancestor of it (or it), is a viable
    -- head at `w` when it is one at `p`
    (hViableEnd : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq B.parent →
      B.parent ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads →
      B.parent ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads)
    -- the two validators count alike: the same score on every child of a block from `X` to
    -- `B`'s parent that has the root of `w`'s fork choice as an ancestor (or is that root), the
    -- same number of voters
    (hCount : ∀ votes_p support_p votes_w support_w : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S (s + 1)) p).A
        (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) s votes_p support_p →
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes_w support_w →
      (∀ Y : Block V, X.AncestorEq Y →
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq Y →
        Y.AncestorEq B.parent →
        ∀ D : Block V, D.parent? = some Y → ∃ n : ℕ,
          goldfish_score (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) votes_p support_p s
            D = .ok n ∧
          goldfish_score (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) votes_w support_w s
            D = .ok n) ∧
      voters_count votes_p = voters_count votes_w)
    -- every child in `w`'s viable tree of a block from `X` to `B`'s parent that has the root of
    -- `w`'s fork choice as an ancestor (or is that root), other than `B`, that `w`'s eligibility
    -- test accepts, is in `p`'s viable tree
    (hChild : ∀ (vbt : Finset (Block V)) (votes_w support_w : Finset (GoldfishVote V)),
      voter_block_tree S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) = .ok vbt →
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes_w support_w →
      ∀ Y : Block V, X.AncestorEq Y →
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq Y →
        Y.AncestorEq B.parent →
        ∀ D ∈ viable_tree (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) vbt,
          D.parent? = some Y → D ≠ B →
          goldfish_eligible S.C (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
            ((voteTime S (s + 1) : ℕ) : Int) votes_w support_w s D = .ok true →
          D ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
            (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) :
    vote.head = B.root := by
  have hF2p : (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).fc_root :=
    by rw [fc_root_eq]; exact F_ancestorEq_fc_root_of_stateBefore S Sched x (slotStart S (s + 1)) p
  have hF2w : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root :=
    by rw [fc_root_eq]; exact F_ancestorEq_fc_root_of_stateBefore S Sched x (voteTime S (s + 1)) w
  -- step 0: the times
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss' : slotStart S (s + 1 + 1) = slotStart S (s + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₁ : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hc₀ : supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S s
  have hslot₁ : S.C.slot ((slotStart S (s + 1) : ℕ) : Int) = s + 1 :=
    slot_eq_of_mem S (le_refl _) (by omega)
  have hslot₃ : S.C.slot ((voteTime S (s + 1) : ℕ) : Int) = s + 1 :=
    slot_eq_of_mem S (by omega) (by omega)
  have hfreeze : ∀ a d : Int, 0 < d → a + 2 * d < a + 3 * d := by
    intro a d hd
    omega
  have h23 : ((S.C.t_ s + 2 * S.C.Δ : Time) : Stamp) < ((S.C.t_ s + 3 * S.C.Δ : Time) : Stamp) :=
    WithBot.coe_lt_coe.2 (hfreeze _ _ S.C.Δ_pos)
  -- step 1: `p`'s run and proposal
  obtain ⟨i₁, hl₁, hm₁⟩ := hPropose
  have hi₁ : stepBefore x (slotStart S (s + 1)) = i₁ := stepBefore_eq_of_lbl x hl₁
  have hti₁ : x[i₁].time + 1 = slotStart S (s + 1) := (time_of_lbl_tickAllAwake x hl₁).1
  obtain ⟨-, n₁', sent₁, hrun₁, hB₁⟩ := tick_send_of_honestSendAt hl₁ hm₁
  have hRootsΦp : RootsNameBlocksIn (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ p
  have hAp : (tickInputState x i₁ (slotStart S (s + 1)) p).A =
      (stateBefore x (slotStart S (s + 1)) p).A := by
    rw [(tickInputState_frame x i₁ _ p).2.1]
    unfold stateBefore
    rw [hi₁]
  have hSp : (tickInputState x i₁ (slotStart S (s + 1)) p).S =
      (stateBefore x (slotStart S (s + 1)) p).S := by
    rw [(tickInputState_frame x i₁ _ p).1]
    unfold stateBefore
    rw [hi₁]
  obtain ⟨-, -, -, Hp, votes_pl, support_pl, hvl, hsl, hWalkP, hBdef⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem19_tick_proposes S.C S.P S.X _ n₁' _ sent₁ B
      hrun₁ hB₁
  rw [hslot₁, Nat.add_sub_cancel, hAp] at hvl
  rw [hAp, hSp] at hsl
  rw [hslot₁, Nat.add_sub_cancel, hAp, hSp] at hWalkP
  rw [hslot₁] at hBdef
  have hPCV : ProposalCountedVotes (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) s votes_pl.toFinset
      support_pl.toFinset :=
    proposalCountedVotes_of_lists _ _ s votes_pl support_pl hvl hsl
  have hBpar : B.parent = Hp := by rw [hBdef]; rfl
  have hBslot : B.slot = s + 1 := by rw [hBdef]; rfl
  have hBne : B ≠ Block.genesis := by rw [hBdef]; exact fun h => by cases h
  have hBpar? : B.parent? = some Hp := by rw [hBdef]; rfl
  -- step 2: `w`'s run and walk
  obtain ⟨i, hl, hm⟩ := hSend
  have hi : stepBefore x (voteTime S (s + 1)) = i := stepBefore_eq_of_lbl x hl
  have hti : x[i].time + 1 = voteTime S (s + 1) := (time_of_lbl_tickAllAwake x hl).1
  obtain ⟨-, n', sent, hrun, hvote⟩ := tick_send_of_honestSendAt hl hm
  have hRootsΦ : RootsNameBlocksIn (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ w
  have hA : (tickInputState x i (voteTime S (s + 1)) w).A =
      (stateBefore x (voteTime S (s + 1)) w).A := by
    rw [(tickInputState_frame x i _ w).2.1]
    unfold stateBefore
    rw [hi]
  have hS : (tickInputState x i (voteTime S (s + 1)) w).S =
      (stateBefore x (voteTime S (s + 1)) w).S := by
    rw [(tickInputState_frame x i _ w).1]
    unfold stateBefore
    rw [hi]
  obtain ⟨-, -, -, -, A', votes, support_votes, vbt, H_w, hRevoke, hCounted, hvbt, hWalk, hhead,
      -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem14_tick_vote_walk S.C S.P S.X _ n' _ sent vote
      hrun hvote
  rw [hslot₃, hA, hS] at hRevoke hCounted hvbt
  rw [hslot₃, hS, Nat.add_sub_cancel] at hWalk
  have hCv := hCounted.1
  have hCs := hCounted.2
  simp only [Nat.add_sub_cancel] at hCv hCs
  -- step 3: the delivered votes at `p` before `t₁`; `p`'s finalized block is an ancestor of each
  -- `H u`, through the root of its fork choice, its anchor and `X`
  have hHeldP : ∀ u ∈ Hs, HeldEarlyVoteFor S.C (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) s (H u) u :=
    GoldilocksCorrectness.Statements.Executions.lem12_honest_vote_delivered_until_upTo S Sched x GST s
      (slotStart S (s + 1)) Hs H p hDiv hMono hSync hCatch hRoots hParent hOwner hGST
      (by omega)
      (fun u hu => ⟨(hHs u hu).1, fun h => (hHs u hu).2.1 (hMono _ _ (by omega) h),
        (hHs u hu).2.2.1, (hHs u hu).2.2.2.1⟩) hp
      (fun u hu => ancestorEq_trans hF2p (ancestorEq_trans (fc_root_ancestorEq_get_anchor _ _ _)
        (ancestorEq_trans hApX (hHs u hu).2.2.2.2)))
  have hVotersW : voters_count votes < 2 * Hs.card := hVoters votes support_votes hCounted
  obtain ⟨u₀, hu₀⟩ : Hs.Nonempty := Finset.card_pos.1 (by omega)
  -- step 4: the roots name blocks at `p` and at `w` (`hRootsΦp`, `hRootsΦ`, steps 1 and 2)
  -- step 5: the two validators count alike, on the children of the blocks from `X` to `B`'s
  -- parent; so `p`'s voters are fewer than twice `Hs`, as `w`'s are
  obtain ⟨hScore, hVotersEq⟩ := hCount _ _ _ _ hPCV hCounted
  have hVotersP : voters_count votes_pl.toFinset < 2 * Hs.card := hVotersEq ▸ hVotersW
  obtain ⟨n, hn⟩ : ∃ n : Block V → ℕ, ∀ Y : Block V, X.AncestorEq Y →
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq Y →
      Y.AncestorEq B.parent → ∀ D : Block V, D.parent? = some Y →
        goldfish_score (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) votes_pl.toFinset
          support_pl.toFinset s D = .ok (n D) ∧
        goldfish_score (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) votes support_votes s
          D = .ok (n D) := by
    classical
    refine ⟨fun D => if h : ∃ m : ℕ,
        goldfish_score (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) votes_pl.toFinset
          support_pl.toFinset s D = .ok m ∧
        goldfish_score (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) votes support_votes s
          D = .ok m then Classical.choose h else 0, ?_⟩
    intro Y hXY hRY hYB D hD
    have h := hScore Y hXY hRY hYB D hD
    simp only [dif_pos h]
    exact Classical.choose_spec h
  -- step 6: `p`'s start
  have hHu₀T : H u₀ ∈ (stateBefore x (slotStart S (s + 1)) p).S.T :=
    ((mem_fg_to_ac_tree _ _).1 (hHeldP u₀ hu₀).2.2.1).1
  have hStartP : StartsTowards (get_anchor (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) ((slotStart S (s + 1) : ℕ) : Int)) X
      (viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
        (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) := by
    obtain ⟨W, hW, hWv, hXW⟩ := hF3p
    refine GoldilocksCorrectness.Statements.Routines.lem7_startsTowards_of_compatible _ _ _ X W
      ((compatible_iff _ _).2 (Or.inl hApX)) (fc_root_ancestorEq_get_anchor _ _ _) ?_ ⟨hW, hWv⟩
      hXW
    intro P hAP _ hPX
    have hPH : P.AncestorEq (H u₀) := ancestorEq_trans hPX (hHs u₀ hu₀).2.2.2.2
    have hPT : P ∈ (stateBefore x (slotStart S (s + 1)) p).S.T :=
      ancestors_mem_T_of_exec S Sched x _ p _ P hHu₀T hPH
    have hFP : (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq P :=
      ancestorEq_trans hF2p (ancestorEq_trans (fc_root_ancestorEq_get_anchor _ _ _) hAP)
    exact (mem_fg_to_ac_tree _ _).2 ⟨hPT, hFP⟩
  -- step 7: `p`'s fork choice, so `X` is `B`'s parent or an ancestor of it
  have hSupportP : support_pl.toFinset ⊆ votes_pl.toFinset := by
    intro vote' hv
    rw [hPCV.1]
    exact ((hPCV.2 vote').1 hv).1
  have hVotesP : ∀ u ∈ Hs, VotesOnceFor (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      votes_pl.toFinset support_pl.toFinset s X u := by
    intro u hu
    obtain ⟨hpool, -, hHΦ, ⟨y, hy, -⟩, huniq⟩ := hHeldP u hu
    refine ⟨GoldfishVote.mk u s (H u).root, (hPCV.2 _).2 ⟨hpool, y, hy⟩, rfl, rfl,
      ⟨H u, hHΦ, rfl, (hHs u hu).2.2.2.2⟩, ?_⟩
    intro vote' hv' hi'
    rw [hPCV.1] at hv'
    exact huniq vote' hv' hi'
  have hXH : X.AncestorEq Hp :=
    GoldilocksCorrectness.Statements.Routines.lem2_goldfish_fork_choice_extends_majority_block
      S.C _ _ votes_pl.toFinset support_pl.toFinset s _ X Hp _ Hs hStartP hRootsΦp hSupportP
      hVotesP hVotersP hWalkP
  have hHB : Hp.AncestorEq B := ancestorEq_of_parent? hBpar?
  have hXB : X.AncestorEq B := ancestorEq_trans hXH hHB
  have hXBp : X.AncestorEq B.parent := hBpar ▸ hXH
  have hBpB : B.parent.AncestorEq B := hBpar ▸ hHB
  -- step 8: `B` is in `w`'s frame tree
  have hRB : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq B :=
    ((mem_viable_heads_iff _ _).1 hBViable).2.2.1
  have hBΦ : B ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree :=
    (mem_fg_to_ac_tree _ _).2 ⟨hBw, ancestorEq_trans hF2w hRB⟩
  -- every ancestor of `B` that has the root of `w`'s fork choice as an ancestor is in `w`'s frame
  -- tree
  have hAncΦ : ∀ Y : Block V, (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq Y →
      Y.AncestorEq B → Y ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree := by
    intro Y hRY hYB
    exact (mem_fg_to_ac_tree _ _).2 ⟨ancestors_mem_T_of_exec S Sched x _ w _ Y hBw hYB,
      ancestorEq_trans hF2w hRY⟩
  -- step 9: `w`'s anchor is `B` or an ancestor of it
  have hAnchorW : (get_anchor A' (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
      ((voteTime S (s + 1) : ℕ) : Int)).AncestorEq B :=
    get_anchor_ancestorEq_of_entries A' (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
      ((voteTime S (s + 1) : ℕ) : Int) B
      (hLocksW A' hRevoke) hRB
  have hRAw : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq
      (get_anchor A' (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int)) :=
    fc_root_ancestorEq_get_anchor _ _ _
  -- step 10: every block of `Φ_w.tree` that is `B` or an ancestor of `B` is in the voter's tree,
  -- and in `tree_w` when the root of the fork choice is an ancestor of it
  have hInVbt : ∀ Y ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree,
      Y.AncestorEq B → Y ∈ vbt := by
    intro Y hY hYB
    have hYT := ((mem_fg_to_ac_tree _ _).1 hY).1
    have hst := (lem11_node_invariant S Sched x (stepBefore x (voteTime S (s + 1))) w).1.2.2.2.2.1
      Y hYT
    obtain ⟨τ, hτ⟩ := Option.ne_none_iff_exists'.1 hst
    exact (mem_voter_block_tree_iff S.C _ _ (s + 1) vbt hvbt Y).2
      ⟨hY, τ, hτ, Or.inr ⟨B, hBΦ, hBslot, hYB⟩⟩
  have hInTree : ∀ Y ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree,
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq Y →
      Y.AncestorEq B →
      Y ∈ viable_tree (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) vbt := by
    intro Y hY hRY hYB
    rw [mem_viable_tree_iff]
    exact ⟨hInVbt Y hY hYB, hRY, B,
      Finset.mem_inter.2 ⟨hInVbt B hBΦ (ancestorEq_refl B), hBViable⟩, hYB⟩
  -- step 11: when `w`'s anchor is `X` or an ancestor of `X`, `w`'s walk passes `X`: Lemma 7 for
  -- the start, then Lemma 2 with `Sup := Hs` and `X` for `R`
  have hXHw_of : (get_anchor A' (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
      ((voteTime S (s + 1) : ℕ) : Int)).AncestorEq X → X.AncestorEq H_w := by
    intro hAwX
    have hFXw : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq X :=
      ancestorEq_trans hF2w (ancestorEq_trans hRAw hAwX)
    have hHeld : ∀ u ∈ Hs, HeldEarlyVoteFor S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) s (H u) u :=
      GoldilocksCorrectness.Statements.Executions.lem12_honest_vote_delivered_upTo S Sched x GST s Hs H
        w hDiv hMono hSync hCatch hRoots hParent hOwner hGST
        (fun u hu => ⟨(hHs u hu).1, (hHs u hu).2.1, (hHs u hu).2.2.1, (hHs u hu).2.2.2.1⟩)
        hw (fun u hu => ancestorEq_trans hFXw (hHs u hu).2.2.2.2)
    have hStartW : StartsTowards (get_anchor A'
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) ((voteTime S (s + 1) : ℕ) : Int)) X
        (viable_tree (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) vbt) := by
      refine GoldilocksCorrectness.Statements.Routines.lem7_startsTowards_of_compatible _ vbt _ X B
        ((compatible_iff _ _).2 (Or.inl hAwX)) (fc_root_ancestorEq_get_anchor _ _ _) ?_
        ⟨hInVbt B hBΦ (ancestorEq_refl B), hBViable⟩ hXB
      intro P hAP _ hPX
      have hPB : P.AncestorEq B := ancestorEq_trans hPX hXB
      exact hInVbt P (hAncΦ P (ancestorEq_trans (fc_root_ancestorEq_get_anchor _ _ _) hAP) hPB)
        hPB
    have hBne' : ∀ B' : Block V, B'.slot = s + 1 → B' ≠ Block.genesis := by
      rintro B' hBs rfl
      exact Nat.succ_ne_zero s hBs.symm
    have hPayload : ∀ B' ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree,
        B'.slot = s + 1 → ac_valid_payload S.P B' = true := by
      intro B' hB' hBs
      have hBT := ((mem_fg_to_ac_tree _ _).1 hB').1
      have hwf := (((lem11_node_invariant S Sched x (stepBefore x (voteTime S (s + 1)))
        w).1.2.2.1).2 B' hBT (hBne' B' hBs)).2.1
      rw [block_well_formed_iff] at hwf
      exact hwf.1.2
    have hIncl : ∀ vote' ∈ included_votes (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        (s + 1), ∃ B' ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree,
          B'.slot = s + 1 ∧ vote' ∈ B'.votes ∧ vote'.slot = s := by
      intro vote' hv
      simp only [mem_included_votes_iff,
        Nat.add_sub_cancel] at hv
      obtain ⟨B', ⟨hB', hBs⟩, hvB, hvs⟩ := hv
      exact ⟨B', hB', hBs, hvB, hvs⟩
    have hSupport : support_votes ⊆ votes := by
      intro vote' hv
      rcases (hCs vote').1 hv with ⟨hp', hτ, -⟩ | ⟨hinc, -⟩
      · exact (hCv vote').2 (Or.inl ⟨hp', hτ⟩)
      · simp only [mem_included_support_votes_iff,
          Nat.add_sub_cancel] at hinc
        obtain ⟨B', ⟨hB', hBs⟩, hvB, hvs⟩ := hinc
        have hvB' : vote' ∈ B'.votes :=
          (ac_valid_payload_facts S.P B' (hPayload B' hB' hBs)).2.1 vote' hvB
        refine (hCv vote').2 (Or.inr ?_)
        simp only [mem_included_votes_iff,
          Nat.add_sub_cancel]
        exact ⟨B', ⟨hB', hBs⟩, hvB', hvs⟩
    have ht₁₃ : voteTime S s ≤ voteTime S (s + 1) := by
      rw [voteTime_succ]
      omega
    have hVotes : ∀ u ∈ Hs, VotesOnceFor (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        votes support_votes s X u := by
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
        exact included_vote_eq_of_owner S Sched x (voteTime S (s + 1)) j₁ (voteTime S s) w u B'
          _ vote' hDiv hMono hOwner hhon ((mem_fg_to_ac_tree _ _).1 hB').1 (hBne' B' hBs) hvB hi'
          hlj₁ ht₁₃ hsent₁ hvs
    exact GoldilocksCorrectness.Statements.Routines.lem2_goldfish_fork_choice_extends_majority_block
      S.C _ _ votes support_votes s _ X H_w _ Hs hStartW hRootsΦ hSupport hVotes hVotersW hWalk
  -- step 12: the merge, Lemma 9
  have hRootsP : RootsNameBlocksIn (viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) :=
    fun B₁ hB₁ B₂ hB₂ hroot =>
      hRootsΦp B₁ ((mem_viable_tree_iff _ _ _).1 hB₁).1 B₂ ((mem_viable_tree_iff _ _ _).1 hB₂).1 hroot
  have hTestP := fun D : Block V => Classical.choose_spec
    (goldfish_eligible_answers S.C hRootsΦp ((slotStart S (s + 1) : ℕ) : Int) votes_pl.toFinset
      support_pl.toFinset s D)
  have hTestW := fun D : Block V => Classical.choose_spec
    (goldfish_eligible_answers S.C hRootsΦ ((voteTime S (s + 1) : ℕ) : Int) votes support_votes s
      D)
  have hSlot : S.C.slot ((slotStart S (s + 1) : ℕ) : Int) =
      S.C.slot ((voteTime S (s + 1) : ℕ) : Int) := hslot₁.trans hslot₃.symm
  -- `B` is eligible at `w`, a block of the current slot
  have hPTest : Classical.choose (goldfish_eligible_answers S.C hRootsΦ
      ((voteTime S (s + 1) : ℕ) : Int) votes support_votes s B) = true :=
    Except.ok.inj ((hTestW B).symm.trans (goldfish_eligible_current_slot S.C _ _ _ _ s B
      (hBslot.trans hslot₃.symm)))
  -- no block of `w`'s tree is a child of `B`
  have hNoChildP : ∀ D ∈ viable_tree (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) vbt,
      D.parent? ≠ some B := by
    intro D hD hDB
    have hDvbt := ((mem_viable_tree_iff _ _ _).1 hD).1
    have hDΦ := ((mem_voter_block_tree_iff S.C _ _ (s + 1) vbt hvbt D).1 hDvbt).1
    have hDT := ((mem_fg_to_ac_tree _ _).1 hDΦ).1
    have hDle : D.slot ≤ S.C.slot ((voteTime S (s + 1) : ℕ) : Int) :=
      slot_le_of_mem_T_before hDiv hMono hDT
    rw [hslot₃] at hDle
    have hDne : D ≠ Block.genesis := by
      rintro rfl
      cases hDB
    have hlt := (((lem11_node_invariant S Sched x (stepBefore x (voteTime S (s + 1))) w).1.2.2.1).2
      D hDT hDne).2.2.2
    rw [parent_eq_of_parent? hDB, hBslot] at hlt
    exact Nat.lt_irrefl _ (lt_of_lt_of_le hlt hDle)
  -- the two tests' answers, named
  obtain ⟨bp, hbp⟩ : ∃ bp : Block V → Bool, ∀ D : Block V,
      goldfish_eligible S.C (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) ((slotStart S (s + 1) : ℕ) : Int)
        votes_pl.toFinset support_pl.toFinset s D = .ok (bp D) :=
    ⟨fun D => Classical.choose (goldfish_eligible_answers S.C hRootsΦp
      ((slotStart S (s + 1) : ℕ) : Int) votes_pl.toFinset support_pl.toFinset s D), hTestP⟩
  obtain ⟨bw, hbw⟩ : ∃ bw : Block V → Bool, ∀ D : Block V,
      goldfish_eligible S.C (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) ((voteTime S (s + 1) : ℕ) : Int)
        votes support_votes s D = .ok (bw D) :=
    ⟨fun D => Classical.choose (goldfish_eligible_answers S.C hRootsΦ
      ((voteTime S (s + 1) : ℕ) : Int) votes support_votes s D), hTestW⟩
  have hPTest' : bw B = true :=
    Except.ok.inj ((hbw B).symm.trans (goldfish_eligible_current_slot S.C _ _ _ _ s B
      (hBslot.trans hslot₃.symm)))
  -- the two tests agree on a child of a path block that is a viable head at `w`
  have hTestAgreeW : ∀ Y : Block V, X.AncestorEq Y →
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq Y →
      Y.AncestorEq B.parent → Y ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads →
      ∀ D : Block V, D.parent? = some Y → bw D = bp D := by
    intro Y hXY hRY hYB hYw D hD
    have hHeads : D.parent ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads ↔
        D.parent ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads := by
      rw [parent_eq_of_parent? hD]
      exact ⟨fun _ => hYw, fun _ => hViableLe Y hXY hRY hYB hYw⟩
    have hEq := goldfish_eligible_congr S.C _ _ _ _ votes_pl.toFinset support_pl.toFinset votes
      support_votes s D (n D) hHeads hSlot (hn Y hXY hRY hYB D hD).1 (hn Y hXY hRY hYB D hD).2
      hVotersEq
    exact Except.ok.inj ((hbw D).symm.trans (hEq.symm.trans (hbp D)))
  -- a child of a block that is not a viable head passes the test
  have hbpTrue : ∀ D : Block V, D.parent ∉ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads → bp D = true :=
    fun D hD => Except.ok.inj ((hbp D).symm.trans
      (goldfish_eligible_of_parent_not_viable S.C _ _ _ _ s D hD))
  have hbwTrue : ∀ D : Block V, D.parent ∉ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads → bw D = true :=
    fun D hD => Except.ok.inj ((hbw D).symm.trans
      (goldfish_eligible_of_parent_not_viable S.C _ _ _ _ s D hD))
  -- `p`'s test on a child of a viable head of `p`, other than a slot-`(s + 1)` block, is the
  -- majority test
  have hbpMaj : ∀ D : Block V, D.parent ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads → D.slot ≠ s + 1 →
      ∀ m : ℕ, goldfish_score (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) votes_pl.toFinset support_pl.toFinset s D = .ok m →
      (bp D = true ↔ voters_count votes_pl.toFinset < 2 * m) := by
    intro D hD hDs m hm
    have hDs' : D.slot ≠ S.C.slot ((slotStart S (s + 1) : ℕ) : Int) := by
      rw [hslot₁]
      exact hDs
    have h := (hbp D).symm.trans (goldfish_eligible_of_parent_viable S.C _ _ _ _ s D m hD hDs' hm)
    rw [Except.ok.inj h]
    exact decide_eq_true_iff
  -- a block of `p`'s viable tree has a slot at most `s`
  have hslot₀ : S.C.slot ((slotStart S (s + 1) - 1 : ℕ) : Int) = s :=
    slot_eq_of_mem S (by omega) (by omega)
  have hTreePSlot : ∀ D ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree, D.slot ≠ s + 1 := by
    intro D hD hDs
    have hDT := ((mem_fg_to_ac_tree _ _).1 ((mem_viable_tree_iff _ _ _).1 hD).1).1
    have h := slot_lt_of_mem_T_before S Sched x hDiv hMono (slotStart S (s + 1)) p D (by omega)
      hDT
    rw [hslot₀, hDs] at h
    exact Nat.not_succ_le_self s h
  have hWalkPB := hWalkP
  rw [← hBpar, goldfish_fork_choice_eq] at hWalkPB
  -- Lemma 9 with the score argument, at any shared block `X'` from `X` to `B`'s parent that is
  -- `w`'s anchor or a descendant of it, and `H_w` or an ancestor of it
  have hMergeAt : ∀ X' : Block V, X.AncestorEq X' → X'.AncestorEq B.parent →
      (get_anchor A' (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int)).AncestorEq X' → X'.AncestorEq H_w → H_w = B := by
    intro X' hXX' hX'B hAwX' hX'H
    have hRX' : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq X' :=
      ancestorEq_trans hRAw hAwX'
    -- `w`'s test accepts what `p`'s does on a child of a path block
    have hImp : ∀ Y : Block V, X'.AncestorEq Y → Y.AncestorEq B.parent →
        ∀ D : Block V, D.parent? = some Y → bp D = true → bw D = true := by
      intro Y hX'Y hYB D hD hb
      by_cases hYw : Y ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads
      · rw [hTestAgreeW Y (ancestorEq_trans hXX' hX'Y) (ancestorEq_trans hRX' hX'Y) hYB hYw D hD]
        exact hb
      · exact hbwTrue D (by rw [parent_eq_of_parent? hD]; exact hYw)
    exact GoldilocksCorrectness.Statements.Routines.lem9le_walk_ends_at_proposal_of_shared_block
      (A_p := get_anchor (stateBefore x (slotStart S (s + 1)) p).A
        (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) ((slotStart S (s + 1) : ℕ) : Int))
      (A_w := get_anchor A' (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int))
      (X := X') (P := B) (H_w := H_w)
      (tree_p := viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
        (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree)
      (tree_w := viable_tree (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) vbt)
      (score_p := goldfish_score (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
        votes_pl.toFinset support_pl.toFinset s)
      (score_w := goldfish_score (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) votes
        support_votes s)
      (eligible_p := goldfish_eligible S.C (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
        ((slotStart S (s + 1) : ℕ) : Int) votes_pl.toFinset support_pl.toFinset s)
      (eligible_w := goldfish_eligible S.C (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) votes support_votes s)
      n bp bw
      (fun Y hX'Y hYB D hD =>
        (hn Y (ancestorEq_trans hXX' hX'Y) (ancestorEq_trans hRX' hX'Y) hYB D hD).1)
      (fun Y hX'Y hYB D hD =>
        (hn Y (ancestorEq_trans hXX' hX'Y) (ancestorEq_trans hRX' hX'Y) hYB D hD).2)
      hbp hbw hRootsP (parent?_eq_some_parent hBne)
      hWalkPB ((goldfish_fork_choice_eq ..).symm.trans hWalk) ⟨ancestorEq_trans hApX hXX', hX'B⟩ hAwX' hX'H
      (fun Y hX'Y _ hYB => hInTree Y (hAncΦ Y (ancestorEq_trans hRX' hX'Y)
          (ancestorEq_trans hYB hBpB))
        (ancestorEq_trans hRX' hX'Y) (ancestorEq_trans hYB hBpB))
      (hInTree B hBΦ hRB (ancestorEq_refl B))
      hPTest' hNoChildP
      (path_test_of_test_imp (P := B) _ _ hbp hWalkPB ⟨ancestorEq_trans hApX hXX', hX'B⟩ hImp)
      (fun Y hX'Y hYB hYne D hD hDpar hDb => by
        have hXY := ancestorEq_trans hXX' hX'Y
        have hRY := ancestorEq_trans hRX' hX'Y
        have hDB : D ≠ B := by
          rintro rfl
          rw [hBpar?] at hDpar
          exact hYne ((Option.some.inj hDpar).symm.trans hBpar.symm)
        have hDp := hChild vbt votes support_votes hvbt hCounted Y hXY hRY hYB D hD hDpar hDB
          (by rw [hbw D, hDb])
        by_cases hYw : Y ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads
        · exact Or.inl ⟨hDp, by rw [← hTestAgreeW Y hXY hRY hYB hYw D hDpar]; exact hDb⟩
        by_cases hYp : Y ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads
        swap
        · exact Or.inl ⟨hDp, hbpTrue D (by rw [parent_eq_of_parent? hDpar]; exact hYp)⟩
        cases hbD : bp D with
        | true => exact Or.inl ⟨hDp, rfl⟩
        | false =>
          refine Or.inr (fun D' hD'p hD'par hD'B hb' => ?_)
          have hYD : D.parent ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads := by
            rw [parent_eq_of_parent? hDpar]; exact hYp
          have hYD' : D'.parent ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads := by
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
        have hDp := hChild vbt votes support_votes hvbt hCounted B.parent hXB' hRB'
          (ancestorEq_refl _) D hD hDpar hDB (by rw [hbw D, hDb])
        refine ⟨hDp, ?_⟩
        by_cases hYw : B.parent ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads
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
      have hAwB : get_anchor A' (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) = B ∨
          (get_anchor A' (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
            ((voteTime S (s + 1) : ℕ) : Int)).AncestorEq B.parent := by
        cases B with
        | genesis => exact absurd rfl hBne
        | node q sl r vs sp ats v => exact (ancestorEq_node_iff _ q sl r vs sp ats v).1 hAnchorW
      rcases hAwB with hAwEq | hAwBp
      · -- `w`'s anchor is `B`: `B` has no child in `w`'s tree, so the walk from `B` ends at `B`
        rw [hAwEq] at hWalk
        have hWalkB : ghost B (viable_tree (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) vbt)
            (goldfish_score (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) votes
              support_votes s)
            (goldfish_eligible S.C (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
              ((voteTime S (s + 1) : ℕ) : Int) votes support_votes s) = .ok B :=
          ghost_reaches (ancestorEq_refl B)
            (fun C hBC hCB hCB' => absurd (ancestorEq_antisymm hBC hCB').symm hCB)
            (ghost_step_none_of_no_child hNoChildP)
            (fun Y hBY hYB hYne => absurd (ancestorEq_antisymm hBY hYB).symm hYne)
        exact (Except.ok.inj (hWalk.symm.trans ((goldfish_fork_choice_eq ..).trans hWalkB)))
      · -- `w`'s anchor is on `p`'s walk from `X` to `B`'s parent, and is the shared block
        have hAwH : (get_anchor A' (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
            ((voteTime S (s + 1) : ℕ) : Int)).AncestorEq H_w := by
          rcases ghost_spec ((goldfish_fork_choice_eq ..).symm.trans hWalk) with h | ⟨h, -⟩
          · rw [h]
            exact ancestorEq_refl _
          · exact h
        exact hMergeAt _ hXAw hAwBp (ancestorEq_refl _) hAwH
  rw [hhead, hMerge]

/-- Lemma 24 with `head_height_floor` at `p` at most at `w`, and `B`'s parent passing `w`'s
viability test. The
proof; the audited statement is in `Statements/Executions/OrderedFloorStatements.lean`.

Roots name blocks until `voteTime S (s + 1)`: Lemma 22 and Lemma 23, which the proof calls, take
blocks as held up to `w`'s vote time of slot `s + 1`;
`lem20le_goldfish_vote_names_honest_proposal` and `child_mem_proposer_viable_tree` read earlier.

Restated with the delivery premises up to `voteTime S (s + 1)`: the proposal of slot `s + 1` reaches `w` by then (`lem22_proposal_held_by_voter_upTo`, `lem23_proposer_and_voter_count_alike_upTo`). -/
theorem lem24le_goldfish_vote_names_honest_proposal_composed_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (voteTime S (s + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (voteTime S (s + 1)))
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (voteTime S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ X.AncestorEq (H u))
    (hVoters : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes_w support_w →
      voters_count votes_w < 2 * Hs.card)
    (hp : ∀ t : ℕ, voteTime S s ≤ t → t ≤ slotStart S (s + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    (hw : ∀ t : ℕ, voteTime S s ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hOnly : ∀ B' ∈ (stateBefore x (voteTime S (s + 1)) w).S.T, B'.slot = s + 1 → B' = B)
    (hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (s + 1)) p).S.T, B'.root ≠ B.root)
    (hF3p : ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree,
      W ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads ∧ X.AncestorEq W)
    (hApX : (get_anchor (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      ((slotStart S (s + 1) : ℕ) : Int)).AncestorEq X)
    (hF2w : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq B)
    (hLocksW : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    (hParentViable : is_viable (stateBefore x (voteTime S (s + 1)) w).S B.parent = true)
    (hFloorLe : head_height_floor (stateBefore x (slotStart S (s + 1)) p).S ≤
      head_height_floor (stateBefore x (voteTime S (s + 1)) w).S) :
    vote.head = B.root := by
  have hF2p : (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).fc_root := by
    rw [fc_root_eq]; exact F_ancestorEq_fc_root_of_stateBefore S Sched x (slotStart S (s + 1)) p
  have hFroot : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root := by
    rw [fc_root_eq]; exact F_ancestorEq_fc_root_of_stateBefore S Sched x (voteTime S (s + 1)) w
  -- the times
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hc₀ : supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S s
  have hv₁ : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hfz : viewFreeze S s = slotStart S s + 3 * Δ S := viewFreeze_eq S s
  -- the windows the callees read
  have hpC : ∀ t : ℕ, voteTime S s ≤ t → t ≤ supportCutoff S s →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int) :=
    fun t h1 h2 => hp t h1 (by omega)
  have hpF : ∀ t : ℕ, viewFreeze S s ≤ t → t ≤ slotStart S (s + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int) :=
    fun t h1 h2 => hp t (by omega) h2
  have hwC : ∀ t : ℕ, voteTime S s ≤ t → t ≤ supportCutoff S s →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int) :=
    fun t h1 h2 => hw t h1 (by omega)
  have hwV : ∀ t : ℕ, slotStart S (s + 1) ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int) :=
    fun t h1 h2 => hw t (by omega) h2
  have hpt₁ : p ∉ Sched.adv (slotStart S (s + 1) : Int) :=
    (hp (slotStart S (s + 1)) (by omega) le_rfl).2
  -- step 1: the end of `p`'s walk
  obtain ⟨i, hl, hsent⟩ := id hPropose
  obtain ⟨-, -, hBpar?, hEnd⟩ := proposal_parent_walk_end S Sched x s i B p hl hsent
  have hPB : B.parent.AncestorEq B := ancestorEq_of_parent? hBpar?
  have hRXp : (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).fc_root.AncestorEq X :=
    ancestorEq_trans (fc_root_ancestorEq_get_anchor _ _ _) hApX
  have hFXp : (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq X :=
    ancestorEq_trans hF2p hRXp
  -- step 2: `B`'s parent is in `p`'s tree, and `p`'s finalized block is an ancestor of `B`
  have hParentHeld : B.parent ∈ (stateBefore x (slotStart S (s + 1)) p).S.T := by
    rcases hEnd with hin | heq
    · exact ((mem_fg_to_ac_tree _ _).1 ((mem_viable_tree_iff _ _ _).1 hin).1).1
    · obtain ⟨W, hW, -, hXW⟩ := hF3p
      refine ancestors_mem_T_of_exec S Sched x _ p W B.parent ((mem_fg_to_ac_tree _ _).1 hW).1 ?_
      rw [heq]
      exact ancestorEq_trans hApX hXW
  have hFpB : (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq B := by
    refine ancestorEq_trans ?_ hPB
    rcases hEnd with hin | heq
    · exact ((mem_fg_to_ac_tree _ _).1 ((mem_viable_tree_iff _ _ _).1 hin).1).2
    · rw [heq]
      exact ancestorEq_trans hF2p (fc_root_ancestorEq_get_anchor _ _ _)
  -- step 3: `p` holds `B` after its tick (Lemma 22a), and `w` before `t₃` (Lemma 22)
  have hBp : B ∈ (x[i + 1][p].st).S.T :=
    GoldilocksCorrectness.Statements.Executions.lem22a_proposer_holds_own_proposal S Sched x s i B p
      hDiv hMono hl hsent hRootNew hParentHeld ((compatible_iff _ _).2 (Or.inl hFpB))
  have hFwB : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq B :=
    ancestorEq_trans hFroot hF2w
  have hBw : B ∈ (stateBefore x (voteTime S (s + 1)) w).S.T :=
    GoldilocksCorrectness.Statements.Executions.lem22_proposal_held_by_voter_upTo S Sched x GST s i B p
      w hDiv hMono hSync hCatch hRoots hParent hGST hpt₁ hwV hl hsent hBp
      ((compatible_iff _ _).2 (Or.inl hFwB))
  -- step 4: `B`'s parent and `B` reach `head_height_floor` at `w`: both chain states are their
  -- own (Lemma 11),
  -- and heights grow along ancestry (Lemma 47 (d))
  have hPw : B.parent ∈ (stateBefore x (voteTime S (s + 1)) w).S.T :=
    ancestors_mem_T_of_exec S Sched x _ w _ B.parent hBw hPB
  have hPfl : head_height_floor (stateBefore x (voteTime S (s + 1)) w).S ≤
      ((stateBefore x (voteTime S (s + 1)) w).S.σ B.parent).h :=
    (is_viable_iff _ _).1 hParentViable
  have hBfl : head_height_floor (stateBefore x (voteTime S (s + 1)) w).S ≤
      ((stateBefore x (voteTime S (s + 1)) w).S.σ B).h := by
    have hCw : ChainStatesComputed S.C (stateBefore x (voteTime S (s + 1)) w).S :=
      (lem11_node_invariant S Sched x (stepBefore x (voteTime S (s + 1))) w).1.2.2.2.2.2.1
    rw [hCw B.parent hPw] at hPfl
    rw [hCw B hBw]
    exact le_trans hPfl
      ((GoldilocksCorrectness.Statements.Routines.lem47_chain_state_heights S.C B.parent
        B).2.2.2.1 hPB)
  have hBVH : B ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads :=
    (mem_viable_heads_iff _ _).2 ⟨hBw, hFwB, hF2w, hBfl⟩
  have hBΦ : B ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree :=
    (mem_fg_to_ac_tree _ _).2 ⟨hBw, hFwB⟩
  -- step 5: the two validators count alike (Lemma 23)
  have hCount := GoldilocksCorrectness.Statements.Executions.lem23_proposer_and_voter_count_alike_upTo
    S Sched x GST s B p w hDiv hMono hSync hCatch hRoots hParent hGST hpF hwV hPropose hBΦ
    hOnly
  -- step 6: a viable head at `w` along the path is one at `p`; `B`'s parent is a viable head at
  -- `w` when the root of `w`'s fork choice is an ancestor of it
  have hViableLe := viable_heads_le_of_floor_le S Sched x s X B p w hParentHeld hRXp hFloorLe
  have hViableEnd : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq
        B.parent →
      B.parent ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads →
      B.parent ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads :=
    fun hRP _ => (mem_viable_heads_iff _ _).2 ⟨hPw, ancestorEq_trans hFroot hRP, hRP, hPfl⟩
  -- step 7: every child in `w`'s viable tree of a block of the path, other than `B`, is in `p`'s
  have hChild := child_mem_proposer_viable_tree_upTo S Sched x GST s X B p w hDiv hMono
    (SynchronyFromWakeUpTo.mono (by omega) hSync) (CatchUpOnWakeUpTo.mono (by omega) hCatch)
    (hRoots.mono (by omega)) hParent hGST hpF hwV hOnly hEnd hApX hFloorLe
  -- step 8: Lemma 20 with `head_height_floor` at `p` at most at `w`
  exact lem20le_goldfish_vote_names_honest_proposal_upTo S Sched x GST s Hs H X B p w vote hDiv hMono
    (SynchronyFromWakeUpTo.mono (by omega) hSync) (CatchUpOnWakeUpTo.mono (by omega) hCatch)
    (hRoots.mono (by omega)) hParent hOwner hGST hHs hVoters hpC hwC hPropose hSend hBw hF3p
    hApX hLocksW hBVH hViableLe hViableEnd
    (fun vp sp vw sw h₁ h₂ => ⟨fun Y hXY hRY _ D hD => (hCount vp sp vw sw h₁ h₂).1 D
        (ancestorEq_trans hFXp (ancestorEq_trans hXY (ancestorEq_of_parent? hD)))
        (ancestorEq_trans hFroot (ancestorEq_trans hRY (ancestorEq_of_parent? hD))),
      (hCount vp sp vw sw h₁ h₂).2⟩)
    (fun vbt _ _ hvbt _ Y hXY _ hYB D hD hDpar hDB _ => hChild vbt hvbt Y hXY hYB D hD hDpar hDB)

/-- Lemma 59 with `φ ≤ φ_w` and `φ_w` at most `B`'s parent's chain-state height, `φ` and `φ_w`
being `head_height_floor` at `p` and at `w`. The proof; the
audited statement is in `Statements/Executions/OrderedFloorStatements.lean`.

Roots name blocks until `voteTime S (s + 1)`: Lemma 22 and
`lem24le_goldfish_vote_names_honest_proposal_composed`, which the proof calls, take blocks as
held up to `w`'s vote time of slot `s + 1`.

Restated with the delivery premises up to `voteTime S (s + 1)`: the proposal of slot `s + 1` reaches `w` by then (`lem22_proposal_held_by_voter_upTo`, `lem23_proposer_and_voter_count_alike_upTo`). -/
theorem lem59le_goldfish_vote_names_honest_proposal_frame_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V) (ρ_p ρ_w : Block V) (φ φ_w : Height)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (voteTime S (s + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (voteTime S (s + 1)))
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (voteTime S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ X.AncestorEq (H u))
    (hVoters : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes_w support_w →
      voters_count votes_w < 2 * Hs.card)
    (hp : ∀ t : ℕ, voteTime S s ≤ t → t ≤ slotStart S (s + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    (hw : ∀ t : ℕ, voteTime S s ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hOnly : ∀ B' ∈ (stateBefore x (voteTime S (s + 1)) w).S.T, B'.slot = s + 1 → B' = B)
    (hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (s + 1)) p).S.T, B'.root ≠ B.root)
    (hShapeP : FrameShape (stateBefore x (slotStart S (s + 1)) p).S ρ_p φ)
    (hShapeW : FrameShape (stateBefore x (voteTime S (s + 1)) w).S ρ_w φ_w)
    (hFloorLe : φ ≤ φ_w)
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S (s + 1)) p).S.T,
      X.AncestorEq W ∧ ρ_p.AncestorEq W ∧ φ ≤ (chainStateOf S.C W).h)
    (hApX : (get_anchor (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      ((slotStart S (s + 1) : ℕ) : Int)).AncestorEq X)
    (hRootW : ρ_w.AncestorEq B)
    (hLocksW : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    (hParentHeight : φ_w ≤ (chainStateOf S.C B.parent).h) :
    vote.head = B.root := by
  -- the times and the windows the callees read
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv₁ : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hwV : ∀ t : ℕ, slotStart S (s + 1) ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int) :=
    fun t h1 h2 => hw t (by omega) h2
  have hpt₁ : p ∉ Sched.adv (slotStart S (s + 1) : Int) :=
    (hp (slotStart S (s + 1)) (by omega) le_rfl).2
  -- Lemma 56 at the two shapes
  obtain ⟨hRp, -, hHp⟩ := GoldilocksCorrectness.Statements.Routines.lem56_frame_of_shape _ _ _
    hShapeP
  obtain ⟨hRw, hVw, -⟩ := GoldilocksCorrectness.Statements.Routines.lem56_frame_of_shape _ _ _
    hShapeW
  -- Lemma 46: each finalized block is its fork-choice root or an ancestor of it
  have hFρp : (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq ρ_p := by
    rw [← hShapeP.1]
    exact F_ancestorEq_fc_root_of_stateBefore S Sched x _ p
  have hFρw : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq ρ_w := by
    rw [← hShapeW.1]
    exact F_ancestorEq_fc_root_of_stateBefore S Sched x _ w
  have hF2p : (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).fc_root := by
    rw [hRp]
    exact hFρp
  have hF2w : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq B := by
    rw [hRw]
    exact hRootW
  -- a viable head of `p`'s frame that is `X` or a descendant of `X`
  have hF3p : ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree,
      W ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads ∧ X.AncestorEq W := by
    obtain ⟨W, hW, hXW, hρW, hφW⟩ := hHeadP
    have hFW := ancestorEq_trans hFρp hρW
    have hσ : (stateBefore x (slotStart S (s + 1)) p).S.σ W = chainStateOf S.C W :=
      (lem11_node_invariant S Sched x (stepBefore x (slotStart S (s + 1))) p).1.2.2.2.2.2.1 W hW
    refine ⟨W, (mem_fg_to_ac_tree _ _).2 ⟨hW, hFW⟩, (hHp W).2 ⟨hW, hFW, hρW, ?_⟩, hXW⟩
    rw [hσ]
    exact hφW
  -- `w` holds `B` before its vote time: steps 1 to 3 of Lemma 24's proof
  obtain ⟨i, hl, hsent⟩ := id hPropose
  obtain ⟨-, -, hBpar?, hEnd⟩ := proposal_parent_walk_end S Sched x s i B p hl hsent
  have hPB : B.parent.AncestorEq B := ancestorEq_of_parent? hBpar?
  have hParentHeld : B.parent ∈ (stateBefore x (slotStart S (s + 1)) p).S.T := by
    rcases hEnd with hin | heq
    · exact ((mem_fg_to_ac_tree _ _).1 ((mem_viable_tree_iff _ _ _).1 hin).1).1
    · obtain ⟨W, hW, -, hXW⟩ := hF3p
      refine ancestors_mem_T_of_exec S Sched x _ p W B.parent ((mem_fg_to_ac_tree _ _).1 hW).1 ?_
      rw [heq]
      exact ancestorEq_trans hApX hXW
  have hFpB : (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq B := by
    refine ancestorEq_trans ?_ hPB
    rcases hEnd with hin | heq
    · exact ((mem_fg_to_ac_tree _ _).1 ((mem_viable_tree_iff _ _ _).1 hin).1).2
    · rw [heq]
      exact ancestorEq_trans hF2p (fc_root_ancestorEq_get_anchor _ _ _)
  have hBp : B ∈ (x[i + 1][p].st).S.T :=
    GoldilocksCorrectness.Statements.Executions.lem22a_proposer_holds_own_proposal S Sched x s i B p
      hDiv hMono hl hsent hRootNew hParentHeld ((compatible_iff _ _).2 (Or.inl hFpB))
  have hFwB : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq B :=
    ancestorEq_trans hFρw hRootW
  have hBw : B ∈ (stateBefore x (voteTime S (s + 1)) w).S.T :=
    GoldilocksCorrectness.Statements.Executions.lem22_proposal_held_by_voter_upTo S Sched x GST s i B p
      w hDiv hMono hSync hCatch hRoots hParent hGST hpt₁ hwV hl hsent hBp
      ((compatible_iff _ _).2 (Or.inl hFwB))
  -- `B`'s parent passes `w`'s viability test: `w` holds it, with its own chain state
  have hParentViable : is_viable (stateBefore x (voteTime S (s + 1)) w).S B.parent = true := by
    have hPw : B.parent ∈ (stateBefore x (voteTime S (s + 1)) w).S.T :=
      ancestors_mem_T_of_exec S Sched x _ w _ B.parent hBw hPB
    have hσ : (stateBefore x (voteTime S (s + 1)) w).S.σ B.parent = chainStateOf S.C B.parent :=
      (lem11_node_invariant S Sched x (stepBefore x (voteTime S (s + 1))) w).1.2.2.2.2.2.1
        B.parent hPw
    refine (hVw B.parent).2 ?_
    rw [hσ]
    exact hParentHeight
  -- `head_height_floor` at `p` and at `w` are `φ` and `φ_w`
  have hFloorLe' : head_height_floor (stateBefore x (slotStart S (s + 1)) p).S ≤
      head_height_floor (stateBefore x (voteTime S (s + 1)) w).S := by
    rw [hShapeP.2, hShapeW.2]
    exact hFloorLe
  exact lem24le_goldfish_vote_names_honest_proposal_composed_upTo S Sched x GST s Hs H X B p w vote
    hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs hVoters hp hw hPropose hSend
    hOnly hRootNew hF3p hApX hF2w hLocksW hParentViable hFloorLe'

end GoldilocksCorrectness.Proofs.Executions

