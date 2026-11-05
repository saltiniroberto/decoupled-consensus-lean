module
public import GoldilocksCorrectness.Statements.Executions.ComposedProposalVoteStatements
public import GoldilocksCorrectness.Statements.Executions.FastConfirmationStatements
public import GoldilocksCorrectness.Statements.Executions.HeightAttestationStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Statements.Routines.FrameStatements
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts

@[expose] public section

/-!
# Lemmas 59, 60, 61: the vote, the confirmation and the attestation over a frame shape

The proofs of the statements of
`GoldilocksCorrectness/Statements/Executions/FrameShapeStatements.lean`. Each derives the
finality-gadget hypotheses of Lemma 24, Lemma 29 or Lemma 55 from the frame shape (Lemma 56), the
node invariant (Lemmas 11, 46, 57), and applies that lemma.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq voteTime_eq)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (mem_viable_tree_of_frameShape)

open GoldilocksCorrectness.Proofs.Routines (mem_viable_tree_iff)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks CountedVotes FrameShape)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans ancestorEq_refl compatible_iff
  ancestorEq_of_parent?)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Under a frame shape with root `ρ` and `head_height_floor` (the least chain-state height a viable block may have) equal to `φ` at `v`'s state before the time `t`, a block of
`v`'s tree that `ρ` is an ancestor of, whose chain-state height is at least `φ`, is in `v`'s viable
tree: the finalized block is the root or an ancestor of it (Lemma 46), and the block's chain state
is its own (Lemma 11).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
- `B`: the block; `ρ`: the root; `φ`: the value of `head_height_floor`. -/
theorem mem_viable_tree_of_frameShape_of_stateBefore (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) (B ρ : Block V) (φ : Height)
    (hShape : FrameShape (stateBefore x t v).S ρ φ)
    (hRootV : ρ.AncestorEq B)
    (hBHeight : φ ≤ (chainStateOf S.C B).h)
    (hBin : B ∈ (stateBefore x t v).S.T) :
    B ∈ viable_tree (fg_to_ac (stateBefore x t v).S) (fg_to_ac (stateBefore x t v).S).tree := by
  refine mem_viable_tree_of_frameShape _ ρ φ B hShape ?_ hRootV hBin ?_
  · rw [← hShape.1]
    exact F_ancestorEq_fc_root_of_stateBefore S Sched x t v
  · have hσ : (stateBefore x t v).S.σ B = chainStateOf S.C B :=
      (lem11_node_invariant S Sched x (stepBefore x t) v).1.2.2.2.2.2.1 B hBin
    rw [hσ]
    exact hBHeight

/-- Lemma 59, the next slot's honest vote names the honest proposal, over a frame shape. The proof;
the audited statement is in `Statements/Executions/FrameShapeStatements.lean`.

Roots name blocks until `voteTime S (s + 1)`: Lemma 22 and Lemma 24, which the proof calls, take
blocks as held up to `w`'s vote time of slot `s + 1`. -/
theorem lem59_goldfish_vote_names_honest_proposal_frame (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V) (ρ_p ρ_w : Block V) (φ : Height)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
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
    (hShapeW : FrameShape (stateBefore x (voteTime S (s + 1)) w).S ρ_w φ)
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
    (hBHeight : φ ≤ (chainStateOf S.C B).h) :
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
      exact ancestorEq_trans hF2p
        (GoldilocksCorrectness.Proofs.Routines.fc_root_ancestorEq_get_anchor _ _ _)
  have hBp : B ∈ (x[i + 1][p].st).S.T :=
    GoldilocksCorrectness.Statements.Executions.lem22a_proposer_holds_own_proposal S Sched x s i B p
      hDiv hMono hl hsent hRootNew hParentHeld ((compatible_iff _ _).2 (Or.inl hFpB))
  have hFwB : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq B :=
    ancestorEq_trans hFρw hRootW
  have hBw : B ∈ (stateBefore x (voteTime S (s + 1)) w).S.T :=
    GoldilocksCorrectness.Statements.Executions.lem22_proposal_held_by_voter S Sched x GST s i B p
      w hDiv hMono hSync hCatch hRoots hParent hGST hpt₁ hwV hl hsent hBp
      ((compatible_iff _ _).2 (Or.inl hFwB))
  -- `B` passes `w`'s viability test, and the two floors are `φ`
  have hBViable : is_viable (stateBefore x (voteTime S (s + 1)) w).S B = true := by
    have hσ : (stateBefore x (voteTime S (s + 1)) w).S.σ B = chainStateOf S.C B :=
      (lem11_node_invariant S Sched x (stepBefore x (voteTime S (s + 1))) w).1.2.2.2.2.2.1 B hBw
    refine (hVw B).2 ?_
    rw [hσ]
    exact hBHeight
  have hFloor : head_height_floor (stateBefore x (slotStart S (s + 1)) p).S =
      head_height_floor (stateBefore x (voteTime S (s + 1)) w).S :=
    hShapeP.2.trans hShapeW.2.symm
  exact GoldilocksCorrectness.Statements.Executions.lem24_goldfish_vote_names_honest_proposal_composed
    S Sched x GST s Hs H X B p w vote hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs
    hVoters hp hw hPropose hSend hOnly hRootNew hF3p hApX hF2w hLocksW hBViable hFloor

/-- Lemma 60, the confirmation update makes a voter-majority block fast and locks it, over a root.
The proof; the audited statement is in `Statements/Executions/FrameShapeStatements.lean`.

Roots name blocks until `supportCutoff S s`: Lemma 29, which the proof calls, takes blocks as
held up to the support cutoff of slot `s`. -/
theorem lem60_update_confirmation_fast_locks_frame (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V)
    (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (supportCutoff S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      B ∈ (stateBefore x (voteTime S s) u).S.T)
    (hVoters : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Hs.card)
    (hHalf : (S.P.committee s).card ≤ 2 * Hs.card)
    (hBne : B ≠ Block.genesis)
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hRootV : (get_fc_root (stateBefore x (supportCutoff S (s + 1)) v).S).AncestorEq B) :
    B ∈ (stateBefore x (supportCutoff S (s + 1) + 1) v).A.fast_blocks ∧
      LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∈
        (stateBefore x (supportCutoff S (s + 1) + 1) v).A.lock_entries :=
  GoldilocksCorrectness.Statements.Executions.lem29_update_confirmation_fast_locks_voter_majority_block
    S Sched x GST s Hs B v hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs hVoters
    hHalf hBne hv (ancestorEq_trans (F_ancestorEq_fc_root_of_stateBefore S Sched x _ v) hRootV)

/-- The hypotheses of Lemma 55 on the viable tree and the record, from a frame shape at `v`. The
proof; the audited statement is in `Statements/Executions/FrameShapeStatements.lean`. -/
theorem lem61_frame_hypotheses (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (B : Block V) (v : V) (ρ : Block V) (φ : Height)
    (hShape : FrameShape (stateBefore x (supportCutoff S (s + 1)) v).S ρ φ)
    (hRootV : ρ.AncestorEq B)
    (hBHeight : φ ≤ (chainStateOf S.C B).h)
    (hBin : B ∈ (stateBefore x (supportCutoff S (s + 1)) v).S.T)
    (hLockBox : (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
        some (chainStateOf S.C B).T_h.root) :
    B ∈ viable_tree (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree ∧
      ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
        ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
            some (chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) v).Λ.sent,
            b.h = (chainStateOf S.C B).h → b.T = (chainStateOf S.C B).T_h.root)) := by
  refine ⟨mem_viable_tree_of_frameShape_of_stateBefore S Sched x _ v B ρ φ hShape hRootV hBHeight
    hBin, ?_⟩
  rcases hLockBox with hlt | hnone | hlock
  · exact Or.inl (lock_none_of_h_j_lt_of_stateBefore S Sched x _ v _ hlt)
  · exact Or.inl hnone
  · exact Or.inr ⟨hlock, lockNamesSent_of_stateBefore S Sched x _ v _ _ hlock⟩

/-- Lemma 61, every honest validator with the honest proposal as its source attests for its
height, over a frame shape. The proof; the audited statement is in
`Statements/Executions/FrameShapeStatements.lean`. -/
theorem lem61_honest_validator_attests_frame (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (r s : ℕ) (B : Block V) (v : V) (A' : ACState V) (ρ : Block V) (φ : Height)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hs : s = r * S.C.R)
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A')
    (hSaved : A'.saved_confirmation s = some B)
    (hFast : B ∈ A'.fast_blocks)
    (hLocks : ∀ e ∈ A'.lock_entries,
      is_live (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    (hShape : FrameShape (stateBefore x (supportCutoff S (s + 1)) v).S ρ φ)
    (hRootV : ρ.AncestorEq B)
    (hBHeight : φ ≤ (chainStateOf S.C B).h)
    (hBin : B ∈ (stateBefore x (supportCutoff S (s + 1)) v).S.T)
    (hLockBox : (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
        some (chainStateOf S.C B).T_h.root) :
    (∃ (i : ℕ) (a : Attestation V), x.lbl i = AtomicAction.tickAllAwake (supportCutoff S (s + 1)) ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent ∧
      a.val_index = v ∧ a.h = (chainStateOf S.C B).h ∧ a.T = (chainStateOf S.C B).T_h.root) ∨
    (∃ b ∈ (stateBefore x (supportCutoff S (s + 1)) v).Λ.sent,
      b.h = (chainStateOf S.C B).h ∧ b.T = (chainStateOf S.C B).T_h.root) := by
  obtain ⟨hViable, hRecord⟩ :=
    lem61_frame_hypotheses S Sched x s B v ρ φ hShape hRootV hBHeight hBin hLockBox
  exact GoldilocksCorrectness.Statements.Executions.lem55_honest_validator_attests_for_height S
    Sched x r s B v A' hDiv hMono hs hv hUpdate hSaved hFast hLocks hViable hRecord

end GoldilocksCorrectness.Proofs.Executions
