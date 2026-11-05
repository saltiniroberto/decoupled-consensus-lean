module
public import GoldilocksCorrectness.Proofs.Executions.Lemma24
public import GoldilocksCorrectness.Statements.Routines.FrameStatements
public import GoldilocksCorrectness.Statements.Executions.ChainStateStatements

@[expose] public section

/-!
# An honest proposal is viable at its proposer

The proof of the statement of
`GoldilocksCorrectness/Statements/Executions/ProposalViabilityStatements.lean`: when the proposer
`p` put the block `B` on the wire at its tick at the start of slot `s + 1`, and `B`'s parent is in
`p`'s viable tree, `B`'s height is at least `head_height_floor` at `p` (the least chain-state height a viable block may have).

The route: Lemma 19 on `p`'s tick makes `B`'s parent the head `p`'s fork choice answered on its
state before the start of slot `s + 1`; Lemma 58 makes it a viable head of `p`'s frame, whose tree
holds every block between two of its blocks (the node invariant); a viable head has a chain-state
height at least `head_height_floor` (`mem_viable_heads_iff`), that chain state is the parent's own
(`ChainStatesComputed`), and `B`'s height is at least its parent's (Lemma 47 (b)).
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem)

open GoldilocksCorrectness.Proofs.Routines (lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree mem_viable_heads_iff)

open GoldilocksCorrectness.Proofs.Routines (fg_to_ac_F get_head_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- An honest proposal is viable at its proposer. The proof; the audited statement is in
`Statements/Executions/ProposalViabilityStatements.lean`.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `s`: the slot before the proposal's;
- `B`: the block proposed; `p`: its proposer. -/
theorem proposal_viable (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (B : Block V) (p : V)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) :
    head_height_floor (stateBefore x (slotStart S (s + 1)) p).S ≤ (chainStateOf S.C B).h := by
  obtain ⟨i, hl, hsent⟩ := hPropose
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss' : slotStart S (s + 1 + 1) = slotStart S (s + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
  have hslot₁ : S.C.slot ((slotStart S (s + 1) : ℕ) : Int) = s + 1 :=
    slot_eq_of_mem S (le_refl _) (by omega)
  have hi : stepBefore x (slotStart S (s + 1)) = i := stepBefore_eq_of_lbl x hl
  obtain ⟨-, n₁', sent₁, hrun₁, hB₁⟩ := tick_send_of_honestSendAt hl hsent
  -- the tick's input state has the AC state and the FG state of `p`'s state before the tick
  have hAp : (tickInputState x i (slotStart S (s + 1)) p).A =
      (stateBefore x (slotStart S (s + 1)) p).A := by
    rw [(tickInputState_frame x i _ p).2.1]
    unfold stateBefore
    rw [hi]
  have hSp : (tickInputState x i (slotStart S (s + 1)) p).S =
      (stateBefore x (slotStart S (s + 1)) p).S := by
    rw [(tickInputState_frame x i _ p).1]
    unfold stateBefore
    rw [hi]
  -- Lemma 19: `B`'s parent is the head of `p`'s fork choice
  obtain ⟨-, -, -, Hp, votes_pl, support_pl, -, -, hWalkP, hBdef⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem19_tick_proposes S.C S.P S.X _ n₁' _ sent₁ B
      hrun₁ hB₁
  rw [hslot₁, Nat.add_sub_cancel, hAp, hSp] at hWalkP
  rw [hslot₁] at hBdef
  have hBpar : B.parent = Hp := by rw [hBdef]; rfl
  have hBne : B ≠ Block.genesis := by rw [hBdef]; exact fun h => by cases h
  have hHead : get_head S.C (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) ((slotStart S (s + 1) : ℕ) : Int)
      votes_pl.toFinset support_pl.toFinset s = .ok B.parent := by
    rw [hBpar, get_head_eq]
    exact hWalkP
  -- Lemma 58: `B`'s parent is a viable head of `p`'s frame
  have hBetween : ∀ X ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree,
      ∀ Y ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree, ∀ Z : Block V,
      X.AncestorEq Z → Z.AncestorEq Y →
        Z ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree :=
    fun X hX Y hY Z hXZ hZY => frame_path_of_exec S Sched x (stepBefore x (slotStart S (s + 1))) p
      Y Z hY (ancestorEq_trans (by rw [fg_to_ac_F]; exact ((mem_fg_to_ac_tree _ _).1 hX).2) hXZ)
      hZY
  have hVH := GoldilocksCorrectness.Statements.Routines.lem58_walk_end_is_viable_head _ _ _ _ _ _
    _ _ (rootsNameBlocksIn_frame_of_exec_node S Sched x (stepBefore x (slotStart S (s + 1))) p)
    hBetween hHead hParentIn
  obtain ⟨hPT, -, -, hfl⟩ := (mem_viable_heads_iff _ _).1 hVH
  -- the parent's chain state is its own, and `B`'s height is at least its parent's
  rw [(lem11_node_invariant S Sched x (stepBefore x (slotStart S (s + 1))) p).1.2.2.2.2.2.1 _ hPT]
    at hfl
  rcases (lem47_chain_state_heights S.C B B).2.1 hBne with h | h
  · rw [h]
    exact hfl
  · rw [h]
    exact Nat.le_succ_of_le hfl

end GoldilocksCorrectness.Proofs.Executions
