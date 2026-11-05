module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma24
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Executions.Lemma24
public import GoldilocksCorrectness.Statements.Routines.FrameStatements
public import GoldilocksCorrectness.Statements.Executions.ChainStateStatements

@[expose] public section

/-!
# ProposalViability, over a model

The theorem of `GoldilocksCorrectness/Proofs/Executions/ProposalViability.lean` over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: an honest proposal is viable at its
proposer. The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem)

open GoldilocksCorrectness.Proofs.Routines (get_head_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- An honest proposal is viable at its proposer. The proof; the audited statement is in
`Statements/Executions/ProposalViabilityStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `s`: the slot before the proposal's;
- `B`: the block proposed; `p`: its proposer.

Read aloud: the chain-state height of the block `B` the honest proposer `p` proposes at the start of
slot `s + 1` is at least `p`'s least viable height, when `B`'s parent is in `p`'s viable tree. -/
theorem proposal_viable (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (B : Block V) (p : V)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree) :
    M.head_height_floor (x.tickInput p (M.slotStart S.C (s + 1))) ≤
      (M.chainStateOf S.C B).h := by
  obtain ⟨i, hl, hsent⟩ := hPropose
  have hΔ := one_le_Δ S
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add,
      Nat.mul_one]
  have hss' : M.slotStart S.C (s + 1 + 1) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1),
      Nat.mul_add, Nat.mul_one]
  -- the slot of the slot's start, read by the spec's clock (the model's slot of a natural-number time is the
  -- spec's, `U`)
  have hslot₁ : S.C.slot ((M.slotStart S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (le_refl _)
      (by omega)
  -- `p`'s run and proposal, at its tick `i` (Lemma 19 over the record, the field `tick_proposal` of `F.tk3`, from the
  -- tick's input state, which satisfies the node invariant: `p` is outside the adversary set at its tick)
  obtain ⟨-, n₁', sent₁, hrun₁, hB₁⟩ := (tick_send_of_honestSendAt M F R E) hl hsent
  have hti : x.tickInput p (M.slotStart S.C (s + 1)) = x.st i p := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hpi : p ∉ A.corrupted i := E.not_mem_corrupted_of_tick hl
  have hInv : M.nodeInv S.C S.P S.X (x.tickInput p (M.slotStart S.C (s + 1))) := by
    rw [hti]
    exact (lem11_node_invariant M F S A x R E i p hpi).1
  obtain ⟨-, -, -, -, Hp, votes_pl, support_pl, -, -, hWalkP, hBdef⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n₁' _ sent₁ B
      hrun₁ hInv hB₁
  rw [hslot₁, Nat.add_sub_cancel] at hWalkP
  rw [hslot₁] at hBdef
  -- `p`'s walk, `PoolHeadOf`'s
  obtain ⟨votes_p, support_p, -, hW⟩ := hWalkP
  have hBpar : B.parent = Hp := by rw [hBdef]; rfl
  have hBne : B ≠ Block.genesis := by rw [hBdef]; exact fun h => by cases h
  -- Lemma 58 over the record: the end of the walk, in the viable tree, is a viable head of `p`'s frame
  -- (`walk_end_viable_of_below`, the frame's tree holding every block between the fgroot and one of its blocks, by
  -- the node invariant and Lemma 46), all at the tick's step `i`
  rw [hBpar] at hParentIn
  obtain ⟨-, hρH, W, hW', hHW⟩ :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 hParentIn
  have hClosed : ∀ Z' ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree, ∀ c : Block V,
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).fc_root.AncestorEq c → c.AncestorEq Z' →
        c ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree := by
    intro Z' hZ' c hρc hcZ
    rw [hti] at hZ' hρc ⊢
    refine (GoldilocksCorrectness.Record.Statements.Executions.frame_path_of_exec M F) S A x R E i p Z' c hZ' ?_ hcZ
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]
    refine ancestorEq_trans ((F_ancestorEq_fc_root_of_exec M F) S A x R E i p) ?_
    rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
    exact hρc
  have hVH : Hp ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads := by
    by_cases hHWe : Hp = W
    · rw [hHWe]
      exact (Finset.mem_inter.1 hW').2
    · exact (GoldilocksCorrectness.Record.Proofs.Routines.walk_end_viable_of_below M F) S.C _ _ _ _ _ _
        s Hp W hClosed hW hρH (Finset.mem_inter.1 hW').1 (Finset.mem_inter.1 hW').2 hHW hHWe
  obtain ⟨-, -, -, hfl⟩ :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hInv _).1 hVH
  -- `B`'s height is at least its parent's (Lemma 47 (b))
  rw [← hBpar] at hfl
  rcases ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B).2.1 hBne
    with h | h
  · rw [h]
    exact hfl
  · rw [h]
    exact Nat.le_succ_of_le hfl

end GoldilocksCorrectness.Record.Proofs.Executions

