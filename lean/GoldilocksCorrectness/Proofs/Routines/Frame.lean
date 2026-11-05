module
public import GoldilocksCorrectness.Statements.Routines.FrameDefs
public import GoldilocksCorrectness.Proofs.Routines.Merge
public import GoldilocksCorrectness.Proofs.Routines.Score
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.State
import all Goldilocks.FG.State

@[expose] public section

/-!
# The frame of a shape, the three boxes, and the walk's end

The proofs of the statements of `GoldilocksCorrectness/Statements/Routines/FrameStatements.lean`:
Lemma 56 (the frame `fg_to_ac S` of an FG state of a given shape, and the shape each of the three
boxes gives) and Lemma 58 (a head the fork choice answers inside the viable tree is a viable head).

The route of Lemma 58: the walk's end has no step (`ghost_step_none_of_ghost_eq`); a block of
the viable tree that is not a viable head has a viable head `W` of the tree as a strict
descendant, and the child of the block towards `W` is in the viable tree and passes the
eligibility test by its first case, so it would be a step (`ghost_step_none_not_eligible`).
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V]

/-! ## Lemma 56 -/

/-- **Lemma 56, the frame of a shape.** The proof; the audited statement is in
`Statements/Routines/FrameStatements.lean`.

The variables:
- `S`: the FG state; `ρ`: the root; `φ`: the value of `head_height_floor` (the least chain-state height a viable block may have). -/
theorem lem56_frame_of_shape (S : FGState V) (ρ : Block V) (φ : Height)
    (hShape : FrameShape S ρ φ) :
    (fg_to_ac S).fc_root = ρ ∧
    (∀ B : Block V, is_viable S B = true ↔ φ ≤ (S.σ B).h) ∧
    (∀ B : Block V, B ∈ (fg_to_ac S).viable_heads ↔
      B ∈ S.T ∧ S.F.AncestorEq B ∧ ρ.AncestorEq B ∧ φ ≤ (S.σ B).h) := by
  obtain ⟨hρ, hφ⟩ := hShape
  have hroot : (fg_to_ac S).fc_root = ρ := hρ
  have hviable : ∀ B : Block V, is_viable S B = true ↔ φ ≤ (S.σ B).h := by
    intro B
    simp only [is_viable, hφ, decide_eq_true_eq]
    exact Iff.rfl
  refine ⟨hroot, hviable, fun B => ?_⟩
  rw [← hρ]
  simp [fg_to_ac, Block.AncestorEq, and_assoc, ← hviable B]

/-- **Lemma 56, box 1: not contested; root `F`, `head_height_floor` equal to `h_max − 1`.** The proof; the audited
statement is in `Statements/Routines/FrameStatements.lean`.

The variables:
- `S`: the FG state. -/
theorem frameShape_of_boxOne (S : FGState V) (h : BoxOne S) :
    fg_contest S = false ∧ FrameShape S S.F (S.h_max - 1) := by
  unfold BoxOne at h
  have hne : S.h_max ≠ S.h_j + 1 := by
    intro he
    unfold Height at *
    omega
  have hc : fg_contest S = false := by
    simp only [fg_contest, Id.run, ne_eq]
    rw [if_pos hne]
    rfl
  refine ⟨hc, ?_, ?_⟩
  · simp only [get_fc_root, Id.run]
    rw [if_neg (by simp [hne])]
    rfl
  · simp only [head_height_floor, Id.run, hc]
    rfl

/-- **Lemma 56, box 2: root `J₀`, `head_height_floor` equal to `h_max − 1`.** The proof; the audited statement is in
`Statements/Routines/FrameStatements.lean`.

The variables:
- `S`: the FG state; `J₀`: the justified block. -/
theorem frameShape_of_boxTwo (S : FGState V) (J₀ : Block V) (h : BoxTwo S J₀) :
    FrameShape S J₀ (S.h_max - 1) := by
  obtain ⟨he, hc, hJ⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [get_fc_root, Id.run]
    rw [if_pos (by simp [he, hc])]
    exact hJ
  · simp only [head_height_floor, Id.run, hc]
    rfl

/-- **Lemma 56, box 3: `h_max = h_j + 1`; root `F`, `head_height_floor` equal to `h_max`.** The proof; the audited
statement is in `Statements/Routines/FrameStatements.lean`.

The variables:
- `S`: the FG state. -/
theorem frameShape_of_boxThree (S : FGState V) (h : BoxThree S) :
    S.h_max = S.h_j + 1 ∧ FrameShape S S.F S.h_max := by
  unfold BoxThree at h
  have he : S.h_max = S.h_j + 1 := by
    by_contra hne
    have hc : fg_contest S = false := by
      simp only [fg_contest, Id.run, ne_eq]
      rw [if_pos hne]
      rfl
    rw [hc] at h
    cases h
  refine ⟨he, ?_, ?_⟩
  · simp only [get_fc_root, Id.run]
    rw [if_neg (by simp [h])]
    rfl
  · simp only [head_height_floor, Id.run, h]
    rfl

/-! ## Lemma 58 -/

variable [Fintype V] [RootOrder]

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- The roots of a subset of a tree whose roots name its blocks name the subset's blocks.

The variables:
- `T`, `T'`: the subset and the tree. -/
theorem rootsNameBlocksIn_mono {T T' : Finset (Block V)} (hsub : T ⊆ T')
    (h : RootsNameBlocksIn T') : RootsNameBlocksIn T :=
  fun B hB B' hB' hr => h B (hsub hB) B' (hsub hB') hr

/-- **Lemma 58, the walk's end in the viable tree is a viable head.** The proof; the audited
statement is in `Statements/Routines/FrameStatements.lean`.

The variables:
- `C`: the parameters; `A`: the AC state; `Φ`: the frame; `t`: the time;
- `votes`, `support_votes`: the votes and the support votes counted; `s`: their slot;
- `H`: the head. -/
theorem lem58_walk_end_is_viable_head (C : Config) (A : ACState V) (Φ : Frame V) (t : Time)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (H : Block V)
    (hRoots : RootsNameBlocksIn Φ.tree)
    (hBetween : ∀ X ∈ Φ.tree, ∀ Y ∈ Φ.tree, ∀ Z : Block V, X.AncestorEq Z → Z.AncestorEq Y →
      Z ∈ Φ.tree)
    (hHead : get_head C A Φ t votes support_votes s = .ok H)
    (hIn : H ∈ viable_tree Φ Φ.tree) :
    H ∈ Φ.viable_heads := by
  by_contra hnot
  -- the walk's end has no step
  have hstop := ghost_step_none_of_ghost_eq (A := get_anchor A Φ t) hHead
  -- a viable head of the tree descending from `H`, and the child of `H` towards it
  obtain ⟨hHt, hcond⟩ := Finset.mem_filter.mp hIn
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
  obtain ⟨hρH, W, hW, hHW⟩ := hcond
  obtain ⟨hWt, hWv⟩ := Finset.mem_inter.mp hW
  have hne : H ≠ W := fun he => hnot (he ▸ hWv)
  obtain ⟨D, hDp, hDW⟩ := exists_child_towards hHW hne
  have hHD : H.AncestorEq D := ancestorEq_of_parent? hDp
  have hDt : D ∈ Φ.tree := hBetween H hHt W hWt D hHD hDW
  have hDv : D ∈ viable_tree Φ Φ.tree := by
    refine Finset.mem_filter.mpr ⟨hDt, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨ancestorEq_trans hρH hHD, W, hW, hDW⟩
  -- every child of `H` passes the eligibility test by its first case
  have hTest : ∀ D' ∈ viable_tree Φ Φ.tree, D'.parent? = some H →
      goldfish_eligible C Φ t votes support_votes s D' = .ok ((fun _ => true) D') := by
    intro D' _ hD'p
    have hpar : D'.parent = H := by
      cases D' with
      | genesis => simp [Block.parent?] at hD'p
      | node p _ _ _ _ _ _ =>
          simp only [Block.parent?, Option.some.injEq] at hD'p
          exact hD'p
    simp only [goldfish_eligible, hpar, hnot, not_false_eq_true, if_true]
    rfl
  have hScore : ∀ D' : Block V, D'.parent? = some H →
      goldfish_score Φ votes support_votes s D' =
        .ok ((fun D'' => (equivocators votes).card +
          (supportersOf Φ votes support_votes s D'').card) D') :=
    fun D' _ => goldfish_score_eq_ok hRoots votes support_votes s D'
  have hfalse := ghost_step_none_not_eligible _ (fun _ => true) hScore hTest
    (rootsNameBlocksIn_mono (Finset.filter_subset _ _) hRoots) hstop D hDv hDp
  cases hfalse

end GoldilocksCorrectness.Proofs.Routines
