module
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Routines.NoRaise
public import GoldilocksCorrectness.Proofs.Routines.WalkEnd
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.State
import all Goldilocks.Config
import all Goldilocks.FG.State

@[expose] public section

/-!
# What the fork choice of the AC answers, and what the Goldfish vote duty does

The theorems about the fork choice of an AC state: the anchor `get_anchor` (`get_anchor_mem_T`,
`get_anchor_cases`, `…_cases_locked`, `…_cases_live_lock`, `…_cases_viable`,
`get_anchor_root_or_viable`, `anchor_compatible`), the end of the walk from the anchor
(`walk_end_mem_T`, `walk_end_extends`, `walk_end_viable_of_below`), the viable tree
(`mem_viable_tree_of_frameShape`, `viable_tree_compatible`, `fork_choice_compatible`), the
Goldfish eligibility test (`goldfish_eligible_of_parent_not_viable`,
`goldfish_eligible_of_parent_viable`, `path_test_of_test_imp`), the head a vote names
(`vote_head_compatible_of_justified_past`, `vote_head_descends_of_F`); and what the Goldfish vote
duty `goldfish_vote` does to an AC state and puts on the wire (`goldfish_vote_votesInv`,
`…_from`, `…_grows`, `…_grows_from`, `…_ok`, `…_prov`, `…_emits_vote`, `…_sends`).

They read the routines, an AC state and a frame alone: no node state, no execution.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (FrameShape)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- Under a frame shape with root `ρ` and `head_height_floor` (the least chain-state height a viable block may have) equal to `φ`, a block of the tree that `ρ` is an ancestor of,
whose chain-state height is at least `φ`, is in the viable tree of the frame, when the finalized
block is `ρ` or an ancestor of it: it is its own viable head (Lemma 56).

The variables:
- `S`: the FG state; `ρ`: the root; `φ`: the value of `head_height_floor`; `B`: the block. -/
theorem mem_viable_tree_of_frameShape (S : FGState V) (ρ : Block V) (φ : Height) (B : Block V)
    (hShape : FrameShape S ρ φ)
    -- the finalized block is `ρ` or an ancestor of `ρ`
    (hFρ : S.F.AncestorEq ρ)
    -- `ρ` is `B` or an ancestor of `B`
    (hRootV : ρ.AncestorEq B)
    -- `B` is in the tree
    (hBin : B ∈ S.T)
    -- `B`'s chain-state height is at least `head_height_floor`
    (hφ : φ ≤ (S.σ B).h) :
    B ∈ viable_tree (fg_to_ac S) (fg_to_ac S).tree := by
  obtain ⟨hR, -, hH⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem56_frame_of_shape S ρ φ hShape
  have hFB : S.F.AncestorEq B := ancestorEq_trans hFρ hRootV
  have hVH : B ∈ (fg_to_ac S).viable_heads := (hH B).2 ⟨hBin, hFB, hRootV, hφ⟩
  have hT : B ∈ (fg_to_ac S).tree := (mem_fg_to_ac_tree _ _).2 ⟨hBin, hFB⟩
  simp only [viable_tree, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hT, ?_, B, Finset.mem_inter.2 ⟨hT, hVH⟩, ancestorEq_refl B⟩
  rw [hR]
  exact hRootV

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- Every answer of the Goldfish vote duty at a time `t ≤ t'` keeps `VotesInv` at `t'` and the
block stamps: it admits at most the node's own vote, at `t`.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `t'`: the bound; `v`: the voter. -/
theorem goldfish_vote_votesInv (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t t' : Time) (v : V) (h : VotesInv P A t') (ht : t ≤ t') :
    DREBPost (goldfish_vote C P A Φ t v)
      (fun A' => VotesInv P A' t' ∧ A'.timestamp_block = A.timestamp_block) := by
  simp only [goldfish_vote]
  repeat' first
    | exact DREBPost.pure ⟨h, rfl⟩
    | exact DREBPost.pure ⟨on_goldfish_vote_votesInv C P A t t' _ h ht,
        on_goldfish_vote_timestamp_block C P A t _⟩
    | refine DREBPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- The Goldfish vote duty at a time `t ≤ t'` keeps "`VotesInv` at `t'`, with the block stamps of
`A₀`". -/
theorem goldfish_vote_from {P : Provisional V} {A₀ : ACState V} {t' : Time} (C : Config)
    (A : ACState V) (Φ : Frame V) (t : Time) (v : V) (ht : t ≤ t')
    (h : VotesInv P A t' ∧ A.timestamp_block = A₀.timestamp_block) :
    DREBPost (goldfish_vote C P A Φ t v)
      (fun A' => VotesInv P A' t' ∧ A'.timestamp_block = A₀.timestamp_block) :=
  (goldfish_vote_votesInv C P A Φ t t' v h.1 ht).mono (fun _ h' => ⟨h'.1, h'.2.trans h.2⟩)

end

end

section

open GoldilocksCorrectness.Statements.Routines (JustifiedInTree)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] in
/-- The anchor of a walk is a block of the FG state's tree, when the finalized and the justified
blocks are: it is a locked block of the viable tree of the frame's tree, or the root of the fork
choice, which is the justified or the finalized block.

The variables:
- `A`: the AC state; `S`: the FG state; `t`: the time. -/
theorem get_anchor_mem_T (A : ACState V) (S : FGState V) (t : Time)
    -- the finalized block is in the tree
    (hFT : S.F ∈ S.T)
    -- the justified block is in the tree
    (hJT : JustifiedInTree S) :
    get_anchor A (fg_to_ac S) t ∈ S.T := by
  simp only [get_anchor, Id.run]
  generalize hD : Block.deepest?
    {B ∈ viable_tree (fg_to_ac S) (fg_to_ac S).tree | is_locked A (fg_to_ac S) t B} = D
  cases D with
  | none =>
      show get_fc_root S ∈ S.T
      simp only [get_fc_root, Id.run]
      split
      · exact hJT
      · exact hFT
  | some B =>
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
        Option.get_some]
      have hmem := GoldilocksCorrectness.Proofs.Routines.deepest?_mem hD
      exact ((mem_fg_to_ac_tree _ _).1
        (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).1).1

end

end

section

open GoldilocksCorrectness.Statements.Routines (JustifiedInTree)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]
variable [RootOrder]

omit [Fintype V] in
/-- The end of a walk, in the viable tree or the anchor, is a block of the tree, when the
finalized and the justified blocks are.

The variables:
- `A`: the AC state; `S`: the FG state; `t`: the time; `H`: the end of the walk. -/
theorem walk_end_mem_T (A : ACState V) (S : FGState V) (t : Time) (H : Block V)
    (hEnd : H ∈ viable_tree (fg_to_ac S) (fg_to_ac S).tree ∨ H = get_anchor A (fg_to_ac S) t)
    (hFT : S.F ∈ S.T) (hJT : JustifiedInTree S) : H ∈ S.T := by
  rcases hEnd with h | rfl
  · exact ((mem_fg_to_ac_tree _ _).1 (Finset.mem_filter.mp h).1).1
  · simp only [get_anchor, Id.run]
    generalize hD : Block.deepest?
      {B ∈ viable_tree (fg_to_ac S) (fg_to_ac S).tree | is_locked A (fg_to_ac S) t B} = D
    cases D with
    | none =>
        show get_fc_root S ∈ S.T
        simp only [get_fc_root, Id.run]
        split
        · exact hJT
        · exact hFT
    | some B =>
        simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
          Option.get_some]
        have hmem := GoldilocksCorrectness.Proofs.Routines.deepest?_mem hD
        exact ((mem_fg_to_ac_tree _ _).1
          (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).1).1

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] in
/-- The anchor of a walk is the fork-choice root, or a block of the viable tree that is locked:
an ancestor of, or equal to, the block of a lock entry live at the time (`get_anchor`).

The variables:
- `A`: the AC state; `Φ`: the frame; `t`: the time. -/
theorem get_anchor_cases_locked (A : ACState V) (Φ : Frame V) (t : Time) :
    get_anchor A Φ t = Φ.fc_root ∨ (get_anchor A Φ t ∈ viable_tree Φ Φ.tree ∧
      ∃ e ∈ A.lock_entries, is_live Φ t e = true ∧ (get_anchor A Φ t).AncestorEq e.B) := by
  simp only [get_anchor, Id.run]
  generalize hD : Block.deepest? {B ∈ viable_tree Φ Φ.tree | is_locked A Φ t B} = D
  cases D with
  | none => exact Or.inl rfl
  | some B =>
    right
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some]
    have hmem := Finset.mem_filter.mp (GoldilocksCorrectness.Proofs.Routines.deepest?_mem hD)
    refine ⟨hmem.1, ?_⟩
    have h2 := hmem.2
    simp only [is_locked, decide_eq_true_eq] at h2
    obtain ⟨e, he, hl, hBe⟩ := h2
    exact ⟨e, he, hl, hBe⟩

end

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The walk's end `H` of the Goldfish fork choice through the viable tree of `VT` has no child
on the way to a viable head of `VT` unless it is a viable head itself: when `P` is the walk's
end, on the chain of the frame's fork-choice root, `P` an ancestor of a viable head `Z ∈ VT` other
than `Z`, and `VT` holds every block from the root to a block of `VT`, then `P` is a viable head.

Why: as Lemma 58: the child of `P` towards `Z` is in the viable tree of `VT` and passes the
eligibility test by its first case when `P` is not a viable head, so the walk would step.

The variables:
- `C`: the parameters; `Φ`: the frame; `t`: the time; `A`: the anchor; `VT`: the tree;
- `votes`, `sv`: the counted votes; `s`: their slot; `H`: the walk's end; `Z`: the viable head. -/
theorem walk_end_viable_of_below (C : Config) (Φ : Frame V) (t : Time) (A : Block V)
    (VT : Finset (Block V)) (votes sv : Finset (GoldfishVote V)) (s : Slot) (H Z : Block V)
    (hRoots : RootsNameBlocksIn Φ.tree) (hVT : VT ⊆ Φ.tree)
    (hClosed : ∀ Z' ∈ VT, ∀ c : Block V, Φ.fc_root.AncestorEq c → c.AncestorEq Z' → c ∈ VT)
    (hWalk : goldfish_fork_choice C Φ t A (viable_tree Φ VT) votes sv s = .ok H)
    (hρH : Φ.fc_root.AncestorEq H) (hZ : Z ∈ VT) (hZv : Z ∈ Φ.viable_heads)
    (hHZ : H.AncestorEq Z) (hne : H ≠ Z) :
    H ∈ Φ.viable_heads := by
  by_contra hnot
  have hstop := GoldilocksCorrectness.Proofs.Routines.ghost_step_none_of_ghost_eq hWalk
  obtain ⟨D, hDp, hDZ⟩ := GoldilocksCorrectness.Proofs.Routines.exists_child_towards hHZ hne
  have hHD : H.AncestorEq D := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_parent? hDp
  have hDVT : D ∈ VT := hClosed Z hZ D (ancestorEq_trans hρH hHD) hDZ
  have hDv : D ∈ viable_tree Φ VT := by
    refine Finset.mem_filter.mpr ⟨hDVT, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨ancestorEq_trans hρH hHD, Z, Finset.mem_inter.mpr ⟨hZ, hZv⟩, hDZ⟩
  have hTest : ∀ D' ∈ viable_tree Φ VT, D'.parent? = some H →
      goldfish_eligible C Φ t votes sv s D' = .ok ((fun _ => true) D') := by
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
      goldfish_score Φ votes sv s D' =
        .ok ((fun D'' => (equivocators votes).card +
          (GoldilocksCorrectness.Proofs.Routines.supportersOf Φ votes sv s D'').card) D') :=
    fun D' _ => GoldilocksCorrectness.Proofs.Routines.goldfish_score_eq_ok hRoots votes sv s D'
  have hfalse := GoldilocksCorrectness.Proofs.Routines.ghost_step_none_not_eligible _
    (fun _ => true) hScore hTest
    (GoldilocksCorrectness.Proofs.Routines.rootsNameBlocksIn_mono
      ((Finset.filter_subset _ _).trans hVT) hRoots) hstop D hDv hDp
  cases hfalse

/-- **The end of the Goldfish fork choice extends a block every viable head extends.** When the
walk of the Goldfish fork choice from the anchor `A` (the fork-choice root, or a block of the viable
tree of the frame's tree) through the viable tree of `VT` ends at `H`; `VT` holds a viable head
`Y` and every block from the root to a block of `VT`; every viable head is `F'` or a descendant of
`F'`; and no strict ancestor of `F'` is a viable head — then `H` is `F'` or a descendant of `F'`.

Why: the end is the anchor or a block of the viable tree of `VT`. A block of that tree is an
ancestor of a viable head `W` of `VT`, so on `F'`'s chain; if it were a strict ancestor of `F'` it
would not be a viable head, and its child towards `W` would be a step
(`walk_end_viable_of_below`). The anchor is an ancestor of a viable head, so on `F'`'s chain; if it
were a strict ancestor of `F'`, it would be one of `Y` too, and its child towards `Y` a step.

The variables:
- `C`: the parameters; `Φ`: the frame; `t`: the time; `A`: the anchor; `VT`: the tree;
- `votes`, `sv`: the counted votes; `s`: their slot; `H`: the walk's end; `F'`: the block;
  `Y`: a viable head of `VT`. -/
theorem walk_end_extends (C : Config) (Φ : Frame V) (t : Time) (A : Block V)
    (VT : Finset (Block V)) (votes sv : Finset (GoldfishVote V)) (s : Slot) (H F' Y : Block V)
    (hRoots : RootsNameBlocksIn Φ.tree) (hVT : VT ⊆ Φ.tree)
    (hClosed : ∀ Z' ∈ VT, ∀ c : Block V, Φ.fc_root.AncestorEq c → c.AncestorEq Z' → c ∈ VT)
    (hA : A = Φ.fc_root ∨ A ∈ viable_tree Φ Φ.tree)
    (hWalk : goldfish_fork_choice C Φ t A (viable_tree Φ VT) votes sv s = .ok H)
    (hρV : ∀ W ∈ Φ.viable_heads, Φ.fc_root.AncestorEq W)
    (hYVT : Y ∈ VT) (hY : Y ∈ Φ.viable_heads)
    (hP : ∀ W ∈ Φ.viable_heads, F'.AncestorEq W)
    (hQ : ∀ B : Block V, B.AncestorEq F' → B ≠ F' → B ∉ Φ.viable_heads) :
    F'.AncestorEq H := by
  -- a block on the root's chain, an ancestor of a viable head `Z ∈ VT` and of `F'`, is `F'`
  have key : ∀ P : Block V, P = H → Φ.fc_root.AncestorEq P → ∀ Z ∈ VT, Z ∈ Φ.viable_heads →
      P.AncestorEq Z → F'.AncestorEq P := by
    intro P hPH hρP Z hZ hZv hPZ
    rcases ancestorEq_compatible hPZ (hP Z hZv) with hPF | hFP
    · by_cases he : P = F'
      · rw [he]
        exact ancestorEq_refl _
      · have hPv : P ∉ Φ.viable_heads := hQ P hPF he
        have hne : P ≠ Z := fun h => hPv (h ▸ hZv)
        subst hPH
        exact absurd (walk_end_viable_of_below C Φ t A VT votes sv s P Z hRoots hVT hClosed hWalk
          hρP hZ hZv hPZ hne) hPv
    · exact hFP
  rcases GoldilocksCorrectness.Proofs.Routines.ghost_mem_tree_or_eq hWalk with hHA | hHT
  · -- the end is the anchor
    have hρA : Φ.fc_root.AncestorEq A := by
      rcases hA with h | h
      · rw [h]
        exact ancestorEq_refl _
      · have h' := (Finset.mem_filter.mp h).2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
        exact h'.1
    -- a viable head extending the anchor
    obtain ⟨Z, hZv, hAZ⟩ : ∃ Z ∈ Φ.viable_heads, A.AncestorEq Z := by
      rcases hA with h | h
      · exact ⟨Y, hY, h ▸ hρV Y hY⟩
      · have h' := (Finset.mem_filter.mp h).2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
        obtain ⟨-, W, hW, hAW⟩ := h'
        exact ⟨W, (Finset.mem_inter.mp hW).2, hAW⟩
    rcases ancestorEq_compatible hAZ (hP Z hZv) with hAF | hFA
    · -- the anchor is an ancestor of `F'`, so of `Y`
      have hAY : A.AncestorEq Y := ancestorEq_trans hAF (hP Y hY)
      rw [hHA]
      exact key A hHA.symm hρA Y hYVT hY hAY
    · rw [hHA]
      exact hFA
  · -- the end is in the viable tree of `VT`
    have h' := (Finset.mem_filter.mp hHT).2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨hρH, W, hW, hHW⟩ := h'
    obtain ⟨hWVT, hWv⟩ := Finset.mem_inter.mp hW
    exact key H rfl hρH W hWVT hWv hHW

omit [Fintype V] in
/-- The anchor of a walk is the fork-choice root or a block of the viable tree of the frame's
tree (`get_anchor`).

The variables:
- `A`: the AC state; `Φ`: the frame; `t`: the time. -/
theorem get_anchor_cases (A : ACState V) (Φ : Frame V) (t : Time) :
    get_anchor A Φ t = Φ.fc_root ∨ get_anchor A Φ t ∈ viable_tree Φ Φ.tree := by
  simp only [get_anchor, Id.run]
  generalize hD : Block.deepest? {B ∈ viable_tree Φ Φ.tree | is_locked A Φ t B} = D
  cases D with
  | none => exact Or.inl rfl
  | some B =>
    right
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some]
    exact (Finset.mem_filter.mp (GoldilocksCorrectness.Proofs.Routines.deepest?_mem hD)).1

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] in
/-- The anchor is the root of the fork choice, or a block of the viable tree.

The variables:
- `A`: the AC state; `Φ`: the frame; `t`: the time. -/
theorem get_anchor_root_or_viable (A : ACState V) (Φ : Frame V) (t : Time) :
    get_anchor A Φ t = Φ.fc_root ∨ get_anchor A Φ t ∈ viable_tree Φ Φ.tree := by
  simp only [get_anchor, Id.run]
  generalize hD : Block.deepest? {B ∈ viable_tree Φ Φ.tree | is_locked A Φ t B} = D
  cases D with
  | none => exact Or.inl rfl
  | some B =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some]
    have hmem := GoldilocksCorrectness.Proofs.Routines.deepest?_mem hD
    rw [Finset.mem_filter] at hmem
    exact Or.inr hmem.1

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] in
/-- The anchor is the root of the fork choice, or an ancestor of the block of a live lock entry.

The variables:
- `A`: the AC state; `Φ`: the frame; `t`: the time. -/
theorem get_anchor_cases_live_lock (A : ACState V) (Φ : Frame V) (t : Time) :
    get_anchor A Φ t = Φ.fc_root ∨
      ∃ e ∈ A.lock_entries, is_live Φ t e = true ∧ (get_anchor A Φ t).AncestorEq e.B := by
  simp only [get_anchor, Id.run]
  generalize hD : Block.deepest? {B ∈ viable_tree Φ Φ.tree | is_locked A Φ t B} = D
  cases D with
  | none => exact Or.inl rfl
  | some B =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some]
    have hmem := deepest?_mem hD
    rw [Finset.mem_filter] at hmem
    have hlocked := hmem.2
    simp only [is_locked, decide_eq_true_eq] at hlocked
    obtain ⟨e, he, hlive, hBe⟩ := hlocked
    exact Or.inr ⟨e, he, hlive, hBe⟩

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- Every answer of the Goldfish vote duty at the time `t`, from a pool filed by slot, keeps the
pool filed by slot, holds the pool's votes and stamps, keeps the block stamps, and stamps what it
adds with `t`: it admits at most the node's own vote.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the voter. -/
theorem goldfish_vote_grows (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) (hk : SlotKeyed A) :
    DREBPost (goldfish_vote C P A Φ t v)
      (fun A' => SlotKeyed A' ∧ ACGrows A A' ∧ A'.timestamp_block = A.timestamp_block ∧
        ACStampsAt A A' t) := by
  simp only [goldfish_vote]
  repeat' first
    | exact DREBPost.pure ⟨hk, ACGrows.refl A, rfl, ACStampsAt.refl A t⟩
    | exact DREBPost.pure (on_goldfish_vote_grows C P A t _ hk)
    | refine DREBPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- The Goldfish vote duty at the time `t` keeps "filed by slot, holding `A₀`'s votes and stamps,
with `A₀`'s block stamps, what it holds beyond `A₀` stamped `t`". -/
theorem goldfish_vote_grows_from {P : Provisional V} {A₀ : ACState V} (C : Config)
    (A : ACState V) (Φ : Frame V) (t : Time) (v : V)
    (h : SlotKeyed A ∧ ACGrows A₀ A ∧ A.timestamp_block = A₀.timestamp_block ∧
      ACStampsAt A₀ A t) :
    DREBPost (goldfish_vote C P A Φ t v)
      (fun A' => SlotKeyed A' ∧ ACGrows A₀ A' ∧ A'.timestamp_block = A₀.timestamp_block ∧
        ACStampsAt A₀ A' t) :=
  (goldfish_vote_grows C P A Φ t v h.1).mono
    (fun _ h' => ⟨h'.1, h.2.1.trans h'.2.1, h'.2.2.1.trans h.2.2.1,
      h.2.2.2.trans h'.2.1 h'.2.2.2⟩)

end

end

section

open GoldilocksCorrectness.Statements.Routines (PoolStamped)

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The Goldfish vote duty answers when no two blocks of the frame's tree share a root, every vote
of the pool is stamped and every block of the frame's tree is stamped.

The variables:
- `C`: the configuration; `P`: the provisional parameters; `A`: the AC state; `Φ`: the frame;
  `t`: the time; `v`: the validator. -/
theorem goldfish_vote_ok (C : Config) (P : Provisional V) (A : ACState V) {Φ : Frame V}
    (hRoots : RootsNameBlocksIn Φ.tree) (t : Time) (v : V) (hPool : PoolStamped A)
    -- every block of the frame's tree is stamped
    (hb : ∀ H ∈ Φ.tree, A.timestamp_block H ≠ none) : DREBOk (goldfish_vote C P A Φ t v) := by
  simp only [goldfish_vote]
  -- the votes stamped before the freeze: a subset of the pool, so stamped
  refine DREBOk.bind (P := fun R => ∀ vote ∈ R, A.timestamp_vote vote ≠ none)
    (DREBOk.liftM (beforeCutoff_ok _ _ _ (pool_stamped hPool _)))
    (DREBPost.liftM (fun R hR vote hv =>
      pool_stamped hPool _ vote ((mem_beforeCutoff_iff hR vote).1 hv).1))
    (fun votes hvotes => ?_)
  -- the support votes
  refine DREBOk.bind_any (DREBOk.liftM (filterM_eq_ok_of_total _ _ (fun vote hvote =>
    DREOk.bind_any (tau_ok A Φ vote hRoots (hvotes vote hvote) hb) (fun _ => DREOk.pure _))))
    (fun _ => ?_)
  -- the included support votes that resolve
  refine DREBOk.bind_any (DREBOk.liftM (filterM_eq_ok_of_total _ _ (fun vote _ => by
    first
      | exact resolved_ok _ vote hRoots
      | exact DREOk.bind_any (resolved_ok _ vote hRoots) (fun _ => DREOk.pure _)))) (fun _ => ?_)
  -- the voter's block tree
  refine DREBOk.bind_any (DREBOk.liftM (voter_block_tree_ok C A Φ _ hb)) (fun _ => ?_)
  -- the head
  refine DREBOk.bind_any (DREBOk.liftM (get_head_in_tree_ok C A hRoots t _ _ _ _)) (fun _ => ?_)
  -- the vote, when `v` is in the committee
  refine DREBOk.ite (fun _ => ?_) (fun _ => DREBOk.pure _)
  exact DREBOk.bind_any (DREBOk.broadcast _) (fun _ => DREBOk.pure _)

end

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- A block whose parent is not a viable head passes the Goldfish eligibility test. -/
theorem goldfish_eligible_of_parent_not_viable (C : Config) (Φ : Frame V) (t : Time)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (D : Block V)
    (hD : D.parent ∉ Φ.viable_heads) :
    goldfish_eligible C Φ t votes support_votes s D = .ok true := by
  simp only [goldfish_eligible, hD, not_false_eq_true, if_true]
  rfl

omit [RootOrder] in
/-- A block whose parent is a viable head, of a slot other than the current one, passes the
Goldfish eligibility test exactly when twice its score exceeds the voters. -/
theorem goldfish_eligible_of_parent_viable (C : Config) (Φ : Frame V) (t : Time)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (D : Block V) (m : ℕ)
    (hD : D.parent ∈ Φ.viable_heads) (hDs : D.slot ≠ C.slot t)
    (hm : goldfish_score Φ votes support_votes s D = .ok m) :
    goldfish_eligible C Φ t votes support_votes s D =
      .ok (decide (voters_count votes < 2 * m)) := by
  simp only [goldfish_eligible, hD, not_true_eq_false, if_false, hDs, hm, GoldilocksCorrectness.Proofs.Routines.dre_bind_ok]
  rfl

omit [Fintype V] in
/-- The second test accepts every block after `X` up to `P`'s parent, when the first walk ends at
`P`'s parent and passes `X`, and on every child of a block from `X` to `P`'s parent the second
test accepts what the first accepts. -/
theorem path_test_of_test_imp {A_p X P : Block V} {tree_p : Finset (Block V)}
    {score_p : Block V → DRE Nat} {eligible_p : Block V → DRE Bool} (b_p b_w : Block V → Bool)
    (hTestP : ∀ D : Block V, eligible_p D = .ok (b_p D))
    (hWalkP : ghost A_p tree_p score_p eligible_p = .ok P.parent)
    (hXOnWalkP : A_p.AncestorEq X ∧ X.AncestorEq P.parent)
    (hImp : ∀ Y : Block V, X.AncestorEq Y → Y.AncestorEq P.parent →
      ∀ D : Block V, D.parent? = some Y → b_p D = true → b_w D = true) :
    ∀ Y : Block V, X.AncestorEq Y → Y ≠ X → Y.AncestorEq P.parent → b_w Y = true := by
  intro Y hXY hYX hYP
  have hYg : Y ≠ Block.genesis := by
    rintro rfl
    exact hYX ((GoldilocksCorrectness.Proofs.Routines.ancestorEq_genesis_iff X).1 hXY).symm
  have hYpar := parent?_eq_some_parent hYg
  have hXQ : X.AncestorEq Y.parent :=
    GoldilocksCorrectness.Proofs.Routines.ancestorEq_parent_of_ne hXY (Ne.symm hYX)
  have hQP : Y.parent.AncestorEq P.parent := ancestorEq_trans (ancestorEq_of_parent? hYpar) hYP
  have hYA : Y ≠ A_p := by
    intro h
    have hYXa : Y.AncestorEq X := h ▸ hXOnWalkP.1
    exact hYX (ancestorEq_antisymm hXY hYXa).symm
  exact hImp Y.parent hXQ hQP Y hYpar
    (GoldilocksCorrectness.Proofs.Routines.ghost_visited_test_true b_p hTestP hWalkP Y
      (ancestorEq_trans hXOnWalkP.1 hXY) hYA hYP)

end

section

set_option linter.unusedSectionVars false
open GoldilocksCorrectness.Statements.Routines (chainStateOf)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- When every viable head descends from `B`, every block of the viable tree of any tree is
compatible with `B`.

The variables:
- `Φ`: the frame; `tree`: the tree; `B`: the block.

Read aloud: when every viable head is `B` or a descendant of `B`, no block of a viable tree
conflicts with `B`. -/
theorem viable_tree_compatible [RootOrder] (Φ : Frame V) (tree : Finset (Block V)) (B : Block V)
    (hH : ∀ W ∈ Φ.viable_heads, B.AncestorEq W) :
    ∀ D ∈ viable_tree Φ tree, D.compatible B = true := by
  intro D hD
  simp only [viable_tree, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hD
  obtain ⟨-, -, W, hW, hDW⟩ := hD
  have hBW := hH W (Finset.mem_inter.1 hW).2
  exact (compatible_iff _ _).2 (ancestorEq_compatible hDW hBW)

/-- The anchor is the root of the fork choice, or a block of the viable tree of the frame's
tree.

The variables:
- `A`: the AC state; `Φ`: the frame; `t`: the time.

Read aloud: every walk starts from the fork-choice root or from a block of the viable tree. -/
theorem get_anchor_cases_viable [RootOrder] (A : ACState V) (Φ : Frame V) (t : Time) :
    get_anchor A Φ t = Φ.fc_root ∨ get_anchor A Φ t ∈ viable_tree Φ Φ.tree := by
  simp only [get_anchor, Id.run]
  generalize hD : Block.deepest? {X ∈ viable_tree Φ Φ.tree | is_locked A Φ t X} = D
  cases D with
  | none => exact Or.inl rfl
  | some X =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
      Option.get_some]
    have hmem := deepest?_mem hD
    rw [Finset.mem_filter] at hmem
    exact Or.inr hmem.1

/-- The anchor is compatible with `B` when the root of the fork choice and every block of the
viable tree of the frame's tree are.

The variables:
- `A`: the AC state; `Φ`: the frame; `t`: the time; `B`: the block.

Read aloud: when the fork-choice root and the viable tree do not conflict with `B`, neither does
the anchor. -/
theorem anchor_compatible [RootOrder] (A : ACState V) (Φ : Frame V) (t : Time) (B : Block V)
    (hroot : Φ.fc_root.compatible B = true)
    (htree : ∀ D ∈ viable_tree Φ Φ.tree, D.compatible B = true) :
    (get_anchor A Φ t).compatible B = true := by
  rcases get_anchor_cases_viable A Φ t with h | h
  · rw [h]; exact hroot
  · exact htree _ h

/-- The end of the Goldfish fork choice is compatible with `B` when its start and every block of
the tree walked are.

The variables:
- `C`: the parameters; `Φ`: the frame; `t`: the time; `anchor`: the start of the walk; `tree`:
  the tree walked; `votes`, `sv`: the votes and the support votes; `s`: the slot; `B`: the block;
  `H`: the end of the walk.

Read aloud: a walk that starts and stays among blocks compatible with `B` ends at one. -/
theorem fork_choice_compatible [RootOrder] (C : Config) (Φ : Frame V) (t : Time)
    (anchor : Block V) (tree : Finset (Block V)) (votes sv : Finset (GoldfishVote V)) (s : Slot)
    (B H : Block V) (hA : anchor.compatible B = true) (hT : ∀ D ∈ tree, D.compatible B = true)
    (h : goldfish_fork_choice C Φ t anchor tree votes sv s = .ok H) : H.compatible B = true := by
  unfold goldfish_fork_choice at h
  rcases ghost_mem_tree_or_eq h with h' | h'
  · rw [h']; exact hA
  · exact hT H h'

/-- The head of the Goldfish vote, in the form Lemma 14 (`lem14_tick_vote_walk`) gives it (the
fork choice from the anchor of the revoked AC state `A'`, through the viable tree of the voter
tree `vbt`), is compatible with `B` at an FG state justified past `B`.

The variables:
- `C`: the parameters; `n`: the FG state; `B`: the block; `A'`: the AC state the anchor is read
  from; `t`: the time; `vbt`: the voter tree; `votes`, `sv`: the votes and the support votes;
  `s`: the slot; `H`: the head.

Read aloud: at an FG state whose caches are compatible with `B`, whose held blocks two heights
past `B` descend from `B`, with `h_j < h_max` and `h_j ≥ h(B) + 1`, the head of any Goldfish vote
it computes is compatible with `B`. -/
theorem vote_head_compatible_of_justified_past [RootOrder] (C : Config) (n : FGState V)
    (B : Block V) (hσ : ChainStatesComputed C n)
    (hJ : n.J.AncestorEq B ∨ B.AncestorEq n.J)
    (hJh : (chainStateOf C n.J).h = n.h_j) (hFJ : n.F.AncestorEq n.J)
    (hTwo : ∀ D ∈ n.T, (chainStateOf C B).h + 2 ≤ (chainStateOf C D).h → B.AncestorEq D)
    (hjmax : n.h_j < n.h_max)
    (hSafe : (chainStateOf C B).h + 1 ≤ n.h_j)
    (A' : ACState V) (t : Time) (vbt : Finset (Block V)) (votes sv : Finset (GoldfishVote V))
    (s : Slot) (H : Block V)
    (h : goldfish_fork_choice C (fg_to_ac n) t (get_anchor A' (fg_to_ac n) t)
      (viable_tree (fg_to_ac n) vbt) votes sv s = .ok H) :
    H.compatible B = true := by
  have hheads := viable_head_descends_of_justified_past C n B hσ hJ hJh hTwo hjmax hSafe
  have hroot : (fg_to_ac n).fc_root.compatible B = true := fc_root_compatible n B hJ hFJ
  exact fork_choice_compatible C _ t _ _ votes sv s B H
    (anchor_compatible A' _ t B hroot (viable_tree_compatible _ _ B hheads))
    (viable_tree_compatible _ _ B hheads) h

/-- **The head of a Goldfish vote descends from the voter's finalized block.** The fork choice
from the anchor of any AC state `A'`, through the viable tree of any tree `vbt`, ends at `n.F` or
a descendant of `n.F`, when `n.F` is an ancestor of `n.J` or `n.J`.

Why: the anchor is the root of the fork choice or a block of a viable tree
(`get_anchor_cases_viable`), and the walk ends at the anchor or at a block of the viable tree it
walks (`ghost_mem_tree_or_eq`); every block of a viable tree is the root of the fork choice or a
descendant of it, and that root is `n.J` or `n.F`, of which `n.F` is an ancestor or which it is.

The variables:
- `C`: the parameters; `n`: the FG state; `A'`: the AC state the anchor is read from; `t`: the
  time; `vbt`: the voter tree; `votes`, `sv`: the votes and the support votes; `s`: the slot;
  `H`: the head.

Read aloud: the head of a Goldfish vote is the voter's finalized block or a descendant of it. -/
theorem vote_head_descends_of_F [RootOrder] (C : Config) (n : FGState V) (A' : ACState V)
    (t : Time) (vbt : Finset (Block V)) (votes sv : Finset (GoldfishVote V)) (s : Slot)
    (H : Block V) (hFJ : n.F.AncestorEq n.J)
    (h : goldfish_fork_choice C (fg_to_ac n) t (get_anchor A' (fg_to_ac n) t)
      (viable_tree (fg_to_ac n) vbt) votes sv s = .ok H) :
    n.F.AncestorEq H := by
  have hFr : n.F.AncestorEq (fg_to_ac n).fc_root := F_ancestorEq_get_fc_root n hFJ
  have hvt : ∀ (tree : Finset (Block V)), ∀ D ∈ viable_tree (fg_to_ac n) tree,
      n.F.AncestorEq D := by
    intro tree D hD
    simp only [viable_tree, Finset.mem_filter, Bool.and_eq_true] at hD
    exact ancestorEq_trans hFr hD.2.1
  have hA : n.F.AncestorEq (get_anchor A' (fg_to_ac n) t) := by
    rcases get_anchor_cases_viable A' (fg_to_ac n) t with h' | h'
    · rw [h']; exact hFr
    · exact hvt _ _ h'
  unfold goldfish_fork_choice at h
  rcases ghost_mem_tree_or_eq h with h' | h'
  · rw [h']; exact hA
  · exact hvt _ _ h'

end

end

section

open Goldilocks

section

variable {V : Type} [DecidableEq V] [Fintype V]
variable [RootOrder]

/-- Every answer of the Goldfish vote duty adds to the pool only a vote it broadcast.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the voter. -/
theorem goldfish_vote_prov (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) :
    DREBSpec (fun A' l => ∀ s : Slot, ∀ vote ∈ A'.gf_votes s, vote ∉ A.gf_votes s →
        NamedObject.gfVote vote ∈ l)
      (goldfish_vote C P A Φ t v) := by
  simp only [goldfish_vote]
  repeat' first
    | exact DREBSpec.pure (fun s vote hv hn => absurd hv hn)
    | refine DREBSpec.bind_liftPost (DREPost.true _) (fun _ _ => ?_)
    | refine DREBSpec.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBSpec.ite (fun _ => ?_) (fun _ => ?_)
    | exact DREBSpec.broadcast_pure _ (fun s vote' hv hn => by
        rw [on_goldfish_vote_new C P A t _ s vote' hv hn]
        exact List.mem_singleton_self _)

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- What the Goldfish vote duty of `v` at `t` sends, when `v` is a member of the committee of the
slot of `t`: a Goldfish vote of `v` for that slot.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the voter.

Read aloud: a committee member's vote duty sends its vote. -/
theorem goldfish_vote_emits_vote (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) :
    DREBEmits (fun l => v ∈ P.committee (C.slot t) →
        ∃ h : BlockId, NamedObject.gfVote (GoldfishVote.mk v (C.slot t) h) ∈ l)
      (goldfish_vote C P A Φ t v) := by
  simp only [goldfish_vote]
  repeat' first
    | refine DREBEmits.bind_nil (DREBEmits.liftM _) (fun _ => ?_)
    | refine DREBEmits.bind_nil (DREBEmits.monadLift _) (fun _ => ?_)
    | refine DREBEmits.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
    | exact DREBEmits.pure (fun h => absurd h (by assumption))
    | refine (DREBEmits.broadcast_then _ (fun _ => DREBEmits.pure rfl)).mono ?_
  rintro _ rfl _
  exact ⟨_, List.mem_singleton_self _⟩

end

section

open Goldilocks

section

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- What the Goldfish vote duty of `v` at the time `t` sends: at most one object, a Goldfish vote
of `v` for the slot of `t`, `C.slot t`.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the voter;
- `h`: the root the vote names.

Read aloud: the duty sends at most one object, `v`'s Goldfish vote for the slot of `t`. -/
theorem goldfish_vote_sends (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) :
    DREBEmits (fun l => l.length ≤ 1 ∧
        ∀ o ∈ l, ∃ h : BlockId, o = NamedObject.gfVote (GoldfishVote.mk v (C.slot t) h))
      (goldfish_vote C P A Φ t v) := by
  simp only [goldfish_vote]
  repeat' first
    | exact DREBEmits.pure ⟨Nat.zero_le _, fun _ h => absurd h List.not_mem_nil⟩
    | refine DREBEmits.bind_nil (DREBEmits.liftM _) (fun _ => ?_)
    | refine DREBEmits.bind_nil (DREBEmits.monadLift _) (fun _ => ?_)
    | refine DREBEmits.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
    | refine (DREBEmits.broadcast_then _ (fun _ => DREBEmits.pure rfl)).mono ?_
  rintro _ rfl
  exact ⟨by simp, fun o ho => ⟨_, by simpa using ho⟩⟩

end

end

section

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The viable tree and the head, as conditions -/

/-- **A block of the viable tree, as a condition.** `B` is in `viable_tree Φ tree` exactly when `B`
is in `tree`, the fork-choice root `Φ.fc_root` is `B` or an ancestor of `B`, and some block `W` of
`tree` that is a viable head of `Φ` is `B` or a descendant of `B`.

The variables:
- `Φ`: the frame; `tree`: the set of blocks; `B`: the block.

Read aloud: the viable tree keeps the blocks of the tree that descend from the fork-choice root,
or are it, and lead to a viable head of the tree. -/
theorem mem_viable_tree_iff (Φ : Frame V) (tree : Finset (Block V)) (B : Block V) :
    B ∈ viable_tree Φ tree ↔ B ∈ tree ∧ Φ.fc_root.ancestorEq B = true ∧
      ∃ W ∈ tree ∩ Φ.viable_heads, B.ancestorEq W = true := by
  simp only [viable_tree, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]

/-- **The head of the fork choice is the Goldfish walk from the anchor.** `get_head C A Φ t votes
support_votes s` answers what the Goldfish fork choice answers, started from the anchor
`get_anchor A Φ t` and walking the viable tree of `Φ.tree`.

The variables:
- `C`: the parameters; `A`: the AC state; `Φ`: the frame; `t`: the time; `votes`,
  `support_votes`: the votes and the support votes counted; `s`: the slot.

Read aloud: the head is where the Goldfish walk from the anchor through the viable tree of the
frame's tree ends. -/
theorem get_head_eq (C : Config) (A : ACState V) (Φ : Frame V) (t : Time)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) :
    get_head C A Φ t votes support_votes s =
      goldfish_fork_choice C Φ t (get_anchor A Φ t) (viable_tree Φ Φ.tree) votes support_votes s :=
  by rfl

/-- **The Goldfish fork choice is the Goldfish walk.** `goldfish_fork_choice C Φ t anchor tree votes
support_votes s` answers what the walk `ghost` answers from `anchor` through `tree`, scoring a block
by `goldfish_score Φ votes support_votes s` and testing it by `goldfish_eligible C Φ t votes
support_votes s`. Added by the record migration, step 1f.

The variables:
- `C`: the parameters; `Φ`: the frame; `t`: the time; `anchor`: the block the walk starts from;
  `tree`: the blocks it walks through; `votes`, `support_votes`: the votes it counts; `s`: the slot.

Read aloud: the Goldfish fork choice walks from the anchor by score among the eligible blocks. -/
theorem goldfish_fork_choice_eq (C : Config) (Φ : Frame V) (t : Time) (anchor : Block V)
    (tree : Finset (Block V)) (votes support_votes : Finset (GoldfishVote V)) (s : Slot) :
    goldfish_fork_choice C Φ t anchor tree votes support_votes s =
      ghost anchor tree (goldfish_score Φ votes support_votes s)
        (goldfish_eligible C Φ t votes support_votes s) :=
  by rfl

end

end GoldilocksCorrectness.Proofs.Routines
