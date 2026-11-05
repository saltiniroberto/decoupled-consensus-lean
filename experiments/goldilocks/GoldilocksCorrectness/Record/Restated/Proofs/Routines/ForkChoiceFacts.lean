module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FrameFGState
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFactsViableTree
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Proofs.Routines.WalkEndLemmas
public import GoldilocksCorrectness.Proofs.Routines.WalkEndMerge

@[expose] public section

/-!
# ForkChoiceFacts, over a model: the anchor, the viable tree and the end of the Goldfish walk

The fork-choice theorems of `GoldilocksCorrectness/Proofs/Routines/ForkChoiceFacts.lean` that read
the fgroot, the anchor or the Goldfish fork choice, over a model `M` whose facts `F` hold.

- The anchor `M.get_anchor n t`: the landed theorems read an AC state `A` and a frame `Φ`; the
  record's anchor reads the node state, so both are re-typed on `n` (`A`'s lock entries are
  `n.lockEntries`, `Φ` is the node's own frame `M.fg_to_ac n`).
- The Goldfish fork choice is not a member of the record: the walk is the library predicate
  `WalkEnd` (`Statements/Routines/WalkEndDefs.lean`) at the model's tie-break `M.tieBreak`, with
  the shared Goldfish score and eligibility test. `walk_end_viable_of_below` and `walk_end_extends`
  take the walk's end as `WalkEnd`; `vote_head_compatible_of_justified_past` and
  `vote_head_descends_of_F` need only the walk steps from the start to the end (the first part of
  `WalkEnd`), and take the start as any block that is the fgroot or a block of the viable tree of
  the frame's tree (the landed statements start from the anchor of any AC state, which is such a
  block: `get_anchor_cases_viable`).
- A theorem that reads the fgroot's equation, the least viable height or viability takes a node
  state satisfying the model's node invariant `M.nodeInv C P X n`.

The free twin `viable_tree_compatible` is on `ForkChoiceFactsViableTree.lean`; the page's theorems
about the Goldfish score, the eligibility test, the head and the vote duty read no member of the
record, or a member the record replaces by the walk predicate, and are not restated here.

The recovery section at the end of the page states each landed theorem again, as the landed
statement (`type_of%`), at the AC state `n.A` and the frame `fg_to_ac n.S` (or the FG state `n.S`)
of a node state `n` where the record re-types them, and proves it from its record form at the
spec's model `Model.goldilocks` and its facts `goldilocksFacts`. A recovery that reads the walk
turns the landed Goldfish fork choice into the walk predicate at the Goldilocks tie-break
(`goldfish_fork_choice_eq_ok_iff_walkEnd`, under the landed hypotheses on the roots of the tree, or
`walkSteps_of_ghost_eq_ok`, which needs none).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Statements.Routines (TieBreak WalkStep WalkEnd)
open GoldilocksCorrectness.Record.Statements.Routines (hMax FrameShape JustifiedInTree)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans deepest?_mem)

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- The model's viable tree is the spec's `viable_tree`: both keep the blocks of the tree that are
the frame's fgroot or a descendant of it and are a viable head of the frame in the tree or an
ancestor of one.

The variables:
- `M`: the model; `F`: its facts;
- `Φ`: the frame; `tree`: the tree.

Read aloud: the model's viable tree of a tree is the spec's. -/
theorem viable_tree_eq_viable_tree [RootOrder] (Φ : Frame V) (tree : Finset (Block V)) :
    M.viable_tree Φ tree = Goldilocks.viable_tree Φ tree := by
  ext B
  rw [GoldilocksCorrectness.Proofs.Routines.mem_viable_tree_iff, F.rd.viable_tree_eq]
  simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]

/-- **`mem_viable_tree_of_frameShape` under the clock-free part of the node invariant.** Its hypothesis `hI` is
`M.nodeInvCore C P X n`, the clauses of the node invariant that compare no stamp with the clock, which
hold for every validator, one in the adversary set included; `mem_viable_tree_of_frameShape` is this theorem at
`F.nd.nodeInv_core hI`.

 Under a frame shape with root `ρ` and least viable height `φ`, a block of the tree that `ρ` is
an ancestor of, whose chain-state height is at least `φ`, is in the viable tree of the frame, when
the finalized block is `ρ` or an ancestor of it: it is its own viable head (Lemma 56).

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the clock-free part of the model's node invariant,
  `M.nodeInvCore C P X n`; `ρ`: the root; `φ`: the least viable height;
  `B`: the block.

Read aloud: under `FrameShape M n ρ φ`, a block of `n`'s tree that `ρ` is an ancestor of or equal
to, with chain-state height at least `φ`, is in the viable tree of `M.fg_to_ac n`, when
`n.finalized` is `ρ` or an ancestor of `ρ`. -/
theorem mem_viable_tree_of_frameShape_of_core (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInvCore C P X n) (ρ : Block V) (φ : Height) (B : Block V)
    (hShape : FrameShape M n ρ φ)
    -- the finalized block is `ρ` or an ancestor of `ρ`
    (hFρ : n.finalized.AncestorEq ρ)
    -- `ρ` is `B` or an ancestor of `B`
    (hRootV : ρ.AncestorEq B)
    -- `B` is in the tree
    (hBin : B ∈ n.tree)
    -- `B`'s chain-state height is at least the least viable height
    (hφ : φ ≤ (M.chainStateOf C B).h) :
    B ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree := by
  obtain ⟨hR, -, hH⟩ := lem56_frame_of_shape_of_core M F C P X n hI ρ φ hShape
  have hFB : n.finalized.AncestorEq B := ancestorEq_trans hFρ hRootV
  have hVH : B ∈ (M.fg_to_ac n).viable_heads := (hH B).2 ⟨hBin, hFB, hRootV, hφ⟩
  have hT : B ∈ (M.fg_to_ac n).tree := (mem_fg_to_ac_tree M F n B).2 ⟨hBin, hFB⟩
  simp only [F.rd.viable_tree_eq, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hT, ?_, B, Finset.mem_inter.2 ⟨hT, hVH⟩,
    GoldilocksCorrectness.Proofs.Routines.ancestorEq_refl B⟩
  rw [hR]
  exact hRootV

/-- Under a frame shape with root `ρ` and least viable height `φ`, a block of the tree that `ρ` is
an ancestor of, whose chain-state height is at least `φ`, is in the viable tree of the frame, when
the finalized block is `ρ` or an ancestor of it: it is its own viable head (Lemma 56).

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `ρ`: the root; `φ`: the least viable height;
  `B`: the block.

Read aloud: under `FrameShape M n ρ φ`, a block of `n`'s tree that `ρ` is an ancestor of or equal
to, with chain-state height at least `φ`, is in the viable tree of `M.fg_to_ac n`, when
`n.finalized` is `ρ` or an ancestor of `ρ`. -/
theorem mem_viable_tree_of_frameShape (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (ρ : Block V) (φ : Height) (B : Block V)
    (hShape : FrameShape M n ρ φ)
    -- the finalized block is `ρ` or an ancestor of `ρ`
    (hFρ : n.finalized.AncestorEq ρ)
    -- `ρ` is `B` or an ancestor of `B`
    (hRootV : ρ.AncestorEq B)
    -- `B` is in the tree
    (hBin : B ∈ n.tree)
    -- `B`'s chain-state height is at least the least viable height
    (hφ : φ ≤ (M.chainStateOf C B).h) :
    B ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree :=
  mem_viable_tree_of_frameShape_of_core M F C P X n (F.nd.nodeInv_core hI) ρ φ B hShape hFρ hRootV hBin hφ

/-- The anchor of a node state is a block of its tree, when its finalized and justified blocks
are: it is a locked block of the viable tree of the frame's tree, or the fgroot, which is the
justified or the finalized block.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `t`: the time.

Read aloud: the anchor is a block of `n`'s tree when the finalized block and the justified block
are. -/
theorem get_anchor_mem_T [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (t : Time)
    -- the finalized block is in the tree
    (hFT : n.finalized ∈ n.tree)
    -- the justified block is in the tree
    (hJT : JustifiedInTree M n) :
    M.get_anchor n t ∈ n.tree := by
  rw [F.rd.get_anchor_eq]
  generalize hD : Block.deepest? {B ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree |
    M.is_locked n t B = true} = D
  cases D with
  | none =>
      show (M.fg_to_ac n).fc_root ∈ n.tree
      rw [fc_root_eq M F n, F.ndAdded.get_fc_root_eq hI]
      split
      · exact hJT
      · exact hFT
  | some B =>
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
        Option.get_some]
      have hmem := deepest?_mem hD
      simp only [Finset.mem_filter, F.rd.viable_tree_eq] at hmem
      exact ((mem_fg_to_ac_tree M F n B).1 hmem.1.1).1

/-- The end of a walk, in the viable tree or the anchor, is a block of the tree, when the
finalized and the justified blocks are.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `t`: the time; `H`: the end of the walk.

Read aloud: a block of the viable tree of `M.fg_to_ac n`, or the anchor, is a block of `n`'s tree
when the finalized block and the justified block are. -/
theorem walk_end_mem_T [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (t : Time) (H : Block V)
    (hEnd : H ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree ∨ H = M.get_anchor n t)
    (hFT : n.finalized ∈ n.tree) (hJT : JustifiedInTree M n) :
    H ∈ n.tree := by
  rcases hEnd with h | rfl
  · simp only [F.rd.viable_tree_eq, Finset.mem_filter] at h
    exact ((mem_fg_to_ac_tree M F n H).1 h.1).1
  · exact get_anchor_mem_T M F C P X n hI t hFT hJT

/-- The anchor of a node state is the fgroot, or a block of the viable tree that is locked: an
ancestor of, or equal to, the block of a lock entry live at the time.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `t`: the time.

Read aloud: the anchor is the fgroot of `n`, or a block of the viable tree that is an ancestor of,
or equal to, the block of a lock entry of `n` live at `t`. -/
theorem get_anchor_cases_locked [RootOrder] (n : M.N) (t : Time) :
    M.get_anchor n t = (M.fg_to_ac n).fc_root ∨
      (M.get_anchor n t ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree ∧
        ∃ e ∈ n.lockEntries, M.is_live n t e = true ∧ (M.get_anchor n t).AncestorEq e.B) := by
  rw [F.rd.get_anchor_eq]
  generalize hD : Block.deepest? {B ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree |
    M.is_locked n t B = true} = D
  cases D with
  | none => exact Or.inl rfl
  | some B =>
    right
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some]
    have hmem := Finset.mem_filter.mp (deepest?_mem hD)
    refine ⟨hmem.1, ?_⟩
    have h2 := hmem.2
    rw [F.rd.is_locked_eq, decide_eq_true_eq] at h2
    obtain ⟨e, he, hl, hBe⟩ := h2
    exact ⟨e, he, hl, hBe⟩

/-- The anchor of a node state is the fgroot or a block of the viable tree of the frame's tree.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `t`: the time.

Read aloud: the anchor is the fgroot of `n` or a block of the viable tree of the frame's tree. -/
theorem get_anchor_cases [RootOrder] (n : M.N) (t : Time) :
    M.get_anchor n t = (M.fg_to_ac n).fc_root ∨
      M.get_anchor n t ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree := by
  rcases get_anchor_cases_locked M F n t with h | h
  · exact Or.inl h
  · exact Or.inr h.1

/-- The anchor is the fgroot, or a block of the viable tree.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `t`: the time.

Read aloud: the anchor is the fgroot of `n` or a block of the viable tree of the frame's tree. -/
theorem get_anchor_root_or_viable [RootOrder] (n : M.N) (t : Time) :
    M.get_anchor n t = (M.fg_to_ac n).fc_root ∨
      M.get_anchor n t ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree :=
  get_anchor_cases M F n t

/-- The anchor is the fgroot, or an ancestor of the block of a live lock entry.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `t`: the time.

Read aloud: the anchor is the fgroot of `n`, or an ancestor of, or equal to, the block of a lock
entry of `n` live at `t`. -/
theorem get_anchor_cases_live_lock [RootOrder] (n : M.N) (t : Time) :
    M.get_anchor n t = (M.fg_to_ac n).fc_root ∨
      ∃ e ∈ n.lockEntries, M.is_live n t e = true ∧ (M.get_anchor n t).AncestorEq e.B := by
  rcases get_anchor_cases_locked M F n t with h | h
  · exact Or.inl h
  · exact Or.inr h.2

/-- The anchor is the fgroot, or a block of the viable tree of the frame's tree.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `t`: the time.

Read aloud: every walk starts from the fgroot or from a block of the viable tree. -/
theorem get_anchor_cases_viable [RootOrder] (n : M.N) (t : Time) :
    M.get_anchor n t = (M.fg_to_ac n).fc_root ∨
      M.get_anchor n t ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree :=
  get_anchor_cases M F n t

/-- The anchor is compatible with `B` when the fgroot and every block of the viable tree of the
frame's tree are.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `t`: the time; `B`: the block.

Read aloud: when the fgroot and the viable tree do not conflict with `B`, neither does the
anchor. -/
theorem anchor_compatible [RootOrder] (n : M.N) (t : Time) (B : Block V)
    (hroot : (M.fg_to_ac n).fc_root.compatible B = true)
    (htree : ∀ D ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree, D.compatible B = true) :
    (M.get_anchor n t).compatible B = true := by
  rcases get_anchor_cases M F n t with h | h
  · rw [h]
    exact hroot
  · exact htree _ h

/-- **A block of the viable tree, as a condition.** `B` is in `M.viable_tree Φ tree` exactly when
`B` is in `tree`, the fgroot `Φ.fc_root` is `B` or an ancestor of `B`, and some block `W` of `tree`
that is a viable head of `Φ` is `B` or a descendant of `B`.

The variables:
- `M`: the model; `F`: its facts;
- `Φ`: the frame; `tree`: the set of blocks; `B`: the block.

Read aloud: the viable tree keeps the blocks of the tree that descend from the fgroot, or are it,
and lead to a viable head of the tree. -/
theorem mem_viable_tree_iff (Φ : Frame V) (tree : Finset (Block V)) (B : Block V) :
    B ∈ M.viable_tree Φ tree ↔ B ∈ tree ∧ Φ.fc_root.ancestorEq B = true ∧
      ∃ W ∈ tree ∩ Φ.viable_heads, B.ancestorEq W = true := by
  simp only [F.rd.viable_tree_eq, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]

/-- The end `H` of the walk through the viable tree of `VT`, with the Goldfish score and the
Goldfish eligibility test, at the model's tie-break, is a viable head, when `H` is on the chain of
the frame's fgroot, `H` is a strict ancestor of a viable head `Z ∈ VT`, and `VT` holds every block
from the root to a block of `VT`.

Why: the walk-predicate form `walkEnd_viable_of_below`, at the model's tie-break, over the model's
viable tree, which is the spec's (`viable_tree_eq_viable_tree`).

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `Φ`: the frame; `t`: the time; `A`: the start; `VT`: the tree;
- `votes`, `sv`: the counted votes; `s`: their slot; `H`: the walk's end; `Z`: the viable head.

Read aloud: when the Goldfish walk through a viable tree ends at a strict ancestor of a viable
head of the tree, the end is itself a viable head. -/
theorem walk_end_viable_of_below [RootOrder] (C : Config) (Φ : Frame V) (t : Time) (A : Block V)
    (VT : Finset (Block V)) (votes sv : Finset (GoldfishVote V)) (s : Slot) (H Z : Block V)
    (hClosed : ∀ Z' ∈ VT, ∀ c : Block V, Φ.fc_root.AncestorEq c → c.AncestorEq Z' → c ∈ VT)
    (hWalk : @WalkEnd V M.tieBreak (M.viable_tree Φ VT) (goldfish_score Φ votes sv s)
      (goldfish_eligible C Φ t votes sv s) A H)
    (hρH : Φ.fc_root.AncestorEq H) (hZ : Z ∈ VT) (hZv : Z ∈ Φ.viable_heads)
    (hHZ : H.AncestorEq Z) (hne : H ≠ Z) :
    H ∈ Φ.viable_heads := by
  letI : TieBreak V := M.tieBreak
  simp only [viable_tree_eq_viable_tree M F] at hWalk
  exact GoldilocksCorrectness.Proofs.Routines.walkEnd_viable_of_below C Φ t A VT votes sv s H Z
    hClosed hWalk hρH hZ hZv hHZ hne

/-- **The end of the Goldfish walk extends a block every viable head extends.** When the walk from
the anchor `A` (the fgroot, or a block of the viable tree of the frame's tree) through the viable
tree of `VT`, with the Goldfish score and the Goldfish eligibility test, at the model's tie-break,
ends at `H`; `VT` holds a viable head `Y` and every block from the root to a block of `VT`; every
viable head is `F'` or a descendant of `F'`; and no strict ancestor of `F'` is a viable head, then
`H` is `F'` or a descendant of `F'`.

Why: the walk-predicate form `walkEnd_extends`, at the model's tie-break, over the model's viable
tree, which is the spec's (`viable_tree_eq_viable_tree`).

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `Φ`: the frame; `t`: the time; `A`: the anchor; `VT`: the tree;
- `votes`, `sv`: the counted votes; `s`: their slot; `H`: the walk's end; `F'`: the block;
  `Y`: a viable head of `VT`.

Read aloud: the Goldfish walk through a viable tree ends at `F'` or a descendant of it, when every
viable head descends from `F'` and no strict ancestor of `F'` is a viable head. -/
theorem walk_end_extends [RootOrder] (C : Config) (Φ : Frame V) (t : Time) (A : Block V)
    (VT : Finset (Block V)) (votes sv : Finset (GoldfishVote V)) (s : Slot) (H F' Y : Block V)
    (hClosed : ∀ Z' ∈ VT, ∀ c : Block V, Φ.fc_root.AncestorEq c → c.AncestorEq Z' → c ∈ VT)
    (hA : A = Φ.fc_root ∨ A ∈ M.viable_tree Φ Φ.tree)
    (hWalk : @WalkEnd V M.tieBreak (M.viable_tree Φ VT) (goldfish_score Φ votes sv s)
      (goldfish_eligible C Φ t votes sv s) A H)
    (hρV : ∀ W ∈ Φ.viable_heads, Φ.fc_root.AncestorEq W)
    (hYVT : Y ∈ VT) (hY : Y ∈ Φ.viable_heads)
    (hP : ∀ W ∈ Φ.viable_heads, F'.AncestorEq W)
    (hQ : ∀ B : Block V, B.AncestorEq F' → B ≠ F' → B ∉ Φ.viable_heads) :
    F'.AncestorEq H := by
  letI : TieBreak V := M.tieBreak
  simp only [viable_tree_eq_viable_tree M F] at hWalk hA
  exact GoldilocksCorrectness.Proofs.Routines.walkEnd_extends C Φ t A VT votes sv s H F' Y hClosed
    hA hWalk hρV hYVT hY hP hQ

/-- The end of the Goldfish walk from a start that is the fgroot or a block of the viable tree of
the frame's tree, through the viable tree of any tree `vbt`, at the model's tie-break, is
compatible with `B`, at a node state justified past `B`.

Why: the walk ends at its start or at a block of the viable tree it walks (`walkSteps_spec`);
every viable head descends from `B` (`viable_head_descends_of_justified_past`), so every block of
a viable tree is compatible with `B` (`viable_tree_compatible`); the fgroot is compatible with `B`
(`fc_root_compatible`).

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `B`: the block; `A₀`: the start of the walk;
  `t`: the time; `vbt`: the voter tree; `votes`, `sv`: the votes and the support votes; `s`: the
  slot; `H`: the end of the walk.

Read aloud: at a node whose justified block is compatible with `B`, whose blocks two heights past
`B` descend from `B`, with `n.justifiedHeight < hMax M C n` and `n.justifiedHeight ≥ h(B) + 1`,
the head of any Goldfish vote it computes is compatible with `B`. -/
theorem vote_head_compatible_of_justified_past [RootOrder] (C : Config) (P : Provisional V)
    (X : External V) (n : M.N) (hI : M.nodeInv C P X n) (B : Block V)
    (hJ : n.justified.AncestorEq B ∨ B.AncestorEq n.justified)
    (hJh : (M.chainStateOf C n.justified).h = n.justifiedHeight)
    (hFJ : n.finalized.AncestorEq n.justified)
    (hTwo : ∀ D ∈ n.tree, (M.chainStateOf C B).h + 2 ≤ (M.chainStateOf C D).h → B.AncestorEq D)
    (hjmax : n.justifiedHeight < hMax M C n)
    (hSafe : (M.chainStateOf C B).h + 1 ≤ n.justifiedHeight)
    -- the start of the walk is the fgroot or a block of the viable tree of the frame's tree
    (A₀ : Block V)
    (hA₀ : A₀ = (M.fg_to_ac n).fc_root ∨ A₀ ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree)
    (t : Time) (vbt : Finset (Block V)) (votes sv : Finset (GoldfishVote V)) (s : Slot)
    (H : Block V)
    -- walk steps at the model's tie-break lead from `A₀` to `H`
    (h : Relation.ReflTransGen (@WalkStep V M.tieBreak (M.viable_tree (M.fg_to_ac n) vbt)
      (goldfish_score (M.fg_to_ac n) votes sv s) (goldfish_eligible C (M.fg_to_ac n) t votes sv s))
      A₀ H) :
    H.compatible B = true := by
  have hheads := viable_head_descends_of_justified_past M F C P X n hI B hJ hJh hTwo hjmax hSafe
  have hroot : (M.fg_to_ac n).fc_root.compatible B = true := by
    rw [fc_root_eq M F n]
    exact fc_root_compatible M F C P X n hI B hJ hFJ
  have hA : A₀.compatible B = true := by
    rcases hA₀ with rfl | hA
    · exact hroot
    · exact viable_tree_compatible M F _ _ B hheads _ hA
  letI : TieBreak V := M.tieBreak
  rcases GoldilocksCorrectness.Proofs.Routines.walkSteps_spec h with rfl | ⟨-, -, hH⟩
  · exact hA
  · exact viable_tree_compatible M F _ vbt B hheads H hH

/-- **The head of a Goldfish vote descends from the voter's finalized block.** The walk from a
start that is the fgroot or a block of the viable tree of the frame's tree, through the viable tree
of any tree `vbt`, at the model's tie-break, ends at `n.finalized` or a descendant of it, when
`n.finalized` is an ancestor of `n.justified` or `n.justified`.

Why: the walk ends at its start or at a block of the viable tree it walks (`walkSteps_spec`);
every block of a viable tree is the fgroot or a descendant of it, and the fgroot is `n.justified`
or `n.finalized`, of which `n.finalized` is an ancestor or which it is.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `A₀`: the start of the walk; `t`: the time;
  `vbt`: the voter tree; `votes`, `sv`: the votes and the support votes; `s`: the slot; `H`: the
  head.

Read aloud: the head of a Goldfish vote is the voter's finalized block or a descendant of it. -/
theorem vote_head_descends_of_F [RootOrder] (C : Config) (P : Provisional V) (X : External V)
    (n : M.N) (hI : M.nodeInv C P X n) (hFJ : n.finalized.AncestorEq n.justified)
    -- the start of the walk is the fgroot or a block of the viable tree of the frame's tree
    (A₀ : Block V)
    (hA₀ : A₀ = (M.fg_to_ac n).fc_root ∨ A₀ ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree)
    (t : Time) (vbt : Finset (Block V)) (votes sv : Finset (GoldfishVote V)) (s : Slot)
    (H : Block V)
    -- walk steps at the model's tie-break lead from `A₀` to `H`
    (h : Relation.ReflTransGen (@WalkStep V M.tieBreak (M.viable_tree (M.fg_to_ac n) vbt)
      (goldfish_score (M.fg_to_ac n) votes sv s) (goldfish_eligible C (M.fg_to_ac n) t votes sv s))
      A₀ H) :
    n.finalized.AncestorEq H := by
  have hFr : n.finalized.AncestorEq (M.fg_to_ac n).fc_root := by
    rw [fc_root_eq M F n]
    exact F_ancestorEq_get_fc_root M F C P X n hI hFJ
  have hvt : ∀ (tree : Finset (Block V)), ∀ D ∈ M.viable_tree (M.fg_to_ac n) tree,
      n.finalized.AncestorEq D := by
    intro tree D hD
    simp only [F.rd.viable_tree_eq, Finset.mem_filter, Bool.and_eq_true] at hD
    exact ancestorEq_trans hFr hD.2.1
  have hA : n.finalized.AncestorEq A₀ := by
    rcases hA₀ with rfl | h'
    · exact hFr
    · exact hvt _ _ h'
  letI : TieBreak V := M.tieBreak
  rcases GoldilocksCorrectness.Proofs.Routines.walkSteps_spec h with rfl | ⟨-, -, h'⟩
  · exact hA
  · exact hvt _ _ h'

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.mem_viable_tree_of_frameShape`, recovered
from its record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying
the spec's model's node invariant.

Read aloud: the landed `mem_viable_tree_of_frameShape` holds at the FG state of every node state
satisfying the invariant. -/
theorem mem_viable_tree_of_frameShape_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.mem_viable_tree_of_frameShape V _
        n.S) := by
  intro C P X n hI ρ φ B hShape hFρ hRootV hBin hφ
  refine mem_viable_tree_of_frameShape Model.goldilocks goldilocksFacts C P X n hI ρ φ B hShape
    hFρ hRootV hBin ?_
  show φ ≤ (GoldilocksCorrectness.Statements.Routines.chainStateOf C B).h
  rw [← hI.1.2.2.2.2.2.1 B hBin]
  exact hφ

/-- The landed `GoldilocksCorrectness.Proofs.Routines.get_anchor_mem_T`, recovered from its record
form at the spec's model, at the AC state `n.A` and the FG state `n.S` of every node state `n`
satisfying the spec's model's node invariant.

Read aloud: the landed `get_anchor_mem_T` holds at the AC state and the FG state of every node
state satisfying the invariant. -/
theorem get_anchor_mem_T_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.get_anchor_mem_T V _ _ n.A n.S) := by
  intro C P X n hI t hFT hJT
  exact get_anchor_mem_T Model.goldilocks goldilocksFacts C P X n hI t hFT hJT

/-- The landed `GoldilocksCorrectness.Proofs.Routines.walk_end_mem_T`, recovered from its record
form at the spec's model, at the AC state `n.A` and the FG state `n.S` of every node state `n`
satisfying the spec's model's node invariant.

Read aloud: the landed `walk_end_mem_T` holds at the AC state and the FG state of every node state
satisfying the invariant. -/
theorem walk_end_mem_T_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.walk_end_mem_T V _ _ n.A n.S) := by
  intro C P X n hI t H hEnd hFT hJT
  exact walk_end_mem_T Model.goldilocks goldilocksFacts C P X n hI t H hEnd hFT hJT

/-- The landed `GoldilocksCorrectness.Proofs.Routines.get_anchor_cases_locked`, recovered from its
record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every node
state `n`.

Read aloud: the landed `get_anchor_cases_locked` holds at the AC state and the frame of every node
state. -/
theorem get_anchor_cases_locked_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (n : NodeState V),
      type_of% (@GoldilocksCorrectness.Proofs.Routines.get_anchor_cases_locked V _ _ n.A
        (fg_to_ac n.S)) := by
  intro n t
  exact get_anchor_cases_locked Model.goldilocks goldilocksFacts n t

/-- The landed `GoldilocksCorrectness.Proofs.Routines.walk_end_viable_of_below`, recovered from its
record form at the spec's model.

Why: the viable tree of `VT` is a subset of `VT`, so of `Φ.tree`, and no two of its blocks share a
root; then `goldfish_fork_choice_eq_ok_iff_walkEnd` turns the landed fork choice into the walk
predicate at the Goldilocks tie-break, the spec's model's.

Read aloud: the landed `walk_end_viable_of_below` holds, as the record's theorem at the spec's
model. -/
theorem walk_end_viable_of_below_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.walk_end_viable_of_below V _ _ _) := by
  intro C Φ t A VT votes sv s H Z hRoots hVT hClosed hWalk hρH hZ hZv hHZ hne
  have hsub : viable_tree Φ VT ⊆ Φ.tree := fun B hB =>
    hVT ((GoldilocksCorrectness.Proofs.Routines.mem_viable_tree_iff Φ VT B).1 hB).1
  exact walk_end_viable_of_below Model.goldilocks goldilocksFacts C Φ t A VT votes sv s H Z hClosed
    ((GoldilocksCorrectness.Proofs.Routines.goldfish_fork_choice_eq_ok_iff_walkEnd C Φ t A
      (viable_tree Φ VT) votes sv s
      (GoldilocksCorrectness.Proofs.Routines.rootsNameBlocksIn_mono hsub hRoots)).1 hWalk)
    hρH hZ hZv hHZ hne

/-- The landed `GoldilocksCorrectness.Proofs.Routines.walk_end_extends`, recovered from its record
form at the spec's model.

Why: as for `walk_end_viable_of_below_recovered`: no two blocks of the viable tree of `VT` share a
root, and `goldfish_fork_choice_eq_ok_iff_walkEnd`.

Read aloud: the landed `walk_end_extends` holds, as the record's theorem at the spec's model. -/
theorem walk_end_extends_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.walk_end_extends V _ _ _) := by
  intro C Φ t A VT votes sv s H F' Y hRoots hVT hClosed hA hWalk hρV hYVT hY hP hQ
  have hsub : viable_tree Φ VT ⊆ Φ.tree := fun B hB =>
    hVT ((GoldilocksCorrectness.Proofs.Routines.mem_viable_tree_iff Φ VT B).1 hB).1
  exact walk_end_extends Model.goldilocks goldilocksFacts C Φ t A VT votes sv s H F' Y hClosed hA
    ((GoldilocksCorrectness.Proofs.Routines.goldfish_fork_choice_eq_ok_iff_walkEnd C Φ t A
      (viable_tree Φ VT) votes sv s
      (GoldilocksCorrectness.Proofs.Routines.rootsNameBlocksIn_mono hsub hRoots)).1 hWalk)
    hρV hYVT hY hP hQ

/-- The landed `GoldilocksCorrectness.Proofs.Routines.get_anchor_cases`, recovered from its record
form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every node state
`n`.

Read aloud: the landed `get_anchor_cases` holds at the AC state and the frame of every node
state. -/
theorem get_anchor_cases_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (n : NodeState V),
      type_of% (@GoldilocksCorrectness.Proofs.Routines.get_anchor_cases V _ _ n.A
        (fg_to_ac n.S)) := by
  intro n t
  exact get_anchor_cases Model.goldilocks goldilocksFacts n t

/-- The landed `GoldilocksCorrectness.Proofs.Routines.get_anchor_root_or_viable`, recovered from
its record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every
node state `n`.

Read aloud: the landed `get_anchor_root_or_viable` holds at the AC state and the frame of every
node state. -/
theorem get_anchor_root_or_viable_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (n : NodeState V),
      type_of% (@GoldilocksCorrectness.Proofs.Routines.get_anchor_root_or_viable V _ _ n.A
        (fg_to_ac n.S)) := by
  intro n t
  exact get_anchor_root_or_viable Model.goldilocks goldilocksFacts n t

/-- The landed `GoldilocksCorrectness.Proofs.Routines.get_anchor_cases_live_lock`, recovered from
its record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every
node state `n`.

Read aloud: the landed `get_anchor_cases_live_lock` holds at the AC state and the frame of every
node state. -/
theorem get_anchor_cases_live_lock_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (n : NodeState V),
      type_of% (@GoldilocksCorrectness.Proofs.Routines.get_anchor_cases_live_lock V _ _ n.A
        (fg_to_ac n.S)) := by
  intro n t
  exact get_anchor_cases_live_lock Model.goldilocks goldilocksFacts n t

/-- The landed `GoldilocksCorrectness.Proofs.Routines.get_anchor_cases_viable`, recovered from its
record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every node
state `n`.

Read aloud: the landed `get_anchor_cases_viable` holds at the AC state and the frame of every node
state. -/
theorem get_anchor_cases_viable_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (n : NodeState V),
      type_of% (@GoldilocksCorrectness.Proofs.Routines.get_anchor_cases_viable V _ _ _ n.A
        (fg_to_ac n.S)) := by
  intro n t
  exact get_anchor_cases_viable Model.goldilocks goldilocksFacts n t

/-- The landed `GoldilocksCorrectness.Proofs.Routines.anchor_compatible`, recovered from its record
form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every node state
`n`.

Read aloud: the landed `anchor_compatible` holds at the AC state and the frame of every node
state. -/
theorem anchor_compatible_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (n : NodeState V),
      type_of% (@GoldilocksCorrectness.Proofs.Routines.anchor_compatible V _ _ _ n.A
        (fg_to_ac n.S)) := by
  intro n t B hroot htree
  exact anchor_compatible Model.goldilocks goldilocksFacts n t B hroot htree

/-- The landed `GoldilocksCorrectness.Proofs.Routines.vote_head_compatible_of_justified_past`,
recovered from its record form at the spec's model, at the FG state `n.S` of every node state `n`
satisfying the spec's model's node invariant: the landed walk starts from the anchor of any AC
state `A'`, the fgroot or a block of the viable tree (`get_anchor_cases_viable`), and its answer is
reached by walk steps at the Goldilocks tie-break (`walkSteps_of_ghost_eq_ok`).

Read aloud: the landed `vote_head_compatible_of_justified_past` holds at the FG state of every node
state satisfying the invariant. -/
theorem vote_head_compatible_of_justified_past_recovered {V : Type} [DecidableEq V] [Fintype V]
    [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.vote_head_compatible_of_justified_past V _
        _ _ C n.S) := by
  intro C P X n hI B _ hJ hJh hFJ hTwo hjmax hSafe A' t vbt votes sv s H h
  rw [GoldilocksCorrectness.Proofs.Routines.goldfish_fork_choice_eq] at h
  exact vote_head_compatible_of_justified_past Model.goldilocks goldilocksFacts C P X n hI B hJ hJh
    hFJ hTwo (by rw [hMax_goldilocks hI]; exact hjmax) hSafe (get_anchor A' (fg_to_ac n.S) t)
    (GoldilocksCorrectness.Proofs.Routines.get_anchor_cases_viable A' (fg_to_ac n.S) t) t vbt
    votes sv s H (GoldilocksCorrectness.Proofs.Routines.walkSteps_of_ghost_eq_ok h)

/-- The landed `GoldilocksCorrectness.Proofs.Routines.vote_head_descends_of_F`, recovered from its
record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the
spec's model's node invariant, as `vote_head_compatible_of_justified_past_recovered`.

Read aloud: the landed `vote_head_descends_of_F` holds at the FG state of every node state
satisfying the invariant. -/
theorem vote_head_descends_of_F_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.vote_head_descends_of_F V _ _ _ C
        n.S) := by
  intro C P X n hI A' t vbt votes sv s H hFJ h
  rw [GoldilocksCorrectness.Proofs.Routines.goldfish_fork_choice_eq] at h
  exact vote_head_descends_of_F Model.goldilocks goldilocksFacts C P X n hI hFJ
    (get_anchor A' (fg_to_ac n.S) t)
    (GoldilocksCorrectness.Proofs.Routines.get_anchor_cases_viable A' (fg_to_ac n.S) t) t vbt
    votes sv s H (GoldilocksCorrectness.Proofs.Routines.walkSteps_of_ghost_eq_ok h)

/-- The landed `GoldilocksCorrectness.Proofs.Routines.mem_viable_tree_iff`, recovered from its record
form at the spec's model.

Read aloud: the landed `mem_viable_tree_iff` holds, as the record's theorem at the spec's model. -/
theorem mem_viable_tree_iff_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.mem_viable_tree_iff V _ _ _) := by
  exact mem_viable_tree_iff Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Proofs.Routines
