module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Proofs.Routines.WalkEndLemmas
public import GoldilocksCorrectness.Proofs.Routines.WalkEndMerge
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.State

@[expose] public section

/-!
# ACInterface, over a model: the source, the head and the anchor of the attestation duty

The theorems of `GoldilocksCorrectness/Proofs/Routines/ACInterface.lean` about the answer of
`ac_to_fg` that execution proofs call (`ac_to_fg_source_fast`, `ac_to_fg_source_mem`,
`ac_to_fg_head_mem`), over a model `M` whose facts `F` hold. The record has no member for
`ac_to_fg`: what the attestation duty reads is in the tick's fact T8
(`TickFacts3.tick_attestation`), whose source is the deepest fast block of the tick's answer `n'`
in the viable tree of the frame of the node state `n` it started from, and whose head is reached by
walk steps from the anchor over that frame with the lock entries of `n'` (`AnchorAt`). So the
twins take those forms as hypotheses: the source as that equation of `Block.deepest?`, the head as
walk steps through the viable tree from `AnchorAt` (the first part of `WalkEnd`), with any score and
any test.

With them, the anchor's cases: `mem_lockedViableBlocks`, `anchorAt_cases_locked`, `anchorAt_cases`
(the twins of `get_anchor_cases_locked` and `get_anchor_cases` for `AnchorAt`), and, at the spec's
model, `goldilocks_get_anchor_eq_anchorAt_frame`: the spec's anchor of any AC state over any frame
is `AnchorAt` over that frame with the AC state's lock entries.

The page's other theorems (the admission of a block, the tick of the available chain, its sends)
are facts of the receipt's and the tick's families, already fields (`ReceiveFacts`, `TickFacts1`).

The recovery section at the end of the page states each landed theorem again, as the landed
statement (`type_of%`), at the AC state `n'.A` (or any AC state `A`) and the frame `fg_to_ac n.S` of
node states, and proves it from its record form at the spec's model, reading the answer of
`ac_to_fg` through its body (`ac_to_fg_eq_ok_facts`) and its walk through
`walkSteps_of_ghost_eq_ok`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Statements.Routines (TieBreak WalkStep WalkEnd)
open GoldilocksCorrectness.Record.Statements.Routines (AnchorAt LockedViableBlocks)
open GoldilocksCorrectness.Proofs.Routines (deepest?_mem ancestorEq_refl)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The anchor's cases -/

/-- A block of `LockedViableBlocks M Φ E t`, as a condition: a block of the viable tree of `Φ.tree`
that is the block of an entry of `E` live at `t`, or an ancestor of it.

The variables:
- `M`: the model; `Φ`: the frame; `E`: the lock entries; `t`: the time; `B`: the block.

Read aloud: `B` is a locked block of the viable tree exactly when it is in the viable tree and a
live entry of `E` locks it. -/
theorem mem_lockedViableBlocks (M : GoldilocksModel V) (Φ : Frame V) (E : Finset M.LE) (t : Time)
    (B : Block V) :
    B ∈ LockedViableBlocks M Φ E t ↔ B ∈ M.viable_tree Φ Φ.tree ∧
      ∃ e ∈ E, t < e.d ∧ e.B ∈ Φ.tree ∧ B.ancestorEq e.B = true := by
  simp only [LockedViableBlocks, Finset.mem_filter]

/-- The anchor over `Φ` with the lock entries `E` is the fgroot of `Φ`, or a block of the viable
tree of `Φ.tree` that is the block of an entry of `E` live at `t`, or an ancestor of it.

The variables:
- `M`: the model; `Φ`: the frame; `E`: the lock entries; `t`: the time.

Read aloud: the anchor is the fgroot, or a locked block of the viable tree. -/
theorem anchorAt_cases_locked [RootOrder] (M : GoldilocksModel V) (Φ : Frame V) (E : Finset M.LE)
    (t : Time) :
    AnchorAt M Φ E t = Φ.fc_root ∨
      (AnchorAt M Φ E t ∈ M.viable_tree Φ Φ.tree ∧
        ∃ e ∈ E, t < e.d ∧ e.B ∈ Φ.tree ∧ (AnchorAt M Φ E t).ancestorEq e.B = true) := by
  unfold AnchorAt
  generalize hD : Block.deepest? (LockedViableBlocks M Φ E t) = D
  cases D with
  | none => exact Or.inl rfl
  | some B =>
    right
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some]
    exact (mem_lockedViableBlocks M Φ E t B).1 (deepest?_mem hD)

/-- The anchor over `Φ` with the lock entries `E` is the fgroot of `Φ` or a block of the viable
tree of `Φ.tree`.

The variables:
- `M`: the model; `Φ`: the frame; `E`: the lock entries; `t`: the time.

Read aloud: every walk of a duty starts from the fgroot or from a block of the viable tree. -/
theorem anchorAt_cases [RootOrder] (M : GoldilocksModel V) (Φ : Frame V) (E : Finset M.LE)
    (t : Time) :
    AnchorAt M Φ E t = Φ.fc_root ∨ AnchorAt M Φ E t ∈ M.viable_tree Φ Φ.tree := by
  rcases anchorAt_cases_locked M Φ E t with h | h
  · exact Or.inl h
  · exact Or.inr h.1

/-! ## The source of the attestation duty -/

/-- The source of the attestation duty, the deepest fast block of `n'` in the viable tree of the
tree of `n`'s frame, is a fast block of `n'` (the record form of `ac_to_fg_source_fast`).

The variables:
- `M`: the model; `n`: the node state whose frame is read; `n'`: the node state whose fast blocks
  are read; `source`: the source.

Read aloud: the attestation duty's source is one of the fast blocks. -/
theorem ac_to_fg_source_fast [RootOrder] (M : GoldilocksModel V) (n n' : M.N) (source : Block V)
    -- the source is the deepest fast block of `n'` in the viable tree of `n`'s frame's tree
    (hs : Block.deepest? (n'.fastBlocks ∩ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree) =
      some source) :
    source ∈ n'.fastBlocks :=
  (Finset.mem_inter.1 (deepest?_mem hs)).1

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- The source of the attestation duty is a block of the tree of `n`'s frame (the record form of
`ac_to_fg_source_mem`).

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state whose frame is read; `n'`: the node state whose fast blocks are read;
  `source`: the source.

Read aloud: the attestation duty's source is a block of the frame's tree. -/
theorem ac_to_fg_source_mem [RootOrder] (n n' : M.N) (source : Block V)
    -- the source is the deepest fast block of `n'` in the viable tree of `n`'s frame's tree
    (hs : Block.deepest? (n'.fastBlocks ∩ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree) =
      some source) :
    source ∈ (M.fg_to_ac n).tree :=
  ((mem_viable_tree_iff M F _ _ source).1 (Finset.mem_inter.1 (deepest?_mem hs)).2).1

/-! ## The head of the attestation duty -/

/-- A block reached by walk steps through the viable tree of the tree of `n`'s frame, from the
anchor over that frame with any lock entries, is a block of `n`'s tree of which `n`'s finalized
block is an ancestor, or which is the finalized block, when `n` satisfies the model's node
invariant (the record form of `ac_to_fg_head_mem`).

Why: the walk ends at its start or in the viable tree (`walkSteps_spec`); the anchor is the fgroot
or a block of the viable tree (`anchorAt_cases`); the fgroot is the justified or the finalized block
(`get_fc_root_eq`), both blocks of the tree on the finalized block's chain under the invariant; and
the viable tree is part of the frame's tree.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `E`: the lock entries; `t`: the time;
- `score`, `eligible`: the walk's score and test; `H`: the block reached.

Read aloud: the head of the attestation duty is a block of the tree on the finalized block's
chain. -/
theorem ac_to_fg_head_mem [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (E : Finset M.LE) (t : Time) (score : Block V → DC.DRE ℕ)
    (eligible : Block V → DC.DRE Bool) (H : Block V)
    -- walk steps through the viable tree of the frame's tree lead from the anchor to `H`
    (hH : Relation.ReflTransGen
      (@WalkStep V M.tieBreak (M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree) score eligible)
      (AnchorAt M (M.fg_to_ac n) E t) H) :
    H ∈ n.tree ∧ n.finalized.AncestorEq H := by
  have hroot : (M.fg_to_ac n).fc_root ∈ n.tree ∧ n.finalized.AncestorEq (M.fg_to_ac n).fc_root := by
    rw [fc_root_eq M F n, F.ndAdded.get_fc_root_eq hI]
    split
    · exact ⟨F.nd.nodeInv_justifiedInTree hI, F.nd.nodeInv_finalizedAncestorJustified hI⟩
    · exact ⟨F.nd.nodeInv_finalized_mem_tree hI, ancestorEq_refl _⟩
  have hVT : ∀ B ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree,
      B ∈ n.tree ∧ n.finalized.AncestorEq B := fun B hB =>
    (mem_fg_to_ac_tree M F n B).1 ((mem_viable_tree_iff M F _ _ B).1 hB).1
  letI : TieBreak V := M.tieBreak
  rcases GoldilocksCorrectness.Proofs.Routines.walkSteps_spec hH with h | ⟨-, -, hin⟩
  · rw [h]
    rcases anchorAt_cases M (M.fg_to_ac n) E t with ha | ha
    · rw [ha]
      exact hroot
    · exact hVT _ ha
  · exact hVT _ hin

end

/-! ## At the spec's model -/

/-- At the spec's model, the anchor `get_anchor A Φ t` of any AC state `A` over any frame `Φ` is
`AnchorAt` over `Φ` with `A`'s lock entries.

The variables:
- `A`: the AC state; `Φ`: the frame; `t`: the time.

Read aloud: the spec's anchor is the anchor over the frame with the AC state's lock entries. -/
theorem goldilocks_get_anchor_eq_anchorAt_frame [RootOrder] (A : ACState V) (Φ : Frame V)
    (t : Time) :
    get_anchor A Φ t = AnchorAt (Model.goldilocks (V := V)) Φ A.lock_entries t := by
  simp only [get_anchor, Id.run]
  unfold AnchorAt
  refine GoldilocksCorrectness.Record.dite_deepest_congr ?_ _
  ext B
  rw [mem_lockedViableBlocks]
  show _ ↔ B ∈ viable_tree Φ Φ.tree ∧
    ∃ e ∈ A.lock_entries, t < e.d ∧ e.B ∈ Φ.tree ∧ B.ancestorEq e.B = true
  simp only [Finset.mem_filter, is_locked, is_live, decide_eq_true_eq, Bool.and_eq_true, and_assoc]

/-- The landed `GoldilocksCorrectness.Proofs.Routines.ac_to_fg_source_fast`, recovered from its
record form at the spec's model, at the AC state `n'.A` and the frame `fg_to_ac n.S` of node states
`n`, `n'`.

Read aloud: the landed `ac_to_fg_source_fast` holds at the AC state and the frame of every pair of
node states. -/
theorem ac_to_fg_source_fast_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (n n' : NodeState V) (t : Time) (fi : FGInput V) (source : Block V),
      type_of% (@GoldilocksCorrectness.Proofs.Routines.ac_to_fg_source_fast V _ _ _ C n'.A
        (fg_to_ac n.S) t fi source) := by
  intro C n n' t fi source hfi hs
  obtain ⟨hsrc, -⟩ := ac_to_fg_eq_ok_facts hfi
  exact ac_to_fg_source_fast Model.goldilocks n n' source (hsrc.symm.trans hs)

/-- The landed `GoldilocksCorrectness.Proofs.Routines.ac_to_fg_source_mem`, recovered from its
record form at the spec's model, at the AC state `n'.A` and the frame `fg_to_ac n.S` of node states
`n`, `n'`.

Read aloud: the landed `ac_to_fg_source_mem` holds at the AC state and the frame of every pair of
node states. -/
theorem ac_to_fg_source_mem_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (n n' : NodeState V) (t : Time) (fi : FGInput V) (source : Block V),
      type_of% (@GoldilocksCorrectness.Proofs.Routines.ac_to_fg_source_mem V _ _ _ C n'.A
        (fg_to_ac n.S) t fi source) := by
  intro C n n' t fi source hfi hs
  obtain ⟨hsrc, -⟩ := ac_to_fg_eq_ok_facts hfi
  exact ac_to_fg_source_mem Model.goldilocks goldilocksFacts n n' source (hsrc.symm.trans hs)

/-- The landed `GoldilocksCorrectness.Proofs.Routines.ac_to_fg_head_mem`, recovered from its record
form at the spec's model, at any AC state `A` and the FG state `n.S` of every node state `n`
satisfying the spec's model's node invariant: the head is the end of the spec's walk from the
anchor of `A`, which is `AnchorAt` over the frame with `A`'s lock entries, and the walk's answer is
reached by walk steps at the Goldilocks tie-break (`walkSteps_of_ghost_eq_ok`).

Read aloud: the landed `ac_to_fg_head_mem` holds at every AC state and at the FG state of every node
state satisfying the invariant. -/
theorem ac_to_fg_head_mem_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) (A : ACState V) (t : Time),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.ac_to_fg_head_mem V _ _ _ C A n.S t) := by
  intro C P X n A t hI _ _ _ fi hfi
  obtain ⟨-, sv, -, hfc⟩ := ac_to_fg_eq_ok_facts hfi
  rw [GoldilocksCorrectness.Proofs.Routines.goldfish_fork_choice_eq,
    goldilocks_get_anchor_eq_anchorAt_frame] at hfc
  exact ac_to_fg_head_mem Model.goldilocks goldilocksFacts C P X n hI A.lock_entries t _ _ fi.head
    (GoldilocksCorrectness.Proofs.Routines.walkSteps_of_ghost_eq_ok hfc)

end GoldilocksCorrectness.Record.Proofs.Routines
