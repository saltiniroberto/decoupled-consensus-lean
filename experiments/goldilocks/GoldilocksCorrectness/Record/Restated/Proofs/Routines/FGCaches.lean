module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FrameFGState
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGCachesDefs
public import GoldilocksCorrectness.Proofs.Routines.FGCaches

@[expose] public section

/-!
# FGCaches, over a model: a viable descendant and a viable head from witnessed caches

The two theorems of `GoldilocksCorrectness/Proofs/Routines/FGCaches.lean` that read the readers of
the stored chain states and the stored greatest height, over a model `M` whose facts `F` hold: a
block with a viable descendant has a descendant of chain-state height at least `hMax M C n − 1`,
and a node state whose caches are witnessed has a viable head. Each is stated for a node state `n`
satisfying the model's node invariant `M.nodeInv C P X n` (the readers' facts `F.ndAdded` hold
under it), with `hMax M C n` for the stored greatest height and `M.chainStateOf C B` for the stored
chain state of a block; the landed hypothesis that the stored chain states are the blocks' own is
dropped (over the record it always holds). The page's definitions are restated on
`Record/Restated/Proofs/Routines/FGCachesDefs.lean`; its theorems about the FG handlers are the
receipt facts of `Record/ReceiveAddedFacts.lean`.

The recovery section at the end of the page states each landed theorem again, as the landed
statement (`type_of%`) at the FG state `n.S` of a node state `n` satisfying the spec's model's node
invariant, and proves it from its record form at the spec's model `Model.goldilocks` and its facts
`goldilocksFacts`, reading `hMax` as the stored `n.S.h_max` (`hMax_goldilocks`) and the chain state
of a block of the tree as the stored one (the invariant's clause `ChainStatesComputed`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Statements.Routines (hMax)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl)

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- A block `F₀` with a viable descendant has a block of the tree, `F₀` or a descendant of it, of
chain-state height at least `hMax M C n − 1`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `F₀`: the block.

Read aloud: a block with a viable descendant has an accepted descendant, or itself, at chain-state
height at least `hMax M C n − 1`. -/
theorem has_viable_descendant_witness (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (F₀ : Block V)
    (hv : M.has_viable_descendant n F₀ = true) :
    ∃ B' ∈ n.tree, F₀.AncestorEq B' ∧ hMax M C n - 1 ≤ (M.chainStateOf C B').h := by
  rw [F.rd.has_viable_descendant_eq, decide_eq_true_eq] at hv
  obtain ⟨B', hB', hanc, hvi⟩ := hv
  rw [F.ndAdded.is_viable_eq hI hB', decide_eq_true_eq] at hvi
  have h1 : (hMax M C n : ℕ) ≤ M.head_height_floor n + 1 := h_max_le_floor_add_one M F C P X n hI
  exact ⟨B', hB', hanc, Nat.sub_le_of_le_add (le_trans h1 (Nat.add_le_add_right hvi 1))⟩

/-- **`exists_viable_head_of_witnessed` under the clock-free part of the node invariant.** Its hypothesis `hI` is
`M.nodeInvCore C P X n`, the clauses of the node invariant that compare no stamp with the clock, which
hold for every validator, one in the adversary set included; `exists_viable_head_of_witnessed` is this theorem at
`F.nd.nodeInv_core hI`.

 A node state whose justified block is in its tree, with the finalized block an ancestor of it
or it, and which satisfies `CachesWitnessed`, has a viable head: in box 3 the block that makes it
contested; in box 2 the justified block; otherwise a block on the finalized block's chain at a
chain-state height at least `hMax M C n − 1`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the clock-free part of the model's node invariant,
  `M.nodeInvCore C P X n`.

Read aloud: a node state with witnessed caches has a viable head. -/
theorem exists_viable_head_of_witnessed_of_core (C : Config) (P : Provisional V) (X : External V)
    (n : M.N) (hI : M.nodeInvCore C P X n)
    (hFJ : n.finalized.AncestorEq n.justified)
    (hJT : n.justified ∈ n.tree) (hW : CachesWitnessed M C n) :
    ∃ W : Block V, W ∈ (M.fg_to_ac n).viable_heads := by
  obtain ⟨⟨D, -, hDJ, hDj⟩, -, ⟨W, hWT, hFW, hWh⟩⟩ := hW
  have hfc : (M.fg_to_ac n).fc_root = M.get_fc_root n := fc_root_eq M F n
  cases hc : M.fg_contest n with
  | true =>
      obtain ⟨-, hroot, hfloor⟩ := frameShape_of_boxThree_of_core M F C P X n hI hc
      obtain ⟨-, B, hBT, hFB, hBh, -⟩ := fg_contest_spec_of_core M F C P X n hI hc
      refine ⟨B, (mem_viable_heads_iff_of_core M F C P X n hI B).2 ⟨hBT, hFB, ?_, ?_⟩⟩
      · rw [hfc, hroot]
        exact hFB
      · rw [hfloor]
        exact le_of_eq hBh.symm
  | false =>
      by_cases hbox : hMax M C n = n.justifiedHeight + 1
      · obtain ⟨hroot, hfloor⟩ :=
          frameShape_of_boxTwo_of_core M F C P X n hI n.justified ⟨hbox, hc, rfl⟩
        refine ⟨n.justified, (mem_viable_heads_iff_of_core M F C P X n hI n.justified).2
          ⟨hJT, hFJ, ?_, ?_⟩⟩
        · rw [hfc, hroot]
          exact ancestorEq_refl _
        · rw [hfloor, hbox, Nat.add_sub_cancel]
          rcases Nat.eq_zero_or_pos n.justifiedHeight with h0 | hpos
          · rw [h0]
            exact Nat.zero_le _
          · rw [hDJ, hDj]
            rw [hDj] at hpos
            exact le_of_eq ((chainStateOf_J_spec M F C D).2.2 hpos).symm
      · have hroot : M.get_fc_root n = n.finalized := by
          rw [F.ndAdded.get_fc_root_eq_of_core hI]
          simp [hbox]
        have hfloor : M.head_height_floor n = hMax M C n - 1 :=
          head_height_floor_of_not_contested_of_core M F C P X n hI hc
        refine ⟨W, (mem_viable_heads_iff_of_core M F C P X n hI W).2 ⟨hWT, hFW, ?_, ?_⟩⟩
        · rw [hfc, hroot]
          exact hFW
        · rw [hfloor]
          exact hWh

/-- A node state whose justified block is in its tree, with the finalized block an ancestor of it
or it, and which satisfies `CachesWitnessed`, has a viable head: in box 3 the block that makes it
contested; in box 2 the justified block; otherwise a block on the finalized block's chain at a
chain-state height at least `hMax M C n − 1`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant.

Read aloud: a node state with witnessed caches has a viable head. -/
theorem exists_viable_head_of_witnessed (C : Config) (P : Provisional V) (X : External V)
    (n : M.N) (hI : M.nodeInv C P X n)
    (hFJ : n.finalized.AncestorEq n.justified)
    (hJT : n.justified ∈ n.tree) (hW : CachesWitnessed M C n) :
    ∃ W : Block V, W ∈ (M.fg_to_ac n).viable_heads :=
  exists_viable_head_of_witnessed_of_core M F C P X n (F.nd.nodeInv_core hI) hFJ hJT hW

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.has_viable_descendant_witness`, recovered from
its record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the
spec's model's node invariant.

Read aloud: the landed `has_viable_descendant_witness` holds at the FG state of every node state
satisfying the invariant. -/
theorem has_viable_descendant_witness_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.has_viable_descendant_witness V _ n.S) := by
  intro C P X n hI F₀ hv
  obtain ⟨B', hB', hanc, hh⟩ :=
    has_viable_descendant_witness Model.goldilocks goldilocksFacts C P X n hI F₀ hv
  rw [hMax_goldilocks hI] at hh
  refine ⟨B', hB', hanc, ?_⟩
  rw [hI.1.2.2.2.2.2.1 B' hB']
  exact hh

/-- The landed `GoldilocksCorrectness.Proofs.Routines.exists_viable_head_of_witnessed`, recovered
from its record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying
the spec's model's node invariant.

Read aloud: the landed `exists_viable_head_of_witnessed` holds at the FG state of every node state
satisfying the invariant. -/
theorem exists_viable_head_of_witnessed_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.exists_viable_head_of_witnessed V _ _ C
        n.S) := by
  intro C P X n hI _ hFJ hJT hW
  exact exists_viable_head_of_witnessed Model.goldilocks goldilocksFacts C P X n hI hFJ hJT
    ((goldilocks_CachesWitnessed C n (hMax_goldilocks hI).symm).1 hW)

end GoldilocksCorrectness.Record.Proofs.Routines
