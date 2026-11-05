module
public import GoldilocksCorrectness.Record.NodeInvAddedFacts
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Proofs.Routines.Node
import all Goldilocks.FG.State
import all Goldilocks.Node

@[expose] public section

/-!
# The spec's readers that read the stored chain states and the stored greatest height

`nodeInvAddedFacts_goldilocks`: the spec's model satisfies `NodeInvAddedFacts`. Its node invariant
is `NodeInv` together with `HeightCacheAttained` of the node's FG state, so on a node state
satisfying it the stored chain state of a block of the tree is the block's own (the clause
`ChainStatesComputed` of `NodeInv`), and the stored greatest height `n.S.h_max` is `hMax` (the
clause `HeightCacheBounds` of `NodeInv` bounds every height of the tree by it, and
`HeightCacheAttained` says some block of the tree reaches it): `hMax_goldilocks`. Each field is
then the spec's reader with those two equations; the admission test passes through the library's
theorems on `block_admissible` and one more read off its body, `block_admissible_slot_le` (this
page sees the spec's bodies of the FG state's readers and of the node's routines).
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

open Goldilocks (Config Provisional External Block Attestation NodeState block_admissible)
open GoldilocksCorrectness.Record.Statements.Routines (hMax le_hMax)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- On a node state satisfying the spec's model's node invariant, the stored greatest chain-state
height `n.S.h_max` is the greatest chain-state height of the tree, `hMax`.

The variables:
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `h`: `n` satisfies the spec's model's node invariant.

Read aloud: under Goldilocks' node invariant, the stored greatest height is the tree's greatest
chain-state height. -/
theorem hMax_goldilocks {C : Config} {P : Provisional V} {X : External V} {n : NodeState V}
    (h : (Model.goldilocks (V := V)).nodeInv C P X n) :
    hMax (Model.goldilocks (V := V)) C n = n.S.h_max := by
  obtain ⟨hI, B, hB, hBh⟩ := h
  have hσ := hI.2.2.2.2.2.1
  have hHB := hI.2.2.2.2.2.2.2.2.2.1.2.1.2
  apply le_antisymm
  · refine Finset.sup_le (fun B' hB' => ?_)
    show (chainStateOf C B').h ≤ n.S.h_max
    rw [← hσ B' hB']
    exact hHB B' hB'
  · rw [← hBh, hσ B hB]
    exact le_hMax (Model.goldilocks (V := V)) (C := C) (n := n) hB

/-- Under the clock-free part of Goldilocks' node invariant, the stored greatest height `n.S.h_max`
is the tree's greatest chain-state height `hMax`: the same proof as `hMax_goldilocks`, which reads
only clock-free clauses.

The variables:
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `h`: `n` satisfies the clock-free part of the spec's model's node invariant.

Read aloud: under the clock-free part of Goldilocks' node invariant, the stored greatest height is
the tree's greatest chain-state height. -/
theorem hMax_goldilocks_of_core {C : Config} {P : Provisional V} {X : External V} {n : NodeState V}
    (h : (Model.goldilocks (V := V)).nodeInvCore C P X n) :
    hMax (Model.goldilocks (V := V)) C n = n.S.h_max := by
  obtain ⟨hI, B, hB, hBh⟩ := h
  have hσ := hI.2.2.2.2.2.1
  have hHB := hI.2.2.2.2.2.2.2.1.2.1.2
  apply le_antisymm
  · refine Finset.sup_le (fun B' hB' => ?_)
    show (chainStateOf C B').h ≤ n.S.h_max
    rw [← hσ B' hB']
    exact hHB B' hB'
  · rw [← hBh, hσ B hB]
    exact le_hMax (Model.goldilocks (V := V)) (C := C) (n := n) hB

omit [Fintype V] in
/-- A block the node admits has a slot at most the slot of the node's clock: the second test of
`block_admissible`.

The variables:
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state; `B`: the
  block;
- `h`: the node admits `B`.

Read aloud: a node admits no block of a slot later than its clock's. -/
theorem block_admissible_slot_le (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (B : Block V) (h : block_admissible C P X n B = true) :
    B.slot ≤ C.slot n.t := by
  simp only [block_admissible, Id.run] at h
  split at h
  · exact absurd h Bool.false_ne_true
  split at h
  · exact absurd h Bool.false_ne_true
  rename_i h2
  exact Nat.le_of_not_lt h2

/-- The spec's model satisfies the facts of the six readers that read the stored chain states and
the stored greatest height.

Read aloud: Goldilocks' readers of the stored chain states and the stored greatest height are, on a
node state satisfying its invariant, what the record says. -/
theorem nodeInvAddedFacts_goldilocks : NodeInvAddedFacts (Model.goldilocks (V := V)) where
  fg_contest_eq {C P X n} h := by
    have hσ := h.1.2.2.2.2.2.1
    rw [hMax_goldilocks h]
    show (if n.S.h_max ≠ n.S.h_j + 1 then false
        else decide (∃ B ∈ n.S.T, n.S.F.ancestorEq B ∧ (n.S.σ B).h = n.S.h_max ∧
          ¬ n.S.J.ancestorEq B)) =
      (if n.S.h_max ≠ n.S.h_j + 1 then false
        else decide (∃ B ∈ n.S.T, n.S.F.ancestorEq B ∧ (chainStateOf C B).h = n.S.h_max ∧
          ¬ n.S.J.ancestorEq B))
    split_ifs
    · rfl
    · refine decide_eq_decide.2 ⟨fun ⟨B, hB, h1, h2, h3⟩ => ⟨B, hB, h1, ?_, h3⟩,
        fun ⟨B, hB, h1, h2, h3⟩ => ⟨B, hB, h1, ?_, h3⟩⟩
      · rw [← hσ B hB]; exact h2
      · rw [hσ B hB]; exact h2
  fg_contest_eq_of_core {C P X n} h := by
    have hσ := h.1.2.2.2.2.2.1
    rw [hMax_goldilocks_of_core h]
    show (if n.S.h_max ≠ n.S.h_j + 1 then false
        else decide (∃ B ∈ n.S.T, n.S.F.ancestorEq B ∧ (n.S.σ B).h = n.S.h_max ∧
          ¬ n.S.J.ancestorEq B)) =
      (if n.S.h_max ≠ n.S.h_j + 1 then false
        else decide (∃ B ∈ n.S.T, n.S.F.ancestorEq B ∧ (chainStateOf C B).h = n.S.h_max ∧
          ¬ n.S.J.ancestorEq B))
    split_ifs
    · rfl
    · refine decide_eq_decide.2 ⟨fun ⟨B, hB, h1, h2, h3⟩ => ⟨B, hB, h1, ?_, h3⟩,
        fun ⟨B, hB, h1, h2, h3⟩ => ⟨B, hB, h1, ?_, h3⟩⟩
      · rw [← hσ B hB]; exact h2
      · rw [hσ B hB]; exact h2
  head_height_floor_eq {C P X n} h := by
    rw [hMax_goldilocks h]
    rfl
  head_height_floor_eq_of_core {C P X n} h := by
    rw [hMax_goldilocks_of_core h]
    rfl
  get_fc_root_eq {C P X n} h := by
    rw [hMax_goldilocks h]
    rfl
  get_fc_root_eq_of_core {C P X n} h := by
    rw [hMax_goldilocks_of_core h]
    rfl
  is_viable_eq {C P X n B} h hB := by
    show decide (Goldilocks.head_height_floor n.S ≤ (n.S.σ B).h) =
      decide (Goldilocks.head_height_floor n.S ≤ (chainStateOf C B).h)
    rw [h.1.2.2.2.2.2.1 B hB]
  is_viable_eq_of_core {C P X n B} h hB := by
    show decide (Goldilocks.head_height_floor n.S ≤ (n.S.σ B).h) =
      decide (Goldilocks.head_height_floor n.S ≤ (chainStateOf C B).h)
    rw [h.1.2.2.2.2.2.1 B hB]
  proposal_attestations_eq {C P X n H} h hH := by
    show n.S.attestations.filter
        (fun a => Goldilocks.valid_attestation (n.S.σ H) a && !Goldilocks.on_chain a H) =
      n.S.attestations.filter
        (fun a => Goldilocks.valid_attestation (chainStateOf C H) a && !Goldilocks.on_chain a H)
    rw [h.1.2.2.2.2.2.1 H hH]
  block_admissible_iff {C P X n} B h := by
    have hσ := h.1.2.2.2.2.2.1
    constructor
    · intro hb
      obtain ⟨h1, -, h3, h4, h5, h6, h7⟩ :=
        GoldilocksCorrectness.Proofs.Routines.block_admissible_facts C P X n B hb
      refine ⟨h1, block_admissible_slot_le C P X n B hb,
        GoldilocksCorrectness.Proofs.Routines.block_admissible_root_fresh C P X n B hb, h3, h4, h5,
        h6, fun a ha => ?_⟩
      have := h7 a ha
      rw [hσ B.parent h3] at this
      exact this
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      refine GoldilocksCorrectness.Proofs.Routines.block_admissible_of C P X n B h1 h2 h3 h4 h5 h6
        h7 (fun a ha => ?_)
      rw [hσ B.parent h4]
      exact h8 a ha

end GoldilocksCorrectness.Record
