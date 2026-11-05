module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.CertificatesFGState
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders

@[expose] public section

/-!
# FGStateReadersOnChain, over a model

The theorems of `GoldilocksCorrectness/Proofs/Routines/FGStateReaders.lean` that read none
of the readers of the node's stored chain states or of its stored greatest height, over a
model `M` whose facts `F` hold: an attestation on a chain is included in the chain's block or
an ancestor of it, and the tree and the finalized block of `M.fg_to_ac n`. The page's
chain-state theorem is restated on `FGStateReadersChainState.lean`;

The recovery section at the end of the page states each landed theorem again, as the
landed statement (`type_of%`), and proves it from its record form at the spec's model
`Model.goldilocks` and its facts `goldilocksFacts`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_compatible ancestorEq_genesis_iff
  ancestorEq_node_iff ancestorEq_refl ancestorEq_trans compatible_iff)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- No attestation is included on the chain of the genesis block: the genesis block includes none
and has no ancestor. Added by the record migration, step 1f.

The variables:
- `M`: the model; `F`: its facts;
- `a`: the attestation.

Read aloud: nothing is on the genesis block's chain. -/
theorem on_chain_genesis (a : Attestation V) :
    M.on_chain a (Block.genesis : Block V) = false := by
  simp [F.rd.on_chain_eq, F.rd.attestations_on_chain_genesis]

/-- An attestation is included on the chain of `B` exactly when some block that is `B` or an
ancestor of `B` includes it.

The variables:
- `M`: the model; `F`: its facts;
- `a`: the attestation; `B`: the block.

Read aloud: an attestation is on a block's chain exactly when the block or one of its ancestors includes it. -/
theorem on_chain_iff (a : Attestation V) (B : Block V) :
    M.on_chain a B = true ↔ ∃ X : Block V, X.AncestorEq B ∧ a ∈ X.attestations := by
  induction B with
  | genesis =>
      constructor
      · intro h
        simp [F.rd.on_chain_eq, F.rd.attestations_on_chain_genesis] at h
      · rintro ⟨X, hX, ha⟩
        rw [(ancestorEq_genesis_iff X).1 hX] at ha
        exact absurd ha List.not_mem_nil
  | node p s r votes support ats v ih =>
      constructor
      · intro h
        simp only [F.rd.on_chain_eq, F.rd.attestations_on_chain_node, decide_eq_true_eq, List.mem_append] at h
        rcases h with h | h
        · exact ⟨_, ancestorEq_refl _, h⟩
        · obtain ⟨X, hX, ha⟩ := ih.1 (by simp only [F.rd.on_chain_eq, decide_eq_true_eq]; exact h)
          exact ⟨X, (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr hX), ha⟩
      · rintro ⟨X, hX, ha⟩
        rcases (ancestorEq_node_iff _ _ _ _ _ _ _ _).1 hX with rfl | hX
        · exact (on_chain_node_of_mem M F) a p s r votes support ats v ha
        · exact (on_chain_node_of_parent M F) a p s r votes support ats v (ih.2 ⟨X, hX, ha⟩)

/-- A block is in the tree of `M.fg_to_ac n` exactly when it is in the node's tree and the
node's finalized block is the block or an ancestor of it.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `B`: the block.

Read aloud: the tree of `M.fg_to_ac n` is the node's blocks that are its finalized block or a
descendant of it. -/
theorem mem_fg_to_ac_tree (n : M.N) (B : Block V) :
    B ∈ (M.fg_to_ac n).tree ↔ B ∈ n.tree ∧ n.finalized.AncestorEq B := by
  simp [F.rd.fg_to_ac_eq, Block.AncestorEq]

/-- An attestation on the chain of `H` is included in `H` or in an ancestor of `H`, other than
the genesis block.

The variables:
- `M`: the model; `F`: its facts;
- `a`: the attestation; `H`: the block.

Read aloud: an attestation on a block's chain is included in that block or an ancestor of it, other than the genesis block. -/
theorem exists_of_on_chain (a : Attestation V) (H : Block V) (h : M.on_chain a H = true) :
    ∃ Y : Block V, Y.AncestorEq H ∧ Y ≠ Block.genesis ∧ a ∈ Y.attestations := by
  induction H with
  | genesis =>
      simp [F.rd.on_chain_eq, F.rd.attestations_on_chain_genesis] at h
  | node p s r votes support ats v ih =>
      simp only [F.rd.on_chain_eq, F.rd.attestations_on_chain_node, decide_eq_true_eq, List.mem_append] at h
      rcases h with h | h
      · exact ⟨_, ancestorEq_refl _, (fun h' => by cases h'), h⟩
      · obtain ⟨Y, hY, hne, ha⟩ := ih (by simpa [F.rd.on_chain_eq] using h)
        exact ⟨Y, (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr hY), hne, ha⟩

/-- **The finalized block of `M.fg_to_ac n` is the node's.** The record `M.fg_to_ac n` carries
the node's finalized block `n.finalized` unchanged.

Why: `fg_to_ac_eq` builds the record with `F := n.finalized`.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state.

Read aloud: the finalized block of the record `M.fg_to_ac n` is the node's finalized block. -/
theorem fg_to_ac_F (n : M.N) :
    (M.fg_to_ac n).F = n.finalized := by
  rw [F.rd.fg_to_ac_eq]

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.on_chain_genesis`,
recovered from its record form at the spec's model.

Read aloud: the landed `on_chain_genesis` holds, as the record's theorem at the spec's
model. -/
theorem on_chain_genesis_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.on_chain_genesis V _) := by
  exact on_chain_genesis Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.on_chain_iff`,
recovered from its record form at the spec's model.

Read aloud: the landed `on_chain_iff` holds, as the record's theorem at the spec's
model. -/
theorem on_chain_iff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.on_chain_iff V _) := by
  exact on_chain_iff Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.mem_fg_to_ac_tree`,
recovered from its record form at the spec's model, at
the FG state `n.S` of every node state `n`.

Read aloud: the landed `mem_fg_to_ac_tree` holds at the FG state `n.S` of every node state `n`, as the record's theorem at the
spec's model. -/
theorem mem_fg_to_ac_tree_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.mem_fg_to_ac_tree V _ n.S) := by
  intro n
  exact mem_fg_to_ac_tree Model.goldilocks goldilocksFacts n

/-- The landed `GoldilocksCorrectness.Proofs.Routines.exists_of_on_chain`,
recovered from its record form at the spec's model.

Read aloud: the landed `exists_of_on_chain` holds, as the record's theorem at the spec's
model. -/
theorem exists_of_on_chain_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.exists_of_on_chain V _) := by
  exact exists_of_on_chain Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.fg_to_ac_F`,
recovered from its record form at the spec's model, at
the FG state `n.S` of every node state `n`.

Read aloud: the landed `fg_to_ac_F` holds at the FG state `n.S` of every node state `n`, as the record's theorem at the
spec's model. -/
theorem fg_to_ac_F_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.fg_to_ac_F V _ n.S) := by
  intro n
  exact fg_to_ac_F Model.goldilocks goldilocksFacts n

end GoldilocksCorrectness.Record.Proofs.Routines
