module
public import Model.Vocabulary.Objects.NamedBlocks
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `NamedBlock.Preceq`

The lemmas that unfold the ancestry proposition `NamedBlock.Preceq` on named blocks and the Boolean
test `NamedBlock.preceq` it is stated over.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.NamedBlock.Preceq
  DecoupledConsensusModel.NamedBlock.preceq

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- A named block is an ancestor of itself. -/
theorem namedBlock_Preceq_self (B : NamedBlock V) : NamedBlock.Preceq B B := by
  cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- The named block `p` is an ancestor of every named node whose parent is `p`. -/
theorem namedBlock_Preceq_parent_node (p : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V) :
    NamedBlock.Preceq p (NamedBlock.node p s root votes support rows proposer) := by
  have hself := namedBlock_Preceq_self p
  simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true] at hself ⊢
  exact Or.inr hself

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- The named genesis is an ancestor of every named block. -/
theorem genesis_namedPreceq_l75 (B : NamedBlock V) : NamedBlock.Preceq .genesis B := by
  induction B with
  | genesis => simp [NamedBlock.Preceq, NamedBlock.preceq]
  | node parent s root votes support rows proposer ih =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
    exact Or.inr ih

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- `A ⪯ node p …` exactly when `A` is that node or `A ⪯ p`. -/
theorem namedPreceq_node_iff_l85 {A p : NamedBlock V} {s : Slot} {root : BlockId}
    {votes support : List (GoldfishVote V)} {rows : List (NamedAttestation V)} {proposer : V} :
    NamedBlock.Preceq A (.node p s root votes support rows proposer) ↔
      A = .node p s root votes support rows proposer ∨ NamedBlock.Preceq A p := by
  simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true, decide_eq_true_eq]

/-- Only the named genesis is an ancestor of the named genesis. -/
theorem namedPreceq_genesis_iff_l85 {A : NamedBlock V} :
    NamedBlock.Preceq A .genesis ↔ A = .genesis := by
  simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq]

end DecoupledConsensusModel.Sts
