import Model.Vocabulary.Protocol.Handlers
import Proofs.Claims.ModelIrreducible
import Proofs.Vocabulary.Objects.Ancestry

/-!
# Facts about `Protocol.floor_on_stable`

The confirmation record's floor on the stable record.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Protocol.floor_on_stable

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- `floor_on_stable stable cand old` is `cand`, or `old`, or a block that is not an ancestor of
    `old`. -/
theorem floor_on_stable_cases (stable cand old : Block V) :
    Protocol.floor_on_stable stable cand old = cand ∨
      Protocol.floor_on_stable stable cand old = old ∨
      ¬ Block.Preceq (Protocol.floor_on_stable stable cand old) old := by
  unfold Protocol.floor_on_stable
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr h2)

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- `stable ⪯ floor_on_stable stable candidate old`. -/
theorem floor_on_stable_stable_preceq (stable candidate old : Block V) :
    Block.Preceq stable (Protocol.floor_on_stable stable candidate old) := by
  unfold Protocol.floor_on_stable
  split_ifs with h1 h2
  · exact h1
  · exact h2
  · exact Block.preceq_self _

end DecoupledConsensusModel.Sts
