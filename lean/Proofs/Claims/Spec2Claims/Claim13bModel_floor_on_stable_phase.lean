import Model.Vocabulary.Protocol.Handlers
import Proofs.Claims.ModelIrreducible

/-!
# The three values of `Protocol.floor_on_stable`

The floor returns the candidate, the old record, or the stable record.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Protocol.floor_on_stable

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- `floor_on_stable stable cand old` is `cand` with `stable ⪯ cand`, or `old` with `stable ⪯ old`,
    or `stable`. -/
theorem floor_on_stable_values (stable cand old : Block V) :
    (Block.Preceq stable cand ∧ Protocol.floor_on_stable stable cand old = cand) ∨
      (Block.Preceq stable old ∧ Protocol.floor_on_stable stable cand old = old) ∨
      Protocol.floor_on_stable stable cand old = stable := by
  unfold Protocol.floor_on_stable
  split_ifs with h1 h2
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨h2, rfl⟩)
  · exact Or.inr (Or.inr rfl)

end DecoupledConsensusModel.Sts
