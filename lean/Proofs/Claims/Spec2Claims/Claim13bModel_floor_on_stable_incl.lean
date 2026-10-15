import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Model.Vocabulary.Protocol.Handlers
import Proofs.Vocabulary.Objects.Ancestry

/-!
# More facts about `Protocol.floor_on_stable`

An ancestor of the candidate is an ancestor of the floor's result when the stable record and the
candidate are compatible.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Protocol.floor_on_stable

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If `stable` and `cand` are compatible and `X ⪯ cand`, then
    `X ⪯ floor_on_stable stable cand old`, whatever `old` is. -/
theorem preceq_floor_on_stable_of_compatible {X stable cand : Block V} (old : Block V)
    (hc : Block.compatible stable cand = true) (hX : Block.Preceq X cand) :
    Block.Preceq X (Protocol.floor_on_stable stable cand old) := by
  unfold Protocol.floor_on_stable
  split_ifs with h1 h2
  · exact hX
  · rcases compatible_cases hc with h | h
    · exact absurd h h1
    · exact Block.preceq_trans hX (Block.preceq_trans h h2)
  · rcases compatible_cases hc with h | h
    · exact absurd h h1
    · exact Block.preceq_trans hX h

end DecoupledConsensusModel.Sts
