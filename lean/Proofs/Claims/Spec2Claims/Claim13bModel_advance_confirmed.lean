import Model.Vocabulary.Protocol.Handlers
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.advance_confirmed`

The record update that keeps the old record when the candidate is its ancestor and takes the
candidate otherwise.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Protocol.advance_confirmed

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- `advance_confirmed old c` is `old`, or it is not an ancestor of `old`. -/
theorem advance_confirmed_eq_or_not_preceq (old c : Block V) :
    Protocol.advance_confirmed old c = old ∨
      ¬ Block.Preceq (Protocol.advance_confirmed old c) old := by
  unfold Protocol.advance_confirmed
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr h

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If `c ⪯ old`, then `advance_confirmed old c` is `old`. -/
theorem advance_confirmed_of_preceq {old c : Block V} (h : Block.Preceq c old) :
    Protocol.advance_confirmed old c = old := by
  unfold Protocol.advance_confirmed
  exact if_pos h

end DecoupledConsensusModel.Sts
