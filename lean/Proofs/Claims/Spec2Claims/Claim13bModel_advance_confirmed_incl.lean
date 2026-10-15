import Model.Vocabulary.Protocol.Handlers
import Proofs.Vocabulary.Objects.Ancestry
import Proofs.Claims.ModelIrreducible

/-!
# More facts about `Protocol.advance_confirmed`

The candidate of the record update is an ancestor of what it returns.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Protocol.advance_confirmed

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- `c ⪯ advance_confirmed old c`. -/
theorem preceq_advance_confirmed_candidate (old c : Block V) :
    Block.Preceq c (Protocol.advance_confirmed old c) := by
  unfold Protocol.advance_confirmed
  split_ifs with h
  · exact h
  · exact Block.preceq_self c

end DecoupledConsensusModel.Sts
