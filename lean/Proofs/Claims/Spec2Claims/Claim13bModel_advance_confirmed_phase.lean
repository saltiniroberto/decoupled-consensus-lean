import Model.Vocabulary.Protocol.Handlers
import Proofs.Vocabulary.Objects.Ancestry
import Proofs.Claims.ModelIrreducible

/-!
# The two values of `Protocol.advance_confirmed`

The record update returns the old record, when the candidate is its ancestor, or the candidate.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Protocol.advance_confirmed

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- `advance_confirmed old c` is `old` with `c ⪯ old`, or it is `c`. -/
theorem advance_confirmed_values (old c : Block V) :
    (Block.Preceq c old ∧ Protocol.advance_confirmed old c = old) ∨
      Protocol.advance_confirmed old c = c := by
  unfold Protocol.advance_confirmed
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr rfl


end DecoupledConsensusModel.Sts
