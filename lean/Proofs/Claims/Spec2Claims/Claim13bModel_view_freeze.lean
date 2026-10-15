import Model.Vocabulary.Protocol.Schedule
import Proofs.Claims.ModelIrreducible

/-!
# Facts on `Protocol.view_freeze`

The view freeze of a slot against the slot's proposal instant.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Env.t
  DecoupledConsensusModel.Protocol.proposal_time DecoupledConsensusModel.Protocol.view_freeze
  DecoupledConsensusModel.slotStart

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The view freeze of slot `s` is the proposal instant of slot `s` plus `3Δ`. -/
theorem proposal_time_add_three_delta_eq_view_freeze (E : Env V) (s : Slot) :
    Protocol.proposal_time E s + 3 * E.Δ = Protocol.view_freeze E s := rfl

end DecoupledConsensusModel.Sts
