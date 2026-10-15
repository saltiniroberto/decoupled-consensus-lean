module
public import Model.Vocabulary.Protocol.Schedule
public import Proofs.Claims.ModelIrreducible
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Facts about `Protocol.support_cutoff`

A slot's support cutoff, against the slot's start.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Env.t
  DecoupledConsensusModel.Protocol.support_cutoff DecoupledConsensusModel.Protocol.vote_time
  DecoupledConsensusModel.slotStart

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The support cutoff of slot `s` is the start of slot `s` plus `2Δ`. -/
theorem slotStart_add_two_delta_eq_support_cutoff (E : Env V) (s : Slot) :
    slotStart E.Δ s + 2 * E.Δ = Protocol.support_cutoff E s := rfl

end DecoupledConsensusModel.Sts
