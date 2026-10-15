module
public import Model.Vocabulary.Protocol.Grades
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_opening_inclRelay
public import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time
public import Proofs.Claims.Spec2Claims.Claim13bModel_slotStart
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The action time of a round and its opening

The action time `Protocol.HealConfig.a` of a round, related to the round's opening time.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.HealConfig.a

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Round `r`'s action time is round `r`'s opening time plus `6Δ`. -/
theorem healA_eq_opening_add_six_delta (E : Env V) (hc : Protocol.HealConfig) (r : Round) :
    hc.a E.Δ r = Protocol.opening E hc r + 6 * E.Δ := by
  rw [opening_eq_proposal_time_inclRelay, ← slotStart_eq_proposal_time]
  rfl

end DecoupledConsensusModel.Sts
