import Model.Vocabulary.Protocol.Grades
import Proofs.Claims.ModelIrreducible
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot

/-!
# Facts about `Protocol.opening`

Lemmas that unfold the instant a round opens.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Env.t
  DecoupledConsensusModel.Protocol.opening DecoupledConsensusModel.Protocol.proposal_time
  DecoupledConsensusModel.slotStart

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Round `r` opens at `4Δ` times its opening slot. -/
theorem opening_closed (E : Env V) (hc : Protocol.HealConfig) (r : Round) :
    Protocol.opening E hc r = 4 * E.Δ * ((hc.opening_slot r : Nat) : Int) := rfl

/-- Round `r` opens at the proposal instant of its opening slot. -/
theorem opening_eq_proposal_time (E : Env V) (hc : Protocol.HealConfig) (r : Round) :
    Protocol.opening E hc r = Protocol.proposal_time E (hc.opening_slot r) := rfl

/-- If the environments `E` and `E'` have the same delay `Δ`, then round `r` opens at the same
    instant in both. -/
theorem opening_eq_of_delta_eq {E E' : Env V} (h : E.Δ = E'.Δ) (hc : Protocol.HealConfig)
    (r : Round) : Protocol.opening E hc r = Protocol.opening E' hc r := by
  unfold Protocol.opening Protocol.proposal_time Env.t
  rw [h]

/-- Round `r + k` opens `k` round lengths `4ΔR` after round `r`. -/
theorem opening_add (E : Env V) (hc : Protocol.HealConfig) (r k : Round) :
    Protocol.opening E hc (r + k) =
      Protocol.opening E hc r + (k : Int) * (4 * E.Δ * (hc.R : Int)) := by
  rw [opening_closed, opening_closed, opening_slot_add]
  push_cast
  ring

end DecoupledConsensusModel.Sts
