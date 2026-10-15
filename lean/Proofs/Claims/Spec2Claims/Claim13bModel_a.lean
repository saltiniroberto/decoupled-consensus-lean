import Model.Vocabulary.Protocol.Grades
import Proofs.Claims.ModelIrreducible
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_slotStart
import Mathlib.Tactic.Ring
import Proofs.Claims.Spec2Claims.Claim13bModel_opening

/-!
# Facts about `Protocol.HealConfig.a`

The action time of a round, in closed form and relative to the round's opening and to the next
round.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.HealConfig.a
  DecoupledConsensusModel.Protocol.HealConfig.opening_slot DecoupledConsensusModel.slotStart

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

/-- Round `r` acts at `4Δ` times its opening slot, plus `6Δ`. -/
theorem healA_closed (hc : Protocol.HealConfig) (Δ : Int) (r : Round) :
    hc.a Δ r = 4 * Δ * ((hc.opening_slot r : Nat) : Int) + 6 * Δ := rfl

/-- The action time of round `r + 1` is the action time of round `r` plus the round length `4ΔR`. -/
theorem healA_succ_round (hc : Protocol.HealConfig) (Δ : Int) (r : Round) :
    hc.a Δ (r + 1) = hc.a Δ r + 4 * Δ * (hc.R : Int) := by
  rw [healA_closed, healA_closed]
  unfold Protocol.HealConfig.opening_slot
  push_cast
  ring

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts


end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

/-- Round `r`'s opening time plus `6Δ` is round `r`'s action time. -/
theorem opening_add_six_delta_eq_a {V : Type} [DecidableEq V] [Fintype V] (E : Env V)
    (hc : Protocol.HealConfig) (r : Round) :
    Protocol.opening E hc r + 6 * E.Δ = hc.a E.Δ r := by
  rw [healA_closed, opening_closed]

end DecoupledConsensusModel.Sts
