module
public import Proofs.Claims.Spec2Claims.Claim13bHandover
public import Proofs.Claims.Spec2Claims.Claim13bModel_HasIntersectionWeight
public import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
public import Proofs.Claims.Spec2Claims.Claim13bModel_a_mk_s4
public import Proofs.Claims.Spec2Claims.Claim13bModel_confirmation_time
public import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
public import Proofs.Claims.Spec2Claims.Claim13bModel_author

@[expose] public section

/-!
# The switch round and the slot schedule

The switch round `switchRound`, the last round whose third slot is confirmed by a given instant, and
monotonicity facts on the slot schedule.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The switch round and the schedule arithmetic -/

/-- The switch round: the last round `r`, searched up to `tE.toNat`, for which the confirmation
    instant of slot `opening_slot r + 2` is at most `tE`. -/
noncomputable def switchRound (S : Setup V) (tE : Int) : Round :=
  Nat.findGreatest
    (fun r => Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤ tE) tE.toNat

/-- The confirmation instant is monotone in the slot. -/
theorem confirmation_time_mono (S : Setup V) {s s' : Slot} (h : s ≤ s') :
    Protocol.confirmation_time S.E s ≤ Protocol.confirmation_time S.E s' := by
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hs := slotStart_le_slotStart (le_of_lt hΔ) h
  rw [← slotStart_add_six_delta_eq_confirmation_time,
    ← slotStart_add_six_delta_eq_confirmation_time]
  linarith

/-- The opening slot is monotone in the round. -/
theorem opening_slot_mono (S : Setup V) {r r' : Round} (h : r ≤ r') :
    S.hc.opening_slot r ≤ S.hc.opening_slot r' :=
  opening_slot_le_of_le_mk S.hc h

/-- A slot's Goldfish vote instant is at most its confirmation instant. -/
theorem vote_time_le_confirmation_time (S : Setup V) (s : Slot) :
    Protocol.vote_time S.E s ≤ Protocol.confirmation_time S.E s := by
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  rw [← slotStart_add_delta_eq_vote_time, ← slotStart_add_six_delta_eq_confirmation_time]
  linarith

end DecoupledConsensusModel.Sts
