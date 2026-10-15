module
public import Proofs.Claims.Spec2Claims.Claim13bStepKitConfirm
public import Proofs.Vocabulary.Objects.AttestationCanonicality
public import Proofs.Claims.Spec2Claims.Claim13bModel_gradeBool_against
public import Proofs.Claims.Spec2Claims.Claim13bModel_early_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_author
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_goldfish_vote_with
public import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
public import Proofs.Claims.Spec2Claims.Claim13bModel_setClock
public import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_incl
public import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG2
public import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
public import Proofs.Claims.Spec2Claims.Claim13bModel_votes_by
public import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
public import Proofs.Claims.Spec2Claims.Claim13bModel_support_cutoff
public import Proofs.Claims.Spec2Claims.Claim13bModel_goldfish_vote_with
public import Proofs.Claims.Spec2Claims.Claim13bModel_slotStart_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_confirmation_time
public import Proofs.Claims.Spec2Claims.Claim13bModel_no_second_vote_in_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_Store_tau_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_GoldfishStore_tau_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_voter_view_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_view_freeze_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_beforeCutoff
public import Proofs.Claims.Spec2Claims.Claim13bModel_stampedBefore

@[expose] public section

/-!
# Timing of the Goldfish vote duty

Where a slot's Goldfish vote instant and support cutoff fall on the schedule.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The Goldfish vote instant of every slot is a whole multiple of `Δ`. -/
theorem vote_time_emod_delta (S : Setup V) (s : Slot) :
    Protocol.vote_time S.E s % S.E.Δ = 0 := by
  rw [← slotStart_add_delta_eq_vote_time, ← Int.emod_eq_add_self_emod]
  exact slotStart_emod_delta S s

/-- Every slot after slot `0` has its Goldfish vote instant strictly after time zero. -/
theorem vote_time_pos (S : Setup V) {s : Slot} (hs : 0 < s) :
    0 < Protocol.vote_time S.E s := by
  have hd := S.E.Δ_pos
  have h1 : (0 : Int) < slotStart S.E.Δ s := slotStart_pos S hs
  rw [← slotStart_add_delta_eq_vote_time]
  linarith

/-- Every slot has its support cutoff strictly after time zero. -/
theorem support_cutoff_pos (S : Setup V) (s : Slot) :
    0 < Protocol.support_cutoff S.E s := by
  have hd := S.E.Δ_pos
  have h1 : (0 : Int) ≤ slotStart S.E.Δ s := slotStart_nonneg (le_of_lt hd) s
  rw [← slotStart_add_two_delta_eq_support_cutoff]
  linarith

/-- A slot's support cutoff is at most its confirmation instant: `t_s + 2Δ ≤ t_s + 6Δ`. -/
theorem support_cutoff_le_confirmation_time (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s ≤ Protocol.confirmation_time E s := by
  have hd := E.Δ_pos
  rw [← slotStart_add_two_delta_eq_support_cutoff, ← slotStart_add_six_delta_eq_confirmation_time]
  linarith

end DecoupledConsensusModel.Sts
