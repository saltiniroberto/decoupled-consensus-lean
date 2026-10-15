module
public import Proofs.Claims.Spec2Claims.Claim13bSGCompatible
public import Proofs.Claims.Spec2Claims.Claim13bModel_actionStoreAt
public import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
public import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
public import Proofs.Vocabulary.ModelProperties.Block_Preceq
public import Proofs.Vocabulary.ModelProperties.get_fg_root

@[expose] public section

/-!
# Arithmetic of the slot schedule

One delay after a slot's Goldfish vote instant is at or before that slot's confirmation instant.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A slot's Goldfish vote instant plus one delay is at or before that slot's confirmation instant. -/
theorem vote_time_add_delta_le_confirmation_time (S : Setup V) (s : Slot) :
    Protocol.vote_time S.E s + S.E.Δ ≤ Protocol.confirmation_time S.E s := by
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  rw [← slotStart_add_delta_eq_vote_time, ← slotStart_add_six_delta_eq_confirmation_time]
  linarith

end DecoupledConsensusModel.Sts
