import Proofs.Claims.Spec2Claims.Claim13beRoute3_75
import Proofs.Claims.Spec2Claims.Claim13beRoute3_74
import Proofs.Claims.Spec2Claims.Claim13bModel_get_fg_root
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Vocabulary.ModelProperties.Block_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclG1
import Proofs.Vocabulary.ModelProperties.get_fg_root

/-!
# Slot and confirmation instants

Confirmation instants are monotone in the slot, and an opening slot plus one is strictly less than
the next round's opening slot.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every index into an sts execution is valid, so `get_elem_tactic` is answered by `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

section AtRn

open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If `s ≤ s'`, the confirmation instant of `s` is at or before that of `s'`. -/
theorem confirmation_time_mono_l78 (S : Setup V) {s s' : Slot} (h : s ≤ s') :
    Protocol.confirmation_time S.E s ≤ Protocol.confirmation_time S.E s' := by
  have hm := Protocol.proposal_time_mono S.E h
  rw [← DecoupledConsensusModel.Sts.proposal_time_add_six_delta, ← DecoupledConsensusModel.Sts.proposal_time_add_six_delta]
  linarith

/-- `opening_slot a + 1 ≤ opening_slot (a + 1)`. -/
theorem opening_slot_succ_le_l78 (S : Setup V) (a : Round) :
    S.hc.opening_slot a + 1 ≤ S.hc.opening_slot (a + 1) := by
  have hR : 1 ≤ S.hc.R := le_trans (by decide) S.hc.R_ge_two
  rw [DecoupledConsensusModel.Sts.opening_slot_succ]
  exact Nat.add_le_add_left hR _

/-- `opening_slot r + 1 < opening_slot (r + 1)`. -/
theorem opening_slot_succ_lt_l78 (S : Setup V) (r : Round) :
    S.hc.opening_slot r + 1 < S.hc.opening_slot (r + 1) := by
  have hR : 1 < S.hc.R := S.hc.R_ge_two
  rw [DecoupledConsensusModel.Sts.opening_slot_succ]
  exact Nat.add_lt_add_left hR _

end AtRn

end DecoupledConsensusModel.Sts
