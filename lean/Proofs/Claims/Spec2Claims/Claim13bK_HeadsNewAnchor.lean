import Proofs.Claims.Spec2Claims.Claim13beRoute3_7
import Proofs.Claims.Spec2Claims.Claim13bModel_GoldfishStore_pool
import Proofs.Claims.Spec2Claims.Claim13bK_CrossTransport
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_get_head_in_tree_with
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG5
import Proofs.Claims.Spec2Claims.Claim13bModel_view_freeze
import Proofs.Claims.Spec2Claims.Claim13bModel_beforeCutoff
import Proofs.Claims.Spec2Claims.Claim13bModel_stampedBefore
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG2
import Proofs.Claims.Spec2Claims.Claim13bModel_slotStart
import Proofs.Claims.Spec2Claims.Claim13bModel_support_cutoff
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmation_time
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_view
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_gf_votes
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclX
import Proofs.Claims.Spec2Claims.Claim13bModel_goldfish_score

/-!
# The support cutoff is a multiple of the delay

A slot's support cutoff leaves no remainder on division by the delay `S.E.Δ`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

section

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

/-- A slot's support cutoff `Protocol.support_cutoff S.E s` leaves no remainder on division by
    `S.E.Δ`. -/
theorem support_cutoff_emod_delta (s : Slot) :
    Protocol.support_cutoff S.E s % S.E.Δ = 0 := by
  rw [← slotStart_add_two_delta_eq_support_cutoff, slotStart_eq_proposal_time,
    Int.add_mul_emod_self_right]
  exact proposal_time_emod_delta_inclX S.E s

end

end DecoupledConsensusModel.Sts
