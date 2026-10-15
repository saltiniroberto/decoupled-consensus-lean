import Proofs.Claims.Spec2Claims.Claim13beRoute3_50
import Proofs.Claims.Spec2Claims.Claim13bModel_Block_parent_inclG5
import Proofs.Claims.Spec2Claims.Claim13bModel_Block_parent
import Proofs.Claims.Spec2Claims.Claim13bModel_select
import Proofs.Claims.Spec2Claims.Claim13bModel_get_head_with
import Proofs.Claims.Spec2Claims.Claim13bModel_goldfish_fork_choice
import Proofs.Claims.Spec2Claims.Claim13bModel_occurrenceBefore
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeView
import Proofs.Claims.Spec2Claims.Claim13bModel_head_covers
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.Spec2Claims.Claim13bModel_initial
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_rawInputs
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAttestation_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_on_sg_vote
import Proofs.Claims.Spec2Claims.Claim13bModel_sgVote
import Proofs.Vocabulary.ModelProperties.NamedReceipt_processed
import Proofs.Vocabulary.ModelProperties.NamedReceipt_process
import Proofs.Claims.Spec2Claims.Claim13bModel_domain
import Proofs.Claims.Spec2Claims.Claim13bModel_a
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time

/-!
# Opening-slot arithmetic

With `R ≥ 2`, the slot two after round `q`'s opening slot is at most round `q + 1`'s opening slot.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

section FrontierRelay

open DecoupledConsensusModel.Statements.Instantiation

/-- `opening_slot q + 2 ≤ opening_slot (q + 1)`. -/
theorem plusTwo_slot_le_nextOpening_l53 (S : Setup V) (q : Round) :
    S.hc.opening_slot q + 2 ≤ S.hc.opening_slot (q + 1) := by
  rw [opening_slot_succ]
  exact Nat.add_le_add_left S.hc.R_ge_two _

end FrontierRelay

section RelativeCrossReaderKernel

open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Proofs.NamedRawRelay

local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

end RelativeCrossReaderKernel

end DecoupledConsensusModel.Sts
