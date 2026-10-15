import Proofs.Claims.Spec2Claims.Claim13beRoute3_6
import Proofs.Claims.Spec2Claims.Claim13bModel_RootInjectiveBelow
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_gf_votes
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_view
import Proofs.Claims.Spec2Claims.Claim13bModel_propose_block_with_snd
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_with

/-!
# The carried votes of a proposal

The block the proposal duty returns is the one the proposal read constructs, and that block's
carried support votes are among its carried raw votes.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the named proposal duty `propose_block_with` returned the block `B`, then `proposal_with` at
    the pool-and-carried row source returned it too. -/
theorem proposal_with_of_propose_block_with (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) {B : NamedBlock V}
    (hB : (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).2 = some B) :
    Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st = some B :=
  proposal_with_eq_of_propose_block_with_snd contract E hc cfg nd st hB

/-- Every support vote carried by the block the proposal read constructs is one of that block's
    carried raw votes. -/
theorem proposal_with_support_subset (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    {B : NamedBlock V}
    (hB : Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st = some B) :
    ∀ u ∈ B.gf_support_votes, u ∈ B.gf_votes :=
  proposal_with_gf_support_subset contract .poolAndCarried E hc nd st hB

section

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

end

end DecoupledConsensusModel.Sts
