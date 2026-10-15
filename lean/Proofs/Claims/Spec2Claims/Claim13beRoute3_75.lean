import Proofs.Claims.Spec2Claims.Claim13beRoute3_72
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_Env_q
import Proofs.Claims.Spec2Claims.Claim13bModel_actionStoreAt
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_RootInjectiveBelow
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAttestation_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_Preceq

/-!
# A quorum has a member never held

Under monotone corruption, if the adversary holds less than a third of the total weight at `tB`,
every quorum has a member the adversary holds at no instant up to `tB`.
-/

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

/-- If corruption is monotone and the adversary at `tB` holds less than a third of the total weight,
    every quorum has a member the adversary holds at no instant at or before `tB`. -/
theorem exists_nonAdv_of_quorum_upTo (S : Setup V) (Sched : Schedule V) {tB : Int}
    (hmono : Sched.MonotoneCorruption)
    (hthird : 3 * S.E.electorate.weightOf (Sched.adv tB) < S.E.electorate.totalWeight)
    {Q : Finset V} (hQ : S.E.electorate.IsQuorum Q) :
    ∃ w ∈ Q, HonestThroughTime Sched tB w := by
  obtain ⟨z, hzQ, hzB⟩ : ∃ z ∈ Q, z ∉ Sched.adv tB := by
    by_cases hsub : Q ⊆ Sched.adv tB
    · exfalso
      have hle := S.E.electorate.weightOf_mono hsub
      have hq := two_mul_totalWeight_le_three_mul_q S.E
      have hQ' : S.E.q ≤ S.E.electorate.weightOf Q := (isQuorum_iff_q_le S.E Q).mp hQ
      omega
    · exact Finset.not_subset.1 hsub
  exact ⟨z, hzQ, fun t' ht' hmem => hzB (hmono t' tB ht' hmem)⟩

end AtRn

end DecoupledConsensusModel.Sts
