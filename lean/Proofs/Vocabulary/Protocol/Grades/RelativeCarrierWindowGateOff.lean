module
public import Proofs.Vocabulary.Protocol.Grades.RelativeSupporter
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeDelivery
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HeightProgressSeedRegime
public import Proofs.Vocabulary.Protocol.Grades.RecoveryGenuineClearNextVote
public import Proofs.Vocabulary.Protocol.Grades.RelativeOneChain
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star

@[expose] public section

/-!
# Grade formation

When the faulty weight is less than one third, a positive round after GST has a grade-forming
majority.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.NamedOutageEntry
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- When the faulty weight is less than one third and `S.a (r - 1)` is at or after GST, a positive
    round `r` has a grade-forming majority. -/
theorem gradeFormingMajority_of_admissible_belowOneThird
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest) {r : Round} (hr : 0 < r)
    (hhor : domain S.E S.hc r .g2 ≤ rho.horizon)
    (hpost : S.E.t_GST ≤ S.a (r - 1)) :
    GradeFormingMajority S rho r := by
  have hq : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hfb
  have hprev : S.a (r - 1) ≤ rho.horizon :=
    (NamedOutageClosure.action_le_domain S S.hc.R_ge_three
      (Nat.sub_lt hr (by decide))).trans hhor
  have hvoters : honestRoundVoters S rho (r - 1) = rho.honest := by
    apply Finset.Subset.antisymm
    · intro v hv
      exact ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho v (r - 1)).mp hv).1
    · intro v hv
      apply (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho v (r - 1)).mpr
      have hemit := honest_emits_exact_actionAttestationAt S adm hv (r - 1) hprev hpost
      have hshape := actionAttestationAt_shape S rho v (r - 1)
      exact ⟨hv, actionAttestationAt S rho v (r - 1), hshape.1,
        hshape.2.1, hemit⟩
  have hhistorical : historicalHonestVoters S rho r ⊆ rho.honest := by
    intro v hv
    obtain ⟨k, _, hvote⟩ := Finset.mem_biUnion.mp hv
    exact ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho v k).mp hvote).1
  have hstale : staleHistoricalVoters S rho r = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro v hv
    have hvoter : v ∈ honestRoundVoters S rho (r - 1) := by
      rw [hvoters]
      exact hhistorical (Finset.mem_sdiff.mp hv).1
    exact (Finset.mem_sdiff.mp hv).2 hvoter
  unfold GradeFormingMajority
  rw [hvoters, hstale, Finset.union_empty]
  exact hq

end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms gradeFormingMajority_of_admissible_belowOneThird
end DecoupledConsensusModel.Proofs.HealingSurface

end
