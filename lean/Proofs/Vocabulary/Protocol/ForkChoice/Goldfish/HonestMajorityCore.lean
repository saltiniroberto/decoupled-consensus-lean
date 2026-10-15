module
public import Proofs.Vocabulary.Objects.Weights
public import Proofs.Vocabulary.Internal.Execution.Assumptions
public import Proofs.Vocabulary.Internal.ModelVocabulary.MajoritySG.ForkChoice
public import Proofs.Vocabulary.ModelVocabulary.Substrate.Env
import Mathlib.Tactic.ENatToNat

@[expose] public section

/-!
# Honest-weight-majority lemmas

Under a strict honest-weight majority, the faulty weight is less than the finality quorum threshold
and every finality quorum has an honest member.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal

variable {V : Type} [DecidableEq V] [Fintype V]

namespace HonestWeightMajority

/-! ## Threshold consequences -/

/-- Under a strict honest-weight majority, the faulty weight is less than the finality quorum
    threshold. -/
theorem faulty_lt_q
    {S : Execution.Setup V} {H : Finset V}
    (hmajority : Execution.HonestWeightMajority S H) :
    S.E.electorate.weightOf (Finset.univ \ H) < S.E.q := by
  have hsum := S.E.electorate.weightOf_add_weightOf_sdiff H
  unfold Execution.HonestWeightMajority at hmajority
  unfold Env.q Electorate.finalityThreshold
  omega


/-- Every finality quorum contains an honest validator. -/
theorem exists_honest_member_of_quorum
    {S : Execution.Setup V} {H Q : Finset V}
    (hmajority : Execution.HonestWeightMajority S H)
    (hQ : S.E.electorate.IsQuorum Q) :
    ∃ v ∈ Q, v ∈ H := by
  by_contra hnone
  push Not at hnone
  have hsub : Q ⊆ Finset.univ \ H := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hnone v hv⟩
  have hle := S.E.electorate.weightOf_mono hsub
  have hlt := faulty_lt_q hmajority
  unfold Electorate.IsQuorum at hQ
  unfold Env.q at hlt
  omega


end HonestWeightMajority

end Protocol
end DecoupledConsensusModel

end
