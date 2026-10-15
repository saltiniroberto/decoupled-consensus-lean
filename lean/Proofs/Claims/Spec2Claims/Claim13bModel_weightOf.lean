module

public import Model.Vocabulary.Objects.Weights
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts on `Electorate.weightOf`

The weight of a set of validators, against the total weight `Electorate.totalWeight`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Electorate.totalWeight
  DecoupledConsensusModel.Electorate.weightOf

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [Fintype V]

/-- The set of all validators weighs the total weight of `E`. -/
theorem weightOf_univ (E : Electorate V) : E.weightOf Finset.univ = E.totalWeight := rfl

/-- The empty set of validators weighs `0`. -/
theorem weightOf_empty (E : Electorate V) : E.weightOf (∅ : Finset V) = 0 := by
  unfold Electorate.weightOf
  exact Finset.sum_empty

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [Fintype V]

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [Fintype V]

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [Fintype V]


end DecoupledConsensusModel.Sts
