module
public import Model.Vocabulary.Objects.Parameters
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# The total weight `W`

A set of validators and the validators outside it weigh the total weight `E.W` together.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Electorate.totalWeight
  DecoupledConsensusModel.Electorate.weightOf DecoupledConsensusModel.Env.W

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- For every set `A` of validators, the weight of `A` plus the weight of the validators outside `A`
    is the total weight `E.W`. -/
theorem weightOf_add_weightOf_sdiff_eq_W (E : Env V) (A : Finset V) :
    E.electorate.weightOf A + E.electorate.weightOf (Finset.univ \ A) = E.W := by
  unfold Env.W Electorate.weightOf Electorate.totalWeight
  rw [Nat.add_comm]
  exact Finset.sum_sdiff (Finset.subset_univ A)

end DecoupledConsensusModel.Sts
