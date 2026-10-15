module

public import Model.Vocabulary.Protocol.Evidence
public import Proofs.Claims.Spec2Claims.Claim13bModel_weightOf
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Proofs.Claims.ModelIrreducible
public import Proofs.Vocabulary.Objects.Weights
public import Proofs.Vocabulary.Protocol.ChainState.AlignedRoundLemmas
public import Proofs.Claims.Spec2Claims.Claim13bModel_Env_W

@[expose] public section

/-!
# The weight of a quorum intersection

A set with the weight of an intersection of two quorums, `HasIntersectionWeight`, weighs at least a
third of the total weight.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Electorate.finalityThreshold
  DecoupledConsensusModel.Electorate.totalWeight DecoupledConsensusModel.Electorate.weightOf
  DecoupledConsensusModel.Env.W DecoupledConsensusModel.Env.q
  DecoupledConsensusModel.HasIntersectionWeight

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Sts

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the set `X` of validators has the weight of an intersection of two quorums of the environment
    `E`, then the total weight of `E`'s electorate is at most three times the weight of `X`. -/
theorem totalWeight_le_three_mul_weightOf_of_hasIntersectionWeight {E : Env V} {X : Finset V}
    (h : HasIntersectionWeight E X) :
    E.electorate.totalWeight ≤ 3 * E.electorate.weightOf X := by
  have hq := Proofs.AlignedRoundLemmas.two_mul_W_le_three_mul_q E
  have hW := weightOf_add_weightOf_sdiff_eq_W E X
  have hT := Electorate.weightOf_add_weightOf_sdiff E.electorate X
  unfold HasIntersectionWeight at h
  omega

end DecoupledConsensusModel.Sts
