module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Proofs.Vocabulary.Internal.Definitions.Evidence
public import Model.Vocabulary.Protocol.Evidence
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.Weights
public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

/-!
# Weighted quorum intersection

Two quorums intersect in weight at least `2q − W`, with no fault bound.
-/

namespace DecoupledConsensusModel
namespace Proofs

open Internal

variable {V : Type} [DecidableEq V] [Fintype V]


omit [DecidableEq V] in
/-- No validator set weighs more than the electorate. -/
theorem weightOf_le_totalWeight (E : Electorate V) (S : Finset V) :
    E.weightOf S ≤ E.totalWeight :=
  Finset.sum_le_sum_of_subset (Finset.subset_univ S)

/-- Two quorums intersect in weight at least `2q − W`, stated additively as `HasIntersectionWeight`. -/
theorem quorum_intersection (E : Env V) {Q Q' : Finset V}
    (hQ : E.electorate.IsQuorum Q) (hQ' : E.electorate.IsQuorum Q') :
    HasIntersectionWeight E (Q ∩ Q') := by
  have hie : E.electorate.weightOf (Q ∪ Q') + E.electorate.weightOf (Q ∩ Q')
      = E.electorate.weightOf Q + E.electorate.weightOf Q' :=
    Finset.sum_union_inter
  have hu := weightOf_le_totalWeight E.electorate (Q ∪ Q')
  unfold Electorate.IsQuorum at hQ hQ'
  unfold HasIntersectionWeight Env.q Env.W
  omega

end Proofs
end DecoupledConsensusModel

end
