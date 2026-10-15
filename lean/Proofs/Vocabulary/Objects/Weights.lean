module
public import Proofs.Vocabulary.Protocol.ChainState.Evidence

@[expose] public section

/-!
# Weight arithmetic

Monotonicity, inclusion–exclusion and the complement identity for electorate weights, and the quorum
bounds built on them.
-/

open scoped BigOperators

namespace DecoupledConsensusModel

namespace Electorate

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Weight is monotone in the set. -/
theorem weightOf_mono (E : Electorate V) {S T : Finset V} (h : S ⊆ T) :
    E.weightOf S ≤ E.weightOf T :=
  Finset.sum_le_sum_of_subset h

/-- Weighted inclusion–exclusion: `w(S ∩ T) + w(S ∪ T) = w(S) + w(T)`. -/
theorem weight_inter_add_weight_union (E : Electorate V) (S T : Finset V) :
    E.weightOf (S ∩ T) + E.weightOf (S ∪ T) = E.weightOf S + E.weightOf T := by
  rw [Nat.add_comm (E.weightOf (S ∩ T))]
  exact Finset.sum_union_inter

/-- The weight of a union is at most the sum of the weights of its parts. -/
theorem weightOf_union_le (E : Electorate V) (S T : Finset V) :
    E.weightOf (S ∪ T) ≤ E.weightOf S + E.weightOf T := by
  have h := weight_inter_add_weight_union E S T
  omega

/-- The complement identity `w(S) + w(V \ S) = W`. -/
theorem weightOf_add_weightOf_sdiff (E : Electorate V) (S : Finset V) :
    E.weightOf S + E.weightOf (Finset.univ \ S) = E.totalWeight := by
  rw [Nat.add_comm]
  exact Finset.sum_sdiff (Finset.subset_univ S)

end Electorate

namespace Proofs

open Internal

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Quorum bounds -/


/-- A quorum `Q` puts weight at least `q − w(V \ Hon)` inside any set `Hon`, stated additively:
    `q ≤ w(Q ∩ Hon) + w(V \ Hon)`. -/
theorem quorum_meets_set (E : Env V) {Q Hon : Finset V}
    (hQ : E.electorate.IsQuorum Q) :
    E.q ≤ E.electorate.weightOf (Q ∩ Hon) +
      E.electorate.weightOf (Finset.univ \ Hon) := by
  have hsub : Q ⊆ (Q ∩ Hon) ∪ (Finset.univ \ Hon) := by
    intro i hi
    by_cases hmem : i ∈ Hon
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hi, hmem⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hmem⟩)
  have hmono := E.electorate.weightOf_mono hsub
  have hle := E.electorate.weightOf_union_le (Q ∩ Hon) (Finset.univ \ Hon)
  unfold Electorate.IsQuorum at hQ
  unfold Env.q
  omega

/-- If `Hon` is a quorum, its intersection with any quorum `Q` has weight at least `2q − W`
    (`HasIntersectionWeight`). -/
theorem honest_part_of_quorum (E : Env V) {Q Hon : Finset V}
    (hQ : E.electorate.IsQuorum Q) (hHon : E.electorate.IsQuorum Hon) :
    HasIntersectionWeight E (Q ∩ Hon) :=
  quorum_intersection E hQ hHon

end Proofs
end DecoupledConsensusModel

end
