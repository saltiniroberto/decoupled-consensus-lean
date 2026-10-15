import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.Weights
import Proofs.Claims.ModelIrreducible

/-!
# The finality threshold `q`

A quorum is a set whose weight reaches `E.q`, and `E.q` is at least two thirds of the total weight.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Electorate.finalityThreshold
  DecoupledConsensusModel.Electorate.totalWeight DecoupledConsensusModel.Env.q

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A set `A` of validators is a quorum of `E`'s electorate exactly when its weight is at least
    `E.q`. -/
theorem isQuorum_iff_q_le (E : Env V) (A : Finset V) :
    E.electorate.IsQuorum A ↔ E.q ≤ E.electorate.weightOf A := Iff.rfl

/-- Twice the total weight of `E`'s electorate is at most three times `E.q`. -/
theorem two_mul_totalWeight_le_three_mul_q (E : Env V) :
    2 * E.electorate.totalWeight ≤ 3 * E.q := by
  unfold Env.q Electorate.finalityThreshold
  omega

end DecoupledConsensusModel.Sts
