module
public import Model.Vocabulary.Protocol.Schedule
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts on `Protocol.votes_by`

The votes of a set cast by one validator.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.votes_by

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- `u` is among the votes of `votes` cast by `v` exactly when `u` is in `votes` and its validator
    index is `v`. -/
theorem mem_votes_by_iff (votes : Finset (GoldfishVote V)) (v : V) (u : GoldfishVote V) :
    u ∈ Protocol.votes_by votes v ↔ u ∈ votes ∧ u.val_index = v := by
  unfold Protocol.votes_by
  exact Finset.mem_filter

end DecoupledConsensusModel.Sts
