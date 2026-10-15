module
public import Model.Vocabulary.Protocol.ForkChoice.Goldfish
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.no_second_vote_in`, for module files

The direction of `no_second_vote_in` that builds the test from its condition.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.no_second_vote_in

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If every vote of `late` is `vote` itself or has a signer other than `vote`'s, then
    `no_second_vote_in late vote` holds. -/
theorem no_second_vote_in_of_forall {late : Finset (GoldfishVote V)} {vote : GoldfishVote V}
    (h : ∀ u ∈ late, u = vote ∨ u.val_index ≠ vote.val_index) :
    Protocol.no_second_vote_in late vote = true := by
  unfold Protocol.no_second_vote_in
  exact decide_eq_true h

end DecoupledConsensusModel.Sts
