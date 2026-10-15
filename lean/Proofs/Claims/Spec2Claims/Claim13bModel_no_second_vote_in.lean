import Model.Vocabulary.Protocol.ForkChoice.Goldfish
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.no_second_vote_in`

A lemma that unfolds the test that a set of late votes holds no other vote of a vote's signer.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.no_second_vote_in

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- `no_second_vote_in late vote` holds exactly when every vote of `late` is `vote` itself or has a
    signer other than `vote`'s. -/
theorem no_second_vote_in_eq_true_iff (late : Finset (GoldfishVote V)) (vote : GoldfishVote V) :
    Protocol.no_second_vote_in late vote = true ↔
      ∀ u ∈ late, u = vote ∨ u.val_index ≠ vote.val_index := by
  simp only [Protocol.no_second_vote_in, decide_eq_true_eq]

end DecoupledConsensusModel.Sts
