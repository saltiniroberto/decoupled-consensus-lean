module
public import Model.Vocabulary.Protocol.Handlers
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.on_goldfish_vote_checked`: the slot

A lemma that unfolds the checked Goldfish-vote handler and the unchecked handler
`Protocol.on_goldfish_vote` it calls.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.on_goldfish_vote
  DecoupledConsensusModel.Protocol.on_goldfish_vote_checked

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The checked Goldfish-vote handler keeps the store's slot. -/
theorem on_goldfish_vote_checked_s' (E : Env V) (c : Store V) (u : GoldfishVote V) :
    (on_goldfish_vote_checked E c u).s = c.s := by
  unfold on_goldfish_vote_checked on_goldfish_vote
  split_ifs <;> rfl

end DecoupledConsensusModel.Sts
