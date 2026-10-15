module
public import Model.Vocabulary.Protocol.Handlers
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.on_goldfish_vote_checked`: the committee test

The checked Goldfish-vote receipt drops a vote whose signer is outside its slot committee and
otherwise runs `Protocol.on_goldfish_vote`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.on_goldfish_vote_checked
  DecoupledConsensusModel.Protocol.on_goldfish_vote

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the signer of `u` is not in the committee of `u`'s slot, the checked Goldfish receipt of `u`
    returns the store it was given. -/
theorem on_goldfish_vote_checked_of_not_mem_committee (E : Env V) (st : Protocol.Store V)
    (u : GoldfishVote V) (h : u.val_index ∉ E.committee u.slot) :
    Protocol.on_goldfish_vote_checked E st u = st := by
  unfold Protocol.on_goldfish_vote_checked
  rw [if_pos h]

end DecoupledConsensusModel.Sts
