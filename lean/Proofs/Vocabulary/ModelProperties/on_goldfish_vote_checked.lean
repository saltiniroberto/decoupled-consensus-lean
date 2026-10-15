module
public import Model.Vocabulary.Protocol.Handlers

@[expose] public section

/-!
# Facts about `Protocol.on_goldfish_vote_checked`

The Goldfish vote handler that drops a vote whose validator is not in its slot's committee and
otherwise calls `on_goldfish_vote`.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A vote whose validator is in its slot's committee goes to `on_goldfish_vote`. -/
theorem on_goldfish_vote_checked_of_mem_committee (E : Env V) (st : Protocol.Store V)
    (u : GoldfishVote V) (h : u.val_index ∈ E.committee u.slot) :
    Protocol.on_goldfish_vote_checked E st u = Protocol.on_goldfish_vote st u := by
  unfold Protocol.on_goldfish_vote_checked
  rw [if_neg (fun hcon => hcon h)]

end DecoupledConsensusModel.Proofs.ModelProperties

end
