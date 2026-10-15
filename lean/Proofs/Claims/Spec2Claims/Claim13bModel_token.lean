module
public import Model.Vocabulary.Protocol.Grades
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.token`

Lemmas that unfold the token of an attestation: its round and the root it names as confirmed.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.token

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type}

/-- The round of the token of `y` is `y`'s round. -/
theorem token_round (y : Protocol.SGVote V) : (Protocol.token y).round = y.round := by
  unfold Protocol.token
  rfl

/-- The key of the token of `y` is the root `y` names as confirmed. -/
theorem token_key (y : Protocol.SGVote V) : (Protocol.token y).key = y.confirmed := by
  unfold Protocol.token
  rfl

end DecoupledConsensusModel.Sts
