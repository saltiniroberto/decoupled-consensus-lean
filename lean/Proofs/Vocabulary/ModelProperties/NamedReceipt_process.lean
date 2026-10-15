module
public import Model.Vocabulary.Execution.Node

@[expose] public section

/-!
# Facts about `Execution.NamedReceipt.process`

How a named store processes a delivered object, one fact per kind of object.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Processing a block gives the store `on_block_with` returns, carried rows admitted. -/
theorem process_block (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    NamedReceipt.process S st (.block B) =
      Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B := rfl

/-- Processing a Goldfish vote replaces the core store with the one the checked vote handler returns
    and keeps the rest. -/
theorem process_gfVote (S : Setup V) (st : Protocol.NamedStore V) (u : GoldfishVote V) :
    NamedReceipt.process S st (.gfVote u) =
      { st with core := Protocol.on_goldfish_vote_checked S.E st.core u } := rfl

/-- Processing an attestation gives the store the row admission returns. -/
theorem process_attest (S : Setup V) (st : Protocol.NamedStore V) (a : NamedAttestation V) :
    NamedReceipt.process S st (.attest a) = Protocol.NamedAdmission.admit_row S.hc st a := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
