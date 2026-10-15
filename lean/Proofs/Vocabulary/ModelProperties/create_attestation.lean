module
public import Model.Vocabulary.Protocol.ValidatorClient

@[expose] public section

/-!
# Facts about `Protocol.create_attestation`

The attestation a validator creates and the record it leaves.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type}

/-- The record `create_attestation` returns is `Λ` with the returned attestation recorded. -/
theorem create_attestation_fst (Λ : Protocol.Record) (val_index : V) (r : Round)
    (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool))
    (h_j : Height) (J : BlockId) (h_F : Height) :
    (Protocol.create_attestation Λ val_index r confirmed fields h_j J h_F).1 =
      Protocol.record_attestation Λ
        (Protocol.create_attestation Λ val_index r confirmed fields h_j J h_F).2 := rfl

/-- The finality pair of the attestation `create_attestation` returns is the finality pair `Λ` gives
    for `h_j`, `J` and `h_F`. -/
theorem create_attestation_snd_finality_pair (Λ : Protocol.Record) (val_index : V) (r : Round)
    (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool))
    (h_j : Height) (J : BlockId) (h_F : Height) :
    (Protocol.create_attestation Λ val_index r confirmed fields h_j J h_F).2.finality_pair =
      Protocol.finality_pair Λ h_j J h_F := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
