module
public import Model.Vocabulary.Protocol.Duties.Inputs

@[expose] public section

/-!
# Facts about `Protocol.grade2_block_with`

The contract's grade-2 candidate for a round.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The grade-2 candidate under `contract` at `st` and `r` is that of the contract's grade read at
    `st` and `r`. -/
theorem grade2_block_with_eq_read_Q2 (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round) :
    Protocol.grade2_block_with contract E hc st r = (contract.read E hc st r).Q2 := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
