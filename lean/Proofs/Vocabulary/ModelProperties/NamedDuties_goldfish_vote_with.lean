module
public import Model.Vocabulary.Protocol.Duties.Proposals

@[expose] public section

/-!
# Facts about `Protocol.NamedDuties.goldfish_vote_with`

The Goldfish vote duty over a named store, read through the vote it returns.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- When `nd`'s validator is in the committee of `st`'s slot `s`, the vote duty returns its vote at
    slot `s` for the root of the head the fork choice under `contract` computes over the voter's
    filtered tree and views at `s`, for slot `s − 1`. -/
theorem goldfish_vote_with_snd_of_mem_committee (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (hcom : nd.val_index ∈ E.committee st.core.s) :
    (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st).2 =
      some ⟨nd.val_index, st.core.s,
        (Protocol.get_head_in_tree_with_layer contract E hc st.core.toHealing
          (Protocol.voter_filtered_block_tree E st.core st.core.s)
          (Protocol.voter_view E st.core.toHealing.toFG.toSG.toGoldfishStore st.core.s)
          (Protocol.voter_support_view E st.core.toHealing.toFG.toSG.toGoldfishStore st.core.s)
          (st.core.s - 1)).root⟩ := by
  simp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with, if_pos hcom]
  rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
