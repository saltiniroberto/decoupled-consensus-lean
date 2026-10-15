import Model.Vocabulary.Protocol.Duties.Proposals
import Proofs.Vocabulary.ModelProperties.NamedDuties_goldfish_vote_with
import Proofs.Claims.ModelIrreducible

/-!
# The vote the named Goldfish vote duty returns

The vote the named-store wrapper of the Goldfish vote duty, `NamedDuties.goldfish_vote_with`,
returns.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Env.committee
  DecoupledConsensusModel.Protocol.NamedDuties.goldfish_vote_with
  DecoupledConsensusModel.Protocol.goldfish_vote_with

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the Goldfish vote duty, run by `nd` on `st`, returns the vote `u`, then `nd`'s validator is
    in the committee of the slot `s` of `st`'s core store, and `u` is its vote at `s` for the root
    of the head the fork choice under `contract` returns at `st`'s healing view. -/
theorem namedDuties_goldfish_vote_with_snd_eq_some (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    {u : GoldfishVote V}
    (h : (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st).2 = some u) :
    nd.val_index ∈ E.committee st.core.s ∧
      u = ⟨nd.val_index, st.core.s,
        (Protocol.get_head_in_tree_with_layer contract E hc st.core.toHealing
          (Protocol.voter_filtered_block_tree E st.core st.core.s)
          (Protocol.voter_view E st.core.toHealing.toFG.toSG.toGoldfishStore st.core.s)
          (Protocol.voter_support_view E st.core.toHealing.toFG.toSG.toGoldfishStore st.core.s)
          (st.core.s - 1)).root⟩ := by
  by_cases hcom : nd.val_index ∈ E.committee st.core.s
  · rw [Proofs.ModelProperties.goldfish_vote_with_snd_of_mem_committee contract E hc nd st hcom]
      at h
    exact ⟨hcom, (Option.some.inj h).symm⟩
  · simp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with,
      if_neg hcom] at h
    exact absurd h (by simp)

end DecoupledConsensusModel.Sts
