module
public import Model.Vocabulary.Protocol.Duties.Inputs
public import Model.Vocabulary.Execution.Node
public import Proofs.Vocabulary.Protocol.Handlers.ConfirmationMembership

@[expose] public section

/-!
# Facts about the attestation input

Facts about `Protocol.with_attestation_input`, read field by field for the input itself (the
continuation `id`).
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The height-pair fields of the attestation input built at `st` are absent when the FG source
    chosen from the grade-2 block of `st`'s round is absent, and otherwise are the height, the
    height target's root and the justification flag of `st`'s chain state at that source. -/
theorem with_attestation_input_id_fields (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.HealingStore V) :
    (Protocol.with_attestation_input contract E hc nd st id).fields =
      (Protocol.fg_source_with contract E hc st (hc.round_of st.s)
        (Protocol.grade2_block_with contract E hc st (hc.round_of st.s))).map
        (fun q => ((st.σ q).h, (st.σ q).T_h.root, (st.σ q).nj)) := rfl

/-- The confirmed root of the attestation input built at `st` is the root of the SG vote the
    contract selects at `st`'s round, from that round's grade-2 block. -/
theorem with_attestation_input_id_confirmed (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.HealingStore V) :
    (Protocol.with_attestation_input contract E hc nd st id).confirmed =
      some (Protocol.get_sg_vote_with contract E hc st (hc.round_of st.s)
        (Protocol.grade2_block_with contract E hc st (hc.round_of st.s))).root := rfl

/-- If the named store `st` satisfies `NamedConfirmationMembership.Invariant`, the root that the
    attestation input built at `st` under the grade contract of `cache` confirms is the root of some
    block of `st`'s block tree. -/
theorem attestation_input_head_gradeContract (cache : DecoupledConsensusModel.Protocol.Cache V)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (h : NamedConfirmationMembership.Invariant E cfg st) :
    ∃ H ∈ st.core.T,
      (Protocol.attestation_input_with (Execution.NamedProfile.gradeContract cache)
        E hc nd st.core.toHealing).confirmed = some H.root :=
  NamedConfirmationMembership.attestation_input_head cache E hc cfg nd st h

end DecoupledConsensusModel.Proofs.ModelProperties

end
