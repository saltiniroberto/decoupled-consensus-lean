module

public import Model.Vocabulary.Protocol.Duties.Proposals
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.NamedActions.round_action_with`: the height pair it signs

The named round action builds the attestation input with `Protocol.with_attestation_input` and hands
it to the signing client `Protocol.NamedRecord.create`, which encodes the height pair of its row
from the input's height fields with `Protocol.NamedRecord.encodeHeight`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.root
  DecoupledConsensusModel.Protocol.HealConfig.round_of
  DecoupledConsensusModel.Protocol.NamedActions.creatorInput
  DecoupledConsensusModel.Protocol.NamedActions.round_action_with
  DecoupledConsensusModel.Protocol.NamedRecord.create
  DecoupledConsensusModel.Protocol.NamedRecord.encodeHeight
  DecoupledConsensusModel.Protocol.NamedRecord.encodeRow
  DecoupledConsensusModel.Protocol.NamedRecord.legacyCreate
  DecoupledConsensusModel.Protocol.create_attestation
  DecoupledConsensusModel.Protocol.fg_source_with DecoupledConsensusModel.Protocol.finality_pair
  DecoupledConsensusModel.Protocol.get_fg_vote_with
  DecoupledConsensusModel.Protocol.get_sg_vote_with
  DecoupledConsensusModel.Protocol.grade2_block_with DecoupledConsensusModel.Protocol.height_pair
  DecoupledConsensusModel.Protocol.with_attestation_input

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Sts

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The height pair of the row the named round action returns at the healing view `st` is the
    encoding, by `Protocol.NamedRecord.encodeHeight`, of the height fields of the attestation input
    built at `st` together with some height pair the signing client decides. -/
theorem round_action_with_height_pair_input (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.HealingStore V)
    (record : Protocol.NamedRecord) :
    ∃ pair : HeightPair,
      (Protocol.NamedActions.round_action_with contract E hc nd st record).2.height_pair =
        Protocol.NamedRecord.encodeHeight
          (Protocol.with_attestation_input contract E hc nd st id).fields pair :=
  ⟨_, rfl⟩

end DecoupledConsensusModel.Sts

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the contract's read at the store `st`, for the round of `st`'s slot, offers no grade-2
    candidate, then the attestation the named round action signs at `st` has the empty height pair. -/
theorem round_action_with_height_pair_of_Q2_none (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.HealingStore V)
    (record : Protocol.NamedRecord)
    (h : (contract.read E hc st (hc.round_of st.s)).Q2 = none) :
    (Protocol.NamedActions.round_action_with contract E hc nd st record).2.height_pair =
      NamedHeightPair.empty := by
  have he : ∀ pair : HeightPair,
      Protocol.NamedRecord.encodeHeight none pair = NamedHeightPair.empty := by
    intro pair
    cases pair <;> rfl
  unfold Protocol.NamedActions.round_action_with Protocol.with_attestation_input
    Protocol.NamedRecord.create Protocol.NamedRecord.encodeRow Protocol.NamedActions.creatorInput
    Protocol.get_fg_vote_with Protocol.grade2_block_with Protocol.fg_source_with
  simp only [h, Option.map_none]
  exact he _

end DecoupledConsensusModel.Sts
