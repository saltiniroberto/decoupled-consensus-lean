import Proofs.Vocabulary.Protocol.ChainState.ProposalBridge
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `propose_block_with`: the block the proposal duty returns

Lemmas that unfold the proposal duty `Protocol.NamedDuties.propose_block_with` and the receiver-side
test `Protocol.carried_attestations_admissible` on the block it returns.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.NamedAttestation.erase
  DecoupledConsensusModel.Protocol.NamedDuties.propose_block_with
  DecoupledConsensusModel.Protocol.Store.toHealing
  DecoupledConsensusModel.Protocol.with_proposal_input

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]


/-- A block `proposal_with` builds on the named store `st` includes only rows whose round is at most
    the round of the block's slot. -/
theorem proposal_with_carried_admissible_inclG2 (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    {B : NamedBlock V}
    (hB : Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st = some B) :
    Protocol.carried_attestations_admissible hc B.erase = true := by
  have hpay := Proofs.NamedActions.proposal_payload contract .poolAndCarried E hc nd st B hB
  have hslot : B.erase.slot = st.core.s := by
    rw [Proofs.NamedWire.erase_slot, hpay.2.2.1]; rfl
  rw [Protocol.carried_attestations_admissible, hslot, Proofs.NamedWire.erase_attestations]
  refine List.all_eq_true.mpr ?_
  intro a ha
  obtain ⟨row, hrow, hae⟩ := List.mem_map.mp ha
  rw [hpay.2.2.2.2.2.2.1] at hrow
  have hsel := Proofs.NamedProposalRows.mem_proposalRows B.parent _ row hrow
  have := Proofs.HealingSurface.selected_row_round_le hc st hsel.1
  rw [← hae]
  exact decide_eq_true this

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the proposal `proposal_with` makes at `st`, with the pool and included rows as the row
    source, is the block `B`, then the block the proposal duty returns at `st` is `B`. -/
theorem propose_block_with_snd_of_some (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) {B : NamedBlock V}
    (h : Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st = some B) :
    (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).2 = some B := by
  simp only [Protocol.NamedDuties.propose_block_with, h]

end DecoupledConsensusModel.Sts
