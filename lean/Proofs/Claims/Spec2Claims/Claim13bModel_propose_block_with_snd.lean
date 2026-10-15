module
public import Model.Vocabulary.Protocol.Duties.Proposals
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.NamedDuties.propose_block_with`: the block it proposes

The proposal duty proposes the block the named proposal read `Protocol.NamedActions.proposal_with`
builds, when it builds one, and admits it to the store.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedDuties.propose_block_with

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the proposal duty under `contract` at the named store `st` proposes the block `B`, then
    `Protocol.NamedActions.proposal_with`, with the pool and the included rows as the row source,
    builds `B` at `st`. -/
theorem proposal_with_eq_of_propose_block_with_snd (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) {B : NamedBlock V}
    (h : (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).2 = some B) :
    Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st = some B := by
  unfold Protocol.NamedDuties.propose_block_with at h
  cases hp : Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st with
  | none => simp [hp] at h
  | some C =>
    rw [hp] at h
    exact h

end DecoupledConsensusModel.Sts
