module
public import Model.Vocabulary.Protocol.Duties.Proposals

@[expose] public section

/-!
# Facts about the proposal duty

Facts about `Protocol.NamedDuties.propose_block_with`, one for each case of its `match` on the
proposal, so that a proof need not unfold it.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- With no proposal, the proposal duty returns the store `st` unchanged. -/
theorem propose_block_with_fst_of_none (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V)
    (h : Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st = none) :
    (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).1 = st := by
  simp only [Protocol.NamedDuties.propose_block_with, h]

/-- If the proposal duty proposes the block `B` at `st`, the store it returns is the store the block
    handler returns on `B`. -/
theorem propose_block_with_fst_of_some (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) {B : NamedBlock V}
    (h : Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st = some B) :
    (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).1 =
      Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st B := by
  simp only [Protocol.NamedDuties.propose_block_with, h]

/-- If the block the proposal duty returns at `st` is `B`, the duty returns the pair of the store
    the block handler returns on `B` and `B`. -/
theorem propose_block_with_eq_of_snd (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) {B : NamedBlock V}
    (h : (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).2 = some B) :
    Protocol.NamedDuties.propose_block_with contract E hc cfg nd st =
      (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st B, some B) := by
  unfold Protocol.NamedDuties.propose_block_with at h ⊢
  cases hp : Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st with
  | none => simp [hp] at h
  | some C =>
    obtain rfl : C = B := by simpa [hp] using h
    simp [hp]

end DecoupledConsensusModel.Proofs.ModelProperties

end
