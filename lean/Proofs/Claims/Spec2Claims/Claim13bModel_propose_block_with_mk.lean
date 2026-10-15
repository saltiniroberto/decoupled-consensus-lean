module
public import Proofs.Claims.ModelIrreducible
public import Proofs.Vocabulary.Protocol.Duties.Proposals.Actions

@[expose] public section

/-!
# Facts about `NamedDuties.propose_block_with`, as a module file

Lemmas that unfold the named proposal duty.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedReceipt.process
  DecoupledConsensusModel.Protocol.NamedDuties.propose_block_with
  DecoupledConsensusModel.Protocol.with_proposal_input

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The named proposal duty either changes nothing and emits nothing, or runs the block receipt on
    the block it emits. -/
theorem named_propose_cases (S : Setup V) (gc : GradeContract V) (nd : Node V)
    (st : NamedStore V) :
    NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st = (st, none) ∨
      ∃ B : NamedBlock V, NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st
        = (NamedReceipt.process S st (.block B), some B) := by
  unfold NamedDuties.propose_block_with
  split
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

/-- A block the named proposal duty emits names the duty's own validator as its proposer. -/
theorem proposer_of_propose_block_with (gc : GradeContract V) (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (nd : Node V) (st : NamedStore V) (B : NamedBlock V)
    (h : (NamedDuties.propose_block_with gc E hc cfg nd st).2 = some B) :
    B.proposer? = some nd.val_index := by
  cases hp : NamedActions.proposal_with gc .poolAndCarried E hc nd st with
  | none =>
      rw [NamedDuties.propose_block_with, hp] at h
      exact absurd h (by simp)
  | some B' =>
      have hBB : B' = B := by
        rw [NamedDuties.propose_block_with, hp] at h
        exact Option.some.inj h
      subst hBB
      exact (Proofs.NamedActions.proposal_payload gc .poolAndCarried E hc nd st B' hp).2.2.2.2.2.2.2

end DecoupledConsensusModel.Sts
