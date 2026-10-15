import Proofs.Vocabulary.Execution.W4FKChainAdvanceFold
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Finality advance and the tick stages

The invariant that every held body's derived finalized block is an ancestor of the store's finalized
block, and the first three stages of a tick as sets of outcomes, stated over a model
`M : Record.Model V`. The last section relates each definition to its counterpart at
`Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Protocol (derive_named)

/-- Every held named body's derived finalized block is an ancestor of the store's finalized block,
    or that block itself. -/
def Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance (M : Record.Model V) (S : Setup V) (st : M.NS) : Prop :=
  ∀ D ∈ st.bodies, Block.Preceq (M.derive_named S.E S.cfg D).F st.core.F

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Protocol (derive_named)

/-- At the proposal instant of a slot after genesis whose proposer is `nd`, the outcomes of `nd`'s
    proposal duty on `st` with its clock set to `t`; otherwise `st` with its clock set to `t` as the
    one outcome. -/
def Vocabulary.Proofs.HealingSurface.tickStage1 (M : Record.Model V) (S : Setup V) (gc : M.Contract) (nd : Protocol.Node V)
    (st : M.NS) (t : Time) : DC.NDRE M.NS :=
  if 0 < S.E.slotOf t ∧ t = M.proposal_time S.E (S.E.slotOf t) ∧
      S.E.proposer (S.E.slotOf t) = nd.val_index then do
    let out ← M.duties_propose_block_with gc S.E S.hc S.cfg nd (M.ns_setClock S.E st t)
    pure out.1
  else pure (M.ns_setClock S.E st t)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Protocol (derive_named)

/-- For an outcome `st₁` of `tickStage1`, at the vote instant of a slot after genesis the outcomes
    of `nd`'s Goldfish vote duty on `st₁`; otherwise `st₁`. -/
def Vocabulary.Proofs.HealingSurface.tickStage2 (M : Record.Model V) (S : Setup V) (gc : M.Contract) (nd : Protocol.Node V)
    (st : M.NS) (t : Time) : DC.NDRE M.NS := do
  let st₁ ← Restated.Vocabulary.Proofs.HealingSurface.tickStage1 M S gc nd st t
  if 0 < S.E.slotOf t ∧ t = M.vote_time S.E (S.E.slotOf t) then do
    let out ← M.duties_goldfish_vote_with gc S.E S.hc nd st₁
    pure out.1
  else pure st₁

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Protocol (derive_named)

/-- For an outcome `st₂` of `tickStage2`, at the support cutoff of a slot after genesis the outcomes
    of the confirmation duty for the previous slot on `st₂`; otherwise `st₂`. -/
def Vocabulary.Proofs.HealingSurface.tickStage3 (M : Record.Model V) (S : Setup V) (gc : M.Contract) (nd : Protocol.Node V)
    (st : M.NS) (t : Time) : DC.NDRE M.NS := do
  let st₂ ← Restated.Vocabulary.Proofs.HealingSurface.tickStage2 M S gc nd st t
  if 0 < S.E.slotOf t ∧ t = M.support_cutoff S.E (S.E.slotOf t) then
    M.duties_update_confirmation_with gc S.E S.hc st₂ (S.E.slotOf t - 1)
  else pure st₂

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Protocol (derive_named)

/-- At `Record.Model.vocabulary`, the restated `NamedFinalityAdvance` holds exactly when
    `DecoupledConsensusModel.Proofs.HealingSurface.NamedFinalityAdvance` does. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance_vocabulary_eq (S : Setup V) (st : Protocol.NamedStore V) :
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.NamedFinalityAdvance (V := V) S st ↔ Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance (V := V) Record.Model.vocabulary S st :=
  Iff.rfl

/-- At `Record.Model.vocabulary`, the restated `tickStage1` is the one outcome
    `DecoupledConsensusModel.Proofs.HealingSurface.tickStage1` computes. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.tickStage1_vocabulary_eq (S : Setup V) (gc : Protocol.GradeContract V) (nd : Protocol.Node V) (st : Protocol.NamedStore V) (t : Time) :
    Restated.Vocabulary.Proofs.HealingSurface.tickStage1 (V := V) Record.Model.vocabulary S gc nd st t =
      pure (_root_.DecoupledConsensusModel.Proofs.HealingSurface.tickStage1 (V := V) S gc nd st t) := by
  unfold Restated.Vocabulary.Proofs.HealingSurface.tickStage1
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.tickStage1
  simp only [Record.Model.vocabulary, pure_bind]
  split_ifs <;> rfl

/-- At `Record.Model.vocabulary`, the restated `tickStage2` is the one outcome
    `DecoupledConsensusModel.Proofs.HealingSurface.tickStage2` computes. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.tickStage2_vocabulary_eq (S : Setup V) (gc : Protocol.GradeContract V) (nd : Protocol.Node V) (st : Protocol.NamedStore V) (t : Time) :
    Restated.Vocabulary.Proofs.HealingSurface.tickStage2 (V := V) Record.Model.vocabulary S gc nd st t =
      pure (_root_.DecoupledConsensusModel.Proofs.HealingSurface.tickStage2 (V := V) S gc nd st t) := by
  unfold Restated.Vocabulary.Proofs.HealingSurface.tickStage2
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.tickStage2
  rw [Restated.Vocabulary.Proofs.HealingSurface.tickStage1_vocabulary_eq]
  simp only [Record.Model.vocabulary, pure_bind]
  split_ifs <;> rfl

/-- At `Record.Model.vocabulary`, the restated `tickStage3` is the one outcome
    `DecoupledConsensusModel.Proofs.HealingSurface.tickStage3` computes. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.tickStage3_vocabulary_eq (S : Setup V) (gc : Protocol.GradeContract V) (nd : Protocol.Node V) (st : Protocol.NamedStore V) (t : Time) :
    Restated.Vocabulary.Proofs.HealingSurface.tickStage3 (V := V) Record.Model.vocabulary S gc nd st t =
      pure (_root_.DecoupledConsensusModel.Proofs.HealingSurface.tickStage3 (V := V) S gc nd st t) := by
  unfold Restated.Vocabulary.Proofs.HealingSurface.tickStage3
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.tickStage3
  rw [Restated.Vocabulary.Proofs.HealingSurface.tickStage2_vocabulary_eq]
  simp only [Record.Model.vocabulary, pure_bind]
  split_ifs <;> rfl

end

end DecoupledConsensusModel.Sts.Restated
