module
public import Proofs.Vocabulary.ModelProperties.NamedStore_process_block_core
public import Proofs.Vocabulary.ModelProperties.NamedStore_commitBlock
public import Proofs.Vocabulary.ModelProperties.on_block_checked_using
public import Proofs.Vocabulary.ModelProperties.Block_parent
public import Proofs.Vocabulary.ModelProperties.on_block_using
public import Proofs.Vocabulary.ModelProperties.update_finality
public import Proofs.Vocabulary.Protocol.ChainState.W4FKChainCheckpointAlgebra
public import Proofs.Vocabulary.Protocol.ChainState.HeightRegimeNamedBaseDeadline
public import Proofs.Vocabulary.Protocol.Duties.Inputs.RecoveryInitialSourceNamedRunHistory
public import Proofs.Vocabulary.Execution.RecoveryInitialSourceNamedActionHistory
public import Proofs.Vocabulary.Protocol.ForkChoice.Views.WeakBootstrapJoin
public import Proofs.Vocabulary.Execution.CommonAncestorBound
public import Proofs.Vocabulary.ModelProperties.propose_block_with
public import Proofs.Vocabulary.ModelProperties.NamedReceipt_process
public import Proofs.Vocabulary.ModelProperties.Block_Preceq
public import Proofs.Vocabulary.ModelProperties.NamedNode_process
public import Proofs.Vocabulary.ModelProperties.NamedNode_tick
public import Proofs.Vocabulary.ModelProperties.NamedAdmission_on_block_with

@[expose] public section

/-!
# Finality advance over the named transitions

`NamedFinalityAdvance` says that every held named body's derived finalized block is an ancestor of
the store's finalized block. This file proves how the named transitions and the stages of a tick
keep it.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every held named body's derived finalized block is an ancestor of the store's finalized block. -/
def NamedFinalityAdvance (S : Setup V) (st : Protocol.NamedStore V) : Prop :=
  ∀ D ∈ st.bodies, Block.Preceq (derive_named S.E S.cfg D).F st.core.F

/-! ## Transitions that keep the bodies -/

theorem advance_of_bodies_eq_of_F
    (S : Setup V) {st st' : Protocol.NamedStore V}
    (hbodies : st'.bodies = st.bodies)
    (hF : Block.Preceq st.core.F st'.core.F)
    (hadv : NamedFinalityAdvance S st) : NamedFinalityAdvance S st' := by
  intro D hD
  rw [hbodies] at hD
  exact Block.preceq_trans (hadv D hD) hF

theorem advance_admit_row (S : Setup V) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) (hadv : NamedFinalityAdvance S st) :
    NamedFinalityAdvance S (Protocol.NamedAdmission.admit_row S.hc st row) := by
  refine advance_of_bodies_eq_of_F S (NamedAdmission.admit_row_bodies S.hc st row) ?_ hadv
  rw [NamedAdmission.admit_row_core, on_sg_vote_F]
  exact Block.preceq_self _

/-! ## The block transition -/

theorem admit_rows_bodies_eq (S : Setup V) (rows : List (NamedAttestation V)) :
    ∀ st : Protocol.NamedStore V,
      (Protocol.NamedAdmission.admit_rows S.hc st rows).bodies = st.bodies := by
  induction rows with
  | nil => intro st; rfl
  | cons row rows ih =>
      intro st
      show (Protocol.NamedAdmission.admit_rows S.hc
        (Protocol.NamedAdmission.admit_row S.hc st row) rows).bodies = st.bodies
      rw [ih, NamedAdmission.admit_row_bodies]

theorem admit_carried_bodies_eq (S : Setup V) (admission : Protocol.CarriedAdmission)
    (before after : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.admit_carried admission S.hc before after B).bodies =
      after.bodies := by
  cases admission with
  | alsoCarried =>
      simp only [Protocol.NamedAdmission.admit_carried]
      split_ifs
      · exact admit_rows_bodies_eq S B.attestations after
      · rfl

theorem on_block_with_bodies_eq (S : Setup V) (admission : Protocol.CarriedAdmission)
    (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with admission S.E S.hc S.cfg st B).bodies =
      (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).bodies := by
  simp only [Protocol.NamedAdmission.on_block_with]
  exact admit_carried_bodies_eq S admission st _ B

/-! ## The remaining duties -/

theorem advance_goldfish_vote_with (S : Setup V) (gc : Protocol.GradeContract V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (hadv : NamedFinalityAdvance S st) :
    NamedFinalityAdvance S
      (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1 := by
  refine advance_of_bodies_eq_of_F S (st := st) rfl ?_ hadv
  rw [NamedDuties.goldfish_vote_core]
  simp only [Protocol.goldfish_vote_with]
  split_ifs <;>
    simp only [on_goldfish_vote_checked_F] <;> exact Block.preceq_self _

theorem advance_update_confirmation_with (S : Setup V) (gc : Protocol.GradeContract V)
    (st : Protocol.NamedStore V) (u : Slot)
    (hadv : NamedFinalityAdvance S st) :
    NamedFinalityAdvance S
      (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st u) := by
  refine advance_of_bodies_eq_of_F S (st := st) rfl ?_ hadv
  show Block.Preceq st.core.F (Protocol.update_confirmation_with gc S.E S.hc st.core u).F
  have hF : (Protocol.update_confirmation_with gc S.E S.hc st.core u).F = st.core.F := rfl
  rw [hF]
  exact Block.preceq_self _

theorem advance_attest_with (S : Setup V) (gc : Protocol.GradeContract V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord)
    (hadv : NamedFinalityAdvance S st) :
    NamedFinalityAdvance S
      (Protocol.NamedDuties.attest_with gc S.E S.hc nd st record).1 :=
  advance_admit_row S st _ hadv


/-! ## The tick, stage by stage -/

def tickStage1 (S : Setup V) (gc : Protocol.GradeContract V) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (t : Time) : Protocol.NamedStore V :=
  if 0 < S.E.slotOf t ∧ t = Protocol.proposal_time S.E (S.E.slotOf t) ∧
      S.E.proposer (S.E.slotOf t) = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd
      (Protocol.NamedStore.setClock S.E st t)).1
  else Protocol.NamedStore.setClock S.E st t

def tickStage2 (S : Setup V) (gc : Protocol.GradeContract V) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (t : Time) : Protocol.NamedStore V :=
  if 0 < S.E.slotOf t ∧ t = Protocol.vote_time S.E (S.E.slotOf t) then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd
      (tickStage1 S gc nd st t)).1
  else tickStage1 S gc nd st t

def tickStage3 (S : Setup V) (gc : Protocol.GradeContract V) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (t : Time) : Protocol.NamedStore V :=
  if 0 < S.E.slotOf t ∧ t = Protocol.support_cutoff S.E (S.E.slotOf t) then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc
      (tickStage2 S gc nd st t) (S.E.slotOf t - 1)
  else tickStage2 S gc nd st t

theorem tick_eq_stage3 (S : Setup V) (gc : Protocol.GradeContract V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) :
    (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 =
      (if t = S.hc.a S.E.Δ (S.hc.round_of (tickStage3 S gc nd st t).core.s) ∧
          nd.awake (S.hc.round_of (tickStage3 S gc nd st t).core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc nd
          (tickStage3 S gc nd st t) record).1
      else tickStage3 S gc nd st t) := by
  rw [NamedTick.tick_computed_duties]
  dsimp only [tickStage3, tickStage2, tickStage1]
  split_ifs <;> rfl

theorem advance_tick_of_stage1 (S : Setup V) (gc : Protocol.GradeContract V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time)
    (hadv1 : NamedFinalityAdvance S (tickStage1 S gc nd st t)) :
    NamedFinalityAdvance S
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 := by
  have hadv2 : NamedFinalityAdvance S (tickStage2 S gc nd st t) := by
    dsimp only [tickStage2]
    split_ifs
    · exact advance_goldfish_vote_with S gc nd _ hadv1
    · exact hadv1
  have hadv3 : NamedFinalityAdvance S (tickStage3 S gc nd st t) := by
    dsimp only [tickStage3]
    split_ifs
    · exact advance_update_confirmation_with S gc _ _ hadv2
    · exact hadv2
  rw [tick_eq_stage3]
  split_ifs
  · exact advance_attest_with S gc nd _ record hadv3
  · exact hadv3

#print axioms advance_tick_of_stage1

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
