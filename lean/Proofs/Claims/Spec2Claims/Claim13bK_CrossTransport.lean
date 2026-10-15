import Proofs.Claims.Spec2Claims.Claim13bK_GradeOldHeads
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13bModel_RootInjectiveBelow
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_round_votes
import Proofs.Claims.Spec2Claims.Claim13bModel_on_sg_vote
import Proofs.Claims.Spec2Claims.Claim13bModel_early
import Proofs.Claims.Spec2Claims.Claim13bModel_late
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_occurrenceBefore
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAttestation_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_rawInputs
import Proofs.Claims.Spec2Claims.Claim13bModel_readyView
import Proofs.Claims.Spec2Claims.Claim13bModel_rawView
import Proofs.Claims.Spec2Claims.Claim13bModel_localCovers
import Proofs.Claims.Spec2Claims.Claim13bModel_interpretedInputs
import Proofs.Claims.Spec2Claims.Claim13bModel_bodyReady
import Proofs.Claims.Spec2Claims.Claim13bModel_token
import Proofs.Claims.Spec2Claims.Claim13bModel_stampedBefore
import Proofs.Claims.Spec2Claims.Claim13bModel_positive
import Proofs.Claims.Spec2Claims.Claim13bModel_opposing
import Proofs.Claims.Spec2Claims.Claim13bModel_Supports
import Proofs.Claims.Spec2Claims.Claim13bModel_Opposes
import Proofs.Claims.Spec2Claims.Claim13bModel_CleanFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeBool
import Proofs.Claims.Spec2Claims.Claim13bModel_round_of
import Proofs.Claims.Spec2Claims.Claim13bModel_a
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedNode_tick
import Proofs.Vocabulary.ModelProperties.NamedNode_process
import Proofs.Vocabulary.ModelProperties.propose_block_with
import Proofs.Vocabulary.ModelProperties.NamedReceipt_process
import Proofs.Vocabulary.ModelProperties.NamedStore_setClock

/-!
# The stamp of a body entering a store

A block that the receipt of an object, or a tick, adds to a node state's bodies is stamped with the
store's clock before the receipt, or with the tick's instant.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom EquivocationAt)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The stamp a store writes when a body enters it -/

local macro "pcsg% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Store.PublicCutSG)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedPublicCutSG ++ n.getId)))

local macro "pcb% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.PublicCutBody)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedPublicCutBody ++ n.getId)))

local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If the receipt of `o` puts the named block `B` among a node state's bodies, where it was not
    before, then the stamp of `B`'s erasure after the receipt is the store's clock before it. -/
theorem node_process_body_stamp (S' : Setup V) (n : NamedNodeState V) (o : NamedObject V)
    (B : NamedBlock V) (h0 : B ∉ n.st.bodies)
    (h1 : B ∈ (NamedNode.process S' n o).st.bodies) :
    (NamedNode.process S' n o).st.core.timestamp_block B.erase
      = some ((n.st.core.t : Int) : Stamp) := by
  rw [Proofs.ModelProperties.process_st] at h1 ⊢
  cases o with
  | block B' =>
      rw [Proofs.ModelProperties.process_block] at h1 ⊢
      rcases on_block_with_bodies_upper .alsoCarried S'.E S'.hc S'.cfg n.st B' B h1 with h | h
      · exact absurd h h0
      · subst h
        exact (pcb% block_new_body_stamp) S' n.st B h0 h1
  | gfVote u =>
      rw [Proofs.ModelProperties.process_gfVote] at h1
      exact absurd h1 h0
  | attest inc =>
      rw [Proofs.ModelProperties.process_attest] at h1
      rw [Proofs.NamedAdmission.admit_row_bodies] at h1
      exact absurd h1 h0

/-- If the tick at `t` puts the named block `B` among a node state's bodies, where it was not
    before, then the stamp of `B`'s erasure after the tick is `t`. -/
theorem node_tick_body_stamp (S' : Setup V) (v : V) (n : NamedNodeState V) (t : Int)
    (B : NamedBlock V) (h0 : B ∉ n.st.bodies)
    (h1 : B ∈ (NamedNode.tick S' v n t).1.st.bodies) :
    (NamedNode.tick S' v n t).1.st.core.timestamp_block B.erase = some (t : Stamp) := by
  obtain ⟨gc, hgc1⟩ : ∃ gc : Protocol.GradeContract V,
      (NamedNode.tick S' v n t).1.st
          = (Protocol.NamedTick.tick gc S'.E S'.hc S'.cfg (S'.node v) n.st n.record t).1 :=
    ⟨_, namedNode_tick_st S' v n t⟩
  rw [hgc1] at h1 ⊢
  obtain ⟨hb, hs⟩ := (pcb% tick_proposal_stage_fields) gc S' (S'.node v) n.st n.record t
  rw [hb] at h1
  rw [hs]
  have h0' : B ∉ (Protocol.NamedStore.setClock S'.E n.st t).bodies := by
    rw [Proofs.ModelProperties.setClock_bodies]; exact h0
  by_cases hdue : 0 < S'.E.slotOf t ∧ t = Protocol.proposal_time S'.E (S'.E.slotOf t) ∧
      S'.E.proposer (S'.E.slotOf t) = (S'.node v).val_index
  · rw [if_pos hdue] at h1 ⊢
    cases hp : Protocol.NamedActions.proposal_with gc .poolAndCarried S'.E S'.hc (S'.node v)
        (Protocol.NamedStore.setClock S'.E n.st t) with
    | none =>
        rw [Proofs.ModelProperties.propose_block_with_fst_of_none _ _ _ _ _ _ hp] at h1
        exact absurd h1 h0'
    | some B' =>
        rw [Proofs.ModelProperties.propose_block_with_fst_of_some _ _ _ _ _ _ hp] at h1 ⊢
        rcases on_block_with_bodies_upper .alsoCarried S'.E S'.hc S'.cfg
            (Protocol.NamedStore.setClock S'.E n.st t) B' B h1 with h | h
        · exact absurd h h0'
        · subst h
          have hst := (pcb% block_new_body_stamp) S' (Protocol.NamedStore.setClock S'.E n.st t) B h0' h1
          rw [Proofs.ModelProperties.setClock_core_t] at hst
          exact hst
  · rw [if_neg hdue] at h1
    exact absurd h1 h0'

section

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

end

end DecoupledConsensusModel.Sts
