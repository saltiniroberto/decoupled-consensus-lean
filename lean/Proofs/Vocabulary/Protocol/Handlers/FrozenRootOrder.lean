module
public import Proofs.Vocabulary.Protocol.Handlers.JustificationCarrier
public import Proofs.Vocabulary.ModelProperties.NamedNode_initial
public import Proofs.Vocabulary.ModelProperties.NamedStore_initial
public import Proofs.Vocabulary.ModelProperties.Block_Preceq
public import Proofs.Vocabulary.ModelProperties.get_fg_root
public import Proofs.Vocabulary.ModelProperties.viable_tree
public import Proofs.Vocabulary.ModelProperties.Store_toHealing
public import Proofs.Vocabulary.Execution.Runtime
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedStableChainOutageInternal
public import Model.Vocabulary.Execution.Node
public import Model.Vocabulary.Execution.Objects
public import Model.Vocabulary.Execution.Run
public import Model.Vocabulary.Execution.Setup

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## `F ⪯ J` at every named state -/

/-- `on_block_using` preserves `F ⪯ J`. -/
theorem frozen_on_block_using_preceq (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V)
    (h : Block.Preceq st.F st.J) :
    Block.Preceq (Protocol.on_block_using E st B buildState).F
      (Protocol.on_block_using E st B buildState).J := by
  simp only [Protocol.on_block_using]
  split_ifs <;> first
    | exact h
    | (apply update_finality_preceq
       have hCE := coreEq_foldl_on_goldfish_vote_checked E B.gf_votes
         ({ st with
             σ := fun C => if C = B then buildState (st.σ B.parent) else st.σ C
             T := insert B st.T
             timestamp_block := fun C =>
               if C = B then some (st.t : Stamp) else st.timestamp_block C } : Protocol.Store V)
       rw [hCE.F_eq, hCE.J_eq]
       exact h)

/-- `process_block_core` preserves `F ⪯ J`. -/
theorem frozen_process_block_core_preceq (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (h : Block.Preceq st.core.F st.core.J) :
    Block.Preceq (Protocol.NamedStore.process_block_core E hc cfg st B).core.F
      (Protocol.NamedStore.process_block_core E hc cfg st B).core.J := by
  simp only [Protocol.NamedStore.process_block_core]
  split_ifs <;> first
    | exact h
    | (rw [NamedStore.commit_core]
       simp only [Protocol.on_block_checked_using]
       split_ifs <;> first
         | exact frozen_on_block_using_preceq E st.core B.erase _ h
         | exact h)

/-- `admit_row` preserves `F ⪯ J`. -/
theorem frozen_admit_row_preceq (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) (h : Block.Preceq st.core.F st.core.J) :
    Block.Preceq (Protocol.NamedAdmission.admit_row hc st row).core.F
      (Protocol.NamedAdmission.admit_row hc st row).core.J := by
  simp only [Protocol.NamedAdmission.admit_row]
  have hCE := coreEq_on_sg_vote hc st.core row.erase
  split_ifs <;> (rw [hCE.F_eq, hCE.J_eq]; exact h)

theorem frozen_admit_rows_preceq (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (h : Block.Preceq st.core.F st.core.J) :
    Block.Preceq (Protocol.NamedAdmission.admit_rows hc st rows).core.F
      (Protocol.NamedAdmission.admit_rows hc st rows).core.J := by
  unfold Protocol.NamedAdmission.admit_rows
  induction rows generalizing st with
  | nil => exact h
  | cons row rows ih => exact ih _ (frozen_admit_row_preceq hc st row h)

theorem frozen_admit_carried_preceq (admission : Protocol.CarriedAdmission)
    (hc : Protocol.HealConfig) (before after : Protocol.NamedStore V) (B : NamedBlock V)
    (h : Block.Preceq after.core.F after.core.J) :
    Block.Preceq (Protocol.NamedAdmission.admit_carried admission hc before after B).core.F
      (Protocol.NamedAdmission.admit_carried admission hc before after B).core.J := by
  cases admission with
  | alsoCarried =>
    unfold Protocol.NamedAdmission.admit_carried
    split_ifs
    · exact frozen_admit_rows_preceq hc after B.attestations h
    · exact h

theorem frozen_on_block_with_preceq (admission : Protocol.CarriedAdmission)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) (h : Block.Preceq st.core.F st.core.J) :
    Block.Preceq (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).core.F
      (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).core.J :=
  frozen_admit_carried_preceq admission hc st _ B (frozen_process_block_core_preceq E hc cfg st B h)

/-- `goldfish_vote_with` preserves `F ⪯ J`, for every grade contract. -/
theorem frozen_goldfish_vote_with_preceq (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (h : Block.Preceq st.core.F st.core.J) :
    Block.Preceq (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1.core.F
      (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1.core.J := by
  show Block.Preceq (Protocol.goldfish_vote_with gc E hc nd st.core).1.F
    (Protocol.goldfish_vote_with gc E hc nd st.core).1.J
  simp only [Protocol.goldfish_vote_with]
  split_ifs <;> first
    | exact h
    | (rw [(coreEq_on_goldfish_vote_checked E st.core _).F_eq,
        (coreEq_on_goldfish_vote_checked E st.core _).J_eq]
       exact h)

/-- `update_confirmation_with` preserves `F ⪯ J`, for every grade contract. -/
theorem frozen_update_confirmation_with_preceq (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (s : Slot)
    (h : Block.Preceq st.core.F st.core.J) :
    Block.Preceq (Protocol.NamedDuties.update_confirmation_with gc E hc st s).core.F
      (Protocol.NamedDuties.update_confirmation_with gc E hc st s).core.J :=
  h

/-- `attest_with` preserves `F ⪯ J`. -/
theorem frozen_attest_with_preceq (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (h : Block.Preceq st.core.F st.core.J) :
    Block.Preceq (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core.F
      (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core.J := by
  unfold Protocol.NamedDuties.attest_with
  exact frozen_admit_row_preceq hc st _ h

/-- `propose_block_with` preserves `F ⪯ J`. -/
theorem frozen_propose_block_with_preceq (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (h : Block.Preceq st.core.F st.core.J) :
    Block.Preceq (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1.core.F
      (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1.core.J := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact h
  · exact frozen_on_block_with_preceq .alsoCarried E hc cfg st _ h

/-- A named tick under the frame contract preserves `F ⪯ J`. -/
theorem frozen_named_tick_preceq (S : Setup V) (cache : DecoupledConsensusModel.Protocol.Cache V)
    (v : V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (h : Block.Preceq st.core.F st.core.J) :
    Block.Preceq
      (Protocol.NamedTick.tick (DecoupledConsensusModel.Protocol.frameContract cache)
        S.E S.hc S.cfg (S.node v) st record t).1.core.F
      (Protocol.NamedTick.tick (DecoupledConsensusModel.Protocol.frameContract cache)
        S.E S.hc S.cfg (S.node v) st record t).1.core.J := by
  let gc := DecoupledConsensusModel.Protocol.frameContract cache
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧
      S.E.proposer s = (S.node v).val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node v) st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc (S.node v) st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have h0 : Block.Preceq st0.core.F st0.core.J := h
  have h1 : Block.Preceq st1.core.F st1.core.J := by
    dsimp only [st1]
    split_ifs
    · exact frozen_propose_block_with_preceq gc S.E S.hc S.cfg (S.node v) st0 h0
    · exact h0
  have h2 : Block.Preceq st2.core.F st2.core.J := by
    dsimp only [st2]
    split_ifs
    · exact frozen_goldfish_vote_with_preceq gc S.E S.hc (S.node v) st1 h1
    · exact h1
  have h3 : Block.Preceq st3.core.F st3.core.J := by
    dsimp only [st3]
    split_ifs
    · exact frozen_update_confirmation_with_preceq gc S.E S.hc st2 (s - 1) h2
    · exact h2
  have hstage : (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v) st record t).1 =
      if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          (S.node v).awake (S.hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node v) st3 record).1
      else st3 := by
    rw [NamedTick.tick_computed_duties]
    dsimp only
    rw [apply_ite (fun out : Protocol.NamedStore V × Protocol.NamedRecord ×
      List (NamedObject V) => out.1)]
  show Block.Preceq
    (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v) st record t).1.core.F
    (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v) st record t).1.core.J
  rw [hstage]
  split_ifs
  · exact frozen_attest_with_preceq gc S.E S.hc (S.node v) st3 record h3
  · exact h3

theorem frozen_tick_preceq (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time)
    (h : Block.Preceq n.st.core.F n.st.core.J) :
    Block.Preceq (NamedNode.tick S v n t).1.st.core.F (NamedNode.tick S v n t).1.st.core.J :=
  frozen_named_tick_preceq S _ v n.st n.record t h

/-- Processing a delivered named object preserves `F ⪯ J`. -/
theorem frozen_process_preceq (S : Setup V) (n : NamedNodeState V) (o : NamedObject V)
    (h : Block.Preceq n.st.core.F n.st.core.J) :
    Block.Preceq (NamedNode.process S n o).st.core.F (NamedNode.process S n o).st.core.J := by
  show Block.Preceq (NamedReceipt.process S n.st o).core.F
    (NamedReceipt.process S n.st o).core.J
  cases o with
  | block B => exact frozen_on_block_with_preceq .alsoCarried S.E S.hc S.cfg n.st B h
  | gfVote u =>
    show Block.Preceq (Protocol.on_goldfish_vote_checked S.E n.st.core u).F
      (Protocol.on_goldfish_vote_checked S.E n.st.core u).J
    have hCE := coreEq_on_goldfish_vote_checked S.E n.st.core u
    rw [hCE.F_eq, hCE.J_eq]
    exact h
  | attest a => exact frozen_admit_row_preceq S.hc n.st a h


end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
