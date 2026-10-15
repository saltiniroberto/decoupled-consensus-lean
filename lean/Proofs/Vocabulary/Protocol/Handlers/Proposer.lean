module
public import Proofs.Vocabulary.Protocol.ValidatorClient.BlockEmission
public import Proofs.Vocabulary.ModelProperties.NamedNode_initial
public import Proofs.Vocabulary.ModelProperties.NamedStore_initial
public import Proofs.Vocabulary.ModelProperties.NamedNode_process
public import Proofs.Vocabulary.ModelProperties.NamedReceipt_process
public import Proofs.Vocabulary.ModelProperties.NamedNode_tick
public import Proofs.Vocabulary.Objects.AdmissibleCore
import Proofs.Vocabulary.Execution.BridgesCore
import Proofs.Vocabulary.Execution.Runtime
import Proofs.Vocabulary.Protocol.Handlers.StoreBridge
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (Record)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## Proposers of held blocks -/


/-- Every block of the tree other than genesis has the proposer of its slot. -/
def ProposerOk (E : Env V) (st : Protocol.Store V) : Prop :=
  ∀ B ∈ st.T, B = Block.genesis ∨ B.proposer? = some (E.proposer B.slot)

/-- A step that keeps the tree preserves `ProposerOk`. -/
theorem proposerOk_of_T_eq {E : Env V} {st st' : Protocol.Store V}
    (hT : st'.T = st.T) (h : ProposerOk E st) : ProposerOk E st' := by
  intro B hB
  exact h B (by rwa [hT] at hB)

private theorem proposerOk_on_block_using (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : Protocol.ChainState V → Protocol.ChainState V)
    (h : ProposerOk E st) : ProposerOk E (Protocol.on_block_using E st B buildState) := by
  simp only [Protocol.on_block_using]
  split_ifs with h1 h2 h3
  · exact h
  · exact h
  · exact h
  · intro C hC
    rw [Proofs.update_finality_T, Proofs.foldl_on_goldfish_vote_checked_T E] at hC
    rcases Finset.mem_insert.mp hC with rfl | hmem
    · exact Or.inr (not_not.mp h3)
    · exact h C hmem
  · exact h

private theorem proposerOk_process_block_core (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (h : ProposerOk E st.core) :
    ProposerOk E (Protocol.NamedStore.process_block_core E hc cfg st B).core := by
  by_cases hp : B.parent ∈ st.bodies
  · rw [Protocol.NamedStore.process_block_core, if_neg (not_not.mpr hp), NamedStore.commit_core]
    dsimp only [Protocol.on_block_checked_using]
    split_ifs
    · exact proposerOk_on_block_using E st.core B.erase _ h
    · exact h
  · simpa only [Protocol.NamedStore.process_block_core, if_pos hp] using h

private theorem proposerOk_admit_row (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (a : NamedAttestation V) (h : ProposerOk E st.core) :
    ProposerOk E (Protocol.NamedAdmission.admit_row hc st a).core := by
  rw [NamedAdmission.admit_row_core]
  exact proposerOk_of_T_eq (on_sg_vote_T hc st.core a.erase) h

private theorem proposerOk_admit_rows (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (rows : List (NamedAttestation V))
    (h : ProposerOk E st.core) :
    ProposerOk E (Protocol.NamedAdmission.admit_rows hc st rows).core := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih => exact ih _ (proposerOk_admit_row E hc st a h)

private theorem proposerOk_admit_carried (E : Env V) (hc : Protocol.HealConfig)
    (admission : Protocol.CarriedAdmission) (before after : Protocol.NamedStore V)
    (B : NamedBlock V) (h : ProposerOk E after.core) :
    ProposerOk E (Protocol.NamedAdmission.admit_carried admission hc before after B).core := by
  cases admission with
  | alsoCarried =>
    dsimp only [Protocol.NamedAdmission.admit_carried]
    split_ifs
    · exact proposerOk_admit_rows E hc after B.attestations h
    · exact h

private theorem proposerOk_on_block_with (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (h : ProposerOk E st.core) :
    ProposerOk E (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st B).core :=
  proposerOk_admit_carried E hc .alsoCarried st _ B (proposerOk_process_block_core E hc cfg st B h)

private theorem proposerOk_propose_block_with (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (gc : Protocol.GradeContract V) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (h : ProposerOk E st.core) :
    ProposerOk E (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1.core := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact h
  · exact proposerOk_on_block_with E hc cfg st _ h

private theorem proposerOk_attest_with (E : Env V) (hc : Protocol.HealConfig)
    (gc : Protocol.GradeContract V) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (h : ProposerOk E st.core) :
    ProposerOk E (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core :=
  proposerOk_admit_row E hc st _ h

/-- A named tick preserves `ProposerOk`. -/
private theorem proposerOk_named_tick (S : Setup V) (gc : Protocol.GradeContract V) (v : V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (h : ProposerOk S.E st.core) :
    ProposerOk S.E (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v) st record t).1.core := by
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧
      S.E.proposer s = (S.node v).val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node v) st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc (S.node v) st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have h0 : ProposerOk S.E st0.core := h
  have h1 : ProposerOk S.E st1.core := by
    dsimp only [st1]
    split_ifs
    · exact proposerOk_propose_block_with S.E S.hc S.cfg gc (S.node v) st0 h0
    · exact h0
  have h2 : ProposerOk S.E st2.core := by
    dsimp only [st2]
    split_ifs
    · exact proposerOk_of_T_eq
        (Protocol.goldfish_vote_with_T gc S.E S.hc (S.node v) st1.core) h1
    · exact h1
  have h3 : ProposerOk S.E st3.core := by
    dsimp only [st3]
    split_ifs
    · exact proposerOk_of_T_eq rfl h2
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
  rw [hstage]
  split_ifs
  · exact proposerOk_attest_with S.E S.hc gc (S.node v) st3 record h3
  · exact h3


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
