module
public import Proofs.Vocabulary.Protocol.Handlers.HMaxMonotone
public import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry
public import Proofs.Vocabulary.ModelProperties.NamedNode_initial
public import Proofs.Vocabulary.ModelProperties.NamedStore_initial
import Proofs.Vocabulary.Protocol.Handlers.Execution
import Mathlib.Tactic.ENatToNat

@[expose] public section

/-!
# The stored maximum height

The heights of the processed blocks are bounded by `h_max`, one event raises `h_max` by at most one,
and the honest maximum before an event index or a time is monotone.
-/

namespace DecoupledConsensusModel
namespace Proofs

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


namespace HealingSurface


/-! ## Processed-tree height bounds -/

/-- Every block of the tree has a height at most `h_max`. -/
def TreeHeightsLeHMax (st : Protocol.Store V) : Prop :=
  ∀ B ∈ st.T, (st.σ B).h ≤ st.h_max


/-! ### One event raises the stored maximum by at most one -/

omit [Fintype V] in
/-- `update_finality` sets `h_max` to the maximum of its old value and the incoming height. -/
theorem update_finality_h_max_eq
    (st : Protocol.Store V) (sigma : Protocol.ChainState V) :
    (Protocol.update_finality st sigma).h_max = max st.h_max sigma.h := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl


private theorem named_transition_h_le_succ
    (E : Env V) (cfg : Protocol.HeightConfig) (B : NamedBlock V)
    (sigma : Protocol.ChainState V) :
    (Protocol.named_transition E cfg sigma B).h ≤ sigma.h + 1 := by
  have hfold : (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V) sigma
      B.erase B.attestations).h = sigma.h := by
    unfold Protocol.fold_rows
    exact (NamedDerivationGeometry.fold_context_fields
      (Protocol.TimeoutBinding.targeted V) B.attestations
      { sigma with s := B.erase.slot }).2.1
  unfold Protocol.named_transition Protocol.transition_rows
  rw [Protocol.process_height_events_eq]
  split_ifs
  · rw [Protocol.advance_height_h, Protocol.afterFin_h, hfold]
  · rw [Protocol.advance_height_h, Protocol.afterFin_h, hfold]
  · rw [Protocol.afterFin_h, hfold]
    exact Nat.le_succ _

private theorem on_block_using_h_max_le_succ
    (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V)
    (hbuild : ∀ parentState, (buildState parentState).h ≤ parentState.h + 1)
    (hbound : TreeHeightsLeHMax st) :
    (Protocol.on_block_using E st B buildState).h_max ≤ st.h_max + 1 := by
  by_cases hfirst : st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T
  · simp [Protocol.on_block_using, hfirst]
  by_cases hadmit : Block.preceq st.F B = true
  · by_cases hproposer : B.proposer? = some (E.proposer B.slot)
    · by_cases hparent : B.parent.slot < B.slot
      · let state := buildState (st.σ B.parent)
        let stored : Protocol.Store V :=
          { st with
            σ := fun C => if C = B then state else st.σ C
            T := insert B st.T
            timestamp_block := fun C =>
              if C = B then some (st.t : Stamp) else st.timestamp_block C }
        let unpacked := B.gf_votes.foldl (Protocol.on_goldfish_vote_checked E) stored
        have hon : Protocol.on_block_using E st B buildState =
            Protocol.update_finality unpacked (unpacked.σ B) := by
          simp [Protocol.on_block_using, hfirst, hadmit, hproposer, hparent,
            unpacked, stored, state]
        have hparentT : B.parent ∈ st.T := by
          by_contra hnot
          exact hfirst (Or.inr (Or.inr hnot))
        have hstate : state.h ≤ st.h_max + 1 :=
          (hbuild (st.σ B.parent)).trans
            (Nat.add_le_add_right (hbound B.parent hparentT) 1)
        have hSigma : unpacked.σ B = state := by
          simp only [unpacked, stored,
            (coreEq_foldl_on_goldfish_vote_checked E B.gf_votes stored).σ_eq,
            if_pos]
        have hMax : unpacked.h_max = st.h_max := by
          simp only [unpacked, stored, foldl_on_goldfish_vote_checked_h_max]
        rw [hon, update_finality_h_max_eq, hSigma, hMax]
        exact Nat.max_le.mpr ⟨Nat.le_succ _, hstate⟩
      · simp [Protocol.on_block_using, hfirst, hadmit, hproposer, hparent]
    · simp [Protocol.on_block_using, hfirst, hadmit, hproposer]
  · simp [Protocol.on_block_using, hfirst, hadmit]

private theorem on_block_checked_using_h_max_le_succ
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (B : Block V)
    (handle : Protocol.Store V → Protocol.Store V)
    (hhandle : TreeHeightsLeHMax st → (handle st).h_max ≤ st.h_max + 1)
    (hbound : TreeHeightsLeHMax st) :
    (Protocol.on_block_checked_using handle hc st B).h_max ≤ st.h_max + 1 := by
  simp only [Protocol.on_block_checked_using]
  split_ifs with hvalid
  · exact hhandle hbound
  · exact Nat.le_succ _

private theorem process_block_core_h_max_le_succ
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hbound : TreeHeightsLeHMax st.core) :
    (Protocol.NamedStore.process_block_core E hc cfg st B).core.h_max ≤ st.core.h_max + 1 := by
  dsimp only [Protocol.NamedStore.process_block_core]
  split_ifs with hp
  · rw [commitBlock_core]
    exact on_block_checked_using_h_max_le_succ hc st.core B.erase _
      (fun h' => on_block_using_h_max_le_succ E st.core B.erase _
        (named_transition_h_le_succ E cfg B) h') hbound
  · exact Nat.le_succ _

private theorem admit_row_h_max_eq
    (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (a : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st a).core.h_max = st.core.h_max := by
  rw [admit_row_core, on_sg_vote_h_max]

private theorem admit_rows_h_max_eq (hc : Protocol.HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : Protocol.NamedStore V),
      (Protocol.NamedAdmission.admit_rows hc st rows).core.h_max = st.core.h_max
  | [], _ => rfl
  | a :: rows, st =>
      (admit_rows_h_max_eq hc rows (Protocol.NamedAdmission.admit_row hc st a)).trans
        (admit_row_h_max_eq hc st a)

private theorem on_block_with_h_max_le_succ
    (admission : Protocol.CarriedAdmission) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hbound : TreeHeightsLeHMax st.core) :
    (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).core.h_max ≤
      st.core.h_max + 1 := by
  have hb := process_block_core_h_max_le_succ E hc cfg st B hbound
  cases admission with
  | alsoCarried =>
      dsimp only [Protocol.NamedAdmission.on_block_with, Protocol.NamedAdmission.admit_carried]
      split_ifs
      · rw [admit_rows_h_max_eq]
        exact hb
      · exact hb

private theorem propose_block_with_h_max_le_succ
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (hbound : TreeHeightsLeHMax st.core) :
    (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1.core.h_max ≤
      st.core.h_max + 1 := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact Nat.le_succ _
  · exact on_block_with_h_max_le_succ .alsoCarried E hc cfg st _ hbound

private theorem goldfish_vote_with_h_max_eq
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1.core.h_max = st.core.h_max := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact on_goldfish_vote_checked_h_max E st.core _
  · rfl

private theorem update_confirmation_with_h_max_eq'
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (s : Slot) :
    (Protocol.NamedDuties.update_confirmation_with gc E hc st s).core.h_max = st.core.h_max :=
  rfl


private theorem attest_with_h_max_eq
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core.h_max = st.core.h_max :=
  admit_row_h_max_eq hc st _

private theorem tick_h_max_le_succ
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (hbound : TreeHeightsLeHMax st.core) :
    (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core.h_max ≤ st.core.h_max + 1 := by
  have hbound0 : TreeHeightsLeHMax (Protocol.NamedStore.setClock E st t).core := hbound
  have hprop : (Protocol.NamedDuties.propose_block_with gc E hc cfg nd
      (Protocol.NamedStore.setClock E st t)).1.core.h_max ≤ st.core.h_max + 1 :=
    propose_block_with_h_max_le_succ gc E hc cfg nd (Protocol.NamedStore.setClock E st t) hbound0
  dsimp only [Protocol.NamedTick.tick, Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps]
  split_ifs <;>
    simp only [goldfish_vote_with_h_max_eq, update_confirmation_with_h_max_eq',
      attest_with_h_max_eq] <;>
    first
      | exact Nat.le_succ _
      | exact hprop

private theorem node_tick_h_max_le_succ
    (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    (hbound : TreeHeightsLeHMax n.st.core) :
    (NamedNode.tick S v n t).1.st.core.h_max ≤ n.st.core.h_max + 1 :=
  tick_h_max_le_succ (NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
    S.E S.hc S.cfg (S.node v) n.st n.record t hbound

private theorem node_process_h_max_le_succ
    (S : Setup V) (n : NodeState V) (o : Object V)
    (hbound : TreeHeightsLeHMax n.st.core) :
    (NamedNode.process S n o).st.core.h_max ≤ n.st.core.h_max + 1 := by
  cases o with
  | block B => exact on_block_with_h_max_le_succ .alsoCarried S.E S.hc S.cfg n.st B hbound
  | gfVote u =>
      show (Protocol.on_goldfish_vote_checked S.E n.st.core u).h_max ≤ n.st.core.h_max + 1
      rw [on_goldfish_vote_checked_h_max]
      exact Nat.le_succ _
  | attest a =>
      show (Protocol.NamedAdmission.admit_row S.hc n.st a).core.h_max ≤ n.st.core.h_max + 1
      rw [admit_row_h_max_eq]
      exact Nat.le_succ _


/-! ## Event-index and time-index frontiers -/

/-! ### Honest event-prefix frontiers -/

/-- An honest node's `h_max` after `n` events is at most `honestHMaxBeforeIndex S rho n`. -/
theorem localHMax_le_honestHMaxBeforeIndex
    (S : Setup V) (rho : Run V) (n : Nat) {v : V}
    (hv : v ∈ rho.honest) :
    (rho.stateBefore S n v).st.h_max ≤ honestHMaxBeforeIndex S rho n := by
  simpa only [honestHMaxBeforeIndex] using
    (Finset.le_sup
      (f := fun w => (rho.stateBefore S n w).st.h_max) hv)

/-- `honestHMaxBeforeIndex` is monotone in the event index. -/
theorem honestHMaxBeforeIndex_mono
    (S : Setup V) (rho : Run V) {n m : Nat} (hnm : n ≤ m) :
    honestHMaxBeforeIndex S rho n ≤ honestHMaxBeforeIndex S rho m := by
  unfold honestHMaxBeforeIndex
  apply Finset.sup_le
  intro v hv
  exact (stateBefore_hMax_mono S rho v hnm).trans
    (Finset.le_sup
      (f := fun w => (rho.stateBefore S m w).st.h_max) hv)

/-! ### Strict and inclusive time indices -/

/-- Number of run events strictly before `t`. -/
def strictEventIndex (rho : Run V) (t : Time) : Nat :=
  (rho.events.filter (fun e => decide (e.time < t))).length

/-- Number of run events at or before `t`. -/
def inclusiveEventIndex (rho : Run V) (t : Time) : Nat :=
  (rho.events.filter (fun e => decide (e.time ≤ t))).length

omit [DecidableEq V] [Fintype V] in
/-- `strictEventIndex` is monotone in the time. -/
theorem strictEventIndex_mono
    (rho : Run V) {t u : Time} (htu : t ≤ u) :
    strictEventIndex rho t ≤ strictEventIndex rho u := by
  unfold strictEventIndex
  exact (List.monotone_filter_right rho.events
    (fun e he => by
      simp only [decide_eq_true_eq] at he ⊢
      exact lt_of_lt_of_le he htu)).length_le

omit [DecidableEq V] [Fintype V] in
/-- `inclusiveEventIndex` is monotone in the time. -/
theorem inclusiveEventIndex_mono
    (rho : Run V) {t u : Time} (htu : t ≤ u) :
    inclusiveEventIndex rho t ≤ inclusiveEventIndex rho u := by
  unfold inclusiveEventIndex
  exact (List.monotone_filter_right rho.events
    (fun e he => by
      simp only [decide_eq_true_eq] at he ⊢
      exact he.trans htu)).length_le

/-- The read before `t` is the state after `strictEventIndex rho t` events. -/
theorem stateBeforeTime_eq_stateBefore_strictEventIndex
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho) (t : Time) :
    NamedRun.stateBeforeTime S rho t = rho.stateBefore S (strictEventIndex rho t) := by
  simpa only [strictEventIndex] using
    Proofs.Optimistic.stateBeforeTime_eq_take S sch t

/-- The read at `t` is the state after `inclusiveEventIndex rho t` events. -/
theorem stateAt_eq_stateBefore_inclusiveEventIndex
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho) (t : Time) :
    NamedRun.readAt S rho t = rho.stateBefore S (inclusiveEventIndex rho t) := by
  simpa only [inclusiveEventIndex] using Proofs.Optimistic.stateAt_eq_take S sch t

/-- A node's store before `t` is its store after `strictEventIndex rho t` events. -/
theorem storeBeforeTime_eq_stateBefore_strictEventIndex
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (v : V) (t : Time) :
    rho.storeBeforeTime S v t =
      (rho.stateBefore S (strictEventIndex rho t) v).st := by
  unfold Run.storeBeforeTime
  rw [congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex S sch t) v]

/-- A node's store at `t` is its store after `inclusiveEventIndex rho t` events. -/
theorem storeAt_eq_stateBefore_inclusiveEventIndex
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (v : V) (t : Time) :
    rho.storeAt S v t =
      (rho.stateBefore S (inclusiveEventIndex rho t) v).st := by
  unfold Run.storeAt
  rw [congrFun (stateAt_eq_stateBefore_inclusiveEventIndex S sch t) v]


omit [DecidableEq V] [Fintype V] in
/-- The exact strict index at `t` is the exact inclusive index at `t - 1`. -/
theorem strictEventIndex_eq_inclusiveEventIndex_pred
    (rho : Run V) (t : Time) :
    strictEventIndex rho t = inclusiveEventIndex rho (t - 1) := by
  have hfilter :
      (fun e : Event V => decide (e.time < t)) =
        (fun e : Event V => decide (e.time ≤ t - 1)) := by
    funext e
    exact Bool.decide_congr (Int.le_sub_one_iff).symm
  unfold strictEventIndex inclusiveEventIndex
  rw [hfilter]

/-- A node's `h_max` before `t` is monotone in `t`. -/
theorem storeBeforeTime_hMax_mono
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (v : V) {t u : Time} (htu : t ≤ u) :
    (rho.storeBeforeTime S v t).h_max ≤
      (rho.storeBeforeTime S v u).h_max := by
  rw [storeBeforeTime_eq_stateBefore_strictEventIndex S sch,
    storeBeforeTime_eq_stateBefore_strictEventIndex S sch]
  exact stateBefore_hMax_mono S rho v (strictEventIndex_mono rho htu)


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
