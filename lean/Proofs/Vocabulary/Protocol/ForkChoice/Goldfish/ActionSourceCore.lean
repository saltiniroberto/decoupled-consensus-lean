module
public import Proofs.Vocabulary.Protocol.Handlers.FinalityMonotoneCore
public import Proofs.Vocabulary.Protocol.Handlers.StoreBridge
public import Proofs.Vocabulary.Protocol.Grades.Q10Frame
public import Proofs.Vocabulary.Internal.Internal.GradeReads
public import Proofs.Vocabulary.Generic.CarrierAdmissionCore
public import Proofs.Vocabulary.ModelProperties.Store_toHealing
public import Proofs.Vocabulary.ModelProperties.NamedDuties_update_confirmation_with
public import Proofs.Vocabulary.ModelProperties.update_confirmation_with
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
public import Proofs.Vocabulary.ModelProperties.NamedProfile_gradeContract
public import Proofs.Vocabulary.ModelProperties.get_sg_vote_with
public import Proofs.Vocabulary.ModelProperties.currentSGVote
public import Proofs.Vocabulary.ModelProperties.get_filtered_block_tree
public import Proofs.Vocabulary.ModelProperties.grade2_block_with
public import Proofs.Vocabulary.ModelProperties.fg_source_with
public import Proofs.Vocabulary.ModelProperties.deepest_clear
public import Proofs.Vocabulary.ModelProperties.Block_Preceq
public import Proofs.Vocabulary.ModelProperties.NamedStore_setClock
import Proofs.Vocabulary.Execution.Acceptance
import Proofs.Vocabulary.Execution.ExcludesRefute
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Proofs.Vocabulary.ModelProperties.NamedProfile_gradeContract
import Proofs.Vocabulary.ModelProperties.grade2Block

@[expose] public section

/-!
# The round action's frame and grade-2 candidate

Facts about an honest validator's round-`r` action read: the frozen round-`r` frame it reads, and
the ancestry of its grade-2 candidate towards the anchor, the SG block and the FG source.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The frozen round-`r` frame the action reads -/


/-- At an honest validator's round-`r` action read, with `0 < r` and `S.a r` within the horizon, the
    frame's result for every phase `p` is the grade root of `v`'s store at `p`'s domain time,
    clipped to the action read's finalized block. -/
theorem actionFrame_phase_completed (S : Setup V) {rho : Run V}
    (core : NamedAdmissibleCore S rho) {v : V} (hv : v ∈ rho.honest)
    {r : Round} (hr : 0 < r) (hhor : S.a r ≤ rho.horizon) (p : DecoupledConsensusModel.Protocol.Phase) :
    DecoupledConsensusModel.Protocol.phaseResult
        (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v r).cache
          (actionReadAt S rho v r).st.core.toHealing r) p =
      some ((PhaseGrades.storeRoot S.E S.hc
          (NamedRun.stateBeforeTime S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r p) v).st r p).map
        (fun B => DecoupledConsensusModel.Protocol.clipGrade B
          (actionReadAt S rho v r).st.core.F)) :=
  FrameForward.frame_phase_checkpoint_eq S rho v r p _
    (FrameCompleted.frame_phase_completed S rho core v hv r hr p (S.a r)
      (NamedOutageClosure.q10_domain_lt_a S r p) le_rfl
      (le_trans (FrameForward.domain_le_a S r p) hhor))

/-- The case `p = g0` of `actionFrame_phase_completed`: the frame's grade-0 result is the grade-0
    root of `v`'s store at the grade-0 domain time, clipped to the action read's finalized block. -/
theorem actionFrame_g0 (S : Setup V) {rho : Run V}
    (core : NamedAdmissibleCore S rho) {v : V} (hv : v ∈ rho.honest)
    {r : Round} (hr : 0 < r) (hhor : S.a r ≤ rho.horizon) :
    (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v r).cache
        (actionReadAt S rho v r).st.core.toHealing r).g0 =
      some ((PhaseGrades.storeRoot S.E S.hc
          (NamedRun.stateBeforeTime S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) v).st r .g0).map
        (fun B => DecoupledConsensusModel.Protocol.clipGrade B
          (actionReadAt S rho v r).st.core.F)) :=
  actionFrame_phase_completed S core hv hr hhor .g0

omit [Fintype V] in
/-- A block of the filtered tree of a store is in the store's block tree. -/
theorem mem_T_of_mem_filteredTree {st : Protocol.Store V} {B : Block V}
    (h : B ∈ Protocol.get_filtered_block_tree st.toHealing.toFG) : B ∈ st.T := by
  simp only [Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
    Protocol.finalized_descendants, Finset.mem_filter,
    Protocol.Store.toHealing] at h
  exact h.1.1.1

/-! ## The grade-2 candidate of the action read -/

/-- At an honest validator's round-`r` action read, the grade-2 candidate `Q` is an ancestor of the
    read's anchor. -/
theorem actionQ2_preceq_actionAnchor (S : Setup V) {rho : Run V}
    (core : NamedAdmissibleCore S rho) {v : V} (hv : v ∈ rho.honest)
    {r : Round} (hr : 0 < r) (hhor : S.a r ≤ rho.horizon) {Q : Block V}
    (hq : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q) :
    Block.Preceq Q (PhaseGrades.nodeAnchor S (actionReadAt S rho v r) r) :=
  NamedOutageClosure.grade2_preceq_anchor_at_checkpoint S rho core v hv (S.a r) r
    ⟨hr, le_rfl, hhor⟩ Q hq

/-- At an honest validator's round-`r` action read, an ancestor `C` of the grade-2 candidate `Q` is
    an ancestor of the action's SG block. -/
theorem preceq_actionSGBlockAt_of_actionQ2 (S : Setup V) {rho : Run V}
    (core : NamedAdmissibleCore S rho) {v : V} (hv : v ∈ rho.honest)
    {r : Round} (hr : 0 < r) (hhor : S.a r ≤ rho.horizon) {C Q : Block V}
    (hq : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q)
    (hCQ : Block.Preceq C Q) :
    Block.Preceq C (actionSGBlockAt S rho v r) := by
  set n := actionReadAt S rho v r with hn
  set st := n.st.core.toHealing with hst
  set grades := DecoupledConsensusModel.Protocol.frameGradeRead n.cache S.E S.hc st r with hgr
  have hk : S.hc.round_of st.s = r := Proofs.HealingLemmas.round_of_slotOf_a S r
  have heq : actionSGBlockAt S rho v r = Protocol.currentSGVote st grades := by
    show Protocol.get_sg_vote_with (NamedProfile.gradeContract n.cache) S.E S.hc st
        (S.hc.round_of st.s)
        (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache) S.E S.hc st
          (S.hc.round_of st.s)) = Protocol.currentSGVote st grades
    rw [hk]; rfl
  have hQ2 : grades.Q2 = some Q := hq
  have hanchor : Block.Preceq Q grades.anchor :=
    actionQ2_preceq_actionAnchor S core hv hr hhor hq
  rw [heq]
  unfold Protocol.currentSGVote
  cases hdc : Protocol.deepest_clear (some grades.anchor) st.live_confirmed grades.clear with
  | none =>
      simp only [hQ2]
      exact hCQ
  | some B =>
      simp only []
      have hAB : Block.Preceq grades.anchor B := by
        have hmem := Proofs.Engine.deepest?_mem hdc
        unfold Protocol.deepest_clear at hmem
        exact (Finset.mem_filter.mp hmem).2.1
      exact Block.preceq_trans hCQ (Block.preceq_trans hanchor hAB)

/-- At a round-`r` action read, an ancestor `C` of the grade-2 candidate `Q` is an ancestor of the
    read's FG source `X`. -/
theorem preceq_actionFGSource_of_actionQ2 (S : Setup V) (rho : Run V) (v : V)
    (r : Round) {C Q X : Block V}
    (hq : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q)
    (hCQ : Block.Preceq C Q)
    (hsource : PhaseGrades.nodeFGSource S (actionReadAt S rho v r) r = some X) :
    Block.Preceq C X := by
  have hQ2 : Protocol.grade2_block_with
      (NamedProfile.gradeContract (actionReadAt S rho v r).cache) S.E S.hc
      (actionReadAt S rho v r).st.core.toHealing r = some Q := by
    rw [Proofs.ModelProperties.grade2_block_with_eq_read_Q2]
    exact hq
  rw [PhaseGrades.nodeFGSource, hQ2] at hsource
  cases hwalk : Protocol.deepest_clear (some Q)
      (actionReadAt S rho v r).st.core.toHealing.live_confirmed
      ((NamedProfile.gradeContract (actionReadAt S rho v r).cache).read S.E S.hc
        (actionReadAt S rho v r).st.core.toHealing r).clear with
  | none =>
      rw [Proofs.ModelProperties.fg_source_with_some_of_deepest_clear_none _ _ _ _ _ hwalk]
        at hsource
      rw [← Option.some_inj.mp hsource]
      exact hCQ
  | some B =>
      rw [Proofs.ModelProperties.fg_source_with_some_of_deepest_clear _ _ _ _ _ hwalk]
        at hsource
      have hQB : Block.Preceq Q B := Proofs.ModelProperties.deepest_clear_floor_Preceq hwalk
      rw [← Option.some_inj.mp hsource]
      exact Proofs.ModelProperties.Preceq_trans hCQ hQB

/-! ## Blocks of a store were accepted before the read -/


/-- A block of `v`'s store before `read` is genesis, or the erasure of a named block `v` accepted
    before `read`. -/
theorem block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (v : V) (read : Time) {B : Block V}
    (hB : B ∈ (rho.storeBeforeTime S v read).T) :
    B = Block.genesis ∨
      ∃ (D : NamedBlock V) (i : Nat) (t : Time),
        D.erase = B ∧ Run.acceptsAt S rho i v (.block D) t ∧ t < read := by
  obtain ⟨N, hN, hNlt⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S sch read
  have hread : rho.storeBeforeTime S v read = (rho.stateBefore S N v).st := by
    unfold Run.storeBeforeTime
    exact congrArg NamedNodeState.st (congrFun hN v)
  have hB' : B ∈ (rho.stateBefore S N v).st.core.T := by
    simpa only [← hread] using hB
  obtain ⟨D, hDbodies, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho N v hB'
  have hprocessed : Object.processed (rho.stateBefore S N v).st (.block D) = true := by
    simp only [Object.processed, NamedReceipt.processed, decide_eq_true_eq]
    exact hDbodies
  rcases Protocol.acceptsAt_block_of_processed S rho v N D hprocessed with
    hgen | ⟨i, hiN, t, hacc⟩
  · exact Or.inl (by rw [← hDerase, hgen]; rfl)
  · obtain ⟨-, e, he, -, het⟩ := hacc.1
    have heLt : e.time < read := hNlt i e hiN he
    exact Or.inr ⟨D, i, t, hDerase, hacc, by simpa only [het] using heLt⟩

/-! ## The grade-2 candidate is in the filtered tree -/

/-- The grade-2 candidate of a round-`r` action read is in that read's filtered tree. -/
theorem actionQ2_mem_filteredTree (S : Setup V) (rho : Run V) (v : V) (r : Round)
    {Q : Block V} (hq : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q) :
    Q ∈ PhaseGrades.filteredTree (actionReadAt S rho v r) := by
  have hq' : DecoupledConsensusModel.Protocol.grade2Block
      (actionReadAt S rho v r).st.core.toHealing
      (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v r).cache
        (actionReadAt S rho v r).st.core.toHealing r) = some Q := by
    rw [← Proofs.ModelProperties.gradeContract_read_Q2 _ S.E]
    exact hq
  exact Proofs.ModelProperties.mem_filtered_of_grade2Block hq'


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
