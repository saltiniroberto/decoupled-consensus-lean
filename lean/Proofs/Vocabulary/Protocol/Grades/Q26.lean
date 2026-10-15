module
public import Proofs.Vocabulary.Protocol.Grades.PostOutage
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# The selected action G2 block and the vote duty

Given the delivery facts at an honest reader, the G2 block selected at an honest action precedes
that reader's frozen G1 root and its vote-duty head.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol
open NamedOutageClosure

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The G2 block `Q` selected at `p`'s round-`r` action precedes the frozen G1 root of `w`'s
    vote-duty frame, provided `Q` is in `w`'s filtered tree and G1-graded at the G1 domain time and
    still in the filtered tree at the vote time. -/
theorem selectedActionG2_preceq_frozenG1_at_reader
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {r : Round} (hr : 0 < r) {p w : V}
    (hp : p ∈ rho.honest) (hw : w ∈ rho.honest) {Q : Block V}
    (hQ : Protocol.grade2_block_with
      (NamedProfile.gradeContract
        (actionDutyRead S rho p r).cache)
      S.E S.hc (actionDutyRead S rho p r).st.core.toHealing r = some Q)
    {s : Slot} (hround : S.hc.round_of s = r)
    (hread : domain S.E S.hc r .g1 < Protocol.vote_time S.E s)
    (hta : Protocol.vote_time S.E s ≤ S.a r)
    (hhor : domain S.E S.hc r .g1 ≤ rho.horizon)
    (hQdomain : Q ∈ filteredTree
      (readAt S rho (domain S.E S.hc r .g1) w))
    (hgrade : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g1) w).st r .g1 Q = true)
    (hQread : Q ∈ filteredTree
      (readAt S rho (Protocol.vote_time S.E s) w)) :
    ∃ R, (DecoupledConsensusModel.Protocol.readFrame
        (voteDutyRead S rho w s).cache
        (voteDutyRead S rho w s).st.core.toHealing r).g1 =
        some (some R) ∧ Block.Preceq Q R := by
  let t := Protocol.vote_time S.E s
  let before := NamedRun.stateBeforeTime S rho t w
  let read := NamedActionReads.confirmationReadFrom S before t
  let domainRead := NamedRun.stateBeforeTime S rho
    (domain S.E S.hc r .g1) w
  have hround' : S.hc.round_of (S.E.slotOf t) = r := by
    simpa only [t, Proofs.Optimistic.slotOf_vote_time] using hround
  have hQmem : Q ∈ domainRead.st.core.T := by
    have h := hQdomain
    simpa only [domainRead, filteredTree, PhaseGrades.readAt] using
      mem_T_of_mem_filteredTree h
  have hgrade' : DecoupledConsensusModel.Protocol.gradeBool S.E
      domainRead.st.core.toHealing.gradeView domainRead.st.core.F
      S.hc.η_SG r (early S.E S.hc r .g1) (late S.E S.hc r .g1) Q = true := by
    simpa only [storeGrade, phaseGrade, domainRead, PhaseGrades.readAt] using hgrade
  obtain ⟨raw, hraw, hQraw⟩ := NamedOutageClosure.q10_freeze_of_graded
    S.E domainRead.st.core.toHealing.gradeView domainRead.st.core.F
    S.hc.η_SG r (NamedOutageClosure.q10_early_le_late S r .g1) hQmem hgrade'
  have hQread' : Q ∈ Protocol.get_filtered_block_tree
      before.st.core.toHealing.toFG := by
    simpa only [before, t, filteredTree, PhaseGrades.readAt] using hQread
  have hFQ : Block.Preceq before.st.core.F Q :=
    NamedOutageClosure.q10_filtered_F hQread'
  have hcompat : Block.compatible Q before.st.core.F = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hFQ
  have hQclip : Block.Preceq Q
      (DecoupledConsensusModel.Protocol.clipGrade raw before.st.core.F) :=
    (NamedOutageClosure.q10_retained_prefix raw before.st.core.F Q hcompat).mpr hQraw
  have hframe := FrameCompleted.frame_phase_completed S rho core w hw r hr
    .g1 t hread hta hhor
  have hframe' :
      (DecoupledConsensusModel.Protocol.readFrame before.cache before.st.core.toHealing r).g1 =
        some ((storeRoot S.E S.hc domainRead.st r .g1).map
          (fun X => DecoupledConsensusModel.Protocol.clipGrade X before.st.core.F)) := by
    simp only [before, domainRead, storeRoot, phaseRoot, Protocol.HealingStore.gradeView]
    exact hframe
  have hbase :
      (DecoupledConsensusModel.Protocol.readFrame before.cache before.st.core.toHealing r).g1 =
        some (some (DecoupledConsensusModel.Protocol.clipGrade raw before.st.core.F)) := by
    simpa only [storeRoot, phaseRoot, hraw, Option.map_some] using hframe'
  have hprepared := NamedOutageClosure.frame_phase_prepared_eq S rho w r
    .g1 t hround' (some (DecoupledConsensusModel.Protocol.clipGrade raw before.st.core.F))
    hbase
  refine ⟨DecoupledConsensusModel.Protocol.clipGrade raw before.st.core.F, ?_, hQclip⟩
  simp only [read, before, t, voteDutyRead,
    NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
    Protocol.NamedStore.setClock, Protocol.Store.toHealing, Protocol.Store.sg_pool]
  exact hprepared

/-- The G2 block `Q` selected at `p`'s round-`r` action precedes `w`'s vote-duty head, provided `Q`
    is in `w`'s filtered tree and G1-graded at the G1 domain time, in the filtered tree at the vote
    time, and in the filtered tree of `w`'s vote-duty read. -/
theorem selectedActionG2_preceq_sameRoundVoteDutyHead_of_activeAtVote
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {r : Round} (hr : 0 < r) {p : V} (hp : p ∈ rho.honest) {Q : Block V}
    (hQ : Protocol.grade2_block_with
      (NamedProfile.gradeContract
        (actionDutyRead S rho p r).cache)
      S.E S.hc (actionDutyRead S rho p r).st.core.toHealing r = some Q)
    {s : Slot} (hround : S.hc.round_of s = r)
    {w : V} (hw : w ∈ rho.honest)
    (hread : domain S.E S.hc r .g1 < Protocol.vote_time S.E s)
    (hta : Protocol.vote_time S.E s ≤ S.a r)
    (hhor : domain S.E S.hc r .g1 ≤ rho.horizon)
    (hQdomain : Q ∈ filteredTree
      (readAt S rho (domain S.E S.hc r .g1) w))
    (hgrade : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g1) w).st r .g1 Q = true)
    (hQread : Q ∈ filteredTree
      (readAt S rho (Protocol.vote_time S.E s) w))
    (hactiveVote : Q ∈ Protocol.get_filtered_block_tree
      (voteDutyRead S rho w s).st.core.toHealing.toFG) :
    Block.Preceq Q (voterHeadAt S rho w s) := by
  obtain ⟨R, hframe, hQR⟩ := selectedActionG2_preceq_frozenG1_at_reader
    S core hr hp hw hQ hround hread hta hhor hQdomain hgrade hQread
  let n := voteDutyRead S rho w s
  have hroundVote : S.hc.round_of n.st.core.s = r := by
    simpa only [n, Proofs.Optimistic.voteDutyRead_slot] using hround
  have hframe' :
      (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing
        (S.hc.round_of n.st.core.s)).g1 = some (some R) := by
    simpa only [n, hroundVote] using hframe
  have hanchorQ : Block.Preceq Q (voterAnchorAt S rho w s) := by
    change Block.Preceq Q
      (DecoupledConsensusModel.Protocol.anchor S.E S.hc n.st.core.toHealing
        (S.hc.round_of n.st.core.s)
        (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing
          (S.hc.round_of n.st.core.s)).g1)
    cases hslot : (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing
        (S.hc.round_of n.st.core.s)).g1 with
    | none =>
        rw [hslot] at hframe'
        cases hframe'
    | some opt =>
        cases opt with
        | none =>
            rw [hslot] at hframe'
            cases hframe'
        | some root =>
            have hQR' : Block.Preceq Q root := by
              have hEq : some (some R) = some (some root) :=
                hframe'.symm.trans hslot
              exact Option.some.inj (Option.some.inj hEq) ▸ hQR
            obtain ⟨A, hA, hQA⟩ :=
              NamedOutageClosure.q10_activePrefix_dominates hactiveVote hQR'
            simp only [DecoupledConsensusModel.Protocol.anchor]
            rw [hA]
            simp only [Option.getD_some]
            exact hQA
  exact NamedOutageClosure.preceq_voteDutyHead_of_preceq_voteDutyAnchor
    S rho w s hanchorQ

#print axioms selectedActionG2_preceq_frozenG1_at_reader
#print axioms selectedActionG2_preceq_sameRoundVoteDutyHead_of_activeAtVote

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
