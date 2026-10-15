module
public import Proofs.Vocabulary.Protocol.Grades.RoundVoterTransport
public import Proofs.Vocabulary.Protocol.Grades.Q20_graded_has_honest_supporter
public import Proofs.Vocabulary.Protocol.Schedule.Action
public import Proofs.Vocabulary.Protocol.Store.HonestPoolActionBridge
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HonestMajorityCore
import Proofs.Vocabulary.Execution.EmissionShape

@[expose] public section

/-!
# Compatibility of relative-graded blocks

Two relative-graded blocks of one view are compatible, and a relative grade has an honest action
carrier of the preceding round.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Execution
open Internal.NamedOutageEntry
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

def relativePhaseRead
    (S : Setup V) (rho : Run V) (r : Round) (p : Phase) (w : V) :
    NamedNodeState V :=
  NamedRun.stateBeforeTime S rho (domain S.E S.hc (r + 1) p) w

/-- Two relative-graded blocks in one view are compatible. -/
theorem graded_oneChain_at_reader
    (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (eta r : Round) {early late : Time} (hcut : early ≤ late)
    {B B' : Block V}
    (hB : DecoupledConsensusModel.Protocol.gradeBool E gv F eta r early late B = true)
    (hB' : DecoupledConsensusModel.Protocol.gradeBool E gv F eta r early late B' = true) :
    Block.compatible B B' = true := by
  exact NamedOutageClosure.q10_graded_compatible E gv F eta r hcut hB hB'

/-- For every honest reader, every honest round-`r` voter's action SG block is an interpreted input
    of the reader's round-`(r + 1)` phase-`p` read, and resolves in the reader's tree. -/
def RelativeCarrierWindowAt
    (S : Setup V) (rho : Run V) (r : Round) (p : Phase) : Prop :=
  ∀ w ∈ rho.honest, ∀ u ∈ honestRoundVoters S rho r,
    ∃ y ∈ interpretedInputs
        (relativePhaseRead S rho r p w).st.core.toHealing.gradeView
        (relativePhaseRead S rho r p w).st.core.F
        S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) p) u,
      y.round = r ∧
      y.confirmed = some (actionSGBlockAt S rho u r).root ∧
      Block.find?
        (relativePhaseRead S rho r p w).st.core.T
        (actionSGBlockAt S rho u r).root = some (actionSGBlockAt S rho u r)

/-- Under `RelativeCarrierWindowAt` and a grade-forming majority, a block graded at an honest
    reader's round-`(r + 1)` phase-`p` domain read precedes some honest round-`r` voter's action SG
    block. -/
theorem relativeGrade_has_roundCarrier
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {r : Round} {p : Phase} (hwindow : RelativeCarrierWindowAt S rho r p)
    (hmajority : GradeFormingMajority S rho (r + 1))
    {w : V} (hw : w ∈ rho.honest) {B : Block V}
    (hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) p) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) p) w).st.core.F
      S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) p)
      (late S.E S.hc (r + 1) p) B = true) :
    ∃ u ∈ honestRoundVoters S rho r,
      Block.Preceq B (actionSGBlockAt S rho u r) := by
  let n := NamedRun.stateBeforeTime S rho (domain S.E S.hc (r + 1) p) w
  let gv := n.st.core.toHealing.gradeView
  let F := n.st.core.F
  let ea := early S.E S.hc (r + 1) p
  let la := late S.E S.hc (r + 1) p
  let voters := honestRoundVoters S rho r
  let bad := (Finset.univ \ rho.honest) ∪ staleHistoricalVoters S rho (r + 1)
  by_contra hnone
  push Not at hnone
  have hcut : ea ≤ la := NamedOutageClosure.q10_early_le_late S (r + 1) p
  have hvotersOpp : voters ⊆ Finset.univ.filter fun u =>
      DecoupledConsensusModel.Protocol.opposing gv F S.hc.η_SG (r + 1) ea la u B = true := by
    intro u hu
    have huHon : u ∈ rho.honest :=
      ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u r).mp hu).1
    obtain ⟨y, hy, hyround, hyconfirmed, hyfind⟩ := hwindow w hw u hu
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ u, ?_⟩
    simp only [DecoupledConsensusModel.Protocol.opposing, decide_eq_true_eq]
    refine Or.inl ⟨DecoupledConsensusModel.Protocol.token y, ?_, ?_, ?_⟩
    · exact Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token
        (NamedOutageClosure.q10_interpreted_cut gv F S.hc.η_SG (r + 1)
          hcut u (by simp only [n, gv, F, ea, Protocol.HealingStore.gradeView]; exact hy))
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzraw := (Finset.mem_filter.mp hz).1
      obtain ⟨_, _, _, _, _, _, _, _, hzupper⟩ :=
        NamedOutageClosure.honest_rawInput_is_own_round_vote S rho core
          (domain S.E S.hc (r + 1) p) (early S.E S.hc (r + 1) p)
          w hw huHon hzraw
      simpa only [DecoupledConsensusModel.Protocol.token, hyround] using hzupper
    · intro hcover
      change Protocol.head_covers n.st.core.T B y.confirmed = true at hcover
      rw [hyconfirmed] at hcover
      have hyfind' : Block.find? n.st.core.T
          (actionSGBlockAt S rho u r).root =
          some (actionSGBlockAt S rho u r) := by
        simpa only [n, relativePhaseRead] using hyfind
      simp only [Protocol.head_covers, hyfind'] at hcover
      exact hnone u hu hcover
  have hpositiveBad : (Finset.univ.filter fun u =>
      DecoupledConsensusModel.Protocol.positive gv F S.hc.η_SG (r + 1) ea la u B = true) ⊆
      bad := by
    intro u hu
    by_cases huHon : u ∈ rho.honest
    · refine Finset.mem_union_right _ ?_
      have huNotVoter : u ∉ voters := by
        intro huVoter
        have huOpp := (Finset.mem_filter.mp (hvotersOpp huVoter)).2
        have huPos := (Finset.mem_filter.mp hu).2
        have hsupports : DecoupledConsensusModel.Protocol.Supports
            (fun k b => DecoupledConsensusModel.Protocol.localCovers gv k b = true)
            (DecoupledConsensusModel.Protocol.readyView gv F S.hc.η_SG (r + 1) ea u)
            (DecoupledConsensusModel.Protocol.readyView gv F S.hc.η_SG (r + 1) la u)
            (DecoupledConsensusModel.Protocol.rawView gv S.hc.η_SG (r + 1) la u) B := by
          simpa only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq] using huPos
        have hnot := NamedOutageClosure.q10_not_opposes_of_supports
          (fun k b => DecoupledConsensusModel.Protocol.localCovers gv k b = true)
          (NamedOutageClosure.q10_readyView_cut gv F S.hc.η_SG (r + 1) hcut u)
          (NamedOutageClosure.q10_ready_subset_raw gv F S.hc.η_SG (r + 1) la u)
          hsupports
        exact hnot (by simpa only [DecoupledConsensusModel.Protocol.opposing,
          decide_eq_true_eq] using huOpp)
      have huPos := (Finset.mem_filter.mp hu).2
      simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq] at huPos
      obtain ⟨x, hx, -, -, -, -⟩ := huPos
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzraw := (Finset.mem_filter.mp hz).1
      obtain ⟨a, haround, hval, hemit, _, _, _, hlower, hupper⟩ :=
        NamedOutageClosure.honest_rawInput_is_own_round_vote S rho core
          (domain S.E S.hc (r + 1) p) (early S.E S.hc (r + 1) p)
          w hw huHon hzraw
      have hlatest : z.round ∈ Protocol.latest_window S.hc.η_SG (r + 1) :=
        NamedOutageClosure.mem_latest_window hlower (Nat.lt_succ_of_le hupper)
      have hzVoter : u ∈ honestRoundVoters S rho z.round :=
        (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u z.round).mpr
          ⟨huHon, a, hval, haround, hemit⟩
      have hnotPrevious : u ∉ honestRoundVoters S rho (r + 1 - 1) := by
        simpa only [Nat.add_sub_cancel, voters] using huNotVoter
      exact Proofs.NamedOutageInputs.stale_of_eligible_vote S rho
        hlatest hzVoter hnotPrevious
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huHon⟩)
  change DecoupledConsensusModel.Protocol.gradeBool S.E gv F S.hc.η_SG
    (r + 1) ea la B = true at hgrade
  simp only [DecoupledConsensusModel.Protocol.gradeBool, decide_eq_true_eq] at hgrade
  have hVotersWeight := S.E.electorate.weightOf_mono hvotersOpp
  have hPositiveWeight := S.E.electorate.weightOf_mono hpositiveBad
  change S.E.electorate.weightOf bad <
    S.E.electorate.weightOf voters at hmajority
  omega


end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms graded_oneChain_at_reader
#print axioms relativeGrade_has_roundCarrier
end DecoupledConsensusModel.Proofs.HealingSurface

end
