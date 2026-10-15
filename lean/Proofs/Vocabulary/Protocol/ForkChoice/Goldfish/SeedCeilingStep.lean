module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeiling
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
public import Proofs.Vocabulary.ModelProperties.get_sg_root_with
public import Proofs.Vocabulary.ModelProperties.Store_toHealing
public import Proofs.Vocabulary.ModelProperties.update_confirmation_with
public import Proofs.Vocabulary.ModelProperties.readFrame
public import Proofs.Vocabulary.ModelProperties.NamedProfile_gradeContract
public import Proofs.Vocabulary.ModelProperties.anchor
public import Proofs.Vocabulary.Execution.EmissionShape
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot
public import Proofs.Vocabulary.Protocol.Grades.RelativeSupporter
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalVoteDuty
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeDelivery
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HeightProgressSeedRegime
import Proofs.Vocabulary.Protocol.Grades.RelativeOneChain
import Proofs.Vocabulary.Protocol.Grades.GSTZeroSelectionSafety
import Proofs.Vocabulary.Protocol.Grades.GradeFormsBridge
import Proofs.Vocabulary.Protocol.Grades.RecoveryCapturedSlotInterval
import Proofs.Vocabulary.Protocol.Schedule.ConfirmationHistoryProducer
import Proofs.Vocabulary.Protocol.Schedule.GSTZeroReorgResilience
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Phase grades pass to ancestors

If a block has a phase grade, so does every ancestor of it (`confirmation_phaseGrade_mono`).
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.PhaseGrades
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem confirmationTime_lt_proposalTime_of_two_le
    (E : Env V) {s s' : Slot} (h : s + 2 ≤ s') :
    Protocol.confirmation_time E s < Protocol.proposal_time E s' := by
  have hcast : ((s : Time) + 2) ≤ (s' : Time) := by exact_mod_cast h
  have hDelta : (0 : Time) < E.Δ := E.Δ_pos
  have hcoef : (0 : Time) ≤ 4 * E.Δ :=
    Int.mul_nonneg (by decide) (le_of_lt hDelta)
  have hmul : 4 * E.Δ * ((s : Time) + 2) ≤ 4 * E.Δ * (s' : Time) :=
    Int.mul_le_mul_of_nonneg_left hcast hcoef
  simp only [Protocol.confirmation_time, Protocol.proposal_time, Env.t,
    slotStart]
  have hexpand : 4 * E.Δ * ((s : Time) + 2) =
      4 * E.Δ * (s : Time) + 8 * E.Δ := by ring
  rw [hexpand] at hmul
  have hstrict : 4 * E.Δ * (s : Time) + 6 * E.Δ <
      4 * E.Δ * (s : Time) + 8 * E.Δ := by
    have h68 : (6 : Time) * E.Δ < 8 * E.Δ := by
      simpa using Int.mul_lt_mul_of_pos_right
        (show (6 : Time) < 8 by decide) hDelta
    exact Int.add_lt_add_left h68 _
  exact lt_of_lt_of_le hstrict hmul


omit [Fintype V] in
private theorem confirmation_localCovers_mono
    {A B : Block V} {gv : Protocol.GradeView V} {key : Option BlockId}
    (hAB : Block.Preceq A B)
    (hB : DecoupledConsensusModel.Protocol.localCovers gv key B = true) :
    DecoupledConsensusModel.Protocol.localCovers gv key A = true := by
  unfold DecoupledConsensusModel.Protocol.localCovers at hB ⊢
  unfold Protocol.head_covers at hB ⊢
  cases key with
  | none => exact hB
  | some root =>
      dsimp only at hB ⊢
      cases hfind : Block.find? gv.T root with
      | none => rw [hfind] at hB; exact absurd hB (by simp)
      | some head =>
          rw [hfind] at hB
          exact Block.preceq_trans hAB hB

omit [Fintype V] in
private theorem confirmation_positive_mono
    {A B : Block V} (hAB : Block.Preceq A B)
    (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (v : V)
    (hB : DecoupledConsensusModel.Protocol.positive gv F eta r early late v B = true) :
    DecoupledConsensusModel.Protocol.positive gv F eta r early late v A = true := by
  simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq] at hB ⊢
  rcases hB with ⟨u, hu, hmax, hcov, hclean, hlate⟩
  refine ⟨u, hu, hmax, confirmation_localCovers_mono hAB hcov, hclean, ?_⟩
  intro x hx hlt
  exact confirmation_localCovers_mono hAB (hlate x hx hlt)

omit [Fintype V] in
private theorem confirmation_opposing_mono
    {A B : Block V} (hAB : Block.Preceq A B)
    (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (v : V)
    (hA : DecoupledConsensusModel.Protocol.opposing gv F eta r early late v A = true) :
    DecoupledConsensusModel.Protocol.opposing gv F eta r early late v B = true := by
  simp only [DecoupledConsensusModel.Protocol.opposing, decide_eq_true_eq] at hA ⊢
  rcases hA with ⟨x, hx, hmax, hnot⟩ |
      ⟨x, hx, y, hy, hmax, heq, hkey⟩
  · left
    refine ⟨x, hx, hmax, ?_⟩
    intro hcov
    exact hnot (confirmation_localCovers_mono hAB hcov)
  · exact Or.inr ⟨x, hx, y, hy, hmax, heq, hkey⟩

theorem confirmation_phaseGrade_mono
    (E : Env V) (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (r : Round) (phase : DecoupledConsensusModel.Protocol.Phase)
    {A B : Block V}
    (hAB : Block.Preceq A B)
    (hB : PhaseGrades.phaseGrade E hc gv F r phase B = true) :
    PhaseGrades.phaseGrade E hc gv F r phase A = true := by
  simp only [PhaseGrades.phaseGrade, DecoupledConsensusModel.Protocol.gradeBool,
    decide_eq_true_eq] at hB ⊢
  have hOpp : (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.opposing gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r phase)
        (DecoupledConsensusModel.Protocol.late E hc r phase) v A = true) ⊆
      Finset.univ.filter fun v =>
        DecoupledConsensusModel.Protocol.opposing gv F hc.η_SG r
          (DecoupledConsensusModel.Protocol.early E hc r phase)
          (DecoupledConsensusModel.Protocol.late E hc r phase) v B = true := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      confirmation_opposing_mono hAB gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r phase)
        (DecoupledConsensusModel.Protocol.late E hc r phase) v
        (Finset.mem_filter.mp hv).2⟩
  have hPos : (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r phase)
        (DecoupledConsensusModel.Protocol.late E hc r phase) v B = true) ⊆
      Finset.univ.filter fun v =>
        DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r
          (DecoupledConsensusModel.Protocol.early E hc r phase)
          (DecoupledConsensusModel.Protocol.late E hc r phase) v A = true := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      confirmation_positive_mono hAB gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r phase)
        (DecoupledConsensusModel.Protocol.late E hc r phase) v
        (Finset.mem_filter.mp hv).2⟩
  exact lt_of_le_of_lt (E.electorate.weightOf_mono hOpp)
    (lt_of_lt_of_le hB (E.electorate.weightOf_mono hPos))


/-- An inclusive slot interval as a finite set. -/
private def seedSlotRange (lo hi : Slot) : Finset Slot :=
  (Finset.range (hi + 1)).filter (fun d => lo ≤ d)

private theorem mem_seedSlotRange {lo hi d : Slot} :
    d ∈ seedSlotRange lo hi ↔ lo ≤ d ∧ d ≤ hi := by
  simp only [seedSlotRange, Finset.mem_filter, Finset.mem_range,
    Nat.lt_succ_iff]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
