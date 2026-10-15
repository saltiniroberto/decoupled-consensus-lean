import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.VocabularyAssumptionsLemmas
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_42

/-!
# Proposer recurrence and run prefixes

The proposer recurrence for the validators not held by the adversary, emissions carried from a run
to a run extending it, and the instants of the events later sts steps add to a run, stated over a
model `M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- If from `tGAT` every window of `gap` rounds contains a round, opening at least two rounds later,
    whose first three slots have proposers honest through their slots' confirmation instants, then
    for every round `r` whose opening slot is proposed at or after `tGAT` and whose window of `gap`
    rounds ends by `tAwakeEnd`, some round from `r` to `r + gap` has each of those three proposers
    not held by the adversary at its slot's confirmation instant. -/
theorem multiProposerRecurrenceOn_of_strongOpeningsRecurFrom (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) {tGAT tAwakeEnd : Int} {gap : Nat}
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap) :
    Restated.MultiProposerRecurrenceOn M S (notHeldAt Sched) gap tGAT tAwakeEnd := by
  intro r hstart hwin
  obtain ⟨s, hlo, hhi, hmp, -⟩ := hrec _ hstart hwin
  obtain ⟨r', rfl⟩ := hmp.1
  have hcarrier : Restated.ProposerCarrierAtOn M S (notHeldAt Sched) r' := by
    intro k hk
    exact mem_notHeldAt.2 (hmp.2 k hk _ le_rfl)
  have hbounds : r + 2 ≤ r' ∧ r' ≤ r + gap := by
    have hΔ := S.E.Δ_pos
    have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
    have hP : (0 : Int) < 4 * S.E.Δ * (S.hc.R : Int) := by positivity
    change M.proposal_time S.E ((M.opening_slot S.hc r)) + 2 * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)) ≤
        M.proposal_time S.E ((M.opening_slot S.hc r')) at hlo
    change M.proposal_time S.E ((M.opening_slot S.hc r')) ≤
      M.proposal_time S.E ((M.opening_slot S.hc r)) + (gap : Int) * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)) at hhi
    rw [← facts.gr.opening_eq_proposal_time, ← facts.gr.opening_eq_proposal_time] at hlo hhi
    have hL : (Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0) = 4 * S.E.Δ * (S.hc.R : Int) := by
      show (M.a S.hc S.E.Δ (0 + 1)) - (M.a S.hc S.E.Δ 0) = _
      rw [facts.gr.healA_succ_round]
      ring
    rw [hL] at hlo hhi
    constructor
    · by_contra hlt
      have hle : r' ≤ r + 1 := Nat.le_of_lt_succ (Nat.lt_of_not_le hlt)
      have h1 := facts.gr.opening_add S.E S.hc r' (r + 1 - r')
      rw [Nat.add_sub_cancel' hle] at h1
      have h2 := facts.gr.opening_add S.E S.hc r 1
      simp only [Nat.cast_one, one_mul] at h2
      have h3 : (0 : Int) ≤ ((r + 1 - r' : Nat) : Int) * (4 * S.E.Δ * (S.hc.R : Int)) :=
        mul_nonneg (Int.natCast_nonneg _) hP.le
      linarith
    · by_contra hlt
      have hle : r + gap + 1 ≤ r' := Nat.lt_of_not_le hlt
      have h1 := facts.gr.opening_add S.E S.hc (r + gap + 1) (r' - (r + gap + 1))
      rw [Nat.add_sub_cancel' hle] at h1
      have h2 := facts.gr.opening_add S.E S.hc r (gap + 1)
      rw [← Nat.add_assoc] at h2
      simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] at h2
      have h3 : (0 : Int) ≤ ((r' - (r + gap + 1) : Nat) : Int) * (4 * S.E.Δ * (S.hc.R : Int)) :=
        mul_nonneg (Int.natCast_nonneg _) hP.le
      linarith
  exact ⟨r', le_trans (Nat.le_add_right r 2) hbounds.1, hbounds.2, hcarrier⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- If `rho`'s events are a prefix of `rho'`'s, every emission of `rho` read along a sequence of
    worlds `W` is an emission of `rho'` read along the same `W`, at the same validator and instant. -/
theorem emits_of_prefix (facts : Record.Facts M) (S : Setup V) {rho rho' : Record.Run V}
    (h : rho.events <+: rho'.events) {W : Nat → V → M.N} {v : V} {o : NamedObject V} {t : Int}
    (he : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v o t) :
    Restated.Vocabulary.Execution.NamedRun.emits M S rho' W v o t := by
  obtain ⟨i, hi, out, hout, hW, ho⟩ := he
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hi
  refine ⟨i, ?_, out, hout, hW, ho⟩
  obtain ⟨l, hl⟩ := h
  rw [← hl, List.getElem?_append_left hlt]
  exact hi

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For `m ≤ n`, the events of the run of the first `n` sts steps are those of the run of the first
    `m` steps followed by events at instants no earlier than `x[m + 1].time`. -/
theorem runEvents_append_late (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {m n : Nat} (h : m ≤ n) :
    ∃ l : List (Record.Event V), Restated.runEvents M S Sched x n = Restated.runEvents M S Sched x m ++ l ∧
      ∀ e ∈ l, (x[m + 1].time : Int) ≤ Record.Event.time e := by
  induction n, h using Nat.le_induction with
  | base => exact ⟨[], (List.append_nil _).symm, fun e he => absurd he List.not_mem_nil⟩
  | succ n hmn ih =>
      obtain ⟨l, hl, hlate⟩ := ih
      refine ⟨l ++ Restated.stepEvents M S Sched x n, ?_, ?_⟩
      · rw [show Restated.runEvents M S Sched x (n + 1)
              = Restated.runEvents M S Sched x n ++ Restated.stepEvents M S Sched x n from rfl, hl,
          List.append_assoc]
      · intro e he
        rcases List.mem_append.1 he with he | he
        · exact hlate e he
        · obtain ⟨v₀, -, hmem⟩ := List.mem_flatMap.1 he
          rw [Restated.actionEvents_time facts S Sched x v₀ n hmem]
          exact_mod_cast Restated.time_mono facts S Sched x (show m + 1 ≤ n + 1 by omega)

end

end DecoupledConsensusModel.Sts.Restated
