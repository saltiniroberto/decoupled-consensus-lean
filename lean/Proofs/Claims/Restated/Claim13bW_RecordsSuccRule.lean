import Proofs.Claims.Restated.Claim13bW_ScheduleRule
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord

/-!
# A change of the confirmed records, read off the awake test its tick passed

`records_succ_cases_rule`: when a step changes an honest validator's `latest_stable` or
`latest_confirmed`, the step is a confirmation tick whose grade-2 awake test the validator's state
passed, and the validator was awake throughout that test's window. A module of its own, apart from
`Claim13bW_ScheduleRule.lean`, because it reads `Claim13bK_ConfirmedRecord.lean`, which imports
modules that need `Claim13bW_ScheduleRule.lean`'s lemmas.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- After step `k`, a validator `v` honest through step `k + 1` holds the `latest_stable` and
    `latest_confirmed` it held before, or step `k` is the tick at some slot `s`'s confirmation
    instant, `v` is awake and not held by the adversary there, `v`'s node state at that tick passes
    the grade-2 awake test of the round of slot `s + 1`, and, when that round's grade-2 window start
    is at or after time `0`, `v` was awake at every time from it to slot `s`'s confirmation instant.

    Variables: `v` the validator, `k` the step, `s` the slot. -/
theorem records_succ_cases_rule (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (k : Nat)
    (hhon : Restated.HonestThrough M Sched x (k + 1) v) :
    ((x[k + 1][v].st).st.core.latest_stable = (x[k][v].st).st.core.latest_stable ∧
      (x[k + 1][v].st).st.core.latest_confirmed = (x[k][v].st).st.core.latest_confirmed) ∨
    ∃ s : Slot, Restated.tickStepAt M x k (M.confirmation_time S.E s) ∧
      v ∈ Sched.awake (M.confirmation_time S.E s) \ Sched.adv (M.confirmation_time S.E s) ∧
      M.awake_for_grade2 (Setup.alwaysAwake S) v
        (Record.wakeStage M Sched (M.confirmation_time S.E s) x[k] v) (M.round_of S.hc (s + 1)) ∧
      (0 ≤ M.early S.E S.hc (M.round_of S.hc (s + 1)) .g2 - S.E.Δ →
        v ∈ Sched.awakeThroughout (M.early S.E S.hc (M.round_of S.hc (s + 1)) .g2 - S.E.Δ)
          (M.confirmation_time S.E s)) := by
  rcases Restated.records_succ_cases facts S Sched x v k with hsame | ⟨s, hm, haw⟩
  · exact Or.inl hsame
  by_cases hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[k] v) (M.round_of S.hc (s + 1))
  · refine Or.inr ⟨s, hm, haw, hrun, fun hr => ?_⟩
    obtain ⟨τ, hl, hτ⟩ := hm
    have htime : (x[k + 1].time : Int) = M.confirmation_time S.E s :=
      (Restated.tickStepAt_time facts x ⟨τ, hl, hτ⟩).1
    rw [← hτ] at hrun haw ⊢
    exact facts.ndWake.run_fact_g2_sound_at S Sched x k τ (M.round_of S.hc (s + 1)) v hl hr
      (fun t ht => hhon t (by rw [htime, ← hτ]; exact ht)) (Finset.mem_sdiff.1 haw).1 hrun
  · left
    have hdvd : M.confirmation_time S.E s % S.E.Δ = 0 := by
      rw [facts.sch.confirmation_time_eq_support_cutoff_succ]
      exact facts.sch.support_cutoff_emod_delta S (s + 1)
    obtain ⟨t', hlbl, ht'⟩ := id hm
    have hdvd' : (t' : Int) % S.E.Δ = 0 := by rw [ht']; exact hdvd
    have haw' : v ∈ Sched.awake (t' : Int) \ Sched.adv (t' : Int) := by rw [ht']; exact haw
    rcases Restated.st_succ_of_tick_awake facts S Sched x v hlbl haw' with
      ⟨out, hout, hst⟩ | ⟨-, hst⟩
    · rw [ht'] at hout
      obtain ⟨hCk, hLk⟩ :=
        facts.nd.tick_records_frame_of_not_awake_for_grade2 S v _ s out hout hrun
      rw [hst, hLk, hCk, Record.wakeStage_st facts]
      exact ⟨rfl, rfl⟩
    · rw [hst, Record.wakeStage_st facts]
      exact ⟨rfl, rfl⟩

end

end DecoupledConsensusModel.Sts.Restated
