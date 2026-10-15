import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.VocabularyAssumptionsLemmas
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_22

/-!
# Time and tick properties of the run built from an execution

The run of the first `n` steps of an execution, with any declared honest set, has a non-negative
horizon, events inside the horizon, ticks at public instants, a tick at every awake validator, and
each tick event at one index only. Stated over a model `M : Record.Model V`.
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

/-- The horizon `x[n].time` of the run of the first `n` steps, with honest set `H`, is at least `0`. -/
theorem horizon_nonneg_runAll_withHonest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (H : Finset V) (n : Nat) :
    0 ≤ ({ Restated.runAll M S Sched x v n with honest := H } : Record.Run V).horizon :=
  Int.natCast_nonneg _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- An event contributed by step `k` is at a time from `0` to `x[k + 1].time`. -/
theorem time_le_of_mem_actionEvents (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (k : Nat) {v₀ : V} {e : Record.Event V}
    (he : e ∈ Record.actionEventsOf M S Sched v₀ (x[k].time : Int) (x.lbl k)) :
    0 ≤ Record.Event.time e ∧ Record.Event.time e ≤ (x[k + 1].time : Int) := by
  cases e with
  | wake v₁ t' =>
      obtain ⟨τ, hlbl, hτ, -, -, -⟩ := Restated.wake_of_mem_actionEventsOf he
      have h2 := (Restated.tickAllAwake_time facts S Sched x hlbl).2
      show 0 ≤ t' ∧ t' ≤ (x[k + 1].time : Int)
      rw [← hτ, h2]
      exact ⟨Int.natCast_nonneg _, le_refl _⟩
  | tick v₁ t' =>
      obtain ⟨τ, hlbl, hτ, -, -⟩ := Restated.tickAllAwake_of_mem_actionEventsOf he
      have h2 := (Restated.tickAllAwake_time facts S Sched x hlbl).2
      show 0 ≤ t' ∧ t' ≤ (x[k + 1].time : Int)
      rw [← hτ, h2]
      exact ⟨Int.natCast_nonneg _, le_refl _⟩
  | deliver v₁ o t' =>
      obtain ⟨m, -, -, h3⟩ := Restated.deliver_of_mem_actionEventsOf he
      show 0 ≤ t' ∧ t' ≤ (x[k + 1].time : Int)
      rw [h3]
      refine ⟨Int.natCast_nonneg _, ?_⟩
      exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_succ k)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every event of the run of the first `n` steps, with honest set `H`, is at a time between `0` and
    the horizon `x[n].time`. -/
theorem in_horizon_runAll_withHonest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (H : Finset V) (n : Nat) :
    ∀ e ∈ ({ Restated.runAll M S Sched x v n with honest := H } : Record.Run V).events,
      0 ≤ Record.Event.time e ∧
        Record.Event.time e ≤ ({ Restated.runAll M S Sched x v n with honest := H } : Record.Run V).horizon := by
  intro e he
  obtain ⟨k, hk, hmem⟩ := Restated.exists_step_of_mem_runEvents facts S Sched x n he
  obtain ⟨h0, h1⟩ := Restated.time_le_of_mem_actionEvents facts S Sched x k hmem
  refine ⟨h0, le_trans h1 ?_⟩
  show (x[k + 1].time : Int) ≤ (x[n].time : Int)
  exact_mod_cast Restated.time_mono facts S Sched x (Nat.succ_le_of_lt hk)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every tick event of the run of the first `n` steps, with honest set `H`, is at a public instant. -/
theorem tick_public_runAll_withHonest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (H : Finset V) (n : Nat) :
    ∀ v₀ t, Record.Event.tick v₀ t ∈ ({ Restated.runAll M S Sched x v n with honest := H } : Record.Run V).events →
      Execution.PublicTime (Setup.alwaysAwake S) t := by
  intro v₀ t he
  obtain ⟨k, -, hmem⟩ := Restated.exists_step_of_mem_runEvents facts S Sched x n he
  obtain ⟨τ, -, hτ, -, hdvd⟩ := Restated.tickAllAwake_of_mem_actionEventsOf hmem
  obtain ⟨j, hj⟩ := (emod_eq_zero_iff_publicTime S τ).1 hdvd
  refine ⟨j, ?_⟩
  rw [← hτ, hj]
  rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- In the run of the first `n` steps, whatever honest set is declared, every validator awake at a
    public instant `t` with `0 < t ≤ x[n].time` and not in `Sched.adv t` has a tick event at `t`. -/
theorem tickAtAwake_runAll_withHonest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (H : Finset V) (n : Nat) :
    TickAtAwake (Setup.alwaysAwake S) Sched { Restated.runAll M S Sched x v n with honest := H } := by
  intro v₀ t hpub ht0 htn haw hadv
  obtain ⟨j, hj⟩ := hpub
  obtain ⟨d, hd⟩ : ∃ d : Nat, t = (d : Int) := ⟨t.toNat, (Int.toNat_of_nonneg (le_of_lt ht0)).symm⟩
  have hdn : d ≤ x[n].time := by
    have : (d : Int) ≤ (x[n].time : Int) := by rw [← hd]; exact htn
    exact_mod_cast this
  obtain ⟨k, hkn, hkt⟩ := Restated.exists_step_at_time facts S Sched x n hdn
  have hd0 : d ≠ 0 := by
    intro h; rw [h] at hd; rw [hd] at ht0; exact lt_irrefl 0 ht0
  obtain ⟨i, hik, hlbl, -, -⟩ := tickAllAwake_of_time x k hkt hd0
  have hin : i < n := Nat.lt_of_lt_of_le hik hkn
  have haw' : v₀ ∈ Sched.awake (d : Int) \ Sched.adv (d : Int) := by
    rw [← hd]; exact Finset.mem_sdiff.2 ⟨haw, hadv⟩
  have hdvd : (d : Int) % S.E.Δ = 0 :=
    (emod_eq_zero_iff_publicTime S d).2 (by rw [← hd]; exact ⟨j, hj⟩)
  have hcond : v₀ ∈ Sched.awake (d : Int) \ Sched.adv (d : Int) ∧ (d : Int) % S.E.Δ = 0 :=
    ⟨haw', hdvd⟩
  have hev : (Record.Event.tick v₀ t : Record.Event V) ∈
      Record.actionEventsOf M S Sched v₀ (x[i].time : Int) (x.lbl i) := by
    rw [hlbl, hd]
    simp only [Record.actionEventsOf, List.mem_append]
    refine Or.inr ?_
    rw [if_pos hcond]
    exact List.mem_singleton_self _
  exact Restated.mem_runEvents_of_mem_actionEvents facts S Sched x n i hin v₀ _ hev

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If every validator the adversary does not hold at a time of `[tGAT, tAwakeEnd]` is awake there,
    corruption only grows, no member of `H` is held at `x[n].time`, and `x[n].time ≤ tAwakeEnd`,
    then in the run of the first `n` steps with honest set `H` every member of `H` has a tick event
    at every public instant `t` with `tGAT ≤ t`, `0 < t` and `t ≤ x[n].time`. -/
theorem tickTotalFrom_runAll_withHonest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (H : Finset V) (n : Nat) (tGAT tAwakeEnd : Int)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hmono : Sched.MonotoneCorruption)
    (hH : ∀ v₀ ∈ H, v₀ ∉ Sched.adv (x[n].time : Int))
    (hn : (x[n].time : Int) ≤ tAwakeEnd) :
    TickTotalFrom (Setup.alwaysAwake S) { Restated.runAll M S Sched x v n with honest := H } tGAT := by
  intro v₀ hv₀ t hpub hlo ht0 htn
  have htn' : t ≤ (x[n].time : Int) := htn
  have hnotadv : v₀ ∉ Sched.adv t := fun hadv => hH v₀ hv₀ (hmono t _ htn' hadv)
  have haw : v₀ ∈ Sched.awake t := hawake t hlo (le_trans htn' hn) v₀ hnotadv
  exact Restated.tickAtAwake_runAll_withHonest facts S Sched x v H n v₀ t hpub ht0 htn haw hnotadv

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `k` contributes the tick of `v₀` at `t`, then step `k` is the `tickAllAwake` step at
    `t`. -/
theorem lbl_of_tick_mem_stepEvents (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (k : Nat) {v₀ : V} {t : Int}
    (he : (Record.Event.tick v₀ t : Record.Event V) ∈ Restated.stepEvents M S Sched x k) :
    ∃ τ : Nat, x.lbl k = AtomicAction.tickAllAwake τ ∧ (τ : Int) = t := by
  obtain ⟨v₁, -, hmem⟩ := List.mem_flatMap.1 he
  obtain ⟨τ, hlbl, hτ, -, -⟩ := Restated.tickAllAwake_of_mem_actionEventsOf hmem
  exact ⟨τ, hlbl, hτ⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If steps `j` and `k` both contribute the tick of `v₀` at `t`, then `j = k`. -/
theorem step_eq_of_tick_mem_stepEvents (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {j k : Nat} {v₀ : V} {t : Int}
    (hj : (Record.Event.tick v₀ t : Record.Event V) ∈ Restated.stepEvents M S Sched x j)
    (hk : (Record.Event.tick v₀ t : Record.Event V) ∈ Restated.stepEvents M S Sched x k) : j = k := by
  obtain ⟨τ₁, hl₁, hτ₁⟩ := Restated.lbl_of_tick_mem_stepEvents facts S Sched x j hj
  obtain ⟨τ₂, hl₂, hτ₂⟩ := Restated.lbl_of_tick_mem_stepEvents facts S Sched x k hk
  have hτ : τ₁ = τ₂ := by exact_mod_cast hτ₁.trans hτ₂.symm
  subst hτ
  exact Restated.tickAllAwake_step_unique facts S Sched x hl₁ hl₂

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Two indices of the events of step `k` holding the same event are equal. -/
theorem index_eq_of_getElem_stepEvents (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (k : Nat) {j₁ j₂ : Nat}
    (h₁ : j₁ < (Restated.stepEvents M S Sched x k).length) (h₂ : j₂ < (Restated.stepEvents M S Sched x k).length)
    (heq : (Restated.stepEvents M S Sched x k)[j₁] = (Restated.stepEvents M S Sched x k)[j₂]) : j₁ = j₂ := by
  exact (List.Nodup.getElem_inj_iff (Restated.stepEvents_nodup facts S Sched x k)).mp heq

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- In the list of every validator's events of the first `n` steps, two indices holding the same
    tick event are equal. -/
theorem tick_index_unique_runEvents (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) :
    ∀ (n : Nat) {j k : Nat} (hj : j < (Restated.runEvents M S Sched x n).length)
      (hk : k < (Restated.runEvents M S Sched x n).length) {v₀ : V} {t : Int},
      (Restated.runEvents M S Sched x n)[j] = Record.Event.tick v₀ t →
      (Restated.runEvents M S Sched x n)[j] = (Restated.runEvents M S Sched x n)[k] → j = k
  | 0, j, _, hj, _, _, _, _, _ => absurd hj (by simp [Restated.runEvents])
  | n + 1, j, k, hj, hk, v₀, t, htick, heq => by
      have hsplit : Restated.runEvents M S Sched x (n + 1)
          = Restated.runEvents M S Sched x n ++ Restated.stepEvents M S Sched x n := rfl
      -- the tick of `v₀` at `t` in the earlier part is contributed by a step before `n`
      have hold : ∀ {i : Nat} (hi : i < (Restated.runEvents M S Sched x n).length),
          (Restated.runEvents M S Sched x n)[i] = Record.Event.tick v₀ t →
          (Record.Event.tick v₀ t : Record.Event V) ∉ Restated.stepEvents M S Sched x n := by
        intro i hi hti hnew
        have hmem : (Record.Event.tick v₀ t : Record.Event V) ∈ Restated.runEvents M S Sched x n := by
          rw [← hti]; exact List.getElem_mem hi
        obtain ⟨k', hk', hmem'⟩ := Restated.exists_step_of_mem_runEvents facts S Sched x n hmem
        have := Restated.step_eq_of_tick_mem_stepEvents facts S Sched x
          (Restated.mem_stepEvents_of_mem_actionEvents facts S Sched x k' hmem') hnew
        omega
      simp only [hsplit] at hj hk htick heq
      rw [List.length_append] at hj hk
      by_cases hj' : j < (Restated.runEvents M S Sched x n).length <;>
        by_cases hk' : k < (Restated.runEvents M S Sched x n).length
      · rw [List.getElem_append_left hj'] at htick heq
        rw [List.getElem_append_left hk'] at heq
        exact tick_index_unique_runEvents facts S Sched x n hj' hk' htick heq
      · rw [List.getElem_append_left hj'] at htick heq
        rw [List.getElem_append_right (Nat.le_of_not_lt hk')] at heq
        exact absurd (by rw [← htick, heq]; exact List.getElem_mem _) (hold hj' htick)
      · rw [List.getElem_append_right (Nat.le_of_not_lt hj')] at htick heq
        rw [List.getElem_append_left hk'] at heq
        exact absurd (by rw [← htick]; exact List.getElem_mem _)
          (hold hk' (heq.symm.trans htick))
      · rw [List.getElem_append_right (Nat.le_of_not_lt hj')] at heq
        rw [List.getElem_append_right (Nat.le_of_not_lt hk')] at heq
        have := Restated.index_eq_of_getElem_stepEvents facts S Sched x n _ _ heq
        omega

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- In the run of the first `n` steps, whatever honest set is declared, a tick event sits at one
    index only (`TickIndexUnique`). -/
theorem tickIndexUnique_runAll_withHonest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (H : Finset V) (n : Nat) :
    TickIndexUnique ({ Restated.runAll M S Sched x v n with honest := H } : Record.Run V) :=
  fun {_ _} {hj hk} {_ _} htick heq =>
    Restated.tick_index_unique_runEvents facts S Sched x n hj hk htick heq

end

end DecoupledConsensusModel.Sts.Restated
