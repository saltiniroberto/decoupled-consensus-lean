import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.RunAll
import Model.Conditions.Generic
import Model.Record.Wiring
import Proofs.Claims.VocabularyAssumptionsLemmas

/-!
# Real time along the sts execution

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: delivery,
adversarial and forward steps do not move real time, every event a step contributes carries the real
time of the next configuration, and real time takes every value up to the one it has reached.
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

/-- A delivery step does not move real time. -/
theorem deliver_time (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k : Nat} {p : V}
    {m : SignedMsg V (NamedObject V)} (hl : x.lbl k = AtomicAction.deliver p m) :
    x[k + 1].time = x[k].time := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  rw [hs.2.2]; rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- An adversarial step does not move real time. -/
theorem adversarial_time (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k : Nat} {p : V} {m : NamedObject V}
    (hl : x.lbl k = AtomicAction.adversarial p m) :
    x[k + 1].time = x[k].time := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  rw [hs.2]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A forward step does not move real time. -/
theorem forward_time (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k : Nat} {p : V}
    {m : SignedMsg V (NamedObject V)}
    (hl : x.lbl k = AtomicAction.forward p m) :
    x[k + 1].time = x[k].time := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  rw [hs.2]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- An event a validator contributes at step `k` carries the real time of the configuration after
    `k + 1` steps. -/
theorem actionEvents_time (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v₀ : V) (k : Nat) {e : Record.Event V}
    (he : e ∈ Record.actionEventsOf M S Sched v₀ (x[k].time : Int) (x.lbl k)) :
    Record.Event.time e = (x[k + 1].time : Int) :=
  (Record.time_of_mem_actionEventsOf M S Sched x k he).1.symm

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `d` is at most the real time after `n` steps, some step `i ≤ n` has real time exactly `d`. -/
theorem exists_step_at_time (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) :
    ∀ (n : Nat) {d : Nat}, d ≤ x[n].time → ∃ i ≤ n, x[i].time = d := by
  intro n
  induction n with
  | zero =>
      intro d hd
      have h0 : x[0].time = 0 := x.init.1
      rw [h0] at hd
      exact ⟨0, le_rfl, by omega⟩
  | succ n ih =>
      intro d hd
      by_cases hle : d ≤ x[n].time
      · obtain ⟨i, hi, hid⟩ := ih hle
        exact ⟨i, Nat.le_succ_of_le hi, hid⟩
      · have hstep := atomic_time_stepwise x n
        exact ⟨n + 1, le_rfl, by omega⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- On an execution that reaches every instant, every natural number `d` is the real time of some
    configuration. -/
theorem exists_step_at_instant (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} (hreach : Restated.ReachesEveryInstant M x) (d : Nat) :
    ∃ i : Nat, x[i].time = d := by
  obtain ⟨n, hn⟩ := hreach (d : Int)
  obtain ⟨i, -, hi⟩ := Restated.exists_step_at_time facts S Sched x n (by exact_mod_cast hn)
  exact ⟨i, hi⟩

end

end DecoupledConsensusModel.Sts.Restated
