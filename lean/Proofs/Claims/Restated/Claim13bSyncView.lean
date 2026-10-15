import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.RunAll
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bSyncView

/-!
# Views and synchrony from wake

A view never loses a message, a delivery puts the message in the receiver's view at once, and the
delivery and view forms of `SynchronyFromWake` for a receiver awake from the sending step. Stated
over a model `M : Record.Model V`.
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

/-- A message in validator `w`'s view after `a` steps is in its view after every later step `b`. -/
theorem mem_view_mono (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {w : V}
    {sm : SignedMsg V (NamedObject V)} {a b : Nat} (hab : a ≤ b)
    (h : sm ∈ x[a][w].view) : sm ∈ x[b][w].view := by
  classical
  induction b, hab using Nat.le_induction with
  | base => exact h
  | succ n hn ih =>
      have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl n) x[n] x[n + 1] := x.step n
      refine AtomicStep.elim
        (motive := fun _ d d' => sm ∈ d[w].view → sm ∈ d'[w].view)
        hs ?_ ?_ ?_ ?_ ?_ ih
      · intro d t wk tk _ _ _ hh
        rw [tickAllAwakeUpdate_getElem_view]
        exact hh
      · intro d q m res _ _ hh
        rw [applyNodeStepResult_view]
        by_cases hq : q = w
        · subst hq
          rw [receive_view_self]
          exact Finset.mem_insert_of_mem hh
        · rw [show (receive q m d)[w] = d[w] from by rw [receive_getElem, if_neg hq]]
          exact hh
      · intro d q ev res _ _ hh
        rw [applyNodeStepResult_view]
        exact hh
      · intro d q m _ hh
        exact hh
      · intro d q m _ hh
        exact hh

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The step that delivers a message to a validator leaves that message in that validator's view. -/
theorem mem_view_succ_of_deliver (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {d : Nat} {w : V}
    {sm : SignedMsg V (NamedObject V)} (hl : x.lbl d = AtomicAction.deliver w sm) :
    sm ∈ x[d + 1][w].view := by
  classical
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl d) x[d] x[d + 1] := x.step d
  rw [hl] at hs
  refine AtomicStep.elim
    (motive := fun a _ d' => a = AtomicAction.deliver w sm → sm ∈ d'[w].view)
    hs ?_ ?_ ?_ ?_ ?_ rfl
  · intro c t wk tk _ _ _ hcon
    exact absurd hcon (by simp)
  · intro c q m res _ _ hq
    injection hq with hq1 hq2
    subst hq1
    subst hq2
    rw [applyNodeStepResult_view, receive_view_self]
    exact Finset.mem_insert_self _ _
  · intro c q ev res _ _ hcon
    exact absurd hcon (by simp)
  · intro c q m _ hcon
    exact absurd hcon (by simp)
  · intro c q m _ hcon
    exact absurd hcon (by simp)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A validator awake at every time from `x[k].time` through `D` is awake at every time from
    `x[k + 1].time` through `D`. -/
theorem awakeThroughout_succ_of_step (facts : Record.Facts M) (S : Setup V) {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {k : Nat} {w : V} {D : Int}
    (haw : w ∈ Sched.awakeThroughout (x[k].time : Int) D) :
    w ∈ Sched.awakeThroughout (x[k + 1].time : Int) D := by
  have h01 : (x[k].time : Int) ≤ (x[k + 1].time : Int) := by
    exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_succ k)
  have hsub : Sched.awakeThroughout (x[k].time : Int) D ≤
      Sched.awakeThroughout (x[k + 1].time : Int) D :=
    Finset.inf_mono (Finset.Icc_subset_Icc h01 le_rfl)
  exact Finset.mem_of_subset hsub haw

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `SynchronyFromWake`, whatever an honest validator puts on the wire at step `k` is
    delivered, at a step after `k` and strictly before the deadline `max x[k].time t_GST + Δ`, to
    every validator awake at every time from `x[k].time` through that deadline. -/
theorem synchronyFromWake_from_step (facts : Record.Facts M) (S : Setup V) {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} (hsync : Restated.SynchronyFromWake M S x)
    {k : Nat} {w : V} {sm : SignedMsg V (NamedObject V)}
    (hsend : Restated.HonestSendAt M S x k sm)
    (haw : w ∈ Sched.awakeThroughout (x[k].time : Int)
      (max (x[k].time : Int) S.E.t_GST + S.E.Δ)) :
    ∃ d : Nat, k < d ∧ x.lbl d = AtomicAction.deliver w sm ∧
      (x[k].time : Int) ≤ (x[d].time : Int) ∧
      (x[d].time : Int) < max (x[k].time : Int) S.E.t_GST + S.E.Δ :=
  hsync k w sm hsend (Restated.awakeThroughout_succ_of_step facts S haw)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `SynchronyFromWake`, a message an honest validator put on the wire at step `k` is in the
    view of every validator awake at every time from `x[k + 1].time` through the deadline
    `max x[k].time t_GST + Δ`, at every step whose time is at or after that deadline. -/
theorem synchronyFromWakeView_of_deliver_succ (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (hsync : Restated.SynchronyFromWake M S x)
    {k j : Nat} {w : V} {sm : SignedMsg V (NamedObject V)}
    (hsend : Restated.HonestSendAt M S x k sm)
    (haw : w ∈ Sched.awakeThroughout (x[k + 1].time : Int)
      (max (x[k].time : Int) S.E.t_GST + S.E.Δ))
    (hj : max (x[k].time : Int) S.E.t_GST + S.E.Δ ≤ (x[j].time : Int)) :
    sm ∈ x[j][w].view := by
  obtain ⟨d, hkd, hlbl, -, hlt⟩ := hsync k w sm hsend haw
  have hdj : d < j := by
    by_contra hcon
    have hle : (x[j].time : Int) ≤ (x[d].time : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_of_not_lt hcon)
    linarith
  exact Restated.mem_view_mono facts S Sched x (Nat.succ_le_of_lt hdj)
    (Restated.mem_view_succ_of_deliver facts S Sched x hlbl)

end

end DecoupledConsensusModel.Sts.Restated
