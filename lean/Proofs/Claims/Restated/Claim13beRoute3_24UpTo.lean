import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bSyncViewUpTo
import Proofs.Claims.Restated.Claim13beRoute3_24
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.ReceiptOutcome
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.RunAll
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Record.Wiring

/-!
# Honest sends handled within one delay, with synchrony up to the deadline

An honest send or direct processing inside the phase is handled by every member of `H` within one
delay, with synchrony assumed only up to the end of that delay. Stated over a model
`M : Record.Model V`.
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

/-- Under `SynchronyFromWakeBefore` up to `x[k].time + S.E.Δ`, if step `k`, starting at a time at or
    after `tGAT`, is an honest send of `sm`, one delay after that time is at most `x[n].time`, and
    `w` is not held at `x[n].time`, then `w` handles the payload of `sm` in the run, along the path
    `x` follows, at the time of a step after `k` and before `x[k].time + S.E.Δ`. -/
theorem handle_of_honestSendAt_phase_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (H : Finset V) (n : Nat) {k : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x ((x[k].time : Int) + S.E.Δ))
    (hmono : Sched.MonotoneCorruption) {tGAT tAwakeEnd : Int}
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hn : (x[n].time : Int) ≤ tAwakeEnd)
    {w : V} {sm : SignedMsg V (NamedObject V)}
    (hsend : Restated.HonestSendAt M S x k sm) (hk : tGAT ≤ (x[k].time : Int))
    (hdl : (x[k].time : Int) + S.E.Δ ≤ (x[n].time : Int))
    (hw : w ∉ Sched.adv (x[n].time : Int)) :
    ∃ d : Nat, k < d ∧ (x[d].time : Int) < (x[k].time : Int) + S.E.Δ ∧
      ∃ j : Nat, Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n)
        j w sm.msg (x[d].time : Int) := by
  have hmax : max (x[k].time : Int) S.E.t_GST = (x[k].time : Int) :=
    max_eq_left (le_trans hgst hk)
  have hw' : w ∉ Sched.adv ((x[k].time : Int) + S.E.Δ) := fun h => hw (hmono _ _ hdl h)
  have hwin : w ∈ Sched.awakeThroughout (x[k].time : Int)
      (max (x[k].time : Int) S.E.t_GST + S.E.Δ) := by
    rw [hmax]
    exact awakeThroughout_phase Sched hawake hmono hk (le_trans hdl hn) hw'
  -- `hsync` at the deadline `max x[k].time t_GST + Δ`
  have hsync' : Restated.SynchronyFromWakeBefore M S x
      (max (x[k].time : Int) S.E.t_GST + S.E.Δ) :=
    fun k' w' sm' hs hle haw => hsync k' w' sm' hs (le_trans hle (le_of_eq (by rw [hmax]))) haw
  obtain ⟨d, hkd, hl, -, hlt⟩ := Restated.synchronyFromWake_from_step_upTo facts S
    hsync' hsend hwin
  rw [hmax] at hlt
  have hdn : d < n := by
    by_contra hcon
    have h1 : (x[n].time : Int) ≤ (x[d].time : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_of_not_lt hcon)
    linarith
  obtain ⟨j, hj⟩ := Restated.handle_of_deliver_step facts S Sched x v H n hdn hl
  exact ⟨d, hkd, hlt, j, hj⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under synchrony up to `t + S.E.Δ`, and if every delivery has an outcome (`hreceipt`), an object
    a validator processes directly at an event at a time `t` strictly after `tGAT`, by its own tick
    or as a delivered payload, is handled by every member of `H` at a time from `t` and before
    `t + S.E.Δ`, provided that delay ends by `x[n].time`; processing and handle are read along the
    path `x` follows. -/
theorem handle_of_processesAtIndex_phase_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (H : Finset V) (n : Nat) {t : Int}
    (hsync : Restated.SynchronyFromWakeBefore M S x (t + S.E.Δ))
    (hmono : Sched.MonotoneCorruption)
    -- every delivery has an outcome from the node state the receiver holds before it
    (hreceipt : ∀ (j : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
      x.lbl j = AtomicAction.deliver w sm →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[j][w].st) sm.msg ⇢ n')
    {tGAT tAwakeEnd : Int}
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hn : (x[n].time : Int) ≤ tAwakeEnd)
    {i : Nat} {v₀ w : V} {o : NamedObject V} {e : Record.Event V}
    (hproc : Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n)
      i v₀ o)
    (he : ({ Restated.runAll M S Sched x v n with honest := H } : Record.Run V).events[i]? = some e)
    (htime : Record.Event.time e = t) (hlo : tGAT < t)
    (hdl : t + S.E.Δ ≤ (x[n].time : Int)) (hw : w ∉ Sched.adv (x[n].time : Int)) :
    ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
      ∃ j : Nat, Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n)
        j w o t' := by
  obtain ⟨k, -, hsend, e', he', hmem⟩ :=
    Restated.honestSendAt_of_processesAtIndex facts S Sched x v H n hmono hreceipt hproc
  have hee : e' = e := Option.some.inj (he'.symm.trans he)
  subst hee
  obtain ⟨hk1, hk0, hk2⟩ := Restated.time_of_mem_actionEvents facts S Sched x k hmem
  rw [htime] at hk1 hk0 hk2
  have hsync' : Restated.SynchronyFromWakeBefore M S x ((x[k].time : Int) + S.E.Δ) :=
    fun k' w' sm' hs hle haw => hsync k' w' sm' hs (le_trans hle (by linarith)) haw
  obtain ⟨d, hkd, hdt, j, hj⟩ := Restated.handle_of_honestSendAt_phase_upTo facts S Sched x v H n
    hsync' hmono hawake hgst hn hsend (by linarith) (by linarith) hw
  refine ⟨(x[d].time : Int), ?_, by linarith, j, hj⟩
  have : (x[k + 1].time : Int) ≤ (x[d].time : Int) := by
    exact_mod_cast Restated.time_mono facts S Sched x (show k + 1 ≤ d by omega)
  linarith

end

end DecoupledConsensusModel.Sts.Restated
