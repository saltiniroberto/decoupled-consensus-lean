import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13b
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRecord
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13bSyncView
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.ReceiptOutcome
import Proofs.Claims.Restated.VocabularyAssumptionsLemmas
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_OutageInputs
import Proofs.Claims.Restated.Vocabulary_Execution_ReceiptCallsBase
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Admission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockAdmission
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_ReceiptCallsF1
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_BlockEmission
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_24

/-!
# Events, handles and honest sends in the run built from an execution

The states around an event of the run, processings and deliveries as handles, honest sends inside
the phase handled within one delay, and the rounds of accepted attestations against their acceptance
time. Stated over a model `M : Record.Model V`.
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

/-- A delivery event of step `k` is at `x[k].time`, which the step does not move; a tick event is at
    `x[k + 1].time`, one after `x[k].time`. -/
theorem time_of_mem_actionEvents (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (k : Nat) {v₀ : V} {e : Record.Event V}
    (he : e ∈ Record.actionEventsOf M S Sched v₀ (x[k].time : Int) (x.lbl k)) :
    (x[k + 1].time : Int) = Record.Event.time e ∧ (x[k].time : Int) ≤ Record.Event.time e ∧
      Record.Event.time e ≤ (x[k].time : Int) + 1 :=
  Record.time_of_mem_actionEventsOf M S Sched x k he

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Along the path `x` follows, the run's state at the event's validator just before an event is
    that validator's node state just before the step the event came from, or that state woken; just
    after the event it is the node state just after that step, or the event is the validator's wake
    and the state is the one before the step, woken. -/
theorem stateBefore_pair_runAll_withHonest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (H : Finset V) (n i : Nat) {e : Record.Event V}
    (he : ({ Restated.runAll M S Sched x v n with honest := H } : Record.Run V).events[i]? = some e) :
    ∃ k < n, e ∈ Record.actionEventsOf M S Sched (Record.Event.node e) (x[k].time : Int) (x.lbl k) ∧
      (Restated.runAllPath M S Sched x v n i (Record.Event.node e) = x[k][Record.Event.node e].st ∨
        Restated.runAllPath M S Sched x v n i (Record.Event.node e)
          = M.wake x[k][Record.Event.node e].st) ∧
      (Restated.runAllPath M S Sched x v n (i + 1) (Record.Event.node e)
          = x[k + 1][Record.Event.node e].st ∨
        ∃ t, e = Record.Event.wake (Record.Event.node e) t ∧
          Restated.runAllPath M S Sched x v n (i + 1) (Record.Event.node e)
            = M.wake x[k][Record.Event.node e].st) := by
  have he' : (Restated.runEvents M S Sched x n)[i]? = some e := he
  obtain ⟨k, hk, hmem, hc⟩ := Restated.runAllPath_at_event facts S Sched x v n i he'
  refine ⟨k, hk, hmem, ?_⟩
  rcases hc with ⟨t, het, hb, ha⟩ | ⟨t, het, hb, ha⟩ | ⟨o, t, het, hb, ha⟩
  · have hmem' : Record.Event.wake (Record.Event.node e) t
        ∈ Record.actionEventsOf M S Sched (Record.Event.node e) (x[k].time : Int) (x.lbl k) := by
      rw [← het]; exact hmem
    obtain ⟨τ, -, hτ, -, -, hent⟩ := Restated.wake_of_mem_actionEventsOf hmem'
    refine ⟨Or.inl hb, Or.inr ⟨t, het, ?_⟩⟩
    rw [ha, ← hτ, Record.wakeStage_coe, if_pos hent]
  · refine ⟨?_, Or.inl ha⟩
    rw [hb]
    unfold Record.wakeStage
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · exact ⟨Or.inl hb, Or.inl ha⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A direct processing of an object, read along a path `W` of the run, is a call of its handler
    along the same path. -/
theorem actualHandlesAtIndex_of_processesAtIndex (facts : Record.Facts M) {S : Setup V} {rho : Record.Run V}
    {W : Nat → V → M.N} {i : Nat} {w : V} {o : NamedObject V}
    (h : Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong M S rho W i w o) :
    Restated.Vocabulary.Execution.NamedRun.actualHandlesAtIndex M S rho W i w o := by
  cases o with
  | block B => exact h
  | gfVote u => exact Or.inl h
  | attest a => exact Or.inl h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Whatever the execution delivers to `w` at a step before `n`, `w` handles in the run, along the
    path `x` follows, at that step's time. -/
theorem handle_of_deliver_step (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (H : Finset V) (n : Nat) {d : Nat} {w : V}
    {m : SignedMsg V (NamedObject V)} (hd : d < n) (hl : x.lbl d = AtomicAction.deliver w m) :
    ∃ j : Nat, Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n)
      j w m.msg (x[d].time : Int) := by
  have hev : (Record.Event.deliver w m.msg (x[d].time : Int) : Record.Event V)
      ∈ Record.actionEventsOf M S Sched w (x[d].time : Int) (x.lbl d) := by
    rw [hl, Record.actionEventsOf, if_pos rfl]
    exact List.mem_singleton_self _
  obtain ⟨j, hj⟩ :=
    List.getElem?_of_mem (Restated.mem_runEvents_of_mem_actionEvents facts S Sched x n d hd w _ hev)
  exact ⟨j, Restated.actualHandlesAtIndex_of_processesAtIndex facts (Or.inr ⟨_, hj⟩), _, hj, rfl, rfl⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Events at indices less than the length of the run of the first `j` steps come from steps before
    `j`. -/
theorem step_lt_of_lt_length (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {j n idx : Nat} (hjn : j ≤ n)
    (hidx : idx < (Restated.runEvents M S Sched x j).length) {e : Record.Event V}
    (he : (Restated.runEvents M S Sched x n)[idx]? = some e) :
    ∃ k < j, e ∈ Record.actionEventsOf M S Sched (Record.Event.node e) (x[k].time : Int) (x.lbl k) := by
  obtain ⟨l, hl⟩ := Restated.runEvents_append facts S Sched x hjn
  rw [hl, List.getElem?_append_left hidx] at he
  exact Restated.exists_step_of_mem_runEvents facts S Sched x j (List.mem_of_getElem? he)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Events at indices from the length of the run of the first `j` steps on come from steps at or
    after `j`. -/
theorem step_ge_of_length_le (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {j : Nat} :
    ∀ {n : Nat}, j ≤ n → ∀ {idx : Nat}, (Restated.runEvents M S Sched x j).length ≤ idx →
      ∀ {e : Record.Event V}, (Restated.runEvents M S Sched x n)[idx]? = some e →
        ∃ k, j ≤ k ∧ k < n ∧
          e ∈ Record.actionEventsOf M S Sched (Record.Event.node e) (x[k].time : Int) (x.lbl k) := by
  intro n hjn
  induction n, hjn using Nat.le_induction with
  | base =>
      intro idx hidx e he
      rw [List.getElem?_eq_none hidx] at he
      exact absurd he (by simp)
  | succ n hjn ih =>
      intro idx hidx e he
      rw [show Restated.runEvents M S Sched x (n + 1)
            = Restated.runEvents M S Sched x n ++ Restated.stepEvents M S Sched x n from rfl] at he
      by_cases hlt : idx < (Restated.runEvents M S Sched x n).length
      · rw [List.getElem?_append_left hlt] at he
        obtain ⟨k, hjk, hkn, hmem⟩ := ih hidx he
        exact ⟨k, hjk, Nat.lt_succ_of_lt hkn, hmem⟩
      · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at he
        obtain ⟨v₀, -, hmem⟩ := List.mem_flatMap.1
          (List.mem_of_getElem? he : e ∈ Restated.stepEvents M S Sched x n)
        have hnode := Record.node_of_mem_actionEventsOf hmem
        exact ⟨n, hjn, Nat.lt_succ_self n, by rw [hnode]; exact hmem⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `out` is an outcome of `v`'s tick at the tick step `k`, read from the node state that tick
    reads, and its node state is the one `v` holds after the step, every object of `out`'s list is
    in `x[k + 1].sent - x[k].sent`, signed by `v`. -/
private theorem mem_sent_diff_of_tick_of_state (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {k t : Nat} {v : V}
    {o : NamedObject V}
    (hl : x.lbl k = AtomicAction.tickAllAwake t)
    (haw : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int))
    {out : M.N × List (NamedObject V)}
    (hout : M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) x[k] v) (t : Int) ⇢ out)
    (hst : x[k + 1][v].st = out.1) (ho : o ∈ out.2) :
    (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent - x[k].sent := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, w, tk, hwake, htick, hc⟩ := hs
  have hwst : (w v).state = Record.wakeStage M Sched (t : Int) x[k] v :=
    Record.wakeStage_of_TickAllAwakeWake M S Sched (hwake v)
  have hx1 : x[k + 1][v].st = (tk v).state := by
    have h2 : x[k + 1][v] = (tickAllAwakeUpdate Sched t x[k] w tk)[v] := by rw [hc]
    rw [h2, tickAllAwakeUpdate_getElem_awake (Finset.mem_sdiff.1 haw).1 (Finset.mem_sdiff.1 haw).2]
  have htk : tk v ∈ Record.reactionsOf M S v ((w v).state) (t : Int) .tick ∨
      (Record.reactionsOf M S v ((w v).state) (t : Int) .tick = ∅ ∧
        tk v = { state := (w v).state, send := 0 }) := htick v haw
  have hsend : (tk v).send = (out.2 : Multiset (NamedObject V)) := by
    rcases htk with htk | ⟨hempty, -⟩
    · simp only [Record.reactionsOf, Set.mem_setOf_eq] at htk
      obtain ⟨out', hout', htkv⟩ := htk
      rw [hwst] at hout'
      rw [htkv] at hx1 ⊢
      have h2 : out'.2 = out.2 :=
        facts.nd.tick_send_eq_of_state (Setup.alwaysAwake S) v
          (Record.wakeStage M Sched (t : Int) x[k] v) (t : Int) out' out
          hout' hout (hx1.symm.trans hst)
      show (out'.2 : Multiset (NamedObject V)) = (out.2 : Multiset (NamedObject V))
      rw [h2]
    · exfalso
      have h' : ({ state := out.1, send := (out.2 : Multiset (NamedObject V)) } :
          NodeStepResult M.N (NamedObject V)) ∈
          Record.reactionsOf M S v ((w v).state) (t : Int) .tick := by
        simp only [Record.reactionsOf, Set.mem_setOf_eq]
        exact ⟨out, by rw [hwst]; exact hout, rfl⟩
      rw [hempty] at h'
      exact h'
  have hsent : x[k + 1].sent = x[k].sent
      + (Sched.awake (t : Int) \ Sched.adv (t : Int)).sum
          (fun q => ((w q).send + (tk q).send).map (SignedMsg.mk q)) := by
    rw [hc]; rfl
  rw [hsent, add_tsub_cancel_left]
  refine Multiset.mem_sum.2 ⟨v, haw, ?_⟩
  refine Multiset.mem_map.2 ⟨o, Multiset.mem_add.2 (Or.inr ?_), rfl⟩
  rw [hsend]
  exact Multiset.mem_coe.2 ho

/-- If every delivery has an outcome from the receiver's node state before it (`hreceipt`), then
    along the path `x` follows, an object a validator emits at its own tick, or is delivered as a
    payload, is put on the wire under that validator's name by an honest send at that very step. -/
theorem honestSendAt_of_processesAtIndex (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (H : Finset V) (n : Nat)
    (hmono : Sched.MonotoneCorruption)
    -- every delivery has an outcome from the node state the receiver holds before it
    (hreceipt : ∀ (j : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
      x.lbl j = AtomicAction.deliver w sm →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[j][w].st) sm.msg ⇢ n')
    {i : Nat} {v₀ : V} {o : NamedObject V}
    (hproc : Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n)
      i v₀ o) :
    ∃ k < n, Restated.HonestSendAt M S x k (⟨v₀, o⟩ : SignedMsg V (NamedObject V)) ∧
      ∃ e : Record.Event V,
        ({ Restated.runAll M S Sched x v n with honest := H } : Record.Run V).events[i]? = some e ∧
        e ∈ Record.actionEventsOf M S Sched v₀ (x[k].time : Int) (x.lbl k) := by
  rcases hproc with ⟨t₀, he, out, hout, hW1, hem⟩ | ⟨t₀, he⟩
  · have he' : (Restated.runEvents M S Sched x n)[i]? = some (Record.Event.tick v₀ t₀) := he
    obtain ⟨k, hk, hmem, hcases⟩ := Restated.runAllPath_at_event facts S Sched x v n i he'
    rcases hcases with ⟨t₁, het, -⟩ | ⟨t₁, het, hb, ha⟩ | ⟨o₁, t₁, het, -⟩
    · cases het
    swap
    · cases het
    obtain ⟨-, htt⟩ := Record.Event.tick.inj het
    have hb' : Restated.runAllPath M S Sched x v n i v₀ = Record.wakeStage M Sched t₁ x[k] v₀ := hb
    have ha' : Restated.runAllPath M S Sched x v n (i + 1) v₀ = x[k + 1][v₀].st := ha
    have hmem' : (Record.Event.tick v₀ t₀ : Record.Event V)
        ∈ Record.actionEventsOf M S Sched v₀ (x[k].time : Int) (x.lbl k) := hmem
    obtain ⟨τ, hl, hτ, haw⟩ := Restated.tickAllAwake_of_mem_actionEventsOf hmem'
    rw [hb', ← htt, ← hτ] at hout
    rw [ha'] at hW1
    refine ⟨k, hk, ⟨mem_sent_diff_of_tick_of_state facts S Sched x hl haw hout hW1 hem, ?_⟩,
      _, he, hmem'⟩
    intro hadv
    have hle : (x[k].time : Int) ≤ (τ : Int) := by
      have := (Restated.tickAllAwake_time facts S Sched x hl).1
      omega
    exact (Finset.mem_sdiff.1 haw).2 (hmono _ _ hle hadv)
  · have he' : (Restated.runEvents M S Sched x n)[i]? = some (Record.Event.deliver v₀ o t₀) := he
    obtain ⟨k, hk, hmem, -⟩ := Restated.runAllPath_at_event facts S Sched x v n i he'
    have hmem' : (Record.Event.deliver v₀ o t₀ : Record.Event V)
        ∈ Record.actionEventsOf M S Sched v₀ (x[k].time : Int) (x.lbl k) := hmem
    obtain ⟨m, hl, hmsg, -⟩ := Restated.deliver_of_mem_actionEventsOf hmem'
    exact ⟨k, hk, Restated.honestSendAt_of_deliver_relay facts S Sched x hl
      ((mem_relayedObjects_iff m.msg o).2 (Or.inl hmsg.symm)) (hreceipt _ _ _ hl),
      _, he, hmem'⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `SynchronyFromWake`, if step `k`, starting at a time at or after `tGAT`, is an honest send
    of `sm`, one delay after that time is at most `x[n].time`, and `w` is not held at `x[n].time`,
    then `w` handles the payload of `sm` in the run, along the path `x` follows, at the time of a
    step after `k` and before `x[k].time + S.E.Δ`. -/
theorem handle_of_honestSendAt_phase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (H : Finset V) (n : Nat)
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption) {tGAT tAwakeEnd : Int}
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hn : (x[n].time : Int) ≤ tAwakeEnd)
    {k : Nat} {w : V} {sm : SignedMsg V (NamedObject V)}
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
  obtain ⟨d, hkd, hl, -, hlt⟩ := Restated.synchronyFromWake_from_step facts S hsync hsend hwin
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

/-- If every delivery has an outcome (`hreceipt`), then an object a validator processes directly at
    an event at a time `t` strictly after `tGAT`, by its own tick or as a delivered payload, is
    handled by every member of `H` at a time from `t` and before `t + S.E.Δ`, provided that delay
    ends by `x[n].time`; processing and handle are read along the path `x` follows. -/
theorem handle_of_processesAtIndex_phase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (H : Finset V) (n : Nat)
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    -- every delivery has an outcome from the node state the receiver holds before it
    (hreceipt : ∀ (j : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
      x.lbl j = AtomicAction.deliver w sm →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[j][w].st) sm.msg ⇢ n')
    {tGAT tAwakeEnd : Int}
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hn : (x[n].time : Int) ≤ tAwakeEnd)
    {i : Nat} {v₀ w : V} {o : NamedObject V} {t : Int} {e : Record.Event V}
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
  obtain ⟨d, hkd, hdt, j, hj⟩ := Restated.handle_of_honestSendAt_phase facts S Sched x v H n hsync hmono hawake
    hgst hn hsend (by linarith) (by linarith) hw
  refine ⟨(x[d].time : Int), ?_, by linarith, j, hj⟩
  have : (x[k + 1].time : Int) ≤ (x[d].time : Int) := by
    exact_mod_cast Restated.time_mono facts S Sched x (show k + 1 ≤ d by omega)
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the proposer of `B`'s slot is a member of `H` not held at `x[n].time`, then any acceptance of
    `B` at `t` in the run, along the path `x` follows, is at or after `B`'s proposal time. -/
theorem proposal_time_le_of_acceptsAt_block (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (H : Finset V) (n : Nat)
    (hmono : Sched.MonotoneCorruption) (hunf : Restated.Unforgeability M S x)
    {i : Nat} {v₀ w : V} {B : NamedBlock V} {t : Int}
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n)
      i v₀ (.block B) t)
    (hprop : S.E.proposer B.slot = w) (hw : w ∉ Sched.adv (x[n].time : Int)) :
    M.proposal_time S.E B.slot ≤ t := by
  have hW : Restated.Vocabulary.Execution.NamedRun.OnePath M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n) :=
    Restated.OnePath_runAllPath facts S Sched x v n
  obtain ⟨e, he, -, htime⟩ := hacc.1.2
  rcases hacc.1.1 with ⟨t₀, he', out, hout, hW1, hem⟩ | ⟨t₀, he'⟩
  · have hee : e = Record.Event.tick v₀ t₀ := Option.some.inj (he.symm.trans he')
    subst hee
    obtain ⟨-, ht, -⟩ := Restated.Vocabulary.Proofs.HealingSurface.emits_block_shape facts (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n) hW
      ⟨i, he', out, hout, hW1, hem⟩
    rw [← htime]
    exact le_of_eq ht.symm
  · have hee : e = Record.Event.deliver v₀ (.block B) t₀ := Option.some.inj (he.symm.trans he')
    subst hee
    have he'' : (Restated.runEvents M S Sched x n)[i]?
        = some (Record.Event.deliver v₀ (.block B) t₀) := he'
    obtain ⟨k, hk, hmem, -⟩ := Restated.runAllPath_at_event facts S Sched x v n i he''
    have hmem' : (Record.Event.deliver v₀ (.block B) t₀ : Record.Event V)
        ∈ Record.actionEventsOf M S Sched v₀ (x[k].time : Int) (x.lbl k) := hmem
    obtain ⟨sm, hl, hmsg, ht₀⟩ := Restated.deliver_of_mem_actionEventsOf hmem'
    have hs := x.step k
    rw [hl] at hs
    have hsm : sm ∈ x[k].sent := hs.1.1
    have hkn : (x[k].time : Int) ≤ (x[n].time : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_of_lt hk)
    have hwt : HonestThroughTime Sched (x[n].time : Int) w :=
      fun t' ht' hadv => hw (hmono _ _ ht' hadv)
    have hauth : NamedObject.author (NamedObject.block B) = some w := by
      have hp := Restated.Vocabulary.Protocol.proposer_eq_of_acceptsAt_block facts (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v n) hW hacc
      rw [Proofs.NamedWire.erase_proposer, Proofs.NamedWire.erase_slot] at hp
      rw [author_block, hp, ← hprop]
      rfl
    have hsent : (⟨w, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[k].sent := by
      have h := hunf.unforgeable k sm w hsm (by rw [hmsg]; exact hauth)
        (fun t' ht' => hwt t' (le_trans ht' hkn))
      rwa [hmsg] at h
    obtain ⟨k', hk', τ, hl', haw', out', hout', hem'⟩ :=
      Restated.tick_of_honest_signed_upTo facts S Sched x w (NamedObject.block B) (x[n].time : Int) hwt hunf
        hauth k hkn hsent
    obtain ⟨W', hW', hemits⟩ := Restated.emits_runAll_of_tick facts S Sched x v (Nat.lt_trans hk' hk)
      hl' haw' hout' hem'
    obtain ⟨-, hτ, -⟩ := Restated.Vocabulary.Proofs.HealingSurface.emits_block_shape facts (Setup.alwaysAwake S)
      (Restated.runAll M S Sched x v n) W' hW' hemits
    have hτk : (τ : Int) ≤ (x[k].time : Int) := by
      have h1 := (Restated.tickAllAwake_time facts S Sched x hl').2
      have h2 : x[k' + 1].time ≤ x[k].time := Restated.time_mono facts S Sched x hk'
      rw [h1] at h2
      exact_mod_cast h2
    have hproposal : M.proposal_time S.E B.slot = (τ : Int) := hτ.symm
    rw [hproposal, ← htime]
    show (τ : Int) ≤ t₀
    rw [ht₀]
    exact hτk

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A row the admission of `incoming` adds to the store's rows of its round is of a round at most
    the round of the store's slot. -/
theorem round_floor_of_new_row (facts : Record.Facts M) (hc : Protocol.HealConfig) (st : M.NS)
    (incoming a : NamedAttestation V) (hpre : a ∉ st.sg_rows a.round)
    (hpost : a ∈ (M.admit_row hc st incoming).sg_rows a.round) :
    a.round ≤ (M.round_of hc st.core.s) := by
  have heq : a = incoming :=
    (facts.hd.admit_row_mem_cases hc st incoming a hpost).resolve_left hpre
  subst incoming
  by_contra hne
  have hfuture : (M.round_of hc st.core.s) < a.round := Nat.lt_of_not_ge hne
  have hcore : M.on_sg_vote hc st.core a.erase = st.core :=
    facts.hd.on_sg_vote_of_rejected hc st.core a.erase
      (Or.inr (Or.inl (by rw [Sts.namedAttestation_erase_round]; exact hfuture)))
  rw [facts.hd.admit_row_of_core_noop hc st a hcore] at hpost
  exact hpre hpost

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A row a fold of row admissions adds is of a round at most the round of the store's slot. -/
theorem round_floor_of_new_rows (facts : Record.Facts M) (hc : Protocol.HealConfig) (st : M.NS)
    (rows : List (NamedAttestation V)) (a : NamedAttestation V) (hpre : a ∉ st.sg_rows a.round)
    (hpost : a ∈ (M.admit_rows hc st rows).sg_rows a.round) :
    a.round ≤ (M.round_of hc st.core.s) := by
  have hslot : ∀ (l : List (CombinedAttestation V)) (c : M.S),
      (l.foldl (M.on_sg_vote hc) c).s = c.s := by
    intro l
    induction l with
    | nil => intro c; rfl
    | cons r l ih =>
        intro c
        rw [List.foldl_cons, ih, facts.hd.on_sg_vote_slot]
  obtain ⟨j, -, -, hpre', hpost'⟩ := facts.hd.admit_rows_new_marker hc st rows a hpre hpost
  have hf := Restated.round_floor_of_new_row facts hc (M.admit_rows hc st (rows.take j)) a a hpre' hpost'
  rw [facts.hd.sameCore_s (facts.hd.admit_rows_core hc st (rows.take j)), hslot] at hf
  exact hf

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A row the block handler adds is of a round at most the round of the store's slot. -/
theorem round_floor_of_new_block_row (facts : Record.Facts M) (S : Setup V) (st : M.NS)
    (B : NamedBlock V) (a : NamedAttestation V) (hpre : a ∉ st.sg_rows a.round)
    (hpost : a ∈
      (M.on_block_with .alsoCarried S.E S.hc S.cfg st B).sg_rows a.round) :
    a.round ≤ (M.round_of S.hc st.core.s) := by
  have hpreCore : a ∉
      (M.ns_process_block_core S.E S.hc S.cfg st B).sg_rows a.round := by
    simpa only [facts.hd.process_block_core_sg_rows_eq] using hpre
  by_cases hcond : B ∉ st.bodies ∧
      B ∈ (M.ns_process_block_core S.E S.hc S.cfg st B).bodies
  · rw [facts.hd.on_block_with_of_new .alsoCarried S.E S.hc S.cfg st B hcond.1 hcond.2] at hpost
    have hf := Restated.round_floor_of_new_rows facts S.hc _ B.attestations a hpreCore hpost
    rw [(facts.hd.process_block_clock S.E S.hc S.cfg st B).2] at hf
    exact hf
  · rw [facts.hd.on_block_with_of_not_new .alsoCarried S.E S.hc S.cfg st B hcond] at hpost
    exact False.elim (hpreCore hpost)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

open scoped DC in
/-- When the `i`-th event of `rho` is a wake of `v`, `v`'s store in every world that event leads to
    from `w₁` is `v`'s store in `w₁`. -/
private theorem stateBefore_wake_st₂₄ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    {i : Nat} {v : V} {t : DecoupledConsensusModel.Time}
    (hi : rho.events[i]? = some (.wake v t)) (w₁ w₂ : V → M.N)
    (hw₂ : w₂ ∈ ((rho.events.drop i).take (i + 1 - i)).foldlM (Record.worldStepOf M S) w₁) :
    (w₂ v).st = (w₁ v).st := by
  have hl : (rho.events.drop i).take (i + 1 - i) = [Record.Event.wake v t] := by
    rw [Nat.add_sub_cancel_left, List.take_one, List.head?_drop, hi]
    rfl
  rw [hl, List.foldlM_cons, Set.bind_def] at hw₂
  obtain ⟨w', hw', h2⟩ := Set.mem_iUnion₂.mp hw₂
  have h2' : w₂ = w' := h2
  subst h2'
  have hw : w₂ = Function.update w₁ v (M.wake (w₁ v)) := hw'
  rw [hw, Function.update_self, (facts.nd.wake_st_record _).1]

/-- Along a path `W` of the run, an attestation accepted at a tick at `ta` is of a round at most the
    round of the slot of `ta`; one accepted at a delivery is of a round at most the round of the
    slot of the accepting store in `W` before the event. -/
theorem round_floor_of_acceptsAt_attest (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {i : Nat} {source : V} {a : NamedAttestation V} {ta : Int}
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i source (.attest a) ta) :
    (∃ _he : rho.events[i]? = some (.tick source ta),
      a.round ≤ (M.round_of S.hc (S.E.slotOf ta))) ∨
    (∃ o : NamedObject V, ∃ _he : rho.events[i]? = some (.deliver source o ta),
      a.round ≤ (M.round_of S.hc (W i source).st.core.s)) := by
  have hpre : a ∉ (W i source).st.sg_rows a.round :=
    of_decide_eq_false hacc.2.1
  have hpost : a ∈ (W (i + 1) source).st.sg_rows a.round :=
    of_decide_eq_true hacc.2.2
  obtain ⟨e, he, hnode, htime⟩ := hacc.1.2
  cases e with
  | wake v t =>
    change v = source at hnode
    subst v
    rw [stateBefore_wake_st₂₄ facts S rho he (W i) (W (i + 1)) (hW i).2] at hpost
    exact absurd hpost hpre
  | tick v t =>
    change v = source at hnode
    change t = ta at htime
    subst v
    subst t
    refine Or.inl ⟨he, ?_⟩
    rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_tick facts S rho he (W i) (hW i).1
        (W (i + 1)) (hW i).2 with ⟨out, hout, hW1⟩ | ⟨-, hW1⟩
    · rw [hW1] at hpost
      rcases Restated.Vocabulary.Proofs.NamedReceiptCallsF1.tick_new_full_row_origin facts S source
          (W i source) ta out hout a hpre hpost with hem' | ⟨B, _, hpre0, hpost0⟩
      · have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W source (.attest a) ta :=
          ⟨i, he, out, hout, hW1, hem'⟩
        obtain ⟨_, _, _, _, _, _, _, _, ht, _⟩ :=
          Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_stages facts S rho W hW hemit
        rw [ht, Restated.Vocabulary.Proofs.HealingLemmas.round_of_slotOf_a facts S a.round]
      · have h := Restated.round_floor_of_new_block_row facts S
          (M.ns_setClock S.E (W i source).st ta)
          B a hpre0 hpost0
        rw [facts.hd.Sts_setClock_core_s] at h
        exact h
    · rw [hW1] at hpost
      exact absurd hpost hpre
  | deliver v o t =>
    change v = source at hnode
    change t = ta at htime
    subst v
    subst t
    refine Or.inr ⟨o, he, ?_⟩
    rw [Restated.Vocabulary.Proofs.NamedReceiptCallsBase.delivery_result facts S rho he (W i) (hW i).1
      (Restated.receipt_outcome_of_changedOn facts S hW he
        (fun h => by rw [h] at hpost; exact hpre hpost)) (W (i + 1)) (hW i).2,
      facts.nd.make_grades_compatible_with_finalized_sg_rows] at hpost
    cases o with
    | block B =>
        rw [facts.nd.process_block] at hpost
        exact Restated.round_floor_of_new_block_row facts S _ B a hpre hpost
    | gfVote u =>
        rw [facts.nd.process_gfVote, facts.hd.ns_with_core_sg_rows S.E _ u _ rfl] at hpost
        exact False.elim (hpre hpost)
    | attest incoming =>
        rw [facts.nd.process_attest] at hpost
        exact Restated.round_floor_of_new_row facts S.hc _ incoming a hpre hpost

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- In the run of the first `n` steps, an attestation accepted at `t`, along the path `x` follows,
    has its round's opening at or before `t`. -/
theorem opening_le_of_acceptsAt_attest_runAll_withHonest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (H : Finset V) (n : Nat)
    {i : Nat} {source : V} {a : NamedAttestation V} {t : Int}
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n)
      i source (.attest a) t) :
    M.opening S.E S.hc a.round ≤ t := by
  have hW : Restated.Vocabulary.Execution.NamedRun.OnePath M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n) :=
    Restated.OnePath_runAllPath facts S Sched x v n
  have hslot_of_round : ∀ {s : Slot}, a.round ≤ (M.round_of S.hc s) →
      (M.opening_slot S.hc a.round) ≤ s :=
    fun hq => facts.gr.opening_slot_le_of_le_round_of S.hc hq
  have hopening : M.opening S.E S.hc a.round = slotStart S.E.Δ (M.opening_slot S.hc a.round) := by
    rw [facts.gr.opening_eq_proposal_time, facts.sch.Γ_0_eq_proposal_time]
  rcases Restated.round_floor_of_acceptsAt_attest facts (Setup.alwaysAwake S) _ _ hW hacc with
    ⟨he, hf⟩ | ⟨o, he, hf⟩
  · have he' : (Restated.runEvents M S Sched x n)[i]? = some (Record.Event.tick source t) := he
    obtain ⟨k, -, hmem, -⟩ := Restated.runAllPath_at_event facts S Sched x v n i he'
    obtain ⟨hk1, -, -⟩ := Restated.time_of_mem_actionEvents facts S Sched x k hmem
    have ht0 : (0 : Int) ≤ t := by
      have : (x[k + 1].time : Int) = t := hk1
      rw [← this]; exact Int.natCast_nonneg _
    rw [hopening]
    exact slotStart_le_of_le_slotOf S ht0 (hslot_of_round hf)
  · have he' : (Restated.runEvents M S Sched x n)[i]? = some (Record.Event.deliver source o t) := he
    obtain ⟨k, -, hmem, hcases⟩ := Restated.runAllPath_at_event facts S Sched x v n i he'
    rcases hcases with ⟨t₁, het, -⟩ | ⟨t₁, het, -⟩ | ⟨o₁, t₁, het, hst0, -⟩
    · cases het
    · cases het
    have hmem' : (Record.Event.deliver source o t : Record.Event V)
        ∈ Record.actionEventsOf M S Sched source (x[k].time : Int) (x.lbl k) := hmem
    obtain ⟨m, -, -, ht⟩ := Restated.deliver_of_mem_actionEventsOf hmem'
    have hst0' : Restated.runAllPath M S Sched x v n i source = x[k][source].st := hst0
    rw [hst0'] at hf
    have hs := hslot_of_round hf
    rw [Restated.slotOfClock_sts facts S Sched x k source] at hs
    rw [hopening, ht]
    calc slotStart S.E.Δ ((M.opening_slot S.hc a.round))
        ≤ (x[k][source].st).st.core.t :=
          slotStart_le_of_le_slotOf S (Restated.clock_nonneg_sts facts S Sched x k source) hs
      _ ≤ (x[k].time : Int) := Restated.clock_le_time_sts facts S Sched x k source

end

end DecoupledConsensusModel.Sts.Restated
