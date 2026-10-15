import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.ReceiptOutcome
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13bSyncView
import Proofs.Claims.Restated.Claim13beRoute3_23
import Proofs.Claims.Restated.Claim13beRoute3_25
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_ReceiptCallsBase
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Pool
import Model.Conditions.ProcessedFlip
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Protocol_Handlers_AcceptanceTiming
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Model.Record.Wiring

/-!
# Recorded Goldfish votes are delivered

A Goldfish vote an honest store records inside the phase is delivered to every validator not held at
the deadline, and the timing of a Goldfish vote's acceptance. Stated over a model
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
open DecoupledConsensusModel.Protocol

/-- Under `SynchronyFromWake`: if a Goldfish vote `u` enters `v`'s pool of `u`'s slot at step `i`,
    `v` is honest through that step, the step starts inside the phase, the deadline (one delay after
    the later of `x[i + 1].time` and `t_GST`) is inside the phase, and the adversary does not hold
    `w` at the deadline, then some step at or after `x[i + 1].time` and strictly before the deadline
    delivers to `w` the message `⟨v, u⟩`. -/
theorem gfVote_delivered_of_recorded_phase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hsync : Restated.SynchronyFromWake M S x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE : Int}
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    {i : Nat} {v w : V} {u : GoldfishVote V}
    (h0 : u ∉ (M.store_pool (x[i][v].st).st.core u.slot))
    (h1 : u ∈ (M.store_pool (x[i + 1][v].st).st.core u.slot))
    (hvh : Restated.HonestThrough M Sched x i v) (hi : tGAT ≤ (x[i].time : Int))
    (hdead : max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ ≤ tE)
    (hw : w ∉ Sched.adv (max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ)) :
    ∃ d : Nat, (x[i + 1].time : Int) ≤ (x[d].time : Int) ∧
      (x[d].time : Int) < max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ ∧
      x.lbl d = AtomicAction.deliver w ⟨v, NamedObject.gfVote u⟩ := by
  have hf0 : Restated.Vocabulary.Execution.Object.processed M (x[i][v].st).st
      (NamedObject.gfVote u) = false :=
    decide_eq_false (fun h => h0 ((facts.sto.mem_store_pool_iff _ _ _).2 h))
  have hf1 : Restated.Vocabulary.Execution.Object.processed M (x[i + 1][v].st).st
      (NamedObject.gfVote u) = true :=
    decide_eq_true ((facts.sto.mem_store_pool_iff _ _ _).1 h1)
  have hti : (x[i].time : Int) ≤ (x[i + 1].time : Int) := by
    exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_succ i)
  have hmax : max (x[i].time : Int) S.E.t_GST ≤ max (x[i + 1].time : Int) S.E.t_GST :=
    max_le_max hti (le_refl _)
  have hwin : w ∈ Sched.awakeThroughout (x[i].time : Int)
      (max (x[i].time : Int) S.E.t_GST + S.E.Δ) :=
    awakeThroughout_shrink Sched (awakeThroughout_phase Sched hawake hmono hi hdead hw)
      (by linarith)
  have hsend : Restated.HonestSendAt M S x i
      (⟨v, NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V)) := by
    rcases Restated.flip_step_cases facts S Sched x hf0 hf1 with
      ⟨m, hl, -, -, hcase⟩ | ⟨τ, hl, haw, out₁, hout, hst, hcase⟩
    · have ho : NamedObject.gfVote u ∈ relayedObjects m.msg := by
        rw [mem_relayedObjects_iff]
        rcases hcase with heq | ⟨B, hB, hcc⟩
        · exact Or.inl heq.symm
        · rw [hB]; exact Or.inr (Restated.carries_of_carriedCall facts _ _ B hcc)
      exact Restated.honestSendAt_of_deliver_relay facts S Sched x hl ho
        (Restated.receipt_outcome_of_flip facts S Sched x hl hf0 hf1)
    · rcases hcase with hmem | ⟨B, hem, hcc⟩
      · exact ⟨Restated.mem_sent_diff_of_tick_of_state facts S Sched x hl haw
          (fun o₁ o₂ h₁ h₂ h12 =>
            facts.nd.tick_send_eq_of_state (Setup.alwaysAwake S) v _ _ o₁ o₂ h₁ h₂ h12)
          hout hst hmem,
          hvh (x[i].time : Int) (le_refl _)⟩
      · exfalso
        obtain ⟨⟨j, hj⟩, -, -⟩ := hcc
        exact h0 (Restated.mem_pool_of_mem_tick_block facts S Sched x i v (τ : Int) out₁ hout
          hem (List.mem_of_getElem? hj))
  obtain ⟨d, hid, hlbl, -, hlt⟩ := Restated.synchronyFromWake_from_step facts S hsync hsend hwin
  refine ⟨d, ?_, by linarith, hlbl⟩
  exact_mod_cast Restated.time_mono facts S Sched x (show i + 1 ≤ d by omega)

end

section
open DecoupledConsensusModel.Protocol
set_option autoImplicit false
open Internal
open Execution
open scoped DC

/-- When the `i`-th event of `rho` is a wake of `v`, `v`'s store in every world that event leads to
    from `w₁` is `v`'s store in `w₁`. -/
private theorem stateBefore_wake_st₃₇ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    {i : Nat} {v : V} {t : Time} (hi : rho.events[i]? = some (.wake v t)) (w₁ w₂ : V → M.N)
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

/-- In a run sorted by key and inside its horizon, for every path `W` of the run, if `v` accepts the
    Goldfish vote `u` at index `i` at `t` along `W`, then either the event is a delivery at `t` and
    `u`'s stamp in `v`'s store in `W (i + 1)` is the clock of `v`'s store in `W i`, whose slot is
    not before `u`'s, or the event is `v`'s tick at `t`, `u`'s stamp in `v`'s store in `W (i + 1)`
    is `t`, and the slot of `t` is not before `u`'s. -/
theorem Vocabulary.Protocol.acceptsAt_gfVote_time_shape_of_fields (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (hin : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon)
    {v : V} {i : Nat} {u : GoldfishVote V} {t : Time}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hacc : Restated.Vocabulary.Execution.Run.acceptsAt M S rho W i v (Object.gfVote u) t) :
    (∃ o : Object V,
        rho.events[i]? = some (Record.Event.deliver v o t) ∧
        (W (i + 1) v).st.core.timestamp_vote u = some ((W i v).st.core.t : Stamp) ∧
        ¬ (W i v).st.core.s < u.slot) ∨
      (rho.events[i]? = some (Record.Event.tick v t) ∧
        (W (i + 1) v).st.core.timestamp_vote u = some (t : Stamp) ∧
        ¬ S.E.slotOf t < u.slot) := by
  have hpre : u ∉ (W i v).st.core.gf_votes u.slot := by
    have h := hacc.2.1
    simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not] at h
    exact h
  have hpost : u ∈ (W (i + 1) v).st.core.gf_votes u.slot := by
    have h := hacc.2.2
    simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] at h
    exact h
  have hs : Restated.Vocabulary.Protocol.PoolStamps M (W i v).st.core :=
    Restated.Vocabulary.Protocol.poolStamps_stateBefore_of_fields facts S hsorted hin v i (W i)
      (hW i).1
  obtain ⟨e, he, hnode, htime⟩ := hacc.1.2
  cases e with
  | deliver w o p =>
      simp only [Record.Event.node, Record.Event.time] at hnode htime
      subst w
      subst p
      rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho he (W i) (hW i).1
          (W (i + 1)) (hW i).2 with hproc | ⟨-, hsame⟩
      · have hstep := facts.ndRun.voteInsertStep_process S (W i v) o (W (i + 1) v) hproc
        exact Or.inl ⟨o, he, hstep.new_stamp hs u hpre hpost, hstep.not_future hs u hpre hpost⟩
      · rw [hsame] at hpost
        exact absurd hpost hpre
  | tick w p =>
      simp only [Record.Event.node, Record.Event.time] at hnode htime
      subst w
      subst p
      have hle : (W i v).st.core.t ≤ t := by
        exact
          Restated.Vocabulary.Protocol.store_time_le_event_time_of_fields facts S hsorted hin he v
            (W i) (hW i).1
      rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_tick facts S rho he (W i) (hW i).1
          (W (i + 1)) (hW i).2 with ⟨out, hout, hw⟩ | ⟨-, hsame⟩
      · have hstep := facts.ndRun.voteInsertStep_onTickEmit S v (W i v) t out hout hle
        rw [← hw] at hstep
        exact Or.inr ⟨he, hstep.new_stamp hs u hpre hpost, hstep.not_future hs u hpre hpost⟩
      · rw [hsame] at hpost
        exact absurd hpost hpre
  | wake w p =>
      simp only [Record.Event.node] at hnode
      subst w
      rw [stateBefore_wake_st₃₇ facts S rho he (W i) (W (i + 1)) (hW i).2] at hpost
      exact absurd hpost hpre

end

end DecoupledConsensusModel.Sts.Restated
