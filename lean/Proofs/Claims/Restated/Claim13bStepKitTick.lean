import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13b
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepKitStore
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Schedule_Alignment
import Model.Record.Wiring

/-!
# Ticks at a round's action instant

The action instant of a round and its slot, the attestation the tick there emits, and the converse
that a logged attestation of an honest validator came from that tick, stated over a model
`M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After any number of steps, every validator's grade view is indexed by the attestations' own
    rounds (`SGVotesRoundIndexed`). -/
theorem sgVotesRoundIndexed_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (i : Nat) (v : V) :
    Restated.SGVotesRoundIndexed M (M.gradeView (M.toHealing (x[i][v].st).st.core)) := by
  obtain ⟨w, hw, heq⟩ := Record.stateBeforeOf_runOfM M S Sched x facts.nd.wake_events_or_id v i
  have hsg := Restated.Vocabulary.Proofs.NamedStoreBridge.sgRounds_stateBefore facts (Setup.alwaysAwake S)
    (Record.runOfM M S Sched x v i) (Record.veventsOf M S Sched x v i).length v w hw
  rw [heq] at hsg
  intro r' u hu
  rw [facts.gr.gradeView_sg_votes, Finset.mem_image] at hu
  obtain ⟨a, ha, hau⟩ := hu
  rw [facts.sto.Sts_mem_sg_pool_iff] at ha
  rw [← hau, facts.sto.sgVote_round_eq_round]
  exact hsg r' a ha

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A round's action instant is the support cutoff of the slot after its opening slot. -/
theorem action_eq_support_cutoff (facts : Record.Facts M) (S : Setup V) (r : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S r) = M.support_cutoff S.E ((M.opening_slot S.hc r) + 1) :=
  Restated.Vocabulary.Protocol.a_eq_support_cutoff_succ facts S.hc S.E r

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The slot a round's action instant falls in is the slot after the round's opening slot. -/
theorem slotOf_action (facts : Record.Facts M) (S : Setup V) (r : Round) :
    S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S r)) = (M.opening_slot S.hc r) + 1 := by
  rw [Restated.action_eq_support_cutoff facts S r, facts.sch.slotOf_support_cutoff]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The round of the slot of round `r`'s action instant is `r`. -/
theorem round_of_slotOf_action (facts : Record.Facts M) (S : Setup V) (r : Round) :
    (M.round_of S.hc (S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S r)))) = r :=
  Restated.Vocabulary.Proofs.HealingLemmas.round_of_slotOf_a facts S r

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A round's action instant is a multiple of `Δ`. -/
theorem action_emod_delta (facts : Record.Facts M) (S : Setup V) (r : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S r) % S.E.Δ = 0 := by
  rw [Restated.action_eq_support_cutoff facts S r]
  exact facts.sch.support_cutoff_emod_delta S _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The attestations `v`'s round-`r` action read can compute from the node state `v`'s tick reads at
    time `t` from configuration `c` are those it can compute from `v`'s node state in `c`. -/
theorem actionAttestationFrom_wakeStage (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (t : Int) (c : Config V (NamedObject V) M.N) (v : V) (r : Round) :
    Restated.actionAttestationFrom M S (Record.wakeStage M Sched t c v) v r =
      Restated.actionAttestationFrom M S (c[v].st) v r := by
  unfold Restated.actionAttestationFrom Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom
  rw [Record.wakeStage_st facts, Record.wakeStage_cache facts, Record.wakeStage_record facts]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every outcome of `v`'s tick at round `r`'s action instant, at a node state `st` passing the
    grade-2 awake test of round `r` (`hrun`), and every attestation `a` that `v`'s round-`r` action
    read can compute from `st`, the outcome emits `a`. The hypothesis `hn` says that `st` is a node
    state a run reaches, and `hv` that `st` runs as `v`. -/
theorem namedTick_emits_attest (facts : Record.Facts M) (S : Setup V) (v : V) (st : M.N) (r : Round)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v st r) : ∀ out₁, M.tick (Setup.alwaysAwake S) v st ((Restated.Vocabulary.Execution.Setup.a M S r)) ⇢ out₁ →
    ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) st v r,
      ∀ (hn : M.reachedNode st := by trivial) (hv : M.runs_as st v := by trivial),
      NamedObject.attest a ∈ out₁.2 := by
  intro out₁ hout a ha _hn _hv
  obtain ⟨n, ⟨c, hc, st', hst', rfl⟩, ns, rec, hD⟩ := ha
  rw [facts.nd.mkNode_st, facts.dt.duties_attest_with_store_with_cache, facts.nd.mkNode_record,
    facts.nd.mkNode_cache] at hD
  rw [facts.nd.tick_at_action_awake (Setup.alwaysAwake S) v st r out₁ hout c hc st' hst'
    (ns, rec, a) hD hrun]
  exact List.mem_singleton.mpr rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every event in `v`'s event list for the first `n` steps happens at or before the time after `n`
    steps. -/
theorem vevents_time_le (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat) :
    ∀ e ∈ Record.veventsOf M S Sched x v n, Record.Event.time e ≤ (x[n].time : Int) := by
  induction n with
  | zero =>
      intro e he
      simp only [Record.veventsOf, List.not_mem_nil] at he
  | succ n ih =>
      intro e he
      rw [show Record.veventsOf M S Sched x v (n + 1)
            = Record.veventsOf M S Sched x v n
              ++ Record.actionEventsOf M S Sched v (x[n].time : Int) (x.lbl n) from rfl] at he
      have hmono : (x[n].time : Int) ≤ (x[n + 1].time : Int) := by
        exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_succ n)
      rcases List.mem_append.mp he with h | h
      · exact le_trans (ih e h) hmono
      · rcases Record.mem_actionEventsOf_cases h with ⟨t, hl, he | he⟩ | ⟨p, m, -, -, he⟩
        · subst he
          obtain ⟨-, h2⟩ := Restated.tickAllAwake_time facts S Sched x hl
          show ((t : Nat) : Int) ≤ ((x[n + 1].time : Nat) : Int)
          omega
        · subst he
          obtain ⟨-, h2⟩ := Restated.tickAllAwake_time facts S Sched x hl
          show ((t : Nat) : Int) ≤ ((x[n + 1].time : Nat) : Int)
          omega
        · subst he
          show (x[n].time : Int) ≤ ((x[n + 1].time : Nat) : Int)
          exact hmono

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `n` is the tick at `t`, some world the run of `v`'s events of the first `n + 1` steps
    reaches strictly before `t` holds, at `v`, `v`'s node state after `n` steps. -/
theorem stateBeforeTime_runOf_action (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {n : Nat} {t : Int} (hn : Restated.tickStepAt M x n t) (v : V) :
    ∃ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M (Setup.alwaysAwake S) (Record.runOfM M S Sched x v (n + 1)) t,
      w v = x[n][v].st := by
  obtain ⟨t', hlbl, ht'⟩ := hn
  obtain ⟨-, htB⟩ := Restated.tickStepAt_time facts x ⟨t', hlbl, ht'⟩
  have hfil : (Record.veventsOf M S Sched x v (n + 1)).filter
        (fun e => decide (Record.Event.time e < t))
      = Record.veventsOf M S Sched x v n := by
    rw [show Record.veventsOf M S Sched x v (n + 1)
          = Record.veventsOf M S Sched x v n
            ++ Record.actionEventsOf M S Sched v (x[n].time : Int) (x.lbl n) from rfl,
      List.filter_append]
    have h1 : (Record.veventsOf M S Sched x v n).filter (fun e => decide (Record.Event.time e < t))
        = Record.veventsOf M S Sched x v n := by
      refine List.filter_eq_self.mpr ?_
      intro e he
      have hle := Restated.vevents_time_le facts S Sched x v n e he
      have hlt : (x[n].time : Int) < t := by omega
      simp only [decide_eq_true_eq]
      exact lt_of_le_of_lt hle hlt
    have h2 : (Record.actionEventsOf M S Sched v (x[n].time : Int) (x.lbl n)).filter
        (fun e => decide (Record.Event.time e < t)) = [] := by
      refine List.filter_eq_nil_iff.mpr ?_
      intro e he
      rcases Record.mem_actionEventsOf_cases he with ⟨τ, hl, he' | he'⟩ | ⟨p, m, hl, -, -⟩
      · rw [hlbl] at hl
        cases hl
        subst he'
        simp only [Record.Event.time, decide_eq_true_eq, not_lt]
        exact le_of_eq ht'.symm
      · rw [hlbl] at hl
        cases hl
        subst he'
        simp only [Record.Event.time, decide_eq_true_eq, not_lt]
        exact le_of_eq ht'.symm
      · rw [hlbl] at hl
        cases hl
    rw [h1, h2, List.append_nil]
  show ∃ w ∈ ((Record.veventsOf M S Sched x v (n + 1)).filter
      (fun e => decide (Record.Event.time e < t))).foldlM
      (Record.worldStepOf M (Setup.alwaysAwake S))
      (fun v' => M.initial (Setup.alwaysAwake S) v'), w v = x[n][v].st
  rw [hfil]
  exact Record.fold_veventsOf M S Sched x facts.nd.wake_events_or_id v n

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `n` is the tick at round `r`'s action instant and `v` is awake and not held by the
    adversary there, with a tick that has an outcome (`hne`) and reads a node state passing the
    grade-2 awake test of round `r` (`hrun`), then the sent log after step `n` holds
    `⟨v, .attest a⟩` for every attestation `a` `v`'s round-`r` action read can compute from its node
    state before the step. -/
theorem attest_emitted_at_tick_from (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {n : Nat} {r : Round}
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r))) {v : V} (hv : v ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S r)) \ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hne : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v) r) :
    ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v].st) v r,
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent := by
  have _hr_0 : M.reachedNode (x[n][v].st) := Record.reachedNode_sts facts S Sched x n v
  have _hv_0 : M.runs_as (x[n][v].st) v := Record.runs_as_sts facts S Sched x n v
  have _hr_1 : M.reachedNode (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v) := Record.reachedNode_wakeStage facts S Sched x n v (Restated.Vocabulary.Execution.Setup.a M S r)
  have _hv_1 : M.runs_as (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v) v := Record.runs_as_wakeStage facts S Sched x n v (Restated.Vocabulary.Execution.Setup.a M S r)
  intro a ha
  have hA : Restated.actionAttestationFrom M (Setup.alwaysAwake S)
      (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v) v r =
      Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v].st) v r := by
    simp only [Restated.actionAttestationFrom,
      Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom, Record.wakeStage_st facts,
      Record.wakeStage_record facts, Record.wakeStage_cache facts]
  obtain ⟨t', hlbl, ht'⟩ := hn
  refine Restated.mem_sent_of_tick facts S Sched x hlbl (by rw [ht']; exact hv)
    (by rw [ht']; exact Restated.action_emod_delta facts S r) ?_ ?_
  · rw [ht']
    exact fun out hout => Restated.namedTick_emits_attest facts S v _ r hrun out hout a
      (by rw [hA]; exact ha)
  · rw [ht']
    exact hne

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `⟨v, .attest a⟩` is in the sent log after `i` steps, `a` names `v`, and `v` is honest through
    a time at or after `x[i].time`, then some step `k < i` is the tick at the action instant of
    `a`'s round, at which `v` was awake and not held by the adversary, and some outcome of `v`'s
    tick there sends `a`. -/
theorem attest_round_of_sent (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {v : V} {a : NamedAttestation V} {tB : Int}
    (hv : HonestThroughTime Sched tB v) (hunf : Restated.Unforgeability M S x) (hauth : a.val_index = v)
    {i : Nat} (hi : (x[i].time : Int) ≤ tB)
    (ho : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent) :
    a.val_index = v ∧ ∃ k < i, Restated.tickStepAt M x k ((Restated.Vocabulary.Execution.Setup.a M S a.round)) ∧
      v ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S a.round)) \ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S a.round)) ∧
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched ((Restated.Vocabulary.Execution.Setup.a M S a.round)) x[k] v) ((Restated.Vocabulary.Execution.Setup.a M S a.round)) ⇢ out ∧
        NamedObject.attest a ∈ out.2 := by
  obtain ⟨k, hk, t, hlbl, haw, hdvd, out, hout, hmem⟩ :=
    Restated.tick_of_honest_signed_upTo facts S Sched x v (NamedObject.attest a) tB hv hunf
      (by rw [author_attest, hauth]) i hi ho
  obtain ⟨W, hW, hemits⟩ :=
    Restated.emits_runAll_of_tick facts S Sched x v hk hlbl haw hdvd hout hmem
  obtain ⟨hsender, ht⟩ :=
    Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts (Setup.alwaysAwake S) W hW hemits
  have ht' : (t : Int) = (Restated.Vocabulary.Execution.Setup.a M S a.round) := ht
  exact ⟨hsender, k, hk, ⟨t, hlbl, ht'⟩, by rw [← ht']; exact haw,
    out, by rw [← ht']; exact hout, hmem⟩

end

end DecoupledConsensusModel.Sts.Restated
