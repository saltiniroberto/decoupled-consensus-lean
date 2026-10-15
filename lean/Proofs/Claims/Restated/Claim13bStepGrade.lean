import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRecord
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13bStepKitStore
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Redelivery
import Proofs.Claims.Restated.RunAll
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepGrade
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.ProcessedFlip
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13b
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_SGArrivalStampCarrier
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Attestations at a round's action instant and the grade inputs

The order of a round's phase cutoffs and action instant, the SG arrival data every store keeps, the
fresh attesters of a round and the attestations their ticks emit, and the rounds of the tokens a
grade reads, stated over a model `M : Record.Model V` and its facts `facts : Record.Facts M`.
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

/-- The G2 early cutoff of a round is at or before the early cutoff of every phase of that round. -/
theorem early_g2_le_early (facts : Record.Facts M) (S : Setup V) (r : Round) (p : Protocol.Phase) :
    M.early S.E S.hc r .g2 ≤ M.early S.E S.hc r p := by
  cases p with
  | g0 => exact facts.gr.early_g2_le_early_g0 S.E S.hc r
  | g1 => exact facts.gr.early_g2_le_early_g1 S.E S.hc r
  | g2 => exact le_refl _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- One delay after round `r`'s action instant is strictly before every phase instant of round
    `r + 1`. -/
theorem action_delta_lt_domain_succ (facts : Record.Facts M) (S : Setup V) (r : Round) (p : Protocol.Phase) :
    (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ < M.domain S.E S.hc (r + 1) p :=
  lt_of_le_of_lt
    (facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r))
    (facts.gr.early_g2_lt_domain S (r + 1) p)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- One delay after round `r`'s action instant is at or before round `r + 1`'s G2 early cutoff. -/
theorem action_delta_le_early_succ (facts : Record.Facts M) (S : Setup V) (r : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ M.early S.E S.hc (r + 1) .g2 :=
  facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Round `r` is in the expiry window of round `r + 1`. -/
theorem mem_latest_window_self_succ (facts : Record.Facts M) (S : Setup V) (r : Round) :
    r ∈ M.latest_window S.hc.η_SG (r + 1) :=
  facts.fc.mem_latest_window
    (Nat.sub_le_iff_le_add.mpr (Nat.add_le_add_left S.hc.η_SG_ge_one r))
    (Nat.lt_succ_self r)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The SG arrival data of a store for a bound `t_0` holds for every bound `t_1 ≥ t_0`. -/
theorem sgRowData_mono (facts : Record.Facts M) {t_0 t_1 : Int} {st : M.NS}
    (h : Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M t_0 st) (ht : t_0 ≤ t_1) :
    Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M t_1 st := by
  refine ⟨le_trans h.1 ht, ?_⟩
  intro k a ha
  obtain ⟨hr, stamp, hstamp, hts⟩ := h.2 k a ha
  exact ⟨hr, stamp, le_trans hstamp ht, hts⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If a coherent node state's store has the SG arrival data for a bound at or after the tick's time
    `t`, then the node state of every outcome of the tick has it too. -/
theorem sgRowData_node_tick (facts : Record.Facts M) (S' : Setup V) (v : V) (n : M.N)
    (t bound : Int) (ht : t ≤ bound)
    (hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S'.E S'.cfg n.st)
    (h : Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M bound n.st) :
    ∀ out₁, M.tick S' v n t ⇢ out₁ →
      Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M bound out₁.1.st := by
  intro out₁ hout
  exact facts.nd.rawRelay_tick_outcome_data S' v n t out₁ hout bound ht hcoh h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If a coherent node state's store has the SG arrival data for a bound, then the node state of
    every outcome of the receipt of any object has it too. -/
theorem sgRowData_node_process (facts : Record.Facts M) (S' : Setup V) (n : M.N)
    (o : NamedObject V) (bound : Int)
    (hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S'.E S'.cfg n.st)
    (h : Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M bound n.st) :
    ∀ n', M.process S' n o ⇢ n' →
      Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M bound n'.st := by
  intro n' hn'
  have hd := facts.nd.rawRelay_process_data S' bound n.st o hcoh h
  rw [facts.nd.process_st S' n o n' hn']
  unfold Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data
  rw [facts.nd.make_grades_compatible_with_finalized_core_t,
    facts.nd.make_grades_compatible_with_finalized_sg_rows,
    facts.nd.make_grades_compatible_with_finalized_core_timestamp_sg_vote]
  exact hd

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `k` is the tick at `t`, either the step took an outcome `out` of `v`'s tick from a node
    state `n₀` with `v`'s store after `k` steps, which a run reaches and which runs as `v`, and
    `v`'s node state after `k + 1` steps is `out`'s, or `v`'s store after `k + 1` steps is its store
    after `k` steps. -/
private theorem tick_step_st_cases_grade (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {k t : Nat} (v : V)
    (hl : x.lbl k = AtomicAction.tickAllAwake t) :
    (∃ (n₀ : M.N) (out : M.N × List (NamedObject V)), n₀.st = (x[k][v].st).st ∧
        (M.reachedNode n₀ ∧ M.runs_as n₀ v) ∧
        M.tick (Setup.alwaysAwake S) v n₀ (t : Int) ⇢ out ∧ x[k + 1][v].st = out.1) ∨
      (x[k + 1][v].st).st = (x[k][v].st).st := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, w, tk, hwake, htick, hc⟩ := hs
  have hwst : ((w v).state).st = (x[k][v].st).st := by
    have hww := hwake v
    unfold TickAllAwakeWake at hww
    by_cases he : v ∈ entrants Sched t
    · rw [if_pos he] at hww
      rw [Record.protocolOf_step_wake M S hww]
      exact (facts.nd.wake_st_record _).1
    · rw [if_neg he] at hww
      rw [hww]
  by_cases haw : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int)
  · have hx1 : x[k + 1][v].st = (tk v).state := by
      have h2 : x[k + 1][v] = (tickAllAwakeUpdate Sched t x[k] w tk)[v] := by rw [hc]
      rw [h2, tickAllAwakeUpdate_getElem_react haw]
    rcases Record.protocolOf_step_tick M S (htick v haw) with ⟨-, out, hout, hres⟩ | ⟨-, hres⟩
    · have hwS : (w v).state = Record.wakeStage M Sched (t : Int) x[k] v :=
        Record.wakeStage_of_TickAllAwakeWake M S Sched (hwake v)
      exact Or.inl ⟨(w v).state, out, hwst,
        ⟨by rw [hwS]; exact Record.reachedNode_wakeStage facts S Sched x k v t,
          by rw [hwS]; exact Record.runs_as_wakeStage facts S Sched x k v t⟩, hout, by rw [hx1, hres]⟩
    · exact Or.inr (by rw [hx1, hres, hwst])
  · refine Or.inr ?_
    have h2 : x[k + 1][v] = (tickAllAwakeUpdate Sched t x[k] w tk)[v] := by rw [hc]
    rw [h2, tickAllAwakeUpdate_getElem_st_of_not_react haw]

/-- After any number of steps, every validator's store has the SG arrival data for the real time of
    that configuration: each attestation row in the bucket of a round is a row of that round, and
    the store's SG stamps are at or before that time. -/
theorem sgRowData_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (m : Nat) (w : V) :
    Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M (x[m].time : Int) (x[m][w].st).st := by
  induction m with
  | zero =>
      have hst : x[0][w].st = M.initial (Setup.alwaysAwake S) w := Record.st_zero M S Sched x w
      have ht : x[0].time = 0 := x.init.1
      rw [hst, ht]
      refine ⟨?_, ?_⟩
      · show (M.initial (Setup.alwaysAwake S) w).st.core.t ≤ ((0 : Nat) : Int)
        rw [facts.nd.initial_st, facts.hd.initial_core_t]
        simp
      · intro k a ha
        rw [facts.nd.initial_st, facts.hd.initial_sg_rows] at ha
        simp at ha
  | succ i ih =>
      have hmono : (x[i].time : Int) ≤ (x[i + 1].time : Int) :=
        Restated.time_mono_int facts S Sched x (Nat.le_succ i)
      have ih' : Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M (x[i + 1].time : Int)
          (x[i][w].st).st := Restated.sgRowData_mono facts ih hmono
      have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M (Setup.alwaysAwake S).E (Setup.alwaysAwake S).cfg
          (x[i][w].st).st := (Restated.nodeInvariant_sts facts S Sched x i w).1.1.1
      cases hl : x.lbl i with
      | tickAllAwake τ =>
          rcases tick_step_st_cases_grade facts S Sched x w hl with ⟨n₀, out₁, hn₀, ⟨_hr₀, _hv₀⟩, hout, hst⟩ | hst
          · obtain ⟨-, httime⟩ := Restated.tickAllAwake_time facts S Sched x hl
            have ht : (τ : Int) ≤ (x[i + 1].time : Int) := by
              rw [httime]
            have hcoh₀ : Restated.Vocabulary.Proofs.NamedStore.Coherent M (Setup.alwaysAwake S).E
                (Setup.alwaysAwake S).cfg n₀.st := by rw [hn₀]; exact hcoh
            have ih₀ : Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M
                (x[i + 1].time : Int) n₀.st := by rw [hn₀]; exact ih'
            rw [hst]
            exact Restated.sgRowData_node_tick facts (Setup.alwaysAwake S) w n₀ (τ : Int)
              (x[i + 1].time : Int) ht hcoh₀ ih₀ out₁ hout
          · rw [hst]; exact ih'
      | deliver q sm =>
          by_cases hq : q = w
          · subst hq
            rcases Restated.st_succ_of_deliver facts S Sched x hl with hp | ⟨-, hst⟩
            · exact Restated.sgRowData_node_process facts (Setup.alwaysAwake S) (x[i][q].st) sm.msg
                (x[i + 1].time : Int) hcoh ih' _ hp
            · rw [hst]; exact ih'
          · rw [Restated.getElem_succ_of_deliver_ne facts S Sched x hl hq]; exact ih'
      | custom q ev => exact ev.elim
      | adversarial q sm =>
          rw [Restated.getElem_succ_of_adversarial facts S Sched x hl]; exact ih'
      | forward q sm =>
          rw [Restated.getElem_succ_of_forward facts S Sched x hl]; exact ih'

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A validator is in `freshAttesters S Sched x r m` exactly when it is in `activeRound S Sched r`
    and honest through step `m`. -/
theorem mem_freshAttesters (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {r : Round} {m : Nat} {q : V} :
    q ∈ Restated.freshAttesters M S Sched x r m ↔
      q ∈ Restated.activeRound M S Sched r ∧ Restated.HonestThrough M Sched x m q := by
  classical
  simp [Restated.freshAttesters]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A member of `freshAttesters S Sched x r m` is awake at round `r`'s action instant. -/
theorem awake_of_mem_freshAttesters (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {r : Round} {m : Nat} {q : V}
    (hq : q ∈ Restated.freshAttesters M S Sched x r m) : q ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S r)) := by
  have h := ((Restated.mem_freshAttesters facts).mp hq).1
  simp only [Restated.activeRound] at h
  refine mem_awake_of_awakeThroughout Sched h ?_ (le_refl _)
  have hd := S.E.Δ_pos
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A member of `freshAttesters S Sched x r m` is honest through step `m`. -/
theorem honestThrough_of_mem_freshAttesters (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {r : Round} {m : Nat} {q : V}
    (hq : q ∈ Restated.freshAttesters M S Sched x r m) : Restated.HonestThrough M Sched x m q :=
  ((Restated.mem_freshAttesters facts).mp hq).2

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `n` is the tick at round `r`'s action instant and `q` is a member of `freshAttesters`
    not held by the adversary there, whose tick at that step has an outcome (`hne`) and reads a node
    state passing the grade-2 awake test of round `r` (`hrun`), then the sent log after step `n`
    holds `q`'s signed message for every attestation its round-`r` action read can compute. -/
theorem fresh_attests (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {r : Round} {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r)))
    {m : Nat} {q : V} (hq : q ∈ Restated.freshAttesters M S Sched x r m)
    (hqr : q ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hne : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] q) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) q
      (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] q) r) :
    ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][q].st) q r,
      (⟨q, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent :=
  Restated.attest_emitted_at_tick_from facts S Sched x hn
    (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_freshAttesters facts hq, hqr⟩) hne hrun

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every outcome of `v`'s tick at round `r`'s action instant, at a node state `st` passing the
    grade-2 awake test of round `r` (`hrun`), and every attestation `a` that `v`'s round-`r` action
    read can compute from `st`, the outcome emits the one-element list carrying `a`. The hypothesis
    `hn` says that `st` is a node state a run reaches, and `hv` that `st` runs as `v`. -/
theorem namedTick_emits_only_attest (facts : Record.Facts M) (S : Setup V) (v : V) (st : M.N) (r : Round)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v st r) : ∀ out₁, M.tick (Setup.alwaysAwake S) v st ((Restated.Vocabulary.Execution.Setup.a M S r)) ⇢ out₁ →
    ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) st v r,
      ∀ (hn : M.reachedNode st := by trivial) (hv : M.runs_as st v := by trivial),
      out₁.2 = [NamedObject.attest a] := by
  intro out₁ hout a ha _hn _hv
  obtain ⟨n, ⟨c, hc, st', hst', rfl⟩, ns, rec, hD⟩ := ha
  rw [facts.nd.mkNode_st, facts.dt.duties_attest_with_store_with_cache, facts.nd.mkNode_record,
    facts.nd.mkNode_cache] at hD
  exact facts.nd.tick_at_action_awake (Setup.alwaysAwake S) v st r out₁ hout c hc st' hst'
    (ns, rec, a) hD hrun

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- An attestation `a` emitted by an outcome of `v`'s tick at round `r`'s action instant equals
    every attestation `v`'s round-`r` action read can compute from `st`. The hypothesis `hn` says
    that `st` is a node state a run reaches, and `hv` that `st` runs as `v`. -/
theorem attest_of_tick_eq (facts : Record.Facts M) (S : Setup V) (v : V) (st : M.N) (r : Round)
    {a : NamedAttestation V} {out₁ : M.N × List (NamedObject V)}
    (hout : M.tick (Setup.alwaysAwake S) v st ((Restated.Vocabulary.Execution.Setup.a M S r)) ⇢ out₁)
    (h : NamedObject.attest a ∈ out₁.2) :
    ∀ a' ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) st v r,
      ∀ (hn : M.reachedNode st := by trivial) (hv : M.runs_as st v := by trivial), a = a' := by
  intro a' ha' _hn _hv
  obtain ⟨ht, hrun, -⟩ :=
    facts.nd.tick_attestation_fields (Setup.alwaysAwake S) v st _ _hv out₁ hout a h
  have hstrict : StrictMono (Restated.Vocabulary.Execution.Setup.a M S) := by
    refine strictMono_nat_of_lt_succ fun r => ?_
    show M.a S.hc S.E.Δ r < M.a S.hc S.E.Δ (r + 1)
    rw [facts.gr.a_add_rounds S r 1]
    have hRnat : 0 < S.hc.R := lt_of_lt_of_le (by omega) S.hc.R_ge_two
    have hR : (0 : Int) < ((S.hc.R : Nat) : Int) := by
      exact_mod_cast hRnat
    have hinc : (0 : Int) < 4 * S.E.Δ * ((S.hc.R : Nat) : Int) := by
      exact Int.mul_pos (Int.mul_pos (by norm_num) S.E.Δ_pos) hR
    simpa only [Nat.mul_one] using
      Int.lt_add_of_pos_right ((Restated.Vocabulary.Execution.Setup.a M S r)) hinc
  have hr : a.round = r := hstrict.injective ht.symm
  rw [hr] at hrun
  rw [Restated.namedTick_emits_only_attest facts S v st r hrun out₁ hout a' ha'] at h
  simpa using h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every round-`r` attestation `v`'s action read can compute names `v` as its sender. -/
theorem actionAttestationFrom_val_index (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (v : V) (r : Round) :
    ∀ a ∈ Restated.actionAttestationFrom M S before v r, a.val_index = v := by
  intro a ha
  obtain ⟨n, -, ns, rec, hD⟩ := ha
  obtain ⟨A, hA⟩ := facts.dt.round_action_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node v) (M.toHealing n.st.core) n.record
  have hrow := facts.dt.attest_with_row _ S.E S.hc (S.node v) n.st n.record _ hD A hA
  have hidx := facts.dt.round_action_with_val_index _ S.E S.hc (S.node v) _ n.record A hA
  simp only at hrow
  rw [hrow, hidx]
  exact S.node_val_index v

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every round-`r` attestation `v`'s action read can compute carries round `r`. -/
theorem actionAttestationFrom_round (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (v : V) (r : Round) :
    ∀ a ∈ Restated.actionAttestationFrom M S before v r, a.round = r := by
  intro a ha
  obtain ⟨n, ⟨c, hc, st', hst', rfl⟩, ns, rec, hD⟩ := ha
  rw [facts.nd.mkNode_st, facts.dt.duties_attest_with_store_with_cache, facts.nd.mkNode_record,
    facts.nd.mkNode_cache] at hD
  obtain ⟨A, hA⟩ := facts.dt.round_action_with_nonempty (M.gradeContract c) S.E S.hc
    (S.node v) (M.toHealing st'.core) before.record
  have hrow := facts.dt.attest_with_row _ S.E S.hc (S.node v) st' before.record _ hD A hA
  have hround := facts.dt.round_action_with_round _ S.E S.hc (S.node v) _ before.record A hA
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  have hcore := facts.dt.named_update_confirmation_with_core _ S.E S.hc _ _ st' hst' X hX
  have hs := facts.dt.update_confirmation_with_s _ S.E S.hc _ _ X hX
  simp only at hrow
  rw [hrow, hround, facts.sto.toHealing_s, hcore, hs, facts.hd.Sts_setClock_core_s]
  exact facts.sch.round_of_slotOf_a S r

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every round's action instant is positive. -/
theorem action_pos (facts : Record.Facts M) (S : Setup V) (r : Round) :
    0 < (Restated.Vocabulary.Execution.Setup.a M S r) := by
  rw [Restated.action_eq_support_cutoff facts S r]
  exact facts.sch.support_cutoff_pos S _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `w`'s store after `m` steps holds, in the grade view's pool of a round, an SG vote `u` whose
    sender `q` is honest through step `m`, then some step `n'` is the tick at the action instant of
    `u`'s round, `q` was awake there, and `u` is the SG vote of every attestation `q`'s action read
    can compute from its node state at step `n'`. -/
theorem token_of_honest_sender (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {m : Nat} {w q : V} (hq : Restated.HonestThrough M Sched x m q)
    {r' : Round} {u : Protocol.SGVote V}
    (hu : u ∈ (M.gradeView (M.toHealing (x[m][w].st).st.core)).sg_votes r')
    (hsender : u.val_index = q) :
    ∃ n' : Nat, Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S u.round)) ∧ q ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S u.round)) ∧
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n'][q].st) q u.round,
        u = M.sgVote a.erase := by
  have _hr_0 : M.reachedNode (x[m][w].st) := Record.reachedNode_sts facts S Sched x m w
  have _hr_1 : M.reachedNode (x[0][w].st) := Record.reachedNode_sts facts S Sched x 0 w
  rw [facts.gr.gradeView_sg_votes, Finset.mem_image] at hu
  obtain ⟨c, hc, hcu⟩ := hu
  rw [facts.sto.Sts_mem_sg_pool_iff] at hc
  have hpv := Restated.poolView_sts facts S Sched x m w r'
  rw [hpv] at hc
  obtain ⟨B, hB, hBc⟩ := List.mem_map.mp hc
  have hBround : B.round = r' := ((Restated.sgRowData_sts facts S Sched x m w).2 r' B hB).1
  have hu_eq : u = M.sgVote B.erase := by rw [← hcu, ← hBc]
  have hur : u.round = B.round := by
    rw [hu_eq, facts.sto.sgVote_round_eq_round, Proofs.ModelProperties.erase_round]
  have hBidx : B.val_index = q := by
    have h : u.val_index = B.val_index := by
      rw [hu_eq, facts.sto.sgVote_val_index_eq_val_index, Proofs.ModelProperties.erase_val_index]
    rw [← h]; exact hsender
  have hBmem : B ∈ (x[m][w].st).st.sg_rows B.round := by rw [hBround]; exact hB
  have h0 : Restated.Vocabulary.Execution.Object.processed M (x[0][w].st).st
      (NamedObject.attest B) = false := by
    rw [Record.st_zero M S Sched x w]
    simp only [Restated.Vocabulary.Execution.Object.processed, facts.nd.initial_st,
      facts.hd.initial_sg_rows]
    simp
  have hm : Restated.Vocabulary.Execution.Object.processed M (x[m][w].st).st
      (NamedObject.attest B) = true := by
    simp only [Restated.Vocabulary.Execution.Object.processed]
    exact decide_eq_true hBmem
  obtain ⟨i, him, hf0, hf1⟩ :=
    Restated.exists_flip_of_processed facts S Sched x w (NamedObject.attest B) h0 hm
  have hauthor : NamedObject.author (NamedObject.attest B) = some q := by
    rw [author_attest, hBidx]
  have hlog : ∃ i' : Nat, i' ≤ m ∧
      (⟨q, NamedObject.attest B⟩ : SignedMsg V (NamedObject V)) ∈ x[i'].sent := by
    rcases Restated.flip_step_cases facts S Sched x hf0 hf1 with
      ⟨sm, hlbl, -, -, hpay⟩ | ⟨τ, hlbl, haw, hdvd, out₁, hout₁, hst₁, hem⟩
    · refine ⟨i, le_of_lt him, ?_⟩
      have hsm : sm ∈ x[i].sent := (Restated.sent_of_deliver facts S Sched x hlbl).1
      have hhon : Restated.HonestThrough M Sched x i q := fun t ht =>
        hq t (le_trans ht (Restated.time_mono_int facts S Sched x (le_of_lt him)))
      rcases hpay with hmsg | ⟨Bl, hmsg, hcc⟩
      · have := hexec.unforgeable i sm q hsm (by rw [hmsg]; exact hauthor) hhon
        rw [hmsg] at this
        exact this
      · refine hexec.carried i sm (NamedObject.attest B) q hsm ?_ hauthor hhon
        rw [hmsg]
        exact Restated.carries_of_carriedCall facts (Setup.alwaysAwake S) (x[i][w].st).st Bl hcc
    · refine ⟨i + 1, Nat.succ_le_of_lt him, ?_⟩
      have hhon : Restated.HonestThrough M Sched x (i + 1) q := fun t ht =>
        hq t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt him)))
      have hsend := facts.nd.tick_send_eq_of_state (Setup.alwaysAwake S) w
        (Record.wakeStage M Sched (τ : Int) x[i] w) (τ : Int)
      rcases hem with hmem | ⟨Bl, hmem, hcc⟩
      · have hsent := Restated.mem_sent_of_tick_of_state facts S Sched x hlbl haw hdvd hsend
          hout₁ hst₁ hmem
        exact hexec.unforgeable (i + 1) ⟨w, NamedObject.attest B⟩ q hsent hauthor hhon
      · have hsent := Restated.mem_sent_of_tick_of_state facts S Sched x hlbl haw hdvd hsend
          hout₁ hst₁ hmem
        exact hexec.carried (i + 1) ⟨w, NamedObject.block Bl⟩ (NamedObject.attest B) q hsent
          (Restated.carries_of_carriedCall facts (Setup.alwaysAwake S) _ Bl hcc) hauthor hhon
  obtain ⟨i', hi'm, hsent⟩ := hlog
  obtain ⟨-, n', -, htick, hawn, out, hout, hemit⟩ :=
    Restated.attest_round_of_sent facts S Sched x (tB := (x[m].time : Int)) hq
      hexec.toUnforgeability hBidx (Restated.time_mono_int facts S Sched x hi'm) hsent
  refine ⟨n', ?_, ?_, ?_⟩
  · rw [hur]; exact htick
  · rw [hur]; exact (Finset.mem_sdiff.1 hawn).1
  · intro a ha
    rw [hur] at ha
    have hA : Restated.actionAttestationFrom M (Setup.alwaysAwake S)
        (Record.wakeStage M Sched ((Restated.Vocabulary.Execution.Setup.a M S B.round)) x[n'] q) q
          B.round =
        Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n'][q].st) q B.round := by
      simp only [Restated.actionAttestationFrom,
        Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom, Record.wakeStage_st facts,
        Record.wakeStage_record facts, Record.wakeStage_cache facts]
    rw [← hA] at ha
    have _hr_w : M.reachedNode
        (Record.wakeStage M Sched ((Restated.Vocabulary.Execution.Setup.a M S B.round)) x[n'] q) :=
      Record.reachedNode_wakeStage facts S Sched x n' q _
    have _hv_w : M.runs_as
        (Record.wakeStage M Sched ((Restated.Vocabulary.Execution.Setup.a M S B.round)) x[n'] q) q :=
      Record.runs_as_wakeStage facts S Sched x n' q _
    have hBeq : B = a := Restated.attest_of_tick_eq facts S q _ B.round hout hemit a ha
    rw [← hBeq]; exact hu_eq

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Two tick steps at the same time `t` are the same step. -/
theorem tickStepAt_unique (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) {n_1 n_2 : Nat} {t : Int}
    (h_1 : Restated.tickStepAt M x n_1 t) (h_2 : Restated.tickStepAt M x n_2 t) : n_1 = n_2 := by
  obtain ⟨t_1, hl_1, ht_1⟩ := h_1
  obtain ⟨t_2, hl_2, ht_2⟩ := h_2
  have hteq : t_1 = t_2 := by exact_mod_cast ht_1.trans ht_2.symm
  subst hteq
  exact Restated.tickAllAwake_step_unique facts S Sched x hl_1 hl_2

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- At the tick step `n` of round `r`'s action instant, with GST at or before that instant, a
    validator awake throughout `[S.a r, T]` with `S.a r + Δ ≤ T` is awake from `x[n + 1].time`
    through the delivery deadline `max x[n].time t_GST + Δ` of that step's sends. -/
theorem receiverWindowA_of_tick (facts : Record.Facts M) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r)) {T : Int} (hT : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ T) {w : V}
    (hawT : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) T) :
    w ∈ Sched.awakeThroughout (x[n + 1].time : Int)
      (max (x[n].time : Int) S.E.t_GST + S.E.Δ) := by
  obtain ⟨h1, h0⟩ := Restated.tickStepAt_time facts x hn
  refine awakeThroughout_mono Sched hawT (le_of_eq h1.symm) ?_
  have hmax : max (x[n].time : Int) S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := max_le (by linarith) hgst
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every outcome of the raw view a round-`(r + 1)` grade reads from `w`'s store after `m`
    steps, every token in it carries a round at most `r`. -/
theorem rawView_round_le (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (m : Nat) (w : V) (r : Round) (cutoff : Int) (q : V) :
    ∀ X, M.rawView (M.gradeView (M.toHealing (x[m][w].st).st.core)) S.hc.η_SG (r + 1)
        cutoff q ⇢ X → ∀ tok ∈ X, tok.round ≤ r := by
  intro X hX tok htok
  have hidx : Restated.SGVotesRoundIndexed M (M.gradeView (M.toHealing (x[m][w].st).st.core)) := by
    intro r' u hu
    rw [facts.gr.gradeView_sg_votes, Finset.mem_image] at hu
    obtain ⟨c, hc, hcu⟩ := hu
    rw [facts.sto.Sts_mem_sg_pool_iff] at hc
    have hpv := Restated.poolView_sts facts S Sched x m w
    rw [hpv] at hc
    obtain ⟨B, hB, hBc⟩ := List.mem_map.mp hc
    rw [← hcu, ← hBc, facts.sto.sgVote_round_eq_round, Proofs.ModelProperties.erase_round]
    exact ((Restated.sgRowData_sts facts S Sched x m w).2 r' B hB).1
  exact Nat.le_of_lt_succ (facts.fc.mem_latest_window_lt
    (Restated.rawView_round_mem_window facts hidx S.hc.η_SG (r + 1) cutoff q X hX tok htok))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `m` is the last step before a phase instant of round `r + 1`, then round `r`'s action instant
    is at or before the time of step `m`. -/
theorem action_le_time_of_stepBefore (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) {r : Round} {m : Nat}
    {p : Protocol.Phase}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p)) :
    (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[m].time : Int) := by
  have hpos : 0 < (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ := by
    linarith only [Restated.action_pos facts S r, S.E.Δ_pos]
  obtain ⟨k_1, hk_1⟩ := Restated.exists_tickStepAt facts x htd hpos
  obtain ⟨hk_1succ, -⟩ := Restated.tickStepAt_time facts x hk_1
  have hk_1m : k_1 < m := by
    by_contra hcon
    have h := hm.2 k_1 (Nat.le_of_not_lt hcon)
    rw [hk_1succ] at h
    exact absurd h (not_le_of_gt (Restated.action_delta_lt_domain_succ facts S r p))
  have hjtime : (x[k_1 + 1].time : Int) ≤ (x[m].time : Int) :=
    Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt hk_1m)
  have hdpos := S.E.Δ_pos
  rw [hk_1succ] at hjtime
  linarith only [hjtime, hdpos]

end

end DecoupledConsensusModel.Sts.Restated
