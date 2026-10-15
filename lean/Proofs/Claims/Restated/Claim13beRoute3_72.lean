import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13b
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Claim13bStepKitStore
import Proofs.Claims.Restated.Claim13beRoute3_11
import Proofs.Claims.Restated.Claim13beRoute3_21
import Proofs.Claims.Restated.Claim13beRoute3_22
import Proofs.Claims.Restated.Claim13beRoute3_30
import Proofs.Claims.Restated.Claim13beRoute3_42
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Ladder
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_RoundTimes
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_72

/-!
# Honest height rows and the deadline bounds

Bounds on the heights of honest height rows by `topHonestRow`, and the arithmetic of the progress
deadline, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under unforgeable signatures, the height of an honest height row by step `n₀ + 1` is at most the
    largest `Σ.h_max` of any validator after `n₀ + 1` steps. -/
theorem honestRow_le_bound (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hunf : Restated.Unforgeability M S x) {n₀ : Nat} {h' : Height}
    (hrow : Restated.HonestRowAt M S Sched x n₀ h') :
    h' ≤ (Finset.univ : Finset V).sup fun w : V => (x[n₀ + 1][w].st).st.core.h_max := by
  obtain ⟨v, n', a, entry, tmo, hn', hv, hidx, hsent, hpair⟩ := hrow
  obtain ⟨k, hk, -, hle⟩ := Restated.heightVote_le_hmax_at_tick facts S Sched x hv hunf hidx hsent hpair
  have hkn : k ≤ n₀ + 1 := by omega
  exact (hle.trans (Restated.h_max_mono_sts facts S Sched x v hkn)).trans
    (Finset.le_sup (f := fun w : V => (x[n₀ + 1][w].st).st.core.h_max) (Finset.mem_univ v))

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under unforgeable signatures, the height of every vote that a validator honest through its send
    has in the sent log by step `n₀ + 1` is at most `topHonestRow S Sched x n₀`. -/
theorem honestRow_le_topHonestRow (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hunf : Restated.Unforgeability M S x) {n₀ : Nat} {h' : Height}
    (hrow : Restated.HonestRowAt M S Sched x n₀ h') :
    h' ≤ Restated.topHonestRow M S Sched x n₀ := by
  classical
  unfold Restated.topHonestRow
  exact Nat.le_findGreatest (Restated.honestRow_le_bound facts S Sched x hunf hrow) hrow

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If `topHonestRow S Sched x n₀` is positive, some validator honest through its send has a height
    vote at that height in the sent log by step `n₀ + 1`. -/
theorem topHonestRow_spec_of_pos (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {n₀ : Nat} (hpos : 0 < Restated.topHonestRow M S Sched x n₀) :
    Restated.HonestRowAt M S Sched x n₀ (Restated.topHonestRow M S Sched x n₀) := by
  classical
  unfold Restated.topHonestRow at hpos ⊢
  exact Nat.findGreatest_of_ne_zero rfl (Nat.pos_iff_ne_zero.mp hpos)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- The progress deadline from round `roundAt S tGAT + η_SG`, plus
    `2 · (7 · gap + 22 + 4 · S.extraRounds) + 2`, is exactly `cutBoundW S tGAT gap`. -/
theorem fgSafetyProgressDeadline_add_slack_eq_cutBoundW_l72 (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (tGAT : Int) (gap : Nat) :
    Restated.fgSafetyProgressDeadline (Setup.alwaysAwake S) rho
        (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds
      + 2 * (7 * gap + 22 + 4 * S.extraRounds) + 2
      = Restated.cutBoundW M S tGAT gap := by
  unfold Restated.fgSafetyProgressDeadline Restated.cutBoundW
  rw [progressLag_alwaysAwake_eq_l72]
  exact deadline_slack_nat_l72 _ _ _ _

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- The progress deadline from round `roundAt S tGAT + η_SG` is at most `cutBoundW S tGAT gap`. -/
theorem fgSafetyProgressDeadline_le_cutBoundW_l72 (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (tGAT : Int)
    (gap : Nat) :
    Restated.fgSafetyProgressDeadline (Setup.alwaysAwake S) rho
        (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds
      ≤ Restated.cutBoundW M S tGAT gap := by
  rw [← Restated.fgSafetyProgressDeadline_add_slack_eq_cutBoundW_l72 facts S rho tGAT gap]
  exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- For every run `rho`, the progress deadline from round `roundAt S tGAT + η_SG` at
    `Setup.alwaysAwake S` is `deadlineRoundW S tGAT gap`. -/
theorem fgSafetyProgressDeadline_eq_deadlineRoundW (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (tGAT : Int)
    (gap : Nat) :
    Restated.fgSafetyProgressDeadline (Setup.alwaysAwake S) rho
        (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds
      = Restated.deadlineRoundW M S tGAT gap := rfl

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If `t_GST ≤ tGAT` and `tGAT + healingLengthη S gap ≤ tE`, then
    `deadlineRoundW S tGAT gap ≤ switchRound S tE`. -/
theorem deadlineRoundW_le_switchRound (facts : Record.Facts M) (S : Setup V) (tGAT tE : Int) (gap : Nat) (rho : Record.Run V)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) :
    Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE := by
  rw [← Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts S rho]
  exact le_trans (Restated.fgSafetyProgressDeadline_le_cutBoundW_l72 facts S rho tGAT gap)
    (le_trans (Nat.le_add_right _ gap) (Restated.hη_of_healingLengthη' facts S tGAT tE gap hgst hlen))

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If `t_GST ≤ tGAT`, `tGAT + healingLengthη S gap ≤ tE` and the clock diverges, then, with `rW`
    the switch round, some step `N` has as its time the confirmation instant of slot
    `opening_slot rW + 2`, with `x[N].time ≤ tE`; the action instant of the deadline `dl` is at or
    before `S.a rW`; `S.a rW ≤ x[N].time`; `opening_slot dl + 1 ≤ opening_slot rW + 2`; `S.a rW` is
    at or before that confirmation instant; and that slot's vote instant plus `Δ` is at or before
    `x[N].time`. -/
theorem switchRound_instants (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tE : Int) (gap : Nat) (rho : Record.Run V)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (htd : Restated.TimeDiverges M x) :
    ∃ N : Nat,
      (x[N].time : Int)
        = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2) ∧
      (x[N].time : Int) ≤ tE ∧
      (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S))
        (Restated.fgSafetyProgressDeadline (Setup.alwaysAwake S) rho
          (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds)
        ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ∧
      (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (x[N].time : Int) ∧
      (M.opening_slot S.hc)
        (Restated.fgSafetyProgressDeadline (Setup.alwaysAwake S) rho
          (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds) + 1
        ≤ (M.opening_slot S.hc (Restated.switchRound M S tE)) + 2 ∧
      (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))
        ≤ M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2) ∧
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2) + S.E.Δ
        ≤ (x[N].time : Int) := by
  have hη : Restated.cutBoundW M S tGAT gap + gap ≤ Restated.switchRound M S tE :=
    Restated.hη_of_healingLengthη' facts S tGAT tE gap hgst hlen
  have hswne : Restated.switchRound M S tE ≠ 0 := Restated.switchRound_ne_zero_of_cutBoundW facts S tGAT tE gap hη
  have hsw := Restated.switchRound_spec facts S tE hswne
  have hdl : Restated.fgSafetyProgressDeadline (Setup.alwaysAwake S) rho
      (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds ≤ Restated.switchRound M S tE :=
    le_trans (Restated.fgSafetyProgressDeadline_le_cutBoundW_l72 facts S rho tGAT gap)
      (le_trans (Nat.le_add_right _ gap) hη)
  have hpos : (0 : Int) <
      M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2) :=
    lt_of_lt_of_le (Restated.action_pos facts S (Restated.switchRound M S tE)) (Restated.action_le_confirmation_third facts S _)
  obtain ⟨n, hn⟩ := Restated.exists_tickStepAt facts x htd hpos
  obtain ⟨hN, -⟩ := Restated.tickStepAt_time facts x hn
  refine ⟨n + 1, hN, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hN]; exact hsw
  · exact (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hdl
  · rw [hN]; exact Restated.action_le_confirmation_third facts S _
  · exact le_trans (Nat.add_le_add_right (facts.gr.opening_slot_mono S hdl) 1) (Nat.le_succ _)
  · exact Restated.action_le_confirmation_third facts S _
  · rw [hN]; exact facts.sch.vote_time_add_delta_le_confirmation_time S _

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If step `m` is the tick at `t` and `m + 1 ≤ N`, then along
    `Restated.runAllPath M S Sched x v N`, every validator `w`'s node state in the world at the
    index of the events strictly before `t` is the node state `w` holds in `x` after `m` steps. -/
theorem stateBeforeTime_runAll_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    {N m : Nat} {t : Int}
    (hm : Restated.tickStepAt M x m t) (hmN : m + 1 ≤ N) (w : V) :
    Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          t) w
      = x[m][w].st := by
  obtain ⟨h1, h0⟩ := Restated.tickStepAt_time facts x hm
  obtain ⟨l, hl, hlate⟩ := Restated.runEvents_append_late facts S Sched x (Nat.le_of_succ_le hmN)
  have hf1 : (Restated.runEvents M S Sched x m).filter
      (fun e => decide (Record.Event.time e < t)) = Restated.runEvents M S Sched x m := by
    refine List.filter_eq_self.2 (fun e he => ?_)
    have hle := (Restated.in_horizon_runAll_withHonest facts S Sched x v ∅ m e he).2
    have hlt : ((x[m].time : Nat) : Int) < t := by omega
    simp only [decide_eq_true_eq]
    exact lt_of_le_of_lt hle hlt
  have hf2 : l.filter (fun e => decide (Record.Event.time e < t)) = [] := by
    refine List.filter_eq_nil_iff.2 (fun e he => ?_)
    have hge := hlate e he
    simp only [decide_eq_true_eq, not_lt]
    rw [namedEvent_time_eq, ← h1]
    exact hge
  have hidx : Restated.strictEventIndex
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      t = (Restated.runEvents M S Sched x m).length := by
    show ((Restated.runEvents M S Sched x N).filter (fun e => decide (Record.Event.time e < t))).length = _
    rw [hl, List.filter_append, hf1, hf2, List.append_nil]
  rw [hidx]
  exact Restated.runAllPath_runEvents_length facts S Sched x v (Nat.le_of_succ_le hmN) w

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If, along `Restated.runAllPath M S Sched x v N`, `w` emitted `o` at `t`, then some step `k < N`
    is the tick at `t`, and `x[k + 1].sent` holds `o` signed by `w`. -/
theorem mem_sent_of_emits_runAll (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    {N : Nat} {w : V} {o : NamedObject V} {t : Int}
    (he : Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) w o t) :
    ∃ k : Nat, k < N ∧ Restated.tickStepAt M x k t ∧
      (⟨w, o⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent := by
  obtain ⟨idx, hidx, out, hout, hst, ho⟩ := he
  obtain ⟨k, hk, hmem, hcase⟩ :=
    Restated.runAllPath_at_event facts S Sched x v N idx hidx
  rcases hcase with ⟨t', he', -, -⟩ | ⟨t', he', hpre, hpost⟩ | ⟨o', t', he', -, -⟩
  · cases he'
  · obtain ⟨τ, hlbl, hτ, haw⟩ := Restated.tickAllAwake_of_mem_actionEventsOf hmem
    have ht' : t' = t := by
      simp only [Record.Event.node, Record.Event.tick.injEq, true_and] at he'
      exact he'.symm
    rw [ht'] at hpre
    have hpre' : Restated.runAllPath M S Sched x v N idx w = Record.wakeStage M Sched t x[k] w := hpre
    have hpost' : Restated.runAllPath M S Sched x v N (idx + 1) w = x[k + 1][w].st := hpost
    rw [hpre', ← hτ] at hout
    exact ⟨k, hk, ⟨τ, hlbl, hτ⟩,
      Restated.mem_sent_of_tick_of_state facts S Sched x hlbl haw
        (facts.nd.tick_send_eq_of_state (Setup.alwaysAwake S) w _ (τ : Int))
        hout (hpost'.symm.trans hst) ho⟩
  · cases he'

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the theorem's hypotheses, with `n₀` the tick step at round `r`'s action instant and `N` a
    step at or after `n₀ + 1` whose time is at most `tAwakeEnd` and at least `S.a r`, the largest
    `Σ.h_max` an honest active attester of round `r` holds after `n₀` steps, minus one, is at most
    `topHonestRow S Sched x n₀`. -/
theorem hmaxRoundAt_sub_one_le_topHonestRow_atRound (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tAwakeEnd : Int}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    {r : Round} {n₀ N : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hn₀N : n₀ + 1 ≤ N) (hn : (x[N].time : Int) ≤ tAwakeEnd)
    (hrWN : (Restated.Vocabulary.Execution.Setup.a M S (r)) ≤ (x[N].time : Int)) :
    Restated.hmaxRoundAt M S Sched x (r) n₀ - 1 ≤ Restated.topHonestRow M S Sched x n₀ := by
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  obtain ⟨hn₀1, -⟩ := Restated.tickStepAt_time facts x hn₀
  have hsup : Restated.hmaxRoundAt M S Sched x (r) n₀
      ≤ Restated.topHonestRow M S Sched x n₀ + 1 := by
    unfold Restated.hmaxRoundAt
    refine Finset.sup_le fun u _ => ?_
    show (x[n₀][u].st).st.core.h_max ≤ Restated.topHonestRow M S Sched x n₀ + 1
    by_cases hlarge : 1 < (x[n₀][u].st).st.core.h_max
    · have hread : Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            ((Restated.Vocabulary.Execution.Setup.a M S (r)))) u = x[n₀][u].st :=
        Restated.stateBeforeTime_runAll_tick facts S Sched x v hn₀ hn₀N u
      have hlarge' : 1 < (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            ((Restated.Vocabulary.Execution.Setup.a M S (r)))) u).st.h_max := by
        rw [hread]; exact hlarge
      obtain ⟨b, tb, hb, hemit, htb, hrow, -⟩ :=
        Restated.frontier_confirmationWitnessOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
          hHs (fun _ => Finset.subset_univ _)
          (honestWeightMajorityOn_of_belowOneThirdOn hbelow) hrWN hlarge'
      rw [hread] at hrow
      obtain ⟨k, -, hk, hsent⟩ := Restated.mem_sent_of_emits_runAll facts S Sched x v hemit
      obtain ⟨hk1, -⟩ := Restated.tickStepAt_time facts x hk
      have hkn : k + 1 ≤ n₀ + 1 := by
        by_contra hcon
        have hmono' : ((x[n₀ + 1].time : Nat) : Int) ≤ ((x[k + 1].time : Nat) : Int) := by
          exact_mod_cast Restated.time_mono facts S Sched x (by omega)
        have : (Restated.Vocabulary.Execution.Setup.a M S (r)) ≤ tb := by
          rw [← hn₀1, ← hk1]; exact hmono'
        exact absurd htb (not_lt.mpr this)
      have hbk : b.val_index ∈ Finset.univ \ Sched.adv (x[k + 1].time : Int) := by
        rw [hk1]
        exact hHs _ _ htb.le hb
      have hhon : Restated.HonestThrough M Sched x (k + 1) b.val_index :=
        Restated.honestThrough_of_mem_notHeld facts S Sched x (k + 1) hmono _ hbk
      obtain ⟨entry, tmo, hpair⟩ := heightPair_vote_of_height_l72 hrow
      have hle := Restated.honestRow_le_topHonestRow facts S Sched x hvalid.toUnforgeability
        ⟨b.val_index, k + 1, b, entry, tmo, hkn, hhon, rfl, hsent, hpair⟩
      exact Nat.sub_le_iff_le_add.mp hle
    · exact (Nat.le_of_not_lt hlarge).trans (Nat.le_add_left 1 _)
  exact Nat.sub_le_iff_le_add.mpr hsup

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the theorem's hypotheses, for a round `r` at or after the deadline round, with `n₀` the
    tick step at `S.a r` and `N` a step whose time lies between `S.a r` and `tAwakeEnd`, there is a
    run-scoped regime on `runAll M S Sched x v N`, read along `Restated.runAllPath M S Sched x v N`
    over the validators not held, from base round `roundAt S tGAT + η_SG + 2`, whose source round is
    at or before `r`, whose checkpoint's chain-state height is the larger of
    `topHonestRow S Sched x n₀` and the regime's height plus one, and that height is at least
    `topHonestRow S Sched x n₀` and at least the largest `Σ.h_max` of an honest active attester of
    round `r` after `n₀` steps minus one. -/
theorem switchRoundRegime_runAll_notHeld_atRound (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tAwakeEnd : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    {r : Round} (hrD : Restated.deadlineRoundW M S tGAT gap ≤ r)
    {n₀ N : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hNlo : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int)) (hNhi : (x[N].time : Int) ≤ tAwakeEnd) :
    ∃ (blocked : Height) (first i : Nat) (a : NamedAttestation V) (ta : Int)
      (Cfg T Tprev : NamedBlock V) (c0 : Round),
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 ∧
      a.round ≤ r ∧
      (M.derive_named S.E S.cfg T).h = max (Restated.topHonestRow M S Sched x n₀) (blocked + 1) ∧
      Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h ∧
      Restated.hmaxRoundAt M S Sched x (r) n₀ - 1
        ≤ (M.derive_named S.E S.cfg T).h := by
  classical
  have hdlrW : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S))
      (Restated.fgSafetyProgressDeadline (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds)
      ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := by
    apply (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
    rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]
    exact hrD
  have hn : (x[N].time : Int) ≤ tAwakeEnd := hNhi
  have hrWN : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) := hNlo
  obtain ⟨hn₀1, hn₀0⟩ := Restated.tickStepAt_time facts x hn₀
  have hn₀N : n₀ + 1 ≤ N := by
    by_contra hcon
    have hle : ((x[N].time : Nat) : Int) ≤ ((x[n₀].time : Nat) : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (by omega)
    linarith
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hX : ∀ t : Int, 0 ≤ t → notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ _ => Finset.subset_univ _
  have hXXb : (Finset.univ : Finset V) ⊆ Finset.univ := Finset.Subset.refl _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  obtain ⟨hpost, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hgstR0 := Restated.Vocabulary.Proofs.HealingSurface.gstLagged_le_Γ_neg1_of_gst_le_a facts S (Restated.roundAt M S tGAT + S.hc.η_SG) hpost
  have hgstLo := Restated.lo_add_lag_le_Γ_neg1_l71 facts S (Restated.roundAt M S tGAT + S.hc.η_SG)
    (Restated.roundAt_lo_le_rGST_l71 facts S tGAT)
  obtain ⟨blocked, first, Tprev, hfirst, hbase⟩ :=
    Restated.exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadline_runAll_notHeld facts S Sched x v N
      hsync hmono hawake hgst hcv hvalid hawm hthird hn hcom hrec (hdlrW.trans hrWN)
  have hband := Restated.hmaxRoundAt_sub_one_le_topHonestRow_atRound facts S Sched x v hsync hmono hawake hgst hcv
    hvalid hawm hthird hn₀ hn₀N hn hrWN
  by_cases hcase : blocked + 1 ≤ Restated.topHonestRow M S Sched x n₀
  · -- the row case
    obtain ⟨v', n', b, entry, tmo, hn', hv', hidx, hsent, hpair⟩ :=
      Restated.topHonestRow_spec_of_pos facts S Sched x (n₀ := n₀) (Nat.lt_of_lt_of_le (Nat.succ_pos _) hcase)
    obtain ⟨k, hkn', τ, hlbl, haw, out, hout, hst, ho⟩ :=
      Restated.tick_of_honest_signed_upTo_taken facts S Sched x v' (NamedObject.attest b) (x[n'].time : Int) hv'
        hvalid.toUnforgeability (by rw [author_attest, hidx]) n' le_rfl hsent
    have hkN : k < N := by omega
    have hemit' := Restated.emits_runAllPath_of_tick facts S Sched x v hkN hlbl haw hout hst ho
    have hemit : Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        b.val_index (Object.attest b) (τ : Int) := by
      rw [hidx]; exact hemit'
    have hτ : (τ : Int) = (Restated.Vocabulary.Execution.Setup.a M S b.round) := (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts _ _ hf.onePath hemit).2
    have hb : b.val_index ∈ notHeldAt Sched (τ : Int) := by
      rw [mem_notHeldAt, hidx]; exact (Finset.mem_sdiff.mp haw).2
    obtain ⟨n, hnEq⟩ : ∃ n : Nat, blocked + n + 1 = Restated.topHonestRow M S Sched x n₀ :=
      ⟨_, add_sub_succ_l72 _ _ hcase⟩
    have hrow : b.height_pair.erase.height? = some (blocked + n + 1) := by
      rw [hpair, hnEq]; exact height?_erase_vote_l72 _ _ _
    obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
      hbase.exists_regime_of_row_named facts hf hHs hHsXb hX hXXb hcomOn hbelow hgstR0 n hb
        hemit hrow hgstLo hloOpen
        (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake hn
          k hk u j hj)
    obtain ⟨-, hTheight'⟩ := hreg.checkpoint_runBlock facts hf hHsXb
    have hTheight : (M.derive_named S.E S.cfg T).h = blocked + n + 1 := hTheight'
    have hab : a.round ≤ b.round := hreg.minimal b (τ : Int) hb hemit hrow
    have hbrW : b.round ≤ r := by
      have hk1 : ((x[k + 1].time : Nat) : Int) = (τ : Int) := by
        exact_mod_cast (Restated.tickAllAwake_time facts S Sched x hlbl).2
      have hle : ((x[k + 1].time : Nat) : Int) ≤ ((x[n₀ + 1].time : Nat) : Int) := by
        exact_mod_cast Restated.time_mono facts S Sched x (by omega)
      apply (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).le_iff_le.mp
      rw [← hτ, ← hn₀1, ← hk1]
      exact hle
    refine ⟨blocked + n, first_n, i, a, ta, Cfg, T, Tprev', c0, hreg, hab.trans hbrW, ?_, ?_, ?_⟩
    · rw [hTheight, hnEq, max_self]
    · rw [hTheight, hnEq]
    · rw [hTheight, hnEq]; exact hband
  · -- the closed case
    have htop : Restated.topHonestRow M S Sched x n₀ < blocked + 1 := Nat.lt_of_not_le hcase
    obtain ⟨i, a, ta, Cfg, T, hreg⟩ :=
      hbase.exists_regime_closed facts hf hHs hHsXb hX hXXb hbelow hgstR0 hgstLo hloOpen
    have hi := hreg.seed.indexLtStop.trans_le hfirst
    have hfilter := Restated.filter_eq_takeOn facts _ (notHeldAt Sched) Finset.univ hf
      (fun e => decide (e.time ≤ (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S))
        (fgSafetyProgressDeadline (Setup.alwaysAwake S)
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds)))
      (Restated.downward_le _)
    have hmem : Record.Event.tick a.val_index ta ∈
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
          Record.Run V).events.take (inclusiveEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S)) (fgSafetyProgressDeadline (Setup.alwaysAwake S)
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
              Record.Run V)
            (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds))) := by
      apply List.mem_of_getElem? (i := i)
      rw [List.getElem?_take_of_lt hi]
      exact hreg.seed.exactTick
    simp only [inclusiveEventIndex] at hmem
    rw [← hfilter] at hmem
    have hadl : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round) ≤ (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S))
        (fgSafetyProgressDeadline (Setup.alwaysAwake S)
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds) := by
      simpa only [Record.Event.time, hreg.seed.actionTime_eq, decide_eq_true_eq, Record.Event.time] using
        (List.mem_filter.mp hmem).2
    have harW : a.round ≤ r :=
      (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).le_iff_le.mp (hadl.trans hdlrW)
    obtain ⟨-, hTheight'⟩ := hreg.checkpoint_runBlock facts hf hHsXb
    have hTheight : (M.derive_named S.E S.cfg T).h = blocked + 1 := hTheight'
    refine ⟨blocked, first, i, a, ta, Cfg, T, Tprev, a.round, hreg, harW, ?_, ?_, ?_⟩
    · rw [hTheight, max_eq_right htop.le]
    · rw [hTheight]; exact htop.le
    · rw [hTheight]; exact hband.trans htop.le

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the theorem's hypotheses, with `n₀` the tick step at the switch round's action instant and
    `N` a step whose time is the confirmation instant of the switch round's third slot, there is a
    run-scoped regime on `runAll M S Sched x v N`, read along `Restated.runAllPath M S Sched x v N`
    over the validators not held, from base round `roundAt S tGAT + η_SG + 2`, whose source round is
    at or before the switch round, whose checkpoint's chain-state height is the larger of
    `topHonestRow S Sched x n₀` and the regime's height plus one, and that height is at least
    `topHonestRow S Sched x n₀` and at least the largest `Σ.h_max` of an honest active attester of
    the switch round after `n₀` steps minus one. -/
theorem switchRoundRegime_runAll_notHeld (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tAwakeEnd : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tAwakeEnd) (htd : Restated.TimeDiverges M x)
    {n₀ N : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tAwakeEnd))))
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tAwakeEnd)) + 2)) :
    ∃ (blocked : Height) (first i : Nat) (a : NamedAttestation V) (ta : Int)
      (Cfg T Tprev : NamedBlock V) (c0 : Round),
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 ∧
      a.round ≤ Restated.switchRound M S tAwakeEnd ∧
      (M.derive_named S.E S.cfg T).h = max (Restated.topHonestRow M S Sched x n₀) (blocked + 1) ∧
      Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h ∧
      Restated.hmaxRoundAt M S Sched x (Restated.switchRound M S tAwakeEnd) n₀ - 1
        ≤ (M.derive_named S.E S.cfg T).h := by
  obtain ⟨N', hN', hN'E, -, hrWN', -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tAwakeEnd
    gap ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hNN' : (x[N].time : Int) = (x[N'].time : Int) := hN.trans hN'.symm
  exact Restated.switchRoundRegime_runAll_notHeld_atRound facts S Sched x v hsync hmono hawake hgst hcv hvalid
    hawm hthird hcom hrec
    (Restated.deadlineRoundW_le_switchRound facts S tGAT tAwakeEnd gap
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      hgst hlen)
    hn₀ (by rw [hNN']; exact hrWN') (by rw [hNN']; exact hN'E)

end

end DecoupledConsensusModel.Sts.Restated
