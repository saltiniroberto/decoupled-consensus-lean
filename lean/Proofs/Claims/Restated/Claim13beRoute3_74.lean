import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13beRoute3_22
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.Claim13beRoute3_30
import Proofs.Claims.Restated.Claim13beRoute3_42
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_65
import Proofs.Claims.Restated.Claim13beRoute3_70
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_74

/-!
# Node states at the switch round from the execution

Theorems relating the worlds of the run `runAll`, read along `Restated.runAllPath`, to the node
states of the execution, at the switch round, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open scoped DC
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event of index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₇₄ (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)) (t : Time) :
    Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t =
      Record.stateBeforeOf M S rho (strictEventIndex rho t) := by
  have hpre : rho.events.filter (fun e => decide (e.time < t)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
  show (rho.events.filter (fun e => decide (e.time < t))).foldlM (Record.worldStepOf M S)
      (fun v => M.initial S v) =
    (rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length).foldlM
      (Record.worldStepOf M S) (fun v => M.initial S v)
  rw [← hpre]

/-- In a run sorted by key, the world of a path `W` before the event of index
    `strictEventIndex rho t` is a world strictly before `t`. -/
private theorem mem_stateBeforeTime_along₇₄ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₇₄ S rho hsorted]
  exact (hW _).1

/-- The round-`r` action read computed from any node state has a node state. -/
private theorem actionReadFrom_nonempty₇₄ (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

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

/-- If the configurations up to step `m` are exactly those strictly before `t`, and `m + 1 ≤ N`,
    then along `Restated.runAllPath M S Sched x v N`, every validator `w`'s node state in the world
    at the index of the events strictly before `t` is the node state `w` holds in `x` after `m`
    steps. -/
theorem stateBeforeTime_runAll_stepBefore (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    {N m : Nat} {t : Int}
    (hm : Restated.stepBeforeInstant M x m t) (hmN : m + 1 ≤ N) (w : V) :
    Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          t) w
      = x[m][w].st := by
  obtain ⟨l, hl, hlate⟩ := Restated.runEvents_append_late facts S Sched x (Nat.le_of_succ_le hmN)
  have hf1 : (Restated.runEvents M S Sched x m).filter
      (fun e => decide (Record.Event.time e < t)) = Restated.runEvents M S Sched x m := by
    refine List.filter_eq_self.2 (fun e he => ?_)
    simp only [decide_eq_true_eq]
    have hle := (Restated.in_horizon_runAll_withHonest facts S Sched x v ∅ m e he).2
    have hle' : Record.Event.time e ≤ ((x[m].time : Nat) : Int) := hle
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · subst hm0
      simp [Restated.runEvents] at he
    · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel hpos).symm⟩
      subst hk
      exact lt_of_le_of_lt hle' (hm.1 k (Nat.lt_succ_self k))
  have hf2 : l.filter (fun e => decide (Record.Event.time e < t)) = [] := by
    refine List.filter_eq_nil_iff.2 (fun e he => ?_)
    have hge := hlate e he
    simp only [decide_eq_true_eq, not_lt]
    rw [namedEvent_time_eq]
    exact (hm.2 m le_rfl).trans hge
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

/-- If step `n₀` is the tick at `S.a rW` and `x[N].time` is the confirmation instant of slot
    `opening_slot rW + 2`, then `n₀ + 1 ≤ N`. -/
theorem succ_le_of_tick_switchRound_l74 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {tE : Int} {n₀ N : Nat}
    (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2)) :
    n₀ + 1 ≤ N := by
  obtain ⟨-, hn₀0⟩ := Restated.tickStepAt_time facts x hn₀
  have hac := Restated.action_le_confirmation_third facts S (Restated.switchRound M S tE)
  by_contra hcon
  have hle : ((x[N].time : Nat) : Int) ≤ ((x[n₀].time : Nat) : Int) := by
    exact_mod_cast Restated.time_mono facts S Sched x (by omega)
  linarith

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

/-- Under the theorem's hypotheses, for a regime on `runAll M S Sched x v N`, read along
    `Restated.runAllPath M S Sched x v N` over the validators not held, whose source round is at or
    before the switch round `rW`: for every validator `w` not held at `S.a rW`, every node state of
    `w`'s round-`rW` action read from its node state in that path's world before `S.a rW`, and every
    outcome of its attestation duty whose attestation `w` emits along that path at `S.a rW`, every
    block its SG vote can return is on one chain with the erasure of the regime's checkpoint `T`. -/
theorem sgEmissionsCompatible_at_switchRound (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE) :
    Restated.HonestSGEmissionsCompatibleAtRoundOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) (Restated.switchRound M S tE) T.erase := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
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
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE)) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (x[N].time : Int)
    rw [hN]
    exact Restated.action_le_confirmation_third facts S _
  rcases Nat.lt_or_ge a.round (Restated.switchRound M S tE) with hlt | hge
  · exact ((hreg.laterHistory_main facts hf hHs hHsXb hX hXXb hcomOn hbelow
      (Nat.succ_le_of_lt hlt) hlo
      (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake
        hn k hk u j hj)).2 hhor).1
  · have heq : a.round = Restated.switchRound M S tE := le_antisymm harW hge
    have hsrc := hreg.seed.sgEmissionsCompatible_of_source_of_frame_named facts hf hHs hHsXb
      hX hXXb hcomOn hreg.crossing hreg.frame hreg.c0le hreg.ready hreg.postPrev hlo
    rw [heq] at hsrc
    exact hsrc

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

/-- If `v'` is an honest active attester of the switch round `rW`, `a` a round-`rW` attestation
    naming `v'` that `v'` signed in the sent log after `n₀ + 1` steps, with `n₀` the tick step at
    `S.a rW` and `n₀ + 1 ≤ N`, then along `Restated.runAllPath M S Sched x v N`, `a` is every
    attestation `v'`'s round-`rW` action read from its node state in the world before `S.a rW` can
    compute, and `v'` emits `a` along that path at `S.a rW`. -/
theorem actionAttestation_of_sent_runAll (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (hmono : Sched.MonotoneCorruption)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) {tE : Int} {n₀ N : Nat}
    (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) (hn₀N : n₀ + 1 ≤ N)
    {v' : V} (hv' : v' ∈ Restated.HonRound M S Sched (Restated.switchRound M S tE)) {a : NamedAttestation V}
    (haround : a.round = Restated.switchRound M S tE) (hval : a.val_index = v')
    (hmem : (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₀ + 1].sent) :
    (∀ a' ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v')
        v' (Restated.switchRound M S tE), a = a') ∧
      Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        v' (Object.attest a)
        (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) := by
  have hvA : v' ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) := (Finset.mem_sdiff.1 hv').2
  have hthr : HonestThroughTime Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v' :=
    fun t' ht' hmem' => hvA (hmono t' _ ht' hmem')
  obtain ⟨hn₀1, -⟩ := Restated.tickStepAt_time facts x hn₀
  obtain ⟨k, hk, τ, hlbl, haw, out, hout, hst, hmemout⟩ :=
    Restated.tick_of_honest_signed_upTo_taken facts S Sched x v' (NamedObject.attest a) _ hthr
      hvalid.toUnforgeability (by rw [author_attest, hval]) (n₀ + 1) (le_of_eq hn₀1) hmem
  have hkN : k < N := lt_of_lt_of_le hk hn₀N
  have hemit := Restated.emits_runAllPath_of_tick facts S Sched x v hkN hlbl haw hout hst
    hmemout
  obtain ⟨-, hτ⟩ := Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts (Setup.alwaysAwake S)
    _ (Restated.OnePath_runAllPath facts S Sched x v N) hemit
  have hτ' : (τ : Int) = Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE) := by
    rw [← haround]; exact hτ
  have hkn : k = n₀ := Restated.tickStepAt_unique facts x ⟨τ, hlbl, hτ'⟩ hn₀
  subst hkn
  rw [hτ'] at hemit hout
  have hread := Restated.stateBeforeTime_runAll_tick facts S Sched x v hn₀ hn₀N v'
  refine ⟨?_, hemit⟩
  intro a' ha'
  rw [hread, ← Restated.actionAttestationFrom_wakeStage facts _ Sched
    (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) _ v'] at ha'
  have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (k) v' (Restated.Vocabulary.Execution.Setup.a M S (switchRound M S tE))
  have _hv_s2 := Record.runs_as_wakeStage facts S Sched x (k) v' (Restated.Vocabulary.Execution.Setup.a M S (switchRound M S tE))
  exact Restated.attest_of_tick_eq facts S v' _ (Restated.switchRound M S tE) hout hmemout a' ha'

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

/-- Under a valid execution with monotone corruption, if `n₀` is the tick step at `S.a rW` with
    `n₀ + 1 ≤ N`, `v'` an honest active attester of the switch round `rW`, `a` a round-`rW`
    attestation naming `v'` that `v'` signed in the sent log after `n₀ + 1` steps, and `C` a body of
    `v'`'s store after `n₀ + 1` steps whose root `a`'s `confirmed` field names, then along
    `Restated.runAllPath M S Sched x v N`, for every node state `n` of `v'`'s round-`rW` action read
    from its node state in the world before `S.a rW`, every outcome `A2` of the grade-2 block at `n`
    and every block `G` the SG vote can return at `n` with `A2`, `C` erases to `G`. -/
theorem erase_eq_actionSGBlockAt_runAll (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (hmono : Sched.MonotoneCorruption)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) {tE : Int} {n₀ N : Nat}
    (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) (hn₀N : n₀ + 1 ≤ N)
    {v' : V} (hv' : v' ∈ Restated.HonRound M S Sched (Restated.switchRound M S tE)) {a : NamedAttestation V}
    (haround : a.round = Restated.switchRound M S tE) (hval : a.val_index = v')
    (hmem : (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₀ + 1].sent)
    {C : NamedBlock V} (hC : C ∈ (x[n₀ + 1][v'].st).st.bodies)
    (hconf : a.confirmed = some C.root) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v')
        (Restated.switchRound M S tE),
      ∀ A2 : Option (Block V),
        M.grade2_block_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
          (M.toHealing n.st.core)
          (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) ⇢ A2 →
      ∀ G : Block V,
        M.get_sg_vote_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
          (M.toHealing n.st.core)
          (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) A2 ⇢ G →
        C.erase = G := by
  classical
  intro n hn A2 hA2 G hG
  have roots : Restated.RootCollisionFreeInLog M S Sched x := hvalid.idealization
  obtain ⟨haeq, -⟩ := Restated.actionAttestation_of_sent_runAll facts S Sched x v hmono hvalid
    hn₀ hn₀N hv' haround hval hmem
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract n.cache) (Setup.alwaysAwake S).E
    (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node v') n.st n.record
  have haD : a = D.2.2 := haeq D.2.2 ⟨n, hn, D.1, D.2.1, hD⟩
  obtain ⟨A, hA⟩ := facts.dt.round_action_with_nonempty (M.gradeContract n.cache)
    (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node v')
    (M.toHealing n.st.core) n.record
  have hrow := facts.dt.attest_with_row (M.gradeContract n.cache) (Setup.alwaysAwake S).E
    (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node v') n.st n.record D hD A hA
  have hconfG : D.2.2.confirmed = some G.root := by
    rw [hrow]
    exact facts.dt.round_action_with_confirmed _ _ _ _ _ _ A hA A2 hA2 G hG
  have hroot : C.root = G.root := by
    rw [← haD, hconf] at hconfG
    exact Option.some.inj hconfG
  have hsorted := Restated.sorted_runAll_withHonest_events facts S Sched x v
    (notHeldAt Sched (x[N].time : Int)) N
  have hP : Restated.Vocabulary.Execution.NamedRun.OnePath M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) := Restated.OnePath_runAllPath facts S Sched x v N
  have hmemW := mem_stateBeforeTime_along₇₄ hsorted hP
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE))
  have hmemT := Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts
    (Setup.alwaysAwake S) _ v' (Restated.switchRound M S tE) _ hmemW n hn A2 hA2 G hG
  have hread := Restated.stateBeforeTime_runAll_tick facts S Sched x v hn₀ hn₀N v'
  have hmemT' : G ∈ (x[n₀][v'].st).st.core.T := by
    rw [← hread]
    exact hmemT
  obtain ⟨Cn, hCnMem, hCnErase⟩ := Restated.exists_named_of_mem_tree facts S Sched x n₀ v' hmemT'
  obtain ⟨hn₀1, hn₀0⟩ := Restated.tickStepAt_time facts x hn₀
  have hvA : v' ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) := (Finset.mem_sdiff.1 hv').2
  have hthr1 : Restated.HonestThrough M Sched x (n₀ + 1) v' := by
    intro t' ht' hmem'
    exact hvA (hmono t' _ (by rw [← hn₀1]; exact ht') hmem')
  have hthr0 : Restated.HonestThrough M Sched x n₀ v' := by
    intro t' ht' hmem'
    exact hvA (hmono t' _ (by linarith) hmem')
  have hCnPlay : Restated.blockInLog M S Sched x Cn := Restated.blockInLog_of_mem_bodies facts S Sched hthr0 hCnMem
  have hCPlay : Restated.blockInLog M S Sched x C := Restated.blockInLog_of_mem_bodies facts S Sched hthr1 hC
  have hrc : C.root = Cn.root := by
    rw [hroot, ← Proofs.NamedWire.erase_root Cn, hCnErase]
  have hCCn : C = Cn :=
    roots.root_injective C Cn hCPlay hCnPlay C Cn
      (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self Cn)) hrc
  rw [hCCn, hCnErase]

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

/-- Under the theorem's hypotheses, for a regime on `runAll M S Sched x v N`, read along
    `Restated.runAllPath M S Sched x v N` over the validators not held, whose source round is at or
    before the switch round `rW`, and `n₀` the tick step at `S.a rW`, every SG block an honest
    active attester of the switch round attested to at that round lies on one chain with the
    regime's checkpoint `T`. -/
theorem sg_at_switchRound (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) :
    ∀ v ∈ Restated.HonRound M S Sched (Restated.switchRound M S tE), ∀ a : NamedAttestation V,
      a.round = Restated.switchRound M S tE → a.val_index = v →
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₀ + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n₀ + 1][v].st).st.bodies → a.confirmed = some C.root →
      Block.compatible C.erase T.erase = true := by
  intro v' hv' a' haround hval hmem C hC hconf
  have hn₀N := Restated.succ_le_of_tick_switchRound_l74 facts S Sched x hn₀ hN
  have hsgc := Restated.sgEmissionsCompatible_at_switchRound facts S Sched x v hsync hmono hawake
    hgst hcv hvalid hawm hthird hcom hlen htd hN hreg harW
  obtain ⟨haeq, hemit⟩ := Restated.actionAttestation_of_sent_runAll facts S Sched x v hmono hvalid
    hn₀ hn₀N hv' haround hval hmem
  have hvH : v' ∈ notHeldAt Sched
      (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE)) :=
    mem_notHeldAt.mpr (Finset.mem_sdiff.1 hv').2
  obtain ⟨n, hn⟩ := actionReadFrom_nonempty₇₄ facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v')
    (Restated.switchRound M S tE)
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract n.cache) (Setup.alwaysAwake S).E
    (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node v') n.st n.record
  have haD : a' = D.2.2 := haeq D.2.2 ⟨n, hn, D.1, D.2.1, hD⟩
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache)
    (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing n.st.core)
    (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s)
  obtain ⟨G, hG⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract n.cache)
    (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing n.st.core)
    (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) A2
  rw [Restated.erase_eq_actionSGBlockAt_runAll facts S Sched x v hmono hvalid hn₀ hn₀N hv' haround
    hval hmem hC hconf n hn A2 hA2 G hG]
  exact hsgc v' hvH n hn D hD (by rw [← haD]; exact hemit) A2 hA2 G hG

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

/-- Under a valid execution with monotone corruption, with `n₀` the tick step at `S.a rW` and `N` a
    step at the confirmation instant of the switch round's third slot, if
    `BaseSGOneChainAtSwitchRound` holds along `Restated.runAllPath M S Sched x v N`, then any two SG
    blocks honest active attesters of the switch round attested to at that round lie on one chain. -/
theorem sgPairwise_at_switchRound (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tE : Int} (hmono : Sched.MonotoneCorruption)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (hchain : Restated.BaseSGOneChainAtSwitchRound M S Sched x v tE N) :
    ∀ v ∈ Restated.HonRound M S Sched (Restated.switchRound M S tE), ∀ v' ∈ Restated.HonRound M S Sched (Restated.switchRound M S tE),
      ∀ a a' : NamedAttestation V,
      a.round = Restated.switchRound M S tE → a.val_index = v →
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₀ + 1].sent →
      a'.round = Restated.switchRound M S tE → a'.val_index = v' →
      (⟨v', NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x[n₀ + 1].sent →
      ∀ C C' : NamedBlock V,
      C ∈ (x[n₀ + 1][v].st).st.bodies → a.confirmed = some C.root →
      C' ∈ (x[n₀ + 1][v'].st).st.bodies → a'.confirmed = some C'.root →
      Block.compatible C.erase C'.erase = true := by
  intro v₁ hv₁ v₂ hv₂ a₁ a₂ hr₁ hval₁ hmem₁ hr₂ hval₂ hmem₂ C₁ C₂ hC₁ hconf₁ hC₂ hconf₂
  have hn₀N := Restated.succ_le_of_tick_switchRound_l74 facts S Sched x hn₀ hN
  have key : ∀ {u : V}, u ∈ Restated.HonRound M S Sched (Restated.switchRound M S tE) →
      ∀ {b : NamedAttestation V}, b.round = Restated.switchRound M S tE → b.val_index = u →
      (⟨u, NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∈ x[n₀ + 1].sent →
      ∀ {C : NamedBlock V}, C ∈ (x[n₀ + 1][u].st).st.bodies → b.confirmed = some C.root →
      ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) u)
        (Restated.switchRound M S tE),
      ∃ g : Option (Block V), M.grade2_block_with (M.gradeContract n.cache)
          (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing n.st.core)
          (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) ⇢ g ∧
        M.get_sg_vote_with (M.gradeContract n.cache)
          (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing n.st.core)
          (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) g ⇢ C.erase := by
    intro u hu b hr hval hmem C hC hconf
    obtain ⟨n, hn⟩ := actionReadFrom_nonempty₇₄ facts (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) u)
      (Restated.switchRound M S tE)
    obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache)
      (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing n.st.core)
      (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s)
    obtain ⟨G, hG⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract n.cache)
      (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing n.st.core)
      (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) A2
    have hCG := Restated.erase_eq_actionSGBlockAt_runAll facts S Sched x v hmono hvalid hn₀ hn₀N
      hu hr hval hmem hC hconf n hn A2 hA2 G hG
    exact ⟨n, hn, A2, hA2, by rw [hCG]; exact hG⟩
  obtain ⟨n₁, hn₁, g₁, hg₁, hG₁⟩ := key hv₁ hr₁ hval₁ hmem₁ hC₁ hconf₁
  obtain ⟨n₂, hn₂, g₂, hg₂, hG₂⟩ := key hv₂ hr₂ hval₂ hmem₂ hC₂ hconf₂
  exact hchain v₁ (mem_notHeldAt.mpr (Finset.mem_sdiff.1 hv₁).2)
    v₂ (mem_notHeldAt.mpr (Finset.mem_sdiff.1 hv₂).2)
    n₁ hn₁ g₁ hg₁ _ hG₁ n₂ hn₂ g₂ hg₂ _ hG₂

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

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the hypotheses of `grade1_atRound` on the execution, the regime and the named fact, the
    bundle holds along `Restated.runAllPath M S Sched x v N`, `r` is positive,
    `tGAT + 1 ≤ S.a (r − 1)`, and every round-`(r − 1)` SG emission along that path of a validator
    not held selects only blocks compatible with `T`'s erasure. -/
private theorem grade1_inputs₇₄ (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    {r : Round} {N : Nat}
    (hrWN : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int)) (hn : (x[N].time : Int) ≤ tE)
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ r)
    (hprev : a.round = r →
      Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T) :
    Restated.AdmissibleFieldsOn M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) }
        (Restated.runAllPath M S Sched x v N) (notHeldAt Sched) Finset.univ (tGAT + 1) ∧
      1 ≤ r ∧ tGAT + 1 ≤ (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) ∧
      Restated.HonestSGEmissionsCompatibleAtRoundOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) (r - 1) T.erase := by
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
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
  obtain ⟨hpredle, hrW1⟩ := pred_le_pred_pos_l74 a.round (r) hapos harW
  obtain ⟨-, -, hloPrev, -⟩ := Restated.loBounds_l70 facts S hapos hlo
  have hpost : tGAT + 1 ≤ (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) :=
    hloPrev.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hpredle)
  refine ⟨hf, hrW1, hpost, ?_⟩
  rcases round_cases_l74 a.round (r) harW with hlt | heq | heq
  · have hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (r - 1)) ≤
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
          Record.Run V).horizon := by
      show (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) ≤ (x[N].time : Int)
      exact (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le _ 1)).trans hrWN
    exact ((hreg.laterHistory_main facts hf hHs hHsXb hX hXXb hcomOn hbelow hlt hlo
      (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake
        hn k hk u j hj)).2 hhor).1
  · have hsrc := hreg.seed.sgEmissionsCompatible_of_source_of_frame_named facts hf hHs
      hHsXb hX hXXb hcomOn hreg.crossing hreg.frame hreg.c0le hreg.ready hreg.postPrev hlo
    rw [heq] at hsrc
    exact hsrc
  · exact hprev heq

end

end DecoupledConsensusModel.Sts.Restated
