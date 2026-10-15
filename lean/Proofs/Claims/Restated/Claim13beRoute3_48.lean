import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.ReceiptOutcome
import Proofs.Claims.Restated.Claim13beRoute3_25
import Proofs.Claims.Restated.Claim13beRoute3_27
import Proofs.Claims.Restated.Claim13beRoute3_30
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_OutageInputs
import Proofs.Claims.Restated.Vocabulary_Execution_OutageProvenance
import Proofs.Claims.Restated.Vocabulary_Execution_ReceiptCallsBase
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Inputs_ActionSources
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionSourceCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_FrameForward
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RecoveryCapturedActionCarrier
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RowTrace
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Admission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_SGArrival
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Alignment
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_ReceiptCallsF1
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedJointOutage
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Vocabulary_Protocol_Grades_LegacyVocabulary
import Proofs.Vocabulary.Protocol.Grades.RelativeOneChain
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_SGArrivalStampCarrier
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13beRoute3_48

/-!
# Action reads, emissions and SG arrival along a path of the run

Theorems about the action tick's read and emission, the first height progress, and the arrival,
sources and public cut of SG votes, stated over a model `M : Record.Model V` along the path `W` of
the bundle `AdmissibleFieldsOn`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC

/-! ## Helpers about event indices and paths -/

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event among the first `strictEventIndex rho t` events is at an
    instant before `t`. -/
private theorem time_lt_of_lt_strict₄₈ {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {j : Nat} {e : Record.Event V} (he : rho.events[j]? = some e) {t : Time}
    (hj : j < strictEventIndex rho t) : e.time < t := by
  have hpre : rho.events.filter (fun f => decide (f.time < t)) =
      rho.events.take (rho.events.filter (fun f => decide (f.time < t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e' f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
  have hj' : j < (rho.events.filter (fun f => decide (f.time < t))).length := hj
  have hmem : e ∈ rho.events.filter (fun f => decide (f.time < t)) := by
    rw [hpre]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj']; exact he)
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hmem).2

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event at index `j` with a time before `t` is among the first
    `strictEventIndex rho t` events. -/
private theorem lt_strict_of_time_lt₄₈ {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {j : Nat} {e : Record.Event V} (he : rho.events[j]? = some e) {t : Time} (ht : e.time < t) :
    j < strictEventIndex rho t := by
  by_contra hnot
  exact absurd ht (not_lt.mpr
    (Restated.le_time_of_index_ge_of_sorted hsorted
      (Nat.le_of_not_gt hnot) he))

/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` lead
    to from `W m`. -/
private theorem onePath_reach₄₈ {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (m : Nat) :
    ∀ k : Nat, W (m + k) ∈ ((rho.events.drop m).take k).foldlM (Record.worldStepOf M S) (W m) := by
  intro k
  induction k with
  | zero => exact Set.mem_singleton _
  | succ k ih =>
    have hstep := (hW (m + k)).2
    rw [Nat.add_sub_cancel_left] at hstep
    rw [List.take_add, List.foldlM_append, Set.bind_def, List.drop_drop]
    refine Set.mem_iUnion₂.mpr ⟨W (m + k), ih, ?_⟩
    rw [← Nat.add_assoc]
    exact hstep

/-- For every path `W` of `rho` and `m ≤ n`, `W n` is among the worlds the events `m` to `n - 1`
    lead to from `W m`. -/
private theorem onePath_slice₄₈ {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₄₈ W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, if the `i`-th event is `e`, the number of events with a time before
    `e`'s time is at most `i`. -/
private theorem strict_le_tick₄₈ {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {i : Nat} {e : Record.Event V} (hi : rho.events[i]? = some e) :
    strictEventIndex rho e.time ≤ i := by
  by_contra hnot
  have hlt : i < strictEventIndex rho e.time := Nat.lt_of_not_ge hnot
  exact lt_irrefl _ (time_lt_of_lt_strict₄₈ hsorted hi hlt)

/-- In a run sorted by key, the worlds strictly before the instant `t` are the worlds before the
    event of index `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₄₈ (S : Setup V) (rho : Record.Run V)
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

/-- In a run sorted by key, along every path `W` of `rho`, the world `W (strictEventIndex rho t)` is
    a world strictly before the instant `t`. -/
private theorem mem_stateBeforeTime_path₄₈ (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₄₈ S rho hsorted t]
  exact (hW _).1

/-- The action read of a woken node state is the action read of the node state. -/
private theorem actionReadFrom_wake₄₈ (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round) :
    Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (M.wake n) r =
      Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S n r := by
  unfold Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom
  rw [(facts.nd.wake_st_record n).1, (facts.nd.wake_st_record n).2, facts.nd.wake_cache n]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.NamedActionSources
open DecoupledConsensusModel.Execution.NamedActionReads

/-- Along the path `W` of the bundle, if the `i`-th event is `v`'s tick at `S.a r`, then `v`'s node
    state in `W i` is its node state in `W (strictEventIndex rho (S.a r))`, or that node state woken
    by `M.wake`. -/
theorem action_read_indexOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V)
    {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) :
    ∀ i v r, rho.events[i]? = some (.tick v ((Restated.Vocabulary.Execution.Setup.a M S r))) →
      W i v = W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v ∨
        W i v = M.wake (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) := by
  have hW := hf.onePath
  intro i v r hi
  have hle : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r) ≤ i :=
    strict_le_tick₄₈ hf.sorted hi
  exact Restated.Vocabulary.Proofs.NamedRuntime.tick_prefix_eq_strict_of_fields facts S rho hf.sorted
    hf.tickIndexUnique hi _ (mem_stateBeforeTime_path₄₈ S rho hf.sorted W hW _) _
    (onePath_slice₄₈ W hW hle)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.NamedActionSources
open DecoupledConsensusModel.Execution.NamedActionReads

/-- Along the path `W` of the bundle, if the `i`-th event is `v`'s tick at `S.a r`, every outcome of
    that tick sends the attestation of every outcome of `v`'s attestation duty on its action read
    when `v`'s node state in `W i` passes `M.awake_for_grade2` for round `r`, and sends nothing
    otherwise. -/
theorem action_emissionOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V)
    {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) :
    ∀ i v r, rho.events[i]? = some (.tick v ((Restated.Vocabulary.Execution.Setup.a M S r))) →
      ∀ out, M.tick S v (W i v) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out →
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
      (M.awake_for_grade2 S v (W i v) r ∧ out.2 = [.attest D.2.2]) ∨
        (¬ M.awake_for_grade2 S v (W i v) r ∧ out.2 = []) := by
  intro i v r hi out hout
  rcases Restated.action_read_indexOn facts S rho Hs Xb hf i v r hi with h | h
  · rw [h] at hout ⊢
    have _hr_s1 := facts.ndRun.stateBeforeOf_reachedNode S rho (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))) (hf.onePath (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))).1 v
    have _hv_s2 := facts.ndRun.stateBeforeOf_runs_as S rho (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))) (hf.onePath (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))).1 v
    exact Restated.Vocabulary.Proofs.NamedActionSources.tick_at_action facts S v _ r out hout
  · rw [h] at hout ⊢
    intro n hn
    have _hr_s3 := facts.nd.reachedNode_wake _ (facts.ndRun.stateBeforeOf_reachedNode S rho (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))) (hf.onePath (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))).1 v)
    have _hv_s4 := facts.nd.runs_as_wake _ v (facts.ndRun.stateBeforeOf_runs_as S rho (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))) (hf.onePath (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))).1 v)
    exact Restated.Vocabulary.Proofs.NamedActionSources.tick_at_action facts S v _ r out hout n
      (by rw [actionReadFrom_wake₄₈ facts]; exact hn)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.NamedActionSources
open DecoupledConsensusModel.Execution.NamedActionReads

/-- Along the path `W` of the bundle, `v` emits the attestation `row` at `S.a r` exactly when `v`
    ticks at `S.a r`, the node state each such tick reads passes the grade-2 awake test of round
    `r`, and `row` is the attestation of every outcome of `v`'s attestation duty on its action read
    strictly before `S.a r`. -/
theorem action_run_emissionOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V)
    {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) :
    ∀ v r (row : NamedAttestation V), Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (.attest row) ((Restated.Vocabulary.Execution.Setup.a M S r)) ↔
      (∃ i : Nat, rho.events[i]? = some (Record.Event.tick v ((Restated.Vocabulary.Execution.Setup.a M S r)))) ∧
      (∀ i : Nat, rho.events[i]? = some (Record.Event.tick v ((Restated.Vocabulary.Execution.Setup.a M S r))) →
        M.awake_for_grade2 S v (W i v) r) ∧
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
      row = D.2.2 := by
  have hW := hf.onePath
  intro v r row
  have hex : ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      ∃ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D := by
    obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc _
      (Restated.Vocabulary.Execution.Setup.a M S r) _
    obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c)
      S.E S.hc (M.ns_setClock S.E
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st
        (Restated.Vocabulary.Execution.Setup.a M S r))
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
    exact ⟨_, ⟨c, hc, st, hst, rfl⟩, facts.dt.attest_with_nonempty _ S.E S.hc (S.node v) _ _⟩
  obtain ⟨n₀, hn₀, D₀, hD₀⟩ := hex
  constructor
  · rintro ⟨i, hi, out, hout, -, hrow⟩
    have hawake : M.awake_for_grade2 S v (W i v) r := by
      rcases Restated.action_emissionOn facts S rho Hs Xb hf i v r hi out hout n₀ hn₀ D₀ hD₀ with
        ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · rw [h] at hrow
        exact absurd hrow List.not_mem_nil
    refine ⟨⟨i, hi⟩, fun j hj => ?_, ?_⟩
    · obtain rfl := Restated.tick_index_eq_of_unique hf.tickIndexUnique hi hj
      exact hawake
    intro n hn D hD
    rcases Restated.action_emissionOn facts S rho Hs Xb hf i v r hi out hout n hn D hD with
      ⟨-, h⟩ | ⟨hno, -⟩
    · rw [h] at hrow
      simpa only [List.mem_singleton, NamedObject.attest.injEq] using hrow
    · exact absurd hawake hno
  · rintro ⟨⟨i, hi⟩, hawake, hrow⟩
    rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_tick facts S rho hi (W i) (hW i).1
        (W (i + 1)) (hW i).2 with ⟨out, hout, hw⟩ | ⟨hnone, -⟩
    · refine ⟨i, hi, out, hout, hw, ?_⟩
      rcases Restated.action_emissionOn facts S rho Hs Xb hf i v r hi out hout n₀ hn₀ D₀ hD₀ with
        ⟨-, h⟩ | ⟨hno, -⟩
      · rw [h, hrow n₀ hn₀ D₀ hD₀]
        exact List.mem_singleton_self _
      · exact absurd (hawake i hi) hno
    · obtain ⟨out, hout⟩ := hf.tick_outcome i v _ hi
      exact absurd hout (hnone out)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- If `1 ≤ H` and the maximum `h_max` over `X` in the world `W stop` exceeds `H`, some index
    `first ≤ stop` is where that maximum, read along `W`, first reaches `H + 1`. -/
theorem exists_firstHeightProgressAtOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {H : Height} (hH : 1 ≤ H) {stop : Nat}
    (hcross : H < X.sup fun v => (W stop v).st.h_max) :
    ∃ first : Nat, first ≤ stop ∧ Restated.FirstHeightProgressAtOn M S rho W X H first := by
  have hzero : (X.sup fun v => (W 0 v).st.h_max) ≤ 1 := by
    apply Finset.sup_le
    intro v _
    have h0 : (W 0 v).st = (M.ns_initial : M.NS) := by
      rw [show W 0 = fun u => M.initial S u from (hf.onePath 0).1]
      exact facts.nd.initial_st_inclG2 S v
    exact ((congrArg (fun st : M.NS => st.core.h_max) h0).trans
      facts.hd.namedStore_initial_h_max).le
  obtain ⟨first, hpos, hstop, hbefore, hfrontier⟩ :=
    Restated.exists_least_honestHMaxBeforeIndex_crossingOn facts S Hs Xb X hf (Nat.zero_le stop)
      (hzero.trans hH) hcross
  exact ⟨first, hstop, hpos, hfrontier, fun i hi => hbefore i (Nat.zero_le i) hi⟩

/-! ## Helpers about SG arrival -/

/-- The action instant of every round is a public instant. -/
private theorem publicTime_a₄₈ (facts : Record.Facts M) (S : Setup V) (r : Round) :
    PublicTime S (Restated.Vocabulary.Execution.Setup.a M S r) := by
  show PublicTime S (M.a S.hc S.E.Δ r)
  rw [facts.sch.a_eq_confirmation_time]
  exact Restated.Vocabulary.Proofs.Optimistic.publicTime_confirmation_time facts S _

/-- When the `i`-th event of `rho` is a wake of `v`, every world that event leads to from `w₁` is
    `w₁` with `v`'s node state woken by `M.wake`. -/
private theorem stateBefore_wake_eq₄₈ (S : Setup V) (rho : Record.Run V)
    {i : Nat} {v : V} {t : Time} (hi : rho.events[i]? = some (.wake v t)) (w₁ w₂ : V → M.N)
    (hw₂ : w₂ ∈ ((rho.events.drop i).take (i + 1 - i)).foldlM (Record.worldStepOf M S) w₁) :
    w₂ = Function.update w₁ v (M.wake (w₁ v)) := by
  have hl : (rho.events.drop i).take (i + 1 - i) = [Record.Event.wake v t] := by
    rw [Nat.add_sub_cancel_left, List.take_one, List.head?_drop, hi]
    rfl
  rw [hl, List.foldlM_cons, Set.bind_def] at hw₂
  obtain ⟨w', hw', h2⟩ := Set.mem_iUnion₂.mp hw₂
  have h2' : w₂ = w' := h2
  subst h2'
  exact hw'

/-- When the `i`-th event of `rho` is a wake of `v`, `v`'s store in every world that event leads to
    from `w₁` is `v`'s store in `w₁`. -/
private theorem stateBefore_wake_st₄₈ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    {i : Nat} {v : V} {t : Time} (hi : rho.events[i]? = some (.wake v t)) (w₁ w₂ : V → M.N)
    (hw₂ : w₂ ∈ ((rho.events.drop i).take (i + 1 - i)).foldlM (Record.worldStepOf M S) w₁) :
    (w₂ v).st = (w₁ v).st := by
  rw [stateBefore_wake_eq₄₈ S rho hi w₁ w₂ hw₂, Function.update_self,
    (facts.nd.wake_st_record _).1]

/-- For every path `W` of `rho`, in every world `W i` the slot of `v`'s store is the slot of its
    clock. -/
private theorem slot_clock_along₄₈ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V) :
    ∀ i : Nat, (W i v).st.core.s = S.E.slotOf (W i v).st.core.t := by
  intro i
  induction i with
  | zero =>
    have h0 : W 0 = fun u => M.initial S u := (hW 0).1
    rw [h0]
    show (M.initial S v).st.core.s = S.E.slotOf (M.initial S v).st.core.t
    rw [facts.nd.initial_st, facts.hd.initial_core_s, facts.hd.initial_core_t,
      _root_.DecoupledConsensusModel.Proofs.ModelProperties.slotOf_zero]
  | succ n ih =>
    obtain ⟨hn, hstep⟩ := hW n
    cases hev : rho.events[n]? with
    | none =>
      have hlen : rho.events.length ≤ n := List.getElem?_eq_none_iff.mp hev
      rw [List.drop_eq_nil_of_le hlen, List.take_nil, List.foldlM_nil] at hstep
      have hsame : W (n + 1) = W n := hstep
      rw [hsame]
      exact ih
    | some e =>
      by_cases hv : v = e.node
      · cases e with
        | wake u t =>
          change v = u at hv
          subst hv
          rw [stateBefore_wake_st₄₈ facts S rho hev (W n) (W (n + 1)) hstep]
          exact ih
        | tick u t =>
          change v = u at hv
          subst hv
          rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_tick facts S rho hev (W n) hn
              (W (n + 1)) hstep with ⟨out, hout, hw⟩ | ⟨-, hw⟩
          · rw [hw, (facts.nd.tick_clock S v (W n v) t out hout).1,
              (facts.nd.tick_clock S v (W n v) t out hout).2]
          · rw [hw]
            exact ih
        | deliver u o t =>
          change v = u at hv
          subst hv
          rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho hev (W n) hn
              (W (n + 1)) hstep with hproc | ⟨-, hw⟩
          · rw [(facts.nd.process_clock S (W n v) o (W (n + 1) v) hproc).1,
              (facts.nd.process_clock S (W n v) o (W (n + 1) v) hproc).2]
            exact ih
          · rw [hw]
            exact ih
      · rw [Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_other facts S rho hev v hv (W n) hn
          (W (n + 1)) hstep]
        exact ih

/-- Setting the clock of `st` leaves its SG vote stamps unchanged. -/
private theorem setClock_timestamp_sg_vote₄₈ (facts : Record.Facts M) (E : Env V) (st : M.NS)
    (t : Time) :
    (M.ns_setClock E st t).core.timestamp_sg_vote = st.core.timestamp_sg_vote := by
  rw [← facts.gr.gradeView_timestamp_sg_vote (M.ns_setClock E st t).core,
    facts.hd.setClock_gradeView, facts.gr.gradeView_timestamp_sg_vote]

/-- Every store the confirmation duty can return on `st` has the SG vote stamps of `st`. -/
private theorem confirmation_timestamp_sg_vote₄₈ (facts : Record.Facts M) (gc : M.Contract)
    (E : Env V) (hc : Protocol.HealConfig) (st : M.NS) (s : Slot) (D : M.NS)
    (hD : M.duties_update_confirmation_with gc E hc st s ⇢ D)
    (hn : M.reachedCore st.core := by trivial) :
    D.core.timestamp_sg_vote = st.core.timestamp_sg_vote := by
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty gc E hc st.core s
  rw [facts.dt.named_update_confirmation_with_core gc E hc st s D hD X hX,
    ← facts.gr.gradeView_timestamp_sg_vote X,
    facts.dt.update_confirmation_with_toHealing_gradeView gc E hc st.core s X hX hn,
    facts.gr.gradeView_timestamp_sg_vote]

/-- A store with the rows, the SG vote stamps and the clock of a store satisfying `Data` at `bound`
    satisfies `Data` at `bound`. -/
private theorem data_fields₄₈ {bound : Time} {st out : M.NS}
    (h : Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M bound st)
    (hr : out.sg_rows = st.sg_rows)
    (hs : out.core.timestamp_sg_vote = st.core.timestamp_sg_vote)
    (ht : out.core.t = st.core.t) :
    Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M bound out :=
  ⟨by rw [ht]; exact h.1, by rw [hr, hs]; exact h.2⟩

/-- If `st` satisfies `Data` at `bound` and `t ≤ bound`, so does `st` with its clock set to `t`. -/
private theorem clock_data₄₈ (facts : Record.Facts M) (S : Setup V) (bound : Time) (st : M.NS)
    (t : Time) (ht : t ≤ bound)
    (hd : Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M bound st) :
    Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M bound (M.ns_setClock S.E st t) :=
  ⟨by rw [facts.hd.ModelProperties_setClock_core_t]; exact ht,
    by rw [facts.hd.setClock_sg_rows, setClock_timestamp_sg_vote₄₈ facts]; exact hd.2⟩

/-- If `st` is coherent and satisfies `Data` at `bound`, so does the store the admission of the rows
    `rows` returns on `st`. -/
private theorem rows_data₄₈ (facts : Record.Facts M) (S : Setup V) (bound : Time) (st : M.NS)
    (rows : List (NamedAttestation V))
    (hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg st)
    (hd : Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M bound st) :
    Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M bound
      (M.admit_rows S.hc st rows) :=
  facts.hd.sgArrival_rows_data S bound st rows hcoh hd

/-- On every path `W` of `rho`, if the `i`-th event delivers `o` to `v`, `v`'s store in `W (i + 1)`
    is `M.make_grades_compatible_with_finalized` of the store the receipt of `o` returns on `v`'s
    store in `W i`. -/
private theorem deliver_post₄₈ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {i : Nat} {v : V} {o : NamedObject V} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (hout : ∃ n' : M.N, M.process S (W i v) o ⇢ n') :
    (W (i + 1) v).st =
      M.make_grades_compatible_with_finalized (M.receipt_process S (W i v).st o) := by
  obtain ⟨hWi, hstep⟩ := hW i
  rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho he (W i) hWi
      (W (i + 1)) hstep with hproc | ⟨hno, -⟩
  · exact facts.nd.process_st S (W i v) o (W (i + 1) v) hproc
  · obtain ⟨n', hn'⟩ := hout
    exact absurd hn' (hno n')

/-- On every path `W` of `rho`, if a block call of `B` at `reader` at the `i`-th event has input
    `before`, every row the block handler holds in its own round's rows on `before` is held by
    `reader`'s store in `W (i + 1)`. -/
private theorem block_call_rows_after_event₄₈ (facts : Record.Facts M) (S : Setup V)
    (rho : Record.Run V) (W : Nat → V → M.N)
    (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    -- every delivery event has an outcome from the node state in `W i`
    (hreceipt : ∀ (i : Nat) (v : V) (o : NamedObject V) (t : Int),
      rho.events[i]? = some (Record.Event.deliver v o t) →
      ∃ n' : M.N, M.process S (W i v) o ⇢ n')
    {i : Nat} {reader : V} {B : NamedBlock V} {before : M.NS}
    (hcall : Restated.Vocabulary.Execution.NamedReceiptCalls.blockCallAt M S rho W i reader B before)
    (a : NamedAttestation V)
    (ha : a ∈ (M.on_block_with .alsoCarried S.E S.hc S.cfg before B).sg_rows a.round) :
    a ∈ (W (i + 1) reader).st.sg_rows a.round := by
  have _hr_0 : M.reachedNode (W i reader) := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hW i).1 reader
  have _hv_0 : M.runs_as (W i reader) reader := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hW i).1 reader
  obtain ⟨hWi, -⟩ := hW i
  rcases hcall with ⟨t, he, rfl⟩ | ⟨t, he, ⟨out, hout, hw, hem⟩, rfl⟩
  · rw [deliver_post₄₈ facts S rho W hW he (hreceipt _ _ _ _ he),
      facts.nd.make_grades_compatible_with_finalized_sg_rows, facts.nd.process_block]
    exact ha
  · obtain ⟨hpos, hprop, hproposer⟩ :=
      (facts.nd.block_mem_on_tick_emit S reader (W i reader) t out hout hem).1
    have hdue : 0 < S.E.slotOf t ∧ t = M.proposal_time S.E (S.E.slotOf t) ∧
        S.E.proposer (S.E.slotOf t) = (S.node reader).val_index ∧
        M.awake_for_grade1 S reader (W i reader) (M.round_of S.hc (S.E.slotOf t)) :=
      ⟨hpos, hprop, hproposer.trans (S.node_val_index reader).symm,
        facts.nd.block_mem_on_tick_emit_awake S reader (W i reader) t out hout hem⟩
    obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W i reader).st.core.toHealing t
      (W i reader).cache
    obtain ⟨D, hD⟩ := facts.dt.propose_block_with_nonempty S reader (W i reader) t out hout
      (facts.nd.block_mem_on_tick_emit S reader (W i reader) t out hout hem).1.1 (facts.nd.block_mem_on_tick_emit S reader (W i reader) t out hout hem).1.2.1
      (facts.nd.block_mem_on_tick_emit S reader (W i reader) t out hout hem).1.2.2
      (facts.nd.block_mem_on_tick_emit_awake S reader (W i reader) t out hout hem) c hc
    have hcallEq := Restated.Vocabulary.Proofs.NamedReceiptCallsBase.self_proposal_call facts S rho
      he (W i) hWi out hout hem c hc D hD
    rw [hw]
    apply (facts.nd.tick_rows_after_proposal_of_outcomes S reader (W i reader) t out hout).1 hdue
      c hc D hD a
    rw [hcallEq]
    simp only [facts.nd.store_with_cache_sg_rows]
    exact ha

/-- If `st` is coherent, every entry `b` of its round-`k` SG pool is the erasure of a named
    attestation held in its round-`k` rows. -/
private theorem pool_full_witness₄₈ (facts : Record.Facts M) (S : Setup V) (st : M.NS)
    (hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg st) (k : Round)
    (b : CombinedAttestation V) (hb : b ∈ M.store_sg_pool st.core k) :
    ∃ named : NamedAttestation V, named ∈ st.sg_rows k ∧ named.erase = b := by
  have hpool : b ∈ st.core.sg_votes k := (facts.sto.ModelProperties_mem_sg_pool_iff _ _ _).mp hb
  rw [hcoh.2.2.2.1 k] at hpool
  exact List.mem_map.mp hpool

/-- In a named store whose bodies contain genesis and the parent of each body, every named ancestor
    of a held body is held. -/
private theorem namedAncestor_mem₄₈ {st : M.NS}
    (hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node p s r gv gsv ats proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (by simpa only [NamedBlock.parent] using hpc.2 _ hB)
          (by unfold NamedBlock.Preceq; exact hparent)

/-- Every node state the round-`r` action read can yield from `before` holds the bodies `before`
    holds. -/
private theorem actionReadFrom_bodies₄₈ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      nr.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
    facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

/-- Along a path `W` of `rho`, if `reader` accepts the row `a` at index `j` at `accepted`, then
    either that event is `reader`'s tick at `accepted` and the SG vote stamp of `a` in `reader`'s
    store in `W (j + 1)` is `accepted`, or it is a delivery to `reader` at `accepted` and the stamp
    is `reader`'s clock in `W j`. -/
private theorem accepted_row_stamp_cases₄₈ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {j : Nat} {reader : V} {a : NamedAttestation V} {accepted : Time}
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W j reader (.attest a) accepted) :
    (rho.events[j]? = some (.tick reader accepted) ∧
      (W (j + 1) reader).st.core.timestamp_sg_vote (M.sgVote a.erase) = some (accepted : Stamp)) ∨
    (∃ o : NamedObject V, rho.events[j]? = some (.deliver reader o accepted) ∧
      (W (j + 1) reader).st.core.timestamp_sg_vote (M.sgVote a.erase) =
        some ((W j reader).st.core.t : Stamp)) := by
  obtain ⟨⟨-, e, he, hnode, het⟩, hpre', hpost'⟩ := hacc
  have hpre : a ∉ (W j reader).st.sg_rows a.round := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not] using hpre'
  have hpost : a ∈ (W (j + 1) reader).st.sg_rows a.round := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hpost'
  cases e with
  | wake v t =>
    change v = reader at hnode
    subst hnode
    rw [stateBefore_wake_st₄₈ facts S rho he (W j) (W (j + 1)) (hW j).2] at hpost
    exact absurd hpost hpre
  | tick v t =>
    change v = reader at hnode
    change t = accepted at het
    subst hnode
    subst het
    left
    refine ⟨he, ?_⟩
    rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_tick facts S rho he (W j) (hW j).1
        (W (j + 1)) (hW j).2 with ⟨out, hout, hw⟩ | ⟨-, hw⟩
    · rw [hw] at hpost ⊢
      exact facts.nd.node_tick_sg_row_stamp S v (W j v) t out hout
        (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho j v (W j)
          (hW j).1).1.1.1 a hpre hpost
    · rw [hw] at hpost
      exact absurd hpost hpre
  | deliver v o t =>
    change v = reader at hnode
    change t = accepted at het
    subst hnode
    subst het
    right
    refine ⟨o, he, ?_⟩
    have hout :=
      Restated.receipt_outcome_of_changedOn facts S hW he (fun h => by rw [h] at hpost; exact hpre hpost)
    rw [deliver_post₄₈ facts S rho W hW he hout, facts.nd.make_grades_compatible_with_finalized_sg_rows]
      at hpost
    rw [deliver_post₄₈ facts S rho W hW he hout,
      facts.nd.make_grades_compatible_with_finalized_core_timestamp_sg_vote]
    exact facts.nd.receipt_process_sg_row_stamp S _ o a hpre hpost

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Proofs.NamedSGArrival
local macro "sga% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.SGArrival)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedSGArrival ++ n.getId)))

/-- For every world `w₁` before event `i` and every world `w₂` before event `i + 1`, the reader's
    store in each satisfies `Data` at the event's instant: its clock and every held row's stamp are
    at or before that instant. -/
theorem data_at_eventOn_SGArrival (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {i : Nat} {e : Record.Event V}
    (he : rho.events[i]? = some e) (reader : V) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i, ∀ w₂ ∈ Record.stateBeforeOf M S rho (i + 1),
    Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M e.time (w₁ reader).st ∧
      Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M e.time (w₂ reader).st :=
  Restated.Vocabulary.Proofs.NamedSGArrival.data_at_event_of_fields facts S rho hf.sorted hf.in_horizon he reader

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Proofs.NamedSGArrival
local macro "sga% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.SGArrival)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedSGArrival ++ n.getId)))

/-- For every world `w₁` right after event `i`, a row `a` held in bucket `k` of the reader's store
    in `w₁` has round `k` and a stamp at or before that event's instant. -/
theorem held_row_own_and_stamp_at_eventOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {i : Nat} {e : Record.Event V}
    (he : rho.events[i]? = some e) (reader : V) (k : Round) (a : NamedAttestation V) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho (i + 1),
    a ∈ (w₁ reader).st.sg_rows k →
    a.round = k ∧ ∃ stamp : Time, stamp ≤ e.time ∧
      (w₁ reader).st.core.timestamp_sg_vote
        (M.sgVote a.erase) = some (stamp : Stamp) := by
  intro w₁ hw₁ ha
  have hn := (hf.in_horizon _ (List.mem_of_getElem? he)).1
  exact (facts.hdRun.sgArrival_prefix_data S rho e.time hn (i + 1)
    (fun j f hj hf' => Restated.event_time_le rho hf.sorted hf' he (Nat.le_of_lt_succ hj)) reader
    w₁ hw₁).2 k a ha

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Proofs.NamedSGArrival
local macro "sga% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.SGArrival)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedSGArrival ++ n.getId)))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Proofs.NamedSGArrival
local macro "sga% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.SGArrival)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedSGArrival ++ n.getId)))

/-- Along the path `W` of the bundle, if the reader is in `Hs (S.a q)` and `lo ≤ S.a q`, a delivery
    to it at `td` in `[S.a q, S.a q + Δ)`, the `i`-th event, finds its store in `W i` in round `q`. -/
theorem delivery_roundOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {i : Nat} {reader : V} {o : NamedObject V}
    {td : Time} (q : Round) (he : rho.events[i]? = some (.deliver reader o td))
    (hlo : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ td) (hhi : td < (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ)
    (hr : reader ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q))) (hgat : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q)) :
    (M.round_of S.hc (W i reader).st.core.s) = q := by
  have hW := hf.onePath
  have hmem := List.mem_of_getElem? he
  have htk := hf.tick_total ((Restated.Vocabulary.Execution.Setup.a M S q)) hgat reader hr (publicTime_a₄₈ facts S q)
    (hlo.trans (hf.in_horizon _ hmem).2)
  have hclock := Restated.tick_le_clock_before_deliveryOn_RawRelay facts S rho Hs Xb hf he htk hlo
  have hup := Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_clock_le_event facts S rho hf.sorted he
    (hf.in_horizon _ hmem).1 reader (W i) (hW i).1
  rw [slot_clock_along₄₈ facts S rho W hW reader i,
    Restated.Vocabulary.Proofs.HealingLemmas.slotOf_of_between_a facts S q hclock (hup.trans_lt hhi),
    facts.gr.HealingLemmas_round_of_opening_succ]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Proofs.NamedSGArrival
local macro "sga% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.SGArrival)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedSGArrival ++ n.getId)))

/-- Along the path `W` of the bundle, if the reader is in `Hs (S.a a.round)` and `lo ≤ S.a a.round`,
    a handle of `a` by it at `td` in `[S.a a.round, S.a a.round + Δ)` at the `i`-th event has an
    input store that is coherent, has its clock and stamps bounded by `td`, is in round `a.round`,
    and whose admission of `a` is carried into the reader's store in `W (i + 1)`. -/
theorem actual_call_inputOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {i : Nat} {reader : V}
    {a : NamedAttestation V} {td : Time}
    (hcall : Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W i reader (.attest a) td)
    (hlo : (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ td) (hhi : td < (Restated.Vocabulary.Execution.Setup.a M S a.round) + S.E.Δ)
    (hr : reader ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S a.round))) (hgat : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S a.round)) :
    ∃ input : M.NS, Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg input ∧
      Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M td input ∧
      (M.round_of S.hc input.core.s) = a.round ∧
      ∀ b : NamedAttestation V,
        b ∈ (M.admit_row S.hc input a).sg_rows b.round →
        b ∈ (W (i + 1) reader).st.sg_rows b.round := by
  have _hr_0 : M.reachedNode (W i reader) := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 reader
  have _hv_0 : M.runs_as (W i reader) reader := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 reader
  have hW := hf.onePath
  obtain ⟨hWi, -⟩ := hW i
  have hWi1 := (hW (i + 1)).1
  have htime_of : ∀ {e : Record.Event V}, rho.events[i]? = some e → e.time = td := by
    intro e he
    obtain ⟨f, hf', _, ht⟩ := hcall.2
    have hef : e = f := Option.some.inj (he.symm.trans hf')
    rw [hef]
    exact ht
  have hdeliv : ∀ {o : NamedObject V}, rho.events[i]? = some (.deliver reader o td) →
      Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (W i reader).st ∧
      Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M td (W i reader).st ∧
      M.round_of S.hc (W i reader).st.core.s = a.round := by
    intro o he
    exact ⟨(Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i reader
        (W i) hWi).1.1.1,
      (Restated.data_at_eventOn_SGArrival facts S rho Hs Xb hf he reader (W i) hWi (W (i + 1)) hWi1).1,
      Restated.delivery_roundOn facts S rho Hs Xb hf a.round he hlo hhi hr hgat⟩
  rcases hcall.1 with hdirect | ⟨B, k, before, hF1⟩
  · rcases hdirect with ⟨t, he, out, hout, hw, hem⟩ | ⟨t, he⟩
    · have ht : t = td := htime_of he
      subst ht
      have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W reader (.attest a) t :=
        ⟨i, he, out, hout, hw, hem⟩
      obtain ⟨j, hj, out', hout', hw', hmem', hstages, hval, htime, hawake⟩ :=
        Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_stages facts S rho W hW hemit
      have hij : j = i := Restated.tick_index_eq_of_unique
        hf.tickIndexUnique hj he
      subst hij
      subst htime
      obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W j reader).st.core.toHealing
        (Restated.Vocabulary.Execution.Setup.a M S a.round) (W j reader).cache
      obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c)
        S.E S.hc (M.ns_setClock S.E (W j reader).st (Restated.Vocabulary.Execution.Setup.a M S a.round))
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S a.round) - 1)
      have hn : M.mkNode st (W j reader).record c ∈
          Restated.Vocabulary.Internal.NamedOutageEntry.actionReadFrom M S (W j reader) a.round :=
        ⟨c, hc, st, hst, rfl⟩
      obtain ⟨hrowall, hround⟩ := hstages _ hn
      rewrite [facts.nd.mkNode_st] at hround; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hround
      obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract c) S.E S.hc (S.node reader)
        st (W j reader).record
      have hrow : D.2.2 = a := hrowall D (by
        rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.nd.mkNode_record,
          facts.dt.duties_attest_with_store_with_cache]
        exact hD)
      have hpre := (Restated.data_at_eventOn_SGArrival facts S rho Hs Xb hf he reader (W j) hWi
        (W (j + 1)) hWi1).1
      have hd : Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M
          (Restated.Vocabulary.Execution.Setup.a M S a.round) st :=
        data_fields₄₈ (clock_data₄₈ facts S _ _ _ le_rfl hpre)
          (facts.dt.confirmation_metadata _ _ _ _ _ st hst).2
          (confirmation_timestamp_sg_vote₄₈ facts _ _ _ _ _ st hst
            (facts.nd.reachedCore_of_store _ (facts.sto.reachedStore_setClock S.E _ _
              (facts.nd.reachedStore_of_node _ _hr_0))))
          (facts.dt.named_confirmation_clock _ _ _ _ _ st hst).1
      have hinv := Restated.Vocabulary.Proofs.NamedOutageInputs.action_read_invariant facts S rho j
        reader a.round (W j) hWi _ hn
      rewrite [facts.nd.mkNode_st] at hinv
      have _hrs : M.reachedStore (M.store_with_cache st c) := by
        have h := facts.nd.reachedStore_of_node _ (facts.nd.reachedNode_confirmationDuty S.E S.hc
          (W j reader) _ c st hc hst _hr_0)
        rwa [facts.nd.mkNode_st] at h
      have hD' : M.duties_attest_with (M.gradeContract c) S.E S.hc (S.node reader)
          (M.store_with_cache st c) (W j reader).record ⇢ D := by
        rw [facts.dt.duties_attest_with_store_with_cache]; exact hD
      refine ⟨M.store_with_cache st c, hinv.1.1,
        data_fields₄₈ hd (funext (facts.nd.store_with_cache_sg_rows st c))
          (facts.nd.store_with_cache_core_timestamp_sg_vote st c)
          (facts.nd.store_with_cache_core_t st c),
        by rw [facts.nd.store_with_cache_core_s]; exact hround.symm, ?_⟩
      intro b hb
      rw [hw, facts.nd.action_tick_store_of_outcomes S reader (W j reader) a.round hawake out hout
          c hc st hst D hD,
        facts.dt.namedDuties_attest_with_fst _ _ _ _ _ _ D hD' _hrs, hrow,
        facts.nd.store_with_cache_sg_rows]
      exact hb
    · have ht : t = td := htime_of he
      subst ht
      obtain ⟨hcoh, hd, hround⟩ := hdeliv he
      refine ⟨(W i reader).st, hcoh, hd, hround, ?_⟩
      intro b hb
      rw [deliver_post₄₈ facts S rho W hW he (hf.receipt_outcome _ _ _ _ he),
        facts.nd.make_grades_compatible_with_finalized_sg_rows, facts.nd.process_attest]
      exact hb
  · have hbefore : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg before ∧
        Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M td before ∧
        M.round_of S.hc before.core.s = a.round := by
      rcases hF1.1 with ⟨t, he, hbef⟩ | ⟨t, he, -, hbef⟩
      · have ht : t = td := htime_of he
        subst ht
        rw [hbef]
        exact hdeliv he
      · have ht : t = td := htime_of he
        subst ht
        rw [hbef]
        refine ⟨(facts.hd.invariant_clock S.E S.cfg _ t
            (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i reader
              (W i) hWi).1).1.1,
          clock_data₄₈ facts S t _ t le_rfl
            (Restated.data_at_eventOn_SGArrival facts S rho Hs Xb hf he reader (W i) hWi
              (W (i + 1)) hWi1).1, ?_⟩
        rw [facts.hd.ModelProperties_setClock_core_s,
          Restated.Vocabulary.Proofs.HealingLemmas.slotOf_of_between_a facts S a.round hlo hhi,
          facts.gr.HealingLemmas_round_of_opening_succ]
    let input := Restated.Vocabulary.Execution.NamedReceiptCalls.f1Input M S before B k
    have hcore := facts.nd.coherent_postCore S before B hbefore.1
    have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg input :=
      facts.hd.NamedAdmission_coherent_admit_rows S.E S.hc S.cfg _ (B.attestations.take k) hcore
    have hd : Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M td input :=
      rows_data₄₈ facts S td _ (B.attestations.take k) hcore
        (data_fields₄₈ hbefore.2.1 (facts.nd.postCore_sg_rows S before B)
          (facts.nd.postCore_timestamp_sg_vote S before B) (facts.nd.postCore_clock S before B).1)
    have hround : (M.round_of S.hc input.core.s) = a.round := by
      rw [(Restated.Vocabulary.Proofs.NamedReceiptCallsF1.actual_f1_clock facts S rho i reader B k a
        before W hW hF1).2]
      exact hbefore.2.2
    refine ⟨input, hcoh, hd, hround, ?_⟩
    intro b hb
    apply block_call_rows_after_event₄₈ facts S rho W hW hf.receipt_outcome hF1.1 b
    rw [(Restated.Vocabulary.Proofs.NamedReceiptCallsF1.actual_carried_call facts S rho i reader B k a
      before W hW hF1).2.2.2.2]
    exact facts.hd.admit_rows_mem_mono S.hc _ (B.attestations.drop (k + 1)) b hb

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Proofs.NamedSGArrival
local macro "sga% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.SGArrival)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedSGArrival ++ n.getId)))

/-- Along the path `W` of the bundle, if every event before index `i + 1` is at an instant at most
    `T`, `a`'s author is in `Hs T` and emitted `a` at its action instant, and the admission of `a`
    into `input` is carried into `reader`'s store in `W (i + 1)`, then any pool entry of `a`'s
    author in round `a.round` of `input` is `a` itself, held as a row. -/
theorem honest_input_pool_rowOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {a : NamedAttestation V}
    (hem : Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (.attest a) ((Restated.Vocabulary.Execution.Setup.a M S a.round)))
    (i : Nat) (reader : V) (input : M.NS) (bound : Time)
    (hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg input)
    (hd : Restated.Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data M bound input)
    (hpost : ∀ b : NamedAttestation V,
      b ∈ (M.admit_row S.hc input a).sg_rows b.round →
      b ∈ (W (i + 1) reader).st.sg_rows b.round)
    {T : Time}
    (hT : ∀ (j : Nat) (e : Record.Event V), j < i + 1 → rho.events[j]? = some e → e.time ≤ T)
    (ha : a.val_index ∈ Hs T)
    (b : CombinedAttestation V) (hb : b ∈ (M.store_sg_pool input.core a.round))
    (hv : b.val_index = a.val_index) : b = a.erase ∧ a ∈ input.sg_rows a.round := by
  obtain ⟨named, hn, he⟩ := pool_full_witness₄₈ facts S input hcoh a.round b hb
  have hr : named.round = a.round := (hd.2 a.round named hn).1
  have hown : named ∈ input.sg_rows named.round := by simpa only [hr] using hn
  have hheld := hpost named (facts.hd.admit_row_mem_mono S.hc input a named hown)
  have hval : named.val_index = a.val_index :=
    (namedAttestation_erase_val_index named).symm.trans
      ((congrArg CombinedAttestation.val_index he).trans hv)
  have hhon : named.val_index ∈ Hs T := by simpa only [hval] using ha
  obtain ⟨_, _, _, _, _, hnEmit⟩ :=
    Restated.honest_held_row_emissionOn facts S rho Hs Xb hf hHs (i + 1) reader hT hheld hhon
  have hnEmit' : Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (.attest named) ((Restated.Vocabulary.Execution.Setup.a M S named.round)) := by
    simpa only [hval] using hnEmit
  have hna : named = a := Restated.emitted_same_round_uniqueOn facts S rho Hs Xb hf hnEmit' hem hr
  exact ⟨he.symm.trans (congrArg NamedAttestation.erase hna), by simpa only [hna] using hn⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Proofs.NamedSGArrival
local macro "sga% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.SGArrival)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedSGArrival ++ n.getId)))

/-- Along the path `W` of the bundle, if `a`'s author is in `Hs td` and emitted `a` at its action
    instant, the reader is in `Hs (S.a a.round)`, `lo ≤ S.a a.round`, and the reader handles `a` at
    `td` in `[S.a a.round, S.a a.round + Δ)` at the `i`-th event, then the reader holds `a` as a row
    of round `a.round` in `W (i + 1)`. -/
theorem honest_row_after_callOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {i : Nat} {reader : V} {a : NamedAttestation V} {td : Time}
    (ha : a.val_index ∈ Hs td)
    (hem : Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (.attest a) ((Restated.Vocabulary.Execution.Setup.a M S a.round)))
    (hcall : Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W i reader (.attest a) td)
    (hlo : (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ td) (hhi : td < (Restated.Vocabulary.Execution.Setup.a M S a.round) + S.E.Δ)
    (hr : reader ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S a.round))) (hgat : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S a.round)) :
    a ∈ (W (i + 1) reader).st.sg_rows a.round := by
  obtain ⟨input, hcoh, hd, hround, hpost⟩ :=
    Restated.actual_call_inputOn facts S rho Hs Xb hf hcall hlo hhi hr hgat
  obtain ⟨ev, hev, -, hevt⟩ := hcall.2
  have hT : ∀ (j : Nat) (e : Record.Event V), j < i + 1 → rho.events[j]? = some e → e.time ≤ td := by
    intro j e hj he
    rw [← hevt]
    exact Restated.event_time_le rho hf.sorted he hev (Nat.le_of_lt_succ hj)
  have hpool := Restated.honest_input_pool_rowOn facts S rho Hs Xb hf hHs hem i reader input td
    hcoh hd hpost hT ha
  have hsub : M.round_votes input.core a.erase ⊆ {a.confirmed} := by
    intro key hk
    obtain ⟨b, hb, hv, hkey⟩ := (Restated.Vocabulary.Proofs.Optimistic.mem_round_votes facts).mp hk
    rw [namedAttestation_erase_round] at hb
    rw [namedAttestation_erase_val_index] at hv
    have he := (hpool b hb hv).1
    subst b
    rw [namedAttestation_erase_confirmed] at hkey
    exact Finset.mem_singleton.mpr hkey.symm
  by_cases hduplicate : a.confirmed ∈ M.round_votes input.core a.erase
  · obtain ⟨b, hb, hv, _⟩ := (Restated.Vocabulary.Proofs.Optimistic.mem_round_votes facts).mp hduplicate
    rw [namedAttestation_erase_round] at hb
    rw [namedAttestation_erase_val_index] at hv
    have hheld := (hpool b hb hv).2
    exact hpost a (facts.hd.admit_row_mem_mono S.hc input a a hheld)
  · have hcard : (M.round_votes input.core a.erase).card ≤ 1 := by
      simpa only [Finset.card_singleton] using Finset.card_le_card hsub
    have hguard : ¬ (a.round < (M.round_of S.hc input.core.s) - S.hc.η_SG ∨
        (M.round_of S.hc input.core.s) < a.round ∨
        a.confirmed ∈ M.round_votes input.core a.erase ∨
        (M.round_votes input.core a.erase).card = 2) := by
      rw [hround]
      simp only [not_or]
      exact ⟨Nat.not_lt.mpr (Nat.sub_le _ _), Nat.lt_irrefl _, hduplicate, by omega⟩
    have hpre : a.erase ∉ (M.store_sg_pool input.core a.round) := by
      intro hmem
      exact hduplicate ((Restated.Vocabulary.Proofs.Optimistic.mem_round_votes facts).mpr
        ⟨a.erase, by rw [namedAttestation_erase_round]; exact hmem, rfl,
          namedAttestation_erase_confirmed a⟩)
    have hnew : a.erase ∈ (M.store_sg_pool (M.on_sg_vote S.hc input.core a.erase) a.round) := by
      have h := facts.hd.mem_on_sg_vote_sg_pool_of_not S.hc input.core a.erase (by
        rw [namedAttestation_erase_round, namedAttestation_erase_confirmed]
        exact hguard)
      rw [namedAttestation_erase_round] at h
      exact h
    exact hpost a (Restated.Vocabulary.Proofs.NamedAdmission.admitted_original_row facts S.hc input a hpre hnew)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- If `v` is in `Hs t`, two SG votes of `v` in bucket `k` of `w`'s grade store in
    `W (strictEventIndex ρ t)` are equal. -/
theorem honest_sgVote_unique_stateBeforeTimeOn (facts : Record.Facts M)
    (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo) (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {t : Time} {w : V} {k : Round} {v : V} (hv : v ∈ Hs t)
    {u z : Protocol.SGVote V}
    (hu : u ∈ (M.toHealing (W (strictEventIndex ρ t) w).st.core).toFG.toSG.sg_votes k)
    (hz : z ∈ (M.toHealing (W (strictEventIndex ρ t) w).st.core).toFG.toSG.sg_votes k)
    (huv : u.val_index = v) (hzv : z.val_index = v) : u = z := by
  have hW := hf.onePath
  rw [facts.sto.Sts_toHealing_sg_votes] at hu hz
  obtain ⟨a, ha, hau⟩ := Finset.mem_image.mp hu
  obtain ⟨b, hb, hbz⟩ := Finset.mem_image.mp hz
  have hav : a.val_index = v := by
    have h := congrArg Protocol.SGVote.val_index hau
    have hauv : a.val_index = u.val_index := by
      rw [facts.sto.sgVote_val_index_eq_val_index] at h
      exact h
    exact hauv.trans huv
  have hbv : b.val_index = v := by
    have h := congrArg Protocol.SGVote.val_index hbz
    have hbzv : b.val_index = z.val_index := by
      rw [facts.sto.sgVote_val_index_eq_val_index] at h
      exact h
    exact hbzv.trans hzv
  set n := strictEventIndex ρ t with hn
  have hbefore : ∀ (j : Nat) (e : Record.Event V), j < n → ρ.events[j]? = some e → e.time < t :=
    fun j e hj hje => time_lt_of_lt_strict₄₈ hf.sorted hje hj
  have ha' : a ∈ M.store_sg_pool (W n w).st.core k := ha
  have hb' : b ∈ M.store_sg_pool (W n w).st.core k := hb
  have hsource : ∀ {x : CombinedAttestation V},
      x ∈ M.store_sg_pool (W n w).st.core k → x.val_index = v →
        ∃ row : NamedAttestation V, x = row.erase ∧
          ∃ tx : Time,
            Restated.Vocabulary.Execution.NamedRun.emits M S ρ W row.val_index (Object.attest row) tx := by
    intro x hx hxval
    obtain ⟨j, e, o, hj, hje, hproc, hcarry⟩ :=
      Restated.Vocabulary.Proofs.Optimistic.processes_attest_of_mem_sg_pool facts S ρ w W hW n k x hx
    have hvE : v ∈ Hs e.time := hHs _ _ (hbefore j e hj hje).le hv
    obtain ⟨row, hrowEq, tx, hem⟩ :
        ∃ row : NamedAttestation V, x = row.erase ∧
          ∃ tx : Time, (Restated.Vocabulary.Execution.NamedRun.emits M S ρ W row.val_index (Object.attest row) tx) := by
      cases o with
      | block Bl =>
          obtain ⟨row, hrowMem, hrowEq⟩ := hcarry
          have hrowVal : row.val_index = v := by
            rw [hrowEq, namedAttestation_erase_val_index] at hxval
            exact hxval
          have hrowHon : row.val_index ∈ Hs e.time := by
            rw [hrowVal]
            exact hvE
          obtain ⟨tx, -, hem⟩ :=
            hf.carried_attest w Bl e.time hproc row hrowMem hrowHon
          exact ⟨row, hrowEq, tx, hem⟩
      | gfVote voteObj => simp only [Proofs.Optimistic.CarriesRow] at hcarry
      | attest row =>
          have hrowEq : x = row.erase := hcarry
          have hrowVal : row.val_index = v := by
            rw [hrowEq, namedAttestation_erase_val_index] at hxval
            exact hxval
          have hrowHon : row.val_index ∈ Hs e.time := by
            rw [hrowVal]
            exact hvE
          obtain ⟨tx, -, hem⟩ :=
            hf.unforgeable w (Object.attest row) e.time hproc
              row.val_index hrowHon (author_attest row)
          exact ⟨row, hrowEq, tx, hem⟩
    exact ⟨row, hrowEq, tx, hem⟩
  obtain ⟨a', haa, hma⟩ := hsource ha' hav
  obtain ⟨b', hbb, hmb⟩ := hsource hb' hbv
  have haRound : a.round = k :=
    (Restated.Vocabulary.Proofs.NamedStoreBridge.sgRounds_stateBefore facts S ρ n w (W n) (hW n).1) k a
      ((facts.sto.Sts_mem_sg_pool_iff _ _ _).mp ha')
  have hbRound : b.round = k :=
    (Restated.Vocabulary.Proofs.NamedStoreBridge.sgRounds_stateBefore facts S ρ n w (W n) (hW n).1) k b
      ((facts.sto.Sts_mem_sg_pool_iff _ _ _).mp hb')
  have ha'Round : a'.round = k := by
    have h : a'.erase.round = k := by
      rw [← haa]
      exact haRound
    rw [namedAttestation_erase_round] at h
    exact h
  have hb'Round : b'.round = k := by
    have h : b'.erase.round = k := by
      rw [← hbb]
      exact hbRound
    rw [namedAttestation_erase_round] at h
    exact h
  have ha'Val : a'.val_index = v := by
    have h : a'.erase.val_index = v := by
      rw [← haa]
      exact hav
    rw [namedAttestation_erase_val_index] at h
    exact h
  have hb'Val : b'.val_index = v := by
    have h : b'.erase.val_index = v := by
      rw [← hbb]
      exact hbv
    rw [namedAttestation_erase_val_index] at h
    exact h
  rw [ha'Val] at hma
  rw [hb'Val] at hmb
  obtain ⟨ta, hma⟩ := hma
  obtain ⟨tb, hmb⟩ := hmb
  have hab' : a' = b' :=
    Restated.emits_attest_uniqueOn facts S Hs Xb hf hma hmb (by rw [ha'Round, hb'Round])
  have hErase : a'.erase = b'.erase :=
    congrArg (fun row : NamedAttestation V => row.erase) hab'
  have hab : a = b :=
    haa.trans (hErase.trans hbb.symm)
  exact hau.symm.trans ((congrArg M.sgVote hab).trans hbz)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- If `v` is in `Hs t`, the round-`r` batch of the grade view of `w`'s store in
    `W (strictEventIndex ρ t)` holds at most one vote by `v`. -/
theorem roundBatch_card_le_one_stateBeforeTimeOn (facts : Record.Facts M)
    (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo) (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {t : Time} {w : V} {r : Round} {v : V} (hv : v ∈ Hs t) :
    (Protocol.sg_votes_by
      (Restated.Vocabulary.Protocol.round_batch M
        (M.gradeView (M.toHealing (W (strictEventIndex ρ t) w).st.core)) r)
      v).card ≤ 1 := by
  by_cases hr : r = 0
  · subst r
    simp [Restated.Vocabulary.Protocol.round_batch, Protocol.sg_votes_by]
  · rw [Finset.card_le_one]
    intro u hu z hz
    obtain ⟨huBatch, huv⟩ := Finset.mem_filter.mp hu
    obtain ⟨hzBatch, hzv⟩ := Finset.mem_filter.mp hz
    apply Restated.honest_sgVote_unique_stateBeforeTimeOn facts S Hs Xb hf hHs hv
    · simp only [Restated.Vocabulary.Protocol.round_batch, hr, ↓reduceIte] at huBatch
      rw [facts.gr.gradeView_sg_votes, ← facts.sto.Sts_toHealing_sg_votes] at huBatch
      exact huBatch
    · simp only [Restated.Vocabulary.Protocol.round_batch, hr, ↓reduceIte] at hzBatch
      rw [facts.gr.gradeView_sg_votes, ← facts.sto.Sts_toHealing_sg_votes] at hzBatch
      exact hzBatch
    · exact huv
    · exact hzv

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.NamedOutageClosure

/-- In every world strictly before `read`, a row held in bucket `k` of the reader's store is a row
    of round `k`. -/
theorem own_strict_readOn_RowTrace (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (read : Time) (reader : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho read,
    ∀ k (a : NamedAttestation V),
      a ∈ (w₁ reader).st.sg_rows k → a.round = k := by
  intro w₁ hw₁ k a ha
  obtain ⟨n, hn, hbefore⟩ := Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_eq_prefix facts S rho hf.sorted read
  rw [hn] at hw₁
  exact ((facts.hdRun.sgArrival_prefix_data S rho (max read 0) (le_max_right _ _) n
    (fun j e hj he => ((hbefore j e hj he).le).trans (le_max_left _ _)) reader w₁ hw₁).2 k a ha).1

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.NamedOutageClosure

/-- For `c ≤ d`, a row the reader holds in `W (strictEventIndex rho c)` is held in
    `W (strictEventIndex rho d)`, with the same projection stamp. -/
theorem strict_sg_row_carryOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (reader : V) {c d : Time} (hcd : c ≤ d)
    {a : NamedAttestation V}
    (ha : a ∈ (W (strictEventIndex rho c) reader).st.sg_rows a.round) :
    a ∈ (W (strictEventIndex rho d) reader).st.sg_rows a.round ∧
      (W (strictEventIndex rho d) reader).st.core.timestamp_sg_vote (M.sgVote a.erase) =
        (W (strictEventIndex rho c) reader).st.core.timestamp_sg_vote (M.sgVote a.erase) := by
  have hcdi : strictEventIndex rho c ≤ strictEventIndex rho d := strict_lengths_mono rho hcd
  exact Restated.Vocabulary.Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono facts S rho reader hcdi
    _ (hf.onePath _).1 ha _ (onePath_slice₄₈ W hf.onePath hcdi)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.NamedOutageClosure

/-- If `reader` is in `Xb` and holds the body `H` in `W (strictEventIndex rho t)`, its tree there
    resolves `H`'s root to `H`. -/
theorem held_find_at_strictOn_RowTrace (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (reader : V) (hreader : reader ∈ Xb) (t : Time) (H : NamedBlock V)
    (hH : H ∈ (W (strictEventIndex rho t) reader).st.bodies) :
    Block.find? (W (strictEventIndex rho t) reader).st.core.T H.erase.root = some H.erase :=
  Restated.held_find_at_strictOn_HealthyHeadReady facts S rho Hs Xb hf reader hreader t H hH

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.NamedOutageClosure

/-- In every world `w₁` strictly before `cut`, an SG vote in bucket `k` of the grade view of the
    reader's store is the projection of a row of round `k` the reader holds there. -/
theorem pool_token_rowOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (cut : Time) (reader : V)
    {k : Round} {x : Protocol.SGVote V} :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho cut,
    x ∈ (M.gradeView (M.toHealing (w₁ reader).st.core)).sg_votes k →
    ∃ a : NamedAttestation V, a.round = k ∧ M.sgVote a.erase = x ∧
      a ∈ (w₁ reader).st.sg_rows a.round := by
  intro w₁ hw₁ hx
  rw [facts.gr.gradeView_sg_votes] at hx
  obtain ⟨erased, herased, hproj⟩ := Finset.mem_image.mp hx
  have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (w₁ reader).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho cut reader w₁ hw₁).1.1.1
  have herased' := (facts.sto.Sts_mem_sg_pool_iff _ _ _).mp herased
  rw [hcoh.2.2.2.1 k] at herased'
  obtain ⟨a, ha, herase⟩ := List.mem_map.mp herased'
  have hround : a.round = k :=
    Restated.own_strict_readOn_RowTrace facts S rho Hs Xb hf cut reader w₁ hw₁ k a ha
  exact ⟨a, hround, (congrArg M.sgVote herase).trans hproj,
    by simpa only [hround] using ha⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.NamedOutageClosure

/-- If `a` is held in its round's bucket of the reader's store in `W (strictEventIndex rho cut)` and
    `a`'s author is in `Hs cut`, then `S.a a.round < cut` and the author emitted `a` at
    `S.a a.round` along `W`. -/
theorem honest_held_row_before_cutOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (cut : Time) (reader : V) {a : NamedAttestation V}
    (ha : a ∈ (W (strictEventIndex rho cut) reader).st.sg_rows a.round)
    (hHon : a.val_index ∈ Hs cut) :
    (Restated.Vocabulary.Execution.Setup.a M S a.round) < cut ∧ Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (.attest a) ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
  have hbefore : ∀ (j : Nat) (e : Record.Event V), j < strictEventIndex rho cut → rho.events[j]? = some e →
      e.time < cut := fun j e hj he => time_lt_of_lt_strict₄₈ hf.sorted he hj
  obtain ⟨j, hj, t, hacc, hsend, hem⟩ :=
    Restated.honest_held_row_emissionOn facts S rho Hs Xb hf hHs (strictEventIndex rho cut) reader
      (fun j e hj he => (hbefore j e hj he).le) ha hHon
  obtain ⟨e, he, _, het⟩ := hacc.1.2
  have ht : t < cut := by simpa only [het] using hbefore j e hj he
  exact ⟨lt_of_le_of_lt hsend ht, hem⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The index of `reader`'s tick at `cut` is at most the index of any event of `reader`, other than
    a wake, at an instant `≥ cut`. -/
theorem tick_index_le_target_eventOn_PublicCutSG (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {k j : Nat} {reader : V}
    {cut : Time} {e : Record.Event V}
    (htick : rho.events[k]? = some (.tick reader cut))
    (he : rho.events[j]? = some e) (hnode : e.node = reader)
    (hnwake : ∀ u t, e ≠ Record.Event.wake u t)
    (hcut : cut ≤ e.time) : k ≤ j :=
  Restated.tick_index_le_target_eventOn_PublicCutBody facts S rho Hs Xb hf htick he hnode hnwake
    hcut

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- If the reader is in `Hs cut` for a public `cut ≥ lo`, a full row it holds in
    `W (strictEventIndex rho read)` whose SG stamp is before `cut` was accepted by it along `W` at
    an instant before `cut`. -/
theorem sg_row_accepted_before_public_cutOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {reader : V} {cut read : Time} (hreader : reader ∈ Hs cut) (hpublic : PublicTime S cut)
    (hcutlo : lo ≤ cut) {a : NamedAttestation V}
    (hheld : a ∈ (W (strictEventIndex rho read) reader).st.sg_rows a.round)
    (hstamp : occurrenceBefore
      ((W (strictEventIndex rho read) reader).st.core.timestamp_sg_vote (M.sgVote a.erase))
      cut = true) :
    ∃ (j : Nat) (accepted : Time), accepted < cut ∧
      Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W j reader (.attest a) accepted := by
  have hW := hf.onePath
  obtain ⟨j, hj, accepted, hacc⟩ :=
    Restated.Vocabulary.Proofs.NamedOutageProvenance.held_row_origin facts S rho
      (strictEventIndex rho read) reader W hW hheld
  by_cases hearly : accepted < cut
  · exact ⟨j, accepted, hearly, hacc⟩
  · have hcutAccepted : cut ≤ accepted := le_of_not_gt hearly
    have hpost : a ∈ (W (j + 1) reader).st.sg_rows a.round := by
      simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hacc.2.2
    have hj1 : j + 1 ≤ strictEventIndex rho read := Nat.succ_le_of_lt hj
    have htransport := Restated.Vocabulary.Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono facts
      S rho reader hj1 (W (j + 1)) (hW _).1 hpost _ (onePath_slice₄₈ W hW hj1)
    have hstampPost : occurrenceBefore
        ((W (j + 1) reader).st.core.timestamp_sg_vote (M.sgVote a.erase)) cut = true := by
      rw [← htransport.2]
      exact hstamp
    obtain ⟨e, he, hnode, het⟩ := hacc.1.2
    have hacceptedHorizon : accepted ≤ rho.horizon := by
      simpa only [het] using (hf.in_horizon e (List.mem_of_getElem? he)).2
    have htickMem := hf.tick_total cut hcutlo reader hreader hpublic
      (hcutAccepted.trans hacceptedHorizon)
    obtain ⟨k, htk⟩ := List.mem_iff_getElem?.mp htickMem
    have hnwake : ∀ u t, e ≠ Record.Event.wake u t := by
      intro u t hwk
      subst hwk
      rcases accepted_row_stamp_cases₄₈ facts S rho W hW hacc with ⟨hj', -⟩ | ⟨o, hj', -⟩
      · rw [he] at hj'
        cases hj'
      · rw [he] at hj'
        cases hj'
    have hkj := Restated.tick_index_le_target_eventOn_PublicCutSG facts S rho Hs Xb hf htk he hnode
      hnwake (by simpa only [het] using hcutAccepted)
    rcases accepted_row_stamp_cases₄₈ facts S rho W hW hacc with
      ⟨_, hpostStamp⟩ | ⟨o, hdeliver, hpostStamp⟩
    · rw [hpostStamp] at hstampPost
      rw [occurrenceBefore_some_iff] at hstampPost
      exact False.elim ((not_lt_of_ge (by exact_mod_cast hcutAccepted)) hstampPost)
    · have hkne : k ≠ j := by
        intro hEq
        subst k
        rw [htk] at hdeliver
        cases hdeliver
      have hclock := Restated.tick_le_clock_before_deliveryOn_RawRelay facts S rho Hs Xb hf
        hdeliver htickMem hcutAccepted
      rw [hpostStamp] at hstampPost
      rw [occurrenceBefore_some_iff] at hstampPost
      have hclockStamp : (cut : Stamp) ≤ ((W j reader).st.core.t : Stamp) := by
        exact_mod_cast hclock
      exact False.elim ((not_lt_of_ge hclockStamp) hstampPost)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.NamedRawSource
local macro "rs% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Store.RawSource)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedRawSource ++ n.getId)))

/-- In every world strictly before `read`, every row held in bucket `k` of the reader's store is a
    row of round `k`. -/
theorem own_strict_readOn_RawSource (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (read : Time) (reader : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho read,
    ∀ k (a : NamedAttestation V), a ∈ (w₁ reader).st.sg_rows k → a.round = k :=
  Restated.own_strict_readOn_RowTrace facts S rho Hs Xb hf read reader

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.NamedRawSource
local macro "rs% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Store.RawSource)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedRawSource ++ n.getId)))

/-- If `source` is in `Hs (early s .g2)` and `lo ≤ early s .g2`, a raw G2 input `u` of `source`'s
    store in `W (strictEventIndex rho (domain s .g2))` is the projection of a full row `a` of a
    round in `s`'s window that `source` accepted along `W` before `early s .g2`. -/
theorem g2_raw_input_source_acceptanceOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (source : V) (s : Round) (sender : V) (u : Protocol.SGVote V)
    (X : Finset (Protocol.SGVote V))
    (hX : M.rawInputs
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc s .g2)) source).st.core))
      S.hc.η_SG s (M.early S.E S.hc s .g2) sender ⇢ X)
    (hraw : u ∈ X)
    (hsource : source ∈ Hs (M.early S.E S.hc s .g2)) (hgat : lo ≤ M.early S.E S.hc s .g2) :
    ∃ (a : NamedAttestation V) (i : Nat) (accepted : Time),
      M.sgVote a.erase = u ∧ a.round ∈ M.latest_window S.hc.η_SG s ∧
      accepted < M.early S.E S.hc s .g2 ∧
      Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i source (.attest a) accepted := by
  have hn := mem_stateBeforeTime_path₄₈ S rho hf.sorted W hf.onePath (M.domain S.E S.hc s .g2)
  let n := W (strictEventIndex rho (M.domain S.E S.hc s .g2)) source
  obtain ⟨⟨k, hwindow, hu⟩, _, hstamp⟩ := facts.gr.rawInputs_mem_window _ _ _ _ _ X hX hraw
  have hs : 0 < s := (Nat.zero_le k).trans_lt (facts.fc.window_bounds hwindow).2
  rw [facts.gr.gradeView_sg_votes] at hu
  obtain ⟨erased, herased, hproj⟩ := Finset.mem_image.mp hu
  have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg n.st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
      (M.domain S.E S.hc s .g2) source _ hn).1.1.1
  rw [facts.sto.Sts_mem_sg_pool_iff, hcoh.2.2.2.1 k] at herased
  obtain ⟨a, ha, herase⟩ := List.mem_map.mp herased
  have hround : a.round = k :=
    Restated.own_strict_readOn_RawSource facts S rho Hs Xb hf (M.domain S.E S.hc s .g2) source
      _ hn k a ha
  have hown : a ∈ n.st.sg_rows a.round := by simpa only [hround] using ha
  have hprojection : M.sgVote a.erase = u := (congrArg M.sgVote herase).trans hproj
  have hstampA : occurrenceBefore (n.st.core.timestamp_sg_vote (M.sgVote a.erase))
      (M.early S.E S.hc s .g2) = true := by
    rw [hprojection]
    rw [facts.gr.gradeView_timestamp_sg_vote] at hstamp
    exact hstamp
  obtain ⟨i, accepted, hbefore, hacc⟩ :=
    Restated.sg_row_accepted_before_public_cutOn facts S rho Hs Xb hf hsource
      (facts.gr.early_g2_public S s hs) hgat hown hstampA
  exact ⟨a, i, accepted, hprojection, by simpa only [hround] using hwindow, hbefore, hacc⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.NamedRawSource
local macro "rs% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Store.RawSource)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedRawSource ++ n.getId)))

/-- If `source` is in `Hs (early s .g1)` and `lo ≤ early s .g1`, a raw G1 input `u` of `source`'s
    store in `W (strictEventIndex rho (domain s .g1))` is the projection of a full row `a` of a
    round in `s`'s window that `source` accepted along `W` before `early s .g1`. -/
theorem g1_raw_input_source_acceptanceOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (source : V) (s : Round) (sender : V) (u : Protocol.SGVote V)
    (X : Finset (Protocol.SGVote V))
    (hX : M.rawInputs
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc s .g1)) source).st.core))
      S.hc.η_SG s (M.early S.E S.hc s .g1) sender ⇢ X)
    (hraw : u ∈ X)
    (hsource : source ∈ Hs (M.early S.E S.hc s .g1)) (hgat : lo ≤ M.early S.E S.hc s .g1) :
    ∃ (a : NamedAttestation V) (i : Nat) (accepted : Time),
      M.sgVote a.erase = u ∧ a.round ∈ M.latest_window S.hc.η_SG s ∧
      accepted < M.early S.E S.hc s .g1 ∧
      Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i source (.attest a) accepted := by
  have hn := mem_stateBeforeTime_path₄₈ S rho hf.sorted W hf.onePath (M.domain S.E S.hc s .g1)
  let n := W (strictEventIndex rho (M.domain S.E S.hc s .g1)) source
  obtain ⟨⟨k, hwindow, hu⟩, _, hstamp⟩ := facts.gr.rawInputs_mem_window _ _ _ _ _ X hX hraw
  have hs : 0 < s := (Nat.zero_le k).trans_lt (facts.fc.window_bounds hwindow).2
  rw [facts.gr.gradeView_sg_votes] at hu
  obtain ⟨erased, herased, hproj⟩ := Finset.mem_image.mp hu
  have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg n.st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
      (M.domain S.E S.hc s .g1) source _ hn).1.1.1
  rw [facts.sto.Sts_mem_sg_pool_iff, hcoh.2.2.2.1 k] at herased
  obtain ⟨a, ha, herase⟩ := List.mem_map.mp herased
  have hround : a.round = k :=
    Restated.own_strict_readOn_RawSource facts S rho Hs Xb hf (M.domain S.E S.hc s .g1) source
      _ hn k a ha
  have hown : a ∈ n.st.sg_rows a.round := by simpa only [hround] using ha
  have hprojection : M.sgVote a.erase = u := (congrArg M.sgVote herase).trans hproj
  have hstampA : occurrenceBefore (n.st.core.timestamp_sg_vote (M.sgVote a.erase))
      (M.early S.E S.hc s .g1) = true := by
    rw [hprojection]
    rw [facts.gr.gradeView_timestamp_sg_vote] at hstamp
    exact hstamp
  obtain ⟨i, accepted, hbefore, hacc⟩ :=
    Restated.sg_row_accepted_before_public_cutOn facts S rho Hs Xb hf hsource
      (facts.gr.q10_early_g1_public S s hs) hgat hown hstampA
  exact ⟨a, i, accepted, hprojection, by simpa only [hround] using hwindow, hbefore, hacc⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.NamedRawSource
local macro "rs% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Store.RawSource)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedRawSource ++ n.getId)))

/-- If `reader` is in `Hs (late s .g1)` and `lo ≤ late s .g1`, a raw G1-late input `u` of `reader`'s
    store in `W (strictEventIndex rho (domain s .g1))` is the projection of a full row `a` of a
    round in `s`'s window that `reader` accepted along `W` before `late s .g1`. -/
theorem g1_late_raw_input_acceptanceOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (reader : V) (s : Round) (sender : V) (u : Protocol.SGVote V)
    (X : Finset (Protocol.SGVote V))
    (hX : M.rawInputs
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc s .g1)) reader).st.core))
      S.hc.η_SG s (M.late S.E S.hc s .g1) sender ⇢ X)
    (hraw : u ∈ X)
    (hreader : reader ∈ Hs (M.late S.E S.hc s .g1)) (hgat : lo ≤ M.late S.E S.hc s .g1) :
    ∃ (a : NamedAttestation V) (i : Nat) (accepted : Time),
      M.sgVote a.erase = u ∧ a.round ∈ M.latest_window S.hc.η_SG s ∧
      accepted < M.late S.E S.hc s .g1 ∧
      Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i reader (.attest a) accepted := by
  have hn := mem_stateBeforeTime_path₄₈ S rho hf.sorted W hf.onePath (M.domain S.E S.hc s .g1)
  let n := W (strictEventIndex rho (M.domain S.E S.hc s .g1)) reader
  obtain ⟨⟨k, hwindow, hu⟩, _, hstamp⟩ := facts.gr.rawInputs_mem_window _ _ _ _ _ X hX hraw
  have hs : 0 < s := (Nat.zero_le k).trans_lt (facts.fc.window_bounds hwindow).2
  rw [facts.gr.gradeView_sg_votes] at hu
  obtain ⟨erased, herased, hproj⟩ := Finset.mem_image.mp hu
  have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg n.st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
      (M.domain S.E S.hc s .g1) reader _ hn).1.1.1
  rw [facts.sto.Sts_mem_sg_pool_iff, hcoh.2.2.2.1 k] at herased
  obtain ⟨a, ha, herase⟩ := List.mem_map.mp herased
  have hround : a.round = k :=
    Restated.own_strict_readOn_RawSource facts S rho Hs Xb hf (M.domain S.E S.hc s .g1) reader
      _ hn k a ha
  have hown : a ∈ n.st.sg_rows a.round := by simpa only [hround] using ha
  have hprojection : M.sgVote a.erase = u := (congrArg M.sgVote herase).trans hproj
  have hstampA : occurrenceBefore (n.st.core.timestamp_sg_vote (M.sgVote a.erase))
      (M.late S.E S.hc s .g1) = true := by
    rw [hprojection]
    rw [facts.gr.gradeView_timestamp_sg_vote] at hstamp
    exact hstamp
  obtain ⟨i, accepted, hbefore, hacc⟩ :=
    Restated.sg_row_accepted_before_public_cutOn facts S rho Hs Xb hf hreader
      (facts.gr.q10_late_g1_public S s hs) hgat hown hstampA
  exact ⟨a, i, accepted, hprojection, by simpa only [hround] using hwindow, hbefore, hacc⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.NamedRawSource
local macro "rs% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Store.RawSource)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedRawSource ++ n.getId)))

/-- If `reader` is in `Hs (late s .g0)` and `lo ≤ late s .g0`, a raw G0-late input `u` of `reader`'s
    store in `W (strictEventIndex rho (domain s .g0))` is the projection of a full row `a` of a
    round in `s`'s window that `reader` accepted along `W` before `late s .g0`. -/
theorem g0_late_raw_input_acceptanceOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (reader : V) (s : Round) (sender : V) (u : Protocol.SGVote V)
    (X : Finset (Protocol.SGVote V))
    (hX : M.rawInputs
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc s .g0)) reader).st.core))
      S.hc.η_SG s (M.late S.E S.hc s .g0) sender ⇢ X)
    (hraw : u ∈ X)
    (hreader : reader ∈ Hs (M.late S.E S.hc s .g0)) (hgat : lo ≤ M.late S.E S.hc s .g0) :
    ∃ (a : NamedAttestation V) (i : Nat) (accepted : Time),
      M.sgVote a.erase = u ∧ a.round ∈ M.latest_window S.hc.η_SG s ∧
      accepted < M.late S.E S.hc s .g0 ∧
      Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i reader (.attest a) accepted := by
  have hn := mem_stateBeforeTime_path₄₈ S rho hf.sorted W hf.onePath (M.domain S.E S.hc s .g0)
  let n := W (strictEventIndex rho (M.domain S.E S.hc s .g0)) reader
  obtain ⟨⟨k, hwindow, hu⟩, _, hstamp⟩ := facts.gr.rawInputs_mem_window _ _ _ _ _ X hX hraw
  have hs : 0 < s := (Nat.zero_le k).trans_lt (facts.fc.window_bounds hwindow).2
  rw [facts.gr.gradeView_sg_votes] at hu
  obtain ⟨erased, herased, hproj⟩ := Finset.mem_image.mp hu
  have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg n.st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
      (M.domain S.E S.hc s .g0) reader _ hn).1.1.1
  rw [facts.sto.Sts_mem_sg_pool_iff, hcoh.2.2.2.1 k] at herased
  obtain ⟨a, ha, herase⟩ := List.mem_map.mp herased
  have hround : a.round = k :=
    Restated.own_strict_readOn_RawSource facts S rho Hs Xb hf (M.domain S.E S.hc s .g0) reader
      _ hn k a ha
  have hown : a ∈ n.st.sg_rows a.round := by simpa only [hround] using ha
  have hprojection : M.sgVote a.erase = u := (congrArg M.sgVote herase).trans hproj
  have hstampA : occurrenceBefore (n.st.core.timestamp_sg_vote (M.sgVote a.erase))
      (M.late S.E S.hc s .g0) = true := by
    rw [hprojection]
    rw [facts.gr.gradeView_timestamp_sg_vote] at hstamp
    exact hstamp
  obtain ⟨i, accepted, hbefore, hacc⟩ :=
    Restated.sg_row_accepted_before_public_cutOn facts S rho Hs Xb hf hreader
      (facts.gr.late_g0_public S s hs) hgat hown hstampA
  exact ⟨a, i, accepted, hprojection, by simpa only [hround] using hwindow, hbefore, hacc⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- If `v` is in `Hs time` and `u` is an SG vote by `v` in bucket `k` of `w`'s store in
    `W (strictEventIndex rho time)`, then for every node state `n` of `v`'s round-`k` action read,
    `u` is `⟨v, k, some B.root⟩` for every block `B` the SG selector can pick on `n`, and `v` emits
    along `W`, at `S.a k`, the attestation of every outcome of its attestation duty on `n`. -/
theorem honestSGVote_actionEmission_of_mem_storeBeforeTimeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {w v : V} {time : Time} {k : Round} {u : Protocol.SGVote V}
    (hv : v ∈ Hs time)
    (hu : u ∈ (M.toHealing (W (strictEventIndex rho time) w).st.core).toFG.toSG.sg_votes k)
    (huv : u.val_index = v) :
    (∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v) k,
      let gc := M.gradeContract n.cache
      let st := M.toHealing n.st.core
      let kk := M.round_of S.hc st.s
      ∀ A2, M.grade2_block_with gc S.E S.hc st kk ⇢ A2 →
      ∀ B, M.get_sg_vote_with gc S.E S.hc st kk A2 ⇢ B →
      u = (⟨v, k, some B.root⟩ : Protocol.SGVote V)) ∧
    (∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v) k,
      ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (Object.attest D.2.2)
        (Restated.Vocabulary.Execution.Setup.a M S k)) := by
  have hW := hf.onePath
  rw [facts.sto.Sts_toHealing_sg_votes] at hu
  obtain ⟨a, ha, hau⟩ := Finset.mem_image.mp hu
  set n := strictEventIndex rho time with hn
  have hbefore : ∀ (j : Nat) (e : Record.Event V), j < n → rho.events[j]? = some e → e.time < time :=
    fun j e hj hje => time_lt_of_lt_strict₄₈ hf.sorted hje hj
  have haN : a ∈ M.store_sg_pool (W n w).st.core k := ha
  have haround : a.round = k :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.sgRounds_stateBefore facts S rho n w (W n) (hW n).1 k a
      ((facts.sto.Sts_mem_sg_pool_iff _ _ _).mp haN)
  have hav : a.val_index = v := by
    have h := congrArg Protocol.SGVote.val_index hau
    have havu : a.val_index = u.val_index := by
      rw [facts.sto.sgVote_val_index_eq_val_index] at h
      exact h
    exact havu.trans huv
  obtain ⟨j, e, o, hj, hje, hproc, hcarry⟩ :=
    Restated.Vocabulary.Proofs.Optimistic.processes_attest_of_mem_sg_pool facts S rho w W hW n k a haN
  have hvE : v ∈ Hs e.time := hHs _ _ (hbefore j e hj hje).le hv
  obtain ⟨row, hrowEq, t', hte, hemit⟩ :
      ∃ row : NamedAttestation V, a = row.erase ∧
        ∃ t' : Time, t' ≤ e.time ∧ (Restated.Vocabulary.Execution.NamedRun.emits M S rho W row.val_index (Object.attest row) t') := by
    cases o with
    | block Bl =>
        obtain ⟨row, hrowMem, hrowEq⟩ := hcarry
        have hrowV : row.val_index = v := by
          rw [hrowEq, namedAttestation_erase_val_index] at hav; exact hav
        have hrowHon : row.val_index ∈ Hs e.time := by rw [hrowV]; exact hvE
        obtain ⟨t', hte, hemit⟩ :=
          hf.carried_attest w Bl e.time hproc row hrowMem hrowHon
        exact ⟨row, hrowEq, t', hte, hemit⟩
    | gfVote voteObj => simp only [Proofs.Optimistic.CarriesRow] at hcarry
    | attest row =>
        have hrowEq : a = row.erase := hcarry
        have hrowV : row.val_index = v := by
          rw [hrowEq, namedAttestation_erase_val_index] at hav; exact hav
        have hrowHon : row.val_index ∈ Hs e.time := by rw [hrowV]; exact hvE
        obtain ⟨t', hte, hemit⟩ :=
          hf.unforgeable w (Object.attest row) e.time hproc row.val_index hrowHon (author_attest row)
        exact ⟨row, hrowEq, t', hte, hemit⟩
  have hrowV : row.val_index = v := by
    rw [hrowEq, namedAttestation_erase_val_index] at hav; exact hav
  have hrowRound : row.round = k := by
    rw [hrowEq, namedAttestation_erase_round] at haround; exact haround
  have hemitV : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (Object.attest row) t' :=
    hrowV ▸ hemit
  have hshape := Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hW hemitV
  have htime : t' = (Restated.Vocabulary.Execution.Setup.a M S k) := by rw [hshape.2, hrowRound]
  rw [htime] at hemitV
  have hrowAction : ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v) k,
      ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
      row = D.2.2 := by
    intro n hn D hD
    obtain ⟨i, hi, out, hout, -, hmem⟩ := id hemitV
    rcases Restated.action_emissionOn facts S rho Hs Xb hf i v k hi out hout n hn D hD with
      ⟨-, h⟩ | ⟨-, h⟩
    · simp only [h, List.mem_singleton, NamedObject.attest.injEq] at hmem
      exact hmem
    · simp only [h, List.not_mem_nil] at hmem
  refine ⟨?_, ?_⟩
  · intro n hn gc st kk A2 hA2 B hB
    obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract n.cache) S.E S.hc (S.node v)
      n.st n.record
    have hsg := Restated.Vocabulary.Proofs.HealingSurface.sgVote_actionAttestationAt facts S rho v k
      _ (mem_stateBeforeTime_path₄₈ S rho hf.sorted W hW (Restated.Vocabulary.Execution.Setup.a M S k))
      n hn D hD A2 hA2 B hB
    rw [← hau, hrowEq, hrowAction n hn D hD]
    exact hsg
  · intro n hn D hD
    rw [← hrowAction n hn D hD]
    exact hemitV

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- If `v` is in `Hs time` and `u` is an SG vote by `v` in bucket `k` of `w`'s store in
    `W (strictEventIndex rho time)`, then for every node state `n` of `v`'s round-`k` action read,
    `u` is `⟨v, k, some B.root⟩` for every block `B` the SG selector can pick on `n`. -/
theorem honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTimeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {w v : V} {time : Time} {k : Round} {u : Protocol.SGVote V}
    (hv : v ∈ Hs time)
    (hu : u ∈ (M.toHealing (W (strictEventIndex rho time) w).st.core).toFG.toSG.sg_votes k)
    (huv : u.val_index = v) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v) k,
      let gc := M.gradeContract n.cache
      let st := M.toHealing n.st.core
      let kk := M.round_of S.hc st.s
      ∀ A2, M.grade2_block_with gc S.E S.hc st kk ⇢ A2 →
      ∀ B, M.get_sg_vote_with gc S.E S.hc st kk A2 ⇢ B →
      u = (⟨v, k, some B.root⟩ : Protocol.SGVote V) :=
  (Restated.honestSGVote_actionEmission_of_mem_storeBeforeTimeOn facts S Hs Xb hf hHs hv hu huv).1

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- If `u` is in `Hs cut`, a raw input `y` of `u` at cutoff `cutoff` in the grade view of the
    reader's store in `W (strictEventIndex rho cut)` is the projection of an attestation `a` by `u`
    of round `y.round` in `r`'s window, with `S.a a.round < cut`, which `u` emitted along `W` at
    `S.a a.round`. -/
theorem rawInputs_traceOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (cut cutoff : Time) (reader : V) (eta r : Round) (u : V) (hu : u ∈ Hs cut)
    {y : Protocol.SGVote V} (X : Finset (Protocol.SGVote V))
    (hX : M.rawInputs
      (M.gradeView (M.toHealing (W (strictEventIndex rho cut) reader).st.core)) eta r cutoff u ⇢ X)
    (hy : y ∈ X) :
    ∃ a : NamedAttestation V, a.val_index = u ∧ a.round = y.round ∧
      M.sgVote a.erase = y ∧ y.round ∈ M.latest_window eta r ∧
      (Restated.Vocabulary.Execution.Setup.a M S a.round) < cut ∧ Restated.Vocabulary.Execution.NamedRun.emits M S rho W u (.attest a) ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
  obtain ⟨⟨k, hk, hyk⟩, hval0, _⟩ := facts.gr.rawInputs_mem_window _ _ _ _ _ X hX hy
  obtain ⟨a, hround, hproj, hmem⟩ := Restated.pool_token_rowOn facts S rho Hs Xb hf cut reader
    _ (mem_stateBeforeTime_path₄₈ S rho hf.sorted W hf.onePath cut) hyk
  have hyround : y.round = a.round := by
    rw [← hproj, facts.sto.sgVote_round_eq_round, namedAttestation_erase_round]
  have hval : a.val_index = u := by
    have hvy : y.val_index = u := hval0
    rw [← hproj, facts.sto.sgVote_val_index_eq_val_index, namedAttestation_erase_val_index] at hvy
    exact hvy
  subst hval
  obtain ⟨hlt, hem⟩ := Restated.honest_held_row_before_cutOn facts S rho Hs Xb hf hHs cut reader hmem hu
  exact ⟨a, rfl, hyround.symm, hproj,
    by rw [hyround, hround]; exact hk, hlt, hem⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Internal.NamedJointOutage
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

/-- If the reader is in `Hs cut` for a public `cut ≥ lo`, a row it holds in
    `W (strictEventIndex rho read)` whose SG stamp is before `cut` is held in
    `W (strictEventIndex rho cut)`. -/
theorem q10_row_at_public_cutOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {reader : V} {cut read : Time} (hreader : reader ∈ Hs cut)
    (hpublic : PublicTime S cut) (hcutlo : lo ≤ cut)
    {a : NamedAttestation V}
    (hheld : a ∈ (W (strictEventIndex rho read) reader).st.sg_rows a.round)
    (hstamp : occurrenceBefore
      ((W (strictEventIndex rho read) reader).st.core.timestamp_sg_vote (M.sgVote a.erase)) cut = true) :
    a ∈ (W (strictEventIndex rho cut) reader).st.sg_rows a.round := by
  have hW := hf.onePath
  obtain ⟨j, accepted, hearly, hacc⟩ :=
    Restated.sg_row_accepted_before_public_cutOn facts S rho Hs Xb hf hreader hpublic hcutlo
      hheld hstamp
  obtain ⟨e, he, hnode, het⟩ := hacc.1.2
  have hpost : a ∈ (W (j + 1) reader).st.sg_rows a.round :=
    of_decide_eq_true hacc.2.2
  have hj : j + 1 ≤ strictEventIndex rho cut :=
    Nat.succ_le_of_lt (lt_strict_of_time_lt₄₈ hf.sorted he (by rw [het]; exact hearly))
  exact (Restated.Vocabulary.Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono facts S rho reader hj
    (W (j + 1)) (hW _).1 hpost _ (onePath_slice₄₈ W hW hj)).1

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Internal.NamedJointOutage
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

/-- For `c ≤ d`, a body the reader holds in `W (strictEventIndex rho c)` is held in
    `W (strictEventIndex rho d)`, with the same stamp. -/
theorem q10_strict_body_carryOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (reader : V) {c d : Time} (hcd : c ≤ d)
    {H : NamedBlock V}
    (hH : H ∈ (W (strictEventIndex rho c) reader).st.bodies) :
    H ∈ (W (strictEventIndex rho d) reader).st.bodies ∧
      (W (strictEventIndex rho d) reader).st.core.timestamp_block H.erase =
        (W (strictEventIndex rho c) reader).st.core.timestamp_block H.erase :=
  Restated.Vocabulary.Proofs.NamedOutageClosure.q10_strict_body_carry_of_sorted facts S rho hf.sorted reader
    hcd _ (mem_stateBeforeTime_path₄₈ S rho hf.sorted W hf.onePath c) hH _
    (onePath_slice₄₈ W hf.onePath (strict_lengths_mono rho hcd))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Internal.NamedJointOutage
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

/-- If `v` is in `Hs c` for a public cutoff `c ≥ lo` at most both reads, every outcome of the raw
    inputs at `c` of the grade view of `v`'s store in `W (strictEventIndex rho T1)` is contained in
    every outcome of the raw inputs at `c` of its store in `W (strictEventIndex rho T2)`. -/
theorem q10_rawInputs_backOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) {c T2 T1 : Time}
    (hpublic : PublicTime S c) (hc2 : c ≤ T2) (hc1 : c ≤ T1) (eta r : Round) (sender : V)
    (hv : v ∈ Hs c) (hclo : lo ≤ c) :
    ∀ X, M.rawInputs
        (M.gradeView (M.toHealing (W (strictEventIndex rho T1) v).st.core)) eta r c sender ⇢ X →
      ∀ Y, M.rawInputs
        (M.gradeView (M.toHealing (W (strictEventIndex rho T2) v).st.core)) eta r c sender ⇢ Y →
      X ⊆ Y := by
  have hW := hf.onePath
  intro X hX Y hY u hu
  obtain ⟨⟨k, hk, huk⟩, hval, hstamp⟩ := facts.gr.rawInputs_mem_window _ _ _ _ _ X hX hu
  obtain ⟨a, hround, hproj, hmem⟩ := Restated.pool_token_rowOn facts S rho Hs Xb hf T1 v
    _ (mem_stateBeforeTime_path₄₈ S rho hf.sorted W hW T1) huk
  subst hproj
  have hstamp1 : occurrenceBefore
      ((W (strictEventIndex rho T1) v).st.core.timestamp_sg_vote (M.sgVote a.erase)) c = true := by
    rw [facts.gr.gradeView_timestamp_sg_vote] at hstamp
    exact hstamp
  have hatc : a ∈ (W (strictEventIndex rho c) v).st.sg_rows a.round :=
    Restated.q10_row_at_public_cutOn facts S rho Hs Xb hf hv hpublic hclo hmem hstamp1
  obtain ⟨_, hstampcut⟩ := Restated.strict_sg_row_carryOn facts S rho Hs Xb hf v hc1 hatc
  have hstampc : occurrenceBefore
      ((W (strictEventIndex rho c) v).st.core.timestamp_sg_vote (M.sgVote a.erase)) c = true := by
    rw [← hstampcut]
    exact hstamp1
  obtain ⟨hmem2, hstamp2⟩ := Restated.strict_sg_row_carryOn facts S rho Hs Xb hf v hc2 hatc
  have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (W (strictEventIndex rho T2) v).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho T2 v _
      (mem_stateBeforeTime_path₄₈ S rho hf.sorted W hW T2)).1.1.1
  have hpool2 := facts.sto.pool_view_mem
    (W (strictEventIndex rho T2) v).st hcoh.2.2.2.1 a hmem2
  refine facts.gr.mem_rawInputs_of_occurrenceBefore _ _ _ k _ _ hk ?_ hval ?_ Y hY
  · rw [facts.gr.gradeView_sg_votes, ← hround]
    exact Finset.mem_image_of_mem M.sgVote hpool2
  · rw [facts.gr.gradeView_timestamp_sg_vote, hstamp2]
    exact hstampc

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Internal.NamedJointOutage
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

/-- If `v` is in `Hs c` for a public cutoff `c ≥ lo` with `c ≤ T2 ≤ T1`, every outcome of the
    interpreted inputs of the grade view of `v`'s store in `W (strictEventIndex rho T1)` is
    contained in every outcome of the interpreted inputs of its store in
    `W (strictEventIndex rho T2)`. -/
theorem q10_interpreted_backOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (v : V) {c T2 T1 : Time} (hv : v ∈ Hs c)
    (hpublic : PublicTime S c) (hc2 : c ≤ T2) (h21 : T2 ≤ T1) (eta r : Round) (sender : V)
    (hclo : lo ≤ c) :
    ∀ X, M.interpretedInputs
        (M.gradeView (M.toHealing (W (strictEventIndex rho T1) v).st.core))
        (W (strictEventIndex rho T1) v).st.core.F eta r c sender ⇢ X →
      ∀ Y, M.interpretedInputs
        (M.gradeView (M.toHealing (W (strictEventIndex rho T2) v).st.core))
        (W (strictEventIndex rho T2) v).st.core.F eta r c sender ⇢ Y →
      X ⊆ Y := by
  have hW := hf.onePath
  have hc1 : c ≤ T1 := hc2.trans h21
  have hFmono : Block.Preceq (W (strictEventIndex rho T2) v).st.core.F
      (W (strictEventIndex rho T1) v).st.core.F :=
    Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_F_mono facts S rho v (strict_lengths_mono rho h21)
      _ (hW _).1 _ (onePath_slice₄₈ W hW (strict_lengths_mono rho h21))
  intro X hX Y hY u hu
  obtain ⟨R1, hR1⟩ := facts.gr.rawInputs_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho T1) v).st.core)) eta r c sender
  obtain ⟨b1, hb1⟩ := facts.gr.bodyReady_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho T1) v).st.core))
    (W (strictEventIndex rho T1) v).st.core.F c u
  obtain ⟨R2, hR2⟩ := facts.gr.rawInputs_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho T2) v).st.core)) eta r c sender
  obtain ⟨b2, hb2⟩ := facts.gr.bodyReady_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho T2) v).st.core))
    (W (strictEventIndex rho T2) v).st.core.F c u
  obtain ⟨hraw, hready⟩ := (facts.gr.mem_interpretedInputs_iff X hX R1 hR1 b1 hb1).mp hu
  refine (facts.gr.mem_interpretedInputs_iff Y hY R2 hR2 b2 hb2).mpr
    ⟨Restated.q10_rawInputs_backOn facts S rho Hs Xb hf v hpublic hc2 hc1 eta r sender hv hclo
      R1 hR1 R2 hR2 hraw, ?_⟩
  cases hconf : u.confirmed with
  | none => exact facts.gr.bodyReady_of_no_head _ _ _ _ hconf b2 hb2
  | some root =>
    obtain ⟨H, hfnd, hready1, hready2⟩ := facts.gr.exists_find_of_bodyReady hconf b1 hb1 hready
    rw [facts.gr.Sts_gradeView_T] at hfnd
    · have hroot : H.root = root := Proofs.HealingLemmas.find?_root hfnd
      have hcoh1 : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (W (strictEventIndex rho T1) v).st :=
        (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho T1 v _
          (mem_stateBeforeTime_path₄₈ S rho hf.sorted W hW T1)).1.1.1
      have hHmem : H ∈ (W (strictEventIndex rho T1) v).st.core.T :=
        Proofs.HealingLemmas.find?_mem hfnd
      rw [hcoh1.1] at hHmem
      obtain ⟨Hn, hHn, hHe⟩ := Finset.mem_image.mp hHmem
      have hstampN : stampedBefore
          (W (strictEventIndex rho T1) v).st.core.timestamp_block c Hn.erase = true := by
        rw [facts.gr.gradeView_timestamp_block, ← hHe] at hready1
        exact hready1
      have hcutN : Hn ∈ (W (strictEventIndex rho c) v).st.bodies :=
        Restated.body_mem_stateBeforeTime_of_public_stampedBeforeOn facts S rho Hs Xb hf hv
          hpublic hclo hHn hstampN
      obtain ⟨hHn2, hstamp2⟩ := Restated.q10_strict_body_carryOn facts S rho Hs Xb hf v hc2 hcutN
      obtain ⟨_, hstamp1⟩ := Restated.q10_strict_body_carryOn facts S rho Hs Xb hf v hc1 hcutN
      have hfind2 : Block.find?
          (M.gradeView (M.toHealing (W (strictEventIndex rho T2) v).st.core)).T root =
          some H := by
        have := Restated.held_find_at_strictOn_RowTrace facts S rho Hs Xb hf v (hHsXb c hv) T2 Hn hHn2
        rw [← hroot, ← hHe, facts.gr.Sts_gradeView_T]
        exact this
      have : stampedBefore
          (W (strictEventIndex rho T2) v).st.core.timestamp_block c Hn.erase = true := by
        rw [stampedBefore_eq_occurrenceBefore] at hstampN ⊢
        rw [hstamp2, ← hstamp1]
        exact hstampN
      refine facts.gr.bodyReady_of_find hconf hfind2 ?_ (q10_compatible_back hFmono hready2) b2 hb2
      rw [facts.gr.gradeView_timestamp_block, ← hHe]
      exact this

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Internal.NamedJointOutage
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

/-- If `v` is in `Xb` and `T2 ≤ T1`, a root that the tree of the grade view of `v`'s store in
    `W (strictEventIndex rho T2)` resolves to `H` resolves to `H` in `W (strictEventIndex rho T1)`. -/
theorem q10_find_fwdOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (hv : v ∈ Xb) {T2 T1 : Time} (h21 : T2 ≤ T1) {root : BlockId}
    {H : Block V}
    (hfnd : Block.find? (M.gradeView (M.toHealing (W (strictEventIndex rho T2) v).st.core)).T
      root = some H) :
    Block.find? (M.gradeView (M.toHealing (W (strictEventIndex rho T1) v).st.core)).T
      root = some H := by
  rw [facts.gr.Sts_gradeView_T] at hfnd ⊢
  have hroot : H.root = root := Proofs.HealingLemmas.find?_root hfnd
  have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (W (strictEventIndex rho T2) v).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho T2 v _
      (mem_stateBeforeTime_path₄₈ S rho hf.sorted W hf.onePath T2)).1.1.1
  have hHmem : H ∈ (W (strictEventIndex rho T2) v).st.core.T :=
    Proofs.HealingLemmas.find?_mem hfnd
  rw [hcoh.1] at hHmem
  obtain ⟨Hn, hHn, hHe⟩ := Finset.mem_image.mp hHmem
  have hHn1 : Hn ∈ (W (strictEventIndex rho T1) v).st.bodies :=
    (Restated.q10_strict_body_carryOn facts S rho Hs Xb hf v h21 hHn).1
  have hfind := Restated.held_find_at_strictOn_RowTrace facts S rho Hs Xb hf v hv T1 Hn hHn1
  rw [← hroot, ← hHe]
  exact hfind

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Internal.NamedJointOutage
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

/-- If `v` is in `Xb` and the cover test of a key `k` and `B` on the grade view of `v`'s store in
    `W (strictEventIndex rho T2)` can return `true`, every outcome of the same test in
    `W (strictEventIndex rho T1)` is `true`, for `T1 ≥ T2`. -/
theorem q10_localCovers_fwdOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (hv : v ∈ Xb) {T2 T1 : Time}
    (h21 : T2 ≤ T1) (k : Option BlockId) (B : Block V)
    (h : M.localCovers (M.gradeView (M.toHealing (W (strictEventIndex rho T2) v).st.core)) k B
      ⇢ true) :
    ∀ b, M.localCovers (M.gradeView (M.toHealing (W (strictEventIndex rho T1) v).st.core)) k B
      ⇢ b → b = true := by
  intro b hb
  cases k with
  | none =>
    exact absurd (facts.gr.localCovers_none _ _ _ h) (by simp)
  | some root =>
    obtain ⟨H, hfnd, hBH⟩ := facts.gr.exists_find_of_localCovers true h rfl
    exact facts.gr.localCovers_of_find (Restated.q10_find_fwdOn facts S rho Hs Xb hf v hv h21 hfnd) hBH
      b hb

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Internal.NamedJointOutage
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

/-- For `T1 ≥ T2` and `c1 ≥ c2`, every outcome of the raw inputs at cutoff `c2` of the grade view of
    `v`'s store in `W (strictEventIndex rho T2)` is contained in every outcome of the raw inputs at
    cutoff `c1` of its store in `W (strictEventIndex rho T1)`. -/
theorem q10_rawInputs_fwdOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) {T2 T1 : Time} (h21 : T2 ≤ T1)
    {c1 c2 : Time} (hc : c2 ≤ c1) (eta r : Round) (sender : V) :
    ∀ X, M.rawInputs
        (M.gradeView (M.toHealing (W (strictEventIndex rho T2) v).st.core)) eta r c2 sender ⇢ X →
      ∀ Y, M.rawInputs
        (M.gradeView (M.toHealing (W (strictEventIndex rho T1) v).st.core)) eta r c1 sender ⇢ Y →
      X ⊆ Y := by
  intro X hX Y hY u hu
  obtain ⟨⟨k, hk, huk⟩, hval, hstamp⟩ := facts.gr.rawInputs_mem_window _ _ _ _ _ X hX hu
  obtain ⟨a, hround, hproj, hmem⟩ := Restated.pool_token_rowOn facts S rho Hs Xb hf T2 v
    _ (mem_stateBeforeTime_path₄₈ S rho hf.sorted W hf.onePath T2) huk
  subst hproj
  obtain ⟨hmem1, hstamp1⟩ := Restated.strict_sg_row_carryOn facts S rho Hs Xb hf v h21 hmem
  have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (W (strictEventIndex rho T1) v).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho T1 v _
      (mem_stateBeforeTime_path₄₈ S rho hf.sorted W hf.onePath T1)).1.1.1
  have hpool1 := facts.sto.pool_view_mem
    (W (strictEventIndex rho T1) v).st hcoh.2.2.2.1 a hmem1
  refine facts.gr.mem_rawInputs_of_occurrenceBefore _ _ _ k _ _ hk ?_ hval ?_ Y hY
  · rw [facts.gr.gradeView_sg_votes, ← hround]
    exact Finset.mem_image_of_mem M.sgVote hpool1
  · rw [facts.gr.gradeView_timestamp_sg_vote, hstamp1]
    rw [facts.gr.gradeView_timestamp_sg_vote] at hstamp
    exact occurrenceBefore_mono hc hstamp

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Internal.NamedJointOutage
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

/-- If `v` is in `Xb`, `u` is in an outcome of the interpreted inputs of the grade view of `v`'s
    store in `W (strictEventIndex rho T2)`, the cover test of `u`'s confirmed root and `B` there can
    return `true`, and `v`'s finalized block in `W (strictEventIndex rho T1)` is an ancestor of `B`,
    then `u` is in every outcome of the interpreted inputs of its store there, for `T1 ≥ T2`. -/
theorem q10_interpreted_fwd_coverOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (hv : v ∈ Xb) {T2 T1 : Time}
    (h21 : T2 ≤ T1) {c1 c2 : Time} (hc : c2 ≤ c1) (eta r : Round) (sender : V)
    (B : Block V)
    (hFB : Block.Preceq (W (strictEventIndex rho T1) v).st.core.F B)
    {u : Protocol.SGVote V} (X : Finset (Protocol.SGVote V))
    (hX : M.interpretedInputs
      (M.gradeView (M.toHealing (W (strictEventIndex rho T2) v).st.core))
      (W (strictEventIndex rho T2) v).st.core.F eta r c2 sender ⇢ X)
    (hu : u ∈ X)
    (hcov : M.localCovers (M.gradeView (M.toHealing (W (strictEventIndex rho T2) v).st.core))
      u.confirmed B ⇢ true) :
    ∀ Y, M.interpretedInputs
      (M.gradeView (M.toHealing (W (strictEventIndex rho T1) v).st.core))
      (W (strictEventIndex rho T1) v).st.core.F eta r c1 sender ⇢ Y → u ∈ Y := by
  intro Y hY
  obtain ⟨R2, hR2⟩ := facts.gr.rawInputs_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho T2) v).st.core)) eta r c2 sender
  obtain ⟨b2, hb2⟩ := facts.gr.bodyReady_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho T2) v).st.core))
    (W (strictEventIndex rho T2) v).st.core.F c2 u
  obtain ⟨R1, hR1⟩ := facts.gr.rawInputs_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho T1) v).st.core)) eta r c1 sender
  obtain ⟨b1, hb1⟩ := facts.gr.bodyReady_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho T1) v).st.core))
    (W (strictEventIndex rho T1) v).st.core.F c1 u
  obtain ⟨hraw, hready⟩ := (facts.gr.mem_interpretedInputs_iff X hX R2 hR2 b2 hb2).mp hu
  refine (facts.gr.mem_interpretedInputs_iff Y hY R1 hR1 b1 hb1).mpr
    ⟨Restated.q10_rawInputs_fwdOn facts S rho Hs Xb hf v h21 hc eta r sender R2 hR2 R1 hR1 hraw, ?_⟩
  cases hconf : u.confirmed with
  | none =>
    rw [hconf] at hcov
    exact absurd (facts.gr.localCovers_none _ _ _ hcov) (by simp)
  | some root =>
    rw [hconf] at hcov
    obtain ⟨H, hfnd, hready1, _⟩ := facts.gr.exists_find_of_bodyReady hconf b2 hb2 hready
    have hBH : Block.Preceq B H := facts.gr.preceq_of_localCovers_of_find true hcov rfl hfnd
    · have hfnd' := hfnd
      rw [facts.gr.Sts_gradeView_T] at hfnd'
      have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (W (strictEventIndex rho T2) v).st :=
        (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho T2 v _
          (mem_stateBeforeTime_path₄₈ S rho hf.sorted W hf.onePath T2)).1.1.1
      have hHmem : H ∈ (W (strictEventIndex rho T2) v).st.core.T :=
        Proofs.HealingLemmas.find?_mem hfnd'
      rw [hcoh.1] at hHmem
      obtain ⟨Hn, hHn, hHe⟩ := Finset.mem_image.mp hHmem
      obtain ⟨_, hstampeq⟩ := Restated.q10_strict_body_carryOn facts S rho Hs Xb hf v h21 hHn
      refine facts.gr.bodyReady_of_find hconf (Restated.q10_find_fwdOn facts S rho Hs Xb hf v hv h21 hfnd)
        ?_ ?_ b1 hb1
      · have hs2 : stampedBefore
            (W (strictEventIndex rho T2) v).st.core.timestamp_block c2 Hn.erase = true := by
          rw [facts.gr.gradeView_timestamp_block, ← hHe] at hready1
          exact hready1
        have hs1 : stampedBefore
            (W (strictEventIndex rho T1) v).st.core.timestamp_block c1 Hn.erase = true := by
          rw [stampedBefore_eq_occurrenceBefore] at hs2 ⊢
          rw [hstampeq]
          exact occurrenceBefore_mono hc hs2
        rw [facts.gr.gradeView_timestamp_block, ← hHe]
        exact hs1
      · exact compatible_of_cases (Or.inr (preceq_trans_Preceq hFB hBH))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Internal.NamedJointOutage
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

/-- If `v` is in `Hs (late r .g1)`, `r`'s window opens at or after `lo`, the G2 grade test of `B` on
    the grade view of `v`'s store in `W (strictEventIndex rho (domain r .g2))` can return `true`,
    and `v`'s finalized block in `W (strictEventIndex rho (domain r .g1))` is an ancestor of `B`,
    then every outcome of the G1 grade test of `B` on that store is `true`. -/
theorem q10_grade_crossOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (v : V) (r : Round) (hv : v ∈ Hs (M.late S.E S.hc r .g1)) (hr : 0 < r)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) (B : Block V)
    (hFB : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core.F B)
    (hgrade : M.gradeBool S.E
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core.F
      S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) B ⇢ true) :
    ∀ b, M.gradeBool S.E
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core.F
      S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) B ⇢ b → b = true := by
  intro b hb
  have hEarlyLo : lo ≤ M.early S.E S.hc r .g1 :=
    (facts.gr.lo_le_early_g2_of_window_start S hr hlo).trans (facts.gr.q10_early_g2_le_early_g1 S r)
  have hLateLo : lo ≤ M.late S.E S.hc r .g1 := hEarlyLo.trans (facts.gr.q10_early_le_late S r .g1)
  have hvEarly : v ∈ Hs (M.early S.E S.hc r .g1) := hHs _ _ (facts.gr.q10_early_le_late S r .g1) hv
  have hvXb : v ∈ Xb := hHsXb _ hv
  have h21 : M.domain S.E S.hc r .g2 ≤ M.domain S.E S.hc r .g1 :=
    (facts.gr.q10_domain_g2_lt_domain_g1 S r).le
  have hearly : M.early S.E S.hc r .g1 ≤ M.domain S.E S.hc r .g2 := facts.gr.q10_early_g1_le_domain_g2 S r
  have hlate : M.late S.E S.hc r .g1 ≤ M.domain S.E S.hc r .g2 := facts.gr.q10_late_g1_le_domain_g2 S r
  set gva := M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core)
    with hgva
  set gvb := M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core)
    with hgvb
  set Fa := (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core.F with hFa
  set Fb := (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core.F with hFb
  choose Rea hRea using fun w =>
    facts.gr.readyView_nonempty gva Fa S.hc.η_SG r (M.early S.E S.hc r .g2) w
  choose Rla hRla using fun w =>
    facts.gr.readyView_nonempty gva Fa S.hc.η_SG r (M.late S.E S.hc r .g2) w
  choose Wa hWa using fun w => facts.gr.rawView_nonempty gva S.hc.η_SG r (M.late S.E S.hc r .g2) w
  choose Reb hReb using fun w =>
    facts.gr.readyView_nonempty gvb Fb S.hc.η_SG r (M.early S.E S.hc r .g1) w
  choose Rlb hRlb using fun w =>
    facts.gr.readyView_nonempty gvb Fb S.hc.η_SG r (M.late S.E S.hc r .g1) w
  choose Wb hWb using fun w => facts.gr.rawView_nonempty gvb S.hc.η_SG r (M.late S.E S.hc r .g1) w
  choose cva hcva using fun k => facts.gr.localCovers_nonempty gva k B
  choose cvb hcvb using fun k => facts.gr.localCovers_nonempty gvb k B
  refine facts.gr.q10_gradeBool_transport S.E gva gvb Fa Fb S.hc.η_SG r _ _ _ _ B
    Rea hRea Rla hRla Wa hWa Reb hReb Rlb hRlb Wb hWb cva hcva cvb hcvb
    (fun w => facts.gr.q10_readyView_cut _ _ _ _ (facts.gr.q10_early_le_late S r .g2) w
      _ (hRea w) _ (hRla w))
    (fun w => facts.gr.q10_ready_subset_raw _ _ _ _ _ w _ (hRla w) _ (hWa w))
    (fun w => facts.gr.q10_readyView_cut _ _ _ _ (facts.gr.q10_early_le_late S r .g1) w
      _ (hReb w) _ (hRlb w))
    (fun w => facts.gr.q10_ready_subset_raw _ _ _ _ _ w _ (hRlb w) _ (hWb w))
    (fun w => ?_) (fun w => ?_) (fun w => ?_) (fun w => ?_)
    (fun k hk => Restated.q10_localCovers_fwdOn facts S rho Hs Xb hf v hvXb h21 k B
      (by rw [← hk]; exact hcva k) (cvb k) (hcvb k))
    true hgrade rfl b hb
  · intro x hx
    obtain ⟨Yb, hYb⟩ := facts.gr.interpretedInputs_nonempty gvb Fb S.hc.η_SG r
      (M.early S.E S.hc r .g1) w
    obtain ⟨y, hy, rfl⟩ := (facts.gr.mem_readyView_iff (Reb w) (hReb w) Yb hYb).mp hx
    obtain ⟨Ra, hRa⟩ := facts.gr.readyView_nonempty gva Fa S.hc.η_SG r (M.early S.E S.hc r .g1) w
    obtain ⟨Ya, hYa⟩ := facts.gr.interpretedInputs_nonempty gva Fa S.hc.η_SG r
      (M.early S.E S.hc r .g1) w
    have hya := Restated.q10_interpreted_backOn facts S rho Hs Xb hf hHsXb v hvEarly
      (facts.gr.q10_early_g1_public S r hr) hearly h21 S.hc.η_SG r w hEarlyLo Yb hYb Ya hYa hy
    exact facts.gr.q10_readyView_cut _ _ _ _ (hearly.trans (facts.gr.q10_domain_g2_le_late_g2 S r)) w
      Ra hRa (Rla w) (hRla w) ((facts.gr.mem_readyView_iff Ra hRa Ya hYa).mpr ⟨y, hya, rfl⟩)
  · intro x hx
    obtain ⟨Yb, hYb⟩ := facts.gr.interpretedInputs_nonempty gvb Fb S.hc.η_SG r
      (M.late S.E S.hc r .g1) w
    obtain ⟨y, hy, rfl⟩ := (facts.gr.mem_readyView_iff (Rlb w) (hRlb w) Yb hYb).mp hx
    obtain ⟨Ra, hRa⟩ := facts.gr.readyView_nonempty gva Fa S.hc.η_SG r (M.late S.E S.hc r .g1) w
    obtain ⟨Ya, hYa⟩ := facts.gr.interpretedInputs_nonempty gva Fa S.hc.η_SG r
      (M.late S.E S.hc r .g1) w
    have hya := Restated.q10_interpreted_backOn facts S rho Hs Xb hf hHsXb v hv
      (facts.gr.q10_late_g1_public S r hr) hlate h21 S.hc.η_SG r w hLateLo Yb hYb Ya hYa hy
    exact facts.gr.q10_readyView_cut _ _ _ _ (hlate.trans (facts.gr.q10_domain_g2_le_late_g2 S r)) w
      Ra hRa (Rla w) (hRla w) ((facts.gr.mem_readyView_iff Ra hRa Ya hYa).mpr ⟨y, hya, rfl⟩)
  · intro x hx
    obtain ⟨Yb, hYb⟩ := facts.gr.rawInputs_nonempty gvb S.hc.η_SG r (M.late S.E S.hc r .g1) w
    obtain ⟨y, hy, rfl⟩ := (facts.gr.mem_rawView_iff _ _ _ _ _ _ (Wb w) (hWb w) Yb hYb).mp hx
    obtain ⟨Va, hVa⟩ := facts.gr.rawView_nonempty gva S.hc.η_SG r (M.late S.E S.hc r .g1) w
    obtain ⟨Ya, hYa⟩ := facts.gr.rawInputs_nonempty gva S.hc.η_SG r (M.late S.E S.hc r .g1) w
    have hya := Restated.q10_rawInputs_backOn facts S rho Hs Xb hf v
      (facts.gr.q10_late_g1_public S r hr) hlate (hlate.trans h21) S.hc.η_SG r w hv hLateLo
      Yb hYb Ya hYa hy
    exact facts.gr.q10_rawView_cut _ _ _ (hlate.trans (facts.gr.q10_domain_g2_le_late_g2 S r)) w
      Va hVa (Wa w) (hWa w) ((facts.gr.mem_rawView_iff _ _ _ _ _ _ Va hVa Ya hYa).mpr ⟨y, hya, rfl⟩)
  · intro u hu hcov
    obtain ⟨Ya, hYa⟩ := facts.gr.interpretedInputs_nonempty gva Fa S.hc.η_SG r
      (M.early S.E S.hc r .g2) w
    obtain ⟨x, hx, rfl⟩ := (facts.gr.mem_readyView_iff (Rea w) (hRea w) Ya hYa).mp hu
    rw [facts.gr.token_key] at hcov
    obtain ⟨Yb, hYb⟩ := facts.gr.interpretedInputs_nonempty gvb Fb S.hc.η_SG r
      (M.early S.E S.hc r .g1) w
    exact (facts.gr.mem_readyView_iff (Reb w) (hReb w) Yb hYb).mpr
      ⟨x, Restated.q10_interpreted_fwd_coverOn facts S rho Hs Xb hf v hvXb h21
        (facts.gr.q10_early_g2_le_early_g1 S r) S.hc.η_SG r w B hFB Ya hYa hx
        (by rw [← hcov]; exact hcva _) Yb hYb, rfl⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Internal.NamedJointOutage
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

/-- For `T2 ≤ T1`, a block in the tree of the grade view of `v`'s store in
    `W (strictEventIndex rho T2)` is in the tree of the grade view of its store in
    `W (strictEventIndex rho T1)`. -/
theorem q10_tree_fwdOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) {T2 T1 : Time} (h21 : T2 ≤ T1) {B : Block V}
    (h : B ∈ (M.gradeView (M.toHealing (W (strictEventIndex rho T2) v).st.core)).T) :
    B ∈ (M.gradeView (M.toHealing (W (strictEventIndex rho T1) v).st.core)).T := by
  have hcoh2 : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (W (strictEventIndex rho T2) v).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho T2 v _
      (mem_stateBeforeTime_path₄₈ S rho hf.sorted W hf.onePath T2)).1.1.1
  have hcoh1 : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (W (strictEventIndex rho T1) v).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho T1 v _
      (mem_stateBeforeTime_path₄₈ S rho hf.sorted W hf.onePath T1)).1.1.1
  have h2 : B ∈ (W (strictEventIndex rho T2) v).st.core.T := by
    rw [facts.gr.Sts_gradeView_T] at h
    exact h
  rw [hcoh2.1] at h2
  obtain ⟨Bn, hBn, hBe⟩ := Finset.mem_image.mp h2
  have h1 : B ∈ (W (strictEventIndex rho T1) v).st.core.T := by
    rw [hcoh1.1]
    exact hBe ▸ Finset.mem_image_of_mem NamedBlock.erase
      ((Restated.q10_strict_body_carryOn facts S rho Hs Xb hf v h21 hBn).1)
  rw [facts.gr.Sts_gradeView_T]
  exact h1

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Internal.NamedJointOutage
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

/-- If `v` is in `Hs (late r .g1)`, `r`'s window opens at or after `lo`, `v`'s G2 freeze root of the
    positive round `r` in `W (strictEventIndex rho (domain r .g2))` can be `some g2`, and `v`'s
    finalized block in `W (strictEventIndex rho (domain r .g1))` is an ancestor of `g2`, then every
    outcome of `v`'s G1 freeze root of `r` there is `some g1` for a descendant `g1` of `g2`. -/
theorem q10_g1_of_g2_freezeOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (v : V) (r : Round) (hv : v ∈ Hs (M.late S.E S.hc r .g1)) (hr : 0 < r)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) (g2 : Block V)
    (hg2raw : M.freezeRoot S.E
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core.F S.hc.η_SG r
      (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) ⇢ some g2)
    (hFB : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core.F g2) :
    ∀ fr, M.freezeRoot S.E
          (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core))
          (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core.F S.hc.η_SG r
          (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) ⇢ fr →
    ∃ g1 : Block V, fr = some g1 ∧ Block.Preceq g2 g1 := by
  intro fr hfr
  have hmem2 := facts.gr.mem_T_of_freezeRoot_eq_some _ hg2raw rfl
  have hgrade2 : M.gradeBool S.E
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core.F
      S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) g2 ⇢ true := by
    obtain ⟨b2, hb2⟩ := facts.gr.gradeBool_nonempty S.E
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core.F
      S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) g2
    have hb2true := facts.gr.gradeBool_of_freezeRoot_eq_some _ hg2raw rfl b2 hb2
    rw [hb2true] at hb2
    exact hb2
  have hgrade1 := Restated.q10_grade_crossOn facts S rho Hs Xb hf hHs hHsXb v r hv hr hlo g2 hFB
    hgrade2
  have hmem1 := Restated.q10_tree_fwdOn facts S rho Hs Xb hf v (facts.gr.q10_domain_g2_lt_domain_g1 S r).le hmem2
  obtain ⟨b1, hb1⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core.F
    S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) g2
  exact facts.gr.q10_freeze_of_graded S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core.F
    S.hc.η_SG r (facts.gr.q10_early_le_late S r .g1) hmem1 b1 hb1 (hgrade1 b1 hb1) fr hfr

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Internal.NamedJointOutage
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

/-- If `v` is in `Hs (late r .g1)` and `r`'s window opens at or after `lo`, for a store whose
    round-`r` frame holds outcomes of `v`'s two freezes in `W (strictEventIndex rho (domain r .g2))`
    and `W (strictEventIndex rho (domain r .g1))`, clipped at its finalized block, a block `q` its
    G2 block read can return is an ancestor of every outcome of the frame's anchor. -/
theorem q10_frame_coreOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (v : V) (r : Round) (hv : v ∈ Hs (M.late S.E S.hc r .g1)) (hr : 0 < r)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG))
    (st : M.HS) (frame : M.Frame)
    (hFmono : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core.F st.F)
    (f2 : Option (Block V))
    (hf2 : M.freezeRoot S.E
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core.F S.hc.η_SG r
      (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) ⇢ f2)
    (hg2 : frame.g2 = some (f2.map (fun X => M.clipGrade X st.F)))
    (f1 : Option (Block V))
    (hf1 : M.freezeRoot S.E
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core.F S.hc.η_SG r
      (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) ⇢ f1)
    (hg1 : frame.g1 = some (f1.map (fun X => M.clipGrade X st.F)))
    (q : Block V)
    (hq : M.grade2Block st frame ⇢ some q) :
    ∀ a, M.anchor S.E S.hc st r frame.g1 ⇢ a → Block.Preceq q a := by
  intro a ha
  obtain ⟨g2c, hg2c, hqle⟩ := facts.gr.grade2Block_some _ hq rfl
  have hqmem : q ∈ M.get_filtered_block_tree st.toFG :=
    facts.gr.mem_filtered_of_grade2Block _ hq rfl
  rw [hg2] at hg2c
  obtain ⟨g2, hg2raw, hclip⟩ := Option.map_eq_some_iff.mp (Option.some_injective _ hg2c)
  subst hg2raw
  have hFq : Block.Preceq st.F q := facts.fc.q10_filtered_F hqmem
  have hcompatq : Block.compatible q st.F = true := compatible_of_cases (Or.inr hFq)
  have hclip' : M.clipGrade g2 st.F = g2c := hclip
  have hqg2 : Block.Preceq q g2 := by
    refine (facts.gr.q10_retained_prefix g2 st.F q hcompatq).mp ?_
    rw [hclip']
    exact hqle
  have hFB : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core.F g2 :=
    preceq_trans_Preceq hFmono (preceq_trans_Preceq hFq hqg2)
  obtain ⟨g1, hfz1, hg2g1⟩ :=
    Restated.q10_g1_of_g2_freezeOn facts S rho Hs Xb hf hHs hHsXb v r hv hr hlo g2 hf2 hFB
      f1 hf1
  have hg1' : frame.g1 = some (some (M.clipGrade g1 st.F)) := by
    rw [hg1, hfz1]
    rfl
  have hqclip : Block.Preceq q (M.clipGrade g1 st.F) :=
    (facts.gr.q10_retained_prefix g1 st.F q hcompatq).mpr (preceq_trans_Preceq hqg2 hg2g1)
  rw [hg1'] at ha
  exact facts.gr.preceq_anchor_of_g1 S.E S.hc st r hqmem hqclip a ha

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Internal.NamedJointOutage
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

/-- Along the path `W` of the bundle, if `v` is in `Hs (domain r .g1)` and `r`'s window opens at or
    after `lo`, then for every outcome `c` of the phase tick at `S.a r` from `v`'s node state in
    `W (strictEventIndex rho (S.a r))`, a block `q` that the G2 block read of the confirmation read
    built with `c` can return is an ancestor of every outcome of that read's anchor. -/
theorem grade2_preceq_anchor_at_checkpointOn (facts : Record.Facts M) (S : Setup V)
    (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (v : V) (b0 : Time) (r : Round) (hv : v ∈ Hs (M.domain S.E S.hc r .g1))
    (hinc : Restated.Vocabulary.Internal.NamedJointOutage.RoundIncluded M S rho b0 r)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (M.toHealing (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core)
      (Restated.Vocabulary.Execution.Setup.a M S r)
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).cache ⇢ c)
    (q : Block V)
    (hq : M.grade2Block
      (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st
          (Restated.Vocabulary.Execution.Setup.a M S r))
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).record c).st.core)
      (M.readFrame (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st
            (Restated.Vocabulary.Execution.Setup.a M S r))
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).record c).cache
        (M.toHealing (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st
            (Restated.Vocabulary.Execution.Setup.a M S r))
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).record c).st.core)
        r) ⇢ some q) :
    ∀ A, M.anchor S.E S.hc
      (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st
          (Restated.Vocabulary.Execution.Setup.a M S r))
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).record c).st.core) r
      (M.readFrame (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st
            (Restated.Vocabulary.Execution.Setup.a M S r))
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).record c).cache
        (M.toHealing (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st
            (Restated.Vocabulary.Execution.Setup.a M S r))
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).record c).st.core)
        r).g1 ⇢ A →
    Block.Preceq q A := by
  intro A hA
  have hr : 0 < r := hinc.1
  have hΔ := S.E.Δ_pos
  have hdomA : ∀ p, M.domain S.E S.hc r p < Restated.Vocabulary.Execution.Setup.a M S r := by
    intro p
    have h5 := facts.gr.domain_add_five_delta_le_action S r p
    show M.domain S.E S.hc r p < M.a S.hc S.E.Δ r
    linarith
  have h21 : M.domain S.E S.hc r .g2 ≤ M.domain S.E S.hc r .g1 :=
    (facts.gr.q10_domain_g2_lt_domain_g1 S r).le
  have hhor : M.domain S.E S.hc r .g1 ≤ rho.horizon := (hdomA .g1).le.trans hinc.2.2
  have hvG2 : v ∈ Hs (M.domain S.E S.hc r .g2) := hHs _ _ h21 hv
  have hvLate : v ∈ Hs (M.late S.E S.hc r .g1) :=
    hHs _ _ ((facts.gr.q10_late_g1_le_domain_g2 S r).trans h21) hv
  have hF : (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st
          (Restated.Vocabulary.Execution.Setup.a M S r))
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).record c).st.core).toFG.F =
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.F := by
    rewrite [facts.sto.ModelProperties_toHealing_F, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_F]
  have hmem := mem_stateBeforeTime_path₄₈ S rho hf.sorted W hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  obtain ⟨f2, hf2⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core.F S.hc.η_SG r
    (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2)
  obtain ⟨f1, hf1⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core.F S.hc.η_SG r
    (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1)
  refine q10_frame_coreOn facts S rho Hs Xb hf hHs hHsXb v r hvLate hr hlo _ _ ?_ f2 hf2 ?_
    f1 hf1 ?_ q hq A hA
  · show Block.Preceq _ (M.toHealing _).toFG.F
    rw [hF]
    have hidx : strictEventIndex rho (M.domain S.E S.hc r .g1) ≤
        strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r) :=
      (List.monotone_filter_right rho.events (fun e he => by
        simp only [decide_eq_true_eq] at he ⊢
        exact lt_of_lt_of_le he (hdomA .g1).le)).length_le
    exact Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_F_mono facts S rho v hidx _
      (hf.onePath _).1 _ (onePath_slice₄₈ W hf.onePath hidx)
  · rw [← facts.gr.Sts_phaseResult_g2]
    show _ = some (Option.map (fun X => M.clipGrade X (M.toHealing _).toFG.F) _)
    rw [hF]
    exact Restated.Vocabulary.Proofs.FrameForward.frame_phase_checkpoint_eq facts S rho v r .g2 _ _
      hmem (Restated.frame_phase_completedOn facts S rho Hs Xb hf v r hr .g2 hvG2 _ (hdomA .g2)
        le_rfl (h21.trans hhor) (facts.gr.lo_le_domain_of_window_start S hr hlo .g2)
        (fun j hj => hf.tick_outcome j _ _ hj) f2 hf2) c hc
  · rw [← facts.gr.phaseResult_g1]
    show _ = some (Option.map (fun X => M.clipGrade X (M.toHealing _).toFG.F) _)
    rw [hF]
    exact Restated.Vocabulary.Proofs.FrameForward.frame_phase_checkpoint_eq facts S rho v r .g1 _ _
      hmem (Restated.frame_phase_completedOn facts S rho Hs Xb hf v r hr .g1 hv _ (hdomA .g1)
        le_rfl hhor (facts.gr.lo_le_domain_of_window_start S hr hlo .g1) (fun j hj => hf.tick_outcome j _ _ hj) f1 hf1) c hc

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

/-- If `reader` is in `Xb` and holds the body `H` in `W (strictEventIndex rho t)`, its tree there
    resolves `H`'s root to `H`. -/
theorem held_find_at_strict_localOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (reader : V)
    (hreader : reader ∈ Xb) (t : Time) (H : NamedBlock V)
    (hH : H ∈ (W (strictEventIndex rho t) reader).st.bodies) :
    Block.find? (W (strictEventIndex rho t) reader).st.core.T H.erase.root = some H.erase :=
  Restated.held_find_at_strictOn_HealthyHeadReady facts S rho Hs Xb hf reader hreader t H hH

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

/-- If `v` and `w` are in `Hs (early r p)`, `v` emits along `W`, at the action instant of a round
    `k` of `r`'s window at or after `lo`, a vote `a` whose head `H` it holds, `H` and the finalized
    block of `w`'s store in `W (strictEventIndex rho t)` have a common descendant, and
    `max (S.a a.round) lo + Δ ≤ early r p ≤ t` with `early r p` inside the horizon, then `a`'s SG
    vote is in every outcome of the interpreted inputs of `w`'s store there for `v` at that cutoff. -/
theorem action_vote_mem_interpretedInputs_after_gst_common_upperOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {t : Time} {r k : Round} (p : Phase)
    (hk : k ∈ M.latest_window S.hc.η_SG r)
    {v w : V} (hv : v ∈ Hs (M.early S.E S.hc r p)) (hw : w ∈ Hs (M.early S.E S.hc r p))
    {a : NamedAttestation V} {H : NamedBlock V} {C : Block V}
    (hvote : a.val_index = v ∧ a.round = k ∧
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (Object.attest a) ((Restated.Vocabulary.Execution.Setup.a M S k)))
    (hhead : ∃ i : Nat, rho.events[i]? = some (.tick v ((Restated.Vocabulary.Execution.Setup.a M S k))) ∧
      (∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (W i v) a.round,
        H ∈ n.st.bodies) ∧
      a.confirmed = some H.root)
    (hHC : Block.Preceq H.erase C)
    (hFC : Block.Preceq (W (strictEventIndex rho t) w).st.core.F C)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S a.round))
    (hdeadline : max ((Restated.Vocabulary.Execution.Setup.a M S a.round)) lo + S.E.Δ ≤
      M.early S.E S.hc r p)
    (horder : M.early S.E S.hc r p ≤ t)
    (hcut : M.early S.E S.hc r p ≤ rho.horizon) :
    ∀ Y, M.interpretedInputs
      (M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core))
      (W (strictEventIndex rho t) w).st.core.F
      S.hc.η_SG r (M.early S.E S.hc r p) v ⇢ Y → M.sgVote a.erase ∈ Y := by
  intro Y hY
  have hW := hf.onePath
  obtain ⟨i, hi, ⟨nr, hnr, hH⟩, hconfirmed⟩ := hhead
  have hmaxEq : max ((Restated.Vocabulary.Execution.Setup.a M S a.round)) lo = (Restated.Vocabulary.Execution.Setup.a M S a.round) := max_eq_left hpost
  have hactionDeadline : (Restated.Vocabulary.Execution.Setup.a M S a.round) + S.E.Δ ≤ M.early S.E S.hc r p := by
    rw [← hmaxEq]
    exact hdeadline
  have hactionEarly : (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ M.early S.E S.hc r p :=
    le_trans (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)) hactionDeadline
  have hvAction : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := hHs _ _ hactionEarly hv
  have hwAction : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := hHs _ _ hactionEarly hw
  have hwDelta : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S a.round) + S.E.Δ) := hHs _ _ hactionDeadline hw
  have hvXb : v ∈ Xb := hHsXb _ hv
  have hwXb : w ∈ Xb := hHsXb _ hw
  have hi' : rho.events[i]? = some (.tick v ((Restated.Vocabulary.Execution.Setup.a M S a.round))) := by
    simpa only [hvote.2.1] using hi
  have hbody : H ∈ (W i v).st.bodies := by
    rw [actionReadFrom_bodies₄₈ facts S _ _ nr hnr] at hH
    exact hH
  have hstate := Restated.action_read_indexOn facts S rho Hs Xb hf i v a.round hi'
  have hHsource : H ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) v).st.bodies := by
    rcases hstate with hstate | hstate
    · rw [← hstate]
      exact hbody
    · rw [hstate, (facts.nd.wake_st_record _).1] at hbody
      exact hbody
  have hEarlyIdx : strictEventIndex rho (M.early S.E S.hc r p) ≤ strictEventIndex rho t :=
    Restated.strict_lengths_mono rho horder
  have hFmono : Block.Preceq
      (W (strictEventIndex rho (M.early S.E S.hc r p)) w).st.core.F
      (W (strictEventIndex rho t) w).st.core.F :=
    Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_F_mono facts S rho w hEarlyIdx
      _ (hW _).1 _ (onePath_slice₄₈ W hW hEarlyIdx)
  have hcompFD : Block.compatible H.erase
      (W (strictEventIndex rho t) w).st.core.F = true :=
    compatible_of_preceq_common_Preceq hHC hFC
  have hcompFE : Block.compatible H.erase
      (W (strictEventIndex rho (M.early S.E S.hc r p)) w).st.core.F = true := by
    rcases compatible_cases hcompFD with hHF | hFH
    · exact compatible_of_preceq_common_Preceq hHF hFmono
    · exact compatible_of_cases (Or.inr (preceq_trans_Preceq hFmono hFH))
  have hEarlyMem := mem_stateBeforeTime_path₄₈ S rho hf.sorted W hW (M.early S.E S.hc r p)
  have hready : H ∈
      (W (strictEventIndex rho t) w).st.bodies ∧
      stampedBefore
        (W (strictEventIndex rho t) w).st.core.timestamp_block
        (M.early S.E S.hc r p) H.erase = true ∧
      Block.find?
        (W (strictEventIndex rho t) w).st.core.T H.root = some H.erase := by
    rcases compatible_cases hcompFE with hHF | hFH
    · have hFmem := Restated.Vocabulary.Proofs.NamedStoreBridge.finalizedInTree_stateBeforeTime facts S rho
          (M.early S.E S.hc r p) w _ hEarlyMem
      obtain ⟨Fname, hFname, hFerase⟩ :=
        Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
          (M.early S.E S.hc r p) w _ hEarlyMem hFmem
      have hHFn : H.erase ⪯ Fname.erase := by
        rw [hFerase]
        exact hHF
      obtain ⟨A, hAF, hAerase⟩ := Proofs.NamedAncestry.erased_ancestor_lift Fname hHFn
      have hFnameRun := Restated.blockInRun_of_directOn facts S rho W Xb
        (Restated.directBlock_of_prefixOn facts S rho W Xb hwXb _ hFname)
      have hArun := Restated.blockInRun_of_ancestorOn facts S rho W Xb hFnameRun hAF
      have hHrun := Restated.blockInRun_of_directOn facts S rho W Xb
        (Restated.directBlock_of_prefixOn facts S rho W Xb hvXb i hbody)
      have hAroot : A.root = H.root := by
        have : A.erase.root = H.root := by
          rw [hAerase, Proofs.NamedWire.erase_root]
        simpa only [Proofs.NamedWire.erase_root] using this
      have hAH := hf.rootCollisionFree.root_injective A H hArun hHrun
        A H (Or.inl (Proofs.NamedAncestry.named_self A))
        (Or.inr (Proofs.NamedAncestry.named_self H)) hAroot
      have hAheld : A ∈ (W (strictEventIndex rho (M.early S.E S.hc r p)) w).st.bodies :=
        namedAncestor_mem₄₈
          ((Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
            (M.early S.E S.hc r p) w _ hEarlyMem).1.1.1.2.2.1) hFname hAF
      have hHheld : H ∈ (W (strictEventIndex rho (M.early S.E S.hc r p)) w).st.bodies := by
        rw [← hAH]
        exact hAheld
      have hstampE :=
        Restated.held_body_stampedBefore_stateBeforeTimeOn facts S rho Hs Xb hf w (M.early S.E S.hc r p) H
          hHheld
      obtain ⟨hheld, hstampCarry⟩ :=
        Restated.q10_strict_body_carryOn facts S rho Hs Xb hf w horder hHheld
      have hstamp : stampedBefore
          (W (strictEventIndex rho t) w).st.core.timestamp_block
          (M.early S.E S.hc r p) H.erase = true := by
        rw [stampedBefore_eq_occurrenceBefore] at hstampE ⊢
        rw [hstampCarry]
        exact hstampE
      have hfind := Restated.held_find_at_strict_localOn facts S Hs Xb hf w hwXb t H hheld
      rw [Proofs.NamedWire.erase_root H] at hfind
      exact ⟨hheld, hstamp, hfind⟩
    · obtain ⟨hheldE, hstampE, -⟩ :=
        Restated.healthy_head_body_at_read_after_gst_admitOn facts S rho Hs Xb hf hHs hHsXb
          v w H ((Restated.Vocabulary.Execution.Setup.a M S a.round)) (M.early S.E S.hc r p)
          (M.early S.E S.hc r p) (by rw [hmaxEq]; exact hvAction) hw hHsource hdeadline le_rfl
          hcut hFH
      obtain ⟨hheld, hstampCarry⟩ :=
        Restated.q10_strict_body_carryOn facts S rho Hs Xb hf w horder hheldE
      have hstamp : stampedBefore
          (W (strictEventIndex rho t) w).st.core.timestamp_block
          (M.early S.E S.hc r p) H.erase = true := by
        rw [stampedBefore_eq_occurrenceBefore] at hstampE ⊢
        rw [hstampCarry]
        exact hstampE
      have hfind := Restated.held_find_at_strict_localOn facts S Hs Xb hf w hwXb t H hheld
      rw [Proofs.NamedWire.erase_root H] at hfind
      exact ⟨hheld, hstamp, hfind⟩
  obtain ⟨hheld, hstamp, hfind⟩ := hready
  have hem : Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (Object.attest a)
      ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
    simpa only [hvote.1, hvote.2.1] using hvote.2.2
  have hvalAction : a.val_index ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
    simpa only [hvote.1] using hvAction
  obtain ⟨td, hlo, hhi, j, hcall⟩ := hf.broadcast a.val_index
    (Object.attest a) ((Restated.Vocabulary.Execution.Setup.a M S a.round)) hvalAction hem w hwDelta hpost
    (hactionDeadline.trans hcut) (fun B hB => by cases hB)
  have htdEarly : td < M.early S.E S.hc r p := hhi.trans_le hactionDeadline
  have hvalTd : a.val_index ∈ Hs td := by
    simpa only [hvote.1] using hHs _ _ htdEarly.le hv
  have hrow := Restated.honest_row_after_callOn facts S rho Hs Xb hf hHs hvalTd hem hcall hlo hhi
    hwAction hpost
  obtain ⟨e, he, _, het⟩ := hcall.2
  obtain ⟨_, stamp, hstampBound, hstampEvent⟩ :=
    Restated.held_row_own_and_stamp_at_eventOn facts S rho Hs Xb hf he w a.round a
      (W (j + 1)) (hW _).1 hrow
  have heEarly : e.time < M.early S.E S.hc r p := by
    simpa only [het] using htdEarly
  have heCut : e.time < t := heEarly.trans_le horder
  have hjN : j + 1 ≤ strictEventIndex rho t :=
    Nat.succ_le_of_lt (lt_strict_of_time_lt₄₈ hf.sorted he heCut)
  have hrowN := Restated.Vocabulary.Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono facts S rho w
    hjN (W (j + 1)) (hW _).1 hrow _ (onePath_slice₄₈ W hW hjN)
  have hrowCut : a ∈ (W (strictEventIndex rho t) w).st.sg_rows a.round := hrowN.1
  have hstampCut :
      (W (strictEventIndex rho t) w).st.core.timestamp_sg_vote
        (M.sgVote a.erase) = some (stamp : Stamp) :=
    hrowN.2.trans hstampEvent
  have hstampEarly : stamp < M.early S.E S.hc r p := hstampBound.trans_lt heEarly
  have hoccur : occurrenceBefore
      ((W (strictEventIndex rho t) w).st.core.timestamp_sg_vote
        (M.sgVote a.erase)) (M.early S.E S.hc r p) = true := by
    rw [hstampCut, occurrenceBefore_some_iff]
    exact WithBot.coe_lt_coe.mpr hstampEarly
  have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho t w _
    (mem_stateBeforeTime_path₄₈ S rho hf.sorted W hW t)).1.1.1
  have hpool := facts.sto.pool_view_mem _ hcoh.2.2.2.1 a hrowCut
  let target := W (strictEventIndex rho t) w
  have hsg : M.sgVote a.erase ∈
      (M.gradeView (M.toHealing target.st.core)).sg_votes a.round := by
    rw [facts.gr.gradeView_sg_votes]
    exact Finset.mem_image_of_mem M.sgVote hpool
  obtain ⟨R, hR⟩ := facts.gr.rawInputs_nonempty (M.gradeView (M.toHealing target.st.core))
    S.hc.η_SG r (M.early S.E S.hc r p) v
  obtain ⟨b, hb⟩ := facts.gr.bodyReady_nonempty (M.gradeView (M.toHealing target.st.core))
    target.st.core.F (M.early S.E S.hc r p) (M.sgVote a.erase)
  have hraw : M.sgVote a.erase ∈ R := by
    refine facts.gr.mem_rawInputs_of_occurrenceBefore _ _ _ a.round _ _
      (by simpa only [hvote.2.1] using hk) hsg ?_ ?_ R hR
    · rw [facts.sto.sgVote_val, hvote.1]
    · rw [facts.gr.gradeView_timestamp_sg_vote]
      exact hoccur
  have hconf : (M.sgVote a.erase).confirmed = some H.root := by
    rw [facts.sto.sgVote_confirmed, hconfirmed]
  have hfind' : Block.find? target.st.core.T H.root = some H.erase := by
    simpa only [target, Proofs.NamedWire.erase_root] using hfind
  have hbodyReady : b = true := by
    refine facts.gr.bodyReady_of_find hconf ?_ ?_ hcompFD b hb
    · rw [facts.gr.Sts_gradeView_T]
      exact hfind'
    · rw [facts.gr.gradeView_timestamp_block]
      exact hstamp
  exact (facts.gr.mem_interpretedInputs_iff Y hY R hR b hb).mpr ⟨hraw, hbodyReady⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

/-- Under the hypotheses of `action_vote_mem_interpretedInputs_after_gst_common_upperOn`, every
    outcome of the interpreted inputs of `w`'s store in `W (strictEventIndex rho t)` for `v` at
    `early r p` has a member of round `k` that confirms `H`'s root, and `w`'s tree there resolves
    `H`'s root to `H`. -/
theorem interpretedInputs_exact_of_honest_window_vote_after_gst_common_upperOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {t : Time} {r k : Round} (p : Phase)
    (hk : k ∈ M.latest_window S.hc.η_SG r)
    {v w : V} (hv : v ∈ Hs (M.early S.E S.hc r p)) (hw : w ∈ Hs (M.early S.E S.hc r p))
    {a : NamedAttestation V} {H : NamedBlock V} {C : Block V}
    (hvote : a.val_index = v ∧ a.round = k ∧
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (Object.attest a) ((Restated.Vocabulary.Execution.Setup.a M S k)))
    (hhead : ∃ i : Nat, rho.events[i]? = some (.tick v ((Restated.Vocabulary.Execution.Setup.a M S k))) ∧
      (∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (W i v) a.round,
        H ∈ n.st.bodies) ∧
      a.confirmed = some H.root)
    (hHC : Block.Preceq H.erase C)
    (hFC : Block.Preceq (W (strictEventIndex rho t) w).st.core.F C)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S a.round))
    (hdeadline : max ((Restated.Vocabulary.Execution.Setup.a M S a.round)) lo + S.E.Δ ≤
      M.early S.E S.hc r p)
    (horder : M.early S.E S.hc r p ≤ t)
    (hcut : M.early S.E S.hc r p ≤ rho.horizon) :
    ∀ Ys, M.interpretedInputs
      (M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core))
      (W (strictEventIndex rho t) w).st.core.F
      S.hc.η_SG r (M.early S.E S.hc r p) v ⇢ Ys →
    ∃ y ∈ Ys,
      y.round = k ∧
      y.confirmed = some H.erase.root ∧
      Block.find? (W (strictEventIndex rho t) w).st.core.T H.root = some H.erase := by
  intro Ys hYs
  have hmem := Restated.action_vote_mem_interpretedInputs_after_gst_common_upperOn facts
    S Hs Xb hf hHs hHsXb p hk hv hw hvote hhead hHC hFC hpost hdeadline horder hcut Ys hYs
  obtain ⟨i, hi, ⟨nr, hnr, hH⟩, hconfirmed⟩ := hhead
  have hHbody : H ∈ (W i v).st.bodies := by
    rw [actionReadFrom_bodies₄₈ facts S _ _ nr hnr] at hH
    exact hH
  have hHrun : Restated.RunBlockOn M S rho W Xb H :=
    Restated.blockInRun_of_directOn facts S rho W Xb
      (Restated.directBlock_of_prefixOn facts S rho W Xb (hHsXb _ hv) i hHbody)
  obtain ⟨R, hR⟩ := facts.gr.rawInputs_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core)) S.hc.η_SG r
    (M.early S.E S.hc r p) v
  obtain ⟨b, hb⟩ := facts.gr.bodyReady_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core))
    (W (strictEventIndex rho t) w).st.core.F (M.early S.E S.hc r p) (M.sgVote a.erase)
  have hready := ((facts.gr.mem_interpretedInputs_iff Ys hYs R hR b hb).mp hmem).2
  have hvoteConfirmed : (M.sgVote a.erase).confirmed = some H.root := by
    rw [facts.sto.sgVote_confirmed, hconfirmed]
  cases hfind : Block.find?
      (M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core)).T H.root with
  | none =>
      obtain ⟨Y, hY, -⟩ := facts.gr.exists_find_of_bodyReady hvoteConfirmed b hb hready
      rw [hfind] at hY
      cases hY
  | some X =>
      have hfindT := hfind
      rw [facts.gr.Sts_gradeView_T] at hfindT
      have hXmem : X ∈ (W (strictEventIndex rho t) w).st.core.T :=
        by exact Proofs.HealingLemmas.find?_mem hfindT
      obtain ⟨Xn, hXerase, hXrun⟩ :=
        Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hw) t hXmem
      have hroot : Xn.root = H.root := by
        rw [← Proofs.NamedWire.erase_root Xn, hXerase]
        exact Proofs.HealingLemmas.find?_root hfind
      have hXH : Xn = H := hf.rootCollisionFree.root_injective
        Xn H hXrun hHrun Xn H
          (Or.inl (Proofs.NamedAncestry.named_self Xn))
          (Or.inr (Proofs.NamedAncestry.named_self H)) hroot
      refine ⟨M.sgVote a.erase, hmem, ?_, ?_, ?_⟩
      · rw [facts.sto.sgVote_round]
        exact hvote.2.1
      · rw [facts.sto.sgVote_confirmed, hconfirmed,
          Proofs.NamedWire.erase_root]
      · exact hfindT.trans (congrArg some
          (hXerase.symm.trans (congrArg NamedBlock.erase hXH)))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₄₈ {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- Along the path `W` of the bundle, if `u` is in `Hs (domain r .g1)`, `r` is positive with `S.a r`
    inside the horizon and its window opens at or after `lo`, `n` is a node state of `u`'s round-`r`
    action read and `G` an outcome of `n`'s round-`r` grade read with Q2 `Q` and clear target `T`,
    and `R` is both the FG root of the store `u`'s confirmation duty reads at the confirmation
    instant of `r`'s opening slot and `n`'s live confirmed block, then `T = R` and `T = Q`. -/
theorem clearTarget_eq_fgRoot_and_selectedG2_of_selectedG2On (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r) (hhor : Restated.Vocabulary.Execution.Setup.a M S r ≤ rho.horizon)
    {u : V} (hu : u ∈ Hs (M.domain S.E S.hc r .g1)) {Q T R : Block V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r)
    (G : Protocol.GradeRead V)
    (hG : Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n r ⇢ G)
    (hQ : G.Q2 = some Q)
    (hclear : M.deepest_clear (some G.anchor) n.st.core.live_confirmed G.clear = some T)
    (hRroot : R = M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r)))
        u).st.core (M.confirmation_time S.E (M.opening_slot S.hc r)))).toFG)
    (hRlive : R = n.st.core.live_confirmed)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    T = R ∧ T = Q := by
  have ha : Restated.Vocabulary.Execution.Setup.a M S r =
      M.confirmation_time S.E (M.opening_slot S.hc r) := facts.sch.a_eq_confirmation_time S.hc S.E r
  rw [← ha] at hRroot
  have hmem := mem_stateBeforeTime_path₄₈ S rho hf.sorted W hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  set w := W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) with hw
  obtain ⟨c, hc, st0, hst0, hneq⟩ := id hn
  have hncache : n.cache = c := by rw [hneq, facts.nd.mkNode_cache]
  have hq2 : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q := by
    rw [← hQ]
    exact returns_map_intro₄₈ (fun g => g.Q2) _ G hG
  have hQaction : Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n :=
    Restated.Vocabulary.Proofs.HealingSurface.actionQ2_mem_filteredTree facts S rho u r w hmem n hn hq2
  have hrootQ : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) Q :=
    preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered hQaction)
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w u).st.core
      (M.confirmation_time S.E (M.opening_slot S.hc r))) (M.opening_slot S.hc r)
  obtain ⟨s0, hs0, hs0X⟩ :=
    Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_eq_update_confirmation_confStore
      facts S rho u r w hmem n hn X hX
  rw [← ha] at hX
  have hcst : Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w u).st.core
      (Restated.Vocabulary.Execution.Setup.a M S r) =
      (M.ns_setClock S.E (w u).st (Restated.Vocabulary.Execution.Setup.a M S r)).core := by
    rw [facts.hd.setClock_core_eq_store_with_t_s]
    rfl
  have htree : M.get_filtered_block_tree (M.toHealing n.st.core).toFG =
      M.get_filtered_block_tree (M.toHealing (M.mkNode (M.ns_setClock S.E (w u).st
        (Restated.Vocabulary.Execution.Setup.a M S r)) (w u).record c).st.core).toFG := by
    rw [hs0, facts.nd.store_with_cache_get_filtered_block_tree, hs0X,
      facts.dt.update_confirmation_with_toHealing_filtered _ _ _ _ _ X hX, hcst, facts.nd.mkNode_st,
      facts.nd.store_with_cache_get_filtered_block_tree]
  have hroot : M.get_fg_root (M.toHealing n.st.core).toFG =
      M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E (w u).st
        (Restated.Vocabulary.Execution.Setup.a M S r)) (w u).record c).st.core).toFG := by
    rw [hs0, facts.nd.store_with_cache_get_fg_root, hs0X,
      facts.dt.update_confirmation_with_toHealing_fg_root _ _ _ _ _ X hX, hcst, facts.nd.mkNode_st,
      facts.nd.store_with_cache_get_fg_root]
  have hframe := Restated.Vocabulary.Proofs.HealingSurface.actionRead_readFrame_eq_checkpoint
    facts S rho u r w hmem n hn
  obtain ⟨x, hx⟩ := facts.gr.grade2Block_nonempty (M.toHealing n.st.core)
    (M.readFrame n.cache (M.toHealing n.st.core) r)
  have hxQ : x = some Q :=
    (facts.nd.ModelProperties_gradeContract_read_Q2 n.cache S.E S.hc _ r G hG x hx).symm.trans hQ
  subst hxQ
  have hframe_g : ∀ p : DecoupledConsensusModel.Protocol.Phase,
      M.phaseResult (M.readFrame n.cache (M.toHealing n.st.core) r) p =
        M.phaseResult (M.readFrame (M.mkNode (M.ns_setClock S.E (w u).st
          (Restated.Vocabulary.Execution.Setup.a M S r)) (w u).record c).cache (M.toHealing (M.mkNode (M.ns_setClock S.E (w u).st
          (Restated.Vocabulary.Execution.Setup.a M S r)) (w u).record c).st.core) r) p := by
    intro p; rw [hframe p, hncache]
  have hx' : M.grade2Block (M.toHealing n.st.core)
      (M.readFrame (M.mkNode (M.ns_setClock S.E (w u).st
          (Restated.Vocabulary.Execution.Setup.a M S r)) (w u).record c).cache
        (M.toHealing (M.mkNode (M.ns_setClock S.E (w u).st
          (Restated.Vocabulary.Execution.Setup.a M S r)) (w u).record c).st.core) r) ⇢ some Q :=
    (facts.gr.grade2Block_eq_of_phases
    (by rw [← facts.gr.phaseResult_g0, ← facts.gr.phaseResult_g0]; exact hframe_g .g0)
    (by rw [← facts.gr.phaseResult_g1, ← facts.gr.phaseResult_g1]; exact hframe_g .g1)
    (by rw [← facts.gr.Sts_phaseResult_g2, ← facts.gr.Sts_phaseResult_g2]; exact hframe_g .g2)
    (some Q)).mp hx
  have hQcheck := (facts.gr.grade2Block_eq_of_filtered_eq _ htree (some Q)).mp hx'
  have hQA := grade2_preceq_anchor_at_checkpointOn facts S rho Hs Xb hf hHs hHsXb u
    (Restated.Vocabulary.Execution.Setup.a M S r) r hu ⟨hr, le_rfl, hhor⟩ hlo c hc Q hQcheck
  have hQA' : Block.Preceq Q G.anchor := by
    obtain ⟨A, hA⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing n.st.core) r
      (M.readFrame n.cache (M.toHealing n.st.core) r).g1
    have hGA : G.anchor = A :=
      facts.nd.ModelProperties_gradeContract_read_anchor n.cache S.E S.hc _ r G hG A hA
    have hg1 : (M.readFrame n.cache (M.toHealing n.st.core) r).g1 =
        (M.readFrame (M.mkNode (M.ns_setClock S.E (w u).st
          (Restated.Vocabulary.Execution.Setup.a M S r)) (w u).record c).cache (M.toHealing (M.mkNode (M.ns_setClock S.E (w u).st
          (Restated.Vocabulary.Execution.Setup.a M S r)) (w u).record c).st.core) r).g1 := by
      rw [← facts.gr.phaseResult_g1, ← facts.gr.phaseResult_g1]; exact hframe_g .g1
    rw [hg1] at hA
    rw [hGA]
    exact hQA A ((facts.gr.anchor_eq_of_filtered_fg_root _ _ _ _ htree hroot A).mp hA)
  have hAT : Block.Preceq G.anchor T :=
    facts.gr.deepest_clear_floor_Preceq hclear
  have hrootEq : M.get_fg_root (M.toHealing n.st.core).toFG =
      M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w u).st.core
        (Restated.Vocabulary.Execution.Setup.a M S r))).toFG := by
    rw [hs0, facts.nd.store_with_cache_get_fg_root, hs0X,
      facts.dt.update_confirmation_with_toHealing_fg_root _ _ _ _ _ X hX]
  have hRQ : Block.Preceq R Q := by
    rw [hRroot, ← hrootEq]
    exact hrootQ
  have hTR : Block.Preceq T R := by
    rw [hRlive]
    exact facts.gr.deepest_clear_Preceq hclear
  have hRT : Block.Preceq R T :=
    preceq_trans_Preceq hRQ (preceq_trans_Preceq hQA' hAT)
  refine ⟨ModelProperties.Preceq_antisymm hTR hRT, ?_⟩
  exact ModelProperties.Preceq_antisymm (preceq_trans_Preceq hTR hRQ)
    (preceq_trans_Preceq hQA' hAT)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedOutageEntry

/-- If the phase window holds for the set along `W`, the round-`r` voters inside `X` outweigh the
    validators outside `X` and the stale historical voters of `r + 1`, `X` is inside
    `Hs (domain (r + 1) p)`, and the grade test of `B` on the store of `w` in
    `W (strictEventIndex rho (domain (r + 1) p))` can return `true`, then some round-`r` voter `u`
    of the set has `B` an ancestor of every block its round-`r` action can select. -/
theorem relativeGrade_has_roundCarrierOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {r : Round} {p : Phase}
    (hwindow : Restated.RelativeCarrierWindowAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs r p)
    (hmajority : Restated.GradeFormingMajorityOn M S rho W Hs X (r + 1))
    (hX : X ⊆ Hs (M.domain S.E S.hc (r + 1) p))
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc (r + 1) p)) {B : Block V}
    (hgrade : M.gradeBool S.E
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core.F
      S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
      (M.late S.E S.hc (r + 1) p) B ⇢ true) :
    ∃ u ∈ Restated.honestRoundVotersOn M S rho W Hs r,
      ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r,
        let gc := M.gradeContract nr.cache
        let st := M.toHealing nr.st.core
        let kk := M.round_of S.hc st.s
        ∀ A2, M.grade2_block_with gc S.E S.hc st kk ⇢ A2 →
        ∀ Bk, M.get_sg_vote_with gc S.E S.hc st kk A2 ⇢ Bk →
        Block.Preceq B Bk := by
  have hW := hf.onePath
  have hnmem := mem_stateBeforeTime_path₄₈ S rho hf.sorted W hW (M.domain S.E S.hc (r + 1) p)
  let n := W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w
  let gv := (M.gradeView (M.toHealing n.st.core))
  let F := n.st.core.F
  let ea := M.early S.E S.hc (r + 1) p
  let la := M.late S.E S.hc (r + 1) p
  let voters := Restated.honestRoundVotersOn M S rho W Hs r
  let bad := (Finset.univ \ X) ∪ Restated.staleHistoricalVotersOn M S rho W Hs (r + 1)
  choose pos hpos using fun u => facts.gr.positive_nonempty gv F S.hc.η_SG (r + 1) ea la u B
  choose opp hopp using fun u => facts.gr.opposing_nonempty gv F S.hc.η_SG (r + 1) ea la u B
  by_contra hnone
  have hwit : ∀ u ∈ voters,
      ∃ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r,
      ∃ A2, M.grade2_block_with (M.gradeContract nr.cache) S.E S.hc (M.toHealing nr.st.core)
          (M.round_of S.hc (M.toHealing nr.st.core).s) ⇢ A2 ∧
      ∃ Bk, M.get_sg_vote_with (M.gradeContract nr.cache) S.E S.hc (M.toHealing nr.st.core)
          (M.round_of S.hc (M.toHealing nr.st.core).s) A2 ⇢ Bk ∧
      ¬ Block.Preceq B Bk := by
    intro u hu
    have h1 : ¬ ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r,
        ∀ A2, M.grade2_block_with (M.gradeContract nr.cache) S.E S.hc (M.toHealing nr.st.core)
          (M.round_of S.hc (M.toHealing nr.st.core).s) ⇢ A2 →
        ∀ Bk, M.get_sg_vote_with (M.gradeContract nr.cache) S.E S.hc (M.toHealing nr.st.core)
          (M.round_of S.hc (M.toHealing nr.st.core).s) A2 ⇢ Bk →
        Block.Preceq B Bk := fun h => hnone ⟨u, hu, h⟩
    simp only [not_forall] at h1
    obtain ⟨nr, hnr, A2, hA2, Bk, hBk, hnot⟩ := h1
    exact ⟨nr, hnr, A2, hA2, Bk, hBk, hnot⟩
  have hcut : ea ≤ la := facts.gr.q10_early_le_late S (r + 1) p
  have horder : M.early S.E S.hc (r + 1) p ≤ M.domain S.E S.hc (r + 1) p := by
    have h := facts.gr.early_add_two_delta_le_domain S (r + 1) p
    linarith [S.E.Δ_pos]
  have hvotersOpp : voters ∩ X ⊆ Finset.univ.filter fun u => opp u = true := by
    intro u huVX
    have hu : u ∈ voters := (Finset.mem_inter.mp huVX).1
    have huEarly : u ∈ Hs (M.early S.E S.hc (r + 1) p) :=
      hHs _ _ horder (hX (Finset.mem_inter.mp huVX).2)
    obtain ⟨nr, hnr, A2, hA2, Bk, hBk, hnot⟩ := hwit u hu
    obtain ⟨I, hI⟩ := facts.gr.interpretedInputs_nonempty gv F S.hc.η_SG (r + 1) ea u
    obtain ⟨y, hy, hyround, hyconfirmed, hyfind⟩ :=
      hwindow w hw u hu huEarly nr hnr A2 hA2 Bk hBk I hI
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ u, ?_⟩
    obtain ⟨Rl, hRl⟩ := facts.gr.readyView_nonempty gv F S.hc.η_SG (r + 1) la u
    obtain ⟨Re, hRe⟩ := facts.gr.readyView_nonempty gv F S.hc.η_SG (r + 1) ea u
    obtain ⟨Il, hIl⟩ := facts.gr.interpretedInputs_nonempty gv F S.hc.η_SG (r + 1) la u
    obtain ⟨b, hb⟩ := facts.gr.head_covers_nonempty gv.T B (M.token y).key
    refine facts.gr.opposing_of_late_not_covers gv F S.hc.η_SG (r + 1) ea la u B
      (x := M.token y) Rl hRl ?_ Re hRe ?_ b hb ?_ (opp u) (hopp u)
    · exact (facts.gr.mem_readyView_iff Rl hRl Il hIl).mpr
        ⟨y, facts.gr.q10_interpreted_cut gv F S.hc.η_SG (r + 1) hcut u I hI Il hIl hy, rfl⟩
    · intro x hx
      obtain ⟨Ie, hIe⟩ := facts.gr.interpretedInputs_nonempty gv F S.hc.η_SG (r + 1) ea u
      obtain ⟨z, hz, rfl⟩ := (facts.gr.mem_readyView_iff Re hRe Ie hIe).mp hx
      obtain ⟨Rz, hRz⟩ := facts.gr.rawInputs_nonempty gv S.hc.η_SG (r + 1) ea u
      obtain ⟨bz, hbz⟩ := facts.gr.bodyReady_nonempty gv F ea z
      have hzraw := ((facts.gr.mem_interpretedInputs_iff Ie hIe Rz hRz bz hbz).mp hz).1
      obtain ⟨⟨k, hk, hzk⟩, -, -⟩ := facts.gr.rawInputs_mem_window _ _ _ _ _ Rz hRz hzraw
      obtain ⟨c, hcround, hcproj, -⟩ :=
        Restated.pool_token_rowOn facts S rho Hs Xb hf (M.domain S.E S.hc (r + 1) p) w _ hnmem hzk
      have hzround : z.round = k := by
        rw [← hcproj, ← hcround, facts.sto.sgVote_round_eq_round, namedAttestation_erase_round]
      have hwin : z.round ∈ M.latest_window S.hc.η_SG (r + 1) := by
        rw [hzround]
        exact hk
      have hzupper : z.round ≤ r :=
        Nat.le_of_lt_succ (by
          simpa only [Nat.add_comm] using (facts.fc.window_bounds hwin).2)
      rw [facts.gr.token_round, facts.gr.token_round, hyround]
      exact hzupper
    · intro hcover
      rw [facts.gr.token_key, hyconfirmed] at hb
      have hyfind' : Block.find? gv.T Bk.root = some Bk := by
        rw [facts.gr.Sts_gradeView_T]
        exact hyfind
      obtain ⟨Hd, hHd, hBHd⟩ := facts.gr.exists_find_of_head_covers b hb hcover
      rw [hyfind'] at hHd
      obtain rfl := Option.some.inj hHd
      exact hnot hBHd
  have hpositiveBad : (Finset.univ.filter fun u => pos u = true) ⊆ bad := by
    intro u hu
    have huPos : pos u = true := (Finset.mem_filter.mp hu).2
    by_cases huX : u ∈ X
    · refine Finset.mem_union_right _ ?_
      have huCut : u ∈ Hs (M.domain S.E S.hc (r + 1) p) := hX huX
      have huNotVoter : u ∉ voters := by
        intro huVoter
        have huOpp : opp u = true := (Finset.mem_filter.mp
          (hvotersOpp (Finset.mem_inter.mpr ⟨huVoter, huX⟩))).2
        rw [facts.gr.opposing_false_of_positive gv F S.hc.η_SG (r + 1) ea la u B hcut (pos u)
          (hpos u) huPos (opp u) (hopp u)] at huOpp
        cases huOpp
      obtain ⟨Re, hRe⟩ := facts.gr.readyView_nonempty gv F S.hc.η_SG (r + 1) ea u
      obtain ⟨Rl, hRl⟩ := facts.gr.readyView_nonempty gv F S.hc.η_SG (r + 1) la u
      obtain ⟨Wv, hWv⟩ := facts.gr.rawView_nonempty gv S.hc.η_SG (r + 1) la u
      choose cov hcov using fun k => facts.gr.head_covers_nonempty gv.T B k
      obtain ⟨x, hx, -⟩ := facts.gr.conditions_of_positive gv F S.hc.η_SG (r + 1) ea la u B (pos u)
        (hpos u) huPos Re hRe Rl hRl Wv hWv cov hcov
      obtain ⟨Ie, hIe⟩ := facts.gr.interpretedInputs_nonempty gv F S.hc.η_SG (r + 1) ea u
      obtain ⟨z, hz, rfl⟩ := (facts.gr.mem_readyView_iff Re hRe Ie hIe).mp hx
      obtain ⟨Rz, hRz⟩ := facts.gr.rawInputs_nonempty gv S.hc.η_SG (r + 1) ea u
      obtain ⟨bz, hbz⟩ := facts.gr.bodyReady_nonempty gv F ea z
      have hzraw := ((facts.gr.mem_interpretedInputs_iff Ie hIe Rz hRz bz hbz).mp hz).1
      obtain ⟨a, hval, haround, -, hlatest, hacut, hemit⟩ :=
        Restated.rawInputs_traceOn facts S rho Hs Xb hf hHs (M.domain S.E S.hc (r + 1) p)
          (M.early S.E S.hc (r + 1) p) w S.hc.η_SG (r + 1) u huCut Rz hRz hzraw
      have huAction : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S z.round)) := by
        rw [← haround]
        exact hHs _ _ hacut.le huCut
      have hzVoter : u ∈ Restated.honestRoundVotersOn M S rho W Hs z.round :=
        (Restated.honestRoundVoters_iffOn facts S rho W hW Hs u z.round).mpr
          ⟨huAction, a, hval, haround, by simpa only [haround] using hemit⟩
      have hnotPrevious : u ∉ Restated.honestRoundVotersOn M S rho W Hs (r + 1 - 1) := by
        simpa only [Nat.add_sub_cancel, voters] using huNotVoter
      exact Restated.stale_of_eligible_voteOn facts S rho W Hs hlatest hzVoter hnotPrevious
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huX⟩)
  replace hgrade : S.E.electorate.weightOf (Finset.univ.filter fun u => opp u = true) <
      S.E.electorate.weightOf (Finset.univ.filter fun u => pos u = true) := by
    by_contra hle
    have hfalse := facts.gr.gradeBool_eq_false_of_weight_le S.E gv F S.hc.η_SG (r + 1) ea la B
      pos hpos opp hopp (not_lt.mp hle) true hgrade
    cases hfalse
  have hVotersWeight := S.E.electorate.weightOf_mono hvotersOpp
  have hPositiveWeight := S.E.electorate.weightOf_mono hpositiveBad
  change S.E.electorate.weightOf bad <
    S.E.electorate.weightOf (voters ∩ X) at hmajority
  omega

end

/-! ## Further theorems along the path of the bundle -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- If index `first` is where the maximum `h_max` over `X` first reaches `H + 1` along the path `W`,
    then `first` opens a window at height `H` along `W`. -/
theorem FirstHeightProgressAtOn.toWindow {S : Setup V} {rho : Record.Run V} {W : Nat → V → M.N}
    {X : Finset V} {H : Height} {first : Nat}
    (h : Restated.FirstHeightProgressAtOn M S rho W X H first) :
    Restated.HeightWindowAtOn M S rho W X H first :=
  ⟨h.positive, h.before⟩

end

end DecoupledConsensusModel.Sts.Restated
