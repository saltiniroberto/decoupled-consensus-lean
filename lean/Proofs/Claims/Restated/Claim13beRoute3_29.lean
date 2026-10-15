import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_OutageInputs
import Proofs.Claims.Restated.Vocabulary_Execution_ReceiptCallsBase
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Admission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_SGArrival
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_ReceiptCallsF1
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_29

/-!
# Row stamps, acceptance rounds and held projections

The opening bounds of a round's window, the condition `Data` on a store's clock and row stamps and
its truth around every event, the opening of an accepted attestation's round, and the projections of
held rows read at a later time. Stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedRawRelay
set_option autoImplicit false
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage DecoupledConsensusModel.Protocol
local macro "rr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.RawRelay)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedRawRelay ++ n.getId)))

/-- For `q` in the latest `η_SG` rounds before `r`, `opening (r - η_SG) ≤ opening q` and
    `opening q + 8 * Δ ≤ opening r`. -/
theorem Vocabulary.Proofs.NamedRawRelay.opening_bounds_of_window (facts : Record.Facts M) (S : Setup V) {r q : Round}
    (hq : q ∈ M.latest_window S.hc.η_SG r) :
    M.opening S.E S.hc (r - S.hc.η_SG) ≤ M.opening S.E S.hc q ∧
      M.opening S.E S.hc q + 8 * S.E.Δ ≤ M.opening S.E S.hc r := by
  have hw := facts.fc.window_bounds hq
  exact ⟨facts.gr.NamedOutageClosure_opening_mono S hw.1, facts.gr.opening_add_le_of_lt S hw.2⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedRawRelay
set_option autoImplicit false
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage DecoupledConsensusModel.Protocol
local macro "rr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.RawRelay)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedRawRelay ++ n.getId)))

/-- The clock of `st` is at or before `bound`, and every named attestation held in `st`'s rows of a
    round `k` has round `k` and a receipt stamp of its projection at or before `bound`. -/
def Vocabulary.Proofs.NamedRawRelay.Data (M : Record.Model V) (bound : Time) (st : M.NS) : Prop :=
  st.core.t ≤ bound ∧ ∀ k (a : NamedAttestation V), a ∈ st.sg_rows k →
    a.round = k ∧ ∃ stamp : Time, stamp ≤ bound ∧
      st.core.timestamp_sg_vote (M.sgVote a.erase) = some (stamp : Stamp)

/-- If `0 ≤ bound` and every event of `rho` before the `i`-th is at or before `bound`, then in every
    world before the `i`-th event `reader`'s store satisfies `Data` at `bound`. -/
private theorem prefix_data_record (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (bound : Time) (hzero : 0 ≤ bound) (reader : V) :
    ∀ i : Nat, (∀ j e, j < i → rho.events[j]? = some e → e.time ≤ bound) →
      ∀ w ∈ Record.stateBeforeOf M S rho i,
        Restated.Vocabulary.Proofs.NamedRawRelay.Data M bound (w reader).st := by
  intro i
  induction i with
  | zero =>
    intro _ w hw
    have hw0 : w = fun v => M.initial S v := hw
    subst hw0
    show Restated.Vocabulary.Proofs.NamedRawRelay.Data M bound (M.initial S reader).st
    rw [facts.nd.initial_st]
    refine ⟨by rw [facts.hd.initial_core_t]; exact hzero, ?_⟩
    intro k a ha
    rw [facts.hd.initial_sg_rows] at ha
    simp only [List.not_mem_nil] at ha
  | succ i ih =>
    intro hbefore w hw
    rw [Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_succ facts S rho i, Set.bind_def] at hw
    obtain ⟨w₀, hw₀, hw'⟩ := Set.mem_iUnion₂.mp hw
    have hd := ih (fun j e hj he => hbefore j e (Nat.lt_succ_of_lt hj) he) w₀ hw₀
    have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i reader
      w₀ hw₀).1.1.1
    cases he : rho.events[i]? with
    | none =>
      rw [he] at hw'
      have hw0 : w = w₀ := hw'
      rw [hw0]
      exact hd
    | some e =>
      rw [he] at hw'
      simp only [Option.toList_some, List.foldlM_cons, List.foldlM_nil, Set.bind_def] at hw'
      obtain ⟨w', hstep, hw''⟩ := Set.mem_iUnion₂.mp hw'
      have hww : w = w' := hw''
      subst hww
      have ht := hbefore i e (Nat.lt_succ_self i) he
      by_cases hv : reader = e.node
      · cases e with
        | wake v t =>
          have hw : w = Function.update w₀ v (M.wake (w₀ v)) := hstep
          have hst : (w reader).st = (w₀ reader).st := by
            rw [hw]
            by_cases hrv : reader = v
            · subst hrv
              rw [Function.update_self, (facts.nd.wake_st_record _).1]
            · rw [Function.update_of_ne hrv]
          rw [hst]
          exact hd
        | tick v t =>
          change reader = v at hv
          subst hv
          rcases Restated.Vocabulary.Proofs.NamedRuntime.step_tick facts S w₀ reader t w hstep with
            ⟨out, hout, hwv⟩ | ⟨-, hwv⟩
          · rw [hwv]
            exact facts.nd.rawRelay_tick_outcome_data S reader (w₀ reader) t out hout bound ht
              hcoh hd
          · rw [hwv]
            exact hd
        | deliver v o t =>
          change reader = v at hv
          subst hv
          rcases Restated.Vocabulary.Proofs.NamedRuntime.step_deliver facts S w₀ reader o t w hstep with
            hproc | ⟨-, hwv⟩
          · rw [facts.nd.process_st S (w₀ reader) o (w reader) hproc]
            have h := facts.nd.rawRelay_process_data S bound (w₀ reader).st o hcoh hd
            simp only [Restated.Vocabulary.Proofs.NamedRawRelay.Data,
              facts.nd.make_grades_compatible_with_finalized_core_t,
              facts.nd.make_grades_compatible_with_finalized_sg_rows,
              facts.nd.make_grades_compatible_with_finalized_core_timestamp_sg_vote]
            exact h
          · rw [hwv]
            exact hd
      · rw [Restated.Vocabulary.Proofs.NamedRuntime.step_other facts S w₀ e reader hv w hstep]
        exact hd

/-- In a run sorted by key and inside its horizon, every store before and right after event `i` has
    its clock and every held row's stamp at or before that event's time. -/
theorem Vocabulary.Proofs.NamedRawRelay.data_at_event_of_fields (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (hin : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon)
    {i : Nat} {e : Record.Event V} (he : rho.events[i]? = some e) (reader : V) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i, ∀ w₂ ∈ Record.stateBeforeOf M S rho (i + 1),
    Restated.Vocabulary.Proofs.NamedRawRelay.Data M e.time (w₁ reader).st ∧
      Restated.Vocabulary.Proofs.NamedRawRelay.Data M e.time (w₂ reader).st := by
  intro w₁ hw₁ w₂ hw₂
  have hn := (hin _ (List.mem_of_getElem? he)).1
  constructor
  · exact prefix_data_record facts S rho e.time hn reader i
      (fun j f hj hf => Restated.event_time_le rho hsorted hf he hj.le) w₁ hw₁
  · exact prefix_data_record facts S rho e.time hn reader (i + 1)
      (fun j f hj hf => Restated.event_time_le rho hsorted hf he (Nat.le_of_lt_succ hj)) w₂ hw₂

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedRawRelay
set_option autoImplicit false
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage DecoupledConsensusModel.Protocol
local macro "rr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.RawRelay)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedRawRelay ++ n.getId)))

/-- When the `i`-th event of `rho` is a wake of `v`, `v`'s store in every world that event leads to
    from `w₁` is `v`'s store in `w₁`. -/
private theorem stateBefore_wake_st (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
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

/-- For every path `W` of `rho`, in every world `W i` the slot of `v`'s store is the slot of its
    clock. -/
private theorem slot_clock_along (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V) :
    ∀ i : Nat, (W i v).st.core.s = S.E.slotOf (W i v).st.core.t := by
  intro i
  induction i with
  | zero =>
    have h0 : W 0 = fun v => M.initial S v := (hW 0).1
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
          rw [stateBefore_wake_st facts S rho hev (W n) (W (n + 1)) hstep]
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

/-- For every path `W` of `rho`, if `source` accepts the attestation `a` at the `i`-th event at
    `ta`, read along `W`, then that event is `source`'s tick at `ta` and `a`'s round is at most the
    round of `ta`'s slot, or it is a delivery to `source` at `ta` and `a`'s round is at most the
    round of the slot of `source`'s store in `W i`. -/
private theorem accepted_round_floor_cases_along (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {i : Nat} {source : V} {a : NamedAttestation V} {ta : Time}
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i source (.attest a) ta) :
    (rho.events[i]? = some (.tick source ta) ∧ a.round ≤ M.round_of S.hc (S.E.slotOf ta)) ∨
    (∃ o : NamedObject V, rho.events[i]? = some (.deliver source o ta) ∧
      a.round ≤ M.round_of S.hc (W i source).st.core.s) := by
  have hpre : a ∉ (W i source).st.sg_rows a.round := of_decide_eq_false hacc.2.1
  have hpost : a ∈ (W (i + 1) source).st.sg_rows a.round := of_decide_eq_true hacc.2.2
  obtain ⟨hWi, hstep⟩ := hW i
  obtain ⟨e, he, hnode, htime⟩ := hacc.1.2
  cases e with
  | wake v t =>
    change v = source at hnode
    subst v
    rw [stateBefore_wake_st facts S rho he (W i) (W (i + 1)) hstep] at hpost
    exact absurd hpost hpre
  | tick v t =>
    change v = source at hnode
    change t = ta at htime
    subst v
    subst t
    refine Or.inl ⟨he, ?_⟩
    rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_tick facts S rho he (W i) hWi
        (W (i + 1)) hstep with ⟨out, hout, hw⟩ | ⟨-, hw⟩
    · rw [hw] at hpost
      rcases facts.nd.tick_new_full_row_origin S source (W i source) ta out hout a hpre hpost with
        hmem | ⟨B, _, hpre0, hpost0⟩
      · have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W source (.attest a) ta :=
          ⟨i, he, out, hout, hw, hmem⟩
        obtain ⟨-, -, -, -, -, -, -, -, ht, -⟩ :=
          Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_stages facts S rho W hW hemit
        rw [ht]
        exact (facts.sch.round_of_slotOf_a S a.round).ge
      · have h := facts.hd.rawRelay_block_new_round_floor S _ B a hpre0 hpost0
        rwa [facts.hd.ModelProperties_setClock_core_s] at h
    · rw [hw] at hpost
      exact absurd hpost hpre
  | deliver v o t =>
    change v = source at hnode
    change t = ta at htime
    subst v
    subst t
    refine Or.inr ⟨o, he, ?_⟩
    rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho he (W i) hWi
        (W (i + 1)) hstep with hproc | ⟨-, hw⟩
    · rw [facts.nd.process_st S (W i source) o (W (i + 1) source) hproc,
        facts.nd.make_grades_compatible_with_finalized_sg_rows] at hpost
      cases o with
      | block B =>
        rw [facts.nd.process_block] at hpost
        exact facts.hd.rawRelay_block_new_round_floor S _ B a hpre hpost
      | gfVote u =>
        rw [facts.nd.process_gfVote, facts.hd.ns_with_core_sg_rows S.E _ u _ rfl] at hpost
        exact absurd hpost hpre
      | attest incoming =>
        rw [facts.nd.process_attest] at hpost
        exact facts.hd.rawRelay_new_row_round_floor S.hc _ incoming a hpre hpost
    · rw [hw] at hpost
      exact absurd hpost hpre

/-- In a run sorted by key and inside its horizon, for every path `W` of the run, an attestation
    accepted at `ta`, read along `W`, has its round's opening at or before `ta`. -/
theorem Vocabulary.Proofs.NamedRawRelay.source_acceptance_opening_le_of_fields (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (hin : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon)
    {i : Nat} {source : V} {a : NamedAttestation V} {ta : Time}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i source (.attest a) ta) :
    M.opening S.E S.hc a.round ≤ ta := by
  rcases accepted_round_floor_cases_along facts S rho W hW hacc with ⟨he, hf⟩ | ⟨o, he, hf⟩
  · have ht0 : 0 ≤ ta := (hin _ (List.mem_of_getElem? he)).1
    rw [facts.gr.opening_eq_proposal_time]
    exact (facts.sch.proposal_time_mono S.E (facts.gr.opening_slot_le_of_le_round_of S.hc hf)).trans
      (facts.sch.proposal_time_slotOf_le S.E ht0)
  · have hWi := (hW i).1
    have hclock0 : 0 ≤ (W i source).st.core.t := by
      have h := Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_clock_mono facts S rho hsorted
        (fun e he => (hin e he).1) source (Nat.zero_le i) (fun v => M.initial S v) (Set.mem_singleton _)
        (W i) (by rw [List.drop_zero, Nat.sub_zero]; exact hWi)
      refine le_trans (le_of_eq ?_) h
      show (0 : Time) = (M.initial S source).st.core.t
      rw [facts.nd.initial_st, facts.hd.initial_core_t]
    have hup := Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_clock_le_event facts S rho hsorted he
      (hin _ (List.mem_of_getElem? he)).1 source (W i) hWi
    have hslot := facts.gr.opening_slot_le_of_le_round_of S.hc hf
    rw [slot_clock_along facts S rho W hW source i] at hslot
    rw [facts.gr.opening_eq_proposal_time]
    exact (facts.sch.proposal_time_mono S.E hslot).trans
      ((facts.sch.proposal_time_slotOf_le S.E hclock0).trans hup)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedRawRelay
set_option autoImplicit false
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage DecoupledConsensusModel.Protocol
local macro "rr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.RawRelay)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedRawRelay ++ n.getId)))

/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_reach {S : Setup V} {rho : Record.Run V}
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

/-- In a run sorted by key and inside its horizon, for every path `W` of the run, a row of `r`'s
    window held by the reader in `W (j + 1)`, right after an event `j` before the cutoff `c`, gives
    its projection in every outcome of the raw inputs for its signer of the reader's store in the
    world of `W` reached by the events before `d ≥ c`, with cutoff `c`. -/
theorem Vocabulary.Proofs.NamedRawRelay.held_projection_raw_after_event_of_fields (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (hin : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon)
    (r : Round) (reader sender : V) (c d : Time) (hcd : c ≤ d)
    {j : Nat} {e : Record.Event V} (he : rho.events[j]? = some e)
    (ht : e.time < c) (b : NamedAttestation V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hb : b ∈ (W (j + 1) reader).st.sg_rows b.round)
    (hwindow : b.round ∈ M.latest_window S.hc.η_SG r) (hval : b.val_index = sender) :
    ∀ X, M.rawInputs
      (M.gradeView (M.toHealing
        (W (rho.events.filter (fun e => decide (e.time < d))).length reader).st.core))
      S.hc.η_SG r c sender ⇢ X → M.sgVote b.erase ∈ X := by
  let n := W (rho.events.filter (fun e => decide (e.time < d))).length reader
  have hpostData := (Restated.Vocabulary.Proofs.NamedRawRelay.data_at_event_of_fields facts S rho hsorted
    hin he reader (W j) (hW j).1 (W (j + 1)) (hW (j + 1)).1).2
  obtain ⟨_, stamp, hstampBound, hstamp⟩ := hpostData.2 b.round b hb
  have hcut : e.time < d := lt_of_lt_of_le ht hcd
  have hindex := Restated.index_succ_le_strict_filter_length rho hsorted d he hcut
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hindex
  have hreach : W (rho.events.filter (fun e => decide (e.time < d))).length ∈
      ((rho.events.drop (j + 1)).take
        ((rho.events.filter (fun e => decide (e.time < d))).length - (j + 1))).foldlM
        (Record.worldStepOf M S) (W (j + 1)) := by
    rw [hk, Nat.add_sub_cancel_left]
    exact onePath_reach W hW (j + 1) k
  obtain ⟨hretained, hstampRetained⟩ :=
    Restated.Vocabulary.Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono facts S rho reader hindex
      (W (j + 1)) (hW (j + 1)).1 hb _ hreach
  have hheld : b ∈ n.st.sg_rows b.round := hretained
  have hreceipt : n.st.core.timestamp_sg_vote (M.sgVote b.erase) =
      some (stamp : Stamp) := hstampRetained.trans hstamp
  have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho _ reader
    _ (hW (rho.events.filter (fun e => decide (e.time < d))).length).1).1.1.1
  have hpool := facts.sto.pool_view_mem n.st hcoh.2.2.2.1 b hheld
  have hsg : M.sgVote b.erase ∈ (M.gradeView (M.toHealing n.st.core)).sg_votes b.round := by
    rw [facts.gr.gradeView_sg_votes]
    exact Finset.mem_image_of_mem M.sgVote hpool
  have hts : (M.gradeView (M.toHealing n.st.core)).timestamp_sg_vote (M.sgVote b.erase) =
      some (stamp : Stamp) := by
    rw [facts.gr.gradeView_timestamp_sg_vote]
    exact hreceipt
  exact facts.gr.mem_rawInputs_of_stamp _ _ _ b.round _ _ hwindow hsg
    ((facts.sto.sgVote_val b).trans hval) hts (hstampBound.trans_lt ht)

end

end DecoupledConsensusModel.Sts.Restated
