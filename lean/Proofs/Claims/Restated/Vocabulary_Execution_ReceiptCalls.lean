import Proofs.Vocabulary.Execution.ReceiptCalls
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_ReceiptCallsBase
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Vocabulary.Protocol.Grades.NamedDuties
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Admission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_ReceiptCallsGF
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_ReceiptCallsF1
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Record.Wiring

/-!
# An object newly processed at an event was accepted there

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, along a path `W`
of a run: when a block, a Goldfish vote or a row becomes processed in a validator's store at an
event, the validator accepts it at that event.
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
open DecoupledConsensusModel.Proofs.NamedReceiptCalls
open Execution
open Execution.NamedReceiptCalls
open NamedReceiptCallsBase

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

/-- For every path `W` of `rho`, if the block `B` is not among `v`'s bodies in `W i` and is among
    them in `W (i + 1)`, then `v` accepts `B` at the `i`-th event, at some time `t`, read along `W`. -/
theorem Vocabulary.Proofs.NamedReceiptCalls.new_block_accepts (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V)
    (B : NamedBlock V) (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hpre : B ∉ (W i v).st.bodies)
    (hpost : B ∈ (W (i + 1) v).st.bodies) :
    ∃ t : Time, Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (.block B) t := by
  obtain ⟨hWi, hstep⟩ := hW i
  have hpre' : Restated.Vocabulary.Execution.Object.processed M (W i v).st (.block B) = false :=
    decide_eq_false hpre
  have hpost' : Restated.Vocabulary.Execution.Object.processed M (W (i + 1) v).st (.block B) = true :=
    decide_eq_true hpost
  cases he : rho.events[i]? with
  | none =>
    have hlen : rho.events.length ≤ i := List.getElem?_eq_none_iff.mp he
    rw [List.drop_eq_nil_of_le hlen, List.take_nil, List.foldlM_nil] at hstep
    have hsame : W (i + 1) = W i := hstep
    rw [hsame] at hpost
    exact absurd hpost hpre
  | some e =>
    have hv : e.node = v := by
      by_contra hne
      have := Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_other facts S rho he v (Ne.symm hne)
        (W i) hWi (W (i + 1)) hstep
      rw [this] at hpost
      exact hpre hpost
    have hcall : Restated.Vocabulary.Execution.NamedRun.actualHandlesAtIndex M S rho W i v (.block B) := by
      cases e with
      | wake u t =>
        change u = v at hv
        subst u
        rw [stateBefore_wake_st facts S rho he (W i) (W (i + 1)) hstep] at hpost
        exact absurd hpost hpre
      | tick u t =>
        change u = v at hv
        subst u
        rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_tick facts S rho he (W i) hWi
            (W (i + 1)) hstep with ⟨out, hout, hw⟩ | ⟨-, hw⟩
        · refine Or.inl ⟨t, he, out, hout, hw, ?_⟩
          have hB := hpost
          rw [hw] at hB
          exact facts.nd.tick_new_body_origin S v (W i v) t out hout B hpre hB
        · rw [hw] at hpost
          exact absurd hpost hpre
      | deliver u o t =>
        change u = v at hv
        subst u
        have hB := hpost
        rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho he (W i) hWi
            (W (i + 1)) hstep with hproc | ⟨-, hw₂v⟩
        · rw [facts.nd.process_st S (W i v) o (W (i + 1) v) hproc,
            facts.nd.make_grades_compatible_with_finalized_bodies] at hB
          cases o with
          | block C =>
            rw [facts.nd.process_block] at hB
            obtain ⟨hBC, -⟩ := facts.hd.on_block_with_new_body .alsoCarried S (W i v).st C B hpre hB
            subst hBC
            exact Or.inr ⟨t, he⟩
          | gfVote u =>
            rw [facts.nd.process_gfVote, facts.hd.ns_with_core_bodies S.E _ u _ rfl] at hB
            exact absurd hB hpre
          | attest a =>
            rw [facts.nd.process_attest, facts.hd.NamedAdmission_admit_row_bodies] at hB
            exact absurd hB hpre
        · rw [hw₂v] at hB
          exact absurd hB hpre
    exact ⟨e.time, ⟨hcall, e, he, hv, rfl⟩, hpre', hpost'⟩

/-- For every path `W` of `rho`, when the `i`-th event of `rho` is `e`, an event of `v`, and the
    Goldfish vote `u` is not among the Goldfish votes of `v`'s store in `W i` but is among those of
    `v`'s store in `W (i + 1)`, then `v` handles `u` at the `i`-th event, read along `W`. -/
private theorem gf_handled_along (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (i : Nat) (v : V) (u : GoldfishVote V) (e : Record.Event V)
    (he : rho.events[i]? = some e) (hv : e.node = v)
    (hpre : u ∉ (W i v).st.core.pool u.slot)
    (hpost : u ∈ (W (i + 1) v).st.core.pool u.slot) :
    Restated.Vocabulary.Execution.NamedRun.actualHandlesAtIndex M S rho W i v (.gfVote u) := by
  obtain ⟨hWi, hstep⟩ := hW i
  cases e with
  | wake x t =>
    change x = v at hv
    subst x
    rw [stateBefore_wake_st facts S rho he (W i) (W (i + 1)) hstep] at hpost
    exact absurd hpost hpre
  | tick x t =>
    change x = v at hv
    subst x
    rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_tick facts S rho he (W i) hWi
        (W (i + 1)) hstep with ⟨out, hout, hw⟩ | ⟨-, hw⟩
    · rw [hw] at hpost
      rcases facts.nd.tick_new_vote_origin S v (W i v) t out hout u hpre hpost
        with hem | ⟨B, hB, hp, hq⟩
      · exact Or.inl (Or.inl ⟨t, he, out, hout, hw, hem⟩)
      · have hcall := Restated.Vocabulary.Proofs.NamedReceiptCallsBase.blockCallAt_self facts S rho he
          W hW ⟨out, hout, hw, hB⟩
        obtain ⟨j, hj⟩ := Restated.Vocabulary.Proofs.NamedReceiptCallsGF.block_with_new_vote_origin facts
          S rho i v B _ W hW hcall u hp hq
        exact Or.inr ⟨B, j, _, hj⟩
    · rw [hw] at hpost
      exact absurd hpost hpre
  | deliver x o t =>
    change x = v at hv
    subst x
    rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho he (W i) hWi
        (W (i + 1)) hstep with hproc | ⟨-, hw⟩
    · rw [facts.nd.process_st S (W i v) o (W (i + 1) v) hproc,
        facts.nd.make_grades_compatible_with_finalized_core_pool] at hpost
      cases o with
      | block B =>
        rw [facts.nd.process_block] at hpost
        obtain ⟨j, hj⟩ := Restated.Vocabulary.Proofs.NamedReceiptCallsGF.block_with_new_vote_origin facts
          S rho i v B _ W hW
          (Restated.Vocabulary.Proofs.NamedReceiptCallsBase.blockCallAt_delivery facts S rho he W hW)
          u hpre hpost
        exact Or.inr ⟨B, j, _, hj⟩
      | gfVote input =>
        rw [facts.nd.process_gfVote] at hpost
        have hpost' := (facts.sto.mem_pool_iff _ _ _).1 hpost
        rw [facts.hd.ns_with_core_core] at hpost'
        rcases facts.hd.mem_gf_votes_on_goldfish_vote_checked S.E (W i v).st.core input u.slot hpost'
          with hold | rfl
        · exact absurd ((facts.sto.mem_pool_iff _ _ _).2 hold) hpre
        · exact Or.inl (Or.inr ⟨t, he⟩)
      | attest a =>
        rw [facts.nd.process_attest] at hpost
        have hp : u ∈ (W i v).st.core.pool u.slot := by
          have h := (facts.sto.mem_pool_iff _ _ _).1 hpost
          rw [facts.hd.sameCore_gf_votes (facts.hd.NamedAdmission_admit_row_core S.hc (W i v).st a),
            facts.hd.on_sg_vote_gf_votes] at h
          exact (facts.sto.mem_pool_iff _ _ _).2 h
        exact absurd hp hpre
    · rw [hw] at hpost
      exact absurd hpost hpre

/-- For every path `W` of `rho`, when the `i`-th event of `rho` is `e`, an event of `v`, and the
    full row `a` is not in the rows of its round of `v`'s store in `W i` but is in those of `v`'s
    store in `W (i + 1)`, then `v` handles `a` at the `i`-th event, read along `W`. -/
private theorem row_handled_along (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (i : Nat) (v : V) (a : NamedAttestation V) (e : Record.Event V)
    (he : rho.events[i]? = some e) (hv : e.node = v)
    (hpre : a ∉ (W i v).st.sg_rows a.round)
    (hpost : a ∈ (W (i + 1) v).st.sg_rows a.round) :
    Restated.Vocabulary.Execution.NamedRun.actualHandlesAtIndex M S rho W i v (.attest a) := by
  obtain ⟨hWi, hstep⟩ := hW i
  cases e with
  | wake x t =>
    change x = v at hv
    subst x
    rw [stateBefore_wake_st facts S rho he (W i) (W (i + 1)) hstep] at hpost
    exact absurd hpost hpre
  | tick x t =>
    change x = v at hv
    subst x
    rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_tick facts S rho he (W i) hWi
        (W (i + 1)) hstep with ⟨out, hout, hw⟩ | ⟨-, hw⟩
    · rw [hw] at hpost
      rcases facts.nd.tick_new_full_row_origin S v (W i v) t out hout a hpre hpost
        with hem | ⟨B, hB, hp, hq⟩
      · exact Or.inl (Or.inl ⟨t, he, out, hout, hw, hem⟩)
      · rw [← facts.nd.process_block S] at hq
        have hcall := Restated.Vocabulary.Proofs.NamedReceiptCallsBase.blockCallAt_self facts S rho he
          W hW ⟨out, hout, hw, hB⟩
        obtain ⟨j, hj, _, _⟩ := Restated.Vocabulary.Proofs.NamedReceiptCallsF1.block_full_marker_origin
          facts S rho i v B _ a W hW hcall hp hq
        exact Or.inr ⟨B, j, _, hj⟩
    · rw [hw] at hpost
      exact absurd hpost hpre
  | deliver x o t =>
    change x = v at hv
    subst x
    exact (Restated.Vocabulary.Proofs.NamedReceiptCallsF1.delivered_row_accepts facts S rho i v o t a
      he W hW hpre hpost).1.1

/-- For every path `W` of `rho`, if `v`'s store in `W i` has not processed `o` and `v`'s store in
    `W (i + 1)` has, then `v` accepts `o` at the `i`-th event, at some time `t`, read along `W`. -/
theorem Vocabulary.Proofs.NamedReceiptCalls.new_marker_accepts (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V)
    (o : NamedObject V) (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hpre : Restated.Vocabulary.Execution.Object.processed M (W i v).st o = false)
    (hpost : Restated.Vocabulary.Execution.Object.processed M (W (i + 1) v).st o = true) :
    ∃ t : Time, Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v o t := by
  obtain ⟨hWi, hstep⟩ := hW i
  cases he : rho.events[i]? with
  | none =>
    have hlen : rho.events.length ≤ i := List.getElem?_eq_none_iff.mp he
    rw [List.drop_eq_nil_of_le hlen, List.take_nil, List.foldlM_nil] at hstep
    have hsame : W (i + 1) = W i := hstep
    rw [hsame, hpre] at hpost
    cases hpost
  | some e =>
    have hv : e.node = v := by
      by_contra hne
      have := Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_other facts S rho he v (Ne.symm hne)
        (W i) hWi (W (i + 1)) hstep
      rw [this, hpre] at hpost
      cases hpost
    have hcall : Restated.Vocabulary.Execution.NamedRun.actualHandlesAtIndex M S rho W i v o := by
      cases o with
      | block B =>
        obtain ⟨_, ⟨h, -⟩, -⟩ := Restated.Vocabulary.Proofs.NamedReceiptCalls.new_block_accepts facts
          S rho i v B W hW (of_decide_eq_false hpre) (of_decide_eq_true hpost)
        exact h
      | gfVote u =>
        exact gf_handled_along facts S rho W hW i v u e he hv
          (fun h => of_decide_eq_false hpre ((facts.sto.mem_pool_iff _ _ _).1 h))
          ((facts.sto.mem_pool_iff _ _ _).2 (of_decide_eq_true hpost))
      | attest a =>
        exact row_handled_along facts S rho W hW i v a e he hv
          (of_decide_eq_false hpre) (of_decide_eq_true hpost)
    exact ⟨e.time, ⟨hcall, e, he, hv, rfl⟩, hpre, hpost⟩

/-- For every path `W` of `rho`, if the full row `a` is not in the rows of its round of `v`'s store
    in `W i` and is in those of `v`'s store in `W (i + 1)`, then `v` accepts `a` at the `i`-th
    event, at some time `t`, read along `W`. -/
theorem Vocabulary.Proofs.NamedReceiptCalls.new_attestation_accepts (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V)
    (a : NamedAttestation V) (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hpre : a ∉ (W i v).st.sg_rows a.round)
    (hpost : a ∈ (W (i + 1) v).st.sg_rows a.round) :
    ∃ t : Time, Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (.attest a) t :=
  Restated.Vocabulary.Proofs.NamedReceiptCalls.new_marker_accepts facts S rho i v (.attest a) W hW
    (decide_eq_false hpre) (decide_eq_true hpost)

end

end DecoupledConsensusModel.Sts.Restated
