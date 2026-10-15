import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13b
import Proofs.Claims.Restated.Claim13beRoute3_25
import Proofs.Claims.Restated.HonestNeverSlashed
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_NamedNode
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25

/-!
# Completed frame phases, well-formed deliveries and emissions

A tick at a phase's domain instant completes that phase of the round's frame for later reads, every
delivery in the run built from an execution carries a well-formed payload, and an object attributed
to an honest validator was emitted by it earlier. Stated over a model `M : Record.Model V`.
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
open DecoupledConsensusModel.Proofs.HealingSurface
open Execution

omit [DecidableEq V] [Fintype V] in
/-- An event whose key is at most another's has a time at most the other's. -/
private theorem time_le_of_key_le₃₀ {e f : Record.Event V} (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event at a smaller index has a time at most the time of an event at a
    larger index. -/
private theorem time_le_of_index_le₃₀ (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {k i : Nat} {e f : Record.Event V} (hki : k < i)
    (hk : rho.events[k]? = some e) (hi : rho.events[i]? = some f) : e.time ≤ f.time := by
  obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hp := (List.pairwise_iff_getElem.mp hsorted) k i hkl hil hki
  rw [hke, hie] at hp
  exact time_le_of_key_le₃₀ hp

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, the events with a time before `t` are the first `strictEventIndex rho t`
    events. -/
private theorem strict_filter_eq_take₃₀ (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)) (t : Time) :
    rho.events.filter (fun e => decide (e.time < t)) = rho.events.take (strictEventIndex rho t) := by
  have hdown : ∀ e f : Record.Event V, e.key ≤ f.key →
      decide (f.time < t) = true → decide (e.time < t) = true := by
    intro e f hkey hf
    simp only [decide_eq_true_eq] at hf ⊢
    exact (time_le_of_key_le₃₀ hkey).trans_lt hf
  refine List.prefix_iff_eq_take.mp ?_
  rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise hdown _ hsorted]
  exact List.takeWhile_prefix _

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event at an index less than `strictEventIndex rho t` has a time
    before `t`. -/
private theorem time_lt_of_lt_strict₃₀ (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)) (t : Time)
    {j : Nat} {e : Record.Event V} (hj : j < strictEventIndex rho t)
    (hget : rho.events[j]? = some e) : e.time < t := by
  have hm : e ∈ rho.events.filter (fun x => decide (x.time < t)) := by
    rw [strict_filter_eq_take₃₀ rho hsorted t]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact hget)
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hm).2

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, if the `j`-th event has a time before `t`, then `j + 1` is at most
    `strictEventIndex rho t`. -/
private theorem succ_le_strict_of_time_lt₃₀ (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)) (t : Time)
    {j : Nat} {e : Record.Event V} (he : rho.events[j]? = some e) (ht : e.time < t) :
    j + 1 ≤ strictEventIndex rho t := by
  by_contra hcon
  have hlt : strictEventIndex rho t ≤ j := by omega
  have hge : t ≤ e.time := by
    have hf := Restated.filter_false_of_index_ge_sorted rho hsorted
      (fun x => decide (x.time < t)) (fun a b hab hb => by
        simp only [decide_eq_true_eq] at hb ⊢
        exact (time_le_of_key_le₃₀ hab).trans_lt hb) hlt he
    simpa using hf
  exact absurd ht (not_lt.mpr hge)

/-- If `t` is before the opening of round `r + 1`, the round of the slot of `t` is at most `r`. -/
private theorem round_le_of_lt_opening₃₀ (facts : Record.Facts M) (S : Setup V) {t : Time}
    {r : Round} (ht : t < M.opening S.E S.hc (r + 1)) : M.round_of S.hc (S.E.slotOf t) ≤ r := by
  by_contra hcon
  have hle : r + 1 ≤ M.round_of S.hc (S.E.slotOf t) := Nat.succ_le_of_lt (Nat.lt_of_not_le hcon)
  have hs := facts.gr.opening_slot_le_of_le_round_of S.hc hle
  by_cases h0 : (0 : Time) ≤ t
  · have h1 := facts.sch.proposal_time_slotOf_le S.E h0
    have h2 := facts.sch.proposal_time_mono S.E hs
    rw [facts.gr.opening_eq_proposal_time] at ht
    exact absurd (lt_of_le_of_lt (h2.trans h1) ht) (lt_irrefl _)
  · have hz : S.E.slotOf t = 0 :=
      Nat.le_zero.mp (le_trans (slotOf_mono_sts S (le_of_lt (not_le.mp h0)))
        (le_of_eq (Proofs.ModelProperties.slotOf_zero S.E)))
    rw [hz] at hle
    have h00 : M.round_of S.hc 0 = 0 := by
      have h := facts.gr.round_of_opening_slot_eq S.hc 0
      rwa [facts.gr.opening_slot_zero_mk] at h
    rw [h00] at hle
    exact absurd hle (Nat.not_succ_le_zero r)

/-- When the `n`-th event of `rho` is `u`'s wake at `t`, the one world it leads to from `w₀` is `w₀`
    with `u`'s node state replaced by its wake. -/
private theorem wake_step₃₀ (S : Setup V) (rho : Record.Run V) {n : Nat} {u : V} {t : Time}
    (he : rho.events[n]? = some (.wake u t)) (w₀ w₁ : V → M.N)
    (hstep : w₁ ∈ ((rho.events.drop n).take (n + 1 - n)).foldlM (Record.worldStepOf M S) w₀) :
    w₁ = Function.update w₀ u (M.wake (w₀ u)) := by
  have hl : (rho.events.drop n).take (n + 1 - n) = [.wake u t] := by
    rw [Nat.add_sub_cancel_left, List.take_one, List.head?_drop, he]
    rfl
  rw [hl, List.foldlM_cons, Set.bind_def] at hstep
  obtain ⟨w', hw', h2⟩ := Set.mem_iUnion₂.mp hstep
  obtain rfl := Set.mem_singleton_iff.mp h2
  exact hw'

/-- Along a path `W` of `rho`, the round of the grade cache of `v`'s node state in `W m` is `0`, or
    the round of the slot of some earlier tick of `v`. -/
private theorem cache_round_witness₃₀ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V) :
    ∀ m : Nat, (W m v).cache.round = 0 ∨
      ∃ (k : Nat) (tau : Time), k < m ∧ rho.events[k]? = some (.tick v tau) ∧
        (W m v).cache.round = M.round_of S.hc (S.E.slotOf tau) := by
  intro m
  induction m with
  | zero =>
    have h0 : W 0 = fun v' => M.initial S v' := (hW 0).1
    rw [h0]
    exact Or.inl (facts.nd.initial_cache_round S v)
  | succ n ih =>
    have carry : (W n v).cache.round = 0 ∨
        ∃ (k : Nat) (tau : Time), k < n + 1 ∧ rho.events[k]? = some (.tick v tau) ∧
          (W n v).cache.round = M.round_of S.hc (S.E.slotOf tau) := by
      rcases ih with h | ⟨k, tau, hk, he, hr⟩
      · exact Or.inl h
      · exact Or.inr ⟨k, tau, Nat.lt_succ_of_lt hk, he, hr⟩
    obtain ⟨hn, hstep⟩ := hW n
    cases hev : rho.events[n]? with
    | none =>
      have hlen : rho.events.length ≤ n := List.getElem?_eq_none_iff.mp hev
      rw [List.drop_eq_nil_of_le hlen, List.take_nil, List.foldlM_nil] at hstep
      have hsame : W (n + 1) = W n := hstep
      rw [hsame]
      exact carry
    | some e =>
      by_cases hv : v = e.node
      · cases e with
        | wake u t =>
          change v = u at hv
          subst hv
          rw [wake_step₃₀ S rho hev (W n) (W (n + 1)) hstep, Function.update_self,
            facts.nd.wake_cache]
          exact carry
        | tick u t =>
          change v = u at hv
          subst hv
          rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_tick facts S rho hev (W n) hn
              (W (n + 1)) hstep with ⟨out, hout, hw⟩ | ⟨-, hw⟩
          · rw [hw]
            exact Or.inr ⟨n, t, Nat.lt_succ_self n, hev,
              facts.nd.tick_cache_round S v (W n v) t out hout⟩
          · rw [hw]
            exact carry
        | deliver u o t =>
          change v = u at hv
          subst hv
          rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho hev (W n) hn
              (W (n + 1)) hstep with hproc | ⟨-, hw⟩
          · rw [facts.nd.process_cache_round S (W n v) o (W (n + 1) v) hproc]
            exact carry
          · rw [hw]
            exact carry
      · rw [Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_other facts S rho hev v hv (W n) hn
          (W (n + 1)) hstep]
        exact carry

/-- Along a path `W` of a run sorted by key, if the round-`r` phase-`p` slot of `v`'s grade cache in
    `W n` has a result, it has one in `W m` for every `m ≥ n` such that every tick of `v` among the
    events `n` to `m - 1` is at a time whose slot's round is at most `r`. -/
private theorem slot_some_along₃₀ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (v : V) (r : Round) (p : DecoupledConsensusModel.Protocol.Phase) (n : Nat)
    (hbase : M.phaseResult (M.cacheAtRound (W n v).cache r) p ≠ none) :
    ∀ m, n ≤ m →
      (∀ j tau, n ≤ j → j < m → rho.events[j]? = some (.tick v tau) →
        M.round_of S.hc (S.E.slotOf tau) ≤ r) →
      M.phaseResult (M.cacheAtRound (W m v).cache r) p ≠ none := by
  intro m hnm
  induction m, hnm using Nat.le_induction with
  | base => intro _; exact hbase
  | succ m hnm ih =>
    intro hwin
    have ihm := ih (fun j tau hj hjm hget => hwin j tau hj (Nat.lt_succ_of_lt hjm) hget)
    obtain ⟨hm, hstep⟩ := hW m
    have _hr_0 : M.reachedNode (W m v) := facts.ndRun.stateBeforeOf_reachedNode S rho m (W m) hm v
    cases hev : rho.events[m]? with
    | none =>
      have hlen : rho.events.length ≤ m := List.getElem?_eq_none_iff.mp hev
      rw [List.drop_eq_nil_of_le hlen, List.take_nil, List.foldlM_nil] at hstep
      have hsame : W (m + 1) = W m := hstep
      rw [hsame]
      exact ihm
    | some e =>
      by_cases hv : v = e.node
      · cases e with
        | wake u t =>
          change v = u at hv
          subst hv
          rw [wake_step₃₀ S rho hev (W m) (W (m + 1)) hstep, Function.update_self,
            facts.nd.wake_cache]
          exact ihm
        | tick u t =>
          change v = u at hv
          subst hv
          have hround : (W m v).cache.round ≤ M.round_of S.hc (S.E.slotOf t) := by
            rcases cache_round_witness₃₀ facts S rho W hW v m with h | ⟨k, tau, hk, hke, hr⟩
            · rw [h]; exact Nat.zero_le _
            · rw [hr]
              exact facts.gr.round_of_mono S.hc
                (slotOf_mono_sts S (time_le_of_index_le₃₀ rho hsorted hk hke hev))
          have hclock : M.round_of S.hc (S.E.slotOf t) ≤ r :=
            hwin m t hnm (Nat.lt_succ_self m) hev
          rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_tick facts S rho hev (W m) hm
              (W (m + 1)) hstep with ⟨out, hout, hw⟩ | ⟨-, hw⟩
          · obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
              (W m v).st.core.toHealing t (W m v).cache
            rw [hw, facts.nd.tick_cache_eq S v (W m v) t out hout c hc]
            exact facts.gr.phaseResult_clipCache_ne_none _ _ r p
              (facts.gr.phaseResult_onPhaseTick_ne_none_of_le S.E S.hc _ t _ r p hround hclock ihm
                c hc)
          · rw [hw]
            exact ihm
        | deliver u o t =>
          change v = u at hv
          subst hv
          rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho hev (W m) hm
              (W (m + 1)) hstep with hproc | ⟨-, hw⟩
          · rw [facts.nd.process_cache_eq S (W m v) o (W (m + 1) v) hproc]
            exact facts.gr.phaseResult_clipCache_ne_none _ _ r p ihm
          · rw [hw]
            exact ihm
      · rw [Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_other facts S rho hev v hv (W m) hm
          (W (m + 1)) hstep]
        exact ihm

/-- Along a path `W` of `rho`, if every event from index `a` to `b - 1` that is at `v` is a wake of
    `v`, then `v`'s node state in `W b` is its node state in `W a`, or the wake of it. -/
private theorem node_eq_or_wake₃₀ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    (a : Nat) : ∀ b, a ≤ b →
      (∀ j e, a ≤ j → j < b → rho.events[j]? = some e → e.node = v →
        ∃ t' : Time, e = .wake v t') →
      W b v = W a v ∨ W b v = M.wake (W a v) := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _; exact Or.inl rfl
  | succ b hab ih =>
    intro hnot
    have ihb := ih (fun j e hj hjb hget => hnot j e hj (Nat.lt_succ_of_lt hjb) hget)
    obtain ⟨hb, hstep⟩ := hW b
    cases hev : rho.events[b]? with
    | none =>
      have hlen : rho.events.length ≤ b := List.getElem?_eq_none_iff.mp hev
      rw [List.drop_eq_nil_of_le hlen, List.take_nil, List.foldlM_nil] at hstep
      have hsame : W (b + 1) = W b := hstep
      rw [hsame]
      exact ihb
    | some e =>
      by_cases hv : v = e.node
      · obtain ⟨t', rfl⟩ := hnot b e hab (Nat.lt_succ_self b) hev hv.symm
        rw [wake_step₃₀ S rho hev (W b) (W (b + 1)) hstep, Function.update_self]
        rcases ihb with h | h
        · exact Or.inr (by rw [h])
        · exact Or.inr (by rw [h, facts.nd.wake_idem])
      · rw [Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_other facts S rho hev v hv (W b) hb
          (W (b + 1)) hstep]
        exact ihb

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key in which a tick event sits at one index only, if the `i`-th event is
    `v`'s tick at `t`, then `strictEventIndex rho t` is at most `i`, and every event from that index
    to `i - 1` that is at `v` is a wake of `v`. -/
private theorem tick_index_facts₃₀ (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (huniq : Restated.TickIndexUnique rho) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) :
    strictEventIndex rho t ≤ i ∧
    ∀ j e, strictEventIndex rho t ≤ j → j < i → rho.events[j]? = some e → e.node = v →
      ∃ t' : Time, e = .wake v t' := by
  refine ⟨?_, ?_⟩
  · by_contra hcon
    have hlt : i < strictEventIndex rho t := Nat.lt_of_not_ge hcon
    have hp := time_lt_of_lt_strict₃₀ rho hsorted t hlt hi
    simp only [Record.Event.time] at hp
    exact lt_irrefl _ hp
  · intro j e hj hji hget hnode
    have hlow : t ≤ e.time := by
      have hf := Restated.filter_false_of_index_ge_sorted rho hsorted
        (fun x => decide (x.time < t)) (fun a b hab hb => by
          simp only [decide_eq_true_eq] at hb ⊢
          exact (time_le_of_key_le₃₀ hab).trans_lt hb) hj hget
      simpa using hf
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hget
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    have hkey : Record.Event.key e ≤ Record.Event.key (Record.Event.tick v t) := by
      have hp := (List.pairwise_iff_getElem.mp hsorted) j i hjl hil hji
      rw [hje, hie] at hp
      exact hp
    have hteq : Record.Event.time e = t :=
      le_antisymm (time_le_of_key_le₃₀ hkey) hlow
    cases e with
    | wake u t' =>
      simp only [Record.Event.node] at hnode
      exact ⟨t', by rw [hnode]⟩
    | tick u t' =>
      exfalso
      have heq : Record.Event.tick u t' = Record.Event.tick v t := by
        simp only [Record.Event.node] at hnode
        simp only [Record.Event.time] at hteq
        rw [hnode, hteq]
      have hev : rho.events[j] = rho.events[i] := by rw [hje, hie, heq]
      have hij : j = i := huniq (hje.trans heq) hev
      omega
    | deliver u o t' =>
      exfalso
      simp only [Record.Event.time] at hteq
      subst hteq
      simp [Record.Event.key, Record.Event.time, Record.Event.phase, Prod.Lex.toLex_le_toLex] at hkey

/-- In a run sorted by key in which a tick event sits at one index only, along a path `W` of the
    run: if the `i`-th event is `v`'s tick at the phase-`p` domain instant of the positive round
    `r`, and every such tick event has an outcome from the node state `W` holds before it, then for
    every `t` after that domain instant and at or before the opening of round `r + 1`, and every
    outcome `fr` of the frozen root `v`'s store computes in the world of `W` strictly before the
    domain instant, the phase-`p` result of the round-`r` frame read from `v`'s node state in the
    world of `W` strictly before `t` is `fr` clipped to the finalized block of `v`'s store in that
    world. -/
theorem Vocabulary.Proofs.FrameCompleted.frame_phase_completed_of_tick_in_round_of_fields
    (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (huniq : Restated.TickIndexUnique rho)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (v : V) (r : Round) (hr : 0 < r) (p : DecoupledConsensusModel.Protocol.Phase)
    (i : Nat) (he : rho.events[i]? = some (.tick v (M.domain S.E S.hc r p)))
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (M.domain S.E S.hc r p)) →
      ∃ out : M.N × List (NamedObject V), M.tick S v (W j v) (M.domain S.E S.hc r p) ⇢ out)
    (t : Time) (ht : M.domain S.E S.hc r p < t) (hta : t ≤ M.opening S.E S.hc (r + 1)) :
    ∀ fr : Option (Block V), M.freezeRoot S.E
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r p)) v).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r p)) v).st.core.F S.hc.η_SG r
        (M.early S.E S.hc r p) (M.late S.E S.hc r p) ⇢ fr →
    M.phaseResult (M.readFrame (W (strictEventIndex rho t) v).cache
        (M.toHealing (W (strictEventIndex rho t) v).st.core) r) p =
      some (fr.map (fun B => M.clipGrade B (W (strictEventIndex rho t) v).st.core.F)) := by
  have _hr_0 : M.reachedNode (W i v) := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hW i).1 v
  have _hr_1 : M.reachedNode (W (strictEventIndex rho (M.domain S.E S.hc r p)) v) := facts.ndRun.stateBeforeOf_reachedNode S rho (strictEventIndex rho (M.domain S.E S.hc r p)) (W (strictEventIndex rho (M.domain S.E S.hc r p))) (hW (strictEventIndex rho (M.domain S.E S.hc r p))).1 v
  have _hr_2 : M.reachedNode (W (i + 1) v) := facts.ndRun.stateBeforeOf_reachedNode S rho (i + 1) (W (i + 1)) (hW (i + 1)).1 v
  have _hr_3 : M.reachedNode (W (strictEventIndex rho t) v) := facts.ndRun.stateBeforeOf_reachedNode S rho (strictEventIndex rho t) (W (strictEventIndex rho t)) (hW (strictEventIndex rho t)).1 v
  -- 0. `v`'s node state before its domain tick is its node state strictly before the domain.
  obtain ⟨hle, hnot⟩ := tick_index_facts₃₀ rho hsorted huniq he
  have hWv := node_eq_or_wake₃₀ facts S rho W hW v _ i hle hnot
  have hWst : (W i v).st = (W (strictEventIndex rho (M.domain S.E S.hc r p)) v).st := by
    rcases hWv with h | h
    · rw [h]
    · rw [h]; exact (facts.nd.wake_st_record _).1
  -- 1. the domain tick completes the slot.
  have hbase : M.phaseResult (M.cacheAtRound (W (i + 1) v).cache r) p ≠ none := by
    obtain ⟨out₀, hout₀⟩ : ∃ out : M.N × List (NamedObject V),
        M.tick S v (W i v) (M.domain S.E S.hc r p) ⇢ out := hneTick i he
    rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_tick facts S rho he (W i) (hW i).1
        (W (i + 1)) (hW i).2 with ⟨out, hout, hw⟩ | ⟨hno, -⟩
    · obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
        (W i v).st.core.toHealing (M.domain S.E S.hc r p) (W i v).cache
      rw [hw, facts.nd.tick_cache_eq S v (W i v) _ out hout c hc]
      exact facts.gr.phaseResult_clipCache_ne_none _ _ r p
        (facts.gr.phaseResult_onPhaseTick_domain_ne_none S.E S.hc _ _
          (facts.gr.lo_le_domain_of_window_start S hr (lo := 0)
            (by rw [facts.gr.opening_eq_proposal_time]; exact facts.sch.Optimistic_proposal_time_nonneg S.E _) p) _
          (facts.gr.round_of_slotOf_domain S hr p) rfl c hc)
    · exact absurd hout₀ (hno out₀)
  -- 2. the slot stays completed up to the strict read of `t`.
  have hidx : i + 1 ≤ strictEventIndex rho t :=
    succ_le_strict_of_time_lt₃₀ rho hsorted t he ht
  have hstrict :
      M.phaseResult (M.cacheAtRound (W (strictEventIndex rho t) v).cache r) p ≠ none := by
    refine slot_some_along₃₀ facts S rho hsorted W hW v r p (i + 1) hbase _ hidx ?_
    intro j tau _ hjm hget
    have hlt : tau < t := time_lt_of_lt_strict₃₀ rho hsorted t hjm hget
    exact round_le_of_lt_opening₃₀ facts S (lt_of_lt_of_le hlt hta)
  -- 3. the value, read back through the provenance along `W`.
  obtain ⟨res, hres⟩ := Option.ne_none_iff_exists'.mp hstrict
  rcases facts.grRun.completed_phase_origin_along S rho W hW _ v r p res hres with
    ⟨hzero, _⟩ | ⟨j, tau, hj, hej, htau, hvalue⟩
  · exact absurd hzero (Nat.pos_iff_ne_zero.mp hr)
  · subst htau
    have hji : j = i := by
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hej
      obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp he
      exact huniq hje (hje.trans hie.symm)
    subst hji
    intro fr hfr
    rw [facts.gr.readFrame_phase, hres, hvalue fr (by rw [hWst]; exact hfr),
      facts.sto.ModelProperties_toHealing_F, facts.gr.clipResult_some_map_clipGrade]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the execution delivers only well-formed payloads, then for every object `o` delivered in the
    run of the first `n` steps, whatever honest set is declared: if `o` is a block `B`, every vote
    `B` includes is of the slot before `B`'s, every vote of `B`'s support list is among the votes
    `B` includes, and every vote `B` includes has its signer in that vote's slot's committee; and if
    `o` is a Goldfish vote `u`, its signer is in the committee of `u`'s slot. -/
theorem wire_runAll_withHonest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (H : Finset V) (n : Nat)
    (hdel : Restated.DeliveryWellFormed M S x) :
    ∀ (i : Nat) (w : V) (o : NamedObject V) (t : Int),
      ({ Restated.runAll M S Sched x v n with honest := H } : Record.Run V).events[i]? =
        some (.deliver w o t) →
      (∀ B : NamedBlock V, o = NamedObject.block B →
        (∀ u ∈ B.gf_votes, u.slot + 1 = B.slot) ∧
          (∀ u ∈ B.gf_support_votes, u ∈ B.gf_votes) ∧
          (∀ u ∈ B.gf_votes, u.val_index ∈ S.E.committee u.slot)) ∧
      (∀ u : GoldfishVote V, o = NamedObject.gfVote u → u.val_index ∈ S.E.committee u.slot) := by
  intro i w o t hi
  have hmem : (Record.Event.deliver w o t : Record.Event V) ∈ Restated.runEvents M S Sched x n :=
    List.mem_of_getElem? hi
  obtain ⟨k, -, hmemk⟩ := Restated.exists_step_of_mem_runEvents facts S Sched x n hmem
  obtain ⟨m, hlbl, hmsg, -⟩ := Restated.deliver_of_mem_actionEventsOf hmemk
  have hw := hdel.wire k w m hlbl
  rw [hmsg] at hw
  exact hw

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under unforgeable signatures and monotone corruption, if no member of `H` is held at
    `x[n].time`, then, along the path `x` follows, an object whose author is a member `u` of `H`,
    and which is processed at `t` in the run of the first `n` steps or carried by an object
    processed there at `t`, was emitted by `u` at a time at or before `t`. -/
theorem emits_of_signed_runAll_withHonest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (H : Finset V) (n : Nat)
    (hunf : Restated.Unforgeability M S x) (hmono : Sched.MonotoneCorruption)
    (hH : ∀ v₀ ∈ H, v₀ ∉ Sched.adv (x[n].time : Int))
    {v₀ u : V} {o o' : NamedObject V} {t : Int}
    (hproc : Restated.Vocabulary.Execution.NamedRun.processes M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n)
      v₀ o t)
    (hco : o' = o ∨ carries o o') (hauth : NamedObject.author o' = some u) (hu : u ∈ H) :
    ∃ t', t' ≤ t ∧ Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n)
      u o' t' := by
  have hv : HonestThroughTime Sched (x[n].time : Int) u :=
    fun t' ht' hadv => hH u hu (hmono t' _ ht' hadv)
  obtain ⟨k, hkn, ⟨sm, hsm, hsmmsg⟩, htk⟩ :=
    Restated.mem_sent_of_processes facts S Sched x v n hproc
  have hkt : (x[k].time : Int) ≤ (x[n].time : Int) := by
    exact_mod_cast Restated.time_mono facts S Sched x hkn
  have hhonest : Restated.HonestThrough M Sched x k u := fun t' ht' => hv t' (le_trans ht' hkt)
  have hcar : (⟨u, o'⟩ : SignedMsg V (NamedObject V)) ∈ x[k].sent := by
    rcases hco with rfl | hc
    · have h := hunf.unforgeable k sm u hsm (by rw [hsmmsg]; exact hauth) hhonest
      rwa [hsmmsg] at h
    · exact hunf.carried k sm o' u hsm (by rw [hsmmsg]; exact hc) hauth hhonest
  obtain ⟨j, hjk, τ, hlbl, haw, out, hout, hst, hemit⟩ :=
    Restated.tick_of_honest_signed_upTo_taken facts S Sched x u o' (x[n].time : Int) hv hunf hauth
      k hkt hcar
  refine ⟨(τ : Int), ?_, ?_⟩
  · have hj1 : x[j + 1].time ≤ x[k].time := Restated.time_mono facts S Sched x hjk
    have hj2 : x[j + 1].time = τ := (Restated.tickAllAwake_time facts S Sched x hlbl).2
    rw [← htk]
    exact_mod_cast hj2 ▸ hj1
  · exact Restated.emits_runAllPath_of_tick facts S Sched x v (Nat.lt_of_lt_of_le hjk hkn) hlbl
      haw hout hst hemit

end

end DecoupledConsensusModel.Sts.Restated
