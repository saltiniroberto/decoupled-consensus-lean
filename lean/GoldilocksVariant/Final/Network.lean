import GoldilocksVariant.Final.Instance
import LARuns.Goldilocks.Defs

/-!
# The network fields of `EnvFactsBy` and `EnvFactsSync`, on the projection of a run

For a run `π` of any protocol `Pr` of the bare framework `RStsVariant2`, read as the trace
`toTrace init π` with the activity `activityOf π` (`GoldilocksVariant.Final.Projection`), the
delivery promise `delivered` of `EnvFactsBy` and the catch-up promise `CatchUpAfterRestartBy` of
`EnvFactsSync` (`GoldilocksCorrectness.Statements.AbstractTrace.TraceDefs`), each concluded in the
structure's own wording for any deadline function:

- `toTrace_delivered`, from the condition on executions `DeliveredBeforeActingG TickStepG dl π`,
  every honest send addressed to every validator, the trace's deadline at least `dl`, and the
  re-delivery condition `RedeliveredAfterReleaseFromDelivery`;
- `toTrace_caught_up`, from `CatchUpAfterRestartG TickStepG dl dlW π`, the same sends and
  re-delivery condition, `ClockWithinSkew`, `dlW` not decreasing in its time argument
  (`syncDeadline_mono`, `deadlineOutside_mono`), and the trace's catch-up deadline at least
  `ΔClockAhead` after both `dl` and `dlW`.

At the synchronous deadlines, `syncDeadline_le_trace` and `syncCatchUp_ge_run` discharge the two
deadline hypotheses from relations between the run's delays and the trace's.

The re-delivery condition `RedeliveredAfterReleaseFromDelivery` is Goldilocks's extra condition on
its runs, defined in `LARuns.Goldilocks.Defs`: the network's re-delivery promise, made to a receiver
up and honest in every configuration from the first delivery's on that is entered before the
re-delivery deadline, the configurations the activity premise of `delivered` and of
`CatchUpAfterRestartBy` reads.

The sync fact `SyncedWithinBy` of the trace, `toTrace_syncedWithinBy`, from the condition on
executions `SyncedWithinByG TickStepG servesR sync π`, the same re-delivery condition and
`ClockWithinSkew`, for a trace selection `servesT` read at a node's last tick's or restart's reading
and a run selection `servesR` read at its clock, related in both directions across the two
readings (`servesT_reading_free_of_relations` says what the two relations together ask), and for
deadlines that leave room for the clocks and end within the holder's window.
-/

set_option autoImplicit false

namespace GoldilocksVariant.Final

open RStsVariant2 (Exec Execution Envelope Action Config Local Protocol)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity)
open LARuns.GoldilocksInstance (RedeliveredAfterReleaseFromDelivery)

/-! ## 1. The deadline functions -/

section Conditions

open RStsVariant2 (Observable HonestG)
open RStsVariant2.Observable

/-- `syncDeadline tGST ΔDelay m` does not decrease in the real time it counts from.

The variables:
- `tGST`: the time from which the network is synchronous; `ΔDelay`: the delay per message; `m`: the
  message. -/
theorem syncDeadline_mono {Msg : Type} (tGST : ℝ) (ΔDelay : (m : Msg) → ℝ) (m : Msg) :
    Monotone (RStsVariant2.syncDeadline tGST ΔDelay m) := by
  intro a b hab
  unfold RStsVariant2.syncDeadline
  have := max_le_max hab (le_refl tGST)
  linarith

/-- `deadlineOutside tGST ΔDelay tAsyncStart tAsyncEnd m` does not decrease in the real time it
counts from: the first case holds on a set of times closed downwards, and the second case's value
is at least the first's.

The variables:
- `tGST`: the time from which the network is synchronous; `ΔDelay`: the delay per message;
  `tAsyncStart`, `tAsyncEnd`: the asynchronous period; `m`: the message. -/
theorem deadlineOutside_mono {Msg : Type} (tGST : ℝ) (ΔDelay : (m : Msg) → ℝ)
    (tAsyncStart tAsyncEnd : ℝ) (m : Msg) :
    Monotone (RStsVariant2.deadlineOutside tGST ΔDelay tAsyncStart tAsyncEnd m) := by
  intro a b hab
  unfold RStsVariant2.deadlineOutside
  have h1 : max a tGST ≤ max b tGST := max_le_max hab le_rfl
  have h2 : max b tGST ≤ max b (max tAsyncEnd tGST) :=
    max_le_max le_rfl (le_max_right _ _)
  have h3 : max a (max tAsyncEnd tGST) ≤ max b (max tAsyncEnd tGST) := max_le_max hab le_rfl
  split_ifs with ha hb hb
  · linarith
  · linarith
  · exact absurd (le_trans (by linarith) hb) ha
  · linarith

/-- The run's deadline `syncDeadline tGST ΔDelay` is at most the trace's `syncDeadline Δ GST` for
every message of the class `ok`, when `tGST ≤ GST` and `ΔDelay m ≤ Δ` for every such message: the
hypothesis `hdl` of `toTrace_delivered` at those two deadlines.

The variables:
- `tGST`, `ΔDelay`: the run's deadline; `Δ`, `GST`: the trace's; `ok`: the class of messages;
  `htGST`, `hΔ`: the two relations. -/
theorem syncDeadline_le_trace {Node Msg : Type} {tGST : ℝ} {ΔDelay : (m : Msg) → ℝ} {Δ GST : ℕ}
    {ok : (m : Msg) → Prop} (htGST : tGST ≤ GST) (hΔ : ∀ m : Msg, ok m → ΔDelay m ≤ Δ) :
    ∀ (sm : Framework.StsMultisetLog.SignedMsg Node Msg) (a d : ℝ), ok sm.msg →
      GoldilocksCorrectness.Statements.AbstractTrace.syncDeadline (α := ℝ) Δ GST sm a = some d →
      RStsVariant2.syncDeadline tGST ΔDelay sm.msg a ≤ d := by
  intro sm a d hok hd
  simp only [GoldilocksCorrectness.Statements.AbstractTrace.syncDeadline, Option.some.injEq] at hd
  subst hd
  unfold RStsVariant2.syncDeadline
  have h1 := max_le_max (le_refl a) htGST
  have h2 := hΔ _ hok
  linarith

/-- The run's deadlines `syncDeadline tGST ΔDelay` from the sending and `syncDeadline tGST ΔCatchUp`
from the restart are each at least `ΔClockAhead` before the trace's catch-up deadline
`syncCatchUp Δ Δw GST` for every message of the class `ok`, when `tGST ≤ GST`,
`ΔDelay m + ΔClockAhead ≤ Δ` and `ΔCatchUp m + ΔClockAhead ≤ Δw` for every such message: the
hypothesis `hcu` of `toTrace_caught_up` at those deadlines.

The variables:
- `tGST`, `ΔDelay`, `ΔCatchUp`: the run's deadlines; `Δ`, `Δw`, `GST`: the trace's;
  `ΔClockAhead`: the clock-ahead bound; `ok`: the class of messages; `htGST`, `hΔ`, `hΔw`: the
  relations. -/
theorem syncCatchUp_ge_run {Node Msg : Type} {tGST ΔClockAhead : ℝ}
    {ΔDelay ΔCatchUp : (m : Msg) → ℝ} {Δ Δw GST : ℕ} {ok : (m : Msg) → Prop}
    (htGST : tGST ≤ GST) (hΔ : ∀ m : Msg, ok m → ΔDelay m + ΔClockAhead ≤ Δ)
    (hΔw : ∀ m : Msg, ok m → ΔCatchUp m + ΔClockAhead ≤ Δw) :
    ∀ (sm : Framework.StsMultisetLog.SignedMsg Node Msg) (a t' c : ℝ), ok sm.msg →
      GoldilocksCorrectness.Statements.AbstractTrace.syncCatchUp (α := ℝ) Δ Δw GST sm a t' =
        some c →
      RStsVariant2.syncDeadline tGST ΔDelay sm.msg a + ΔClockAhead ≤ c ∧
        RStsVariant2.syncDeadline tGST ΔCatchUp sm.msg t' + ΔClockAhead ≤ c := by
  intro sm a t' c hok hc
  simp only [GoldilocksCorrectness.Statements.AbstractTrace.syncCatchUp, Option.some.injEq] at hc
  subst hc
  unfold RStsVariant2.syncDeadline
  have h1 := max_le_max (le_refl a) htGST
  have h2 := max_le_max (le_refl t') htGST
  have h3 := hΔ _ hok
  have h4 := hΔw _ hok
  have h5 := le_max_left (max a (GST : ℝ) + Δ) (max t' (GST : ℝ) + Δw)
  have h6 := le_max_right (max a (GST : ℝ) + Δ) (max t' (GST : ℝ) + Δw)
  constructor <;> linarith

end Conditions

/-! ## 2. Sends, read on the run -/

section Sends

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} (init : (v : Node) → NodeState) (π : Exec Pr)

/-- No element is in a multiset minus itself.

The variables:
- `e`: the element; `m`: the multiset. -/
theorem not_mem_sub_self {α : Type} [DecidableEq α] (e : α) (m : Multiset α) : e ∉ m - m := by
  intro hm
  have hc := Multiset.count_pos.2 hm
  rw [Multiset.count_sub] at hc
  omega

/-- A signed message the trace's step `j` puts on the wire is the signed message of an envelope
that a step `i` of `π` puts on the wire, with `j = newIdx π i`: a trace step of the kind `other`
keeps the run's configuration, and the run's sent log only grows, so the difference of the two
logs with the recipients dropped is the difference of the logs, recipients dropped.

The variables:
- `j`: the trace step; `sm`: the signed message; `h`: step `j` puts `sm` on the wire. -/
theorem exists_envelope_of_putsAt {j : ℕ} {sm : Framework.StsMultisetLog.SignedMsg Node Msg}
    (h : (toTrace init π).PutsAt j sm) :
    ∃ (i : ℕ) (e : Envelope Node Msg), newIdx π i = j ∧ e ∈ π[i + 1].sent - π[i].sent ∧
      traceMsg e = sm := by
  unfold GoldilocksCorrectness.Statements.AbstractTrace.Trace.PutsAt at h
  by_cases hj : ∃ i : ℕ, newIdx π i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [toTrace_sent_newIdx_succ, toTrace_sent_newIdx] at h
    obtain ⟨d, hd⟩ := Multiset.le_iff_exists_add.1 (π.sent_mono (Nat.le_succ i))
    rw [hd, Multiset.map_add, add_tsub_cancel_left] at h
    obtain ⟨e, he, hes⟩ := Multiset.mem_map.1 h
    refine ⟨i, e, rfl, ?_, hes⟩
    rw [hd, add_tsub_cancel_left]
    exact he
  · rw [toTrace_sent, toTrace_sent, origBefore_succ_of_not π hj] at h
    exact absurd h (not_mem_sub_self _ _)

/-- A restart puts nothing on the wire: the sent log is the same before and after it.

The variables:
- `i`: the step; `v`: the validator; `keep`: whether the memory is kept. -/
theorem sent_succ_of_restart {i : ℕ} {v : Node} {keep : Bool} (h : π.lbl i = .restart v keep) :
    π[i + 1].sent = π[i].sent := by
  have hs := π.step_at i
  rw [h] at hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hsent⟩ := hs.restart_eq
  exact hsent

/-- `SendsToAll Pr`: every reaction the protocol `Pr` permits addresses each of its sends to every
validator. A property of a protocol, not a condition on executions.

The variables:
- `Pr`: the protocol.

Read aloud: the protocol only broadcasts. -/
def SendsToAll (Pr : Protocol Node Msg NodeState Ev) : Prop :=
  ∀ (p : Node) (r : ℕ) (s : NodeState) (ev : RStsVariant2.Event Node Msg Ev)
    (res : RStsVariant2.NodeStepResult Node NodeState Msg),
    Pr.step p r s ev res → ∀ a : RStsVariant2.Addressed Node Msg,
      RStsVariant2.NodeEffect.send a ∈ res.effects → a.recipients = .all

open RStsVariant2 in
/-- An envelope a step of a run of a protocol that only broadcasts puts on the wire, signed by a
validator outside the corrupted set before the step, is addressed to every validator: such a step
is a reaction of that validator (an adversarial send is signed by a corrupted one, and the other
steps put nothing on the wire).

The variables:
- `hP`: `Pr` only broadcasts; `i`: the step; `e`: the envelope; `he`: step `i` puts `e` on the
  wire; `hs`: its signer is outside the corrupted set of configuration `i`. -/
theorem recipients_of_sent_sub (hP : SendsToAll Pr) {i : ℕ} {e : Envelope Node Msg}
    (he : e ∈ π[i + 1].sent - π[i].sent) (hs : e.sender ∉ π[i].adv) :
    ∀ v : Node, e.recipients.Has v := by
  suffices hall : e.recipients = .all by
    intro v; rw [hall]; trivial
  have h := π.step_at i
  refine h.elim (motive := fun a d d' => e ∈ d'.sent - d.sent → e.sender ∉ d.adv →
      e.recipients = .all)
    ?setClock ?tick ?deliver ?deliverAdv ?corrupt ?crash ?crashDuring ?restart ?custom
    ?adversarial he hs
  case setClock =>
    intro d w t _ _ he' _
    exact absurd he' (not_mem_sub_self _ _)
  case tick =>
    intro d w l t res _ _ _ _ hst he' _
    rw [applyNodeStepResult_sent] at he'
    exact hP _ _ _ _ _ hst _ (mem_applyEffects_sent_sub w d res.effects he').2
  case deliver =>
    intro d w e' l t res _ _ _ _ _ _ hst he' _
    rw [applyNodeStepResult_sent] at he'
    rw [← receive_sent w e'.toSignedMsg d] at he'
    exact hP _ _ _ _ _ hst _ (mem_applyEffects_sent_sub w _ res.effects he').2
  case deliverAdv =>
    intro d w e' _ _ _ he' _
    rw [receive_sent] at he'
    exact absurd he' (not_mem_sub_self _ _)
  case corrupt =>
    intro d w _ he' _
    exact absurd he' (not_mem_sub_self _ _)
  case crash =>
    intro d w _ he' _
    exact absurd he' (not_mem_sub_self _ _)
  case crashDuring =>
    intro d w na k l t res _ _ _ hst he' _
    rw [applyCrashDuring_sent] at he'
    have hr : (na.prepare w d).sent = d.sent := by
      cases na <;> simp [NodeAction.prepare, receive]
    rw [← hr] at he'
    have hm := (mem_applyEffects_sent_sub w _ _ he').2
    exact hP _ _ _ _ _ hst _ (List.mem_of_mem_take hm)
  case restart =>
    intro d w keep t _ _ _ he' _
    have he'' : e ∈ d.sent - d.sent := by simpa using he'
    exact absurd he'' (not_mem_sub_self _ _)
  case custom =>
    intro d w ev l t res _ _ _ _ _ hst he' _
    rw [applyNodeStepResult_sent] at he'
    exact hP _ _ _ _ _ hst _ (mem_applyEffects_sent_sub w d res.effects he').2
  case adversarial =>
    intro d w m rs hw he' hs'
    by_cases hea : e = { sender := w, msg := m, recipients := rs }
    · rw [hea] at hs'
      exact absurd hw hs'
    · have hc := Multiset.count_pos.2 he'
      rw [Multiset.count_sub, Multiset.count_cons_of_ne hea] at hc
      omega

/-- A run step before step `j₀` at which `v` ticks or restarts at a reading at least `r` is a trace
step before `newIdx π j₀` with the same event: the run's `ReactedAtLeastG` at `j₀` gives the trace's
`ReactedAtLeast` at `newIdx π j₀`.

The variables:
- `j₀`: the run step; `v`: the validator; `r`: the reading. -/
theorem reactedAtLeast_of_reactedAtLeastG {j₀ : ℕ} {v : Node} {r : ℕ}
    (h : LARuns.ReactedAtLeastG π (iBefore := j₀) v (tAtLeast := r)) :
    (toTrace init π).ReactedAtLeast (newIdx π j₀) v r := by
  obtain ⟨iR, tR, hlt, hr, hc⟩ := h
  refine ⟨newIdx π iR, (newIdx_lt π hlt).le, tR, hr, ?_⟩
  rw [toTrace_lbl_newIdx]
  rcases hc with ⟨hl, hcl⟩ | ⟨keep, hl, hcl⟩
  · exact Or.inl ((eventOf_eq_tick π).2 ⟨hl, hcl⟩)
  · exact Or.inr ⟨keep, (eventOf_eq_restart π).2 ⟨hl, hcl⟩⟩

end Sends

/-! ## 3. The receiver's activity, read on the run -/

section Activity

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg] [Fintype Node]
  {Pr : Protocol Node Msg NodeState Ev} (init : (v : Node) → NodeState) (π : Exec Pr)

/-- A validator active after every trace step from `newIdx π lo + 1` to `newIdx π k₀` is up and
outside the corrupted set in every configuration of `π` from `lo + 1` to `k₀`: configuration `l + 1`
is the trace's after step `newIdx π l + 1`.

The variables:
- `lo`, `k₀`: the run steps; `v`: the validator; `hact`: the activity on the trace. -/
theorem up_of_active_window {lo k₀ : ℕ} {v : Node}
    (hact : ∀ j : ℕ, newIdx π lo + 1 ≤ j → j ≤ newIdx π k₀ → v ∈ (activityOf π).active j) :
    ∀ l : ℕ, lo + 1 ≤ l → l ≤ k₀ → (v ∉ π[l].crashed ∧ π[l][v] ≠ none) ∧ v ∉ π[l].adv := by
  intro l hl1 hl2
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  have hj1 : newIdx π lo + 1 ≤ newIdx π l' + 1 :=
    Nat.succ_le_succ ((newIdx_strictMono π).monotone (by omega))
  have hj2 : newIdx π l' + 1 ≤ newIdx π k₀ := newIdx_lt π (by omega)
  have h := hact _ hj1 hj2
  rw [mem_active_activityOf, origBefore_newIdx_succ] at h
  exact h

omit [Fintype Node] in
/-- A validator up in configuration `i₀ + 1` is up in configuration `i₀` when step `i₀` puts an
envelope on the wire: a step that brings a validator up is its restart (`restart_of_up`), which puts
nothing on the wire (`sent_succ_of_restart`).

The variables:
- `i₀`: the step; `v`: the validator; `e`: the envelope. -/
theorem up_of_up_succ_of_sent {i₀ : ℕ} {v : Node} {e : Envelope Node Msg}
    (he : e ∈ π[i₀ + 1].sent - π[i₀].sent) (hup : v ∉ π[i₀ + 1].crashed ∧ π[i₀ + 1][v] ≠ none) :
    v ∉ π[i₀].crashed ∧ π[i₀][v] ≠ none := by
  by_contra hn
  obtain ⟨keep, hr⟩ := restart_of_up π i₀ v hn hup
  rw [sent_succ_of_restart π hr] at he
  exact not_mem_sub_self _ _ he

omit [Fintype Node] in
/-- No step at which `v` is up in the configuration it starts from is a restart of `v`: a restart is
enabled only at a validator crashed or with its local state unknown.

The variables:
- `l`: the step; `v`: the validator; `keep`: whether the memory is kept. -/
theorem not_restart_of_up {l : ℕ} {v : Node} {keep : Bool}
    (hup : v ∉ π[l].crashed ∧ π[l][v] ≠ none) : π.lbl l ≠ .restart v keep := by
  intro hl
  have hs := π.step_at l
  rw [hl] at hs
  obtain ⟨-, hdown, -⟩ := hs.restart_eq
  rcases hdown with hc | hn
  · exact hup.1 hc
  · exact hup.2 hn

omit [Fintype Node] in
/-- The re-delivery case of the release clause, for a receiver read on the run: take a validator `v`
up and outside the corrupted set in every configuration of `π` from `j₀` to `k₀`, an envelope `e` an
honest validator put on the wire at step `i₀`, delivered to `v` at step `j₀ < k₀` while `v` had not
yet reacted to `e`'s release reading `r`, and `v`'s tick `k₀` at a reading `t ≥ r`. When the trace's
re-delivery deadline (`ΔRedeliver` after `v`'s first tick at a reading at least `r` after the trace
step of `j₀`) is at most the time of `newIdx π k₀`, and the run meets
`RedeliveredAfterReleaseFromDelivery`, `e` is delivered to `v` again at a step `j` with
`j₀ < j < k₀`, that delivery found `v` reacted to `r`, and no step between `j` and `k₀` restarts
`v`.

Route: the first tick `k₁` of `v` after `j₀` at a reading at least `r` is at or before `k₀`
(`Nat.find`); the premise at `newIdx π k₁` gives `π.stamp (k₁ + 1) + ΔRedeliver ≤ π.stamp (k₀ + 1)`,
so every configuration from `j₀`'s on entered before that deadline is at most the `k₀`-th, where
`v` is up and honest; the re-delivery is before `v`'s tick `k₀`, which is at or after the deadline.

The variables:
- `hRe`: the re-delivery condition; `i₀`, `j₀`, `k₀`: the run steps; `v`: the validator; `e`: the
  envelope; `t`: `k₀`'s reading; `r`: the release reading; `hup`: `v` up and honest from `j₀` to
  `k₀`; `hprem`: the trace's re-delivery premise at the trace step of `j₀`.

Read aloud: a message delivered to a node up and honest until its tick, before that node reached its
release, is delivered again before the tick, once reached. -/
theorem redelivered_reacted_of_up {release : (m : Msg) → Option ℕ} {ΔRedeliver : ℕ}
    (hRe : RedeliveredAfterReleaseFromDelivery release (ΔRedeliver : ℝ) π)
    {i₀ j₀ k₀ : ℕ} {v : Node} {e : Envelope Node Msg} {t r : ℕ}
    (hup : ∀ l : ℕ, j₀ ≤ l → l ≤ k₀ → (v ∉ π[l].crashed ∧ π[l][v] ≠ none) ∧ v ∉ π[l].adv)
    (hsend : e ∈ π[i₀ + 1].sent - π[i₀].sent) (hsadv : e.sender ∉ π[i₀].adv)
    (hjk : j₀ < k₀) (hlj : π.lbl j₀ = .deliver v e)
    (hk : π.lbl k₀ = .tick v) (hc : π[k₀].clock v = some t)
    (hrel : release e.msg = some r) (hrt : r ≤ t)
    (hnr : ¬ (toTrace init π).ReactedAtLeast (newIdx π j₀) v r)
    (hprem : ∀ (k₁ t₁ : ℕ), newIdx π j₀ < k₁ → k₁ ≤ newIdx π k₀ →
      (toTrace init π).lbl k₁ = Event.tick v t₁ → r ≤ t₁ →
      (∀ (l t' : ℕ), newIdx π j₀ < l → l < k₁ → (toTrace init π).lbl l = Event.tick v t' → t' < r) →
      (toTrace init π).time (k₁ + 1) + ΔRedeliver ≤ (toTrace init π).time (newIdx π k₀)) :
    ∃ j : ℕ, j₀ < j ∧ j < k₀ ∧ π.lbl j = .deliver v e ∧
      (toTrace init π).ReactedAtLeast (newIdx π j) v r ∧
      ∀ (l : ℕ) (keep : Bool), j < l → l < k₀ → π.lbl l ≠ .restart v keep := by
  classical
  -- `v`'s first tick after `j₀` at a reading at least `r`
  have hex : ∃ n : ℕ, j₀ < n ∧ n ≤ k₀ ∧ π.lbl n = .tick v ∧
      ∃ t₁ : ℕ, π[n].clock v = some t₁ ∧ r ≤ t₁ := ⟨k₀, hjk, le_rfl, hk, t, hc, hrt⟩
  obtain ⟨hjk₁, hk₁k, hlk₁, t₁, hc₁, hr₁⟩ := Nat.find_spec hex
  have hmin : ∀ n : ℕ, j₀ < n → n < Nat.find hex → π.lbl n = .tick v →
      ∀ t' : ℕ, π[n].clock v = some t' → t' < r := by
    intro n h1 h2 hl t' hc'
    by_contra hge
    exact Nat.find_min hex h2 ⟨h1, by omega, hl, t', hc', by omega⟩
  -- the trace's premise gives the deadline before the tick `k₀`
  have hupj₀ := hup j₀ le_rfl hjk.le
  have hdead := hprem (newIdx π (Nat.find hex)) t₁ (newIdx_lt π hjk₁)
    ((newIdx_strictMono π).monotone hk₁k)
    (by rw [toTrace_lbl_newIdx]; exact (eventOf_eq_tick π).2 ⟨hlk₁, hc₁⟩) hr₁
    (by
      intro l t' h1 h2 hl
      obtain ⟨l₀, rfl, hl₀, hc₀⟩ := exists_of_lbl_tick init π hl
      exact hmin l₀ ((newIdx_strictMono π).lt_iff_lt.1 h1)
        ((newIdx_strictMono π).lt_iff_lt.1 h2) hl₀ t' hc₀)
  rw [toTrace_time_newIdx_succ, toTrace_time_newIdx] at hdead
  -- the re-delivery
  obtain ⟨j, hkj, ⟨hlj', -, -, -⟩, -, hacts⟩ := hRe i₀ j₀ (Nat.find hex) v e r t₁
    ⟨hlj, hupj₀.1.1, hupj₀.1.2, hupj₀.2⟩ hrel ⟨hsend, hsadv⟩
    (fun h => hnr (reactedAtLeast_of_reactedAtLeastG init π h)) hjk₁ ⟨hlk₁, hc₁⟩ hr₁
    (fun n tT h1 h2 hn => hmin n h1 h2 hn.1 tT hn.2)
    (by
      intro c hc1 hc2
      have hck : c ≤ k₀ := by
        by_contra hgt
        have := π.stamp_mono (show k₀ + 1 ≤ c by omega)
        simp only [RStsVariant2.observable_stamp_exec] at hc2
        linarith
      have := hup c hc1 hck
      exact ⟨this.1.1, this.1.2, this.2⟩)
  have hjk' : j < k₀ := hacts k₀ ⟨t, hk, hc⟩ (by simpa using hdead)
  refine ⟨j, by omega, hjk', hlj', ?_, ?_⟩
  · refine ⟨newIdx π (Nat.find hex), (newIdx_lt π hkj).le, t₁, hr₁, Or.inl ?_⟩
    rw [toTrace_lbl_newIdx]
    exact (eventOf_eq_tick π).2 ⟨hlk₁, hc₁⟩
  · intro l keep hl1 hl2
    exact not_restart_of_up π (hup l (by omega) hl2.le).1

/-- The re-delivery case of the release clause, shared by `delivered` and `CatchUpAfterRestartBy`.
Take a validator `v` active after every trace step from `newIdx π lo + 1` to `newIdx π k₀`, an
envelope `e` an honest validator put on the wire at step `i₀`, delivered to `v` at step `j₀` with
`lo < j₀ < k₀` while `v` had not yet reacted to `e`'s release reading `r`, and `v`'s tick `k₀` at a
reading `t ≥ r`. When the trace's re-delivery deadline (`ΔRedeliver` after `v`'s first tick at a
reading at least `r` after a delivery after `newIdx π lo` that found `v` not yet reacted to `r`) is
at most the time of `newIdx π k₀`, and the run meets `RedeliveredAfterReleaseFromDelivery`, `e` is
delivered to `v` again at a step `j` with `lo < j < k₀`, that delivery found `v` reacted to `r`, and
no step between `j` and `k₀` restarts `v`.

Route: `v` is up and honest in every configuration from `lo + 1` to `k₀` (`up_of_active_window`), so
from `j₀` to `k₀`; the trace's premise at the trace step of `j₀` is the one
`redelivered_reacted_of_up` reads.

The variables:
- `hRe`: the re-delivery condition; `lo`, `i₀`, `j₀`, `k₀`: the run steps; `v`: the validator; `e`:
  the envelope; `t`: `k₀`'s reading; `r`: the release reading; `hprem`: the trace's re-delivery
  premise. -/
theorem redelivered_reacted {release : (m : Msg) → Option ℕ} {ΔRedeliver : ℕ}
    (hRe : RedeliveredAfterReleaseFromDelivery release (ΔRedeliver : ℝ) π)
    {lo i₀ j₀ k₀ : ℕ} {v : Node} {e : Envelope Node Msg} {t r : ℕ}
    (hact : ∀ j : ℕ, newIdx π lo + 1 ≤ j → j ≤ newIdx π k₀ → v ∈ (activityOf π).active j)
    (hsend : e ∈ π[i₀ + 1].sent - π[i₀].sent) (hsadv : e.sender ∉ π[i₀].adv)
    (hlo : lo < j₀) (hjk : j₀ < k₀) (hlj : π.lbl j₀ = .deliver v e)
    (hk : π.lbl k₀ = .tick v) (hc : π[k₀].clock v = some t)
    (hrel : release e.msg = some r) (hrt : r ≤ t)
    (hnr : ¬ (toTrace init π).ReactedAtLeast (newIdx π j₀) v r)
    (hprem : ∀ (r j₀' k₁ t₁ : ℕ), release e.msg = some r →
      newIdx π lo < j₀' → (toTrace init π).lbl j₀' = Event.deliver v (traceMsg e) →
      ¬ (toTrace init π).ReactedAtLeast j₀' v r →
      j₀' < k₁ → k₁ ≤ newIdx π k₀ → (toTrace init π).lbl k₁ = Event.tick v t₁ → r ≤ t₁ →
      (∀ (l t' : ℕ), j₀' < l → l < k₁ → (toTrace init π).lbl l = Event.tick v t' → t' < r) →
      (toTrace init π).time (k₁ + 1) + ΔRedeliver ≤ (toTrace init π).time (newIdx π k₀)) :
    ∃ j : ℕ, lo < j ∧ j < k₀ ∧ π.lbl j = .deliver v e ∧
      (toTrace init π).ReactedAtLeast (newIdx π j) v r ∧
      ∀ (l : ℕ) (keep : Bool), j < l → l < k₀ → π.lbl l ≠ .restart v keep := by
  have hup := up_of_active_window π hact
  have hupj₀ := hup j₀ (by omega) hjk.le
  have hdel : (toTrace init π).lbl (newIdx π j₀) = Event.deliver v (traceMsg e) := by
    rw [toTrace_lbl_newIdx]
    exact (eventOf_eq_deliver π).2 ⟨e, hlj, rfl, hupj₀.1.1, hupj₀.1.2, hupj₀.2⟩
  obtain ⟨j, hj, hjk', hlj', hreact, hnres⟩ := redelivered_reacted_of_up init π hRe
    (fun l h1 h2 => hup l (by omega) h2) hsend hsadv hjk hlj hk hc hrel hrt hnr
    (fun k₁ t₁ h1 h2 h3 h4 h5 => hprem r (newIdx π j₀) k₁ t₁ hrel (newIdx_lt π hlo) hdel hnr h1
      h2 h3 h4 h5)
  exact ⟨j, by omega, hjk', hlj', hreact, hnres⟩

end Activity

/-! ## 4. The delivery promise and the catch-up promise -/

section Fields

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg] [Fintype Node]
  {Pr : Protocol Node Msg NodeState Ev} (init : (v : Node) → NodeState) (π : Exec Pr)

/-- `delivered` on `toTrace init π` and `activityOf π`, for any deadline function `deadline` of the
trace and any `dl` of the run with `dl sm.msg a` at most the trace's deadline `deadline sm a` for every
message of the class `ok`, and any release readings `release` and re-delivery delay `ΔRedeliver`.

Route: the trace's honest send is a step `i₀` of `π` putting an envelope `e` on the wire
(`exists_envelope_of_putsAt`), addressed to `v` (`hAll`), and the trace's tick is a tick `k₀` of
`π` (`exists_of_lbl_tick`); `v` is up in every configuration of `π` from `i₀` to `k₀`
(`up_of_active_window`, `up_of_up_succ_of_sent`), and `e` is due by the tick's real time, since the
trace's times of the sending and of the tick are the run's; `DeliveredBeforeActingG` gives the
delivery `j₀`. When `e`'s message has a release reading `r ≤ t` and `j₀` found `v` not yet reacted
to `r`, `redelivered_reacted` gives the re-delivery after `v`'s first tick at a reading at least `r`.

The variables:
- `init`: the node states before a local state is known; `π`: the run; `dl`: the run's deadline
  function; `hD`: the run's delivery condition; `hRe`: the run's re-delivery condition; `hAll`:
  every envelope an honest validator puts on the wire is addressed to every validator; `hdl`: the
  run's deadline is at most the trace's.

Read aloud: when the network of `π` delivers every honest envelope to each recipient up from its
sending to its tick after the deadline, re-delivers a message that came too early for its release,
and every honest envelope is addressed to everyone, the trace of `π` meets the trace layer's
delivery promise. -/
theorem toTrace_delivered {dl : (m : Msg) → (tSend : ℝ) → ℝ}
    {deadline : (sm : Framework.StsMultisetLog.SignedMsg Node Msg) → (a : ℝ) → Option ℝ}
    {release : (m : Msg) → Option ℕ} {ΔRedeliver : ℕ} {ok : (m : Msg) → Prop}
    (hD : RStsVariant2.DeliveredBeforeActingG RStsVariant2.TickStepG dl π)
    (hRe : RedeliveredAfterReleaseFromDelivery release (ΔRedeliver : ℝ) π)
    (hAll : ∀ (i : ℕ) (e : Envelope Node Msg), e ∈ π[i + 1].sent - π[i].sent →
      e.sender ∉ π[i].adv → ∀ v : Node, e.recipients.Has v)
    (hdl : ∀ (sm : Framework.StsMultisetLog.SignedMsg Node Msg) (a d : ℝ), ok sm.msg →
      deadline sm a = some d → dl sm.msg a ≤ d) :
    ∀ (i k : ℕ) (v : Node) (sm : Framework.StsMultisetLog.SignedMsg Node Msg) (t : ℕ) (d : ℝ),
      (toTrace init π).HonestSendAt (activityOf π) i sm → ok sm.msg →
      (toTrace init π).lbl k = Event.tick v t → i < k →
      (∀ j : ℕ, i + 1 ≤ j → j ≤ k → v ∈ (activityOf π).active j) →
      deadline sm ((toTrace init π).time (i + 1)) = some d → d ≤ (toTrace init π).time k →
      (∀ (r j₀ k₁ t₁ : ℕ), release sm.msg = some r →
        i < j₀ → (toTrace init π).lbl j₀ = Event.deliver v sm →
        ¬ (toTrace init π).ReactedAtLeast j₀ v r →
        j₀ < k₁ → k₁ ≤ k → (toTrace init π).lbl k₁ = Event.tick v t₁ → r ≤ t₁ →
        (∀ (l t' : ℕ), j₀ < l → l < k₁ → (toTrace init π).lbl l = Event.tick v t' → t' < r) →
        (toTrace init π).time (k₁ + 1) + ΔRedeliver ≤ (toTrace init π).time k) →
      ∃ j : ℕ, i < j ∧ j < k ∧ (toTrace init π).lbl j = Event.deliver v sm ∧
        (∀ r : ℕ, release sm.msg = some r → r ≤ t → (toTrace init π).ReactedAtLeast j v r) ∧
        ∀ (l t' : ℕ), j < l → l < k → (toTrace init π).lbl l ≠ Event.restart v t' false := by
  classical
  intro i k v sm t d hHS hok hk hik hact hd hdk hprem
  obtain ⟨i₀, e, rfl, he, rfl⟩ := exists_envelope_of_putsAt init π hHS.1
  have hsadv : e.sender ∉ π[i₀].adv := by
    have := hHS.2
    rwa [corrupted_activityOf_newIdx] at this
  obtain ⟨k₀, rfl, hlk, hck⟩ := exists_of_lbl_tick init π hk
  have hik₀ : i₀ < k₀ := (newIdx_strictMono π).lt_iff_lt.1 hik
  have hup := up_of_active_window π hact
  have hup0 := up_of_up_succ_of_sent π he (hup (i₀ + 1) le_rfl (by omega)).1
  have hUp : RStsVariant2.UpBetweenG π i₀ k₀ v := by
    intro l hl1 hl2
    rcases Nat.eq_or_lt_of_le hl1 with rfl | h
    · exact hup0
    · exact (hup l h hl2).1
  have hdue : RStsVariant2.DueByG dl π i₀ e (π.stamp (k₀ + 1)) := by
    refine ⟨he, ?_⟩
    have h1 := hdl _ _ _ hok hd
    rw [toTrace_time_newIdx_succ] at h1
    rw [toTrace_time_newIdx] at hdk
    exact h1.trans hdk
  obtain ⟨j₀, hij₀, hjk₀, hlj₀, hnr⟩ := hD k₀ v hlk i₀ e hik₀ (hAll i₀ e he hsadv v) hUp hdue
  have hupj₀ := hup j₀ hij₀ hjk₀.le
  have hdelj₀ : (toTrace init π).lbl (newIdx π j₀) = Event.deliver v (traceMsg e) := by
    rw [toTrace_lbl_newIdx]
    exact (eventOf_eq_deliver π).2 ⟨e, hlj₀, rfl, hupj₀.1.1, hupj₀.1.2, hupj₀.2⟩
  by_cases hcase : ∀ r : ℕ, release e.msg = some r → r ≤ t →
      (toTrace init π).ReactedAtLeast (newIdx π j₀) v r
  · refine ⟨newIdx π j₀, newIdx_lt π hij₀, newIdx_lt π hjk₀, hdelj₀, hcase, ?_⟩
    intro l t' hl1 hl2 hl
    obtain ⟨l₀, rfl, hl₀, -⟩ := exists_of_lbl_restart init π hl
    exact hnr l₀ ((newIdx_strictMono π).lt_iff_lt.1 hl1) ((newIdx_strictMono π).lt_iff_lt.1 hl2) hl₀
  · push Not at hcase
    obtain ⟨r, hrel, hrt, hnreact⟩ := hcase
    obtain ⟨j, hij, hjk, hlj, hreact, hnres⟩ := redelivered_reacted init π hRe hact he hsadv
      hij₀ hjk₀ hlj₀ hlk hck hrel hrt hnreact hprem
    have hupj := hup j hij hjk.le
    refine ⟨newIdx π j, newIdx_lt π hij, newIdx_lt π hjk, ?_, ?_, ?_⟩
    · rw [toTrace_lbl_newIdx]
      exact (eventOf_eq_deliver π).2 ⟨e, hlj, rfl, hupj.1.1, hupj.1.2, hupj.2⟩
    · intro r' hr' _
      have hr'' : release e.msg = some r' := hr'
      rw [hrel] at hr''
      cases hr''
      exact hreact
    · intro l t' hl1 hl2 hl
      obtain ⟨l₀, rfl, hl₀, -⟩ := exists_of_lbl_restart init π hl
      exact hnres l₀ false ((newIdx_strictMono π).lt_iff_lt.1 hl1)
        ((newIdx_strictMono π).lt_iff_lt.1 hl2) hl₀

/-- `CatchUpAfterRestartBy` on `toTrace init π` and `activityOf π`, for any catch-up deadline
function `catchUp` of the trace and any `dl`, `dlW` of the run with `dl sm.msg a` and `dlW sm.msg t`
each at least `ΔClockAhead` before the trace's catch-up deadline `catchUp sm a t` for every message
of the class `ok`, `dlW` not decreasing in the real time it counts from, and any release readings
`release` and re-delivery delay `ΔRedeliver`.

Route: the trace's honest send, restart and tick are a send `i₀`, a restart `kr` and a tick `k₀` of
`π`; the tick's real time is at least its reading `c'` less `ΔClockAhead` (`le_stamp_of_clock`), so
at least the run's deadlines from the sending and from the restart `kr`; a restart of `v` after
`kr` and before `k₀` is excluded by `v`'s activity, and one before `kr` has a deadline at most
`kr`'s; `CatchUpAfterRestartG` gives a delivery `j₀` with no restart of `v` between it and `k₀`, so
after `kr`. The release clause is `delivered`'s (`redelivered_reacted`).

The variables:
- `init`: the node states before a local state is known; `π`: the run; `dl`, `dlW`: the run's
  deadline functions; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `hC`: the run's catch-up
  condition; `hRe`: the run's re-delivery condition; `hAll`: every envelope an honest validator puts
  on the wire is addressed to every validator; `hSkew`: every clock change is within the bounds;
  `hW`: `dlW` does not decrease; `hcu`: the run's deadlines are at least `ΔClockAhead` before the
  trace's.

Read aloud: when the network of `π` re-delivers every earlier envelope to a node that restarted,
after the deadlines from the sending and from its restarts, the trace of `π` meets the trace layer's
catch-up promise at a catch-up deadline leaving room for the clocks. -/
theorem toTrace_caught_up {dl dlW : (m : Msg) → (t : ℝ) → ℝ} {ΔClockAhead ΔClockBehind : ℝ}
    {catchUp : (sm : Framework.StsMultisetLog.SignedMsg Node Msg) → (a : ℝ) → (t : ℝ) → Option ℝ}
    {release : (m : Msg) → Option ℕ} {ΔRedeliver : ℕ} {ok : (m : Msg) → Prop}
    (hC : RStsVariant2.CatchUpAfterRestartG RStsVariant2.TickStepG dl dlW π)
    (hRe : RedeliveredAfterReleaseFromDelivery release (ΔRedeliver : ℝ) π)
    (hAll : ∀ (i : ℕ) (e : Envelope Node Msg), e ∈ π[i + 1].sent - π[i].sent →
      e.sender ∉ π[i].adv → ∀ v : Node, e.recipients.Has v)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hW : ∀ m : Msg, Monotone (dlW m))
    (hcu : ∀ (sm : Framework.StsMultisetLog.SignedMsg Node Msg) (a t' c : ℝ), ok sm.msg →
      catchUp sm a t' = some c → dl sm.msg a + ΔClockAhead ≤ c ∧ dlW sm.msg t' + ΔClockAhead ≤ c) :
    GoldilocksCorrectness.Statements.AbstractTrace.CatchUpAfterRestartBy (activityOf π)
      (toTrace init π) catchUp release ΔRedeliver ok := by
  classical
  intro i k v sm t keep c k' c' hHS hok hk hik hc hkk' hk' hcc' hact hprem
  obtain ⟨i₀, e, rfl, he, rfl⟩ := exists_envelope_of_putsAt init π hHS.1
  have hsadv : e.sender ∉ π[i₀].adv := by
    have := hHS.2
    rwa [corrupted_activityOf_newIdx] at this
  obtain ⟨kr, rfl, hlr, -⟩ := exists_of_lbl_restart init π hk
  obtain ⟨k₀, rfl, hlk, hck⟩ := exists_of_lbl_tick init π hk'
  have hi : i₀ < kr := (newIdx_strictMono π).lt_iff_lt.1 hik
  have hkk : kr < k₀ := (newIdx_strictMono π).lt_iff_lt.1 hkk'
  have hact' : ∀ j : ℕ, newIdx π kr + 1 ≤ j → j ≤ newIdx π k₀ → v ∈ (activityOf π).active j :=
    fun j h1 h2 => hact j (by omega) h2
  have hup := up_of_active_window π hact'
  obtain ⟨hcd, hcw⟩ := hcu _ _ _ _ hok hc
  rw [toTrace_time_newIdx_succ] at hcd
  rw [toTrace_time_newIdx] at hcw
  change dl e.msg (π.stamp (i₀ + 1)) + ΔClockAhead ≤ c at hcd
  change dlW e.msg (π.stamp (kr + 1)) + ΔClockAhead ≤ c at hcw
  have htick : (c' : ℝ) - ΔClockAhead ≤ π.stamp (k₀ + 1) :=
    le_stamp_of_clock π ΔClockAhead ΔClockBehind hSkew hck
  have hdue : RStsVariant2.DueByG dl π i₀ e (π.stamp (k₀ + 1)) := ⟨he, by
    show dl e.msg (π.stamp (i₀ + 1)) ≤ π.stamp (k₀ + 1)
    linarith⟩
  have hdueW : ∀ (l : ℕ) (keep' : Bool), i₀ < l → l < k₀ → π.lbl l = .restart v keep' →
      dlW e.msg (π.stamp (l + 1)) ≤ π.stamp (k₀ + 1) := by
    intro l keep' hl1 hl2 hl
    rcases le_or_gt l kr with hle | hgt
    · have := hW e.msg (π.stamp_mono (show l + 1 ≤ kr + 1 by omega))
      show dlW e.msg (π.stamp (l + 1)) ≤ π.stamp (k₀ + 1)
      linarith
    · exact absurd hl (not_restart_of_up π (hup l hgt hl2.le).1)
  obtain ⟨j₀, hjk₀, hlj₀, hnr⟩ := hC k₀ v hlk i₀ e (by omega) (hAll i₀ e he hsadv v)
    ⟨kr, keep, hi, hkk, hlr⟩ hdue hdueW
  have hkj₀ : kr < j₀ := by
    rcases lt_trichotomy j₀ kr with h | h | h
    · exact absurd hlr (hnr kr keep h hkk)
    · subst h
      have hc : (Action.deliver v e : Action Node Msg Ev) = .restart v keep :=
        hlj₀.symm.trans hlr
      cases hc
    · exact h
  have hupj₀ := hup j₀ hkj₀ hjk₀.le
  have hdelj₀ : (toTrace init π).lbl (newIdx π j₀) = Event.deliver v (traceMsg e) := by
    rw [toTrace_lbl_newIdx]
    exact (eventOf_eq_deliver π).2 ⟨e, hlj₀, rfl, hupj₀.1.1, hupj₀.1.2, hupj₀.2⟩
  by_cases hcase : ∀ r : ℕ, release e.msg = some r → r ≤ c' →
      (toTrace init π).ReactedAtLeast (newIdx π j₀) v r
  · refine ⟨newIdx π j₀, newIdx_lt π hkj₀, newIdx_lt π hjk₀, hdelj₀, hcase, ?_⟩
    intro l t' hl1 hl2 hl
    obtain ⟨l₀, rfl, hl₀, -⟩ := exists_of_lbl_restart init π hl
    exact hnr l₀ false ((newIdx_strictMono π).lt_iff_lt.1 hl1)
      ((newIdx_strictMono π).lt_iff_lt.1 hl2) hl₀
  · push Not at hcase
    obtain ⟨r, hrel, hrt, hnreact⟩ := hcase
    obtain ⟨j, hkj, hjk, hlj, hreact, hnres⟩ := redelivered_reacted init π hRe hact' he hsadv
      hkj₀ hjk₀ hlj₀ hlk hck hrel hrt hnreact hprem
    have hupj := hup j hkj hjk.le
    refine ⟨newIdx π j, newIdx_lt π hkj, newIdx_lt π hjk, ?_, ?_, ?_⟩
    · rw [toTrace_lbl_newIdx]
      exact (eventOf_eq_deliver π).2 ⟨e, hlj, rfl, hupj.1.1, hupj.1.2, hupj.2⟩
    · intro r' hr' _
      have hr'' : release e.msg = some r' := hr'
      rw [hrel] at hr''
      cases hr''
      exact hreact
    · intro l t' hl1 hl2 hl
      obtain ⟨l₀, rfl, hl₀, -⟩ := exists_of_lbl_restart init π hl
      exact hnres l₀ false ((newIdx_strictMono π).lt_iff_lt.1 hl1)
        ((newIdx_strictMono π).lt_iff_lt.1 hl2) hl₀

end Fields

/-! ## 5. The sync fact -/

section Sync

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} (init : (v : Node) → NodeState) (π : Exec Pr)

/-- `v`'s clock value on the trace after `j` steps is at most its clock reading `c` in any
configuration of `π` from `origBefore π j` on: the clock value is the reading of `v`'s last tick or
restart before `j`, a step of `π` before configuration `origBefore π j`, and a clock never goes back
along a run (`Execution.clock_le_of_le`); with no such step it is `0`.

The variables:
- `j`: the trace step; `i`: the configuration of `π`; `v`: the validator; `c`: the reading;
  `hi`: `origBefore π j ≤ i`; `h`: `v`'s clock reads `c` in configuration `i`.

Read aloud: the trace's clock value is never ahead of the run's clock. -/
theorem clockValue_le_of_clock :
    ∀ (j i : ℕ) (v : Node) (c : ℕ), origBefore π j ≤ i → π[i].clock v = some c →
      (toTrace init π).clockValue j v ≤ c := by
  intro j
  induction j with
  | zero => intro i v c _ _; simp
  | succ j ih =>
    intro i v c hi h
    by_cases ht : ∃ t : ℕ, (toTrace init π).lbl j = Event.tick v t
    · obtain ⟨t, ht⟩ := ht
      rw [(toTrace init π).clockValue_succ_of_tick ht]
      obtain ⟨k, rfl, -, hck⟩ := exists_of_lbl_tick init π ht
      rw [origBefore_newIdx_succ] at hi
      exact π.clock_le_of_le hck h (by omega)
    by_cases hr : ∃ (t : ℕ) (keep : Bool), (toTrace init π).lbl j = Event.restart v t keep
    · obtain ⟨t, keep, hr⟩ := hr
      rw [(toTrace init π).clockValue_succ_of_restart hr]
      obtain ⟨k, rfl, -, hck⟩ := exists_of_lbl_restart init π hr
      rw [origBefore_newIdx_succ] at hi
      exact π.clock_le_of_le hck h (by omega)
    rw [(toTrace init π).clockValue_succ_of_not (fun t h => ht ⟨t, h⟩)
      (fun t keep h => hr ⟨t, keep, h⟩)]
    exact ih i v c ((origBefore_mono π (Nat.le_succ j)).trans hi) h

/-- An envelope on the wire in configuration `j` of `π` was put on the wire by a step `i₀ < j`:
nothing is on the wire at the start.

The variables:
- `j`: the configuration; `e`: the envelope; `h`: `e` is on the wire in configuration `j`. -/
theorem exists_put_of_mem_sent {j : ℕ} {e : Envelope Node Msg} (h : e ∈ π[j].sent) :
    ∃ i₀ : ℕ, i₀ < j ∧ e ∈ π[i₀ + 1].sent - π[i₀].sent := by
  induction j with
  | zero =>
    rw [show π[0].sent = 0 from π.init.2.2.2] at h
    simp at h
  | succ j ih =>
    by_cases hj : e ∈ π[j].sent
    · obtain ⟨i₀, hi, hm⟩ := ih hj
      exact ⟨i₀, by omega, hm⟩
    · refine ⟨j, Nat.lt_succ_self j, ?_⟩
      have h1 := Multiset.count_pos.2 h
      have h0 := Multiset.count_eq_zero.2 hj
      rw [← Multiset.count_pos, Multiset.count_sub]
      omega

/-- The trace layer's `SyncedWithinBy` on `toTrace init π` and `activityOf π`, from the run's
`SyncedWithinByG TickStepG servesR sync π`, for any selections and deadlines related as follows.

- The trace's selection `servesT` is read at a node's clock value (its last tick's or restart's
  reading), the run's `servesR` at its clock reading, which is at least the clock value
  (`clockValue_le_of_clock`). `hT`: what the trace's selection serves at a reading, the run's serves
  at every later reading (read for the holder). `hR`: what the run's serves at a reading, the trace's
  serves at every earlier reading (read for the receiver and for the holder's earlier state).
- `hdl`: the run's deadline `sync o t` at the real time `t` is at least `ΔClockAhead` before the
  trace's deadline at the clock value `⌈t⌉₊`, so that the receiver's tick to a reading at least the
  trace's deadline is at a real time at least the run's (`le_stamp_of_clock`); `htdl`: the run's
  deadline of an object of the class `ok` is not before `t`.
- `hon`: the run's deadline is at most `ΔHolderOnline` after `⌈t⌉₊`, so that the holder, active
  until then, is not corrupted at the delivery, and the delivered envelope was put on the wire by an
  honest holder: the re-delivery condition then applies to it.

Route: the trace's last step `k` before `t` is a step of the kind `other`, so the configuration of
`π` in force at `t` is `origBefore π k` (`toTrace_time_mem`); there the holder is up and honest with
the local state `l` and clock reading `c`, and serves `o` by `servesR` (`hT`); the receiver's tick
`k'` is a tick `k₀` of `π` at a real time at least the run's deadline, and the trace's activity of the
receiver from `t` to `k'` gives `UpAndHonestUntilActingG` on the run. The run's condition gives either
that the receiver already serves `o` (`hR`), or a delivery `j₀ < k₀` after a configuration `i'`
entered before `t` from which the holder served `o` (the trace step `2 i' + ⌊π.stamp i'⌋₊` enters it,
`origBefore_entry`; `hR`), with the receiver up and honest from `j₀` to `k₀` (from the run's clause
up to the first tick at or after the deadline, and from the trace's activity from `t` on). When the
delivery found the receiver not yet reacted to the release reading, `redelivered_reacted_of_up`
gives the re-delivery after the receiver's first tick at a reading at least it.

The variables:
- `init`: the node states before a local state is known; `π`: the run; `servesR`, `servesT`: the
  run's and the trace's selections; `sync`, `syncT`: the run's and the trace's sync deadlines; `ok`:
  the class of objects; `release`, `ΔRedeliver`: the release readings and the re-delivery delay;
  `ΔHolderOnline`: how long the trace asks the holder to stay active; `ΔClockAhead`,
  `ΔClockBehind`: the clock bounds; `hS`, `hRe`, `hSkew`: the conditions on `π`.

Read aloud: when the network of `π` brings what an honest node that is up serves to every node up
and honest until it ticks after the sync deadline, and re-delivers a message that came too early for
its release, the trace of `π` meets the trace layer's sync promise, for selections that agree across
the two readings of the clock and deadlines that leave room for the clocks. -/
theorem toTrace_syncedWithinBy [Fintype Node]
    {servesR : ℕ → Local Node Msg NodeState → Msg → Prop}
    {servesT : NodeState → ℕ → Msg → Prop} {sync : (m : Msg) → (t : ℝ) → ℝ}
    {syncT : Node → Framework.StsMultisetLog.SignedMsg Node Msg → ℕ → Option ℕ}
    {ok : (m : Msg) → Prop} {release : (m : Msg) → Option ℕ} {ΔRedeliver : ℕ}
    {ΔHolderOnline ΔClockAhead ΔClockBehind : ℝ}
    (hS : RStsVariant2.SyncedWithinByG RStsVariant2.TickStepG servesR sync π)
    (hRe : RedeliveredAfterReleaseFromDelivery release (ΔRedeliver : ℝ) π)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hT : ∀ (l : Local Node Msg NodeState) (c c' : ℕ) (o : Msg), c ≤ c' → servesT l.st c o →
      servesR c' l o)
    (hR : ∀ (l : Local Node Msg NodeState) (c c' : ℕ) (o : Msg), c ≤ c' → servesR c' l o →
      servesT l.st c o)
    (hdl : ∀ (w u : Node) (o : Msg) (t : ℝ) (d : ℕ), ok o → syncT w ⟨u, o⟩ ⌈t⌉₊ = some d →
      sync o t + ΔClockAhead ≤ d)
    (htdl : ∀ (o : Msg) (t : ℝ), ok o → t ≤ sync o t)
    (hon : ∀ (o : Msg) (t : ℝ), ok o → sync o t ≤ ⌈t⌉₊ + ΔHolderOnline) :
    GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinBy (activityOf π) (toTrace init π)
      servesT ok release ΔRedeliver syncT ΔHolderOnline := by
  classical
  intro t k u w o d d' k' hkt hkt1 hu ho hok honT hd hk' hdd hwin hprem
  -- the configuration of `π` in force at `t`
  have hnot : ¬ ∃ i' : ℕ, newIdx π i' = k := by
    rintro ⟨i', rfl⟩
    rw [toTrace_time_newIdx] at hkt
    rw [toTrace_time_newIdx_succ] at hkt1
    linarith
  have hmem := toTrace_time_mem init π k
  have hmem1 := toTrace_time_mem init π (k + 1)
  rw [origBefore_succ_of_not π hnot] at hmem1
  have hin : RStsVariant2.InForceG π (origBefore π k) t :=
    ⟨by show π.stamp _ < t; linarith [hmem.1], by show t ≤ π.stamp _; linarith [hmem1.2]⟩
  -- the holder there
  rw [mem_active_activityOf] at hu
  obtain ⟨⟨hucr, hukn⟩, huadv⟩ := hu
  obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.mp hukn
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp
    (π.clock_ne_none_of_getElem_ne_none (origBefore π k) u (by rw [hl]; exact Option.some_ne_none _))
  rw [toTrace_st, lastKnownSt_of_some init π hl] at ho
  have hsR : servesR c l o :=
    hT l _ c o (clockValue_le_of_clock init π k _ u c le_rfl hc) ho
  -- the receiver's tick, at a real time at least the run's deadline
  obtain ⟨k₀, rfl, hlk₀, hck₀⟩ := exists_of_lbl_tick init π hk'
  have hk₀time : (d' : ℝ) - ΔClockAhead ≤ π.stamp (k₀ + 1) :=
    le_stamp_of_clock π ΔClockAhead ΔClockBehind hSkew hck₀
  have hdl' := hdl w u o t d hok hd
  have hdd' : (d : ℝ) ≤ d' := by exact_mod_cast hdd
  have hlate : sync o t ≤ π.stamp (k₀ + 1) := by linarith
  have hk₀act : RStsVariant2.TickStepG π k₀ w := hlk₀
  -- the receiver is up and honest from `t` until it ticks at or after the deadline
  have hUA : RStsVariant2.UpAndHonestUntilActingG RStsVariant2.TickStepG π t (sync o t) w := by
    intro n hn hbefore
    have hnk : n ≤ k₀ := hbefore k₀ hk₀act hlate
    have h := hwin (newIdx π n) (by rw [toTrace_time_newIdx]; exact hn)
      ((newIdx_strictMono π).monotone hnk)
    rw [mem_active_activityOf, origBefore_newIdx] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  rcases hS t (origBefore π k) u w o c l hin hucr huadv hl hc hsR hUA with
    ⟨c'', l'', hl'', hc'', hs''⟩ |
    ⟨j₀, i', e, c', l', hij, hit, hl', hc', hs', hlbl, hsend, hmsg, hjs, hjk, hup⟩
  · left
    rw [toTrace_st, lastKnownSt_of_some init π hl'']
    exact hR l'' _ c'' o (clockValue_le_of_clock init π k _ w c'' le_rfl hc'') hs''
  right
  have hlbl' : π.lbl j₀ = .deliver w e := hlbl
  have hj₀k₀ : j₀ < k₀ := hjk k₀ hk₀act hlate
  -- the receiver is up and honest from the delivery to its tick
  have hupw : ∀ n : ℕ, j₀ ≤ n → n ≤ k₀ →
      (w ∉ π[n].crashed ∧ π[n][w] ≠ none) ∧ w ∉ π[n].adv := by
    intro n h1 h2
    by_cases hnt : t ≤ π.stamp (n + 1)
    · have h := hwin (newIdx π n) (by rw [toTrace_time_newIdx]; exact hnt)
        ((newIdx_strictMono π).monotone h2)
      rwa [mem_active_activityOf, origBefore_newIdx] at h
    · have hnt' : π.stamp (n + 1) < t := lt_of_not_ge hnt
      have hb : ∀ k : ℕ, RStsVariant2.TickStepG π k w →
          sync o t ≤ RStsVariant2.Observable.stamp π (k + 1) → n ≤ k := by
        intro k _ hk2
        by_contra hcon
        have := π.stamp_mono (show k + 1 ≤ n + 1 by omega)
        have : π.stamp (k + 1) ≥ t := le_trans (htdl o t hok) hk2
        linarith
      obtain ⟨a, b, cc⟩ := hup n h1 hb
      exact ⟨⟨a, b⟩, cc⟩
  have hactFrom : ∀ j : ℕ, j₀ ≤ j → ∀ L : ℕ, newIdx π j ≤ L → L ≤ newIdx π k₀ →
      w ∈ (activityOf π).active L := by
    intro j hj L h1 h2
    rw [mem_active_activityOf]
    have a1 : j ≤ origBefore π L := by
      have := origBefore_mono π h1
      rwa [origBefore_newIdx] at this
    have a2 : origBefore π L ≤ k₀ := by
      have := origBefore_mono π h2
      rwa [origBefore_newIdx] at this
    exact hupw _ (hj.trans a1) a2
  -- the holder's earlier state, read at the trace step entering configuration `i'`
  obtain ⟨kh, hkh_le, hkh_t, hkh_s⟩ : ∃ kh : ℕ, kh ≤ newIdx π j₀ ∧ (toTrace init π).time kh < t ∧
      servesT ((toTrace init π).st kh u) ((toTrace init π).clockValue kh u) o := by
    refine ⟨2 * i' + ⌊π.stamp i'⌋₊, ?_, ?_, ?_⟩
    · have := Nat.floor_mono (π.stamp_mono (show i' ≤ j₀ + 1 by omega))
      unfold newIdx
      omega
    · rw [toTrace_time_entry]; exact hit
    · rw [toTrace_st, origBefore_entry, lastKnownSt_of_some init π hl']
      exact hR l' _ c' o
        (clockValue_le_of_clock init π _ _ u c' (by rw [origBefore_entry]) hc') hs'
  -- the delivered envelope was put on the wire by the holder, honest then
  have hes : e ∈ π[j₀].sent := by
    have hs := π.step_at j₀
    rw [hlbl'] at hs
    exact hs.deliver_sent.1
  obtain ⟨i₀, hi₀, hput⟩ := exists_put_of_mem_sent π hes
  have hu_j₀ : u ∉ π[j₀].adv := by
    by_cases hjt : t ≤ π.stamp (j₀ + 1)
    · have hjs' : π.stamp (j₀ + 1) ≤ sync o t := hjs
      have h := honT (newIdx π j₀) (by rw [toTrace_time_newIdx]; exact hjt)
        (by rw [toTrace_time_newIdx]; linarith [hon o t hok])
      rw [mem_active_activityOf, origBefore_newIdx] at h
      exact h.2
    · have hji : j₀ < origBefore π k := by
        by_contra hcon
        have := π.stamp_mono (show origBefore π k + 1 ≤ j₀ + 1 by omega)
        have h2 : t ≤ π.stamp (origBefore π k + 1) := hin.2
        linarith [lt_of_not_ge hjt]
      exact fun h => huadv (π.adv_mono hji.le h)
  have hsadv : e.sender ∉ π[i₀].adv := by
    rw [hsend]
    exact fun h => hu_j₀ (π.adv_mono hi₀.le h)
  have hdel : ∀ j : ℕ, j₀ ≤ j → j < k₀ → π.lbl j = .deliver w e →
      (toTrace init π).lbl (newIdx π j) = Event.deliver w ⟨u, o⟩ := by
    intro j h1 h2 hl
    have hw := hupw j h1 h2.le
    rw [toTrace_lbl_newIdx]
    exact (eventOf_eq_deliver π).2
      ⟨e, hl, by simp [traceMsg, hsend, hmsg], hw.1.1, hw.1.2, hw.2⟩
  by_cases hcase : ∀ r : ℕ, release o = some r → r ≤ d' →
      (toTrace init π).ReactedAtLeast (newIdx π j₀) w r
  · exact ⟨newIdx π j₀, kh, hkh_le, hkh_t, hkh_s, hdel j₀ le_rfl hj₀k₀ hlbl',
      newIdx_lt π hj₀k₀, hcase, hactFrom j₀ le_rfl⟩
  obtain ⟨r, hrel, hrd, hnreact⟩ : ∃ r : ℕ, release o = some r ∧ r ≤ d' ∧
      ¬ (toTrace init π).ReactedAtLeast (newIdx π j₀) w r := by
    by_contra hne
    exact hcase fun r h1 h2 => by
      by_contra h3
      exact hne ⟨r, h1, h2, h3⟩
  have hrel' : release e.msg = some r := by rw [hmsg]; exact hrel
  obtain ⟨j₁, hj01, hj1k, hlj₁, hreact, -⟩ := redelivered_reacted_of_up init π hRe
    hupw hput hsadv hj₀k₀ hlbl' hlk₀ hck₀ hrel' hrd hnreact
    (fun k₁ t₁ h1 h2 h3 h4 h5 => hprem r (newIdx π j₀) k₁ t₁ hrel
      (hdel j₀ le_rfl hj₀k₀ hlbl') hnreact h1 h2 h3 h4 h5)
  refine ⟨newIdx π j₁, kh, hkh_le.trans ((newIdx_strictMono π).monotone hj01.le), hkh_t, hkh_s,
    hdel j₁ hj01.le hj1k hlj₁, newIdx_lt π hj1k, fun r' hr' _ => ?_, hactFrom j₁ hj01.le⟩
  obtain rfl : r = r' := Option.some.inj (hrel.symm.trans hr')
  exact hreact

omit [DecidableEq Node] [DecidableEq Msg] in
/-- The two relations `toTrace_syncedWithinBy` asks of the selections make the trace's selection
independent of the reading, on every node state of a local state: by `hT` it serves at the larger of
the two readings what it serves at one, and by `hR` at the other what it serves at the larger.

The variables:
- `servesR`, `servesT`: the run's and the trace's selections; `hT`, `hR`: the two relations;
  `l`: the local state; `c`, `c'`: two readings; `o`: the object.

Read aloud: a selection that agrees across the run's and the trace's readings of the clock in both
directions does not depend on the reading. -/
theorem servesT_reading_free_of_relations
    {servesR : ℕ → Local Node Msg NodeState → Msg → Prop}
    {servesT : NodeState → ℕ → Msg → Prop}
    (hT : ∀ (l : Local Node Msg NodeState) (c c' : ℕ) (o : Msg), c ≤ c' → servesT l.st c o →
      servesR c' l o)
    (hR : ∀ (l : Local Node Msg NodeState) (c c' : ℕ) (o : Msg), c ≤ c' → servesR c' l o →
      servesT l.st c o)
    (l : Local Node Msg NodeState) (c c' : ℕ) (o : Msg) (h : servesT l.st c o) :
    servesT l.st c' o :=
  hR l c' (max c c') o (le_max_right c c') (hT l c (max c c') o (le_max_left c c') h)

end Sync

end GoldilocksVariant.Final
