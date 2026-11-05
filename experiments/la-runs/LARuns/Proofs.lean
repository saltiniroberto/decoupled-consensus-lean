import LARuns.Statements.Statement4OnRuns
import RStsVariant2.Analysis.Lemmas

/-!
# The proofs about LARuns's generic pages

This page holds the proofs about the pages it imports: `LARuns.Statements.Statement4OnRuns` and, through it,
`Trace`, `Environment`, `Statement4Defs`, `Readers` and `Bridge`. Those
pages define and prove nothing; every theorem about them is here.

The theorems say how the trace of a run (`toRealTrace tAwakeEnd π`, `LARuns.Bridge`) reads the run:
its awake set, its views, its events, its sent log and its activity windows, each against what the
run itself has; and the facts about the bare framework's steps they use (a validator's local
state, crashes and corruption across a step, and when a clock changes), proved from
`RStsVariant2.Analysis.Lemmas`.

This page imports `LARuns.Statements.Statement4OnRuns` and `RStsVariant2.Analysis.Lemmas`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace LARuns

open RStsVariant2 (Exec Protocol Execution Config Local Action NodeAction)

/-! ## A. Facts about the bare framework's steps -/

section StepFacts

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev}

/-- A validator whose local state is known keeps it known through every step but its corruption. -/
theorem step_getElem_ne_none {a : Action Node Msg Ev} {c c' : Config Node Msg NodeState}
    (h : RStsVariant2.Step Pr a c c') {v : Node} (hv : c[v] ≠ none) (hcor : a ≠ .corrupt v) :
    c'[v] ≠ none := by
  refine h.elim (motive := fun a d d' => d[v] ≠ none → a ≠ .corrupt v → d'[v] ≠ none)
    ?setClock ?tick ?deliver ?deliverAdv ?corrupt ?crash ?crashDuring ?restart ?custom
    ?adversarial hv hcor
  case setClock => intro d w t _ _ hd _; simpa using hd
  case tick =>
    intro d w l t res _ _ _ _ _ hd _
    rwa [Ne, RStsVariant2.applyNodeStepResult_getElem_eq_none_iff]
  case deliver =>
    intro d w e l t res _ _ _ _ _ _ _ hd _
    rwa [Ne, RStsVariant2.applyNodeStepResult_getElem_eq_none_iff, RStsVariant2.receive_getElem]
  case deliverAdv => intro d w e _ _ _ hd _; rwa [RStsVariant2.receive_getElem]
  case corrupt =>
    intro d w _ hd hc
    have hw : v ≠ w := fun h => hc (by rw [h])
    change (d.setNode w none)[v] ≠ none
    rwa [RStsVariant2.Config.setNode_other _ _ _ _ hw]
  case crash => intro d w _ hd _; exact hd
  case crashDuring =>
    intro d w na k l t res _ _ _ _ hd _
    rwa [Ne, RStsVariant2.applyCrashDuring_getElem, RStsVariant2.applyEffects_getElem_eq_none_iff,
      NodeAction.prepare_getElem]
  case restart =>
    intro d w keep t _ _ _ hd _
    change (d.setNode w _)[v] ≠ none
    rw [RStsVariant2.Config.setNode_apply]
    by_cases hw : w = v
    · rw [if_pos hw]; simp
    · rw [if_neg hw]; exact hd
  case custom =>
    intro d w ev l t res _ _ _ _ _ _ hd _
    rwa [Ne, RStsVariant2.applyNodeStepResult_getElem_eq_none_iff]
  case adversarial => intro d w m r _ hd _; exact hd

/-- A validator not up before a step (crashed, or its local state unknown) and up after it (outside
`crashed`, local state known) was restarted at that step. -/
theorem step_restart_of_up {a : Action Node Msg Ev} {c c' : Config Node Msg NodeState}
    (h : RStsVariant2.Step Pr a c c') {v : Node} (hnot : v ∈ c.crashed ∨ c[v] = none)
    (hc : v ∉ c'.crashed) (hn : c'[v] ≠ none) : ∃ keep : Bool, a = .restart v keep := by
  by_contra hne
  push Not at hne
  rcases hnot with hv | hv
  · exact hc (h.mem_crashed hv hne)
  · apply hn
    by_cases htick : a = .tick v
    · subst htick
      obtain ⟨-, -, l, t, hl, -⟩ := h.up_honest (Or.inl rfl)
      rw [hv] at hl; cases hl
    by_cases hcustom : ∃ ev : Ev, a = .custom v ev
    · obtain ⟨ev, rfl⟩ := hcustom
      obtain ⟨-, -, l, t, hl, -⟩ := h.up_honest (Or.inr (Or.inl ⟨ev, rfl⟩))
      rw [hv] at hl; cases hl
    by_cases hcd : ∃ (na : NodeAction Node Msg Ev) (k : Nat), a = .crashDuring v na k
    · obtain ⟨na, k, rfl⟩ := hcd
      obtain ⟨-, -, l, t, hl, -⟩ := h.up_honest (Or.inr (Or.inr ⟨na, k, rfl⟩))
      rw [hv] at hl; cases hl
    by_cases hdel : ∃ e : RStsVariant2.Envelope Node Msg, a = .deliver v e
    · obtain ⟨e, rfl⟩ := hdel
      by_cases hadv : v ∈ c.adv
      · obtain ⟨-, -, rfl⟩ := h.deliver_eq_of_mem_adv hadv
        rw [RStsVariant2.receive_getElem]; exact hv
      · obtain ⟨-, l, t, hl, -⟩ := h.deliver_up_of_not_mem_adv hadv
        rw [hv] at hl; cases hl
    by_cases hcor : a = .corrupt v
    · subst hcor; exact h.corrupt_eq.2.1
    push Not at hcustom hcd hdel
    rw [h.getElem_eq htick hdel hcustom hcd hcor hne, hv]

/-- A validator up and honest before a step and down or corrupted after it was crashed, crashed
during a reaction, or corrupted at that step. -/
theorem step_lost {a : Action Node Msg Ev} {c c' : Config Node Msg NodeState}
    (h : RStsVariant2.Step Pr a c c') {v : Node} (hc : v ∉ c.crashed) (hn : c[v] ≠ none)
    (ha : v ∉ c.adv) (hlost : v ∈ c'.crashed ∨ c'[v] = none ∨ v ∈ c'.adv) :
    a = .crash v ∨ (∃ (na : NodeAction Node Msg Ev) (k : Nat), a = .crashDuring v na k) ∨
      a = .corrupt v := by
  by_cases hcor : a = .corrupt v
  · exact Or.inr (Or.inr hcor)
  by_cases hcr : a = .crash v
  · exact Or.inl hcr
  by_cases hcd : ∃ (na : NodeAction Node Msg Ev) (k : Nat), a = .crashDuring v na k
  · exact Or.inr (Or.inl hcd)
  push Not at hcd
  exfalso
  rcases hlost with h1 | h1 | h1
  · exact h.not_mem_crashed hc hcr hcd h1
  · exact step_getElem_ne_none h hn hcor h1
  · rcases h.mem_adv_or_corrupt h1 with h2 | h2
    · exact ha h2
    · exact hcor h2

/-- The clock of `v` comes to read `t` at step `i` (it reads `t` after the step and did not before
it) exactly when step `i` is `setClock v t`. -/
theorem clock_change_iff (π : Exec Pr) (i : ℕ) (v : Node) (t : ℕ) :
    (π[i + 1].clock v = some t ∧ π[i].clock v ≠ some t) ↔ π.lbl i = .setClock v t := by
  have hs := π.step_at i
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hset : ∃ t', π.lbl i = .setClock v t'
    · obtain ⟨t', ht'⟩ := hset
      rw [ht'] at hs
      obtain ⟨-, -, heq⟩ := hs.setClock_eq
      rw [heq, RStsVariant2.setClock_clock_self] at h1
      rw [ht', Option.some_injective _ h1]
    · push Not at hset
      by_cases hcor : π.lbl i = .corrupt v
      · rw [hcor] at hs
        obtain ⟨-, -, hnone, -⟩ := hs.corrupt_eq
        rw [hnone] at h1; cases h1
      · exact absurd ((π.clock_succ hset hcor).symm.trans h1) h2
  · intro hl
    rw [hl] at hs
    obtain ⟨-, hlt, heq⟩ := hs.setClock_eq
    refine ⟨by rw [heq, RStsVariant2.setClock_clock_self], fun h0 => ?_⟩
    exact absurd (hlt t h0) (lt_irrefl t)

end StepFacts

/-! ## B. How the bridge reads a run -/

section BridgeFacts

variable {Node Msg NodeState Ev Block : Type} [DecidableEq Node] [DecidableEq Msg] [Fintype Node]
  {Pr : Protocol Node Msg NodeState Ev} [NodeViewOf NodeState Block] [ProtocolCommittees Pr Block]

/-- A validator is awake in configuration `i` of the trace of a run exactly when it is up there:
outside `crashed`, with its local state known.

Read aloud: the trace's awake set is the run's up validators. -/
theorem toRealTrace_awake_iff (tAwakeEnd : ℝ) (π : Exec Pr) (i : ℕ) (v : Node) :
    (toRealTrace tAwakeEnd π).Awake i v ↔ v ∉ π[i].crashed ∧ π[i][v] ≠ none := by
  simp [RealTrace.Awake, toRealTrace, Option.isSome_iff_ne_none]

omit [ProtocolCommittees Pr Block] in
/-- A validator's view in configuration `i` of a run is known exactly when its local state is.

Read aloud: a validator has a view exactly when it has come online and is not corrupted. -/
theorem viewAt_ne_none_iff (π : Exec Pr) (i : ℕ) (v : Node) :
    (NodeViewOf.viewAt π i v : Option (NodeView Block)) ≠ none ↔ π[i][v] ≠ none := by
  simp [NodeViewOf.viewAt, NodeViewOf.viewOf]

/-- The trace's event of step `i` is `v`'s tick at the reading `t` exactly when step `i` is `tick v`
and `v`'s clock reads `t` there.

Read aloud: the trace reads a tick at the reading the clock shows. -/
theorem eventOf_eq_tick_iff (π : Exec Pr) (i : ℕ) (v : Node) (t : ℕ) :
    eventOf π i = .tick v t ↔ π.lbl i = .tick v ∧ π[i].clock v = some t := by
  constructor
  · intro h
    unfold eventOf at h
    split at h
    · rename_i w hl
      split at h
      · rename_i t' ht
        injection h with h1 h2
        subst h1; subst h2
        exact ⟨hl, ht⟩
      · cases h
    · split at h <;> cases h
    · split at h <;> cases h
    · cases h
  · rintro ⟨hl, ht⟩
    unfold eventOf
    simp only [hl, ht]

/-- The trace's event of step `i` is `v`'s restart at the reading `t` exactly when step `i` is
`restart v keep` and `v`'s clock reads `t` there.

Read aloud: the trace reads a restart at the reading the clock shows. -/
theorem eventOf_eq_restart_iff (π : Exec Pr) (i : ℕ) (v : Node) (t : ℕ) (keep : Bool) :
    eventOf π i = .restart v t keep ↔ π.lbl i = .restart v keep ∧ π[i].clock v = some t := by
  constructor
  · intro h
    unfold eventOf at h
    split at h
    · split at h <;> cases h
    · rename_i w k hl
      split at h
      · rename_i t' ht
        injection h with h1 h2 h3
        subst h1; subst h2; subst h3
        exact ⟨hl, ht⟩
      · cases h
    · split at h <;> cases h
    · cases h
  · rintro ⟨hl, ht⟩
    unfold eventOf
    simp only [hl, ht]

/-- The trace's event of step `i` is the delivery of `y` to `v` exactly when step `i` delivers to
`v` an envelope `e` that the bridge reads as `y`, and `v` is up and honest there.

Read aloud: the trace reads a delivery only to a validator that is up and honest. -/
theorem eventOf_eq_deliver_iff (π : Exec Pr) (i : ℕ) (v : Node) (y : Envelope Node Msg) :
    eventOf π i = .deliver v y ↔ ∃ e : RStsVariant2.Envelope Node Msg, π.lbl i = .deliver v e ∧
      envelopeOf e = y ∧ v ∉ π[i].crashed ∧ π[i][v] ≠ none ∧ v ∉ π[i].adv := by
  constructor
  · intro h
    unfold eventOf at h
    split at h
    · split at h <;> cases h
    · split at h <;> cases h
    · rename_i w e hl
      split at h
      · rename_i hcond
        injection h with h1 h2
        subst h1; subst h2
        obtain ⟨c1, c2, c3⟩ := hcond
        exact ⟨e, hl, rfl, c1, Option.isSome_iff_ne_none.mp c2, c3⟩
      · cases h
    · cases h
  · rintro ⟨e, hl, rfl, h1, h2, h3⟩
    unfold eventOf
    simp [hl, h1, h3, Option.isSome_iff_ne_none.mpr h2]

/-- A step that is no tick, no delivery and no restart is read by the trace as a step of another
kind.

Read aloud: every other step is `.other` on the trace. -/
theorem eventOf_eq_other_of (π : Exec Pr) (i : ℕ) (htick : ∀ p : Node, π.lbl i ≠ .tick p)
    (hdel : ∀ (p : Node) (e : RStsVariant2.Envelope Node Msg), π.lbl i ≠ .deliver p e)
    (hrestart : ∀ (p : Node) (keep : Bool), π.lbl i ≠ .restart p keep) : eventOf π i = .other := by
  unfold eventOf
  split
  · rename_i w hl; exact absurd hl (htick w)
  · rename_i w k hl; exact absurd hl (hrestart w k)
  · rename_i w e hl; exact absurd hl (hdel w e)
  · rfl

/-- The bridge's reading of the recipients is injective.

Read aloud: two recipient lists read the same only if they are the same. -/
theorem recipientsOf_injective : Function.Injective (recipientsOf (Node := Node)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [recipientsOf]

/-- The bridge's reading of an envelope is injective.

Read aloud: two envelopes read the same only if they are the same. -/
theorem envelopeOf_injective : Function.Injective (envelopeOf (Node := Node) (Msg := Msg)) := by
  rintro ⟨⟨s, m⟩, r⟩ ⟨⟨s', m'⟩, r'⟩ h
  simp only [envelopeOf, Envelope.mk.injEq, SignedMsg.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, hr⟩ := h
  rw [recipientsOf_injective hr]

/-- Every envelope of the trace is the bridge's reading of an envelope of `RStsVariant2`.

Read aloud: the trace has no envelope the run does not have. -/
theorem envelopeOf_surjective (y : Envelope Node Msg) :
    ∃ e : RStsVariant2.Envelope Node Msg, envelopeOf e = y := by
  obtain ⟨⟨s, m⟩, r⟩ := y
  cases r with
  | all => exact ⟨⟨⟨s, m⟩, .all⟩, rfl⟩
  | only ns => exact ⟨⟨⟨s, m⟩, .only ns⟩, rfl⟩

/-- For an injective `f`, `f a` is among the copies `s₁.map f` has more than `s₀.map f` exactly when
`a` is among the copies `s₁` has more than `s₀`.

Read aloud: an injective map keeps which elements were added. -/
theorem mem_map_sub_iff {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (s₁ s₀ : Multiset α) (a : α) :
    f a ∈ s₁.map f - s₀.map f ↔ a ∈ s₁ - s₀ := by
  rw [Multiset.mem_sub, Multiset.mem_sub, Multiset.count_map_eq_count' f _ hf,
    Multiset.count_map_eq_count' f _ hf]

/-- Step `i` of the trace of a run puts the bridge's reading of `e` on the wire exactly when step
`i` of the run adds a copy of `e` to the sent log.

Read aloud: the trace sends what the run sends. -/
theorem puts_envelopeOf_iff (tAwakeEnd : ℝ) (π : Exec Pr) (i : ℕ)
    (e : RStsVariant2.Envelope Node Msg) :
    (toRealTrace tAwakeEnd π).Puts i (envelopeOf e) ↔ e ∈ π[i + 1].sent - π[i].sent :=
  mem_map_sub_iff envelopeOf_injective _ _ e

/-- `v` is active throughout `[t, t']` on the trace of a run exactly when it is up and honest
throughout `[t, t']` on the run (`RStsVariant2.Execution.UpAndHonestThroughout`).

Read aloud: the trace's activity window is the run's. -/
theorem activeThroughout_iff (tAwakeEnd : ℝ) (π : Exec Pr) (t t' : ℝ) (v : Node) :
    (toRealTrace tAwakeEnd π).ActiveThroughout t t' v ↔ π.UpAndHonestThroughout t t' v := by
  constructor
  · intro h i h1 h2
    obtain ⟨ha, hh⟩ := h i ⟨h1, h2⟩
    obtain ⟨hc, hn⟩ := (toRealTrace_awake_iff tAwakeEnd π i v).1 ha
    exact ⟨hc, hn, hh⟩
  · rintro h i ⟨h1, h2⟩
    obtain ⟨hc, hn, hh⟩ := h i h1 h2
    exact ⟨(toRealTrace_awake_iff tAwakeEnd π i v).2 ⟨hc, hn⟩, hh⟩

/-- Every reaction completes, on the trace of every run: after a step that `toRealTrace tAwakeEnd π`
reads as a tick, a delivery or a restart of `v`, `v` is awake, whatever `π` is (a reaction
interrupted by a crash is read as `.other`). -/
theorem up_after_reaction (tAwakeEnd : ℝ) (π : Exec Pr) (i : ℕ) (v : Node)
    (hs : (toRealTrace tAwakeEnd π).ActingStep i v ∨
      (∃ y : Envelope Node Msg, (toRealTrace tAwakeEnd π).action i = .deliver v y) ∨
      ∃ (t : ℕ) (keep : Bool), (toRealTrace tAwakeEnd π).action i = .restart v t keep) :
    (toRealTrace tAwakeEnd π).Awake (i + 1) v := by
  rw [toRealTrace_awake_iff]
  have hstep := π.step_at i
  have keep_up : v ∉ π[i].crashed → π[i][v] ≠ none → v ∉ π[i].adv →
      π.lbl i ≠ .crash v → (∀ (na : NodeAction Node Msg Ev) (k : Nat), π.lbl i ≠ .crashDuring v na k) →
      π.lbl i ≠ .corrupt v → v ∉ π[i + 1].crashed ∧ π[i + 1][v] ≠ none := by
    intro hc hn ha h1 h2 h3
    by_contra hne
    rw [not_and_or, not_not, not_not] at hne
    rcases step_lost hstep hc hn ha (hne.elim Or.inl (fun h => Or.inr (Or.inl h))) with
      h | ⟨na, k, h⟩ | h
    · exact h1 h
    · exact h2 na k h
    · exact h3 h
  rcases hs with ⟨t, ht⟩ | ⟨y, hy⟩ | ⟨t, keep, hr⟩
  · obtain ⟨hl, -⟩ := (eventOf_eq_tick_iff π i v t).1 ht
    rw [hl] at hstep
    obtain ⟨ha, hc, l, t', hl', -⟩ := hstep.up_honest (Or.inl rfl)
    exact keep_up hc (by rw [hl']; simp) ha (by rw [hl]; simp) (by rw [hl]; simp) (by rw [hl]; simp)
  · obtain ⟨e, hl, -, hc, hn, ha⟩ := (eventOf_eq_deliver_iff π i v y).1 hy
    exact keep_up hc hn ha (by rw [hl]; simp) (by rw [hl]; simp) (by rw [hl]; simp)
  · obtain ⟨hl, -⟩ := (eventOf_eq_restart_iff π i v t keep).1 hr
    rw [hl] at hstep
    obtain ⟨-, -, t', -, hv, -, -, -, hcr, -⟩ := hstep.restart_eq
    rw [hcr, hv]
    simp

end BridgeFacts

end LARuns
