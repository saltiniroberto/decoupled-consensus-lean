import Proofs.Instance.Model
import Proofs.Instance.NoRaise.Tick
import Model.Record.Wiring
import Model.Record.NodeFacts
import Model.Record.NodeFactsWake

/-!
# The run facts of the no-raise invariant at `Model.spec`

Proofs of five fields of `NodeRunFacts` at the model `Model.spec`: `tick_outcome_sts`,
`run_fact_g1_at`, `run_fact_g2_at`, `tick_emits_proposal_inclX` and `stateBeforeOf_runs_as`. They
rest on two invariants of an execution: a validator not held by the adversary and awake throughout
`[w, now]` records a wake time at or before `w` (`inv_awake`); and, when honest proposers hold no
block with their proposal's root, such a validator has its grades due and a clock trailing the time
by less than one delay (`inv_due`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SpecRecord.NoRaise

open Spec Spec.Protocol
open DC (DRE)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An `optStep` that answers keeps a property `Q` of its argument when the step, if taken, gives
    `Q` to every answer. -/
private theorem optStep_post {α : Type} (c : Prop) [Decidable c] (f : α → DREB V α)
    (Q : α → Prop) {a : α} {l : List (NamedObject V)} {out : α × List (NamedObject V)}
    (h : (optStep c f a).run l = .ok out) (ha : Q a)
    (hf : c → ∀ l' (out' : α × List (NamedObject V)), (f a).run l' = .ok out' → Q out'.1) :
    Q out.1 := by
  unfold optStep at h
  split_ifs at h with hc
  · exact hf hc l out h
  · rw [DREB.pure_run_ok_iff] at h
    subst h
    exact ha

/-- The block a proposal builds has the root `X.new_root v st.s`. -/
private theorem build_proposal_root {C : Config} {X : External V} {v : V} {st : Store V}
    {B : Block V} (h : build_proposal C X v st = .ok B) : B.root = X.new_root v st.s := by
  unfold build_proposal at h
  obtain ⟨input, hi, h⟩ := DRE.ok_of_bind h
  obtain ⟨rows, -, h⟩ := DRE.ok_of_bind h
  cases h
  unfold proposal_input at hi
  obtain ⟨sv, -, hi⟩ := DRE.ok_of_bind hi
  obtain ⟨H, -, hi⟩ := DRE.ok_of_bind hi
  cases hi
  rfl

/-- An answer of the proposal duty meets `StoreOk` when its input store does and no block of the
    input tree has the proposer's new root for the store's slot. -/
private theorem storeOk_propose_block {C : Config} {P : Provisional V} {X : External V} {v : V}
    {st : Store V} {l : List (NamedObject V)} {out : Store V × List (NamedObject V)}
    (h : (propose_block C P X v st).run l = .ok out) (hok : StoreOk st)
    (hroot : ∀ B ∈ st.T, B.root ≠ X.new_root v st.s) : StoreOk out.1 := by
  unfold propose_block at h
  cases hb : build_proposal C X v st with
  | error e => rw [hb] at h; cases h
  | ok B =>
    rw [hb] at h
    have h2 : (Except.ok (on_block C P st B, l ++ [NamedObject.block B]) :
        DRE (Store V × List (NamedObject V))) = Except.ok out := h
    cases h2
    refine SpecRecord.OkStore.on_block C P hok ?_
    rintro ⟨B', hB', -, hr⟩
    exact hroot B' hB' (hr.trans (build_proposal_root hb))

/-- An answer of the Goldfish vote duty meets `StoreOk` when its input store does. -/
private theorem storeOk_goldfish_vote {C : Config} {P : Provisional V} {v : V} {st : Store V}
    {l : List (NamedObject V)} {out : Store V × List (NamedObject V)}
    (h : (goldfish_vote C P v st).run l = .ok out) (hok : StoreOk st) : StoreOk out.1 := by
  unfold goldfish_vote at h
  dsimp only at h
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨_, _, -, h⟩ := h
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨_, _, -, h⟩ := h
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨_, _, -, h⟩ := h
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨H, _, -, h⟩ := h
  split_ifs at h
  · rw [DREB.run_bind_ok_iff] at h
    obtain ⟨_, _, -, h⟩ := h
    rw [DREB.pure_run_ok_iff] at h
    subst h
    exact SpecRecord.OkStore.on_goldfish_vote_checked P hok _
  · rw [DREB.pure_run_ok_iff] at h
    subst h
    exact hok

/-- An answer of the attestation duty meets `StoreOk` when its input store does. -/
private theorem storeOk_attest {C : Config} {v : V} {st : Store V} {sh : SigningHistory}
    {l : List (NamedObject V)} {out : (Store V × SigningHistory) × List (NamedObject V)}
    (h : (attest C v st sh).run l = .ok out) (hok : StoreOk st) : StoreOk out.1.1 := by
  unfold attest at h
  dsimp only at h
  cases hb : build_attestation C v st sh with
  | error e => rw [hb] at h; cases h
  | ok p =>
    rw [hb] at h
    have h2 : (Except.ok ((admit_attestation C st p.2, p.1), l ++ [NamedObject.attest p.2]) :
        DRE ((Store V × SigningHistory) × List (NamedObject V))) = Except.ok out := h
    cases h2
    exact SpecRecord.OkStore.admit_attestation C hok p.2

/-- The tick keeps `StoreOk` when its proposal, if it runs, gives a root that no block of the tree
    has. -/
private theorem storeOk_tick {C : Config} {P : Provisional V} {X : External V} {n : NodeState V}
    {t : Time} {out : NodeState V × List (NamedObject V)}
    (h : (tick C P X n t).run [] = .ok out) (hok : StoreOk n.st)
    (hroot : C.slotOf t > 0 →
      (decide (t = C.proposal_time (C.slotOf t)) &&
        decide (P.proposer (C.slotOf t) = (record_awake n t).v) &&
        (record_awake n t).awake_since (grade1_window_start C (C.round_of (C.slotOf t)))) = true →
      ∀ B ∈ n.st.T, B.root ≠ X.new_root n.v (C.slotOf t)) :
    StoreOk out.1.st := by
  rw [tick_eq_tickSteps] at h
  unfold tickSteps at h
  dsimp only at h
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨st0, l0, h0, h⟩ := h
  rw [DREB.liftM_run_ok_iff] at h0
  obtain ⟨h0, rfl⟩ := h0
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨st4, l3, h3, h⟩ := h
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨p, l4, h4, h⟩ := h
  rw [DREB.pure_run_ok_iff] at h
  subst h
  have hv : (record_awake n t).v = n.v := by rw [record_awake_eq]
  have hst0 : st0 = { n.st with saved_grades := st0.saved_grades } := by
    have := update_grades_eq h0
    rwa [record_awake_st] at this
  have hok1 : StoreOk ({ st0 with t := t, s := C.slotOf t } : Store V) := by
    rw [hst0]; exact hok
  have hT1 : ({ st0 with t := t, s := C.slotOf t } : Store V).T = n.st.T := by rw [hst0]
  have hok4 : StoreOk st4 := by
    refine optStep_post _ _ StoreOk h3 hok1 ?_
    intro hs l' out' h'
    rw [DREB.run_bind_ok_iff] at h'
    obtain ⟨st2, l2, h2, h'⟩ := h'
    rw [DREB.run_bind_ok_iff] at h'
    obtain ⟨st3, l3', h3', h'⟩ := h'
    have hok2 : StoreOk st2 := by
      refine optStep_post _ _ StoreOk h2 hok1 ?_
      intro hc l'' out'' hp
      refine storeOk_propose_block hp hok1 ?_
      rw [hT1, hv]
      exact hroot hs hc
    have hok3 : StoreOk st3 :=
      optStep_post _ _ StoreOk h3' hok2 (fun _ _ _ hp => storeOk_goldfish_vote hp hok2)
    refine optStep_post _ _ StoreOk h' hok3 ?_
    intro _ l'' out'' hp
    obtain ⟨o1, o2⟩ := out''
    rw [DREB.liftM_run_ok_iff] at hp
    rw [update_confirmation_eq hp.1]
    exact hok3
  have hok5 : StoreOk p.1 :=
    optStep_post _ _ (fun q => StoreOk q.1) h4 hok4 (fun _ _ _ hp => storeOk_attest hp hok4)
  exact hok5

/-- After a wake (`n.awakeSince = none`), `record_awake n t` records `t` as the wake time. -/
private theorem record_awake_of_none {n : NodeState V} {t : Time} (hn : n.awakeSince = none) :
    (record_awake n t).awakeSince = some t := by
  simp [record_awake, Id.run, hn]; rfl

/-- When `awakeSince` is already set, `record_awake` keeps it. -/
private theorem record_awake_of_some {n : NodeState V} {t a : Time} (hn : n.awakeSince = some a) :
    (record_awake n t).awakeSince = some a := by
  simp only [record_awake, Id.run, hn, reduceCtorEq]
  exact hn

/-- The tick right after a wake fails the awake test against every time `w` before its own time `t`. -/
private theorem awake_since_record_of_none {n : NodeState V} {t w : Time}
    (hn : n.awakeSince = none) (hw : w < t) : (record_awake n t).awake_since w = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  obtain ⟨a, ha, hle⟩ := awake_since_eq_true h
  rw [record_awake_of_none hn] at ha
  cases ha
  exact absurd hw (not_lt.mpr hle)

/-- The grade-1 and grade-2 window starts of the round of a non-negative time `t` are before `t`. -/
private theorem window_starts_lt (C : Config) {t : Time} (ht : 0 ≤ t) :
    grade1_window_start C (roundAt C t) < t ∧ grade2_window_start C (roundAt C t) < t := by
  have hΔ := C.Δ_pos
  have h := (opening_le_self C ht).1
  rw [grade1_window_start_eq, grade2_window_start_eq]
  constructor <;> linarith

/-- The tick right after a wake answers, from a stamped store of distinct roots: no duty runs, and
    the grades update answers. -/
private theorem tick_ok_of_none (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (t : Time) (hroots : DistinctRoots n.st.T) (hst : Stamped n.st)
    (hn : n.awakeSince = none) (ht : 0 ≤ t) :
    ∃ out, (tick C P X n t).run [] = .ok out := by
  obtain ⟨hw1, hw2⟩ := window_starts_lt C ht
  have h1 := awake_since_record_of_none hn hw1
  have h2 := awake_since_record_of_none hn hw2
  obtain ⟨st0, h0⟩ : ∃ st0, update_grades C P (record_awake n t).st t = .ok st0 := by
    rw [record_awake_st]; exact update_grades_ok C P hroots hst t
  rw [tick_eq_tickSteps]
  unfold tickSteps
  dsimp only
  rw [StateT.run_bind]
  have hl : (liftM (update_grades C P (record_awake n t).st t) : DREB V (Store V)).run []
      = .ok (st0, []) := by rw [h0]; rfl
  rw [hl, DRE.bind_ok]
  simp only [optStep, h1, h2, Bool.and_false, Bool.false_eq_true, if_false, pure_bind, ite_self]
  exact ⟨_, rfl⟩

/-- An answer of the proposal duty sends one block, appended to the list it was run from. -/
private theorem propose_block_sends {C : Config} {P : Provisional V} {X : External V} {v : V}
    {st : Store V} {l : List (NamedObject V)} {out : Store V × List (NamedObject V)}
    (h : (propose_block C P X v st).run l = .ok out) :
    ∃ B : Block V, out.2 = l ++ [NamedObject.block B] := by
  unfold propose_block at h
  cases hb : build_proposal C X v st with
  | error e => rw [hb] at h; cases h
  | ok B =>
    rw [hb] at h
    have h2 : (Except.ok (on_block C P st B, l ++ [NamedObject.block B]) :
        DRE (Store V × List (NamedObject V))) = Except.ok out := h
    cases h2
    exact ⟨B, rfl⟩

/-- A tick at a slot's proposal time, by the slot's proposer, that passes the grade-1 awake test of
    the slot's round, sends a block whenever it answers. -/
private theorem tick_sends_block {C : Config} {P : Provisional V} {X : External V}
    {n : NodeState V} {t : Time} {out : NodeState V × List (NamedObject V)}
    (h : (tick C P X n t).run [] = .ok out) (hs : C.slotOf t > 0)
    (htime : t = C.proposal_time (C.slotOf t)) (hprop : P.proposer (C.slotOf t) = n.v)
    (hawake : (record_awake n t).awake_since
      (grade1_window_start C (C.round_of (C.slotOf t))) = true) :
    ∃ B : Block V, NamedObject.block B ∈ out.2 := by
  have hv : (record_awake n t).v = n.v := by rw [record_awake_eq]
  have hΔ := C.Δ_pos
  rw [tick_eq_tickSteps] at h
  unfold tickSteps at h
  dsimp only at h
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨st0, l0, h0, h⟩ := h
  rw [DREB.liftM_run_ok_iff] at h0
  obtain ⟨-, rfl⟩ := h0
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨st4, l3, h3, h⟩ := h
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨p, l4, h4, h⟩ := h
  rw [DREB.pure_run_ok_iff] at h
  subst h
  have c4 : ¬ ((decide (t = C.round_attestation_time (C.round_of (C.slotOf t))) &&
      (record_awake n t).awake_since
        (grade2_window_start C (C.round_of (C.slotOf t)))) = true) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rintro ⟨h', -⟩
    exact round_attestation_time_ne_proposal_time C _ _ (h'.symm.trans htime)
  rw [optStep_run, if_neg c4] at h4
  rw [optStep_run, if_pos hs, DREB.run_bind_ok_iff] at h3
  obtain ⟨st2, l2, h2, h3⟩ := h3
  rw [DREB.run_bind_ok_iff] at h3
  obtain ⟨st3, l3', h3', h3⟩ := h3
  have c1 : (decide (t = C.proposal_time (C.slotOf t)) &&
      decide (P.proposer (C.slotOf t) = (record_awake n t).v) &&
      (record_awake n t).awake_since
        (grade1_window_start C (C.round_of (C.slotOf t)))) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨htime, hprop.trans hv.symm⟩, hawake⟩
  have c2 : ¬ ((decide (t = C.vote_time (C.slotOf t)) &&
      (record_awake n t).awake_since
        (grade1_window_start C (C.round_of (C.slotOf t)))) = true) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, Config.vote_time]
    rintro ⟨h', -⟩
    linarith
  have c3 : ¬ ((decide (t = C.gf_confirmation_time (C.slotOf t)) &&
      (record_awake n t).awake_since
        (grade2_window_start C (C.round_of (C.slotOf t)))) = true) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, Config.gf_confirmation_time]
    rintro ⟨h', -⟩
    linarith
  rw [optStep_run, if_pos c1] at h2
  rw [optStep_run, if_neg c2] at h3'
  rw [optStep_run, if_neg c3] at h3
  obtain ⟨B, hB⟩ := propose_block_sends h2
  simp only [Except.ok.injEq, Prod.mk.injEq] at h4 h3 h3'
  refine ⟨B, ?_⟩
  show NamedObject.block B ∈ l4
  rw [← h4.2, ← h3.2, ← h3'.2]
  have hB' : l2 = [] ++ [NamedObject.block B] := hB
  rw [hB']
  simp

/-- The receiving routines keep the validator, `awakeSince` and the store's clock, and keep the
    grades due. -/
private theorem receive_fields (C : Config) (P : Provisional V) (n : NodeState V)
    (o : NamedObject V) :
    (Spec.Sts.receive C P n o).v = n.v ∧
      (Spec.Sts.receive C P n o).awakeSince = n.awakeSince ∧
      (Spec.Sts.receive C P n o).st.t = n.st.t ∧
      (GradesDue C n → GradesDue C (Spec.Sts.receive C P n o)) := by
  cases o with
  | block B =>
    exact ⟨rfl, rfl, (frame_on_block C P n.st B).2.1, gradesDue_receive_block P B⟩
  | gfVote u =>
    exact ⟨rfl, rfl, (frame_on_goldfish_vote_checked P n.st u).2.1,
      gradesDue_receive_goldfish_vote P u⟩
  | attest a =>
    exact ⟨rfl, rfl, (frame_admit_attestation C n.st a).2.1, gradesDue_receive_attestation a⟩

/-- The awake test against `t₀` passes when the node has been awake since a time `a ≤ t₀`. -/
private theorem awake_since_of_some {n : NodeState V} {a t₀ : Time} (ha : n.awakeSince = some a)
    (hle : a ≤ t₀) : n.awake_since t₀ = true := by
  simp [NodeState.awake_since, Id.run, ha, Option.value, hle]; rfl

/-- The slot of a slot's proposal time is that slot. -/
private theorem slotOf_proposal_time (C : Config) (s : Slot) :
    C.slotOf (C.proposal_time s) = s := by
  have hΔ : (0 : Int) < 4 * C.Δ := by have := C.Δ_pos; time_omega
  simp only [Config.slotOf, Config.proposal_time]
  rw [Int.fdiv_eq_ediv_of_nonneg _ hΔ.le, Int.mul_ediv_cancel_left _ hΔ.ne']
  simp

/-- The initial node state of `v` runs as `v`, has the initial store, and has been awake since round
    `0`'s grade-2 window start. -/
private theorem initial_fields (C : Config) (v : V) :
    (initial C v).v = v ∧ (initial C v).st = Store.init ∧
      (initial C v).awakeSince = some (grade2_window_start C 0) :=
  ⟨rfl, rfl, rfl⟩

end SpecRecord.NoRaise

namespace SpecRecord.NodeRunFacts

open DecoupledConsensusModel.Execution DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open SpecRecord.NoRaise
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-! ## The members of `Model.spec` the run facts read, unfolded -/

/-- The tick of `Model.spec` can return `out` exactly when the spec's tick answers with the
    value of `out`'s node state and objects whose images are `out`'s. -/
private theorem tick_returns (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Int)
    (out : (Model.spec (V := V)).N × List (NamedObject V)) :
    (Model.spec (V := V)).tick S v n t ⇢ out ↔
      ∃ sent, (Spec.tick (Setup.toSpec S).C (Setup.toSpec S).P (Setup.toSpec S).X
          n.val t).run [] = .ok (out.1.val, sent) ∧
        out.2 = sent.map Spec.NamedObject.toProof := by
  show Returns (successOutcomes _) (out.1.val, out.2) ↔ _
  rw [returns_successOutcomes]
  cases h : (Spec.tick (Setup.toSpec S).C (Setup.toSpec S).P (Setup.toSpec S).X
      n.val t).run [] with
  | error e =>
    simp only [Except.map, reduceCtorEq, false_iff, not_exists, not_and]
    intro sent h'
    cases h'
  | ok p =>
    obtain ⟨n', sent⟩ := p
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨sent, ⟨h1, rfl⟩, h2.symm⟩
    · rintro ⟨sent', ⟨h1, rfl⟩, h2⟩
      exact ⟨h1, h2.symm⟩

/-- An answer of the spec's tick whose store meets `StoreOk` gives an outcome of the instance's
    tick. -/
private theorem tick_exists (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Int)
    {n' : Spec.NodeState V} {sent : List (Spec.NamedObject V)}
    (h : (Spec.tick (Setup.toSpec S).C (Setup.toSpec S).P (Setup.toSpec S).X
      n.val t).run [] = .ok (n', sent)) (hok : StoreOk n'.st) :
    ∃ out, (Model.spec (V := V)).tick S v n t ⇢ out :=
  ⟨(⟨n', hok⟩, sent.map Spec.NamedObject.toProof),
    (tick_returns S v n t _).2 ⟨sent, h, rfl⟩⟩

/-- The receipt of `o` by `Model.spec` can return `n'` exactly when `n'`'s value is
    `receiveNamedObject S n.val o`. -/
private theorem process_returns (S : Setup V) (n : (Model.spec (V := V)).N)
    (o : NamedObject V) (n' : (Model.spec (V := V)).N) :
    (Model.spec (V := V)).process S n o ⇢ n' ↔ n'.val = receiveNamedObject S n.val o := by
  show Returns (pure (receiveNamedObject S n.val o)) n'.val ↔ _
  exact returns_pure _ _

/-- The node state the tick stage of a `tickAllAwake t` step reads is the wake of the node state
    before the step, for a validator entering the awake set at `t`, and that node state otherwise. -/
private theorem wakeStage_cases (Sched : Framework.StsMultisetLog.Schedule V) (t : Int)
    (c : Framework.StsMultisetLog.Config V (NamedObject V) (Model.spec (V := V)).N) (v : V) :
    (v ∈ (Sched.awake t \ Sched.adv t) \ Sched.awake (t - 1) ∧
        (wakeStage (Model.spec (V := V)) Sched t c v).val = Spec.wake c[v].st.val) ∨
      (v ∉ (Sched.awake t \ Sched.adv t) \ Sched.awake (t - 1) ∧
        wakeStage (Model.spec (V := V)) Sched t c v = c[v].st) := by
  unfold wakeStage
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨h, rfl⟩

/-! ## One step of an execution, at one validator, with its context -/

/-- What step `k` of an execution does to `v`'s node state, with the time before and after it. A
    `tickAllAwake τ` step moves the time from `τ − 1` to `τ`; a validator awake at `τ` and not held
    by the adversary there holds, after it, an outcome of the instance's tick at `τ` on the node
    state its tick stage reads, or, when that tick has no outcome, that node state itself; any other
    validator keeps its node state. Every other step keeps the
    time, and leaves the validator's node state unchanged or replaces it by an outcome of the
    instance's receipt of an object. -/
private theorem step_shape (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    (k : Nat) (v : V) :
    (∃ τ : Nat, x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake τ ∧
      x[k].time + 1 = τ ∧ x[k + 1].time = τ ∧
      ((v ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) ∧
        ((∃ out : (Model.spec (V := V)).N × List (NamedObject V),
            (Model.spec (V := V)).tick (Setup.alwaysAwake S) v
              (wakeStage (Model.spec (V := V)) Sched (τ : Int) x[k] v) (τ : Int) ⇢ out ∧
            x[k + 1][v].st = out.1) ∨
          ((∀ out : (Model.spec (V := V)).N × List (NamedObject V),
                ¬ (Model.spec (V := V)).tick (Setup.alwaysAwake S) v
                  (wakeStage (Model.spec (V := V)) Sched (τ : Int) x[k] v) (τ : Int) ⇢ out) ∧
            x[k + 1][v].st = wakeStage (Model.spec (V := V)) Sched (τ : Int) x[k] v))) ∨
        (v ∉ Sched.awake (τ : Int) \ Sched.adv (τ : Int) ∧ x[k + 1][v].st = x[k][v].st))) ∨
    (x[k + 1].time = x[k].time ∧
      (x[k + 1][v].st = x[k][v].st ∨
        ∃ o : NamedObject V,
          (Model.spec (V := V)).process (Setup.alwaysAwake S) x[k][v].st o ⇢
            x[k + 1][v].st)) := by
  have hs : Framework.StsMultisetLog.AtomicStep (protocolOf (Model.spec (V := V)) S) Sched
      (x.lbl k) x[k] x[k + 1] := x.step k
  cases hl : x.lbl k with
  | tickAllAwake t =>
    rw [hl] at hs
    obtain ⟨hen, w', tk, hwake, htick, hc⟩ := hs
    refine Or.inl ⟨t, rfl, hen, by rw [hc]; rfl, ?_⟩
    have h2 : x[k + 1][v] =
        (Framework.StsMultisetLog.tickAllAwakeUpdate Sched t x[k] w' tk)[v] := by rw [hc]
    by_cases hv : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int)
    · have hx1 : x[k + 1][v].st = (tk v).state := by
        rw [h2, Framework.StsMultisetLog.tickAllAwakeUpdate_getElem_awake
          (Finset.mem_sdiff.1 hv).1 (Finset.mem_sdiff.1 hv).2]
      have hw := wakeStage_of_TickAllAwakeWake (Model.spec (V := V)) S Sched (hwake v)
      have htk := protocolOf_step_tick (Model.spec (V := V)) S (htick v hv)
      rw [hw] at htk
      refine Or.inl ⟨hv, ?_⟩
      rcases htk with ⟨out, hout, hst⟩ | ⟨hno, hst⟩
      · exact Or.inl ⟨out, hout, by rw [hx1, hst]⟩
      · exact Or.inr ⟨hno, by rw [hx1, hst]⟩
    · refine Or.inr ⟨hv, ?_⟩
      rw [h2]
      exact Framework.StsMultisetLog.tickAllAwakeUpdate_getElem_st_of_not_react hv
  | deliver p m =>
    have ht : x[k + 1].time = x[k].time := by
      have hs' := hs
      rw [hl] at hs'
      obtain ⟨-, hns⟩ := hs'
      exact hns.time
    refine Or.inr ⟨ht, ?_⟩
    by_cases hp : p = v
    · subst hp
      rcases st_succ_of_deliver (Model.spec (V := V)) S Sched x hl with h | ⟨-, h⟩
      · exact Or.inr ⟨m.msg, h⟩
      · exact Or.inl h
    · exact Or.inl (by rw [getElem_succ_of_deliver_ne (Model.spec (V := V)) S Sched x hl hp])
  | custom _ ev => exact ev.elim
  | adversarial p m =>
    refine Or.inr ⟨?_, Or.inl (by
      rw [getElem_succ_of_adversarial (Model.spec (V := V)) S Sched x hl])⟩
    rw [hl] at hs
    rw [hs.2]
  | forward p m =>
    refine Or.inr ⟨?_, Or.inl (by
      rw [getElem_succ_of_forward (Model.spec (V := V)) S Sched x hl])⟩
    rw [hl] at hs
    rw [hs.2]

/-- At a `tickAllAwake τ` step, for a validator `v` awake at `τ` and not held by the adversary
    there, the node state its tick stage reads runs as the validator its node state runs as, has its
    store, and either has `awakeSince = none` or is its node state, `v` being awake at `τ − 1`. -/
private theorem wakeStage_facts (Sched : Framework.StsMultisetLog.Schedule V) (τ : Int)
    (c : Framework.StsMultisetLog.Config V (NamedObject V) (Model.spec (V := V)).N) (v : V)
    (hv : v ∈ Sched.awake τ \ Sched.adv τ) :
    (wakeStage (Model.spec (V := V)) Sched τ c v).val.v = c[v].st.val.v ∧
      (wakeStage (Model.spec (V := V)) Sched τ c v).val.st = c[v].st.val.st ∧
      ((wakeStage (Model.spec (V := V)) Sched τ c v).val.awakeSince = none ∨
        (wakeStage (Model.spec (V := V)) Sched τ c v = c[v].st ∧
          v ∈ Sched.awake (τ - 1))) := by
  rcases wakeStage_cases Sched τ c v with ⟨-, h⟩ | ⟨hn, h⟩
  · rw [h]
    exact ⟨rfl, rfl, Or.inl rfl⟩
  · rw [h]
    refine ⟨rfl, rfl, Or.inr ⟨rfl, ?_⟩⟩
    by_contra ha
    exact hn (Finset.mem_sdiff.2 ⟨hv, ha⟩)

/-- The wake time `record_awake` records: the tick's own time after a wake, the earlier wake time
    otherwise. -/
private theorem record_awake_cases (n : Spec.NodeState V) (t : Int) :
    (n.awakeSince = none ∧ (Spec.record_awake n t).awakeSince = some t) ∨
      ∃ a, n.awakeSince = some a ∧ (Spec.record_awake n t).awakeSince = some a := by
  cases h : n.awakeSince with
  | none => exact Or.inl ⟨rfl, record_awake_of_none h⟩
  | some a => exact Or.inr ⟨a, rfl, record_awake_of_some h⟩

/-- Round `0`'s grade-2 window start is not positive. -/
private theorem grade2_window_start_zero_le (C : Spec.Config) :
    Spec.grade2_window_start C 0 ≤ 0 := by
  have hΔ := C.Δ_pos
  rw [grade2_window_start_eq]
  simp only [Spec.Config.opening, Spec.Config.proposal_time]
  push_cast
  linarith

/-- The instance's tick on a node state with `awakeSince = none` has an outcome at every
    non-negative time. -/
private theorem tick_exists_of_none (S : Setup V) (v : V) (n : (Model.spec (V := V)).N)
    (t : Int) (hn : n.val.awakeSince = none) (ht : 0 ≤ t) :
    ∃ out, (Model.spec (V := V)).tick S v n t ⇢ out := by
  obtain ⟨⟨n', sent⟩, h⟩ := tick_ok_of_none (Setup.toSpec S).C (Setup.toSpec S).P
    (Setup.toSpec S).X n.val t n.property.2.1 n.property.1 hn ht
  refine tick_exists S v n t h (storeOk_tick (out := (n', sent)) h n.property ?_)
  intro _ hc
  have hw : (Spec.record_awake n.val t).awake_since
      (Spec.grade1_window_start (Setup.toSpec S).C
        ((Setup.toSpec S).C.round_of ((Setup.toSpec S).C.slotOf t))) = false :=
    awake_since_record_of_none hn (window_starts_lt (Setup.toSpec S).C ht).1
  rw [hw] at hc
  simp at hc

/-- After `k` steps of the execution `x`, whenever `v` has been awake at every time from `w` to the
    current time, `w` being a multiple of `Δ` at or after round `0`'s grade-2 window start, `v`'s
    node state records a wake time at or before `w`. -/
private def AwakeWin (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    (k : Nat) (v : V) : Prop :=
  ∀ w : Int, Spec.grade2_window_start (Setup.toSpec S).C 0 ≤ w → w % S.E.Δ = 0 →
    w ≤ (x[k].time : Int) →
    (∀ t' : Int, w ≤ t' → t' ≤ (x[k].time : Int) → v ∈ Sched.awake t') →
    ∃ a : Int, (x[k][v].st.val).awakeSince = some a ∧ a ≤ w

/-- After every number `k` of steps, every validator's node state runs as that validator and records
    no wake time after the current time, and, for a validator not held by the adversary up to the
    current time, `AwakeWin` holds. -/
private theorem inv_awake (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    (k : Nat) (v : V) :
    (x[k][v].st.val).v = v ∧
      (∀ a : Int, (x[k][v].st.val).awakeSince = some a → a ≤ (x[k].time : Int)) ∧
      ((∀ t' ≤ (x[k].time : Int), v ∉ Sched.adv t') → AwakeWin S Sched x k v) := by
  induction k with
  | zero =>
    have h0 : (x[0][v].st).val = Spec.initial (Setup.toSpec S).C v := by
      rw [Record.st_zero]; rfl
    obtain ⟨h1, -, h3⟩ := initial_fields (Setup.toSpec S).C v
    rw [h0, h1, h3]
    refine ⟨rfl, ?_, ?_⟩
    · intro a ha
      cases ha
      have := grade2_window_start_zero_le (Setup.toSpec S).C
      have : (0 : Int) ≤ (x[0].time : Int) := Int.natCast_nonneg _
      linarith
    · intro _ w hw _ _ _
      rw [h0, h3]
      exact ⟨_, rfl, hw⟩
  | succ k ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    rcases step_shape S Sched x k v with ⟨τ, hl, hT, hT', hcase⟩ | ⟨hT, hcase⟩
    · have hTi : (x[k].time : Int) + 1 = (τ : Int) := by exact_mod_cast hT
      have hT'i : (x[k + 1].time : Int) = (τ : Int) := by exact_mod_cast hT'
      rw [hT'i]
      rcases hcase with ⟨hv, hres⟩ | ⟨hv, hst⟩
      · obtain ⟨hnv, -, hns⟩ := wakeStage_facts Sched (τ : Int) x[k] v hv
        have key : (x[k + 1][v].st.val).v = v ∧
            ((x[k + 1][v].st.val).awakeSince =
                (wakeStage (Model.spec (V := V)) Sched (τ : Int) x[k] v).val.awakeSince ∨
              (x[k + 1][v].st.val).awakeSince = (Spec.record_awake
                (wakeStage (Model.spec (V := V)) Sched (τ : Int) x[k] v).val τ).awakeSince) ∧
            ((wakeStage (Model.spec (V := V)) Sched (τ : Int) x[k] v).val.awakeSince = none →
              (x[k + 1][v].st.val).awakeSince = some (τ : Int)) := by
          rcases hres with ⟨out, hout, hst⟩ | ⟨hno, hst⟩
          · obtain ⟨sent, hrun, -⟩ := (tick_returns _ _ _ _ _).1 hout
            obtain ⟨-, -, -, -, -, haw, hv'⟩ := tick_outcome hrun
            rw [hst]
            refine ⟨hv'.trans (hnv.trans ih1), Or.inr haw, fun hn => ?_⟩
            rw [haw]
            exact record_awake_of_none hn
          · rw [hst]
            refine ⟨hnv.trans ih1, Or.inl rfl, fun hn => ?_⟩
            exfalso
            obtain ⟨out, hout⟩ := tick_exists_of_none (Setup.alwaysAwake S) v _ (τ : Int) hn
              (Int.natCast_nonneg _)
            exact hno out hout
        obtain ⟨k1, k2, k3⟩ := key
        refine ⟨k1, ?_, ?_⟩
        · intro a ha
          rcases hns with hn | ⟨heq, -⟩
          · rcases k2 with k2 | k2
            · rw [k2, hn] at ha; cases ha
            · rw [k2, record_awake_of_none hn] at ha; cases ha; exact le_refl _
          · rcases k2 with k2 | k2
            · rw [k2, heq] at ha; have := ih2 a ha; linarith
            · rw [k2, heq] at ha
              rcases record_awake_cases (x[k][v].st.val) (τ : Int) with ⟨-, h⟩ | ⟨b, hb, h⟩
              · rw [h] at ha; cases ha; exact le_refl _
              · rw [h] at ha; cases ha; have := ih2 _ hb; linarith
        · intro hhon w hw0 hwm hwτ hawk
          rw [hT'i] at hwτ hawk
          by_cases hwT : w ≤ (x[k].time : Int)
          · obtain ⟨a, ha, hle⟩ := ih3 (fun t' ht' => hhon t' (by linarith)) w hw0 hwm hwT
              (fun t' h1 h2 => hawk t' h1 (by linarith))
            have hnot : v ∈ Sched.awake ((τ : Int) - 1) := hawk _ (by linarith) (by linarith)
            rcases hns with hn | ⟨heq, -⟩
            · exfalso
              rcases wakeStage_cases Sched (τ : Int) x[k] v with ⟨he, -⟩ | ⟨hne, h⟩
              · exact (Finset.mem_sdiff.1 he).2 hnot
              · rw [h] at hn; rw [hn] at ha; cases ha
            · rcases k2 with k2 | k2
              · exact ⟨a, by rw [k2, heq, ha], hle⟩
              · exact ⟨a, by rw [k2, heq, record_awake_of_some ha], hle⟩
          · have hwτ' : w = (τ : Int) := by linarith
            rcases hns with hn | ⟨heq, -⟩
            · refine ⟨(τ : Int), k3 hn, by rw [hwτ']⟩
            · rcases record_awake_cases (x[k][v].st.val) (τ : Int) with ⟨hn, -⟩ | ⟨b, hb, h⟩
              · rw [← heq] at hn
                refine ⟨(τ : Int), k3 hn, by rw [hwτ']⟩
              · have := ih2 _ hb
                rcases k2 with k2 | k2
                · exact ⟨b, by rw [k2, heq, hb], by linarith⟩
                · exact ⟨b, by rw [k2, heq, h], by linarith⟩
      · rw [hst]
        refine ⟨ih1, fun a ha => by have := ih2 a ha; linarith, ?_⟩
        intro hhon w _ _ hwτ hawk
        rw [hT'i] at hwτ hawk
        exfalso
        exact hv (Finset.mem_sdiff.2 ⟨hawk _ hwτ (le_refl _), hhon _ (le_refl _)⟩)
    · rw [hT]
      rcases hcase with hst | ⟨o, ho⟩
      · rw [hst]; exact ⟨ih1, ih2, fun hhon => by unfold AwakeWin; rw [hT, hst]; exact ih3 hhon⟩
      · have hp := (process_returns _ _ _ _).1 ho
        obtain ⟨r1, r2, -, -⟩ := receive_fields (Setup.toSpec (Setup.alwaysAwake S)).C
          (Setup.toSpec (Setup.alwaysAwake S)).P (x[k][v].st.val)
          (Spec.NamedObject.toSpec o)
        have e1 : (x[k + 1][v].st.val).v = (x[k][v].st.val).v := by rw [hp]; exact r1
        have e2 : (x[k + 1][v].st.val).awakeSince = (x[k][v].st.val).awakeSince := by
          rw [hp]; exact r2
        refine ⟨e1.trans ih1, fun a ha => ih2 a (e2 ▸ ha), fun hhon => ?_⟩
        intro w hw0 hwm hwT hawk
        rw [hT] at hwT hawk
        obtain ⟨a, ha, hle⟩ := ih3 hhon w hw0 hwm hwT hawk
        exact ⟨a, e2.trans ha, hle⟩

/-- After `k` steps of the execution `x`, `v` is asleep at the current time, or its node state has
    run no tick since its last wake (`awakeSince = none`), or its store's clock is the current
    time. -/
private def Consec (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    (k : Nat) (v : V) : Prop :=
  v ∉ Sched.awake (x[k].time : Int) ∨ (x[k][v].st.val).awakeSince = none ∨
    (x[k][v].st.val).st.t = (x[k].time : Int)

/-- At the tick step at a slot's proposal time, the slot's proposer, if honest up to that time,
    holds no block whose root is the root it gives its proposal. -/
private def RootsNew (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf (Model.spec (V := V)) S) Sched) :
    Prop :=
  ∀ (k τ : Nat) (s : DecoupledConsensusModel.Slot),
    x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake τ →
    (τ : Int) = (Model.spec (V := V)).proposal_time S.E s →
    (∀ t' ≤ (τ : Int), S.E.proposer s ∉ Sched.adv t') →
    ∀ B ∈ x[k][S.E.proposer s].st.st.bodies, B.root ≠ (S.node (S.E.proposer s)).new_root s

/-- Under `RootsNew`, at a tick step `k` at time `τ`, a validator awake at `τ` and
    honest up to `τ`, whose node state has its grades due and meets `Consec`, has an outcome of the
    instance's tick on the node state its tick stage reads; that outcome has its grades due and its
    clock at `τ`. -/
private theorem outcome_of_due (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    (hnew : RootsNew S Sched x) (k τ : Nat) (v : V)
    (hl : x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake τ)
    (hv : v ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int))
    (hhon : ∀ t' ≤ (τ : Int), v ∉ Sched.adv t') (hv1 : (x[k][v].st.val).v = v)
    (hdue : GradesDue (Setup.toSpec S).C (x[k][v].st.val)) (hcons : Consec S Sched x k v) :
    ∃ out : (Model.spec (V := V)).N × List (NamedObject V),
      (Model.spec (V := V)).tick (Setup.alwaysAwake S) v
        (wakeStage (Model.spec (V := V)) Sched (τ : Int) x[k] v) (τ : Int) ⇢ out ∧
      GradesDue (Setup.toSpec S).C out.1.val ∧ out.1.val.st.t = (τ : Int) := by
  have hT : x[k].time + 1 = τ := (tickAllAwake_time (Model.spec (V := V)) S Sched x hl).1
  have hTi : (x[k].time : Int) + 1 = (τ : Int) := by exact_mod_cast hT
  have hΔ := (Setup.toSpec S).C.Δ_pos
  obtain ⟨hnv, hnst, -⟩ := wakeStage_facts Sched (τ : Int) x[k] v hv
  set ns := wakeStage (Model.spec (V := V)) Sched (τ : Int) x[k] v with hns
  have hdue' : GradesDue (Setup.toSpec S).C ns.val ∧
      (ns.val.awakeSince = none ∨ (τ : Int) = ns.val.st.t + 1) := by
    rcases wakeStage_cases Sched (τ : Int) x[k] v with ⟨-, h⟩ | ⟨hne, h⟩
    · rw [hns, h]
      exact ⟨gradesDue_wake hdue, Or.inl rfl⟩
    · rw [hns, h]
      refine ⟨hdue, ?_⟩
      have haw : v ∈ Sched.awake (x[k].time : Int) := by
        have : (x[k].time : Int) = (τ : Int) - 1 := by linarith
        rw [this]
        by_contra ha
        exact hne (Finset.mem_sdiff.2 ⟨hv, ha⟩)
      rcases hcons with hc | hc | hc
      · exact absurd haw hc
      · exact Or.inl hc
      · refine Or.inr ?_
        rw [hc]
        exact hTi.symm
  obtain ⟨hdue1, hcons1⟩ := hdue'
  obtain ⟨out0, hrun, -, hdue0⟩ := tick_ok (Setup.toSpec (Setup.alwaysAwake S)).C
    (Setup.toSpec (Setup.alwaysAwake S)).P (Setup.toSpec (Setup.alwaysAwake S)).X ns.val
    (τ : Int) ns.property.2.1 ns.property.1 hdue1 hcons1 (Int.natCast_nonneg _)
  have hok : StoreOk out0.1.st := by
    refine storeOk_tick hrun ns.property ?_
    intro _ hc B hB hroot
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨htime, hprop⟩, -⟩ := hc
    have hrv : (Spec.record_awake ns.val (τ : Int)).v = ns.val.v := by
      rw [record_awake_eq]
    have hvp : S.E.proposer ((Setup.toSpec S).C.slotOf (τ : Int)) = v :=
      hprop.trans (hrv.trans (hnv.trans hv1))
    have hnew' := hnew k τ ((Setup.toSpec S).C.slotOf (τ : Int)) hl htime (by rw [hvp]; exact hhon)
    rw [hvp] at hnew'
    refine hnew' B.toProofNamed ?_ ?_
    · show B.toProofNamed ∈ (x[k][v].st.val.st.T).map Spec.Block.toProofNamedEmb
      rw [← hnst]
      exact Finset.mem_map_of_mem _ hB
    · rw [Spec.Block.toProofNamed_root, hroot, hnv, hv1]
      rfl
  obtain ⟨n', sent⟩ := out0
  refine ⟨(⟨n', hok⟩, sent.map Spec.NamedObject.toProof),
    (tick_returns _ _ _ _ _).2 ⟨sent, hrun, rfl⟩, hdue0, tick_clock hrun⟩

/-- Two outcomes of the instance's tick from one node state at one time have the same node state. -/
private theorem tick_outcome_unique (S : Setup V) (v : V) (n : (Model.spec (V := V)).N)
    (t : Int) {out out' : (Model.spec (V := V)).N × List (NamedObject V)}
    (h : (Model.spec (V := V)).tick S v n t ⇢ out)
    (h' : (Model.spec (V := V)).tick S v n t ⇢ out') : out'.1 = out.1 := by
  obtain ⟨sent, hr, -⟩ := (tick_returns _ _ _ _ _).1 h
  obtain ⟨sent', hr', -⟩ := (tick_returns _ _ _ _ _).1 h'
  rw [hr] at hr'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hr'
  exact Subtype.ext hr'.1.symm

/-- Under `RootsNew`, after every number `k` of steps, every validator not held by the adversary up
    to the current time has its grades due (`GradesDue`) and meets `Consec`. -/
private theorem inv_due (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    (hnew : RootsNew S Sched x) (k : Nat) (v : V) :
    (∀ t' ≤ (x[k].time : Int), v ∉ Sched.adv t') →
      GradesDue (Setup.toSpec S).C (x[k][v].st.val) ∧ Consec S Sched x k v := by
  have hΔ : (0 : Int) < S.E.Δ := (Setup.toSpec S).C.Δ_pos
  induction k with
  | zero =>
    intro _
    have h0 : (x[0][v].st).val = Spec.initial (Setup.toSpec S).C v := by
      rw [Record.st_zero]; rfl
    have ht0 : x[0].time = 0 := x.init.1
    refine ⟨by rw [h0]; exact gradesDue_initial _ v, Or.inr (Or.inr ?_)⟩
    rw [h0, ht0]
    show (0 : Int) = ((0 : Nat) : Int)
    rfl
  | succ k ih =>
    intro hhon
    rcases step_shape S Sched x k v with ⟨τ, hl, hT, hT', hcase⟩ | ⟨hT, hcase⟩
    · have hTi : (x[k].time : Int) + 1 = (τ : Int) := by exact_mod_cast hT
      have hT'i : (x[k + 1].time : Int) = (τ : Int) := by exact_mod_cast hT'
      rw [hT'i] at hhon
      obtain ⟨hdue, hcons⟩ := ih (fun t' ht' => hhon t' (by linarith))
      unfold Consec
      rw [hT'i]
      rcases hcase with ⟨hv, hres⟩ | ⟨hv, hst⟩
      · obtain ⟨out, hout, hdue', hclock⟩ := outcome_of_due S Sched x hnew k τ v hl hv hhon
          (inv_awake S Sched x k v).1 hdue hcons
        rcases hres with ⟨out', hout', hst⟩ | ⟨hno, -⟩
        · have he := tick_outcome_unique _ _ _ _ hout hout'
          rw [hst, he]
          exact ⟨hdue', Or.inr (Or.inr hclock)⟩
        · exact absurd hout (hno out)
      · rw [hst]
        refine ⟨hdue, Or.inl fun ha => hv (Finset.mem_sdiff.2 ⟨ha, hhon _ (le_refl _)⟩)⟩
    · rw [hT] at hhon
      obtain ⟨hdue, hcons⟩ := ih hhon
      unfold Consec at hcons ⊢
      rw [hT]
      rcases hcase with hst | ⟨o, ho⟩
      · rw [hst]; exact ⟨hdue, hcons⟩
      · have hp := (process_returns _ _ _ _).1 ho
        obtain ⟨-, r2, r3, r4⟩ := receive_fields (Setup.toSpec (Setup.alwaysAwake S)).C
          (Setup.toSpec (Setup.alwaysAwake S)).P (x[k][v].st.val)
          (Spec.NamedObject.toSpec o)
        have e2 : (x[k + 1][v].st.val).awakeSince = (x[k][v].st.val).awakeSince := by
          rw [hp]; exact r2
        have e3 : (x[k + 1][v].st.val).st.t = (x[k][v].st.val).st.t := by rw [hp]; exact r3
        refine ⟨by rw [hp]; exact r4 hdue, ?_⟩
        rw [e2, e3]
        exact hcons

/-! ## The schedule facts the fields read -/

/-- A validator awake throughout `[t₀, t₁]` is awake at every time of it. -/
private theorem awake_of_awakeThroughout {Sched : Framework.StsMultisetLog.Schedule V}
    {v : V} {t₀ t₁ : Int} (h : v ∈ Sched.awakeThroughout t₀ t₁) :
    ∀ t' : Int, t₀ ≤ t' → t' ≤ t₁ → v ∈ Sched.awake t' := by
  intro t' h1 h2
  unfold Framework.StsMultisetLog.Schedule.awakeThroughout at h
  exact Finset.mem_inf.1 h t' (Finset.mem_Icc.2 ⟨h1, h2⟩)

/-- A grade window start of any round is a multiple of `Δ` at or after round `0`'s grade-2 window
    start. -/
private theorem window_start_facts (C : Spec.Config) (r : DecoupledConsensusModel.Round) :
    (Spec.grade2_window_start C 0 ≤ Spec.grade1_window_start C r ∧
        Spec.grade1_window_start C r % C.Δ = 0) ∧
      (Spec.grade2_window_start C 0 ≤ Spec.grade2_window_start C r ∧
        Spec.grade2_window_start C r % C.Δ = 0) := by
  have hΔ := C.Δ_pos
  have h0 : C.opening 0 ≤ C.opening r := opening_mono C (Nat.zero_le r)
  have hd := opening_dvd C r
  rw [grade1_window_start_eq, grade2_window_start_eq, grade2_window_start_eq]
  refine ⟨⟨by linarith, ?_⟩, ⟨by linarith, ?_⟩⟩
  · exact Int.emod_eq_zero_of_dvd (Int.dvd_sub hd ⟨5, by ring⟩)
  · exact Int.emod_eq_zero_of_dvd (Int.dvd_sub hd ⟨6, by ring⟩)

/-- A validator awake at `τ − 1` does not enter the awake set at `τ`, so its tick stage at `τ` reads
    its own node state. -/
private theorem wakeStage_of_awake_prev (Sched : Framework.StsMultisetLog.Schedule V) (τ : Int)
    (c : Framework.StsMultisetLog.Config V (NamedObject V) (Model.spec (V := V)).N) (v : V)
    (h : v ∈ Sched.awake (τ - 1)) : wakeStage (Model.spec (V := V)) Sched τ c v = c[v].st := by
  rcases wakeStage_cases Sched τ c v with ⟨he, -⟩ | ⟨-, heq⟩
  · exact absurd h (Finset.mem_sdiff.1 he).2
  · exact heq

/-- At a tick step whose time `τ` is after a window start `w` of round `r`, a validator awake
    throughout `[w, τ]` and honest up to `τ` has a node state, read by its tick, that records a wake
    time at or before `w`. -/
private theorem awake_window_at (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    (k τ : Nat) (v : V) (w : Int)
    (hl : x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake τ)
    (hw0 : Spec.grade2_window_start (Setup.toSpec S).C 0 ≤ w) (hwm : w % S.E.Δ = 0)
    (hlt : w < (τ : Int)) (hawake : v ∈ Sched.awakeThroughout w (τ : Int))
    (hhon : ∀ t' ≤ (τ : Int), v ∉ Sched.adv t') :
    ∃ a : Int, (wakeStage (Model.spec (V := V)) Sched (τ : Int) x[k] v).val.awakeSince =
      some a ∧ a ≤ w := by
  have hT := (tickAllAwake_time (Model.spec (V := V)) S Sched x hl).1
  have hTi : (x[k].time : Int) + 1 = (τ : Int) := by exact_mod_cast hT
  have hawk := awake_of_awakeThroughout hawake
  rw [wakeStage_of_awake_prev Sched (τ : Int) x[k] v (hawk _ (by linarith) (by linarith))]
  exact (inv_awake S Sched x k v).2.2 (fun t' ht' => hhon t' (by linarith)) w hw0 hwm
    (by linarith) (fun t' h1 h2 => hawk t' h1 (by linarith))

/-! ## The five fields -/

/-- The field `tick_outcome_sts` of `NodeRunFacts` at `Model.spec`: in an execution in which an
    honest proposer never already holds a block carrying the root of its proposal, every tick at a
    tick step `k` at `τ`, for a validator awake at `τ` and not held by the adversary at any time up
    to `τ`, has an outcome from the node state that tick reads. -/
theorem spec_tick_outcome_sts : ∀ (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf (Model.spec (V := V)) S) Sched),
    (∀ B C : DecoupledConsensusModel.NamedBlock V,
      (∃ B' : DecoupledConsensusModel.NamedBlock V,
        ((∃ (i : Nat) (sm : Framework.StsMultisetLog.SignedMsg V (NamedObject V)),
            sm ∈ x[i].sent ∧ sm.msg = .block B') ∨
          (∃ (i : Nat) (v : V), (∀ t' ≤ (x[i].time : Int), v ∉ Sched.adv t') ∧
            B' ∈ x[i][v].st.st.bodies)) ∧
        DecoupledConsensusModel.NamedBlock.Preceq B B') →
      (∃ C' : DecoupledConsensusModel.NamedBlock V,
        ((∃ (i : Nat) (sm : Framework.StsMultisetLog.SignedMsg V (NamedObject V)),
            sm ∈ x[i].sent ∧ sm.msg = .block C') ∨
          (∃ (i : Nat) (v : V), (∀ t' ≤ (x[i].time : Int), v ∉ Sched.adv t') ∧
            C' ∈ x[i][v].st.st.bodies)) ∧
        DecoupledConsensusModel.NamedBlock.Preceq C C') →
      ∀ A D : DecoupledConsensusModel.NamedBlock V,
        (DecoupledConsensusModel.NamedBlock.Preceq A B ∨
          DecoupledConsensusModel.NamedBlock.Preceq A C) →
        (DecoupledConsensusModel.NamedBlock.Preceq D B ∨
          DecoupledConsensusModel.NamedBlock.Preceq D C) → A.root = D.root → A = D) →
    (∀ (k τ : Nat) (s : DecoupledConsensusModel.Slot),
      x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake τ →
      (τ : Int) = (Model.spec (V := V)).proposal_time S.E s →
      (∀ t' ≤ (τ : Int), S.E.proposer s ∉ Sched.adv t') →
      ∀ B ∈ x[k][S.E.proposer s].st.st.bodies, B.root ≠ (S.node (S.E.proposer s)).new_root s) →
    ∀ (k τ : Nat) (v : V), x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake τ →
      v ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), v ∉ Sched.adv t') →
      ∃ out : (Model.spec (V := V)).N × List (NamedObject V),
        (Model.spec (V := V)).tick (Setup.alwaysAwake S) v
          (wakeStage (Model.spec (V := V)) Sched (τ : Int) x[k] v) (τ : Int) ⇢ out := by
  intro S Sched x _ hnew k τ v hl hv hhon
  have hT := (tickAllAwake_time (Model.spec (V := V)) S Sched x hl).1
  have hTi : (x[k].time : Int) + 1 = (τ : Int) := by exact_mod_cast hT
  obtain ⟨hdue, hcons⟩ := inv_due S Sched x hnew k v (fun t' ht' => hhon t' (by linarith))
  obtain ⟨out, hout, -⟩ := outcome_of_due S Sched x hnew k τ v hl hv hhon
    (inv_awake S Sched x k v).1 hdue hcons
  exact ⟨out, hout⟩

/-- The field `run_fact_g1_at` of `NodeRunFacts` at `Model.spec`: at a tick step `k` whose time
    `τ` is strictly after one delay before round `r`'s grade-1 cutoff, a validator awake at every
    time from that time to `τ`, and not held by the adversary at any time up to `τ`, passes the
    grade-1 awake test of round `r` on the node state its tick at `τ` reads. -/
theorem spec_run_fact_g1_at : ∀ (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    (k τ : Nat) (r : DecoupledConsensusModel.Round) (v : V),
    x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake τ →
    (Model.spec (V := V)).early S.E S.hc r .g1 - S.E.Δ < (τ : Int) →
    v ∈ Sched.awakeThroughout ((Model.spec (V := V)).early S.E S.hc r .g1 - S.E.Δ)
      (τ : Int) →
    (∀ t' ≤ (τ : Int), v ∉ Sched.adv t') →
    (Model.spec (V := V)).awake_for_grade1 (Setup.alwaysAwake S) v
      (wakeStage (Model.spec (V := V)) Sched (τ : Int) x[k] v) r := by
  intro S Sched x k τ r v hl hlt hawake hhon
  obtain ⟨⟨h0, hm⟩, -⟩ := window_start_facts (Setup.toSpec S).C r
  exact awake_window_at S Sched x k τ v _ hl h0 hm hlt hawake hhon

/-- The field `run_fact_g2_at` of `NodeRunFacts` at `Model.spec`: at a tick step `k` whose time
    `τ` is strictly after one delay before round `r`'s grade-2 cutoff, a validator awake at every
    time from that time to `τ`, and not held by the adversary at any time up to `τ`, passes the
    grade-2 awake test of round `r` on the node state its tick at `τ` reads. -/
theorem spec_run_fact_g2_at : ∀ (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    (k τ : Nat) (r : DecoupledConsensusModel.Round) (v : V),
    x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake τ →
    (Model.spec (V := V)).early S.E S.hc r .g2 - S.E.Δ < (τ : Int) →
    v ∈ Sched.awakeThroughout ((Model.spec (V := V)).early S.E S.hc r .g2 - S.E.Δ)
      (τ : Int) →
    (∀ t' ≤ (τ : Int), v ∉ Sched.adv t') →
    (Model.spec (V := V)).awake_for_grade2 (Setup.alwaysAwake S) v
      (wakeStage (Model.spec (V := V)) Sched (τ : Int) x[k] v) r := by
  intro S Sched x k τ r v hl hlt hawake hhon
  obtain ⟨-, ⟨h0, hm⟩⟩ := window_start_facts (Setup.toSpec S).C r
  exact awake_window_at S Sched x k τ v _ hl h0 hm hlt hawake hhon

/-- The field `tick_emits_proposal_inclX` of `NodeRunFacts` at `Model.spec`: for a slot `s > 0`
    whose proposer is awake at every time from `proposal_wake_start S s` to `s`'s proposal time and
    not held by the adversary up to it, every outcome of the proposer's tick at that time, run on
    its node state after the tick step `k` of that time, emits a named block. -/
theorem spec_tick_emits_proposal_inclX : ∀ (S : Setup V)
    (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    (k : Nat) {s : DecoupledConsensusModel.Slot}
    (_hl : x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake
      ((Model.spec (V := V)).proposal_time S.E s).toNat)
    (_hhon : ∀ t' ≤ (Model.spec (V := V)).proposal_time S.E s, S.E.proposer s ∉ Sched.adv t')
    (_hs : 0 < s)
    (_hawake : S.E.proposer s ∈
      Sched.awakeThroughout ((Model.spec (V := V)).proposal_wake_start S s)
        ((Model.spec (V := V)).proposal_time S.E s))
    (out : (Model.spec (V := V)).N × List (NamedObject V))
    (_hout : (Model.spec (V := V)).tick (Setup.alwaysAwake S) (S.E.proposer s)
      (x[k][S.E.proposer s].st) ((Model.spec (V := V)).proposal_time S.E s) ⇢ out),
    ∃ B : DecoupledConsensusModel.NamedBlock V, NamedObject.block B ∈ out.2 := by
  intro S Sched x k s hl hhon hs hawake out hout
  set C := (Setup.toSpec S).C with hC
  have hΔ := C.Δ_pos
  have htp : (Model.spec (V := V)).proposal_time S.E s = C.proposal_time s := rfl
  rw [htp] at hl hhon hawake hout
  have ht0 : 0 ≤ C.proposal_time s := by
    simp only [Spec.Config.proposal_time]
    have : (0 : Int) ≤ (s : Int) := Int.natCast_nonneg _
    positivity
  have hτ : ((C.proposal_time s).toNat : Int) = C.proposal_time s := Int.toNat_of_nonneg ht0
  have hT := (tickAllAwake_time (Model.spec (V := V)) S Sched x hl).1
  have hTi : (x[k].time : Int) + 1 = C.proposal_time s := by rw [← hτ]; exact_mod_cast hT
  obtain ⟨sent, hrun, hsent⟩ := (tick_returns _ _ _ _ _).1 hout
  have hrun' : (Spec.tick C (Setup.toSpec S).P (Setup.toSpec S).X
      (x[k][S.E.proposer s].st.val) (C.proposal_time s)).run [] = .ok (out.1.val, sent) := hrun
  obtain ⟨hv1, -, h3⟩ := inv_awake S Sched x k (S.E.proposer s)
  have hslot : C.slotOf (C.proposal_time s) = s := slotOf_proposal_time C s
  have hwake : (Model.spec (V := V)).proposal_wake_start S s =
      Spec.grade1_window_start C (C.round_of s) := rfl
  rw [hwake] at hawake
  have hawk := awake_of_awakeThroughout hawake
  obtain ⟨⟨h0, hm⟩, -⟩ := window_start_facts C (C.round_of s)
  have hop : C.opening (C.round_of s) ≤ C.proposal_time s := by
    simp only [Spec.Config.opening, Spec.Config.proposal_time]
    have : ((C.round_of s * C.R : Nat) : Int) ≤ (s : Int) := by
      exact_mod_cast Nat.div_mul_le_self s C.R
    exact Int.mul_le_mul_of_nonneg_left this (by linarith)
  have hle : Spec.grade1_window_start C (C.round_of s) ≤ (x[k].time : Int) := by
    have hΔ1 : 0 + 1 ≤ C.Δ := Int.add_one_le_of_lt hΔ
    rw [grade1_window_start_eq]; linarith
  obtain ⟨a, ha, hale⟩ := h3 (fun t' ht' => hhon t' (by linarith)) _ h0 hm hle
    (fun t' h1 h2 => hawk t' h1 (by linarith))
  have htest : (Spec.record_awake (x[k][S.E.proposer s].st.val)
      (C.proposal_time s)).awake_since
      (Spec.grade1_window_start C (C.round_of (C.slotOf (C.proposal_time s)))) =
        true := by
    rw [hslot]; exact awake_since_of_some (record_awake_of_some ha) hale
  obtain ⟨B, hB⟩ := tick_sends_block hrun' (by rw [hslot]; exact hs) (by rw [hslot])
    (by rw [hslot, hv1]; rfl) htest
  rw [hsent]
  exact ⟨B.toProofNamed, List.mem_map.2 ⟨_, hB, rfl⟩⟩

/-- The field `stateBeforeOf_runs_as` of `NodeRunFacts` at `Model.spec`: for every world `w`
    that the run `rho` can reach before its `i`-th event, the node state of `v` in `w` runs as `v`. -/
theorem spec_stateBeforeOf_runs_as : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat)
    (w : V → (Model.spec (V := V)).N)
    (_hw : w ∈ stateBeforeOf (Model.spec (V := V)) S rho i) (v : V),
    (Model.spec (V := V)).runs_as (w v) v := by
  intro S rho i w hw v
  show (w v).val.v = v
  have key : ∀ (es : List (Record.Event V)) (w₁ : V → (Model.spec (V := V)).N),
      (∀ u, (w₁ u).val.v = u) →
      ∀ w₂ ∈ es.foldlM (worldStepOf (Model.spec (V := V)) S) w₁, ∀ u, (w₂ u).val.v = u := by
    intro es
    induction es with
    | nil =>
      intro w₁ h w₂ hw₂ u
      have hw' : w₂ = w₁ := hw₂
      subst hw'
      exact h u
    | cons e es ih =>
      intro w₁ h w₂ hw₂ u
      rw [List.foldlM_cons, Set.bind_def] at hw₂
      obtain ⟨w', hw', hw₂⟩ := Set.mem_iUnion₂.mp hw₂
      refine ih w' ?_ w₂ hw₂ u
      intro u'
      cases e with
      | wake p t =>
        simp only [worldStepOf, Set.mem_singleton_iff] at hw'
        subst hw'
        by_cases hu : u' = p
        · subst hu
          rw [Function.update_self]
          exact h u'
        · rw [Function.update_of_ne hu]
          exact h u'
      | tick p t =>
        simp only [worldStepOf, Set.mem_setOf_eq] at hw'
        rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
        · by_cases hu : u' = p
          · subst hu
            rw [Function.update_self]
            obtain ⟨sent, hrun, -⟩ := (tick_returns _ _ _ _ _).1 hout
            obtain ⟨-, -, -, -, -, -, hv'⟩ := tick_outcome hrun
            exact hv'.trans (h u')
          · rw [Function.update_of_ne hu]
            exact h u'
        · exact h u'
      | deliver p o t =>
        simp only [worldStepOf, Set.mem_setOf_eq] at hw'
        rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
        · by_cases hu : u' = p
          · subst hu
            rw [Function.update_self]
            have hp := (process_returns _ _ _ _).1 hn'
            rw [hp]
            exact (receive_fields (Setup.toSpec S).C (Setup.toSpec S).P ((w₁ u').val)
              (Spec.NamedObject.toSpec o)).1.trans (h u')
          · rw [Function.update_of_ne hu]
            exact h u'
        · exact h u'
  exact key _ _ (fun u => rfl) w hw v

/-! ## The converse awake facts, the fields of `NodeWakeFacts` -/

/-- After every number `k` of steps, a validator not held by the adversary at any time up to the
    current time and awake at the current time, whose node state records the wake time `a`, has been
    awake at every non-negative time from `a` to the current time. -/
private theorem inv_awakeSince_sound (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    (k : Nat) (v : V) :
    (∀ t' ≤ (x[k].time : Int), v ∉ Sched.adv t') → v ∈ Sched.awake (x[k].time : Int) →
    ∀ a : Int, (x[k][v].st.val).awakeSince = some a →
      ∀ t' : Int, 0 ≤ t' → a ≤ t' → t' ≤ (x[k].time : Int) → v ∈ Sched.awake t' := by
  induction k with
  | zero =>
    intro _ hv a _ t' h0 _ h1
    have ht0 : (x[0].time : Int) = 0 := by
      have := x.init.1
      exact_mod_cast this
    have : t' = (x[0].time : Int) := by omega
    rw [this]; exact hv
  | succ k ih =>
    intro hhon hv a ha t' h0 hat htT
    rcases step_shape S Sched x k v with ⟨τ, hl, hT, hT', hcase⟩ | ⟨hT, hcase⟩
    · have hTi : (x[k].time : Int) + 1 = (τ : Int) := by exact_mod_cast hT
      have hT'i : (x[k + 1].time : Int) = (τ : Int) := by exact_mod_cast hT'
      rw [hT'i] at hhon hv htT
      rcases hcase with ⟨hvτ, hres⟩ | ⟨hvτ, -⟩
      · have hns := (wakeStage_facts Sched (τ : Int) x[k] v hvτ).2.2
        have k2 : (x[k + 1][v].st.val).awakeSince =
                (wakeStage (Model.spec (V := V)) Sched (τ : Int) x[k] v).val.awakeSince ∨
              (x[k + 1][v].st.val).awakeSince = (Spec.record_awake
                (wakeStage (Model.spec (V := V)) Sched (τ : Int) x[k] v).val τ).awakeSince := by
          rcases hres with ⟨out, hout, hst⟩ | ⟨-, hst⟩
          · obtain ⟨sent, hrun, -⟩ := (tick_returns _ _ _ _ _).1 hout
            obtain ⟨-, -, -, -, -, haw, -⟩ := tick_outcome hrun
            rw [hst]; exact Or.inr haw
          · rw [hst]; exact Or.inl rfl
        by_cases htτ : t' = (τ : Int)
        · rw [htτ]; exact (Finset.mem_sdiff.1 hvτ).1
        · rcases hns with hn | ⟨heq, hprev⟩
          · exfalso
            rcases k2 with k2 | k2
            · rw [k2, hn] at ha; cases ha
            · rw [k2, record_awake_of_none hn] at ha; cases ha; omega
          · have hprev' : v ∈ Sched.awake (x[k].time : Int) := by
              have : (x[k].time : Int) = (τ : Int) - 1 := by omega
              rw [this]; exact hprev
            have hb : (x[k][v].st.val).awakeSince = some a := by
              rcases k2 with k2 | k2
              · rw [k2, heq] at ha; exact ha
              · rw [k2, heq] at ha
                rcases record_awake_cases (x[k][v].st.val) (τ : Int) with ⟨-, h⟩ | ⟨b, hb, h⟩
                · rw [h] at ha; cases ha; omega
                · rw [h] at ha; cases ha; exact hb
            exact ih (fun t'' h => hhon t'' (by omega)) hprev' a hb t' h0 hat (by omega)
      · exfalso
        exact hvτ (Finset.mem_sdiff.2 ⟨hv, hhon _ (le_refl _)⟩)
    · rw [hT] at hhon hv htT
      have e2 : (x[k + 1][v].st.val).awakeSince = (x[k][v].st.val).awakeSince := by
        rcases hcase with hst | ⟨o, ho⟩
        · rw [hst]
        · have hp := (process_returns _ _ _ _).1 ho
          obtain ⟨-, r2, -, -⟩ := receive_fields (Setup.toSpec (Setup.alwaysAwake S)).C
            (Setup.toSpec (Setup.alwaysAwake S)).P (x[k][v].st.val) (Spec.NamedObject.toSpec o)
          rw [hp]; exact r2
      exact ih hhon hv a (e2 ▸ ha) t' h0 hat htT

/-- At a tick step at time `τ`, a validator not held by the adversary up to `τ` and awake at `τ`,
    whose node state, as its tick reads it, records a wake time at or before a non-negative time
    `w`, has been awake at every time from `w` to `τ`. -/
private theorem awakeThroughout_of_test (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    (k τ : Nat) (v : V) (w : Int)
    (hl : x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake τ) (h0 : 0 ≤ w)
    (hhon : ∀ t' ≤ (τ : Int), v ∉ Sched.adv t') (hv : v ∈ Sched.awake (τ : Int))
    (hfor : ∃ a, (wakeStage (Model.spec (V := V)) Sched (τ : Int) x[k] v).val.awakeSince =
      some a ∧ a ≤ w) :
    v ∈ Sched.awakeThroughout w (τ : Int) := by
  obtain ⟨a, ha, haw⟩ := hfor
  have hT := (tickAllAwake_time (Model.spec (V := V)) S Sched x hl).1
  have hTi : (x[k].time : Int) + 1 = (τ : Int) := by exact_mod_cast hT
  have hvτ : v ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) :=
    Finset.mem_sdiff.2 ⟨hv, hhon _ (le_refl _)⟩
  unfold Framework.StsMultisetLog.Schedule.awakeThroughout
  refine Finset.mem_inf.2 (fun t' ht' => ?_)
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 ht'
  by_cases htτ : t' = (τ : Int)
  · rw [htτ]; exact hv
  · rcases (wakeStage_facts Sched (τ : Int) x[k] v hvτ).2.2 with hn | ⟨heq, hprev⟩
    · rw [hn] at ha; cases ha
    · rw [heq] at ha
      have hprev' : v ∈ Sched.awake (x[k].time : Int) := by
        have : (x[k].time : Int) = (τ : Int) - 1 := by omega
        rw [this]; exact hprev
      exact inv_awakeSince_sound S Sched x k v (fun t'' h => hhon t'' (by omega)) hprev' a ha t'
        (by omega) (le_trans haw h1) (by omega)

/-- The field `run_fact_g2_sound_at` of `NodeWakeFacts` at `Model.spec`: at a tick step `k` at
    time `τ`, a validator not held by the adversary up to `τ` and awake at `τ`, whose node state, as
    its tick at `τ` reads it, passes the grade-2 awake test of round `r`, has been awake at every
    time from round `r`'s grade-2 window start, when that start is non-negative, to `τ`. -/
theorem spec_run_fact_g2_sound_at : ∀ (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    (k τ : Nat) (r : DecoupledConsensusModel.Round) (v : V),
    x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake τ →
    0 ≤ (Model.spec (V := V)).early S.E S.hc r .g2 - S.E.Δ →
    (∀ t' ≤ (τ : Int), v ∉ Sched.adv t') →
    v ∈ Sched.awake (τ : Int) →
    (Model.spec (V := V)).awake_for_grade2 (Setup.alwaysAwake S) v
      (wakeStage (Model.spec (V := V)) Sched (τ : Int) x[k] v) r →
    v ∈ Sched.awakeThroughout ((Model.spec (V := V)).early S.E S.hc r .g2 - S.E.Δ)
      (τ : Int) := by
  intro S Sched x k τ r v hl h0 hhon hv hfor
  exact awakeThroughout_of_test S Sched x k τ v _ hl h0 hhon hv hfor

/-- The field `run_fact_g1_sound_at` of `NodeWakeFacts` at `Model.spec`: at a tick step `k` at
    time `τ`, a validator not held by the adversary up to `τ` and awake at `τ`, whose node state, as
    its tick at `τ` reads it, passes the grade-1 awake test of round `r`, has been awake at every
    time from round `r`'s grade-1 window start, when that start is non-negative, to `τ`. -/
theorem spec_run_fact_g1_sound_at : ∀ (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    (k τ : Nat) (r : DecoupledConsensusModel.Round) (v : V),
    x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake τ →
    0 ≤ (Model.spec (V := V)).early S.E S.hc r .g1 - S.E.Δ →
    (∀ t' ≤ (τ : Int), v ∉ Sched.adv t') →
    v ∈ Sched.awake (τ : Int) →
    (Model.spec (V := V)).awake_for_grade1 (Setup.alwaysAwake S) v
      (wakeStage (Model.spec (V := V)) Sched (τ : Int) x[k] v) r →
    v ∈ Sched.awakeThroughout ((Model.spec (V := V)).early S.E S.hc r .g1 - S.E.Δ)
      (τ : Int) := by
  intro S Sched x k τ r v hl h0 hhon hv hfor
  exact awakeThroughout_of_test S Sched x k τ v _ hl h0 hhon hv hfor

end SpecRecord.NodeRunFacts
