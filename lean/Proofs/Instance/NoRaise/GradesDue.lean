import Proofs.Instance.NoRaise.Stamps
import Proofs.Instance.NoRaise.Schedule

/-!
# `GradesDue` is kept by every step

`GradesDue` holds initially and is kept by the wake, by receiving a block, a Goldfish vote or an
attestation, and by a tick that follows a wake or the store's clock by one time unit. After the
grades update of such a tick, every grade result a duty of the round reads is computed when that
duty's wake test holds.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SpecRecord.NoRaise

open Spec Spec.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The clauses of `GradesDue` for the wake value `a?`, the clock `t` and the saved grades `c`: `t`
    is non-negative, `c.round` is the round of `t`, and every result the wake `a?` requires at `t`
    is computed in `c`. -/
def GradesDueAt (C : Config) (a? : Option Time) (t : Time) (c : SavedGrades V) : Prop :=
  0 ≤ t ∧ c.round = roundAt C t ∧
  ∀ a, a? = some a →
    (a ≤ grade1_window_start C c.round → c.current.g1 ≠ .pending) ∧
    (a ≤ grade2_window_start C c.round → c.current.g2 ≠ .pending) ∧
    (a ≤ grade2_window_start C c.round → C.opening c.round + C.Δ ≤ t →
      c.current.g0 ≠ .pending) ∧
    (a ≤ grade2_window_start C (c.round + 1) → C.opening (c.round + 1) - C.Δ ≤ t →
      c.next.g2 ≠ .pending)

/-- `GradesDue C n` is `GradesDueAt` of the node's wake value, clock and saved grades. -/
theorem gradesDue_iff (C : Config) (n : NodeState V) :
    GradesDue C n ↔ GradesDueAt C n.awakeSince n.st.t n.st.saved_grades := Iff.rfl

/-! ## Compatibility keeps which results are computed -/

/-- A result made compatible with a block is pending exactly when it was. -/
theorem make_result_compatible_with_ne_pending_iff (F : Block V) (x : GradeResult V) :
    make_result_compatible_with F x ≠ .pending ↔ x ≠ .pending := by
  cases x with
  | pending => exact Iff.rfl
  | computed G =>
    cases G <;> simp [make_result_compatible_with, Id.run, GradeResult.block]

/-- `GradesDueAt` is kept when the saved blocks are made compatible with a block `F`. -/
theorem gradesDueAt_compat {C : Config} {a? : Option Time} {t : Time} {c : SavedGrades V}
    (F : Block V) (h : GradesDueAt C a? t c) :
    GradesDueAt C a? t (make_saved_grades_compatible_with F c) := by
  obtain ⟨h2, h3, h4⟩ := h
  refine ⟨h2, h3, fun a ha => ?_⟩
  obtain ⟨k1, k2, k3, k4⟩ := h4 a ha
  simp only [make_saved_grades_compatible_with, make_round_grades_compatible_with,
    make_result_compatible_with_ne_pending_iff]
  exact ⟨k1, k2, k3, k4⟩

/-! ## What `update_grades` computes -/

/-- The saved grades brought to round `r` are at round `r`. -/
theorem advance_to_round_round (c : SavedGrades V) (r : Round) :
    (advance_to_round c r).round = r := by
  unfold advance_to_round
  split_ifs with h1
  · exact h1.symm
  · rfl
  · rfl

/-- An answer `st'` of `update_grades` at time `t` has its saved grades at `t`'s round, keeps every
    result computed in the saved grades brought to that round, and computes each result whose time
    is `t`. -/
theorem update_grades_results {C : Config} {P : Provisional V} {st st' : Store V} {t : Time}
    (h : update_grades C P st t = .ok st') :
    st'.saved_grades.round = roundAt C t ∧
    ((advance_to_round st.saved_grades (roundAt C t)).current.g1 ≠ .pending ∨
        t = C.opening (roundAt C t) → st'.saved_grades.current.g1 ≠ .pending) ∧
    ((advance_to_round st.saved_grades (roundAt C t)).current.g2 ≠ .pending →
        st'.saved_grades.current.g2 ≠ .pending) ∧
    ((advance_to_round st.saved_grades (roundAt C t)).current.g0 ≠ .pending ∨
        t = C.opening (roundAt C t) + C.Δ → st'.saved_grades.current.g0 ≠ .pending) ∧
    ((advance_to_round st.saved_grades (roundAt C t)).next.g2 ≠ .pending ∨
        t = C.opening (roundAt C t + 1) - C.Δ → st'.saved_grades.next.g2 ≠ .pending) := by
  simp only [update_grades] at h
  repeat' (first
    | (split_ifs at h)
    | (obtain ⟨_, -, h⟩ := DRE.ok_of_bind h; try dsimp only at h))
  all_goals
    have h' := h
    simp only [pure, Except.pure, Except.ok.injEq] at h'
    subst h'
    refine ⟨advance_to_round_round _ _, ?_, ?_, ?_, ?_⟩ <;>
      simp only [make_saved_grades_compatible_with, make_round_grades_compatible_with,
        make_result_compatible_with_ne_pending_iff, ne_eq, reduceCtorEq, not_false_eq_true,
        implies_true] <;>
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at * <;>
      tauto

/-! ## The clauses after the grades update -/

/-- Right after a wake at the clock `t ≥ 0`, with the saved grades at `t`'s round, `GradesDueAt`
    holds: a node that woke at `t` requires no result at `t`. -/
theorem gradesDueAt_of_wake {C : Config} {t : Time} {c : SavedGrades V} (ht : 0 ≤ t)
    (hc : c.round = roundAt C t) : GradesDueAt C (some t) t c := by
  refine ⟨ht, hc, fun a ha => ?_⟩
  cases ha
  obtain ⟨h1, h2⟩ := opening_le_self C ht
  have hL := roundLength_ge C
  have hΔ := C.Δ_pos
  rw [opening_succ] at h2
  rw [hc, grade1_window_start_eq, grade2_window_start_eq, grade2_window_start_eq, opening_succ]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> (try intro h') <;> exfalso <;> time_omega

/-- `GradesDueAt` at `t − 1` for `c`, and what the grades update kept or computed at `t` in the same
    round, give `GradesDueAt` at `t` for the new saved grades `c'`. -/
theorem gradesDueAt_step_same {C : Config} {a t : Time} {c c' : SavedGrades V}
    (hold : GradesDueAt C (some a) (t - 1) c)
    (hρ : c.round = roundAt C t) (hround : c'.round = roundAt C t)
    (k1 : c.current.g1 ≠ .pending → c'.current.g1 ≠ .pending)
    (k2 : c.current.g2 ≠ .pending → c'.current.g2 ≠ .pending)
    (k3 : c.current.g0 ≠ .pending ∨ t = C.opening (roundAt C t) + C.Δ →
      c'.current.g0 ≠ .pending)
    (k4 : c.next.g2 ≠ .pending ∨ t = C.opening (roundAt C t + 1) - C.Δ →
      c'.next.g2 ≠ .pending) :
    GradesDueAt C (some a) t c' := by
  obtain ⟨h0, -, hcl⟩ := hold
  obtain ⟨o1, o2, o3, o4⟩ := hcl a rfl
  refine ⟨by time_omega, hround, fun a' ha' => ?_⟩
  cases ha'
  rw [hround]
  rw [← hρ] at k3 k4 ⊢
  refine ⟨fun h => k1 (o1 h), fun h => k2 (o2 h), fun h hle => ?_, fun h hle => ?_⟩
  · by_cases hle' : C.opening c.round + C.Δ ≤ t - 1
    · exact k3 (Or.inl (o3 h hle'))
    · exact k3 (Or.inr (by time_omega))
  · by_cases hle' : C.opening (c.round + 1) - C.Δ ≤ t - 1
    · exact k4 (Or.inl (o4 h hle'))
    · exact k4 (Or.inr (by time_omega))

/-- `GradesDueAt` at `t − 1` for `c`, and what the grades update kept or computed at the opening `t`
    of the next round, give `GradesDueAt` at `t` for the new saved grades `c'`. -/
theorem gradesDueAt_step_next {C : Config} {a t : Time} {c c' : SavedGrades V}
    (hold : GradesDueAt C (some a) (t - 1) c)
    (hρ : c.round + 1 = roundAt C t) (hto : t = C.opening (roundAt C t))
    (hround : c'.round = roundAt C t)
    (k1 : t = C.opening (roundAt C t) → c'.current.g1 ≠ .pending)
    (k2 : c.next.g2 ≠ .pending → c'.current.g2 ≠ .pending) :
    GradesDueAt C (some a) t c' := by
  obtain ⟨h0, -, hcl⟩ := hold
  obtain ⟨-, -, -, o4⟩ := hcl a rfl
  have hΔ := C.Δ_pos
  have hL := roundLength_ge C
  refine ⟨by time_omega, hround, fun a' ha' => ?_⟩
  cases ha'
  rw [hround]
  refine ⟨fun _ => k1 hto, fun h => k2 (o4 (by rwa [hρ]) (by rw [hρ]; time_omega)),
    fun _ hle => ?_, fun _ hle => ?_⟩
  · exfalso; time_omega
  · rw [opening_succ] at hle
    exfalso; time_omega

/-- `GradesDueAt` at `t − 1` for `c`, and what the grades update kept or computed at `t`, give
    `GradesDueAt` at `t` for the new saved grades `c'`. -/
theorem gradesDueAt_step {C : Config} {a t : Time} {c c' : SavedGrades V}
    (hold : GradesDueAt C (some a) (t - 1) c)
    (hround : c'.round = roundAt C t)
    (k1 : (advance_to_round c (roundAt C t)).current.g1 ≠ .pending ∨
        t = C.opening (roundAt C t) → c'.current.g1 ≠ .pending)
    (k2 : (advance_to_round c (roundAt C t)).current.g2 ≠ .pending →
        c'.current.g2 ≠ .pending)
    (k3 : (advance_to_round c (roundAt C t)).current.g0 ≠ .pending ∨
        t = C.opening (roundAt C t) + C.Δ → c'.current.g0 ≠ .pending)
    (k4 : (advance_to_round c (roundAt C t)).next.g2 ≠ .pending ∨
        t = C.opening (roundAt C t + 1) - C.Δ → c'.next.g2 ≠ .pending) :
    GradesDueAt C (some a) t c' := by
  have hc := hold.2.1
  have h0 := hold.1
  rcases round_step_one C h0 with hr | ⟨hr, hto⟩
  · have hρ : c.round = roundAt C t := hc.trans hr.symm
    have hadv : advance_to_round c (roundAt C t) = c := by
      simp [advance_to_round, hρ]
    rw [hadv] at k1 k2 k3 k4
    exact gradesDueAt_step_same hold hρ hround (fun h => k1 (Or.inl h)) k2 k3 k4
  · have hρ : c.round + 1 = roundAt C t := by rw [hc, hr]
    have hadv : advance_to_round c (roundAt C t) = ⟨roundAt C t, c.next, pending_round_grades⟩ := by
      simp only [advance_to_round, ← hρ]
      simp
    rw [hadv] at k1 k2
    exact gradesDueAt_step_next hold hρ hto hround (fun h => k1 (Or.inr h)) k2

/-- After the grades update of a tick at `t ≥ 0` that follows a wake or the store's clock by one
    time unit, from a node whose grades are due, the saved grades satisfy `GradesDueAt` at `t` for
    the wake value `record_awake` leaves. -/
theorem gradesDueAt_update {C : Config} {P : Provisional V} {n : NodeState V} {t : Time}
    {st0 : Store V} (hdue : GradesDue C n)
    (h0 : update_grades C P (record_awake n t).st t = .ok st0) (ht : 0 ≤ t)
    (hcons : n.awakeSince = none ∨ t = n.st.t + 1) :
    GradesDueAt C (record_awake n t).awakeSince t st0.saved_grades := by
  obtain ⟨r0, k1, k2, k3, k4⟩ := update_grades_results h0
  cases hn : n.awakeSince with
  | none =>
    have : (record_awake n t).awakeSince = some t := by simp [record_awake, Id.run, hn]; rfl
    rw [this]
    exact gradesDueAt_of_wake ht r0
  | some a =>
    have hra : record_awake n t = n := by simp [record_awake, Id.run, hn]; rfl
    rw [hra] at k1 k2 k3 k4 ⊢
    rw [hn]
    have htt : t = n.st.t + 1 := hcons.resolve_left (by simp [hn])
    have hold : GradesDueAt C (some a) (t - 1) n.st.saved_grades := by
      rw [show t - 1 = n.st.t by time_omega, ← hn]
      exact hdue
    exact gradesDueAt_step hold r0 k1 k2 k3 k4

/-! ## The results the duties read are computed -/

/-- If the wake test `n.awake_since t₀` passes, the node has been awake since some `a` with
    `a ≤ t₀`. -/
theorem awake_since_eq_true {n : NodeState V} {t₀ : Time} (h : n.awake_since t₀ = true) :
    ∃ a, n.awakeSince = some a ∧ a ≤ t₀ := by
  cases ha : n.awakeSince with
  | none => simp [NodeState.awake_since, Id.run, ha] at h
  | some a =>
    refine ⟨a, rfl, ?_⟩
    simp [NodeState.awake_since, Id.run, ha, Option.value] at h
    exact of_decide_eq_true h

/-- In the tick at `t`, after the grades update, the saved grades are at `t`'s round, and its
    grade-1 result is computed when the node passes the grade-1 wake test of that round: the result
    the proposal and the Goldfish vote read. -/
theorem due_g1 {C : Config} {P : Provisional V} {n : NodeState V} {t : Time} {st0 : Store V}
    (hdue : GradesDue C n) (h0 : update_grades C P (record_awake n t).st t = .ok st0)
    (ht : 0 ≤ t) (hcons : n.awakeSince = none ∨ t = n.st.t + 1)
    (hawake : (record_awake n t).awake_since (grade1_window_start C (roundAt C t)) = true) :
    st0.saved_grades.round = roundAt C t ∧ st0.saved_grades.current.g1 ≠ .pending := by
  obtain ⟨-, hr, hcl⟩ := gradesDueAt_update hdue h0 ht hcons
  obtain ⟨a, ha, hle⟩ := awake_since_eq_true hawake
  rw [← hr] at hle
  exact ⟨hr, (hcl a ha).1 hle⟩

/-- In the tick at `t`, after the grades update, the saved grades are at `t`'s round, and its
    grade-1 and grade-2 results are computed when the node passes the grade-2 wake test of that
    round: the results the confirmation reads. -/
theorem due_g2 {C : Config} {P : Provisional V} {n : NodeState V} {t : Time} {st0 : Store V}
    (hdue : GradesDue C n) (h0 : update_grades C P (record_awake n t).st t = .ok st0)
    (ht : 0 ≤ t) (hcons : n.awakeSince = none ∨ t = n.st.t + 1)
    (hawake : (record_awake n t).awake_since (grade2_window_start C (roundAt C t)) = true) :
    st0.saved_grades.round = roundAt C t ∧ st0.saved_grades.current.g1 ≠ .pending ∧
      st0.saved_grades.current.g2 ≠ .pending := by
  obtain ⟨-, hr, hcl⟩ := gradesDueAt_update hdue h0 ht hcons
  obtain ⟨a, ha, hle⟩ := awake_since_eq_true hawake
  rw [← hr] at hle
  have hΔ := C.Δ_pos
  have hle1 : a ≤ grade1_window_start C st0.saved_grades.round := by
    rw [grade1_window_start_eq]; rw [grade2_window_start_eq] at hle; time_omega
  exact ⟨hr, (hcl a ha).1 hle1, (hcl a ha).2.1 hle⟩

/-- In the tick at the attestation time `t` of its round, after the grades update, the saved grades
    are at `t`'s round, and its grade-0, grade-1 and grade-2 results are computed when the node
    passes the grade-2 wake test of that round: the results the attestation reads. -/
theorem due_attest {C : Config} {P : Provisional V} {n : NodeState V} {t : Time}
    {st0 : Store V} (hdue : GradesDue C n)
    (h0 : update_grades C P (record_awake n t).st t = .ok st0)
    (ht : 0 ≤ t) (hcons : n.awakeSince = none ∨ t = n.st.t + 1)
    (htime : t = C.round_attestation_time (roundAt C t))
    (hawake : (record_awake n t).awake_since (grade2_window_start C (roundAt C t)) = true) :
    st0.saved_grades.round = roundAt C t ∧ st0.saved_grades.current.g0 ≠ .pending ∧
      st0.saved_grades.current.g1 ≠ .pending ∧ st0.saved_grades.current.g2 ≠ .pending := by
  obtain ⟨hr, h1, h2⟩ := due_g2 hdue h0 ht hcons hawake
  obtain ⟨-, -, hcl⟩ := gradesDueAt_update hdue h0 ht hcons
  obtain ⟨a, ha, hle⟩ := awake_since_eq_true hawake
  rw [← hr] at hle htime
  have hΔ := C.Δ_pos
  refine ⟨hr, (hcl a ha).2.2.1 hle ?_, h1, h2⟩
  rw [htime, Config.round_attestation_time]
  time_omega

/-! ## The steps -/

/-- The initial node state has its grades due. -/
theorem gradesDue_initial (C : Config) (v : V) : GradesDue C (initial C v) := by
  have hΔ := C.Δ_pos
  have hL := roundLength_ge C
  have h0 : roundAt C 0 = 0 := by simp [roundAt, Config.slotOf, Config.round_of]
  refine ⟨le_refl _, ?_, fun a _ => ?_⟩
  · simp only [initial, Store.init, initial_saved_grades]
    exact h0.symm
  · simp only [initial, Store.init, initial_saved_grades, empty_round_grades, ne_eq,
      reduceCtorEq, not_false_eq_true, implies_true, true_and]
    intro _ hle
    rw [opening_succ] at hle
    have : C.opening 0 = 0 := by simp [Config.opening, Config.proposal_time]
    rw [this] at hle
    exfalso; time_omega

/-- The wake keeps the grades due. -/
theorem gradesDue_wake {C : Config} {n : NodeState V} (hdue : GradesDue C n) :
    GradesDue C (wake n) := by
  obtain ⟨h2, h3, -⟩ := hdue
  refine ⟨h2, h3, fun a ha => ?_⟩
  simp [wake, Id.run] at ha

/-- A step that replaces the store by `make_grades_compatible_with_finalized` of a frame of it, and
    keeps the wake value, keeps the grades due. -/
theorem gradesDue_of_frame {C : Config} {n n' : NodeState V} {st' : Store V}
    (hdue : GradesDue C n) (hf : Frame n.st st')
    (hst : n'.st = make_grades_compatible_with_finalized st')
    (haw : n'.awakeSince = n.awakeSince) : GradesDue C n' := by
  rw [gradesDue_iff] at hdue ⊢
  rw [hst, haw]
  change GradesDueAt C n.awakeSince st'.t
    (make_saved_grades_compatible_with st'.F st'.saved_grades)
  rw [hf.2.1, hf.2.2.2]
  exact gradesDueAt_compat _ hdue

/-- Receiving a block keeps the grades due. -/
theorem gradesDue_receive_block {C : Config} (P : Provisional V) {n : NodeState V}
    (B : Block V) (hdue : GradesDue C n) : GradesDue C (receive_block C P n B) :=
  gradesDue_of_frame hdue (frame_on_block C P n.st B) rfl rfl

/-- Receiving a Goldfish vote keeps the grades due. -/
theorem gradesDue_receive_goldfish_vote {C : Config} (P : Provisional V) {n : NodeState V}
    (u : GoldfishVote V) (hdue : GradesDue C n) : GradesDue C (receive_goldfish_vote P n u) :=
  gradesDue_of_frame hdue (frame_on_goldfish_vote_checked P n.st u) rfl rfl

/-- Receiving an attestation keeps the grades due. -/
theorem gradesDue_receive_attestation {C : Config} {n : NodeState V} (a : Attestation V)
    (hdue : GradesDue C n) : GradesDue C (receive_attestation C n a) :=
  gradesDue_of_frame hdue (frame_admit_attestation C n.st a) rfl rfl

/-- The tick keeps the grades due: a tick at `t ≥ 0` that answers from a node whose grades are due
    and follows a wake or the store's clock by one time unit leaves the grades due. -/
theorem gradesDue_tick {C : Config} {P : Provisional V} {X : External V} {n : NodeState V}
    {t : Time} {out : NodeState V × List (NamedObject V)}
    (h : (tick C P X n t).run [] = .ok out) (hdue : GradesDue C n) (ht : 0 ≤ t)
    (hcons : n.awakeSince = none ∨ t = n.st.t + 1) :
    GradesDue C out.1 := by
  obtain ⟨st0, st5, h0, hf, hst, haw, -⟩ := tick_outcome h
  have hdue0 := gradesDueAt_update hdue h0 ht hcons
  rw [gradesDue_iff, hst, haw]
  change GradesDueAt C _ st5.t (make_saved_grades_compatible_with st5.F st5.saved_grades)
  rw [hf.2.1, hf.2.2.2]
  exact gradesDueAt_compat _ hdue0

/-- An answer of the tick at `t` has the clock `t`. -/
theorem tick_clock {C : Config} {P : Provisional V} {X : External V} {n : NodeState V}
    {t : Time} {out : NodeState V × List (NamedObject V)}
    (h : (tick C P X n t).run [] = .ok out) : out.1.st.t = t := by
  obtain ⟨st0, st5, -, hf, hst, -, -⟩ := tick_outcome h
  rw [hst]
  exact hf.2.1

end SpecRecord.NoRaise
