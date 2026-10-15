import Proofs.Instance.NoRaise.Routines
import Proofs.Instance.NoRaise.GradesDue

/-!
# The spec's tick answers

`tick_ok`: from a node state whose tree has distinct roots, whose store is stamped and whose grades
are due, the tick at a non-negative time `t` that follows a wake or the store's clock by one time
unit answers, and its answer is stamped and has its grades due.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SpecRecord.NoRaise

open Spec Spec.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Walkers -/

/-- An `optStep` run from `l` is its step run from `l` when the condition holds, and answers its
    argument with `l` otherwise. -/
theorem optStep_run {α : Type} (c : Prop) [Decidable c] (f : α → DREB V α) (a : α)
    (l : List (NamedObject V)) :
    (optStep c f a).run l = if c then (f a).run l else .ok (a, l) := by
  unfold optStep
  split_ifs <;> rfl

/-- If `x` answers from `l` with an answer satisfying `Q`, and `f` answers from every answer
    satisfying `Q`, then `x >>= f` answers from `l`. -/
theorem DREB.bind_ok_post {α β : Type} {x : DREB V α} {f : α → DREB V β}
    {l : List (NamedObject V)} (Q : α × List (NamedObject V) → Prop)
    (hx : ∃ p, x.run l = .ok p ∧ Q p) (hf : ∀ p, Q p → ∃ q, (f p.1).run p.2 = .ok q) :
    ∃ q, (x >>= f).run l = .ok q := by
  obtain ⟨⟨a, l'⟩, hx, hq⟩ := hx
  rw [StateT.run_bind, hx]
  exact hf _ hq

/-- `record_awake` keeps the store. -/
theorem record_awake_st (n : NodeState V) (t : Time) : (record_awake n t).st = n.st := by
  simp only [record_awake, Id.run]
  split_ifs <;> rfl

/-! ## The attestation never falls on a proposal or a vote time -/

/-- For `Δ > 0` and `k` equal to `0` or `1`, `4Δa + 6Δ` is not `4Δb + kΔ`. -/
theorem four_mul_add_six_ne {Δ a b : Int} (hΔ : 0 < Δ) (k : Int) (hk : k = 0 ∨ k = 1)
    (h : 4 * Δ * a + 6 * Δ = 4 * Δ * b + k * Δ) : False := by
  have h' : Δ * (4 * a + 6 - 4 * b - k) = 0 := by linarith
  rcases mul_eq_zero.mp h' with h'' | h'' <;> omega

/-- Round `r`'s attestation time is no slot's proposal time. -/
theorem round_attestation_time_ne_proposal_time (C : Config) (r : Round) (s : Slot) :
    C.round_attestation_time r ≠ C.proposal_time s := by
  intro h
  simp only [Config.round_attestation_time, Config.opening, Config.proposal_time] at h
  exact four_mul_add_six_ne (a := ((r * C.R : Nat) : Int)) (b := (s : Int)) C.Δ_pos 0
    (Or.inl rfl) (by linarith)

/-- Round `r`'s attestation time is no slot's Goldfish vote time. -/
theorem round_attestation_time_ne_vote_time (C : Config) (r : Round) (s : Slot) :
    C.round_attestation_time r ≠ C.vote_time s := by
  intro h
  simp only [Config.round_attestation_time, Config.opening, Config.vote_time,
    Config.proposal_time] at h
  exact four_mul_add_six_ne (a := ((r * C.R : Nat) : Int)) (b := (s : Int)) C.Δ_pos 1
    (Or.inr rfl) (by linarith)

/-! ## The three slot duties -/

/-- The tick's three slot duties, each behind its condition `c1`, `c2`, `c3`, answer from every list
    on a stamped store `st` whose tree has distinct roots, when each condition gives the grade
    results its duty reads and no two conditions hold together; when neither the proposal nor the
    vote ran, the answer has the tree, the saved grades and the slot of `st`. -/
theorem slot_duties_ok (C : Config) (P : Provisional V) (X : External V) (v : V) (s : Slot)
    {c1 c2 c3 : Prop} [Decidable c1] [Decidable c2] [Decidable c3] {st : Store V}
    (hT : DistinctRoots st.T) (hst : Stamped st)
    (h1 : c1 → (saved_round_grades st.saved_grades (C.round_of st.s)).g1 ≠ .pending)
    (h2 : c2 → (saved_round_grades st.saved_grades (C.round_of st.s)).g1 ≠ .pending)
    (h3 : c3 → (saved_round_grades st.saved_grades (C.round_of st.s)).g1 ≠ .pending ∧
      (saved_round_grades st.saved_grades (C.round_of st.s)).g2 ≠ .pending)
    (h12 : c1 → ¬ c2) (h13 : c1 → ¬ c3) (h23 : c2 → ¬ c3) (l : List (NamedObject V))
    (Q : Store V × List (NamedObject V) → Prop)
    (hQ : ∀ out, (¬ c1 → ¬ c2 →
      out.1.T = st.T ∧ out.1.saved_grades = st.saved_grades ∧ out.1.s = st.s) → Q out) :
    ∃ out, (do
      let st2 ← optStep c1 (propose_block C P X v) st
      let st3 ← optStep c2 (goldfish_vote C P v) st2
      optStep c3 (fun st => liftM (update_confirmation C st (s - 1))) st3 :
        DREB V (Store V)).run l = .ok out ∧ Q out := by
  by_cases hc1 : c1
  · obtain ⟨⟨st2, l2⟩, hp⟩ := propose_block_ok C P X v hT (h1 hc1) l
    have hr : (optStep c1 (propose_block C P X v) st).run l = .ok (st2, l2) := by
      rw [optStep_run, if_pos hc1, hp]
    rw [StateT.run_bind, hr, DRE.bind_ok, StateT.run_bind, optStep_run, if_neg (h12 hc1),
      DRE.bind_ok, optStep_run, if_neg (h13 hc1)]
    exact ⟨_, rfl, hQ _ fun h => absurd hc1 h⟩
  · have hr : (optStep c1 (propose_block C P X v) st).run l = .ok (st, l) := by
      rw [optStep_run, if_neg hc1]
    rw [StateT.run_bind, hr, DRE.bind_ok]
    by_cases hc2 : c2
    · obtain ⟨⟨st3, l3⟩, hp⟩ := goldfish_vote_ok C P v hT hst (h2 hc2) l
      rw [StateT.run_bind, optStep_run, if_pos hc2, hp, DRE.bind_ok, optStep_run,
        if_neg (h23 hc2)]
      exact ⟨_, rfl, hQ _ fun _ h => absurd hc2 h⟩
    · rw [StateT.run_bind, optStep_run, if_neg hc2, DRE.bind_ok, optStep_run]
      by_cases hc3 : c3
      · obtain ⟨st4, hu⟩ := update_confirmation_ok C hT hst (h3 hc3).1 (h3 hc3).2 (s - 1)
        rw [if_pos hc3, hu]
        refine ⟨_, rfl, hQ _ fun _ _ => ?_⟩
        rw [update_confirmation_writes_only_confirmation hu]
        exact ⟨rfl, rfl, rfl⟩
      · rw [if_neg hc3]
        exact ⟨_, rfl, hQ _ fun _ _ => ⟨rfl, rfl, rfl⟩⟩

/-! ## The tick -/

/-- From a node state whose tree has distinct roots, whose store is stamped and whose grades are
    due, the tick at a non-negative time `t` that follows a wake or the store's clock by one time
    unit answers, and its answer's store is stamped and has its grades due. -/
theorem tick_ok (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) (t : Time)
    (hroots : DistinctRoots n.st.T) (hst : Stamped n.st) (hdue : GradesDue C n)
    (hcons : n.awakeSince = none ∨ t = n.st.t + 1) (ht : 0 ≤ t) :
    ∃ out, (tick C P X n t).run [] = .ok out ∧ Stamped out.1.st ∧ GradesDue C out.1 := by
  suffices hex : ∃ out, (tick C P X n t).run [] = .ok out by
    obtain ⟨out, h⟩ := hex
    exact ⟨out, h, stamped_tick h hst, gradesDue_tick h hdue ht hcons⟩
  have hΔ := C.Δ_pos
  have hn0 := record_awake_st n t
  -- the grades update answers `st0`
  obtain ⟨st0, h0⟩ : ∃ st0, update_grades C P (record_awake n t).st t = .ok st0 := by
    rw [hn0]; exact update_grades_ok C P hroots hst t
  obtain ⟨hw, hr0⟩ := update_grades_writes_only_grades h0
  have hT0 : DistinctRoots st0.T := by
    have : st0.T = n.st.T := by rw [hw]; show (record_awake n t).st.T = n.st.T; rw [hn0]
    rw [this]; exact hroots
  have hst0 : Stamped st0 := stamped_update_grades h0 (hn0 ▸ hst)
  have hg : saved_round_grades st0.saved_grades (C.round_of (C.slotOf t)) =
      st0.saved_grades.current := saved_round_grades_of_round hr0
  rw [tick_eq_tickSteps]
  unfold tickSteps
  dsimp only
  rw [StateT.run_bind]
  have hl : (liftM (update_grades C P (record_awake n t).st t) : DREB V (Store V)).run []
      = .ok (st0, []) := by rw [h0]; rfl
  rw [hl, DRE.bind_ok]
  -- the slot duties answer
  refine DREB.bind_ok_post (fun p =>
    ((decide (t = C.round_attestation_time (C.round_of (C.slotOf t))) &&
        (record_awake n t).awake_since (grade2_window_start C (C.round_of (C.slotOf t)))) = true) →
      p.1.T = st0.T ∧ p.1.saved_grades = st0.saved_grades ∧ p.1.s = C.slotOf t) ?_ ?_
  · rw [optStep_run]
    split_ifs with hs
    · refine slot_duties_ok C P X _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ _ ?_
      · exact hT0
      · exact hst0
      · intro hc
        simp only [Bool.and_eq_true] at hc
        show (saved_round_grades st0.saved_grades (C.round_of (C.slotOf t))).g1 ≠ .pending
        rw [hg]
        exact (due_g1 hdue h0 ht hcons hc.2).2
      · intro hc
        simp only [Bool.and_eq_true] at hc
        show (saved_round_grades st0.saved_grades (C.round_of (C.slotOf t))).g1 ≠ .pending
        rw [hg]
        exact (due_g1 hdue h0 ht hcons hc.2).2
      · intro hc
        simp only [Bool.and_eq_true] at hc
        show (saved_round_grades st0.saved_grades (C.round_of (C.slotOf t))).g1 ≠ .pending ∧
          (saved_round_grades st0.saved_grades (C.round_of (C.slotOf t))).g2 ≠ .pending
        rw [hg]
        exact (due_g2 hdue h0 ht hcons hc.2).2
      · intro hc1 hc2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc1 hc2
        rw [Config.vote_time] at hc2
        time_omega
      · intro hc1 hc3
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc1 hc3
        rw [Config.gf_confirmation_time] at hc3
        time_omega
      · intro hc2 hc3
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc2 hc3
        rw [Config.gf_confirmation_time] at hc3
        rw [Config.vote_time] at hc2
        time_omega
      · intro out hout h4
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h4
        refine hout (fun hc1 => ?_) (fun hc2 => ?_)
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc1
          exact round_attestation_time_ne_proposal_time C _ _ (h4.1.symm.trans hc1.1.1)
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc2
          exact round_attestation_time_ne_vote_time C _ _ (h4.1.symm.trans hc2.1)
    · exact ⟨_, rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩
  -- the attestation answers, and the tick returns
  · rintro ⟨st4, l3⟩ hq
    refine DREB.bind_ok_of ?_ (fun _ _ => DREB.pure_ok _ _)
    rw [optStep_run]
    split_ifs with h4
    · obtain ⟨hT4, hg4, hs4⟩ := hq h4
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h4
      obtain ⟨-, hd0, hd1, hd2⟩ := due_attest hdue h0 ht hcons h4.1 h4.2
      have hgr : saved_round_grades st4.saved_grades (C.round_of st4.s) =
          st0.saved_grades.current := by rw [hg4, hs4, hg]
      refine attest_ok C _ (hT4 ▸ hT0) ?_ ?_ ?_ _ _
      · rw [hgr]; exact hd2
      · rw [hgr]; exact hd1
      · rw [hgr]; exact hd0
    · exact ⟨_, rfl⟩

end SpecRecord.NoRaise
