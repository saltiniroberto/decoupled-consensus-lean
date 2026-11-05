module
public import StsMultisetLog.Analysis.AtomicLemmas
public import StsRefinement.Notion

@[expose] public section

/-!
# Reading a refined execution back on the refining one

Given a `TimedProjection α μ ε τ x y`, the refined execution `y` stands for the refining
execution `x` through the step map `σ`. The facts here say what `y` tells about `x`: the refined
time, node states and sent log at `σ i` are those of `x[i]` seen through the maps; whatever holds at
every step of `y` holds of the projection of every step of `x` (safety reads back); and when the
refining time diverges and `τ` is unbounded, every step of `y` is `σ` of a step of `x`, so a refined
step at a time reads back as a refining step whose time `τ` sends there (liveness reads back).
-/

set_option autoImplicit false

namespace StsRefinement

open Framework.StsMultisetLog

variable {Node : Type} [DecidableEq Node]

section ReadBack

variable {Msg₁ St₁ Ev₁ Msg₂ St₂ Ev₂ : Type} [DecidableEq Msg₁] [DecidableEq Msg₂]
  {Pr₁ : Protocol Node Msg₁ St₁ Ev₁} {Pr₂ : Protocol Node Msg₂ St₂ Ev₂}
  {S₁ S₂ : Schedule Node} {α : St₁ → St₂} {μ : Msg₁ → Option Msg₂} {ε : Ev₁ → Option Ev₂}
  {τ : TimeMap}

/-- Atomic time is monotone along the steps., from the framework's `atomic_time_stepwise`. -/
theorem atomic_time_mono (y : AtomicExec Pr₂ S₂) : Monotone fun j : ℕ => y[j].time :=
  monotone_nat_of_le_succ fun j => by rcases atomic_time_stepwise y j with h | h <;> simp [h]

/-- Atomic time after `j` steps is at most `j`. -/
theorem atomic_time_le (y : AtomicExec Pr₂ S₂) (j : ℕ) : y[j].time ≤ j := by
  induction j with
  | zero => obtain ⟨h0, -, -⟩ := y.init; show (y.cfg 0).time ≤ 0; rw [h0]
  | succ j ih => rcases atomic_time_stepwise y j with h | h <;> omega

variable {x : AtomicExec Pr₁ S₁} {y : AtomicExec Pr₂ S₂} (P : TimedProjection α μ ε τ x y)

namespace TimedProjection

/-- The refined time at `σ i` is `τ` of the refining time at `i`. -/
theorem time (i : ℕ) : y[P.σ i].time = τ x[i].time := by rw [P.cfg i]; rfl

/-- The refined node state at `σ i` is `α` of the refining one at `i`. -/
theorem st (i : ℕ) (p : Node) : y[P.σ i][p].st = α x[i][p].st := by rw [P.cfg i]; rfl

/-- The refined sent log at `σ i` is the refining one's visible messages, mapped. -/
theorem sent (i : ℕ) : y[P.σ i].sent = x[i].sent.filterMap (SignedMsg.mapP μ) := by
  rw [P.cfg i]; rfl

theorem mono : Monotone P.σ :=
  monotone_nat_of_le_succ fun i => by rcases P.step i with h | h <;> omega

/-- Every refined step up to `σ i` is `σ` of a refining step up to `i`. -/
theorem exists_eq_of_le : ∀ (i j : ℕ), j ≤ P.σ i → ∃ i' ≤ i, P.σ i' = j := by
  intro i
  induction i with
  | zero => intro j hj; exact ⟨0, le_rfl, by rw [P.zero] at hj ⊢; omega⟩
  | succ i ih =>
    intro j hj
    by_cases h : j ≤ P.σ i
    · obtain ⟨i', hi', he⟩ := ih j h; exact ⟨i', by omega, he⟩
    · exact ⟨i + 1, le_rfl, by rcases P.step i with h' | h' <;> omega⟩

/-- **Every refined step stands for a refining step** when the refining time diverges and `τ` is
unbounded: then no continuation is needed. -/
theorem surj (hx : ∀ t : ℕ, ∃ i : ℕ, t ≤ x[i].time) (hτ : τ.Unbounded) (j : ℕ) :
    ∃ i : ℕ, P.σ i = j := by
  obtain ⟨t, ht⟩ := hτ (j + 1)
  obtain ⟨i, hi⟩ := hx t
  have h1 : j + 1 ≤ τ x[i].time := le_trans ht (τ.mono hi)
  have h2 : j < P.σ i := by
    by_contra hc
    have h3 := atomic_time_mono y (not_lt.mp hc)
    simp only at h3
    rw [P.time] at h3
    have := atomic_time_le y j
    omega
  obtain ⟨i', -, he⟩ := P.exists_eq_of_le i j h2.le
  exact ⟨i', he⟩

/-- A refined step `j` whose successor is reached is the image of a visible refining step. -/
theorem exists_visible (j i : ℕ) (h : j + 1 ≤ P.σ i) :
    ∃ i', P.σ i' = j ∧ P.σ (i' + 1) = j + 1 := by
  classical
  have hex : ∃ k, P.σ k = j + 1 := by
    obtain ⟨k, -, hk⟩ := P.exists_eq_of_le i (j + 1) h; exact ⟨k, hk⟩
  have hk : P.σ (Nat.find hex) = j + 1 := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by intro h0; rw [h0, P.zero] at hk; omega
  obtain ⟨k', hk'⟩ := Nat.exists_eq_add_one_of_ne_zero hk0
  have hmin : P.σ k' ≠ j + 1 := Nat.find_min hex (by omega)
  rw [hk'] at hk
  refine ⟨k', ?_, hk⟩
  rcases P.step k' with h' | h' <;> omega

/-- **A step at a time reads back** (the liveness fact): when every refined step stands for a
refining step, the refined execution has a step at time `T` with property `Q` exactly when the
refining execution has a step whose time `τ` sends to `T` and whose projection has `Q`. -/
theorem exists_at_time (hsurj : ∀ j : ℕ, ∃ i : ℕ, P.σ i = j) (T : ℕ)
    (Q : Config Node Msg₂ St₂ → Prop) :
    (∃ j : ℕ, y[j].time = T ∧ Q y[j]) ↔
      ∃ i : ℕ, τ x[i].time = T ∧ Q (Config.mapT α μ τ x[i]) := by
  constructor
  · rintro ⟨j, hj, hq⟩
    obtain ⟨i, rfl⟩ := hsurj j
    exact ⟨i, by rw [← P.time]; exact hj, by rw [← P.cfg]; exact hq⟩
  · rintro ⟨i, hi, hq⟩
    exact ⟨P.σ i, by rw [P.time]; exact hi, by rw [P.cfg]; exact hq⟩

include P in
/-- **Safety reads back**: whatever holds at every refined step holds of the projection of every
refining step. -/
theorem forall_steps (Q : Config Node Msg₂ St₂ → Prop) (h : ∀ j : ℕ, Q y[j]) (i : ℕ) :
    Q (Config.mapT α μ τ x[i]) := P.cfg i ▸ h (P.σ i)

/-- A refined tick at the image of a visible step is the image of a refining tick at a time
`t + 1` that moves refined time, with `τ (t + 1)` the refined time. -/
theorem tick_of_visible (i T : ℕ) (hv : P.σ (i + 1) = P.σ i + 1)
    (h : y.lbl (P.σ i) = .tickAllAwake T) :
    ∃ t, x.lbl i = .tickAllAwake (t + 1) ∧ τ.Visible t ∧ τ (t + 1) = T := by
  have hl := P.lbl_visible i hv
  rw [h] at hl
  cases hx : x.lbl i with
  | tickAllAwake t' =>
    rw [hx] at hl
    cases t' with
    | zero => simp [AtomicAction.mapT] at hl
    | succ t =>
      simp only [AtomicAction.mapT] at hl
      split_ifs at hl with hc
      · simp only [Option.some.injEq, AtomicAction.tickAllAwake.injEq] at hl
        exact ⟨t, rfl, hc, hl.symm⟩
  | deliver p m => rw [hx] at hl; simp [AtomicAction.mapT] at hl
  | custom p ev => rw [hx] at hl; simp [AtomicAction.mapT] at hl
  | adversarial p m => rw [hx] at hl; simp [AtomicAction.mapT] at hl
  | forward p m => rw [hx] at hl; simp [AtomicAction.mapT] at hl

end TimedProjection

end ReadBack

end StsRefinement
