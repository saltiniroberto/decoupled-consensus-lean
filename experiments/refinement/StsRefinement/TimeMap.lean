module
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.MinMax

@[expose] public section

/-!
# Time maps

A refinement relates a refining protocol to a refined protocol of the sts framework. The two may
keep time on different clocks: a time map `τ` sends each refining time `t` to the refined time
`τ t` it stands for.

The sts framework's atomic semantics starts every execution at time `0` and moves time by exactly
one per `tickAllAwake` step. So a refined tick at `T` stands for a refining tick at some `t` with
`τ t = T`, and the next refined tick for a later refining tick: `τ 0 = 0`, and one refining time
unit moves `τ` by `0` or by `1` (`TimeMap`). A refining tick at `t + 1` with `τ (t + 1) = τ t + 1`
is a refined tick (`TimeMap.Visible t`); a refining tick at `t + 1` with `τ (t + 1) = τ t` does not
move refined time and is invisible to the refined protocol.

The page also holds the deadline conditions: when a refining promise "strictly before `D₁ t`"
lands, through `τ`, strictly before the refined promise `D₂ (τ t)` (`DeadlineFits`, with the
ordinary delay `DelayFits` as its case), and the example of a clock `k` times finer
(`TimeMap.div k`, `τ t = t / k`).
-/

set_option autoImplicit false

namespace StsRefinement

/-- **A time map** `τ`: from the refining protocol's times to the refined protocol's times. It
starts at `0`, and one refining time unit moves it by `0` or by `1`. Read aloud: refined time
never jumps, and several refining times may share one refined time. -/
structure TimeMap where
  /-- The refined time `τ t` standing for the refining time `t`. -/
  toFun : ℕ → ℕ
  /-- Refined time starts at `0`. -/
  zero : toFun 0 = 0
  /-- One refining time unit moves refined time by `0` or by `1`. -/
  step : ∀ t, toFun (t + 1) = toFun t ∨ toFun (t + 1) = toFun t + 1

instance : CoeFun TimeMap (fun _ => ℕ → ℕ) := ⟨TimeMap.toFun⟩

namespace TimeMap

variable (τ : TimeMap)

/-- The identity time map: the two protocols keep the same clock. -/
def id : TimeMap := ⟨fun t => t, rfl, fun _ => Or.inr rfl⟩

/-- `τ.Visible t`: the refining tick at the time `t + 1` moves refined time
(`τ (t + 1) = τ t + 1`), so it is a refined tick; otherwise it is hidden (`τ (t + 1) = τ t`). -/
def Visible (t : ℕ) : Prop := τ (t + 1) = τ t + 1

/-- `τ.Unbounded`: `τ` reaches every refined time: for every `T` some refining time `t` has
`T ≤ τ t`. -/
def Unbounded : Prop := ∀ T : ℕ, ∃ t : ℕ, T ≤ τ t

theorem le_succ (t : ℕ) : τ t ≤ τ (t + 1) := by rcases τ.step t with h | h <;> omega

theorem succ_le (t : ℕ) : τ (t + 1) ≤ τ t + 1 := by rcases τ.step t with h | h <;> omega

/-- `τ` is monotone. -/
theorem mono : Monotone τ := monotone_nat_of_le_succ τ.le_succ

/-- Refined time never runs ahead of refining time: `τ t ≤ t`. -/
theorem le_self (t : ℕ) : τ t ≤ t := by
  induction t with
  | zero => rw [τ.zero]
  | succ t ih => have := τ.succ_le t; omega

/-- Every refined time up to `τ t` is `τ` of a refining time up to `t`. -/
theorem exists_eq_of_le : ∀ (t T : ℕ), T ≤ τ t → ∃ t' ≤ t, τ t' = T := by
  intro t
  induction t with
  | zero => intro T hT; exact ⟨0, le_rfl, by rw [τ.zero] at hT ⊢; omega⟩
  | succ t ih =>
    intro T hT
    by_cases h : T ≤ τ t
    · obtain ⟨t', ht', he⟩ := ih T h; exact ⟨t', by omega, he⟩
    · exact ⟨t + 1, le_rfl, by have := τ.succ_le t; omega⟩

/-- When `τ` is unbounded, every refined time is `τ` of some refining time. -/
theorem surj (h : τ.Unbounded) (T : ℕ) : ∃ t, τ t = T := by
  obtain ⟨t, ht⟩ := h T
  obtain ⟨t', -, he⟩ := τ.exists_eq_of_le t T ht
  exact ⟨t', he⟩

open Classical in
/-- `τ.first T`: the least refining time `τ` sends to `T`, `0` when there is none. The refining
tick at `τ.first T` is the one the refined tick at `T` stands for. -/
noncomputable def first (T : ℕ) : ℕ := if h : ∃ t, τ t = T then Nat.find h else 0

/-- Under the identity time map every refining tick is visible. -/
theorem id_visible (t : ℕ) : TimeMap.id.Visible t := rfl

/-- A refining clock `k` times finer: `τ t = t / k`. -/
def div (k : ℕ) : TimeMap where
  toFun t := t / k
  zero := Nat.zero_div k
  step t := by
    show (t + 1) / k = t / k ∨ (t + 1) / k = t / k + 1
    rw [Nat.succ_div]
    split_ifs <;> simp

/-- The refining tick a visible refined tick stands for is the first refining time of its refined
time: `τ.Visible t → τ.first (τ (t + 1)) = t + 1`. -/
theorem first_of_visible {t : ℕ} (h : τ.Visible t) : τ.first (τ (t + 1)) = t + 1 := by
  classical
  unfold TimeMap.first
  rw [dif_pos ⟨t + 1, rfl⟩, Nat.find_eq_iff]
  refine ⟨rfl, fun n hn => ?_⟩
  have := τ.mono (show n ≤ t by omega)
  unfold TimeMap.Visible at h
  omega

/-- With `τ t = t / k`, the refining tick at `t + 1` is visible exactly when `k` divides `t + 1`. -/
theorem div_visible_iff (k t : ℕ) : (TimeMap.div k).Visible t ↔ k ∣ t + 1 := by
  show (t + 1) / k = t / k + 1 ↔ k ∣ t + 1
  rw [Nat.succ_div]
  split_ifs with h <;> simp [h]

end TimeMap

/-! ## Deadlines -/

/-- **The deadline condition.** `DeadlineFits τ D₁ D₂`: for every send time `t`, the last refining
time strictly before the refining deadline `D₁ t` maps, through `τ`, strictly before the refined
deadline `D₂ (τ t)`. Read aloud: a refining promise "delivered strictly before `D₁ t`" is, seen
through `τ`, a refined promise "delivered strictly before `D₂ (τ t)`". The lemmas that use it
take `t < D₁ t` where they need it. -/
def DeadlineFits (τ : TimeMap) (D₁ D₂ : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, τ (D₁ t - 1) < D₂ (τ t)

/-- **The delay condition**, the case of `DeadlineFits` for the deadlines of a network that
delivers within a delay after a global stabilisation time. `DelayFits τ GST₁ d₁ GST Δ`: a refining
promise "strictly before `max t GST₁ + d₁`" lands, through `τ`, strictly before the refined
deadline `max (τ t) GST + Δ`. -/
def DelayFits (τ : TimeMap) (GST₁ d₁ GST Δ : ℕ) : Prop :=
  DeadlineFits τ (fun t => max t GST₁ + d₁) (fun T => max T GST + Δ)

variable {τ : TimeMap}

/-- Under `DeadlineFits`, a refining delivery time strictly before the refining deadline maps
strictly before the refined deadline. -/
theorem deadline_of_fits {D₁ D₂ : ℕ → ℕ} (h : DeadlineFits τ D₁ D₂) {t t' : ℕ}
    (ht : t' < D₁ t) : τ t' < D₂ (τ t) :=
  lt_of_le_of_lt (τ.mono (by omega)) (h t)

/-- Under `DeadlineFits`, and when the deadline `D₁ t` is after the send time `t`, the refining
window up to its deadline maps into the refined window, so a receiver awake through the refined
window is awake through the refining one. -/
theorem window_of_fits {D₁ D₂ : ℕ → ℕ} (h : DeadlineFits τ D₁ D₂) {t t' : ℕ} (hD : t < D₁ t)
    (ht : t' ≤ D₁ t) : τ t' ≤ D₂ (τ t) := by
  have h1 := h t
  have h2 := τ.succ_le (D₁ t - 1)
  have h3 : D₁ t - 1 + 1 = D₁ t := by omega
  rw [h3] at h2
  have := τ.mono ht
  omega

/-- **The clock `k` times finer.** With `τ t = t / k`, a refining delay `d₁ ≤ k · (Δ − 1) + 1` from
`k · GST` fits the refined delay `Δ` from `GST`: one refined unit is lost to the rounding of the
send time. -/
theorem div_fits (k GST Δ d₁ : ℕ) (hk : 0 < k) (hΔ : 1 ≤ Δ) (hd : d₁ ≤ k * (Δ - 1) + 1) :
    DelayFits (TimeMap.div k) (k * GST) d₁ GST Δ := by
  intro t
  show (max t (k * GST) + d₁ - 1) / k < max (t / k) GST + Δ
  have h1 : max t (k * GST) + d₁ - 1 ≤ max t (k * GST) + k * (Δ - 1) := by omega
  have h2 : (max t (k * GST) + d₁ - 1) / k ≤ (max t (k * GST) + k * (Δ - 1)) / k :=
    Nat.div_le_div_right h1
  rw [Nat.add_mul_div_left _ _ hk] at h2
  have h3 : max t (k * GST) / k = max (t / k) GST := by
    rw [(show Monotone (fun n : ℕ => n / k) from fun a b h => Nat.div_le_div_right h).map_max,
      Nat.mul_div_cancel_left GST hk]
  rw [h3] at h2
  omega

/-- **The delay back, for conclusions.** With `τ t = t / k`, `k · Δ` refining units after `t` are
`Δ` refined units after `τ t`. -/
theorem div_back (k t Δ : ℕ) (hk : 0 < k) : TimeMap.div k (t + k * Δ) = TimeMap.div k t + Δ :=
  Nat.add_mul_div_left t Δ hk

end StsRefinement
