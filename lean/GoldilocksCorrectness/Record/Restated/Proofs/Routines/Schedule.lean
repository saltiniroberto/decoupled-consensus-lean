module
public import GoldilocksCorrectness.Record.ScheduleGoldilocks
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# Schedule, over a slot layout

The theorems of `GoldilocksCorrectness/Proofs/Routines/Schedule.lean` that name a member of the
slot layout, over a slot layout `L` whose facts `SF : ScheduleFacts L` hold: the order of the
times of a slot, their growth with the slot, and the slot of a time, from `SF` alone; the exact
spacing, the times read back as the spec's integer times, and the wake windows' exact starts,
with the hypothesis `U : UniformSchedule L`. Four helpers come first: `times_le`,
`viewFreeze_add_Δ_le_slotStart_of_lt`, `times_mono`, `le_slotStart`.

The landed theorems that name no member of the slot layout are shared and get no twin:
`Δ_cast`, `one_le_Δ`, `slot_mono_int`, `voteTime_ne_cutoff`, `lockDeadline_injective`, `slot_le_of_t_lt`, `t_lt_of_lt`, `t_le_of_le`, `duty_window_start_mono`, `after_of_before`, `Δ_F_cast`, `t_add`, `t_one`, `proposal_window_start_eqJ`, `proposal_window_start_eq`, `lt_of_t_lt`, `proposal_window_start_zero_le`, `proposal_window_start_zero_le_duty`, `slotStart_ne_actionTime`, `duty_window_start_eq`, `t_eq_mul`, `anchorCW_eq`.

The recovery section at the end of the page states each landed theorem again, as the landed
statement (`type_of%`), and proves it from its record form at the spec's slot layout
`SlotLayout.goldilocks`, its facts `scheduleFacts_goldilocks` and, where the twin takes it,
`uniformSchedule_goldilocks`. This page sees the bodies of the library's times
(`import all` of `Statements/Routines/ScheduleDefs.lean`) for that section only: at the spec's
slot layout each member is the library's time by definition.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks (duty_window_start)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F anchorCW)
open GoldilocksCorrectness.Proofs.Routines (Δ_cast Δ_F_cast one_le_Δ t_eq_mul t_add t_one
  duty_window_start_eq anchorCW_eq)

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (L : SlotLayout V) (SF : ScheduleFacts L)
include L SF

/-- The four duty times of slot `s` are at least `Δ S` apart, the next slot starts at least `Δ S`
after slot `s`'s view freeze, and `Δ S` is at least `1`: the first four fields of `ScheduleFacts`
at slot `s`, and `one_le_Δ`.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`: the slot.

Read aloud: slot `s`'s start, vote time, support cutoff and view freeze, and slot `s + 1`'s start,
come in that order, each at least `Δ S` after the one before. -/
theorem times_le (S : Setup V) (s : ℕ) :
    L.slotStart S.C s + Δ S ≤ L.voteTime S.C s ∧ L.voteTime S.C s + Δ S ≤ L.supportCutoff S.C s ∧
      L.supportCutoff S.C s + Δ S ≤ L.viewFreeze S.C s ∧
      L.viewFreeze S.C s + Δ S ≤ L.slotStart S.C (s + 1) ∧ 1 ≤ Δ S :=
  ⟨SF.slotStart_add_Δ_le_voteTime S s, SF.voteTime_add_Δ_le_supportCutoff S s,
    SF.supportCutoff_add_Δ_le_viewFreeze S s, SF.viewFreeze_add_Δ_le_slotStart_succ S s, one_le_Δ S⟩

/-- A later slot starts at least `Δ S` after an earlier slot's view freeze.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s < s'`: the two slots.

Read aloud: when `s < s'`, slot `s'` starts at least `Δ S` after slot `s`'s view freeze. -/
theorem viewFreeze_add_Δ_le_slotStart_of_lt (S : Setup V) {s s' : ℕ} (h : s < s') :
    L.viewFreeze S.C s + Δ S ≤ L.slotStart S.C s' := by
  obtain ⟨d, rfl⟩ : ∃ d, s' = s + 1 + d := ⟨s' - (s + 1), by omega⟩
  induction d with
  | zero => exact SF.viewFreeze_add_Δ_le_slotStart_succ S s
  | succ d ih =>
    have h1 := ih (by omega)
    have h2 := times_le L SF S (s + 1 + d)
    rw [show s + 1 + (d + 1) = s + 1 + d + 1 by omega]
    omega

/-- The four duty times grow with the slot.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s ≤ s'`: the two slots.

Read aloud: a later slot's start, vote time, support cutoff and view freeze are each no earlier. -/
theorem times_mono (S : Setup V) {s s' : ℕ} (h : s ≤ s') :
    L.slotStart S.C s ≤ L.slotStart S.C s' ∧ L.voteTime S.C s ≤ L.voteTime S.C s' ∧
      L.supportCutoff S.C s ≤ L.supportCutoff S.C s' ∧ L.viewFreeze S.C s ≤ L.viewFreeze S.C s' := by
  rcases Nat.eq_or_lt_of_le h with rfl | hlt
  · exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  · have := viewFreeze_add_Δ_le_slotStart_of_lt L SF S hlt
    have := times_le L SF S s
    have := times_le L SF S s'
    omega

/-- A slot starts no earlier than its number: slots last at least `4 * Δ S ≥ 1`.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`: the slot.

Read aloud: slot `s` starts at a time at least `s`. -/
theorem le_slotStart (S : Setup V) (s : ℕ) : s ≤ L.slotStart S.C s := by
  induction s with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have := times_le L SF S n
    omega

/-- The start of slot `s` read back as an integer is `S.C.t_ s`.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `s`: the slot.

Read aloud: the start of slot `s`, read as an integer, is the spec's `S.C.t_ s`. -/
theorem slotStart_cast (U : UniformSchedule L) (S : Setup V) (s : ℕ) :
    ((L.slotStart S.C s : ℕ) : Int) = S.C.t_ s := by
  rw [U.slotStart_eq, t_eq_mul]
  push_cast
  rw [Δ_cast]

/-- The vote time of slot `s` read back as an integer is `S.C.t_ s + S.C.Δ`.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `s`: the slot.

Read aloud: slot `s`'s vote time, read as an integer, is the spec's `S.C.t_ s + S.C.Δ`. -/
theorem voteTime_cast (U : UniformSchedule L) (S : Setup V) (s : ℕ) :
    ((L.voteTime S.C s : ℕ) : Int) = S.C.t_ s + S.C.Δ := by
  have h1 := slotStart_cast L SF U S s
  have h2 := Δ_cast S
  rw [U.voteTime_eq]
  omega

/-- The support cutoff of slot `s` read back as an integer is `S.C.t_ s + 2 * S.C.Δ`.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `s`: the slot.

Read aloud: slot `s`'s support cutoff, read as an integer, is the spec's `S.C.t_ s + 2 * S.C.Δ`. -/
theorem supportCutoff_cast (U : UniformSchedule L) (S : Setup V) (s : ℕ) :
    ((L.supportCutoff S.C s : ℕ) : Int) = S.C.t_ s + 2 * S.C.Δ := by
  have h1 := slotStart_cast L SF U S s
  have h2 := Δ_cast S
  rw [U.supportCutoff_eq]
  omega

/-- Slot `s` starts at `4 * Δ S * s`.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `s`: the slot.

Read aloud: slot `s` starts at `4 * Δ S * s`. -/
theorem slotStart_eq (U : UniformSchedule L) (S : Setup V) (s : ℕ) :
    L.slotStart S.C s = 4 * Δ S * s := by
  exact U.slotStart_eq S s

/-- The vote time of slot `s` is one delay after its start.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `s`: the slot.

Read aloud: slot `s`'s vote time is `Δ S` after its start. -/
theorem voteTime_eq (U : UniformSchedule L) (S : Setup V) (s : ℕ) :
    L.voteTime S.C s = L.slotStart S.C s + Δ S := by
  exact U.voteTime_eq S s

/-- The support cutoff of slot `s` is one delay after its vote time.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `s`: the slot.

Read aloud: slot `s`'s support cutoff is `Δ S` after its vote time. -/
theorem supportCutoff_eq (U : UniformSchedule L) (S : Setup V) (s : ℕ) :
    L.supportCutoff S.C s = L.voteTime S.C s + Δ S := by
  rw [U.supportCutoff_eq, U.voteTime_eq]
  omega

/-- The vote time of slot `s + 1` is four delays after the vote time of slot `s`.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `s`: the slot.

Read aloud: the vote time of slot `s + 1` is `4 * Δ S` after slot `s`'s. -/
theorem voteTime_succ (U : UniformSchedule L) (S : Setup V) (s : ℕ) :
    L.voteTime S.C (s + 1) = L.voteTime S.C s + 4 * Δ S := by
  rw [U.voteTime_eq S (s + 1), U.voteTime_eq S s, U.slotStart_eq S (s + 1), U.slotStart_eq S s,
    Nat.mul_add, Nat.mul_one]
  omega

/-- The slot of a natural-number time `t` is `t / (4 * Δ S)`.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `t`: the time.

Read aloud: the time `t` is in slot `t / (4 * Δ S)`. -/
theorem slot_natCast (U : UniformSchedule L) (S : Setup V) (t : ℕ) :
    L.slot S.C t = t / (4 * Δ S) := by
  exact U.slot_eq S t

/-- The slot of a natural-number time grows with the time.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `t ≤ t'`: the two times.

Read aloud: a later time is in the same slot or a later one. -/
theorem slot_mono (S : Setup V) {t t' : ℕ} (h : t ≤ t') :
    L.slot S.C t ≤ L.slot S.C t' := by
  exact (SF.slotStart_le_iff S _ t').1 (le_trans ((SF.slotStart_le_iff S _ t).2 le_rfl) h)

/-- A time from the start of slot `s` and strictly before the start of slot `s + 1` is in slot
`s`.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`: the slot; `t`: the time.

Read aloud: a time from the start of slot `s` and before the start of slot `s + 1` is in slot `s`. -/
theorem slot_eq_of_mem (S : Setup V) {s t : ℕ} (h1 : L.slotStart S.C s ≤ t)
    (h2 : t < L.slotStart S.C (s + 1)) :
    L.slot S.C t = s := by
  have a := (SF.slotStart_le_iff S s t).1 h1
  have b : ¬ (s + 1 ≤ L.slot S.C t) := fun hc => absurd ((SF.slotStart_le_iff S (s + 1) t).2 hc) (by omega)
  omega

/-- The view freeze of slot `s` read back as an integer is `S.C.t_ s + 3 * S.C.Δ`.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `s`: the slot.

Read aloud: slot `s`'s view freeze, read as an integer, is the spec's `S.C.t_ s + 3 * S.C.Δ`. -/
theorem viewFreeze_cast (U : UniformSchedule L) (S : Setup V) (s : ℕ) :
    ((L.viewFreeze S.C s : ℕ) : Int) = S.C.t_ s + 3 * S.C.Δ := by
  have h1 := slotStart_cast L SF U S s
  have h2 := Δ_cast S
  rw [U.viewFreeze_eq]
  omega

/-- The view freeze of slot `s` is three delays after its start.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `s`: the slot.

Read aloud: slot `s`'s view freeze is `3 * Δ S` after its start. -/
theorem viewFreeze_eq (U : UniformSchedule L) (S : Setup V) (s : ℕ) :
    L.viewFreeze S.C s = L.slotStart S.C s + 3 * Δ S := by
  exact U.viewFreeze_eq S s

/-- A time is at least the start of slot `s` exactly when its slot is at least `s`.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`: the slot; `t`: the time.

Read aloud: slot `s` has started at `t` exactly when the slot of `t` is `s` or later. -/
theorem slotStart_le_iff (S : Setup V) (s t : ℕ) :
    L.slotStart S.C s ≤ t ↔ s ≤ L.slot S.C t := by
  exact SF.slotStart_le_iff S s t

/-- The duty window of slot `s + 1` starts no later than slot `s`: `duty_window_start S.C (s + 1)
= S.C.t_ (s + 1) + S.C.Δ − 4 · S.C.Δ · S.C.k`, and `S.C.k ≥ 2`.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`: the slot.

Read aloud: a validator awake from the duty window's start of slot `s + 1` is awake from the start
of slot `s`. -/
theorem dutyWindowStart_succ_le_slotStart (S : Setup V) (s : ℕ) :
    L.dutyWindowStart S.C (s + 1) ≤ L.slotStart S.C s := by
  exact SF.dutyWindowStart_succ_le_slotStart S s

/-- A time before the start of slot `s` is in a slot less than `s`.

The variables:
- `L`: the slot layout; `SF`: its facts.

Read aloud: a time before slot `s` starts is in a slot less than `s`. -/
theorem slot_lt_of_lt_slotStart (S : Setup V) {s t : ℕ} (h : t < L.slotStart S.C s) :
    L.slot S.C t < s := by
  by_contra hc
  have := (SF.slotStart_le_iff S s t).2 (by omega)
  omega

/-- **Kit fact, slots against support cutoffs.** When the support cutoff of slot `s_a + 1` is before
the vote time of slot `s`, then `s_a + 2 ≤ s`; when it is before the support cutoff of slot
`s + 1`, then `s_a < s`; when it is at most that cutoff, then `s_a ≤ s`.

Why: slot `s` starts at `4Δ · s`, its vote time is `Δ` later and its support cutoff `2Δ` later.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s_a`, `s`: the two slots.

Read aloud: a support cutoff before a vote time is two slots earlier; before or at a support
cutoff, one slot earlier or the same.

 -/
theorem slot_le_of_supportCutoff_lt (S : Setup V) (s_a s : ℕ) :
    (L.supportCutoff S.C (s_a + 1) < L.voteTime S.C s → s_a + 2 ≤ s) ∧
    (L.supportCutoff S.C (s_a + 1) < L.supportCutoff S.C (s + 1) → s_a < s) ∧
    (L.supportCutoff S.C (s_a + 1) ≤ L.supportCutoff S.C (s + 1) → s_a ≤ s) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · by_contra hc
    have := times_mono L SF S (show s ≤ s_a + 1 by omega)
    have := times_le L SF S (s_a + 1)
    omega
  · by_contra hc
    have := times_mono L SF S (show s + 1 ≤ s_a + 1 by omega)
    omega
  · by_contra hc
    have := viewFreeze_add_Δ_le_slotStart_of_lt L SF S (show s + 1 < s_a + 1 by omega)
    have := times_le L SF S (s + 1)
    have := times_le L SF S (s_a + 1)
    omega

/-- The support cutoff grows strictly with the slot.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`, `s'`: two slots, `s` before `s'`.

Read aloud: a later slot's support cutoff is strictly later. -/
theorem supportCutoff_lt_of_lt (S : Setup V) {s s' : ℕ} (h : s < s') :
    L.supportCutoff S.C s < L.supportCutoff S.C s' := by
  have := viewFreeze_add_Δ_le_slotStart_of_lt L SF S h
  have := times_le L SF S s
  have := times_le L SF S s'
  omega

/-- The duty window of slot `s` starts no later than the support cutoff of every slot `s'` with
`s ≤ s' + S.C.k`: the window starts at `S.C.t_ s + S.C.Δ − 4 · S.C.Δ · S.C.k`, or at `0` when that
value is negative.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `s`: the slot of the duty window; `s'`: the slot of the cutoff.

Read aloud: slot `s`'s duty window starts no later than the support cutoff of every slot `s'` with `s ≤ s' + S.C.k`. -/
theorem dutyWindowStart_le_supportCutoff (U : UniformSchedule L) (S : Setup V) {s s' : ℕ} (hj : s ≤ s' + S.C.k) :
    L.dutyWindowStart S.C s ≤ L.supportCutoff S.C s' := by
  rw [U.dutyWindowStart_eq, U.supportCutoff_eq, U.slotStart_eq S s, U.slotStart_eq S s']
  have h := Nat.mul_le_mul_left (4 * Δ S) hj
  rw [Nat.mul_add] at h
  omega

/-- The start of a slot grows with the slot.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`, `s'`: two slots, `s` at most `s'`.

Read aloud: a later slot starts no earlier. -/
theorem slotStart_mono (S : Setup V) {s s' : ℕ} (h : s ≤ s') :
    L.slotStart S.C s ≤ L.slotStart S.C s' := by
  exact (times_mono L SF S h).1

/-- The duty window of slot `s + 1` starts no later than the support cutoff of every slot `s'` with
`s + 1 ≤ s' + S.C.k`: the window starts at `S.C.t_ (s + 1) + S.C.Δ − 4 · S.C.Δ · S.C.k`, one delay
after the start of slot `s + 1 − S.C.k`, or at `0` when that value is negative.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `s`: the slot before the duty window's slot; `s'`: the slot of the cutoff.

Read aloud: a validator awake from the duty window's start of slot `s + 1` is awake from the
support cutoff of each of the last `S.C.k` slots up to `s`. -/
theorem dutyWindowStart_succ_le_supportCutoff (U : UniformSchedule L) (S : Setup V) {s s' : ℕ} (hj : s + 1 ≤ s' + S.C.k) :
    L.dutyWindowStart S.C (s + 1) ≤ L.supportCutoff S.C s' := by
  exact dutyWindowStart_le_supportCutoff L SF U S hj

/-- The times of the support cutoff of slot `s + 1`, when `s = r · R` is the first slot of round
`r`: its slot is `s + 1`, the round of that slot is `r`, and it is the action time of that round
and the support cutoff of its slot.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `r`: the round; `s`: its first slot.

Read aloud: when slot `s` is the first slot of round `r`, the support cutoff of slot `s + 1` is in slot `s + 1`, that slot is in round `r`, and the cutoff is round `r`'s action time and slot `s + 1`'s support cutoff in the spec's integer times. -/
theorem supportCutoff_succ_times (U : UniformSchedule L) (S : Setup V) (r s : ℕ) (hs : s = r * S.C.R) :
    L.slot S.C (L.supportCutoff S.C (s + 1)) = s + 1 ∧ S.C.round (s + 1) = r ∧
      ((L.supportCutoff S.C (s + 1) : ℕ) : Int) =
        S.C.a_ (S.C.round (L.slot S.C (L.supportCutoff S.C (s + 1)))) ∧
      ((L.supportCutoff S.C (s + 1) : ℕ) : Int) =
        S.C.t_ (L.slot S.C (L.supportCutoff S.C (s + 1))) + 2 * S.C.Δ := by
  have hslot : L.slot S.C (L.supportCutoff S.C (s + 1)) = s + 1 := by
    obtain ⟨a1, a2, a3, a4, hΔ⟩ := times_le L SF S (s + 1)
    exact slot_eq_of_mem L SF S (by omega) (by omega)
  have hR := S.C.R_ge_two
  have hround : S.C.round (s + 1) = r := by
    show (s + 1) / S.C.R = r
    rw [hs, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  have hc := supportCutoff_cast L SF U S (s + 1)
  refine ⟨hslot, hround, ?_, ?_⟩
  · rw [hslot, hround, hc]
    simp only [Goldilocks.Config.a_, Goldilocks.Config.T_]
    rw [← hs, t_add S s 1, t_one S]
    omega
  · rw [hslot]
    exact hc

/-- The duty window's start, as a natural number, grows with the slot.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`, `s'`: two slots, `s` at most `s'`.

Read aloud: a later slot's duty window starts no earlier. -/
theorem dutyWindowStart_mono (S : Setup V) {s s' : ℕ} (h : s ≤ s') :
    L.dutyWindowStart S.C s ≤ L.dutyWindowStart S.C s' := by
  exact SF.dutyWindowStart_mono S s s' h

/-- The start of a slot grows with the slot.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `a ≤ b`: the two slots.

Read aloud: a later slot starts no earlier. -/
theorem slotStart_le_of_le (S : Setup V) {a b : ℕ} (h : a ≤ b) :
    L.slotStart S.C a ≤ L.slotStart S.C b := by
  exact (times_mono L SF S h).1

/-- The support cutoff of a slot is no later than the start of the next slot.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`: the slot.

Read aloud: slot `s`'s support cutoff is no later than the start of slot `s + 1`. -/
theorem supportCutoff_le_slotStart_succ (S : Setup V) (s : ℕ) :
    L.supportCutoff S.C s ≤ L.slotStart S.C (s + 1) := by
  have := times_le L SF S s
  omega

/-- The support cutoff of slot `s + 1` is before that of slot `s + 2`.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`: the slot.

Read aloud: slot `s + 1`'s support cutoff is no later than slot `s + 2`'s. -/
theorem supportCutoff_succ_le (S : Setup V) (s : ℕ) :
    L.supportCutoff S.C (s + 1) ≤ L.supportCutoff S.C (s + 1 + 1) := by
  exact (times_mono L SF S (Nat.le_add_right (s + 1) 1)).2.2.1

/-- The duty window of slot `s` starts `4Δk − Δ` before the start of slot `s`, or at `0` when
that is negative.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `s`: the slot.

Read aloud: slot `s`'s duty window starts `4 * Δ S * S.C.k − Δ S` before slot `s` starts, or at `0` when that time would be negative. -/
theorem dutyWindowStart_cases (U : UniformSchedule L) (S : Setup V) (s : ℕ) :
    L.dutyWindowStart S.C s + 4 * Δ S * S.C.k = 4 * Δ S * s + Δ S ∨
      (L.dutyWindowStart S.C s = 0 ∧ 4 * Δ S * s + Δ S < 4 * Δ S * S.C.k) := by
  rw [U.dutyWindowStart_eq, U.slotStart_eq]
  omega

/-- **Every committee the premise constrains has its duty window inside the phase.** When slot
`s + 1` starts at or after `anchorCW S tGAT`, the duty window of slot `s` starts at least one
delay after `tGAT`.

Why: `slotStart S s ≥ tGAT + 4Δ(k + 1)`, and the duty window starts `4Δk − Δ` before it.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `tGAT`: the time every honest validator is awake from; `s`: the slot.

Read aloud: when slot `s + 1` starts at or after `anchorCW S tGAT`, slot `s`'s duty window starts at least `Δ S` after `tGAT`. -/
theorem dutyWindowStart_of_anchor (U : UniformSchedule L) (S : Setup V) (tGAT s : ℕ)
    (hA : anchorCW S tGAT ≤ L.slotStart S.C (s + 1)) :
    tGAT + Δ S ≤ L.dutyWindowStart S.C s := by
  rw [anchorCW_eq, U.slotStart_eq, Nat.mul_add, Nat.mul_add, Nat.mul_one] at hA
  rcases dutyWindowStart_cases L SF U S s with h | ⟨-, h⟩ <;> omega

/-- **The committee premise constrains every committee the front counts.** With `s_w ≥ 1` a slot
whose duty window starts at or after `tGAT`, `anchorCW S tGAT` is at most the start of slot
`s_w + k + 1`, so the premise constrains the committee of slot `s_w + k` and every later one.

Why: `tGAT + 4Δ ≤ 4Δ s_w`, from the duty window's start `4Δ s_w + Δ − 4Δk` with `k ≥ 2`, or from
`tGAT = 0` and `s_w ≥ 1` when that start is clamped to `0`.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `tGAT`: the time every honest validator is awake from; `s_w`: the slot.

Read aloud: when slot `s_w ≥ 1` has its duty window start at or after `tGAT`, `anchorCW S tGAT` is at most the start of slot `s_w + S.C.k + 1`. -/
theorem anchor_le_front (U : UniformSchedule L) (S : Setup V) (tGAT s_w : ℕ) (hs_w : 1 ≤ s_w)
    (hsw : tGAT ≤ L.dutyWindowStart S.C s_w) :
    anchorCW S tGAT ≤ L.slotStart S.C (s_w + S.C.k + 1) := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hk2 : 4 * Δ S * 2 ≤ 4 * Δ S * S.C.k := Nat.mul_le_mul_left _ hk
  have hs1 : 4 * Δ S * 1 ≤ 4 * Δ S * s_w := Nat.mul_le_mul_left _ hs_w
  rw [anchorCW_eq, U.slotStart_eq, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_one]
  rcases dutyWindowStart_cases L SF U S s_w with h | ⟨h0, h⟩ <;> omega

/-- **The slot `τ / 4Δ` holds the time `τ`.** Its start is at most `τ`, and the next slot's start
is greater than `τ`.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `τ`: the time.

Read aloud: slot `τ / (4 * Δ S)` starts at or before `τ` and the next slot starts after `τ`. -/
theorem slotStart_div_le (U : UniformSchedule L) (S : Setup V) (τ : ℕ) :
    L.slotStart S.C (τ / (4 * Δ S)) ≤ τ ∧ τ < L.slotStart S.C (τ / (4 * Δ S) + 1) := by
  have hΔ := one_le_Δ S
  have h1 := Nat.div_add_mod τ (4 * Δ S)
  have h2 := Nat.mod_lt τ (show 0 < 4 * Δ S by omega)
  rw [U.slotStart_eq, U.slotStart_eq, Nat.mul_add, Nat.mul_one]
  generalize τ / (4 * Δ S) = q at h1 ⊢
  generalize τ % (4 * Δ S) = b at h1 h2
  generalize 4 * Δ S * q = a at h1 ⊢
  omega

/-- **The next slot's support cutoff is one slot later.**

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `n`: the slot.

Read aloud: slot `n + 1`'s support cutoff is `4 * Δ S` after slot `n`'s. -/
theorem supportCutoff_succ_eq (U : UniformSchedule L) (S : Setup V) (n : ℕ) :
    L.supportCutoff S.C (n + 1) = L.supportCutoff S.C n + 4 * Δ S := by
  rw [U.supportCutoff_eq S (n + 1), U.supportCutoff_eq S n, U.slotStart_eq S (n + 1),
    U.slotStart_eq S n, Nat.mul_add, Nat.mul_one]
  omega

/-- The times of a slot, from its start.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is.

Read aloud: slot `s`'s vote time, support cutoff and view freeze are `Δ S`, `2 * Δ S` and `3 * Δ S` after its start, the next slot starts `4 * Δ S` after it, and `Δ S` is at least `1`. -/
theorem times_eq (U : UniformSchedule L) (S : Setup V) (s : ℕ) :
    L.voteTime S.C s = L.slotStart S.C s + Δ S ∧ L.supportCutoff S.C s = L.slotStart S.C s + 2 * Δ S ∧
      L.viewFreeze S.C s = L.slotStart S.C s + 3 * Δ S ∧ L.slotStart S.C (s + 1) = L.slotStart S.C s + 4 * Δ S ∧
      1 ≤ Δ S := by
  refine ⟨U.voteTime_eq S s, U.supportCutoff_eq S s, U.viewFreeze_eq S s, ?_, one_le_Δ S⟩
  rw [U.slotStart_eq S (s + 1), U.slotStart_eq S s, Nat.mul_add, Nat.mul_one]

/-- The support cutoff grows strictly with the slot.

The variables:
- `L`: the slot layout; `SF`: its facts.

Read aloud: a later slot's support cutoff is strictly later. -/
theorem supportCutoff_lt (S : Setup V) {a b : ℕ} (h : a < b) :
    L.supportCutoff S.C a < L.supportCutoff S.C b := by
  exact supportCutoff_lt_of_lt L SF S h

/-- A slot at most `k + 1` slots before the first slot after the anchor starts at or after
`tGAT`.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is.

Read aloud: when slot `s₀ + 1` starts at or after `anchorCW S tGAT`, every slot `s` with `s₀ + 1 ≤ s + S.C.k + 2` starts at or after `tGAT`. -/
theorem tGAT_le_slotStart (U : UniformSchedule L) (S : Setup V) {tGAT s₀ s : ℕ}
    (hA : anchorCW S tGAT ≤ L.slotStart S.C (s₀ + 1)) (hs : s₀ + 1 ≤ s + S.C.k + 2) :
    tGAT ≤ L.slotStart S.C s := by
  rw [anchorCW_eq] at hA
  rw [U.slotStart_eq] at hA ⊢
  have h := Nat.mul_le_mul_left (4 * Δ S) hs
  have e1 : 4 * Δ S * (s + S.C.k + 2) = 4 * Δ S * s + 4 * Δ S * S.C.k + 4 * Δ S * 2 := by
    rw [Nat.mul_add, Nat.mul_add]
  have e2 : 4 * Δ S * (S.C.k + 2) = 4 * Δ S * S.C.k + 4 * Δ S * 2 := Nat.mul_add _ _ _
  omega

/-- The support cutoff grows with the slot.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `a ≤ b`: the two slots.

Read aloud: a later slot's support cutoff is no earlier. -/
theorem supportCutoff_mono (S : Setup V) {a b : ℕ} (h : a ≤ b) :
    L.supportCutoff S.C a ≤ L.supportCutoff S.C b := by
  exact (times_mono L SF S h).2.2.1

/-- A round's first slot `s`: a round's first slot whose action time is before the support cutoff
of slot `s + 1` is at most `s − R`, so at least two slots before `s`.

The variables:
- `L`: the slot layout; `SF`: its facts.

Read aloud: when `s` is a round's first slot and the action time of round `r'` is before slot `s + 1`'s support cutoff, round `r'`'s first slot is at least two slots before `s`. -/
theorem round_slot_le_of_lt (S : Setup V) {s r' : ℕ} (hsR : S.C.R ∣ s)
    (h : L.supportCutoff S.C (r' * S.C.R + 1) < L.supportCutoff S.C (s + 1)) :
    r' * S.C.R + 2 ≤ s := by
  have hR := S.C.R_ge_two
  have hlt : r' * S.C.R < s := by
    by_contra hn
    have := supportCutoff_mono L SF S (show s + 1 ≤ r' * S.C.R + 1 by omega)
    omega
  obtain ⟨r₀, rfl⟩ := hsR
  rw [Nat.mul_comm S.C.R r₀] at hlt ⊢
  have h1 : r' < r₀ := Nat.lt_of_mul_lt_mul_right hlt
  have h2 := Nat.mul_le_mul_right S.C.R (show r' + 1 ≤ r₀ by omega)
  rw [Nat.succ_mul] at h2
  omega

/-- The vote time grows with the slot.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `a ≤ b`: the two slots.

Read aloud: a later slot's vote time is no earlier. -/
theorem voteTime_mono (S : Setup V) {a b : ℕ} (h : a ≤ b) :
    L.voteTime S.C a ≤ L.voteTime S.C b := by
  exact (times_mono L SF S h).2.1

/-- The duty window of a slot starts no later than its vote time.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`: the slot.

Read aloud: slot `s`'s duty window starts no later than its vote time. -/
theorem dutyWindowStart_le_voteTime (S : Setup V) (s : ℕ) :
    L.dutyWindowStart S.C s ≤ L.voteTime S.C s := by
  have h1 := SF.dutyWindowStart_mono S s (s + 1) (Nat.le_add_right s 1)
  have h2 := SF.dutyWindowStart_succ_le_slotStart S s
  have h3 := SF.slotStart_add_Δ_le_voteTime S s
  omega

/-- The support cutoff of the slot of a time `t` that is the support cutoff of its slot is `t`.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `t`: the time.

Read aloud: when `t` is the support cutoff of its slot in the spec's integer times, the support cutoff of `t`'s slot is `t`. -/
theorem supportCutoff_slot_eq (U : UniformSchedule L) (S : Setup V) {t : ℕ}
    -- `t` is the support cutoff of its slot
    (ht : (t : Int) = S.C.t_ (L.slot S.C t) + 2 * S.C.Δ) :
    L.supportCutoff S.C (L.slot S.C t) = t := by
  have h := supportCutoff_cast L SF U S (L.slot S.C t)
  rw [← ht] at h
  exact_mod_cast h

/-- A slot starting after the support cutoff of slot `s₀ + 1` is at least `s₀ + 2`, starts after
the vote time of slot `s₀`, and starts at a time at least `1`.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s₀`, `s`: the two slots.

Read aloud: a slot that starts after slot `s₀ + 1`'s support cutoff is at least `s₀ + 2`, starts after slot `s₀`'s vote time, and starts at a time at least `1`. -/
theorem slot_after_healed_round (S : Setup V) (s₀ s : ℕ)
    (h : L.supportCutoff S.C (s₀ + 1) < L.slotStart S.C s) :
    s₀ + 2 ≤ s ∧ L.voteTime S.C s₀ < L.slotStart S.C s ∧ 1 ≤ L.slotStart S.C s := by
  have hs : s₀ + 2 ≤ s := by
    by_contra hc
    have := times_mono L SF S (show s ≤ s₀ + 1 by omega)
    have := times_le L SF S (s₀ + 1)
    omega
  have := times_mono L SF S (show s₀ ≤ s₀ + 1 by omega)
  have := times_le L SF S s₀
  have := times_le L SF S (s₀ + 1)
  exact ⟨hs, by omega, by omega⟩

/-- A slot is less than the support cutoff of the next slot.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `n`: the slot.

Read aloud: the slot number `n` is less than slot `n + 1`'s support cutoff. -/
theorem lt_supportCutoff_succ (S : Setup V) (n : ℕ) :
    n < L.supportCutoff S.C (n + 1) := by
  have := le_slotStart L SF S n
  have := times_le L SF S n
  have := times_le L SF S (n + 1)
  omega

/-- A support cutoff at most the support cutoff of slot `n` is the support cutoff of a slot less
than `n`.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`: the slot; `n`: the bound.

Read aloud: when slot `s + 1`'s support cutoff is at most slot `n`'s, `s` is less than `n`. -/
theorem slot_lt_of_supportCutoff_le (S : Setup V) {s n : ℕ}
    (h : L.supportCutoff S.C (s + 1) ≤ L.supportCutoff S.C n) :
    s < n := by
  by_contra hc
  have := supportCutoff_lt_of_lt L SF S (show n < s + 1 by omega)
  omega

/-- A time whose slot is at least `s` is at least the start of slot `s`.

The variables:
- `L`: the slot layout; `SF`: its facts.

Read aloud: a time whose slot is at least `s` is at or after the start of slot `s`. -/
theorem slotStart_le_of_le_slot (S : Setup V) {s t : ℕ} (h : s ≤ L.slot S.C t) :
    L.slotStart S.C s ≤ t := by
  exact (SF.slotStart_le_iff S s t).2 h

/-- The vote time of a later slot is later.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `a`, `b`: the two slots.

Read aloud: a later slot's vote time is no earlier. -/
theorem voteTime_mono' (S : Setup V) {a b : ℕ} (h : a ≤ b) :
    L.voteTime S.C a ≤ L.voteTime S.C b := by
  exact voteTime_mono L SF S h

/-- The vote time of the next slot is four delays later.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `a`: the slot.

Read aloud: the vote time of slot `a + 1` is `4 * Δ S` after slot `a`'s. -/
theorem voteTime_succ' (U : UniformSchedule L) (S : Setup V) (a : ℕ) :
    L.voteTime S.C (a + 1) = L.voteTime S.C a + 4 * Δ S := by
  exact voteTime_succ L SF U S a

/-- An update at a time at or after the lock's deadline `voteTime S (s + k + 1)` is the update of a
slot `s' ≥ s + k`. Copied from `scratch/goldilocks_async/probe_ar4_replan.lean:156`.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`: the hand-over slot; `s'`: the slot of the update.

Read aloud: a support cutoff of slot `s' + 1` at or after the vote time of slot `s + S.C.k + 1` has `s + S.C.k ≤ s'`. -/
theorem slot_of_update_after_deadline (S : Setup V) (s s' : ℕ)
    (h : L.voteTime S.C (s + S.C.k + 1) ≤ L.supportCutoff S.C (s' + 1)) :
    s + S.C.k ≤ s' := by
  by_contra hlt
  have := viewFreeze_add_Δ_le_slotStart_of_lt L SF S (show s' + 1 < s + S.C.k + 1 by omega)
  have := times_le L SF S (s' + 1)
  have := times_le L SF S (s + S.C.k + 1)
  omega

/-- At a slot `s' ≥ s + k`, the period has ended by the vote time. Copied from
`scratch/goldilocks_async/probe_ar4_replan.lean:171`.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`: the hand-over slot; `s'`: the slot; `b₁`: the end of the period.

Read aloud: when `b₁ + Δ S` is at most slot `s + S.C.k`'s vote time, `b₁` is at most the vote time of every slot `s' ≥ s + S.C.k`. -/
theorem votes_due_of_after_period (S : Setup V) (s s' b₁ : ℕ)
    (hb₁ : b₁ + Δ S ≤ L.voteTime S.C (s + S.C.k)) (hs' : s + S.C.k ≤ s') :
    b₁ ≤ L.voteTime S.C s' := by
  have := (times_mono L SF S hs').2.1
  omega

/-- **Kit fact, the proposal window covers the delivery of attestations.** When
`Δ_F + Δ ≤ 4Δ(k + 1)` and `s ≥ R`, the start of the proposal window of slot `s`, plus `Δ_F`, is at
most the start of slot `s`.

Why: the window starts at `t_s + Δ − 4Δ(k + 1)` when that is nonnegative, and the condition is
the inequality; otherwise at `0`, and `Δ_F < 4ΔR ≤ t_s` (`R_covers`).

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `s`: the slot.

Read aloud: when `Δ_F S + Δ S ≤ 4 * Δ S * (S.C.k + 1)` and `s ≥ S.C.R`, slot `s`'s proposal window starts at least `Δ_F S` before slot `s` starts. -/
theorem proposalWindowStart_add_Δ_F_le (U : UniformSchedule L) (S : Setup V) {s : ℕ} (hs : S.C.R ≤ s)
    (hParam : Δ_F S + Δ S ≤ 4 * Δ S * (S.C.k + 1)) :
    L.proposalWindowStart S.C s + Δ_F S ≤ L.slotStart S.C s := by
  have hR := six_Δ_add_Δ_F_le_round S
  have hsR := Nat.mul_le_mul_left (4 * Δ S) hs
  rw [U.proposalWindowStart_eq, U.slotStart_eq]
  omega

/-- **Kit fact, the round covers the delivery of attestations.** The support cutoff of slot
`s + 1`, plus `Δ_F`, is no later than the start of slot `s + R`: the support cutoff of slot `s + 1`
is `4Δs + 6Δ`, the start of slot `s + R` is `4Δs + 4ΔR`, and `6Δ + Δ_F ≤ 4ΔR`.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`: the slot.

Read aloud: an attestation sent at the action time of the round starting at `s` arrives by the
start of the next round. -/
theorem supportCutoff_succ_add_Δ_F_le_slotStart (S : Setup V) (s : ℕ) :
    L.supportCutoff S.C (s + 1) + Δ_F S ≤ L.slotStart S.C (s + S.C.R) := by
  exact SF.supportCutoff_succ_add_Δ_F_le_slotStart S s

/-- The support cutoff of slot `s + 1` is no later than the start of slot `s''` when `s + R ≤ s''`.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`, `s''`: the slots.

Read aloud: slot `s + 1`'s support cutoff is no later than the start of every slot `s''` with `s + S.C.R ≤ s''`. -/
theorem supportCutoff_succ_le_of_round (S : Setup V) {s s'' : ℕ} (hs'' : s + S.C.R ≤ s'') :
    L.supportCutoff S.C (s + 1) ≤ L.slotStart S.C s'' := by
  exact le_trans (Nat.le_add_right _ _) (le_trans (SF.supportCutoff_succ_add_Δ_F_le_slotStart S s)
    (slotStart_le_of_le L SF S hs''))

/-- **Kit fact, the delivery before a slot places it two slots later.** When the support cutoff of
slot `s + 1`, plus `Δ_F`, is at most the start of slot `s''`, then `s + 2 ≤ s''`: the support
cutoff of slot `s + 1` is `4Δ(s + 1) + 2Δ`, so the start of slot `s + 1` is before the start of
slot `s''`.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`, `s''`: the slots.

Read aloud: if an attestation sent at the action time of slot `s` arrives before slot `s''`
starts, then `s''` is at least two slots after `s`. -/
theorem slot_add_two_le_of_delivery (S : Setup V) {s s'' : ℕ}
    (h : L.supportCutoff S.C (s + 1) + Δ_F S ≤ L.slotStart S.C s'') :
    s + 2 ≤ s'' := by
  by_contra hc
  have := times_mono L SF S (show s'' ≤ s + 1 by omega)
  have := times_le L SF S (s + 1)
  omega

/-- **Kit fact, a later round's slot is after the delivery.** When `s + R ≤ s''`, the support cutoff
of slot `s + 1`, plus `Δ_F`, is at most the start of slot `s''`
(`supportCutoff_succ_add_Δ_F_le_slotStart`).

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`, `s''`: the slots.

Read aloud: an attestation sent at the action time of the round starting at `s` arrives before
any slot of a later round starts. -/
theorem delivery_of_round (S : Setup V) {s s'' : ℕ} (hs'' : s + S.C.R ≤ s'') :
    L.supportCutoff S.C (s + 1) + Δ_F S ≤ L.slotStart S.C s'' := by
  exact le_trans (SF.supportCutoff_succ_add_Δ_F_le_slotStart S s) (slotStart_le_of_le L SF S hs'')

/-- `proposalWindowStart_eq` of `Lemma90Inclusion.lean`, copied, on the natural-number times.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `q`: the slot.

Read aloud: slot `q + 2`'s proposal window starts where slot `q + 1`'s duty window starts. -/
theorem proposalWindowStart_eqJ (U : UniformSchedule L) (S : Setup V) (q : ℕ) :
    L.proposalWindowStart S.C (q + 2) = L.dutyWindowStart S.C (q + 1) := by
  rw [U.proposalWindowStart_eq, U.dutyWindowStart_eq, U.slotStart_eq S (q + 2),
    U.slotStart_eq S (q + 1), show q + 2 = (q + 1) + 1 from rfl, Nat.mul_add (4 * Δ S) (q + 1) 1,
    Nat.mul_add (4 * Δ S) S.C.k 1, Nat.mul_one]
  omega

/-- `proposal_window_start_eq` on the natural-number times.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `q`: the slot.

Read aloud: slot `q + 2`'s proposal window starts where slot `q + 1`'s duty window starts. -/
theorem proposalWindowStart_eq (U : UniformSchedule L) (S : Setup V) (q : ℕ) :
    L.proposalWindowStart S.C (q + 2) = L.dutyWindowStart S.C (q + 1) := by
  exact proposalWindowStart_eqJ L SF U S q

/-- The support cutoff of slot `s + 1` is in slot `s + 1`, and is at least `1`.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`: the slot before the cutoff's slot.

Read aloud: slot `s + 1`'s support cutoff is in slot `s + 1` and is at least `1`. -/
theorem supportCutoff_slot (S : Setup V) (s : ℕ) :
    L.slot S.C (L.supportCutoff S.C (s + 1)) = s + 1 ∧ 1 ≤ L.supportCutoff S.C (s + 1) := by
  obtain ⟨a1, a2, a3, a4, hΔ⟩ := times_le L SF S (s + 1)
  exact ⟨slot_eq_of_mem L SF S (by omega) (by omega), by omega⟩

/-- The duty window of slot `s + 1` starts strictly before the support cutoff of slot `s + 1`.

The variables:
- `L`: the slot layout; `SF`: its facts;
- `S`: the setup; `s`: the slot.

Read aloud: slot `s + 1`'s duty window starts strictly before its support cutoff. -/
theorem dutyWindowStart_succ_lt_supportCutoff (S : Setup V) (s : ℕ) :
    L.dutyWindowStart S.C (s + 1) < L.supportCutoff S.C (s + 1) := by
  have := SF.dutyWindowStart_succ_le_slotStart S s
  have := times_mono L SF S (Nat.le_add_right s 1)
  have := times_le L SF S (s + 1)
  omega

/-- **The spec's duty window start is at most the library's.** `dutyWindowStart S s` is
`duty_window_start S.C s` made a natural number by `Int.toNat`, which raises a negative value to
`0` and keeps the others.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `s`: the slot.

Read aloud: the spec's start of slot `s`'s duty window, an integer, is at most
`dutyWindowStart S s` read as an integer. -/
theorem duty_window_start_le_dutyWindowStart (U : UniformSchedule L) (S : Setup V) (s : ℕ) :
    duty_window_start S.C s ≤ ((L.dutyWindowStart S.C s : ℕ) : Int) := by
  have h1 := slotStart_cast L SF U S s
  have h2 := Δ_cast S
  have hk : ((4 * Δ S * S.C.k : ℕ) : Int) = 4 * S.C.Δ * (S.C.k : Int) := by
    push_cast
    rw [h2]
  have e : L.dutyWindowStart S.C s = (duty_window_start S.C s).toNat := by
    rw [duty_window_start_eq, ← h1, ← hk, ← h2, ← Nat.cast_add, Int.toNat_sub, U.dutyWindowStart_eq]
  rw [e]
  exact Int.self_le_toNat _

/-- **The duty window of a slot starts before the slot's support cutoff.** The spec's
`duty_window_start S.C s` is `S.C.t_ s + S.C.Δ − 4 * S.C.Δ * S.C.k`, and the support cutoff
`supportCutoff S s` is `S.C.t_ s + 2 * S.C.Δ`, with `S.C.Δ` positive.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `s`: the slot.

Read aloud: the duty window of slot `s` starts strictly before slot `s`'s support cutoff. -/
theorem duty_window_start_lt_supportCutoff (U : UniformSchedule L) (S : Setup V) (s : ℕ) :
    duty_window_start S.C s < ((L.supportCutoff S.C s : ℕ) : Int) := by
  rw [supportCutoff_cast L SF U S s, duty_window_start_eq]
  have hk : (0 : Int) ≤ 4 * S.C.Δ * (S.C.k : Int) := by
    have := S.C.Δ_pos
    positivity
  have key : ∀ a d m : Int, 0 < d → 0 ≤ m → a + d - m < a + 2 * d := by
    intro a d m h1 h2; omega
  exact key _ _ _ S.C.Δ_pos hk

/-- **The duty window's start as a natural number, written out.** `dutyWindowStart S s` is the
spec's `duty_window_start S.C s` made a natural number by `Int.toNat`.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `s`: the slot.

Read aloud: `dutyWindowStart S s` is `duty_window_start S.C s`, or `0` when that is negative. -/
theorem dutyWindowStart_eq_toNat (U : UniformSchedule L) (S : Setup V) (s : ℕ) :
    L.dutyWindowStart S.C s = (duty_window_start S.C s).toNat := by
  have h1 := slotStart_cast L SF U S s
  have h2 := Δ_cast S
  have hk : ((4 * Δ S * S.C.k : ℕ) : Int) = 4 * S.C.Δ * (S.C.k : Int) := by
    push_cast
    rw [h2]
  rw [duty_window_start_eq, ← h1, ← hk, ← h2, ← Nat.cast_add, Int.toNat_sub, U.dutyWindowStart_eq]

/-- **A time at most the spec's duty window start is negative, or the start is at least `1`.** The
spec's `duty_window_start S.C s` is `S.C.Δ * (4 * s + 1 − 4 * S.C.k)`, never `0` (an odd multiple
of the positive `S.C.Δ`); so when `dutyWindowStart S s`, its value made a natural number, is `0`,
the spec's start is negative, and so is every time at most it.

The variables:
- `L`: the slot layout; `SF`: its facts; `U`: it is spaced as Goldilocks is;
- `S`: the setup; `s`: the slot; `τ`: the time.

Read aloud: a time at most the spec's start of slot `s`'s duty window is negative, or that start,
as a natural number, is at least `1`. -/
theorem lt_zero_or_one_le_dutyWindowStart_of_le (U : UniformSchedule L) (S : Setup V) (s : ℕ)
    {τ : Int} (h : τ ≤ duty_window_start S.C s) : τ < 0 ∨ 1 ≤ L.dutyWindowStart S.C s := by
  rw [dutyWindowStart_eq_toNat L SF U S s]
  have hne : duty_window_start S.C s ≠ 0 := by
    rw [duty_window_start_eq, t_eq_mul]
    intro h0
    have hΔ := S.C.Δ_pos
    have e1 : S.C.Δ * (4 * (s : Int)) = 4 * S.C.Δ * (s : Int) := by
      rw [← Int.mul_assoc, Int.mul_comm S.C.Δ 4]
    have e2 : S.C.Δ * (4 * (S.C.k : Int)) = 4 * S.C.Δ * (S.C.k : Int) := by
      rw [← Int.mul_assoc, Int.mul_comm S.C.Δ 4]
    have h1 : S.C.Δ * (4 * (s : Int) + 1 - 4 * (S.C.k : Int)) = 0 := by
      rw [Int.mul_sub, Int.mul_add, Int.mul_one, e1, e2]; exact h0
    rcases Int.mul_eq_zero.1 h1 with h2 | h2
    · exact (Int.ne_of_gt hΔ) h2
    · have h3 : (4 * (s : Int) + 1 - 4 * (S.C.k : Int)) = 0 := h2
      omega
  rcases Int.lt_or_le τ 0 with h3 | h3
  · exact Or.inl h3
  · right
    have h4 : (0 : Int) < duty_window_start S.C s :=
      lt_of_le_of_ne (le_trans h3 h) (Ne.symm hne)
    have h5 : (((duty_window_start S.C s).toNat : ℕ) : Int) = duty_window_start S.C s :=
      Int.toNat_of_nonneg h4.le
    omega

end

/-! ## At the spec's slot layout -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.slotStart_cast`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `slotStart_cast` holds, as the record's theorem at the spec's slot
layout. -/
theorem slotStart_cast_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.slotStart_cast V _ _) := by
  exact slotStart_cast SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.voteTime_cast`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `voteTime_cast` holds, as the record's theorem at the spec's slot
layout. -/
theorem voteTime_cast_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.voteTime_cast V _ _) := by
  exact voteTime_cast SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.supportCutoff_cast`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `supportCutoff_cast` holds, as the record's theorem at the spec's slot
layout. -/
theorem supportCutoff_cast_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.supportCutoff_cast V _ _) := by
  exact supportCutoff_cast SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.slotStart_eq`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `slotStart_eq` holds, as the record's theorem at the spec's slot
layout. -/
theorem slotStart_eq_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.slotStart_eq V _ _) := by
  exact slotStart_eq SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.voteTime_eq`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `voteTime_eq` holds, as the record's theorem at the spec's slot
layout. -/
theorem voteTime_eq_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.voteTime_eq V _ _) := by
  exact voteTime_eq SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.supportCutoff_eq`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `supportCutoff_eq` holds, as the record's theorem at the spec's slot
layout. -/
theorem supportCutoff_eq_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.supportCutoff_eq V _ _) := by
  exact supportCutoff_eq SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.voteTime_succ`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `voteTime_succ` holds, as the record's theorem at the spec's slot
layout. -/
theorem voteTime_succ_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.voteTime_succ V _ _) := by
  exact voteTime_succ SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.slot_natCast`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `slot_natCast` holds, as the record's theorem at the spec's slot
layout. -/
theorem slot_natCast_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.slot_natCast V _ _) := by
  exact slot_natCast SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.slot_mono`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `slot_mono` holds, as the record's theorem at the spec's slot
layout. -/
theorem slot_mono_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.slot_mono V _ _) := by
  exact slot_mono SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.slot_eq_of_mem`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `slot_eq_of_mem` holds, as the record's theorem at the spec's slot
layout. -/
theorem slot_eq_of_mem_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.slot_eq_of_mem V _ _) := by
  exact slot_eq_of_mem SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.viewFreeze_cast`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `viewFreeze_cast` holds, as the record's theorem at the spec's slot
layout. -/
theorem viewFreeze_cast_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.viewFreeze_cast V _ _) := by
  exact viewFreeze_cast SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.viewFreeze_eq`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `viewFreeze_eq` holds, as the record's theorem at the spec's slot
layout. -/
theorem viewFreeze_eq_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.viewFreeze_eq V _ _) := by
  exact viewFreeze_eq SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.slotStart_le_iff`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `slotStart_le_iff` holds, as the record's theorem at the spec's slot
layout. -/
theorem slotStart_le_iff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.slotStart_le_iff V _ _) := by
  exact slotStart_le_iff SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.dutyWindowStart_succ_le_slotStart`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `dutyWindowStart_succ_le_slotStart` holds, as the record's theorem at the spec's slot
layout. -/
theorem dutyWindowStart_succ_le_slotStart_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.dutyWindowStart_succ_le_slotStart V _ _) := by
  exact dutyWindowStart_succ_le_slotStart SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.slot_lt_of_lt_slotStart`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `slot_lt_of_lt_slotStart` holds, as the record's theorem at the spec's slot
layout. -/
theorem slot_lt_of_lt_slotStart_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.slot_lt_of_lt_slotStart V _ _) := by
  exact slot_lt_of_lt_slotStart SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.slot_le_of_supportCutoff_lt`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `slot_le_of_supportCutoff_lt` holds, as the record's theorem at the spec's slot
layout. -/
theorem slot_le_of_supportCutoff_lt_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.slot_le_of_supportCutoff_lt V _ _) := by
  exact slot_le_of_supportCutoff_lt SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.supportCutoff_lt_of_lt`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `supportCutoff_lt_of_lt` holds, as the record's theorem at the spec's slot
layout. -/
theorem supportCutoff_lt_of_lt_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.supportCutoff_lt_of_lt V _ _) := by
  exact supportCutoff_lt_of_lt SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.dutyWindowStart_le_supportCutoff`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `dutyWindowStart_le_supportCutoff` holds, as the record's theorem at the spec's slot
layout. -/
theorem dutyWindowStart_le_supportCutoff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.dutyWindowStart_le_supportCutoff V _ _) := by
  exact dutyWindowStart_le_supportCutoff SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.slotStart_mono`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `slotStart_mono` holds, as the record's theorem at the spec's slot
layout. -/
theorem slotStart_mono_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.slotStart_mono V _ _) := by
  exact slotStart_mono SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.dutyWindowStart_succ_le_supportCutoff`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `dutyWindowStart_succ_le_supportCutoff` holds, as the record's theorem at the spec's slot
layout. -/
theorem dutyWindowStart_succ_le_supportCutoff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.dutyWindowStart_succ_le_supportCutoff V _ _) := by
  exact dutyWindowStart_succ_le_supportCutoff SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.supportCutoff_succ_times`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `supportCutoff_succ_times` holds, as the record's theorem at the spec's slot
layout. -/
theorem supportCutoff_succ_times_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.supportCutoff_succ_times V _ _) := by
  exact supportCutoff_succ_times SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.dutyWindowStart_mono`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `dutyWindowStart_mono` holds, as the record's theorem at the spec's slot
layout. -/
theorem dutyWindowStart_mono_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.dutyWindowStart_mono V _ _) := by
  exact dutyWindowStart_mono SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.slotStart_le_of_le`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `slotStart_le_of_le` holds, as the record's theorem at the spec's slot
layout. -/
theorem slotStart_le_of_le_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.slotStart_le_of_le V _ _) := by
  exact slotStart_le_of_le SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.supportCutoff_le_slotStart_succ`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `supportCutoff_le_slotStart_succ` holds, as the record's theorem at the spec's slot
layout. -/
theorem supportCutoff_le_slotStart_succ_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.supportCutoff_le_slotStart_succ V _ _) := by
  exact supportCutoff_le_slotStart_succ SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.supportCutoff_succ_le`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `supportCutoff_succ_le` holds, as the record's theorem at the spec's slot
layout. -/
theorem supportCutoff_succ_le_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.supportCutoff_succ_le V _ _) := by
  exact supportCutoff_succ_le SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.dutyWindowStart_cases`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `dutyWindowStart_cases` holds, as the record's theorem at the spec's slot
layout. -/
theorem dutyWindowStart_cases_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.dutyWindowStart_cases V _ _) := by
  exact dutyWindowStart_cases SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.dutyWindowStart_of_anchor`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `dutyWindowStart_of_anchor` holds, as the record's theorem at the spec's slot
layout. -/
theorem dutyWindowStart_of_anchor_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.dutyWindowStart_of_anchor V _ _) := by
  exact dutyWindowStart_of_anchor SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.anchor_le_front`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `anchor_le_front` holds, as the record's theorem at the spec's slot
layout. -/
theorem anchor_le_front_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.anchor_le_front V _ _) := by
  exact anchor_le_front SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.slotStart_div_le`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `slotStart_div_le` holds, as the record's theorem at the spec's slot
layout. -/
theorem slotStart_div_le_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.slotStart_div_le V _ _) := by
  exact slotStart_div_le SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.supportCutoff_succ_eq`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `supportCutoff_succ_eq` holds, as the record's theorem at the spec's slot
layout. -/
theorem supportCutoff_succ_eq_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.supportCutoff_succ_eq V _ _) := by
  exact supportCutoff_succ_eq SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.times_eq`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `times_eq` holds, as the record's theorem at the spec's slot
layout. -/
theorem times_eq_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.times_eq V _ _) := by
  exact times_eq SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.supportCutoff_lt`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `supportCutoff_lt` holds, as the record's theorem at the spec's slot
layout. -/
theorem supportCutoff_lt_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.supportCutoff_lt V _ _) := by
  exact supportCutoff_lt SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.tGAT_le_slotStart`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `tGAT_le_slotStart` holds, as the record's theorem at the spec's slot
layout. -/
theorem tGAT_le_slotStart_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.tGAT_le_slotStart V _ _) := by
  exact tGAT_le_slotStart SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.supportCutoff_mono`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `supportCutoff_mono` holds, as the record's theorem at the spec's slot
layout. -/
theorem supportCutoff_mono_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.supportCutoff_mono V _ _) := by
  exact supportCutoff_mono SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.round_slot_le_of_lt`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `round_slot_le_of_lt` holds, as the record's theorem at the spec's slot
layout. -/
theorem round_slot_le_of_lt_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.round_slot_le_of_lt V _ _) := by
  exact round_slot_le_of_lt SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.voteTime_mono`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `voteTime_mono` holds, as the record's theorem at the spec's slot
layout. -/
theorem voteTime_mono_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.voteTime_mono V _ _) := by
  exact voteTime_mono SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.dutyWindowStart_le_voteTime`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `dutyWindowStart_le_voteTime` holds, as the record's theorem at the spec's slot
layout. -/
theorem dutyWindowStart_le_voteTime_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.dutyWindowStart_le_voteTime V _ _) := by
  exact dutyWindowStart_le_voteTime SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.supportCutoff_slot_eq`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `supportCutoff_slot_eq` holds, as the record's theorem at the spec's slot
layout. -/
theorem supportCutoff_slot_eq_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.supportCutoff_slot_eq V _ _) := by
  exact supportCutoff_slot_eq SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.slot_after_healed_round`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `slot_after_healed_round` holds, as the record's theorem at the spec's slot
layout. -/
theorem slot_after_healed_round_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.slot_after_healed_round V _ _) := by
  exact slot_after_healed_round SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lt_supportCutoff_succ`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `lt_supportCutoff_succ` holds, as the record's theorem at the spec's slot
layout. -/
theorem lt_supportCutoff_succ_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.lt_supportCutoff_succ V _ _) := by
  exact lt_supportCutoff_succ SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.slot_lt_of_supportCutoff_le`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `slot_lt_of_supportCutoff_le` holds, as the record's theorem at the spec's slot
layout. -/
theorem slot_lt_of_supportCutoff_le_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.slot_lt_of_supportCutoff_le V _ _) := by
  exact slot_lt_of_supportCutoff_le SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.slotStart_le_of_le_slot`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `slotStart_le_of_le_slot` holds, as the record's theorem at the spec's slot
layout. -/
theorem slotStart_le_of_le_slot_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.slotStart_le_of_le_slot V _ _) := by
  exact slotStart_le_of_le_slot SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.voteTime_mono'`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `voteTime_mono'` holds, as the record's theorem at the spec's slot
layout. -/
theorem voteTime_mono'_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.voteTime_mono' V _ _) := by
  exact voteTime_mono' SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.voteTime_succ'`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `voteTime_succ'` holds, as the record's theorem at the spec's slot
layout. -/
theorem voteTime_succ'_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.voteTime_succ' V _ _) := by
  exact voteTime_succ' SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.slot_of_update_after_deadline`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `slot_of_update_after_deadline` holds, as the record's theorem at the spec's slot
layout. -/
theorem slot_of_update_after_deadline_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.slot_of_update_after_deadline V _ _) := by
  exact slot_of_update_after_deadline SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.votes_due_of_after_period`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `votes_due_of_after_period` holds, as the record's theorem at the spec's slot
layout. -/
theorem votes_due_of_after_period_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.votes_due_of_after_period V _ _) := by
  exact votes_due_of_after_period SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.proposalWindowStart_add_Δ_F_le`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `proposalWindowStart_add_Δ_F_le` holds, as the record's theorem at the spec's slot
layout. -/
theorem proposalWindowStart_add_Δ_F_le_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.proposalWindowStart_add_Δ_F_le V _ _) := by
  exact proposalWindowStart_add_Δ_F_le SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.supportCutoff_succ_add_Δ_F_le_slotStart`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `supportCutoff_succ_add_Δ_F_le_slotStart` holds, as the record's theorem at the spec's slot
layout. -/
theorem supportCutoff_succ_add_Δ_F_le_slotStart_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.supportCutoff_succ_add_Δ_F_le_slotStart V _ _) := by
  exact supportCutoff_succ_add_Δ_F_le_slotStart SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.supportCutoff_succ_le_of_round`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `supportCutoff_succ_le_of_round` holds, as the record's theorem at the spec's slot
layout. -/
theorem supportCutoff_succ_le_of_round_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.supportCutoff_succ_le_of_round V _ _) := by
  exact supportCutoff_succ_le_of_round SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.slot_add_two_le_of_delivery`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `slot_add_two_le_of_delivery` holds, as the record's theorem at the spec's slot
layout. -/
theorem slot_add_two_le_of_delivery_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.slot_add_two_le_of_delivery V _ _) := by
  exact slot_add_two_le_of_delivery SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.delivery_of_round`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `delivery_of_round` holds, as the record's theorem at the spec's slot
layout. -/
theorem delivery_of_round_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.delivery_of_round V _ _) := by
  exact delivery_of_round SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.proposalWindowStart_eqJ`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `proposalWindowStart_eqJ` holds, as the record's theorem at the spec's slot
layout. -/
theorem proposalWindowStart_eqJ_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.proposalWindowStart_eqJ V _ _) := by
  exact proposalWindowStart_eqJ SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.proposalWindowStart_eq`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `proposalWindowStart_eq` holds, as the record's theorem at the spec's slot
layout. -/
theorem proposalWindowStart_eq_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.proposalWindowStart_eq V _ _) := by
  exact proposalWindowStart_eq SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.supportCutoff_slot`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `supportCutoff_slot` holds, as the record's theorem at the spec's slot
layout. -/
theorem supportCutoff_slot_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.supportCutoff_slot V _ _) := by
  exact supportCutoff_slot SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.dutyWindowStart_succ_lt_supportCutoff`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `dutyWindowStart_succ_lt_supportCutoff` holds, as the record's theorem at the spec's slot
layout. -/
theorem dutyWindowStart_succ_lt_supportCutoff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.dutyWindowStart_succ_lt_supportCutoff V _ _) := by
  exact dutyWindowStart_succ_lt_supportCutoff SlotLayout.goldilocks scheduleFacts_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.duty_window_start_le_dutyWindowStart`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `duty_window_start_le_dutyWindowStart` holds, as the record's theorem at the spec's slot
layout. -/
theorem duty_window_start_le_dutyWindowStart_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.duty_window_start_le_dutyWindowStart V _ _) := by
  exact duty_window_start_le_dutyWindowStart SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.duty_window_start_lt_supportCutoff`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `duty_window_start_lt_supportCutoff` holds, as the record's theorem at the spec's slot
layout. -/
theorem duty_window_start_lt_supportCutoff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.duty_window_start_lt_supportCutoff V _ _) := by
  exact duty_window_start_lt_supportCutoff SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.dutyWindowStart_eq_toNat`,
recovered from its record form at the spec's slot layout.

Read aloud: the landed `dutyWindowStart_eq_toNat` holds, as the record's theorem at the spec's slot
layout. -/
theorem dutyWindowStart_eq_toNat_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.dutyWindowStart_eq_toNat V _ _) := by
  exact dutyWindowStart_eq_toNat SlotLayout.goldilocks scheduleFacts_goldilocks uniformSchedule_goldilocks

end GoldilocksCorrectness.Record.Proofs.Routines
