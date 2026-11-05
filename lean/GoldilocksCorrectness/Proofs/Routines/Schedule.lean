module
public import GoldilocksCorrectness.Statements.Routines.ScheduleDefs
import all Goldilocks.Config
import all Goldilocks.Node
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# The schedule: the times of a slot and the slot of a time

The theorems that read the schedule alone, no node state and no execution: the times of
`Statements/Routines/ScheduleDefs.lean` read back as integers (`Δ_cast`, `slotStart_cast`, …),
the equations between the times of a slot (`slotStart_eq`, `voteTime_eq`, `supportCutoff_eq`, …),
their growth with the slot (`slotStart_mono`, `voteTime_mono`, `supportCutoff_mono`, …), the slot
of a time (`slot_natCast`, `slot_eq_of_mem`, `slot_le_of_t_lt`, …), and the spec's
`duty_window_start` and `proposal_window_start` against them.

Moved here unchanged from the execution pages, `Proofs/Routines/TickFrame.lean` and
`Proofs/Routines/Attestation.lean`. The theorems keep the
order in which each follows the theorems its proof uses.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff viewFreeze
  lateVoteCutoff dutyWindowStart proposalWindowStart anchorCW)

section

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The delay `Δ S` read back as an integer is `S.C.Δ`.

The variables:
- `S`: the setup. -/
theorem Δ_cast (S : Setup V) : ((Δ S : ℕ) : Int) = S.C.Δ :=
  Int.toNat_of_nonneg (le_of_lt S.C.Δ_pos)

/-- The delay `Δ S` is at least `1`.

The variables:
- `S`: the setup. -/
theorem one_le_Δ (S : Setup V) : 1 ≤ Δ S := by
  have h1 : ((Δ S : ℕ) : Int) = S.C.Δ := Δ_cast S
  have h2 : (0 : Int) < S.C.Δ := S.C.Δ_pos
  omega

/-- The start of slot `s` read back as an integer is `S.C.t_ s`.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem slotStart_cast (S : Setup V) (s : ℕ) :
    ((slotStart S s : ℕ) : Int) = S.C.t_ s := by
  have h2 : (0 : Int) < S.C.Δ := S.C.Δ_pos
  have h : (0 : Int) ≤ S.C.t_ s := by
    show (0 : Int) ≤ 4 * S.C.Δ * (s : Int)
    positivity
  exact Int.toNat_of_nonneg h

/-- The vote time of slot `s` read back as an integer is `S.C.t_ s + S.C.Δ`.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem voteTime_cast (S : Setup V) (s : ℕ) :
    ((voteTime S s : ℕ) : Int) = S.C.t_ s + S.C.Δ := by
  have h2 : (0 : Int) < S.C.Δ := S.C.Δ_pos
  have h : (0 : Int) ≤ S.C.t_ s := by
    show (0 : Int) ≤ 4 * S.C.Δ * (s : Int)
    positivity
  exact Int.toNat_of_nonneg (by omega)

/-- The support cutoff of slot `s` read back as an integer is `S.C.t_ s + 2 * S.C.Δ`.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem supportCutoff_cast (S : Setup V) (s : ℕ) :
    ((supportCutoff S s : ℕ) : Int) = S.C.t_ s + 2 * S.C.Δ := by
  have h2 : (0 : Int) < S.C.Δ := S.C.Δ_pos
  have h : (0 : Int) ≤ S.C.t_ s := by
    show (0 : Int) ≤ 4 * S.C.Δ * (s : Int)
    positivity
  exact Int.toNat_of_nonneg (by omega)

/-- Slot `s` starts at `4 * Δ S * s`.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem slotStart_eq (S : Setup V) (s : ℕ) : slotStart S s = 4 * Δ S * s := by
  have h1 := slotStart_cast S s
  have h2 := Δ_cast S
  have h3 : S.C.t_ s = 4 * S.C.Δ * (s : Int) := rfl
  have : ((slotStart S s : ℕ) : Int) = ((4 * Δ S * s : ℕ) : Int) := by
    push_cast
    rw [h1, h2, h3]
  exact_mod_cast this

/-- The vote time of slot `s` is one delay after its start.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem voteTime_eq (S : Setup V) (s : ℕ) : voteTime S s = slotStart S s + Δ S := by
  have h1 : ((voteTime S s : ℕ) : Int) = S.C.t_ s + S.C.Δ := voteTime_cast S s
  have h2 : ((Δ S : ℕ) : Int) = S.C.Δ := Δ_cast S
  have h3 : ((slotStart S s : ℕ) : Int) = S.C.t_ s := slotStart_cast S s
  omega

/-- The support cutoff of slot `s` is one delay after its vote time.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem supportCutoff_eq (S : Setup V) (s : ℕ) : supportCutoff S s = voteTime S s + Δ S := by
  have h1 : ((voteTime S s : ℕ) : Int) = S.C.t_ s + S.C.Δ := voteTime_cast S s
  have h2 : ((Δ S : ℕ) : Int) = S.C.Δ := Δ_cast S
  have h3 : ((supportCutoff S s : ℕ) : Int) = S.C.t_ s + 2 * S.C.Δ := supportCutoff_cast S s
  omega

/-- The vote time of slot `s + 1` is four delays after the vote time of slot `s`.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem voteTime_succ (S : Setup V) (s : ℕ) : voteTime S (s + 1) = voteTime S s + 4 * Δ S := by
  have h1 := voteTime_eq S s
  have h2 := voteTime_eq S (s + 1)
  have h3 := slotStart_eq S s
  have h4 := slotStart_eq S (s + 1)
  rw [h2, h1, h4, h3, Nat.mul_add, Nat.mul_one]
  omega

/-- The slot of a natural-number time `t` is `t / (4 * Δ S)`.

The variables:
- `S`: the setup; `t`: the time. -/
theorem slot_natCast (S : Setup V) (t : ℕ) : S.C.slot (t : Int) = t / (4 * Δ S) := by
  have h4 : (4 * S.C.Δ : Int) = ((4 * Δ S : ℕ) : Int) := by
    push_cast
    rw [Δ_cast]
  show (Int.fdiv (t : Int) (4 * S.C.Δ)).toNat = _
  rw [h4, Int.fdiv_eq_ediv_of_nonneg (t : Int) (Int.natCast_nonneg _), ← Int.natCast_div,
    Int.toNat_natCast]

/-- The slot of a time grows with the time.

The variables:
- `S`: the setup; `t ≤ t'`: the two times. -/
theorem slot_mono_int (S : Setup V) {t t' : Int} (h : t ≤ t') : S.C.slot t ≤ S.C.slot t' := by
  have h2 : (0 : Int) < 4 * S.C.Δ := by
    have h0 : (0 : Int) < S.C.Δ := S.C.Δ_pos
    omega
  show (Int.fdiv t (4 * S.C.Δ)).toNat ≤ (Int.fdiv t' (4 * S.C.Δ)).toNat
  rw [Int.fdiv_eq_ediv_of_nonneg t (le_of_lt h2), Int.fdiv_eq_ediv_of_nonneg t' (le_of_lt h2)]
  exact Int.toNat_le_toNat (Int.ediv_le_ediv h2 h)

/-- The slot of a natural-number time grows with the time.

The variables:
- `S`: the setup; `t ≤ t'`: the two times. -/
theorem slot_mono (S : Setup V) {t t' : ℕ} (h : t ≤ t') :
    S.C.slot (t : Int) ≤ S.C.slot (t' : Int) :=
  slot_mono_int S (by exact_mod_cast h)

/-- A time from the start of slot `s` and strictly before the start of slot `s + 1` is in slot
`s`.

The variables:
- `S`: the setup; `s`: the slot; `t`: the time. -/
theorem slot_eq_of_mem (S : Setup V) {s t : ℕ} (h1 : slotStart S s ≤ t)
    (h2 : t < slotStart S (s + 1)) : S.C.slot (t : Int) = s := by
  rw [slot_natCast]
  rw [slotStart_eq] at h1 h2
  apply Nat.div_eq_of_lt_le
  · rw [Nat.mul_comm]; exact h1
  · rw [Nat.mul_comm]; exact h2

/-- The view freeze of slot `s` read back as an integer is `S.C.t_ s + 3 * S.C.Δ`.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem viewFreeze_cast (S : Setup V) (s : ℕ) :
    ((viewFreeze S s : ℕ) : Int) = S.C.t_ s + 3 * S.C.Δ := by
  have h2 : (0 : Int) < S.C.Δ := S.C.Δ_pos
  have h : (0 : Int) ≤ S.C.t_ s := by
    show (0 : Int) ≤ 4 * S.C.Δ * (s : Int)
    positivity
  exact Int.toNat_of_nonneg (by omega)

/-- The view freeze of slot `s` is three delays after its start.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem viewFreeze_eq (S : Setup V) (s : ℕ) : viewFreeze S s = slotStart S s + 3 * Δ S := by
  have h1 : ((viewFreeze S s : ℕ) : Int) = S.C.t_ s + 3 * S.C.Δ := viewFreeze_cast S s
  have h2 : ((Δ S : ℕ) : Int) = S.C.Δ := Δ_cast S
  have h3 : ((slotStart S s : ℕ) : Int) = S.C.t_ s := slotStart_cast S s
  omega

/-- A time is at least the start of slot `s` exactly when its slot is at least `s`.

The variables:
- `S`: the setup; `s`: the slot; `t`: the time.

Read aloud: slot `s` has started at `t` exactly when the slot of `t` is `s` or later. -/
theorem slotStart_le_iff (S : Setup V) (s t : ℕ) :
    slotStart S s ≤ t ↔ s ≤ S.C.slot (t : Int) := by
  have hq : 0 < 4 * Δ S := by have := one_le_Δ S; omega
  rw [slot_natCast, slotStart_eq, Nat.le_div_iff_mul_le hq, Nat.mul_comm s]

omit [DecidableEq V] [Fintype V] in
/-- The vote time `C.t_ (C.slot t) + C.Δ` is not the support cutoff `C.t_ (C.slot t) + 2 * C.Δ`,
since `C.Δ` is positive.

The variables:
- `C`: the configuration; `t`: the time. -/
theorem voteTime_ne_cutoff {C : Config} {t : Time} (h : t = C.t_ (C.slot t) + C.Δ) :
    t ≠ C.t_ (C.slot t) + 2 * C.Δ := by
  intro h2
  have h3 : C.Δ = 2 * C.Δ := Int.add_left_cancel (h.symm.trans h2)
  rw [Int.two_mul] at h3
  have h4 : 0 = C.Δ := Int.add_left_cancel ((Int.add_zero C.Δ).trans h3)
  have hΔ := C.Δ_pos
  rw [← h4] at hΔ
  exact Int.lt_irrefl 0 hΔ

end

section

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- The duty window of slot `s + 1` starts no later than slot `s`: `duty_window_start S.C (s + 1)
= S.C.t_ (s + 1) + S.C.Δ − 4 · S.C.Δ · S.C.k`, and `S.C.k ≥ 2`.

The variables:
- `S`: the setup; `s`: the slot.

Read aloud: a validator awake from the duty window's start of slot `s + 1` is awake from the start
of slot `s`. -/
theorem dutyWindowStart_succ_le_slotStart (S : Setup V) (s : ℕ) :
    dutyWindowStart S (s + 1) ≤ slotStart S s := by
  unfold dutyWindowStart
  rw [Int.toNat_le, slotStart_cast]
  have hk : 4 * S.C.Δ * 2 ≤ 4 * S.C.Δ * (S.C.k : Int) :=
    Int.mul_le_mul_of_nonneg_left (by exact_mod_cast S.C.k_ge_two)
      (Int.le_of_lt (Int.mul_pos (by decide) S.C.Δ_pos))
  have key : ∀ X d Y : Int, 0 < d → 4 * d * 2 ≤ Y → X + 4 * d + d - Y ≤ X := by
    intro X d Y h1 h2
    omega
  show 4 * S.C.Δ * (((s + 1 : ℕ) : Int)) + S.C.Δ - 4 * S.C.Δ * (S.C.k : Int) ≤
    4 * S.C.Δ * ((s : ℕ) : Int)
  rw [Nat.cast_add, Nat.cast_one, Int.mul_add, Int.mul_one]
  exact key _ _ _ S.C.Δ_pos hk

omit [RootOrder] in
/-- A time before the start of slot `s` is in a slot less than `s`. -/
theorem slot_lt_of_lt_slotStart (S : Setup V) {s t : ℕ} (h : t < slotStart S s) :
    S.C.slot (t : Int) < s := by
  rw [slot_natCast]
  rw [slotStart_eq, Nat.mul_comm] at h
  have hΔ := one_le_Δ S
  exact (Nat.div_lt_iff_lt_mul (by omega)).2 h

omit [RootOrder] in
/-- **Kit fact, slots against support cutoffs.** When the support cutoff of slot `s_a + 1` is before
the vote time of slot `s`, then `s_a + 2 ≤ s`; when it is before the support cutoff of slot
`s + 1`, then `s_a < s`; when it is at most that cutoff, then `s_a ≤ s`.

Why: slot `s` starts at `4Δ · s`, its vote time is `Δ` later and its support cutoff `2Δ` later.

The variables:
- `S`: the setup; `s_a`, `s`: the two slots.

Read aloud: a support cutoff before a vote time is two slots earlier; before or at a support
cutoff, one slot earlier or the same.

 -/
theorem slot_le_of_supportCutoff_lt (S : Setup V) (s_a s : ℕ) :
    (supportCutoff S (s_a + 1) < voteTime S s → s_a + 2 ≤ s) ∧
    (supportCutoff S (s_a + 1) < supportCutoff S (s + 1) → s_a < s) ∧
    (supportCutoff S (s_a + 1) ≤ supportCutoff S (s + 1) → s_a ≤ s) := by
  have hΔ := one_le_Δ S
  rw [supportCutoff_eq, supportCutoff_eq, voteTime_eq, voteTime_eq, voteTime_eq, slotStart_eq,
    slotStart_eq, slotStart_eq]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · by_contra hc
    have : 4 * Δ S * s ≤ 4 * Δ S * (s_a + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  · by_contra hc
    have : 4 * Δ S * (s + 1) ≤ 4 * Δ S * (s_a + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  · by_contra hc
    have : 4 * Δ S * (s + 1) < 4 * Δ S * (s_a + 1) :=
      Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    omega

omit [RootOrder] in
/-- The support cutoff grows strictly with the slot.

The variables:
- `S`: the setup; `s`, `s'`: two slots, `s` before `s'`. -/
theorem supportCutoff_lt_of_lt (S : Setup V) {s s' : ℕ} (h : s < s') :
    supportCutoff S s < supportCutoff S s' := by
  rw [supportCutoff_eq, supportCutoff_eq, voteTime_eq, voteTime_eq, slotStart_eq, slotStart_eq]
  have hΔ := one_le_Δ S
  have := Nat.mul_lt_mul_of_pos_left h (by omega : 0 < 4 * Δ S)
  omega

omit [RootOrder] in
/-- The deadline of a lock entry names its slot: two slots whose lock deadlines
`S.C.t_ (s + S.C.k) + 5 · S.C.Δ` agree are the same slot.

Why: the deadline is `4 · S.C.Δ · (s + S.C.k) + 5 · S.C.Δ`, and `S.C.Δ` is positive.

The variables:
- `S`: the setup; `s`, `s'`: the two slots.

Read aloud: two lock entries with the same deadline are locks of the same slot. -/
theorem lockDeadline_injective (S : Setup V) {s s' : ℕ}
    -- the deadlines of a lock of slot `s` and of a lock of slot `s'` agree
    (h : S.C.t_ (s + S.C.k) + 5 * S.C.Δ = S.C.t_ (s' + S.C.k) + 5 * S.C.Δ) :
    s = s' := by
  have hΔ : (0 : Int) < (S.C.Δ : Int) := S.C.Δ_pos
  have h' : @Eq Int (4 * (S.C.Δ : Int) * (((s + S.C.k : ℕ) : Int)))
      (4 * (S.C.Δ : Int) * (((s' + S.C.k : ℕ) : Int))) := by
    have h0 : @Eq Int (S.C.t_ (s + S.C.k)) (S.C.t_ (s' + S.C.k)) := by
      have h1 : @Eq Int (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) (S.C.t_ (s' + S.C.k) + 5 * S.C.Δ) := h
      omega
    exact h0
  have h4 : @Ne Int (4 * S.C.Δ) 0 := by omega
  have h'' := Int.eq_of_mul_eq_mul_left h4 h'
  have : s + S.C.k = s' + S.C.k := by exact_mod_cast h''
  omega

omit [RootOrder] in
/-- A slot comparison read off the slot starts: when `S.C.t_ s < S.C.t_ s' + r` with
`r ≤ 4 · S.C.Δ · (n + 1)`, then `s ≤ s' + n`. The two hypotheses are stated at `Int`, so that
`omega` reads them at the call sites (`omega` reads a fact stated at `Time`, an `abbrev` of `Int`,
only once restated at `Int`, as in `Lemma41.lean`).

The variables:
- `S`: the setup; `s`, `s'`, `n`: the slots and the offset; `r`: the margin. -/
theorem slot_le_of_t_lt (S : Setup V) {s s' n : ℕ} {r : Int}
    (h : @LT.lt Int _ (S.C.t_ s) (S.C.t_ s' + r))
    (hr : @LE.le Int _ r (4 * S.C.Δ * ((n : Int) + 1))) : s ≤ s' + n := by
  have hΔ : @LT.lt Int _ 0 S.C.Δ := S.C.Δ_pos
  have h' : @LT.lt Int _ (4 * S.C.Δ * (s : Int)) (4 * S.C.Δ * (s' : Int) + r) := h
  have e : @Eq Int (4 * S.C.Δ * (((s' + n + 1 : ℕ) : Int)))
      (4 * S.C.Δ * (s' : Int) + 4 * S.C.Δ * ((n : Int) + 1)) := by
    rw [show (((s' + n + 1 : ℕ) : Int)) = (s' : Int) + ((n : Int) + 1) by omega, Int.mul_add]
  have h1 : @LT.lt Int _ (4 * S.C.Δ * (s : Int)) (4 * S.C.Δ * (((s' + n + 1 : ℕ) : Int))) := by
    rw [e]
    omega
  have h2 : (s : Int) < ((s' + n + 1 : ℕ) : Int) := Int.lt_of_mul_lt_mul_left h1 (by omega)
  omega

omit [RootOrder] in
/-- The slot start grows strictly with the slot.

The variables:
- `S`: the setup; `s`, `s'`: two slots, `s` before `s'`. -/
theorem t_lt_of_lt (S : Setup V) {s s' : ℕ} (h : s < s') : @LT.lt Int _ (S.C.t_ s) (S.C.t_ s') := by
  have hΔ : @LT.lt Int _ 0 S.C.Δ := S.C.Δ_pos
  show @LT.lt Int _ (4 * S.C.Δ * (s : Int)) (4 * S.C.Δ * (s' : Int))
  exact Int.mul_lt_mul_of_pos_left (by exact_mod_cast h) (by omega)

omit [RootOrder] in
/-- The slot start grows with the slot.

The variables:
- `S`: the setup; `s`, `s'`: two slots, `s` at most `s'`. -/
theorem t_le_of_le (S : Setup V) {s s' : ℕ} (h : s ≤ s') : @LE.le Int _ (S.C.t_ s) (S.C.t_ s') := by
  have hΔ : @LT.lt Int _ 0 S.C.Δ := S.C.Δ_pos
  show @LE.le Int _ (4 * S.C.Δ * (s : Int)) (4 * S.C.Δ * (s' : Int))
  exact Int.mul_le_mul_of_nonneg_left (by exact_mod_cast h) (by omega)

omit [RootOrder] in
/-- The duty window of slot `s` starts no later than the support cutoff of every slot `s'` with
`s ≤ s' + S.C.k`: the window starts at `S.C.t_ s + S.C.Δ − 4 · S.C.Δ · S.C.k`, or at `0` when that
value is negative.

The variables:
- `S`: the setup; `s`: the slot of the duty window; `s'`: the slot of the cutoff. -/
theorem dutyWindowStart_le_supportCutoff (S : Setup V) {s s' : ℕ} (hj : s ≤ s' + S.C.k) :
    dutyWindowStart S s ≤ supportCutoff S s' := by
  unfold dutyWindowStart
  rw [Int.toNat_le, supportCutoff_cast]
  have hΔ : (0 : Int) < S.C.Δ := S.C.Δ_pos
  have h : 4 * S.C.Δ * ((s : ℕ) : Int) ≤ 4 * S.C.Δ * (((s' + S.C.k : ℕ) : Int)) :=
    Int.mul_le_mul_of_nonneg_left (by exact_mod_cast hj) (by omega)
  show 4 * S.C.Δ * ((s : ℕ) : Int) + S.C.Δ - 4 * S.C.Δ * (S.C.k : Int) ≤
    4 * S.C.Δ * ((s' : ℕ) : Int) + 2 * S.C.Δ
  rw [Nat.cast_add (R := Int) s' S.C.k, Int.mul_add] at h
  have key : ∀ P Q K d : Int, 0 < d → P ≤ Q + K → P + d - K ≤ Q + 2 * d := by
    intro P Q K d h1 h2
    omega
  exact key _ _ _ _ hΔ h

omit [RootOrder] in
/-- The duty window's start, as the spec writes it, grows with the slot.

The variables:
- `S`: the setup; `s`, `s'`: two slots, `s` at most `s'`. -/
theorem duty_window_start_mono (S : Setup V) {s s' : ℕ} (h : s ≤ s') :
    duty_window_start S.C s ≤ duty_window_start S.C s' := by
  have h' := t_le_of_le S h
  show @LE.le Int _ (S.C.t_ s + S.C.Δ - 4 * S.C.Δ * (S.C.k : Int))
    (S.C.t_ s' + S.C.Δ - 4 * S.C.Δ * (S.C.k : Int))
  omega

omit [RootOrder] in
/-- The start of a slot grows with the slot.

The variables:
- `S`: the setup; `s`, `s'`: two slots, `s` at most `s'`. -/
theorem slotStart_mono (S : Setup V) {s s' : ℕ} (h : s ≤ s') : slotStart S s ≤ slotStart S s' := by
  rw [slotStart_eq, slotStart_eq]
  exact Nat.mul_le_mul_left (4 * Δ S) h

omit [RootOrder] in
/-- The duty window of slot `s + 1` starts no later than the support cutoff of every slot `s'` with
`s + 1 ≤ s' + S.C.k`: the window starts at `S.C.t_ (s + 1) + S.C.Δ − 4 · S.C.Δ · S.C.k`, one delay
after the start of slot `s + 1 − S.C.k`, or at `0` when that value is negative.

The variables:
- `S`: the setup; `s`: the slot before the duty window's slot; `s'`: the slot of the cutoff.

Read aloud: a validator awake from the duty window's start of slot `s + 1` is awake from the
support cutoff of each of the last `S.C.k` slots up to `s`. -/
theorem dutyWindowStart_succ_le_supportCutoff (S : Setup V) {s s' : ℕ} (hj : s + 1 ≤ s' + S.C.k) :
    dutyWindowStart S (s + 1) ≤ supportCutoff S s' := by
  unfold dutyWindowStart
  rw [Int.toNat_le, supportCutoff_cast]
  have hΔ : (0 : Int) < S.C.Δ := S.C.Δ_pos
  have h : 4 * S.C.Δ * (((s + 1 : ℕ) : Int)) ≤ 4 * S.C.Δ * (((s' + S.C.k : ℕ) : Int)) :=
    Int.mul_le_mul_of_nonneg_left (by exact_mod_cast hj) (by omega)
  show 4 * S.C.Δ * (((s + 1 : ℕ) : Int)) + S.C.Δ - 4 * S.C.Δ * (S.C.k : Int) ≤
    4 * S.C.Δ * ((s' : ℕ) : Int) + 2 * S.C.Δ
  rw [Nat.cast_add (R := Int) s' S.C.k, Int.mul_add] at h
  have key : ∀ P Q K d : Int, 0 < d → P ≤ Q + K → P + d - K ≤ Q + 2 * d := by
    intro P Q K d h1 h2
    omega
  exact key _ _ _ _ hΔ h

omit [RootOrder] in
/-- The times of the support cutoff of slot `s + 1`, when `s = r · R` is the first slot of round
`r`: its slot is `s + 1`, the round of that slot is `r`, and it is the action time of that round
and the support cutoff of its slot.

The variables:
- `S`: the setup; `r`: the round; `s`: its first slot. -/
theorem supportCutoff_succ_times (S : Setup V) (r s : ℕ) (hs : s = r * S.C.R) :
    S.C.slot ((supportCutoff S (s + 1) : ℕ) : Int) = s + 1 ∧ S.C.round (s + 1) = r ∧
      ((supportCutoff S (s + 1) : ℕ) : Int) =
        S.C.a_ (S.C.round (S.C.slot ((supportCutoff S (s + 1) : ℕ) : Int))) ∧
      ((supportCutoff S (s + 1) : ℕ) : Int) =
        S.C.t_ (S.C.slot ((supportCutoff S (s + 1) : ℕ) : Int)) + 2 * S.C.Δ := by
  have hΔ := one_le_Δ S
  have hss' : slotStart S (s + 1 + 1) = slotStart S (s + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
  have hslot : S.C.slot ((supportCutoff S (s + 1) : ℕ) : Int) = s + 1 := by
    apply slot_eq_of_mem S
    · rw [supportCutoff_eq, voteTime_eq]; omega
    · rw [supportCutoff_eq, voteTime_eq, hss']; omega
  have hR := S.C.R_ge_two
  have hround : S.C.round (s + 1) = r := by
    show (s + 1) / S.C.R = r
    rw [hs, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  refine ⟨hslot, hround, ?_, ?_⟩
  · rw [hslot, hround, supportCutoff_cast]
    simp only [Config.a_, Config.T_, Config.t_]
    rw [hs]
    push_cast
    have key : ∀ d a : Int, 4 * d * (a + 1) + 2 * d = 4 * d * a + 6 * d := by
      intro d a
      rw [Int.mul_add]
      omega
    exact key _ _
  · rw [hslot]
    exact supportCutoff_cast S (s + 1)

omit [RootOrder] in
/-- The duty window's start, as a natural number, grows with the slot.

The variables:
- `S`: the setup; `s`, `s'`: two slots, `s` at most `s'`. -/
theorem dutyWindowStart_mono (S : Setup V) {s s' : ℕ} (h : s ≤ s') :
    dutyWindowStart S s ≤ dutyWindowStart S s' :=
  Int.toNat_le_toNat (duty_window_start_mono S h)

omit [RootOrder] in
/-- The start of a slot grows with the slot.

The variables:
- `S`: the setup; `a ≤ b`: the two slots. -/
theorem slotStart_le_of_le (S : Setup V) {a b : ℕ} (h : a ≤ b) : slotStart S a ≤ slotStart S b := by
  rw [slotStart_eq, slotStart_eq]
  exact Nat.mul_le_mul_left _ h

omit [RootOrder] in
/-- The support cutoff of a slot is no later than the start of the next slot.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem supportCutoff_le_slotStart_succ (S : Setup V) (s : ℕ) :
    supportCutoff S s ≤ slotStart S (s + 1) := by
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  rw [supportCutoff_eq, voteTime_eq]
  omega

omit [RootOrder] in
/-- The support cutoff of slot `s + 1` is before that of slot `s + 2`.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem supportCutoff_succ_le (S : Setup V) (s : ℕ) :
    supportCutoff S (s + 1) ≤ supportCutoff S (s + 1 + 1) := by
  have h1 := supportCutoff_eq S (s + 1)
  have h2 := supportCutoff_eq S (s + 1 + 1)
  have h3 := voteTime_succ S (s + 1)
  omega

omit [RootOrder] in
/-- The duty window of slot `s` starts `4Δk − Δ` before the start of slot `s`, or at `0` when
that is negative.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem dutyWindowStart_cases (S : Setup V) (s : ℕ) :
    dutyWindowStart S s + 4 * Δ S * S.C.k = 4 * Δ S * s + Δ S ∨
      (dutyWindowStart S s = 0 ∧ 4 * Δ S * s + Δ S < 4 * Δ S * S.C.k) := by
  have hΔ : ((Δ S : ℕ) : Int) = S.C.Δ := Δ_cast S
  have hz : duty_window_start S.C s =
      ((4 * Δ S * s : ℕ) : Int) + ((Δ S : ℕ) : Int) - ((4 * Δ S * S.C.k : ℕ) : Int) := by
    show S.C.t_ s + S.C.Δ - 4 * S.C.Δ * (S.C.k : Int) = _
    have hts : S.C.t_ s = 4 * S.C.Δ * (s : Int) := rfl
    rw [hts, ← hΔ]
    push_cast
    rfl
  unfold dutyWindowStart
  rw [hz]
  by_cases hc : 4 * Δ S * S.C.k ≤ 4 * Δ S * s + Δ S
  · left
    have : ((4 * Δ S * s : ℕ) : Int) + ((Δ S : ℕ) : Int) - ((4 * Δ S * S.C.k : ℕ) : Int) =
        ((4 * Δ S * s + Δ S - 4 * Δ S * S.C.k : ℕ) : Int) := by
      omega
    rw [this, Int.toNat_natCast]
    omega
  · right
    refine ⟨Int.toNat_of_nonpos (by omega), by omega⟩

omit [RootOrder] in
/-- **Every committee the premise constrains has its duty window inside the phase.** When slot
`s + 1` starts at or after `anchorCW S tGAT`, the duty window of slot `s` starts at least one
delay after `tGAT`.

Why: `slotStart S s ≥ tGAT + 4Δ(k + 1)`, and the duty window starts `4Δk − Δ` before it.

The variables:
- `S`: the setup; `tGAT`: the time every honest validator is awake from; `s`: the slot. -/
theorem dutyWindowStart_of_anchor (S : Setup V) (tGAT s : ℕ)
    (hA : anchorCW S tGAT ≤ slotStart S (s + 1)) :
    tGAT + Δ S ≤ dutyWindowStart S s := by
  unfold anchorCW at hA
  rw [slotStart_eq, Nat.mul_add, Nat.mul_add, Nat.mul_one] at hA
  rcases dutyWindowStart_cases S s with h | ⟨-, h⟩ <;> omega

omit [RootOrder] in
/-- **The committee premise constrains every committee the front counts.** With `s_w ≥ 1` a slot
whose duty window starts at or after `tGAT`, `anchorCW S tGAT` is at most the start of slot
`s_w + k + 1`, so the premise constrains the committee of slot `s_w + k` and every later one.

Why: `tGAT + 4Δ ≤ 4Δ s_w`, from the duty window's start `4Δ s_w + Δ − 4Δk` with `k ≥ 2`, or from
`tGAT = 0` and `s_w ≥ 1` when that start is clamped to `0`.

The variables:
- `S`: the setup; `tGAT`: the time every honest validator is awake from; `s_w`: the slot. -/
theorem anchor_le_front (S : Setup V) (tGAT s_w : ℕ) (hs_w : 1 ≤ s_w)
    (hsw : tGAT ≤ dutyWindowStart S s_w) :
    anchorCW S tGAT ≤ slotStart S (s_w + S.C.k + 1) := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hk2 : 4 * Δ S * 2 ≤ 4 * Δ S * S.C.k := Nat.mul_le_mul_left _ hk
  have hs1 : 4 * Δ S * 1 ≤ 4 * Δ S * s_w := Nat.mul_le_mul_left _ hs_w
  unfold anchorCW
  rw [slotStart_eq, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_one]
  rcases dutyWindowStart_cases S s_w with h | ⟨h0, h⟩ <;> omega

omit [RootOrder] in
/-- **The slot `τ / 4Δ` holds the time `τ`.** Its start is at most `τ`, and the next slot's start
is greater than `τ`.

The variables:
- `S`: the setup; `τ`: the time. -/
theorem slotStart_div_le (S : Setup V) (τ : ℕ) :
    slotStart S (τ / (4 * Δ S)) ≤ τ ∧ τ < slotStart S (τ / (4 * Δ S) + 1) := by
  have hΔ := one_le_Δ S
  have h1 := Nat.div_add_mod τ (4 * Δ S)
  have h2 := Nat.mod_lt τ (show 0 < 4 * Δ S by omega)
  rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  generalize τ / (4 * Δ S) = q at h1 ⊢
  generalize τ % (4 * Δ S) = b at h1 h2
  generalize 4 * Δ S * q = a at h1 ⊢
  omega

omit [RootOrder] in
/-- **The next slot's support cutoff is one slot later.**

The variables:
- `S`: the setup; `n`: the slot. -/
theorem supportCutoff_succ_eq (S : Setup V) (n : ℕ) :
    supportCutoff S (n + 1) = supportCutoff S n + 4 * Δ S := by
  have h1 := supportCutoff_eq S n
  have h2 := supportCutoff_eq S (n + 1)
  have h3 := voteTime_eq S n
  have h4 := voteTime_eq S (n + 1)
  have h5 : slotStart S (n + 1) = slotStart S n + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  omega

omit [RootOrder] in
/-- **The counting step of the climb.** For a decidable property `P` of the honest round opening
slots (in the climb, being outside the spans): with at most six honest round opening slots `i < m`
having `P` before `rR` (the one whose round holds `rR` among them), and at least `need ≥ 8` having
`P` in all: at least `need − 6` honest round opening slots having `P` are at or after `rR`. The case
`rs m * R < rR` is contradictory: at most seven have `P`. With `need = 9`, three.

The variables:
- `S`: the setup; `rs`: the rounds; `m`: the last index; `rR`: the slot counted from;
- `P`: the property; `need`: the bound.

Read aloud: the count leaves `need − 6` honest round opening slots after the fast block's first
slot. -/
theorem after_of_before (S : Setup V) (rs : ℕ → ℕ) (m rR need : ℕ) (P : ℕ → Prop)
    [DecidablePred P] (hneed : 8 ≤ need)
    (hle : ∀ i : ℕ, i ≤ m → rs i * S.C.R ≤ rs m * S.C.R)
    (h6 : ((Finset.range m).filter (fun i => rs i * S.C.R < rR ∧ P i)).card ≤ 6)
    (hO : need ≤ ((Finset.range (m + 1)).filter P).card) :
    need - 6 ≤ ((Finset.range (m + 1)).filter (fun i => rR ≤ rs i * S.C.R ∧ P i)).card := by
  classical
  set O := (Finset.range (m + 1)).filter P with hOdef
  set Bef := (Finset.range m).filter (fun i => rs i * S.C.R < rR ∧ P i) with hBef
  set Aft := (Finset.range (m + 1)).filter (fun i => rR ≤ rs i * S.C.R ∧ P i) with hAft
  have hmemBef : ∀ i ∈ O, i ≠ m → rs i * S.C.R < rR → i ∈ Bef := by
    intro i hi him hlt
    rw [hOdef, Finset.mem_filter, Finset.mem_range] at hi
    rw [hBef, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hlt, hi.2⟩
  have hmemAft : ∀ i ∈ O, rR ≤ rs i * S.C.R → i ∈ Aft := by
    intro i hi hge
    rw [hOdef, Finset.mem_filter, Finset.mem_range] at hi
    rw [hAft, Finset.mem_filter, Finset.mem_range]
    exact ⟨hi.1, hge, hi.2⟩
  by_cases hm : rR ≤ rs m * S.C.R
  · have hsub : O ⊆ Bef ∪ Aft := by
      intro i hi
      by_cases hlt : rs i * S.C.R < rR
      · have him : i ≠ m := by
          intro h
          rw [h] at hlt
          omega
        exact Finset.mem_union_left _ (hmemBef i hi him hlt)
      · exact Finset.mem_union_right _ (hmemAft i hi (by omega))
    have h1 := Finset.card_le_card hsub
    have h3 := Finset.card_union_le Bef Aft
    omega
  · exfalso
    have hsub : O ⊆ Bef ∪ {m} := by
      intro i hi
      by_cases him : i = m
      · exact Finset.mem_union_right _ (Finset.mem_singleton.2 him)
      · have hi' := hi
        rw [hOdef, Finset.mem_filter, Finset.mem_range] at hi'
        have := hle i (by omega)
        exact Finset.mem_union_left _ (hmemBef i hi him (by omega))
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le Bef ({m} : Finset ℕ)
    rw [Finset.card_singleton] at h2
    omega

omit [RootOrder] in
/-- The times of a slot, from its start. -/
theorem times_eq (S : Setup V) (s : ℕ) :
    voteTime S s = slotStart S s + Δ S ∧ supportCutoff S s = slotStart S s + 2 * Δ S ∧
      viewFreeze S s = slotStart S s + 3 * Δ S ∧ slotStart S (s + 1) = slotStart S s + 4 * Δ S ∧
      1 ≤ Δ S := by
  have h1 := voteTime_eq S s
  have h2 := supportCutoff_eq S s
  have h3 := viewFreeze_eq S s
  have h4 : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  exact ⟨h1, by omega, h3, h4, one_le_Δ S⟩

omit [RootOrder] in
/-- The support cutoff grows strictly with the slot. -/
theorem supportCutoff_lt (S : Setup V) {a b : ℕ} (h : a < b) :
    supportCutoff S a < supportCutoff S b := by
  have h1 := supportCutoff_eq S a
  have h2 := supportCutoff_eq S b
  have h3 := voteTime_eq S a
  have h4 := voteTime_eq S b
  have h5 := slotStart_eq S a
  have h6 := slotStart_eq S b
  have hΔ := one_le_Δ S
  have : 4 * Δ S * a < 4 * Δ S * b := Nat.mul_lt_mul_of_pos_left h (by omega)
  omega

omit [RootOrder] in
/-- A slot at most `k + 1` slots before the first slot after the anchor starts at or after
`tGAT`. -/
theorem tGAT_le_slotStart (S : Setup V) {tGAT s₀ s : ℕ}
    (hA : anchorCW S tGAT ≤ slotStart S (s₀ + 1)) (hs : s₀ + 1 ≤ s + S.C.k + 2) :
    tGAT ≤ slotStart S s := by
  unfold anchorCW at hA
  rw [slotStart_eq] at hA ⊢
  have h := Nat.mul_le_mul_left (4 * Δ S) hs
  have e1 : 4 * Δ S * (s + S.C.k + 2) = 4 * Δ S * s + 4 * Δ S * S.C.k + 4 * Δ S * 2 := by
    rw [Nat.mul_add, Nat.mul_add]
  have e2 : 4 * Δ S * (S.C.k + 2) = 4 * Δ S * S.C.k + 4 * Δ S * 2 := Nat.mul_add _ _ _
  omega

omit [RootOrder] in
/-- The support cutoff grows with the slot.

The variables:
- `S`: the setup; `a ≤ b`: the two slots. -/
theorem supportCutoff_mono (S : Setup V) {a b : ℕ} (h : a ≤ b) :
    supportCutoff S a ≤ supportCutoff S b := by
  have h1 := supportCutoff_eq S a
  have h2 := supportCutoff_eq S b
  have h3 := voteTime_eq S a
  have h4 := voteTime_eq S b
  have h5 := slotStart_mono S h
  omega

omit [RootOrder] in
/-- A round's first slot `s`: a round's first slot whose action time is before the support cutoff
of slot `s + 1` is at most `s − R`, so at least two slots before `s`. -/
theorem round_slot_le_of_lt (S : Setup V) {s r' : ℕ} (hsR : S.C.R ∣ s)
    (h : supportCutoff S (r' * S.C.R + 1) < supportCutoff S (s + 1)) : r' * S.C.R + 2 ≤ s := by
  have hR := S.C.R_ge_two
  have hlt : r' * S.C.R < s := by
    by_contra hn
    have := supportCutoff_mono S (show s + 1 ≤ r' * S.C.R + 1 by omega)
    omega
  obtain ⟨r₀, rfl⟩ := hsR
  rw [Nat.mul_comm S.C.R r₀] at hlt ⊢
  have h1 : r' < r₀ := Nat.lt_of_mul_lt_mul_right hlt
  have h2 := Nat.mul_le_mul_right S.C.R (show r' + 1 ≤ r₀ by omega)
  rw [Nat.succ_mul] at h2
  omega

omit [RootOrder] in
/-- The vote time grows with the slot.

The variables:
- `S`: the setup; `a ≤ b`: the two slots. -/
theorem voteTime_mono (S : Setup V) {a b : ℕ} (h : a ≤ b) : voteTime S a ≤ voteTime S b := by
  have h3 := voteTime_eq S a
  have h4 := voteTime_eq S b
  have h5 := slotStart_mono S h
  omega

omit [RootOrder] in
/-- The duty window of a slot starts no later than its vote time.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem dutyWindowStart_le_voteTime (S : Setup V) (s : ℕ) : dutyWindowStart S s ≤ voteTime S s := by
  have h1 := dutyWindowStart_mono S (Nat.le_add_right s 1)
  have h2 := dutyWindowStart_succ_le_slotStart S s
  have h3 := voteTime_eq S s
  omega

omit [RootOrder] in
/-- The support cutoff of the slot of a time `t` that is the support cutoff of its slot is `t`.

The variables:
- `S`: the setup; `t`: the time. -/
theorem supportCutoff_slot_eq (S : Setup V) {t : ℕ}
    -- `t` is the support cutoff of its slot
    (ht : (t : Int) = S.C.t_ (S.C.slot t) + 2 * S.C.Δ) :
    supportCutoff S (S.C.slot t) = t := by
  unfold supportCutoff
  rw [← ht]
  exact Int.toNat_natCast t

omit [RootOrder] in
/-- A slot starting after the support cutoff of slot `s₀ + 1` is at least `s₀ + 2`, starts after
the vote time of slot `s₀`, and starts at a time at least `1`.

The variables:
- `S`: the setup; `s₀`, `s`: the two slots. -/
theorem slot_after_healed_round (S : Setup V) (s₀ s : ℕ)
    (h : supportCutoff S (s₀ + 1) < slotStart S s) :
    s₀ + 2 ≤ s ∧ voteTime S s₀ < slotStart S s ∧ 1 ≤ slotStart S s := by
  have hΔ := one_le_Δ S
  rw [supportCutoff_eq, voteTime_eq, slotStart_eq, slotStart_eq] at h
  rw [voteTime_eq, slotStart_eq, slotStart_eq]
  have hs : s₀ + 2 ≤ s := by
    by_contra hc
    have : 4 * Δ S * s ≤ 4 * Δ S * (s₀ + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  refine ⟨hs, ?_, ?_⟩
  · have : 4 * Δ S * (s₀ + 1) ≤ 4 * Δ S * s := Nat.mul_le_mul_left _ (by omega)
    have h2 : 4 * Δ S * (s₀ + 1) = 4 * Δ S * s₀ + 4 * Δ S := by rw [Nat.mul_add, Nat.mul_one]
    omega
  · have : 4 * Δ S * 1 ≤ 4 * Δ S * s := Nat.mul_le_mul_left _ (by omega)
    omega

omit [RootOrder] in
/-- A slot is less than the support cutoff of the next slot.

The variables:
- `S`: the setup; `n`: the slot. -/
theorem lt_supportCutoff_succ (S : Setup V) (n : ℕ) : n < supportCutoff S (n + 1) := by
  have hΔ := one_le_Δ S
  have h1 : n + 1 ≤ 4 * Δ S * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
  rw [supportCutoff_eq, voteTime_eq, slotStart_eq]
  omega

omit [RootOrder] in
/-- A support cutoff at most the support cutoff of slot `n` is the support cutoff of a slot less
than `n`.

The variables:
- `S`: the setup; `s`: the slot; `n`: the bound. -/
theorem slot_lt_of_supportCutoff_le (S : Setup V) {s n : ℕ}
    (h : supportCutoff S (s + 1) ≤ supportCutoff S n) : s < n := by
  have hΔ := one_le_Δ S
  rw [supportCutoff_eq, supportCutoff_eq, voteTime_eq, voteTime_eq, slotStart_eq,
    slotStart_eq] at h
  by_contra hc
  have : 4 * Δ S * n < 4 * Δ S * (s + 1) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  omega

omit [RootOrder] in
/-- A time whose slot is at least `s` is at least the start of slot `s`. -/
theorem slotStart_le_of_le_slot (S : Setup V) {s t : ℕ} (h : s ≤ S.C.slot (t : Int)) :
    slotStart S s ≤ t := by
  rw [slot_natCast] at h
  rw [slotStart_eq, Nat.mul_comm]
  have hΔ := one_le_Δ S
  exact (Nat.le_div_iff_mul_le (by omega)).1 h

omit [RootOrder] in
/-- The vote time of a later slot is later.

The variables:
- `S`: the setup; `a`, `b`: the two slots. -/
theorem voteTime_mono' (S : Setup V) {a b : ℕ} (h : a ≤ b) : voteTime S a ≤ voteTime S b := by
  have h1 := voteTime_eq S a
  have h2 := voteTime_eq S b
  have h3 := slotStart_mono S h
  omega

omit [RootOrder] in
/-- The vote time of the next slot is four delays later.

The variables:
- `S`: the setup; `a`: the slot. -/
theorem voteTime_succ' (S : Setup V) (a : ℕ) : voteTime S (a + 1) = voteTime S a + 4 * Δ S := by
  rw [voteTime_eq, voteTime_eq, slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  omega

omit [RootOrder] in
/-- An update at a time at or after the lock's deadline `voteTime S (s + k + 1)` is the update of a
slot `s' ≥ s + k`. Copied from `scratch/goldilocks_async/probe_ar4_replan.lean:156`.

The variables:
- `S`: the setup; `s`: the hand-over slot; `s'`: the slot of the update. -/
theorem slot_of_update_after_deadline (S : Setup V) (s s' : ℕ)
    (h : voteTime S (s + S.C.k + 1) ≤ supportCutoff S (s' + 1)) :
    s + S.C.k ≤ s' := by
  have hΔ := one_le_Δ S
  by_contra hlt
  have hmono := slotStart_mono S (show s' + 1 ≤ s + S.C.k by omega)
  have h1 := voteTime_eq S (s + S.C.k + 1)
  have h2 := supportCutoff_eq S (s' + 1)
  have h3 := voteTime_eq S (s' + 1)
  have h4 : slotStart S (s + S.C.k + 1) = slotStart S (s + S.C.k) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  omega

omit [RootOrder] in
/-- At a slot `s' ≥ s + k`, the period has ended by the vote time. Copied from
`scratch/goldilocks_async/probe_ar4_replan.lean:171`.

The variables:
- `S`: the setup; `s`: the hand-over slot; `s'`: the slot; `b₁`: the end of the period. -/
theorem votes_due_of_after_period (S : Setup V) (s s' b₁ : ℕ)
    (hb₁ : b₁ + Δ S ≤ voteTime S (s + S.C.k)) (hs' : s + S.C.k ≤ s') :
    b₁ ≤ voteTime S s' := by
  have hmono := slotStart_mono S hs'
  have h1 := voteTime_eq S (s + S.C.k)
  have h2 := voteTime_eq S s'
  omega

omit [RootOrder] in
/-- `Δ_F S`, cast back, is the delay `S.C.Δ_F`: the value is at least `Δ`, which is positive.

The variables:
- `S`: the setup. -/
theorem Δ_F_cast (S : Setup V) : ((Δ_F S : ℕ) : Int) = S.C.Δ_F :=
  Int.toNat_of_nonneg (le_trans (le_of_lt S.C.Δ_pos) S.C.Δ_F_ge)

omit [RootOrder] in
/-- **Kit fact, the proposal window covers the delivery of attestations.** When
`Δ_F + Δ ≤ 4Δ(k + 1)` and `s ≥ R`, the start of the proposal window of slot `s`, plus `Δ_F`, is at
most the start of slot `s`.

Why: the window starts at `t_s + Δ − 4Δ(k + 1)` when that is nonnegative, and the condition is
the inequality; otherwise at `0`, and `Δ_F < 4ΔR ≤ t_s` (`R_covers`).

The variables:
- `S`: the setup; `s`: the slot. -/
theorem proposalWindowStart_add_Δ_F_le (S : Setup V) {s : ℕ} (hs : S.C.R ≤ s)
    (hParam : Δ_F S + Δ S ≤ 4 * Δ S * (S.C.k + 1)) :
    proposalWindowStart S s + Δ_F S ≤ slotStart S s := by
  have h1 := slotStart_cast S s
  have h2 := Δ_F_cast S
  have h3 := Δ_cast S
  have hR := S.C.R_covers
  have hΔ := S.C.Δ_pos
  have hP : S.C.Δ_F + S.C.Δ ≤ 4 * S.C.Δ * ((S.C.k : Int) + 1) := by
    have h : ((Δ_F S + Δ S : ℕ) : Int) ≤ ((4 * Δ S * (S.C.k + 1) : ℕ) : Int) := by
      exact_mod_cast hParam
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_add, h2, h3] at h
    simpa using h
  have hsR : 4 * S.C.Δ * (S.C.R : Int) ≤ 4 * S.C.Δ * (s : Int) :=
    Int.mul_le_mul_of_nonneg_left (by exact_mod_cast hs) (by omega)
  suffices h : ((proposalWindowStart S s : ℕ) : Int) + S.C.Δ_F ≤ S.C.t_ s by
    have : ((proposalWindowStart S s + Δ_F S : ℕ) : Int) ≤ ((slotStart S s : ℕ) : Int) := by
      push_cast
      rw [h2, h1]
      exact h
    exact_mod_cast this
  have ht : S.C.t_ s = 4 * S.C.Δ * (s : Int) := rfl
  unfold proposalWindowStart proposal_window_start
  rw [ht]
  obtain ⟨K, hK⟩ : ∃ K : Int, K = 4 * S.C.Δ * ((S.C.k : Int) + 1) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Int, T = 4 * S.C.Δ * (s : Int) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Int, A = 4 * S.C.Δ * (S.C.R : Int) := ⟨_, rfl⟩
  rw [← hK] at hP ⊢
  rw [← hT] at hsR ⊢
  rw [← hA] at hR hsR
  unfold Time at *
  by_cases h : 0 ≤ T + S.C.Δ - K
  · rw [Int.toNat_of_nonneg h]
    omega
  · rw [Int.toNat_of_nonpos (by omega)]
    push_cast
    omega

omit [RootOrder] in
/-- **Kit fact, the round covers the delivery of attestations.** The support cutoff of slot
`s + 1`, plus `Δ_F`, is no later than the start of slot `s + R`: the support cutoff of slot `s + 1`
is `4Δs + 6Δ`, the start of slot `s + R` is `4Δs + 4ΔR`, and `6Δ + Δ_F ≤ 4ΔR`.

The variables:
- `S`: the setup; `s`: the slot.

Read aloud: an attestation sent at the action time of the round starting at `s` arrives by the
start of the next round. -/
theorem supportCutoff_succ_add_Δ_F_le_slotStart (S : Setup V) (s : ℕ) :
    supportCutoff S (s + 1) + Δ_F S ≤ slotStart S (s + S.C.R) := by
  have h1 := supportCutoff_cast S (s + 1)
  have h2 := slotStart_cast S (s + S.C.R)
  have h3 := Δ_F_cast S
  have hR := S.C.R_covers
  suffices h : ((supportCutoff S (s + 1) : ℕ) : Int) + ((Δ_F S : ℕ) : Int) ≤
      ((slotStart S (s + S.C.R) : ℕ) : Int) by exact_mod_cast h
  rw [h1, h2, h3]
  simp only [Config.t_]
  push_cast
  have key : ∀ d f a r : Int, 6 * d + f ≤ 4 * d * r →
      4 * d * (a + 1) + 2 * d + f ≤ 4 * d * (a + r) := by
    intro d f a r h
    rw [Int.mul_add, Int.mul_add, Int.mul_one]
    omega
  exact key _ _ _ _ hR

omit [RootOrder] in
/-- The support cutoff of slot `s + 1` is no later than the start of slot `s''` when `s + R ≤ s''`.

The variables:
- `S`: the setup; `s`, `s''`: the slots. -/
theorem supportCutoff_succ_le_of_round (S : Setup V) {s s'' : ℕ} (hs'' : s + S.C.R ≤ s'') :
    supportCutoff S (s + 1) ≤ slotStart S s'' :=
  le_trans (Nat.le_add_right _ _) (le_trans (supportCutoff_succ_add_Δ_F_le_slotStart S s)
    (slotStart_le_of_le S hs''))

omit [RootOrder] in
/-- **Kit fact, the delivery before a slot places it two slots later.** When the support cutoff of
slot `s + 1`, plus `Δ_F`, is at most the start of slot `s''`, then `s + 2 ≤ s''`: the support
cutoff of slot `s + 1` is `4Δ(s + 1) + 2Δ`, so the start of slot `s + 1` is before the start of
slot `s''`.

The variables:
- `S`: the setup; `s`, `s''`: the slots.

Read aloud: if an attestation sent at the action time of slot `s` arrives before slot `s''`
starts, then `s''` is at least two slots after `s`. -/
theorem slot_add_two_le_of_delivery (S : Setup V) {s s'' : ℕ}
    (h : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'') : s + 2 ≤ s'' := by
  have hΔ := one_le_Δ S
  have h1 : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have h2 : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have h3 : slotStart S (s + 1) < slotStart S s'' := by omega
  rw [slotStart_eq, slotStart_eq] at h3
  have := Nat.lt_of_mul_lt_mul_left h3
  omega

omit [RootOrder] in
/-- **Kit fact, a later round's slot is after the delivery.** When `s + R ≤ s''`, the support cutoff
of slot `s + 1`, plus `Δ_F`, is at most the start of slot `s''`
(`supportCutoff_succ_add_Δ_F_le_slotStart`).

The variables:
- `S`: the setup; `s`, `s''`: the slots.

Read aloud: an attestation sent at the action time of the round starting at `s` arrives before
any slot of a later round starts. -/
theorem delivery_of_round (S : Setup V) {s s'' : ℕ} (hs'' : s + S.C.R ≤ s'') :
    supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'' := by
  refine le_trans (supportCutoff_succ_add_Δ_F_le_slotStart S s) ?_
  rw [slotStart_eq, slotStart_eq]
  exact Nat.mul_le_mul_left _ hs''

omit [RootOrder] in
/-- The start of slot `a + b` is the sum of the starts of slots `a` and `b`, as integers.

The variables:
- `S`: the setup; `a`, `b`: the slots. -/
theorem t_add (S : Setup V) (a b : ℕ) :
    @Eq Int (S.C.t_ (a + b)) (S.C.t_ a + S.C.t_ b) := by
  show 4 * S.C.Δ * (((a + b : ℕ) : Int)) = 4 * S.C.Δ * (a : Int) + 4 * S.C.Δ * (b : Int)
  rw [Nat.cast_add, Int.mul_add]

omit [RootOrder] in
/-- The start of slot `1` is `4 · S.C.Δ`, as an integer.

The variables:
- `S`: the setup. -/
theorem t_one (S : Setup V) : @Eq Int (S.C.t_ 1) (4 * S.C.Δ) := by
  show 4 * S.C.Δ * (((1 : ℕ) : Int)) = 4 * S.C.Δ
  rw [Nat.cast_one, Int.mul_one]

omit [RootOrder] in
/-- `proposal_window_start_eq` of `Lemma90Inclusion.lean`, copied: the proposal window of slot
`q + 2` starts where the duty window of slot `q + 1` starts.

The variables:
- `S`: the setup; `q`: the slot. -/
theorem proposal_window_start_eqJ (S : Setup V) (q : ℕ) :
    proposal_window_start S.C (q + 2) = duty_window_start S.C (q + 1) := by
  unfold proposal_window_start duty_window_start
  have h1 : S.C.t_ (q + 2) = S.C.t_ (q + 1) + 4 * S.C.Δ := by
    rw [show q + 2 = (q + 1) + 1 from rfl, t_add, t_one]
  rw [h1, Int.mul_add, Int.mul_one]
  have key : ∀ a d z : Int, a + 4 * d + d - (z + 4 * d) = a + d - z := by intro a d z; omega
  exact key _ _ _

omit [RootOrder] in
/-- `proposalWindowStart_eq` of `Lemma90Inclusion.lean`, copied, on the natural-number times.

The variables:
- `S`: the setup; `q`: the slot. -/
theorem proposalWindowStart_eqJ (S : Setup V) (q : ℕ) :
    proposalWindowStart S (q + 2) = dutyWindowStart S (q + 1) := by
  unfold proposalWindowStart dutyWindowStart
  rw [proposal_window_start_eqJ]

omit [RootOrder] in
/-- The proposal window of slot `q + 2` starts where the duty window of slot `q + 1` starts.

The variables:
- `S`: the setup; `q`: the slot. -/
theorem proposal_window_start_eq (S : Setup V) (q : ℕ) :
    proposal_window_start S.C (q + 2) = duty_window_start S.C (q + 1) := by
  unfold proposal_window_start duty_window_start
  have h1 : S.C.t_ (q + 2) = S.C.t_ (q + 1) + 4 * S.C.Δ := by
    rw [show q + 2 = (q + 1) + 1 from rfl, t_add, t_one]
  rw [h1, Int.mul_add, Int.mul_one]
  have key : ∀ a d z : Int, a + 4 * d + d - (z + 4 * d) = a + d - z := by intro a d z; omega
  exact key _ _ _

omit [RootOrder] in
/-- `proposal_window_start_eq` on the natural-number times.

The variables:
- `S`: the setup; `q`: the slot. -/
theorem proposalWindowStart_eq (S : Setup V) (q : ℕ) :
    proposalWindowStart S (q + 2) = dutyWindowStart S (q + 1) := by
  unfold proposalWindowStart dutyWindowStart
  rw [proposal_window_start_eq]

omit [RootOrder] in
/-- A slot whose start is before another slot's start is less than it.

The variables:
- `S`: the setup; `a`, `b`: the slots. -/
theorem lt_of_t_lt (S : Setup V) {a b : ℕ} (h : @LT.lt Int _ (S.C.t_ a) (S.C.t_ b)) : a < b := by
  by_contra hc
  exact absurd h (Int.not_lt.2 (t_le_of_le S (Nat.le_of_not_lt hc)))

omit [RootOrder] in
/-- The support cutoff of slot `s + 1` is in slot `s + 1`, and is at least `1`.

The variables:
- `S`: the setup; `s`: the slot before the cutoff's slot. -/
theorem supportCutoff_slot (S : Setup V) (s : ℕ) :
    S.C.slot (supportCutoff S (s + 1) : Int) = s + 1 ∧ 1 ≤ supportCutoff S (s + 1) := by
  have hΔ := one_le_Δ S
  have hss' : slotStart S (s + 1 + 1) = slotStart S (s + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₂ : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  exact ⟨slot_eq_of_mem S (by omega) (by omega), by omega⟩

omit [RootOrder] in
/-- The duty window of slot `s + 1` starts strictly before the support cutoff of slot `s + 1`.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem dutyWindowStart_succ_lt_supportCutoff (S : Setup V) (s : ℕ) :
    dutyWindowStart S (s + 1) < supportCutoff S (s + 1) := by
  have hc1 := (supportCutoff_slot S s).2
  unfold dutyWindowStart
  rcases le_or_gt (duty_window_start S.C (s + 1)) 0 with h | h
  · rw [Int.toNat_eq_zero.mpr h]
    omega
  · have hlt : duty_window_start S.C (s + 1) < ((supportCutoff S (s + 1) : ℕ) : Int) := by
      rw [supportCutoff_cast]
      unfold duty_window_start
      have hk : (0 : Int) ≤ 4 * S.C.Δ * (S.C.k : Int) := by
        have := S.C.Δ_pos
        positivity
      have key : ∀ a d m : Int, 0 < d → 0 ≤ m → a + d - m < a + 2 * d := by
        intro a d m h1 h2; omega
      exact key _ _ _ S.C.Δ_pos hk
    have h2 : (((duty_window_start S.C (s + 1)).toNat : ℕ) : Int) <
        ((supportCutoff S (s + 1) : ℕ) : Int) := by
      rw [Int.toNat_of_nonneg h.le]
      exact hlt
    exact_mod_cast h2

omit [RootOrder] in
/-- The initial `awakeSince`, `proposal_window_start C 0`, is at most `0`.

The variables:
- `C`: the configuration. -/
theorem proposal_window_start_zero_le (C : Config) : proposal_window_start C 0 ≤ 0 := by
  have h0 : C.t_ 0 = 0 := by
    show 4 * C.Δ * ((0 : Slot) : Time) = 0
    simp
  have hm : (0 : Int) ≤ 4 * C.Δ * (C.k : Int) := by
    have := C.Δ_pos
    positivity
  have key : ∀ z d m : Int, z = 0 → 0 < d → 0 ≤ m → z + d - (m + 4 * d) ≤ 0 := by
    intro z d m h1 h2 h3
    omega
  show C.t_ 0 + C.Δ - 4 * C.Δ * ((C.k : Time) + 1) ≤ 0
  rw [Int.mul_add, Int.mul_one]
  exact key _ _ _ h0 C.Δ_pos hm

omit [RootOrder] in
/-- The initial `awakeSince`, `proposal_window_start C 0`, is at most the duty window's start of
every slot.

The variables:
- `C`: the configuration; `s'`: the slot. -/
theorem proposal_window_start_zero_le_duty (C : Config) (s' : Slot) :
    proposal_window_start C 0 ≤ duty_window_start C s' := by
  have h0 : C.t_ 0 = 0 := by
    show 4 * C.Δ * ((0 : Slot) : Time) = 0
    simp
  have hs : 0 ≤ C.t_ s' := by
    have := C.Δ_pos
    show (0 : Int) ≤ 4 * C.Δ * (s' : Int)
    positivity
  have key : ∀ z d m w : Int, z = 0 → 0 < d → 0 ≤ w → z + d - (m + 4 * d) ≤ w + d - m := by
    intro z d m w h1 h2 h3
    omega
  show C.t_ 0 + C.Δ - 4 * C.Δ * ((C.k : Time) + 1) ≤ C.t_ s' + C.Δ - 4 * C.Δ * (C.k : Time)
  rw [Int.mul_add, Int.mul_one]
  exact key _ _ _ _ h0 C.Δ_pos hs

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- The start of a slot is never the action time of the round of that slot: `4 Δ s` and
`4 Δ (r R) + 6 Δ` differ, since `4 s = 4 r R + 6` has no solution.

The variables:
- `C`: the parameters; `s`: the slot. -/
theorem slotStart_ne_actionTime (C : Config) (s : Slot) : C.t_ s ≠ C.a_ (C.round s) := by
  intro h
  simp only [Config.t_, Config.a_, Config.T_] at h
  generalize ((C.round s * C.R : ℕ) : Int) = b at h
  generalize (s : Int) = a at h
  have e1 : 4 * C.Δ * a = C.Δ * (4 * a) := by rw [Int.mul_comm 4 C.Δ, Int.mul_assoc]
  have e2 : 4 * C.Δ * b + 6 * C.Δ = C.Δ * (4 * b + 6) := by
    rw [Int.mul_add, Int.mul_comm 6 C.Δ, Int.mul_comm 4 C.Δ, Int.mul_assoc]
  rw [e1, e2] at h
  have h3 := Int.eq_of_mul_eq_mul_left (ne_of_gt C.Δ_pos) h
  omega

end

/-! ## The times read through their definitions by execution proofs

Added by the record migration, step 1h: the facts that execution proofs read off the
bodies of the time definitions, which `Statements/Routines/ScheduleDefs.lean` and the spec now keep
to their own pages. -/

section

variable {V : Type} [DecidableEq V] [Fintype V]

/-- **The spec's duty window start is at most the library's.** `dutyWindowStart S s` is
`duty_window_start S.C s` made a natural number by `Int.toNat`, which raises a negative value to
`0` and keeps the others.

The variables:
- `S`: the setup; `s`: the slot.

Read aloud: the spec's start of slot `s`'s duty window, an integer, is at most
`dutyWindowStart S s` read as an integer. -/
theorem duty_window_start_le_dutyWindowStart (S : Setup V) (s : ℕ) :
    duty_window_start S.C s ≤ ((dutyWindowStart S s : ℕ) : Int) := by
  unfold dutyWindowStart
  exact Int.self_le_toNat _

/-- **The duty window of a slot starts before the slot's support cutoff.** The spec's
`duty_window_start S.C s` is `S.C.t_ s + S.C.Δ − 4 * S.C.Δ * S.C.k`, and the support cutoff
`supportCutoff S s` is `S.C.t_ s + 2 * S.C.Δ`, with `S.C.Δ` positive.

The variables:
- `S`: the setup; `s`: the slot.

Read aloud: the duty window of slot `s` starts strictly before slot `s`'s support cutoff. -/
theorem duty_window_start_lt_supportCutoff (S : Setup V) (s : ℕ) :
    duty_window_start S.C s < ((supportCutoff S s : ℕ) : Int) := by
  rw [supportCutoff_cast]
  unfold duty_window_start
  have hk : (0 : Int) ≤ 4 * S.C.Δ * (S.C.k : Int) := by
    have := S.C.Δ_pos
    positivity
  have key : ∀ a d m : Int, 0 < d → 0 ≤ m → a + d - m < a + 2 * d := by
    intro a d m h1 h2; omega
  exact key _ _ _ S.C.Δ_pos hk

/-- **The duty window's start as a natural number, written out.** `dutyWindowStart S s` is the
spec's `duty_window_start S.C s` made a natural number by `Int.toNat`.

The variables:
- `S`: the setup; `s`: the slot.

Read aloud: `dutyWindowStart S s` is `duty_window_start S.C s`, or `0` when that is negative. -/
theorem dutyWindowStart_eq_toNat (S : Setup V) (s : ℕ) :
    dutyWindowStart S s = (duty_window_start S.C s).toNat := by
  rfl

omit [DecidableEq V] [Fintype V] in
/-- **The spec's duty window start, written out.** `duty_window_start C s` is
`C.t_ s + C.Δ − 4 * C.Δ * C.k`: one delay after the start of slot `s`, less `C.k` slots.

The variables:
- `C`: the parameters; `s`: the slot.

Read aloud: the duty window of slot `s` starts `C.k` slots before slot `s`'s vote time. -/
theorem duty_window_start_eq (C : Config) (s : Slot) :
    duty_window_start C s = C.t_ s + C.Δ - 4 * C.Δ * (C.k : Time) := by
  rfl

omit [DecidableEq V] [Fintype V] in
/-- **The start of a slot, written out.** The spec's `C.t_ s` is `4 * C.Δ * s`: the slots are
`4 * C.Δ` long and slot `0` starts at the time `0`.

The variables:
- `C`: the parameters; `s`: the slot.

Read aloud: slot `s` starts at the time `4 * C.Δ * s`. -/
theorem t_eq_mul (C : Config) (s : Slot) : C.t_ s = 4 * C.Δ * (s : Time) := by
  rfl

/-- **The time `anchorCW S tGAT`, written out.** `anchorCW S tGAT` is the time `k + 2` slots after
`tGAT`, `tGAT + 4 * Δ S * (S.C.k + 2)`.

The variables:
- `S`: the setup; `tGAT`: the time from which every honest validator is awake.

Read aloud: `anchorCW S tGAT` is `tGAT` plus `k + 2` slots of `4 * Δ S` each. -/
theorem anchorCW_eq (S : Setup V) (tGAT : ℕ) :
    anchorCW S tGAT = tGAT + 4 * Δ S * (S.C.k + 2) := by
  rfl

end

end GoldilocksCorrectness.Proofs.Routines
