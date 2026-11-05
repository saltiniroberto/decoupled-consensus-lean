module
public import Goldilocks.AC.Interface
public import GoldilocksCorrectness.Proofs.Routines.Confirmation
import all Goldilocks.AC.Confirmation
import all Goldilocks.AC.Interface
import all Goldilocks.AC.State

@[expose] public section

/-!
# The record of the confirmed tip at the routine level

The proofs of the three routine facts of `GoldilocksCorrectness/Statements/Executions/ConfirmedTipStatements.lean`
about the record `A.latest_confirmed` and the confirmed tip `ac_confirmed A Φ`:

- `advance_cases`: `advance Φ old C?` is `old` or the confirmation `C?` holds;
- `ac_confirmed_cases`: the confirmed tip is the record when the record is in `Φ.tree`, and
  `Φ.F` otherwise;
- `update_confirmation_latest_cases`, a kit fact: the confirmation update keeps the record when it
  saves no confirmation or a live lock vetoes the one it saves, and otherwise writes `advance` of
  the record with the saved confirmation;
- `update_confirmation_latest_confirmed`: the update keeps the record, or writes the
  confirmation it saves, which no live lock vetoes.


-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- `advance Φ old C?` is `old`, or `C?` is some block `C` and `advance Φ old C?` is `C`.

The variables:
- `Φ`: the frame; `old`: the record of the confirmed tip; `C?`: the confirmation. -/
theorem advance_cases (Φ : Frame V) (old : Block V) (C? : Option (Block V)) :
    advance Φ old C? = old ∨ ∃ C : Block V, C? = some C ∧ advance Φ old C? = C := by
  cases C? with
  | none =>
      left
      simp only [advance, Id.run, ne_eq, not_true_eq_false, dite_false]
      rfl
  | some C =>
      simp only [advance, Id.run, ne_eq, reduceCtorEq, not_false_eq_true, dite_true,
        Option.value, Option.get_some]
      split
      · left; rfl
      · right; exact ⟨C, rfl, rfl⟩

omit [Fintype V] [RootOrder] in
/-- `advance Φ old (some C)` is `old` when `old` is in `Φ.tree` and `C` is an ancestor of `old` or
`old` itself, and `C` otherwise.

The variables:
- `Φ`: the frame; `old`: the record of the confirmed tip; `C`: the confirmation. -/
theorem advance_some (Φ : Frame V) (old C : Block V) :
    (old ∈ Φ.tree ∧ C.AncestorEq old ∧ advance Φ old (some C) = old) ∨
      (¬ (old ∈ Φ.tree ∧ C.AncestorEq old) ∧ advance Φ old (some C) = C) := by
  simp only [advance, Id.run, ne_eq, reduceCtorEq, not_false_eq_true, dite_true,
    Option.value, Option.get_some]
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact Or.inl ⟨h.1, h.2, rfl⟩
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact Or.inr ⟨h, rfl⟩

omit [Fintype V] [RootOrder] in
/-- The confirmed tip is the record `A.latest_confirmed` when the record is in `Φ.tree`, and
`Φ.F` otherwise.

The variables:
- `A`: the AC state; `Φ`: the frame. -/
theorem ac_confirmed_cases (A : ACState V) (Φ : Frame V) :
    (A.latest_confirmed ∈ Φ.tree ∧ ac_confirmed A Φ = A.latest_confirmed) ∨
      (A.latest_confirmed ∉ Φ.tree ∧ ac_confirmed A Φ = Φ.F) := by
  simp only [ac_confirmed, Id.run]
  split
  · rename_i h
    exact Or.inl ⟨h, rfl⟩
  · rename_i h
    exact Or.inr ⟨h, rfl⟩

/-- **Kit fact, what the confirmation update does to the record of the confirmed tip.** The
confirmation update of slot `s ≥ 1` saves no confirmation of slot `s − 1` and keeps the record;
or it saves a block `C`, and either a live lock of its input vetoes `C` and the record is kept,
or none does and the record becomes `advance Φ A.latest_confirmed (some C)`.

Why: the update writes the record once, in its fourth step, under the two tests that a
confirmation was saved and that no live lock of the input's lock entries vetoes it; the saved
confirmation and the fast blocks are written before, and the lock entries after.

The variables:
- `C`: the parameters; `P`: the values; `A`, `A'`: the AC state before and after the update;
- `Φ`: the frame; `t`: the time; `s`: the slot of the update. -/
theorem update_confirmation_latest_cases (C : Config) (P : Provisional V) (A A' : ACState V)
    (Φ : Frame V) (t : Time) (s : Slot)
    -- the update is of a slot after slot `0`
    (hs : s ≠ 0)
    -- the update answers `A'`
    (hUpdate : update_confirmation C P A Φ t s = .ok A') :
    (A'.saved_confirmation (s - 1) = none ∧ A'.latest_confirmed = A.latest_confirmed) ∨
      ∃ C' : Block V, A'.saved_confirmation (s - 1) = some C' ∧
        ((live_lock_vetoes A Φ t C' = true ∧ A'.latest_confirmed = A.latest_confirmed) ∨
          (live_lock_vetoes A Φ t C' = false ∧
            A'.latest_confirmed = advance Φ A.latest_confirmed (some C'))) := by
  simp only [update_confirmation] at hUpdate
  rw [if_neg hs] at hUpdate
  obtain ⟨early, -, h1⟩ := dre_bind_eq_ok hUpdate
  obtain ⟨late, -, h2⟩ := dre_bind_eq_ok h1
  obtain ⟨H, -, h3⟩ := dre_bind_eq_ok h2
  obtain ⟨b, -, h4⟩ := dre_bind_eq_ok h3
  cases b
  · -- no block is saved
    rw [if_neg (by decide)] at h4
    split at h4
    case isTrue hne => exact absurd rfl hne
    case isFalse =>
      simp only [pure, Except.pure, Except.ok.injEq] at h4
      subst h4
      exact Or.inl ⟨by simp only [Function.update_self], rfl⟩
  rw [if_pos rfl] at h4
  split at h4
  case isFalse hne => exact absurd (Option.some_ne_none H) hne
  split at h4
  case isFalse hveto =>
    -- a live lock vetoes `H`: the record is kept
    simp only [pure, Except.pure, Except.ok.injEq] at h4
    subst h4
    refine Or.inr ⟨H, by simp only [Function.update_self], Or.inl ⟨?_, rfl⟩⟩
    have h' : live_lock_vetoes { A with
        saved_confirmation := Function.update A.saved_confirmation (s - 1) (some H),
        fast_blocks := ∅ } Φ t H = true := by
      simpa [Option.value, Option.get_some] using hveto
    exact h'
  case isTrue hveto =>
    obtain ⟨fb, -, h5⟩ := dre_bind_eq_ok h4
    obtain ⟨lk, -, h6⟩ := dre_bind_eq_ok h5
    have hv' : live_lock_vetoes { A with
        saved_confirmation := Function.update A.saved_confirmation (s - 1) (some H),
        fast_blocks := ∅ } Φ t H = false := by
      simpa [Option.value, Option.get_some] using hveto
    have hv : live_lock_vetoes A Φ t H = false := hv'
    generalize hD : Block.deepest? lk = D at h6
    cases D with
    | none =>
        simp only [ne_eq, not_true_eq_false, dite_false, pure, Except.pure,
          Except.ok.injEq] at h6
        subst h6
        exact Or.inr ⟨H, by simp only [Function.update_self], Or.inr ⟨hv, rfl⟩⟩
    | some D =>
        simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
          Option.get_some, pure, Except.pure, Except.ok.injEq] at h6
        subst h6
        exact Or.inr ⟨H, by simp only [Function.update_self], Or.inr ⟨hv, rfl⟩⟩

/-- The confirmation update of slot `s ≥ 1` keeps the record of the confirmed tip, or writes the
confirmation of slot `s − 1` it saves, which no live lock of its input vetoes.

Why: `update_confirmation_latest_cases`, and `advance_some`: `advance` of the record with the
saved confirmation is the record or the saved confirmation.

The variables:
- `C`: the parameters; `P`: the values; `A`, `A'`: the AC state before and after the update;
- `Φ`: the frame; `t`: the time; `s`: the slot of the update. -/
theorem update_confirmation_latest_confirmed (C : Config) (P : Provisional V)
    (A A' : ACState V) (Φ : Frame V) (t : Time) (s : Slot)
    -- the update is of a slot after slot `0`
    (hs : s ≠ 0)
    -- the update answers `A'`
    (hUpdate : update_confirmation C P A Φ t s = .ok A') :
    A'.latest_confirmed = A.latest_confirmed ∨
      (A'.saved_confirmation (s - 1) = some A'.latest_confirmed ∧
        live_lock_vetoes A Φ t A'.latest_confirmed = false) := by
  rcases update_confirmation_latest_cases C P A A' Φ t s hs hUpdate with
    ⟨-, h⟩ | ⟨C', hC', ⟨-, h⟩ | ⟨hv, h⟩⟩
  · exact Or.inl h
  · exact Or.inl h
  · rcases advance_some Φ A.latest_confirmed C' with ⟨-, -, ha⟩ | ⟨-, ha⟩
    · rw [ha] at h
      exact Or.inl h
    · rw [ha] at h
      rw [h]
      exact Or.inr ⟨hC', hv⟩

end GoldilocksCorrectness.Proofs.Routines
