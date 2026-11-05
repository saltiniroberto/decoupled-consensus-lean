module
public import GoldilocksCorrectness.Proofs.Routines.Lemma35
import all Goldilocks.AC.Confirmation

@[expose] public section

/-!
# Lemma 37: the slow test reads the saved confirmations

The proof of `lem37_slow_test_saved_confirmations`, stated in
`GoldilocksCorrectness/Statements/Routines/ConfirmationStatements.lean`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 37, the slow test reads the saved confirmations.** When the slow test of `L` in the
update of slot `s` passes, `C.k − 1 ≤ s`, and for every slot `s'` from `s + 1 − C.k` to
`s − 1`, slot `s'` has a saved confirmation `C'`, `C'` is a block of `Φ.tree`, and `L` is `C'` or
an ancestor of `C'`.

Why: the slow test asks `C.k − 1 ≤ s` and `saved_extends` at every slot of `slots_before s C.k`,
the slots `s + 1 − C.k + i` for `i < C.k − 1`, which are the slots from `s + 1 − C.k` to
`s − 1`; `saved_extends` is `false` at a slot with no saved confirmation.

The variables:
- `C`: the configuration; `A`: the AC state; `Φ`: the frame;
- `s`: the slot of the update; `L`: the block tested.

Read aloud: the slow test of `L` for slot `s` says `C.k − 1 ≤ s` and, for every slot `s'` from
`s + 1 − C.k` to `s − 1`, that a saved confirmation of slot `s'` exists, is in `Φ.tree`, and
extends `L`. -/
theorem lem37_slow_test_saved_confirmations (C : Config) (A : ACState V) (Φ : Frame V)
    (s : Slot) (L : Block V)
    -- the slow test of `L` in the update of slot `s` passes
    (hSlow : slow_test C A Φ s L = true) :
    C.k - 1 ≤ s ∧ ∀ s' : Slot, s + 1 - C.k ≤ s' → s' < s →
      ∃ C' : Block V, A.saved_confirmation s' = some C' ∧ C' ∈ Φ.tree ∧ L.AncestorEq C' := by
  simp only [slow_test, decide_eq_true_eq] at hSlow
  obtain ⟨hk, hall⟩ := hSlow
  refine ⟨hk, fun s' hj hjs => ?_⟩
  have hmem : s' ∈ slots_before s C.k := by
    simp only [slots_before, Finset.map', Finset.mem_image, Finset.mem_range]
    -- `omega` reads facts stated at `Slot`, an `abbrev` of `ℕ`, only once restated at `ℕ`
    have hjs' : @LT.lt ℕ _ s' s := hjs
    have hj' : @LE.le ℕ _ (s + 1 - C.k) s' := hj
    have hk' : @LE.le ℕ _ (C.k - 1) s := hk
    exact ⟨s' - (s + 1 - C.k), by omega, Nat.add_sub_of_le hj'⟩
  have h := hall s' hmem
  rw [saved_extends_eq] at h
  cases hS : A.saved_confirmation s' with
  | none => simp [hS] at h
  | some C' =>
    simp only [hS, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨C', rfl, h⟩

end GoldilocksCorrectness.Proofs.Routines
