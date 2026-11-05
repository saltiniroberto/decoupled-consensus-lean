module
public import GoldilocksCorrectness.Proofs.Routines.Confirmation
import all Goldilocks.AC.Confirmation
import all Goldilocks.Config
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# Lemma 35: the lock entry a confirmation update adds

The proof of `lem35_update_confirmation_lock_entries`, stated in
`GoldilocksCorrectness/Statements/Routines/ConfirmationStatements.lean`, and of the two facts
about the slow test it uses: what `saved_extends` answers (`saved_extends_eq`), and that the slow
test of the update of slot `s'` reads only the saved confirmations of the slots before `s'`
(`slow_test_congr`).
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- `saved_extends A Φ j B` answers, when slot `j` has a saved confirmation `Cj`, whether `Cj` is
a block of `Φ.tree` of which `B` is an ancestor or which is `B`, and `false` when slot `j` has no
saved confirmation.

The variables:
- `A`: the AC state; `Φ`: the frame; `j`: the slot read; `B`: the block tested. -/
theorem saved_extends_eq (A : ACState V) (Φ : Frame V) (j : Slot) (B : Block V) :
    saved_extends A Φ j B =
      match A.saved_confirmation j with
      | none => false
      | some Cj => decide (Cj ∈ Φ.tree) && B.ancestorEq Cj := by
  have hget : A.saved_confirmation[j] = A.saved_confirmation j := rfl
  simp only [saved_extends, Id.run]
  cases hS : A.saved_confirmation j with
  | none => simp [hget, hS, pure]
  | some Cj =>
    simp only [hget, hS, ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
      Option.get_some, pure]

omit [Fintype V] [RootOrder] in
/-- The slow test of a block in the update of slot `s'` answers alike on two AC states whose saved
confirmations agree at every slot before `s'`.

Why: the test reads the saved confirmations of the slots `s' + 1 − C.k` to `s' − 1` only.

The variables:
- `C`: the configuration; `A₁`, `A₂`: the two AC states; `Φ`: the frame;
- `s'`: the slot of the update; `B`: the block tested. -/
theorem slow_test_congr (C : Config) (A₁ A₂ : ACState V) (Φ : Frame V) (s' : Slot) (B : Block V)
    -- the two AC states have the same saved confirmation at every slot before `s'`
    (h : ∀ j : Slot, j < s' → A₁.saved_confirmation j = A₂.saved_confirmation j) :
    slow_test C A₁ Φ s' B = slow_test C A₂ Φ s' B := by
  unfold slow_test
  rw [decide_eq_decide]
  refine and_congr_right fun hk => forall₂_congr fun j hj => ?_
  simp only [slots_before, Finset.map', Finset.mem_image, Finset.mem_range] at hj
  obtain ⟨i, hi, rfl⟩ := hj
  -- `omega` reads facts stated at `Slot`, an `abbrev` of `ℕ`, only once restated at `ℕ`
  have hk' : @LE.le ℕ _ (C.k - 1) s' := hk
  have hlt : @LT.lt ℕ _ (s' + 1 - C.k + i) s' := by omega
  rw [saved_extends_eq, saved_extends_eq, h _ hlt]

/-- **Lemma 35, the lock entry a confirmation update adds.** The confirmation update of slot `s`
deletes no lock entry, and every entry of its answer that is not an entry of its input has the
deadline `C.t_ (s − 1 + C.k) + 5 · C.Δ`, is on a block of `Φ.tree` other than the genesis block
that is the saved confirmation of slot `s − 1` or an ancestor of it, and that block is a fast
block of the answer or passes the slow test on the input.

Why: the update writes the lock entries once, adding one entry on the deepest block of the path
(the blocks of `Φ.tree`, other than the genesis block, that are the confirmation or ancestors of
it) passing the fast or the slow test; a block passing the fast test is one of the fast blocks the
update writes, and the slow test reads only the saved confirmations of the slots before `s − 1`,
which the update does not change.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees;
- `A`: the AC state before the update; `A'`: the AC state after it; `Φ`: the frame;
- `t`: the time of the update; `s`: the slot of the update.

Read aloud: the confirmation update of slot `s` deletes no lock entry, and every entry it adds has
the deadline `C.t_ (s − 1 + C.k) + 5 · C.Δ`, is on a non-genesis block of `Φ.tree` that is the
saved confirmation of slot `s − 1` or an ancestor of it, and that block is a fast block of the
answer or passes the slow test. -/
theorem lem35_update_confirmation_lock_entries (C : Config) (P : Provisional V) (A A' : ACState V)
    (Φ : Frame V) (t : Time) (s : Slot)
    -- the confirmation update of slot `s` answers `A'`
    (hUpdate : update_confirmation C P A Φ t s = .ok A') :
    A.lock_entries ⊆ A'.lock_entries ∧
    ∀ e ∈ A'.lock_entries, e ∈ A.lock_entries ∨
      (e.d = C.t_ (s - 1 + C.k) + 5 * C.Δ ∧ e.B ∈ Φ.tree ∧ e.B ≠ Block.genesis ∧
        (∃ C' : Block V, A'.saved_confirmation (s - 1) = some C' ∧ e.B.AncestorEq C') ∧
        (e.B ∈ A'.fast_blocks ∨ slow_test C A Φ (s - 1) e.B = true)) := by
  simp only [update_confirmation] at hUpdate
  by_cases hs0 : s = 0
  · -- at the first slot the update answers its input
    rw [if_pos hs0] at hUpdate
    simp only [pure, Except.pure, Except.ok.injEq] at hUpdate
    subst hUpdate
    exact ⟨subset_refl _, fun e he => Or.inl he⟩
  rw [if_neg hs0] at hUpdate
  obtain ⟨early, -, h1⟩ := dre_bind_eq_ok hUpdate
  obtain ⟨late, -, h2⟩ := dre_bind_eq_ok h1
  obtain ⟨H, -, h3⟩ := dre_bind_eq_ok h2
  obtain ⟨b, -, h4⟩ := dre_bind_eq_ok h3
  cases b
  · -- no block is saved: the lock entries are kept
    rw [if_neg (by decide)] at h4
    split at h4
    case isTrue hne => exact absurd rfl hne
    case isFalse =>
      simp only [pure, Except.pure, Except.ok.injEq] at h4
      subst h4
      exact ⟨subset_refl _, fun e he => Or.inl he⟩
  rw [if_pos rfl] at h4
  split at h4
  case isFalse hne => exact absurd (Option.some_ne_none H) hne
  split at h4
  case isFalse =>
    -- a live lock vetoes `H`: the lock entries are kept
    simp only [pure, Except.pure, Except.ok.injEq] at h4
    subst h4
    exact ⟨subset_refl _, fun e he => Or.inl he⟩
  obtain ⟨fb, hfb, h5⟩ := dre_bind_eq_ok h4
  obtain ⟨lk, hlk, h6⟩ := dre_bind_eq_ok h5
  generalize hD : Block.deepest? lk = D at h6
  cases D with
  | none =>
    -- no block passes a lock test: the lock entries are kept
    simp only [ne_eq, not_true_eq_false, dite_false, pure, Except.pure, Except.ok.injEq] at h6
    subst h6
    exact ⟨subset_refl _, fun e he => Or.inl he⟩
  | some D =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some,
      pure, Except.pure, Except.ok.injEq] at h6
    subst h6
    refine ⟨Finset.subset_union_left, fun e he => ?_⟩
    rcases Finset.mem_union.1 he with he | he
    · exact Or.inl he
    right
    rw [Finset.mem_singleton] at he
    subst he
    -- `D` is a block of the path that passes the fast or the slow test
    obtain ⟨hpath, htest⟩ := (mem_of_filterM_eq_ok_iff _ _ _ hlk D).1 (deepest?_mem hD)
    have hpath' := hpath
    simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hpath'
    obtain ⟨hDT, hDne, hDH⟩ := hpath'
    refine ⟨rfl, hDT, hDne, ⟨H, Function.update_self _ _ _, hDH⟩, ?_⟩
    obtain ⟨f, hf, hor⟩ := dre_bind_eq_ok htest
    simp only [pure, Except.pure, Except.ok.injEq] at hor
    cases f
    · -- the slow test, which reads only the saved confirmations of the slots before `s − 1`
      right
      rw [Bool.false_or] at hor
      rw [← hor]
      refine slow_test_congr C _ _ Φ (s - 1) D fun j hj => ?_
      exact (Function.update_of_ne (Nat.ne_of_lt hj) _ _).symm
    · -- the fast test
      left
      exact (mem_of_filterM_eq_ok_iff _ _ _ hfb D).2 ⟨hpath, hf⟩

end GoldilocksCorrectness.Proofs.Routines
