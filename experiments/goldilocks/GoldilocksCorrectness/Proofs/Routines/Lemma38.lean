module
public import GoldilocksCorrectness.Proofs.Routines.Locks
import all Goldilocks.AC.Confirmation
import all Goldilocks.AC.State

@[expose] public section

/-!
# Lemma 38: the revocation moves entries to ancestors and keeps deadlines

The proof of `lem38_revoke_locks_entries_moved`, stated in
`GoldilocksCorrectness/Statements/Routines/LockStatements.lean`, and of the helper
`moved_entry_eq_ok_some_d`: an entry that `moved_entry` answers keeps the deadline of the entry
moved.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] in
/-- An entry that `moved_entry` answers has the deadline of the entry moved.

The variables:
- `P`: the provisional parameters, with the committees; `A`: the AC state; `Φ`: the frame;
- `votes`: the votes counted; `equivocators`: the validators not counted; `s`: the slot;
- `e`: the entry moved; `e'`: the entry answered. -/
theorem moved_entry_eq_ok_some_d {P : Provisional V} {A : ACState V} {Φ : Frame V}
    {votes : Finset (GoldfishVote V)} {equivocators : Finset V} {s : Slot}
    {e e' : LockEntry V}
    -- `moved_entry` answers `e'` on `e`
    (h : moved_entry P A Φ votes equivocators s e = .ok (some e')) :
    e'.d = e.d := by
  simp only [moved_entry] at h
  obtain ⟨candidates, -, hret⟩ := dre_bind_eq_ok h
  generalize hD : Block.deepest? candidates = D at hret
  cases D with
  | none => cases hret
  | some B' =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
      Option.get_some] at hret
    cases hret
    rfl

/-- **Lemma 38, the revocation moves entries to ancestors and keeps deadlines.** After the
revocation of the locks of slot `s ≥ 1` at the time `t`, every lock entry `e'` left comes from a
lock entry `e` of the input that is live at `t`: `e'` has `e`'s deadline, and `e'`'s block is a
block of `Φ.tree` that is `e`'s block or an ancestor of it.

Why: the revocation replaces the lock entries by the live entries, each moved back by
`moved_entry`, which answers an entry on a block of `Φ.tree` that is the entry's block or an
ancestor of it, with the entry's deadline.

The variables:
- `P`: the provisional parameters, with the committees; `A`: the AC state before the revocation;
  `A'`: the AC state after it; `Φ`: the frame; `t`: the time of the revocation;
- `s`: the slot of the revocation.

Read aloud: every entry the revocation of slot `s ≥ 1` leaves comes from an entry of the input live
at `t`, has that entry's deadline, and is on a block of `Φ.tree` that is that entry's block or an
ancestor of it. -/
theorem lem38_revoke_locks_entries_moved (P : Provisional V) (A A' : ACState V) (Φ : Frame V)
    (t : Time) (s : Slot)
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- the revocation of slot `s` answers `A'`
    (hRevoke : revoke_locks P A Φ t s = .ok A') :
    ∀ e' ∈ A'.lock_entries, ∃ e ∈ A.lock_entries, is_live Φ t e = true ∧ e'.d = e.d ∧
      e'.B.AncestorEq e.B ∧ e'.B ∈ Φ.tree := by
  simp only [revoke_locks] at hRevoke
  rw [if_neg (Nat.one_le_iff_ne_zero.mp hs)] at hRevoke
  obtain ⟨moved, hmoved, hret⟩ := dre_bind_eq_ok hRevoke
  cases hret
  intro e' he'
  rw [present_mem_iff] at he'
  obtain ⟨e₀, he₀, hm⟩ := mem_of_imageM_eq_ok _ _ _ hmoved _ he'
  obtain ⟨hT, hanc, -⟩ := moved_entry_eq_ok_some hm
  simp only [live_entries, Finset.mem_filter] at he₀
  exact ⟨e₀, he₀.1, he₀.2, moved_entry_eq_ok_some_d hm, hanc, hT⟩

end GoldilocksCorrectness.Proofs.Routines
