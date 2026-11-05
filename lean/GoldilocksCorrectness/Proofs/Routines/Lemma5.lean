module
public import GoldilocksCorrectness.Proofs.Routines.Locks
import all Goldilocks.AC.Confirmation

@[expose] public section

/-!
# Lemma 5: after the revocation, every lock entry is compatible with a majority block

The proof of `lem5_revoke_locks_entries_compatible`, stated in
`GoldilocksCorrectness/Statements/Routines/LockStatements.lean`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 5, after the revocation every lock entry is compatible with a majority block.** After
the revocation of the locks of slot `s` against the slot-`(s − 1)` votes of `A`'s pool, every lock
entry left is on a block of `Φ.tree` compatible with `R`, when every member of `Hs` has exactly one
slot-`(s − 1)` vote in the pool, it resolves and its head is a block of `Φ.tree` that is `R` or a
descendant of `R`, and the slot-`(s − 1)` committee is at most twice `Hs`.

Why: every entry left is an entry moved back to a block `B'` of `Φ.tree` whose opponents, counted
twice, are fewer than the committee. If `B'` conflicted with `R`, it would conflict with the head
of every member of `Hs`, so every member of `Hs` would be an opponent of `B'`, and the opponents,
counted twice, would be at least twice `Hs`, hence at least the committee.



The variables:
- `P`: the provisional parameters, with the committees; `A`: the AC state before the revocation;
- `A'`: the AC state after it; `Φ`: the frame; `t`: the time of the revocation;
- `s`: the slot of the revocation; `R`: the majority block;
- `Hs`: the members of the slot-`(s − 1)` committee voting for `R`'s chain. -/
theorem lem5_revoke_locks_entries_compatible (P : Provisional V) (A A' : ACState V)
    (Φ : Frame V) (t : Time) (s : Slot) (R : Block V) (Hs : Finset V)
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- no two blocks of `Φ.tree` share a root
    (hRoots : RootsNameBlocksIn Φ.tree)
    -- each member of `Hs` has exactly one slot-`(s − 1)` vote in `A`'s pool, it resolves, and
    -- its head is a block of `Φ.tree` that is `R` or a descendant of `R`
    (hHs : ∀ v ∈ Hs, VotesOnceInPoolFor A Φ (s - 1) R v)
    -- the slot-`(s − 1)` committee is at most twice `Hs`
    (hHalf : (P.committee (s - 1)).card ≤ 2 * Hs.card)
    -- the revocation of slot `s` answers `A'`
    (hRevoke : revoke_locks P A Φ t s = .ok A') :
    -- then every lock entry of `A'` is on a block of `Φ.tree` compatible with `R`
    ∀ e ∈ A'.lock_entries, e.B ∈ Φ.tree ∧ e.B.compatible R = true := by
  simp only [revoke_locks] at hRevoke
  have hs0 : s ≠ 0 := Nat.one_le_iff_ne_zero.mp hs
  rw [if_neg hs0] at hRevoke
  obtain ⟨moved, hmoved, hret⟩ := dre_bind_eq_ok hRevoke
  cases hret
  intro e he
  rw [present_mem_iff] at he
  obtain ⟨e₀, -, he₀⟩ := mem_of_imageM_eq_ok _ _ _ hmoved _ he
  obtain ⟨hT, -, o, ho, hcard⟩ := moved_entry_eq_ok_some he₀
  refine ⟨hT, ?_⟩
  by_contra hcompat
  have hconf : e.B.conflicts R = true := (conflicts_iff _ _).2 hcompat
  have hsub : Hs ⊆ o := by
    intro v hv
    obtain ⟨vote, hvote, hval, ⟨x, hτ⟩, ⟨H, hH, hr, hRH⟩, hu⟩ := hHs v hv
    have hopp : opposes Φ e.B vote = .ok true := by
      rw [opposes_eq_ok hRoots]
      congr 1
      rw [decide_eq_true_iff]
      refine ⟨H, hH, hr, ?_⟩
      rw [conflicts_comm]
      exact conflicts_of_ancestorEq_conflicts hRH hconf
    exact mem_opponents_of_eq_ok ho hvote hval (not_mem_equivocators_of_unique hu) hτ hopp
  have h1 := Finset.card_le_card hsub
  omega

end GoldilocksCorrectness.Proofs.Routines
