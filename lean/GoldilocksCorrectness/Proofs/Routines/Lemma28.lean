module
public import GoldilocksCorrectness.Proofs.Routines.Lemma25

@[expose] public section

/-!
# Lemma 28: the confirmation update makes a voter-majority block fast and locks it

The proof of `lem28_update_confirmation_fast_locks_voter_majority_block`, stated in
`GoldilocksCorrectness/Statements/Routines/ConfirmationStatements.lean`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 28, the confirmation update makes a voter-majority block fast and locks it.** The
confirmation update of slot `s`, for the slot `s − 1`, puts `B` among the fast blocks and adds the
lock entry on `B` with the deadline `C.t_ (s − 1 + C.k) + 5 · C.Δ`, under the hypotheses of
Lemma 25 (`B` not the genesis block, `Φ.F` an ancestor of `B` or `B`, the members of `Hs` voting
once, early, for `B`, every vote of the pool with the slot `s − 1`, fewer than twice `Hs` voters in
the pool, no live lock conflicting with `B`) and when the slot-`(s − 1)` committee is at most twice
`Hs`.

Why: by Lemma 25's argument `B` is confirmed with a score at least `|Hs|`; the fast test asks that
the committee be at most twice the score, which the half condition gives, so `B` is fast and is the
deepest block of its path passing a lock test.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees;
- `A`: the AC state before the update; `A'`: the AC state after it; `Φ`: the frame;
- `t`: the time of the update; `s`: the slot of the update; `B`: the block confirmed;
- `Hs`: the validators voting early for `B`.

Read aloud: when fewer than twice `Hs` validators have a slot-`(s − 1)` vote in the pool, each
member of `Hs` voting once, early, for `B`, no live lock conflicts with `B`, and the committee is at
most twice `Hs`, the update makes `B` a fast block and adds the lock entry on `B`. -/
theorem lem28_update_confirmation_fast_locks_voter_majority_block (C : Config)
    (P : Provisional V) (A A' : ACState V) (Φ : Frame V) (t : Time) (s : Slot) (B : Block V)
    (Hs : Finset V)
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- no two blocks of `Φ.tree` share a root
    (hRoots : RootsNameBlocksIn Φ.tree)
    -- `B` is not the genesis block
    (hBne : B ≠ Block.genesis)
    -- `Φ.F` is `B` or an ancestor of `B`
    (hF : Φ.F.AncestorEq B)
    -- every block from `Φ.F` to `B` is in `Φ.tree`
    (hPathF : ∀ P' : Block V, Φ.F.AncestorEq P' → P'.AncestorEq B → P' ∈ Φ.tree)
    -- each member of `Hs` has exactly one slot-`(s − 1)` vote in `A`'s pool, early, with head `B`
    (hHs : ∀ v ∈ Hs, EarlyVoteOnceFor C A Φ (s - 1) B v)
    -- every vote of `A`'s slot-`(s − 1)` pool has the slot `s − 1`
    (hSlot : ∀ vote ∈ A.pool (s - 1), vote.slot = s - 1)
    -- the validators with a slot-`(s − 1)` vote in `A`'s pool are fewer than twice `Hs`
    (hVoters : voters_count (A.pool (s - 1)) < 2 * Hs.card)
    -- the slot-`(s − 1)` committee is at most twice `Hs`
    (hHalf : (P.committee (s - 1)).card ≤ 2 * Hs.card)
    -- the block of every lock entry of `A` live at `t` is compatible with `B`
    (hNoVeto : ∀ e ∈ A.lock_entries, is_live Φ t e = true → e.B.compatible B = true)
    -- the confirmation update of slot `s` answers `A'`
    (hUpdate : update_confirmation C P A Φ t s = .ok A') :
    -- then `B` is fast and locked
    B ∈ A'.fast_blocks ∧ LockEntry.mk B (C.t_ (s - 1 + C.k) + 5 * C.Δ) ∈ A'.lock_entries :=
  (update_confirmation_of_voter_majority C P A A' Φ t s B Hs hs hRoots hBne hF hPathF hHs hSlot
    hVoters hNoVeto hUpdate).2.2 hHalf

end GoldilocksCorrectness.Proofs.Routines
