module
public import GoldilocksCorrectness.Proofs.Routines.Lemma28

@[expose] public section

/-!
# Lemma 8b: the confirmation update confirms a block a committee majority votes for early

The proof of `lem8b_update_confirmation_confirms_majority_block`, stated in
`GoldilocksCorrectness/Statements/Routines/ConfirmationStatements.lean`.

## Rendering note

This was made as a COPY of Lemma 8, `lem8_update_confirmation_confirms_majority_block`, with one
change: the hypothesis `hSlot`, every vote of `A.pool (s - 1)` has the slot `s - 1`. Lemma 8, the
version without `hSlot`, carried a named `sorry`;

Why Lemma 8 could not be proved. `goldfish_score` counts a support vote only when its field
`vote.slot` is the slot scored, `s - 1`. `EarlyVoteOnceFor` says that `v`'s vote is in
`A.pool (s - 1)`, early, with head `B`'s root, but not that its field `vote.slot` is `s - 1`, and
nothing in the type `ACState` relates the list `A.gf_votes (s - 1)` to the votes' slot fields. A
counterexample to Lemma 8: `s = 2`, one validator `v`, `Hs = P.committee 1 = {v}`, `Φ.tree` the
genesis block and a child `B` of slot `1`, `Φ.F` the genesis block, `A.pool 1` the one vote of
`v` with head `B`'s root and slot field `7`, stamped `0`, `B` stamped `0`, no lock entry. Every
hypothesis of Lemma 8 holds; the vote is early and late, so the number of voters is `1`, but
every score is `0` (the vote's slot field is not `1`), so the walk stays at the genesis block, the
genesis block is not eligible, and the update saves `none` for slot `1`: the first conjunct of
the conclusion fails.

The change. `hSlot : ∀ vote ∈ A.pool (s - 1), vote.slot = s - 1`. Read aloud: every vote the
node holds for slot `s − 1` names slot `s − 1`. It has the shape of `hCommittee`, and the same
source: the admission `on_goldfish_vote` appends a vote only to `A.gf_votes[vote.slot]`, so every
AC state reached from `ACState.initial` by admissions satisfies it at every slot (not yet proved;
an invariant for phase 2). The callers: the G1 assembly of phase 2, not yet written, which must
supply `hCommittee` from the same admission invariant.

Rejected alternative: the condition on the votes of `Hs` alone (`∀ v ∈ Hs`, its vote's slot is
`s - 1`), which is weaker and also suffices; not chosen because its only source is the same
invariant, stated for the whole pool.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 8b, the confirmation update confirms a block a committee majority votes for early.**
The confirmation update of slot `s`, for the slot `s − 1`, saves `B` as the confirmation of slot
`s − 1`, puts `B` among the fast blocks, adds the lock entry on `B` with the deadline
`C.t_ (s − 1 + C.k) + 5 · C.Δ`, and advances the record of the confirmed tip with `B`, when the
roots of `Φ.tree` name its blocks, `B` is not the genesis block, `Φ.F` is `B` or an ancestor of
`B` with every block between them in `Φ.tree`, every member of `Hs` has exactly one
slot-`(s − 1)` vote in `A`'s pool, early and with head `B`, every vote of the pool has the slot
`s − 1` and a validator of the slot-`(s − 1)` committee, `Hs` outnumbers the rest of that
committee, and no live lock entry conflicts with `B`.

Why: it is Lemmas 25 and 28 with the committee majority in place of the voter bound: the voters
of the pool are members of the committee, so fewer than twice `Hs`, and the committee is at most
twice `Hs`.



The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees;
- `A`: the AC state before the update; `A'`: the AC state after it; `Φ`: the frame;
- `t`: the time of the update; `s`: the slot of the update; `B`: the block confirmed;
- `Hs`: the members of the slot-`(s − 1)` committee voting early for `B`. -/
theorem lem8b_update_confirmation_confirms_majority_block (C : Config) (P : Provisional V)
    (A A' : ACState V) (Φ : Frame V) (t : Time) (s : Slot) (B : Block V) (Hs : Finset V)
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
    -- every vote of `A`'s slot-`(s − 1)` pool has the slot `s − 1` (the one change from Lemma 8)
    (hSlot : ∀ vote ∈ A.pool (s - 1), vote.slot = s - 1)
    -- every vote of `A`'s slot-`(s − 1)` pool is from a member of the slot-`(s − 1)` committee
    (hCommittee : ∀ vote ∈ A.pool (s - 1), vote.val_index ∈ P.committee (s - 1))
    -- the members of the slot-`(s − 1)` committee outside `Hs` are fewer than `Hs`
    (hMajority : (P.committee (s - 1) \ Hs).card < Hs.card)
    -- the block of every lock entry of `A` live at `t` is compatible with `B`
    (hNoVeto : ∀ e ∈ A.lock_entries, is_live Φ t e = true → e.B.compatible B = true)
    -- the confirmation update of slot `s` answers `A'`
    (hUpdate : update_confirmation C P A Φ t s = .ok A') :
    -- then `B` is saved, fast, locked, and the confirmed tip advances with it
    A'.saved_confirmation (s - 1) = some B ∧ B ∈ A'.fast_blocks ∧
      LockEntry.mk B (C.t_ (s - 1 + C.k) + 5 * C.Δ) ∈ A'.lock_entries ∧
      A'.latest_confirmed = advance Φ A.latest_confirmed (some B) :=
  let h25 := lem25_update_confirmation_confirms_voter_majority_block C P A A' Φ t s B Hs hs
    hRoots hBne hF hPathF hHs hSlot (voters_count_lt_of_committee_majority hCommittee hMajority)
    hNoVeto hUpdate
  let h28 := lem28_update_confirmation_fast_locks_voter_majority_block C P A A' Φ t s B Hs hs
    hRoots hBne hF hPathF hHs hSlot (voters_count_lt_of_committee_majority hCommittee hMajority)
    (committee_card_le_of_majority hMajority) hNoVeto hUpdate
  ⟨h25.1, h28.1, h28.2, h25.2⟩

end GoldilocksCorrectness.Proofs.Routines
