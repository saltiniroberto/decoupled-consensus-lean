module
public import GoldilocksCorrectness.Proofs.Routines.Lemma8b
public import GoldilocksCorrectness.Proofs.Routines.Lemma25
public import GoldilocksCorrectness.Proofs.Routines.Lemma28
public import GoldilocksCorrectness.Proofs.Routines.Lemma30
public import GoldilocksCorrectness.Proofs.Routines.Lemma35
public import GoldilocksCorrectness.Proofs.Routines.Lemma36
public import GoldilocksCorrectness.Proofs.Routines.Lemma37
public import Goldilocks.AC.Interface
public import GoldilocksCorrectness.Proofs.Routines.ConfirmedTip
public import GoldilocksCorrectness.Proofs.Routines.Lemma77Compat
public import GoldilocksCorrectness.Proofs.Routines.PeriodLocks

@[expose] public section

/-!
# The statements about the confirmation update

The audited statements about the confirmation update `update_confirmation`: Lemma 8b, under a
committee majority, Lemmas 25 and 28, under a voter majority, Lemma 30, two updates that save
blocks save compatible ones, Lemma 35, the lock entry an update adds, Lemma 36, the early
supporters of a block on the confirmed path, and Lemma 37, what the slow test reads, each proved
in its own file under
`GoldilocksCorrectness/Proofs/Routines/`. Lemma 36's conclusion is stated with
`EarlySupporterOf`, defined in `GoldilocksCorrectness/Statements/Executions/SupporterDefs.lean`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks

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

The statement includes `hSlot`, that every vote of the slot-`(s − 1)` pool has the slot field
`s − 1`, because without it a vote filed under slot `s − 1` with another slot field changes the
counts: `goldfish_score` counts a vote only when its slot field is the slot scored, while the
number of voters counts it. the name keeps its `b` because the lemma numbers are append-only.



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
  GoldilocksCorrectness.Proofs.Routines.lem8b_update_confirmation_confirms_majority_block C P A A'
    Φ t s B Hs hs hRoots hBne hF hPathF hHs hSlot hCommittee hMajority hNoVeto hUpdate

/-- **Lemma 25, the confirmation update confirms a block a voter majority votes for early.** The
confirmation update of slot `s`, for the slot `s − 1`, saves `B` as the confirmation of slot
`s − 1` and advances the record of the confirmed tip with `B`, when the roots of `Φ.tree` name its
blocks, `B` is not the genesis block, `Φ.F` is `B` or an ancestor of `B` with every block between
them in `Φ.tree`, every member of `Hs` has exactly one slot-`(s − 1)` vote in `A`'s pool, early and
with head `B`, every vote of the pool has the slot `s − 1`, fewer than twice `Hs` validators have
a vote in the pool, and no live lock entry conflicts with `B`.

Why: every early vote is a late vote, so the votes of `Hs` are support votes, and the late voters
are voters of the pool, fewer than twice `Hs`. Lemma 4 makes the walk from `Φ.F` end at `B`, and
`B`'s score is at least `|Hs|`, so `B` is eligible; no live entry vetoes `B`. The committee size
does not enter: only the fast test reads it, and Lemma 28 adds the half condition for the fast
block and the lock.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees;
- `A`: the AC state before the update; `A'`: the AC state after it; `Φ`: the frame;
- `t`: the time of the update; `s`: the slot of the update; `B`: the block confirmed;
- `Hs`: the validators voting early for `B`.

Read aloud: when fewer than twice `Hs` validators have a slot-`(s − 1)` vote in the pool, each
member of `Hs` voting once, early, for `B`, and no live lock conflicts with `B`, the update saves
`B` and advances the confirmed tip with `B`. -/
theorem lem25_update_confirmation_confirms_voter_majority_block (C : Config) (P : Provisional V)
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
    -- every vote of `A`'s slot-`(s − 1)` pool has the slot `s − 1`
    (hSlot : ∀ vote ∈ A.pool (s - 1), vote.slot = s - 1)
    -- the validators with a slot-`(s − 1)` vote in `A`'s pool are fewer than twice `Hs`
    (hVoters : voters_count (A.pool (s - 1)) < 2 * Hs.card)
    -- the block of every lock entry of `A` live at `t` is compatible with `B`
    (hNoVeto : ∀ e ∈ A.lock_entries, is_live Φ t e = true → e.B.compatible B = true)
    -- the confirmation update of slot `s` answers `A'`
    (hUpdate : update_confirmation C P A Φ t s = .ok A') :
    -- then `B` is saved, and the confirmed tip advances with it
    A'.saved_confirmation (s - 1) = some B ∧
      A'.latest_confirmed = advance Φ A.latest_confirmed (some B) :=
  GoldilocksCorrectness.Proofs.Routines.lem25_update_confirmation_confirms_voter_majority_block C
    P A A' Φ t s B Hs hs hRoots hBne hF hPathF hHs hSlot hVoters hNoVeto hUpdate

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
  GoldilocksCorrectness.Proofs.Routines.lem28_update_confirmation_fast_locks_voter_majority_block
    C P A A' Φ t s B Hs hs hRoots hBne hF hPathF hHs hSlot hVoters hHalf hNoVeto hUpdate

/-- **Lemma 30, two confirmation updates save compatible blocks.** Two confirmation updates of
slot `s`, for the slot `s − 1`, on the AC states `A₁`, `A₂` and the frames `Φ₁`, `Φ₂`, that save
`C₁` and `C₂` as the confirmation of slot `s − 1`, save compatible blocks, when no two blocks of
the two frame trees share a root, every vote of either slot-`(s − 1)` pool is stamped strictly
before the late cutoff `C.t_ (s − 1) + 6 · C.Δ`, and every vote of either pool that resolves
strictly before `C.t_ (s − 1) + 2 · C.Δ` is in the other pool, or the other pool holds two
distinct votes of its validator.

Why: a saved block passed the eligibility test, fewer late voters than twice its score, and the
score counts the supporters only, since no validator has two support votes. If `C₁` and `C₂`
conflicted, no validator would support both, and the supporters of either have late votes at both
nodes, so each supporter set would outnumber the other.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees;
- `A₁`, `A₂`: the AC states before the two updates; `A₁'`, `A₂'`: the AC states after them;
- `Φ₁`, `Φ₂`: the two frames; `t₁`, `t₂`: the times of the two updates;
- `s`: the slot of the updates; `C₁`, `C₂`: the blocks saved.

Read aloud: two confirmation updates of slot `s` that save `C₁` and `C₂` for slot `s − 1` save
blocks on one chain, when a root names one block across the two trees, every pool vote is late,
and every early vote of either pool is in the other pool unless that pool holds two votes of its
validator. -/
theorem lem30_saved_confirmations_compatible (C : Config) (P : Provisional V)
    (A₁ A₁' A₂ A₂' : ACState V) (Φ₁ Φ₂ : Frame V) (t₁ t₂ : Time) (s : Slot) (C₁ C₂ : Block V)
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- no two blocks of the two frame trees share a root
    (hRoots : RootsNameBlocksIn (Φ₁.tree ∪ Φ₂.tree))
    -- every vote of `A₁`'s slot-`(s − 1)` pool is stamped strictly before the late cutoff
    (hLate₁ : ∀ vote ∈ A₁.pool (s - 1), ∃ τ : Stamp, A₁.timestamp_vote vote = some τ ∧
      τ < ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp))
    -- every vote of `A₂`'s slot-`(s − 1)` pool is stamped strictly before the late cutoff
    (hLate₂ : ∀ vote ∈ A₂.pool (s - 1), ∃ τ : Stamp, A₂.timestamp_vote vote = some τ ∧
      τ < ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp))
    -- every vote of `A₁`'s pool that resolves strictly before `C.t_ (s − 1) + 2 · C.Δ` is in
    -- `A₂`'s pool, or `A₂`'s pool holds two distinct votes of its validator
    (hReach₁₂ : ∀ vote ∈ A₁.pool (s - 1),
      (∃ y : Stamp, A₁.tau Φ₁ vote = .ok (some y) ∧
        occurrenceBefore (some y) (C.t_ (s - 1) + 2 * C.Δ) = true) →
      vote ∈ A₂.pool (s - 1) ∨
        ∃ u₁ ∈ A₂.pool (s - 1), ∃ u₂ ∈ A₂.pool (s - 1),
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index)
    -- every vote of `A₂`'s pool that resolves strictly before `C.t_ (s − 1) + 2 · C.Δ` is in
    -- `A₁`'s pool, or `A₁`'s pool holds two distinct votes of its validator
    (hReach₂₁ : ∀ vote ∈ A₂.pool (s - 1),
      (∃ y : Stamp, A₂.tau Φ₂ vote = .ok (some y) ∧
        occurrenceBefore (some y) (C.t_ (s - 1) + 2 * C.Δ) = true) →
      vote ∈ A₁.pool (s - 1) ∨
        ∃ u₁ ∈ A₁.pool (s - 1), ∃ u₂ ∈ A₁.pool (s - 1),
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index)
    -- the update on `A₁`, `Φ₁` answers `A₁'` and saves `C₁`
    (hUpdate₁ : update_confirmation C P A₁ Φ₁ t₁ s = .ok A₁')
    (hSaved₁ : A₁'.saved_confirmation (s - 1) = some C₁)
    -- the update on `A₂`, `Φ₂` answers `A₂'` and saves `C₂`
    (hUpdate₂ : update_confirmation C P A₂ Φ₂ t₂ s = .ok A₂')
    (hSaved₂ : A₂'.saved_confirmation (s - 1) = some C₂) :
    -- then `C₁` and `C₂` are compatible
    C₁.compatible C₂ = true :=
  GoldilocksCorrectness.Proofs.Routines.lem30_saved_confirmations_compatible C P A₁ A₁' A₂ A₂'
    Φ₁ Φ₂ t₁ t₂ s C₁ C₂ hs hRoots hLate₁ hLate₂ hReach₁₂ hReach₂₁ hUpdate₁ hSaved₁ hUpdate₂ hSaved₂

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
        (e.B ∈ A'.fast_blocks ∨ slow_test C A Φ (s - 1) e.B = true)) :=
  GoldilocksCorrectness.Proofs.Routines.lem35_update_confirmation_lock_entries C P A A' Φ t s
    hUpdate

open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf) in
/-- **Lemma 36, a confirmed block's ancestors have early supporters.** When the confirmation
update of slot `s` saves `C'` as the confirmation of slot `s − 1`, every block `L` that is `C'` or
an ancestor of `C'` has a set `Sup` of validators such that each member of `Sup` has exactly one
slot-`(s − 1)` vote in `A`'s pool, resolving strictly before `C.t_ (s − 1) + 2 · C.Δ`, whose head
is a block of `Φ.tree` that is `L` or a descendant of `L`; the validators with a slot-`(s − 1)`
vote in the pool are fewer than twice `Sup`; and when `L` is a fast block of the answer, the
slot-`(s − 1)` committee is at most twice `Sup`. This holds when no two blocks of `Φ.tree` share a
root and every vote of the slot-`(s − 1)` pool is stamped strictly before the late cutoff
`C.t_ (s − 1) + 6 · C.Δ`.

Why: `Sup` is the set of supporters of `L` among the update's support votes. `C'` passed the
eligibility test, fewer late voters than twice its score; no validator has two support votes, so
the score is the number of `C'`'s supporters, and every supporter of `C'` supports `L`. Every
vote of the pool is late, so the late voters are the voters of the pool. A support vote is early
and its validator has no second late vote, hence no second vote in the pool. A fast block passed
the fast test, the committee at most twice its score, and the score of `L` is the size of `Sup`.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees;
- `A`: the AC state before the update; `A'`: the AC state after it; `Φ`: the frame;
- `t`: the time of the update; `s`: the slot of the update;
- `C'`: the confirmation saved; `L`: the block, `C'` or an ancestor of it.

Read aloud: when the update saves `C'` and `L` is `C'` or an ancestor of it, some set `Sup` of
validators each has exactly one slot-`(s − 1)` vote in the pool, resolving strictly before
`C.t_ (s − 1) + 2 · C.Δ`, heading a block of `Φ.tree` on `L`'s chain, and the pool's voters are
fewer than twice `Sup`; and when `L` is a fast block of the answer, the committee is at most twice
`Sup`. -/
theorem lem36_confirmed_ancestor_early_supporters (C : Config) (P : Provisional V)
    (A A' : ACState V) (Φ : Frame V) (t : Time) (s : Slot) (C' L : Block V)
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- no two blocks of `Φ.tree` share a root
    (hRoots : RootsNameBlocksIn Φ.tree)
    -- every vote of the slot-`(s − 1)` pool is stamped strictly before the late cutoff
    (hLate : ∀ vote ∈ A.pool (s - 1), ∃ τ : Stamp, A.timestamp_vote vote = some τ ∧
      τ < ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp))
    -- the update answers `A'` and saves `C'`
    (hUpdate : update_confirmation C P A Φ t s = .ok A')
    (hSaved : A'.saved_confirmation (s - 1) = some C')
    -- `L` is `C'` or an ancestor of `C'`
    (hLC : L.AncestorEq C') :
    ∃ Sup : Finset V, (∀ u ∈ Sup, EarlySupporterOf C A Φ (s - 1) L u) ∧
      voters_count (A.pool (s - 1)) < 2 * Sup.card ∧
      (L ∈ A'.fast_blocks → (P.committee (s - 1)).card ≤ 2 * Sup.card) :=
  GoldilocksCorrectness.Proofs.Routines.lem36_confirmed_ancestor_early_supporters C P A A' Φ t s
    C' L hs hRoots hLate hUpdate hSaved hLC

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
      ∃ C' : Block V, A.saved_confirmation s' = some C' ∧ C' ∈ Φ.tree ∧ L.AncestorEq C' :=
  GoldilocksCorrectness.Proofs.Routines.lem37_slow_test_saved_confirmations C A Φ s L hSlow

end GoldilocksCorrectness.Statements.Routines

namespace GoldilocksCorrectness.Statements.Routines

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 77c, the confirmation update over a majority of votes compatible with `B`, routine
form.** The confirmation the update of slot `s ≥ 1` saves for the slot `s − 1`, when it saves one,
is compatible with `B`, when the roots of `Φ.tree` name its blocks, every member `u` of `Hs` has
in `A`'s pool of slot `s − 1` a vote stamped strictly before the late cutoff
`C.t_ (s − 1) + 6 · C.Δ`, its only vote of that slot in the pool, every block of `Φ.tree` whose
root is that vote's head being compatible with `B`, and fewer than twice `Hs` validators have a
vote in the pool.

Why: the update saves the end of its walk only when it passes the test
`voters_count late < 2 · score`. A block conflicting with `B` is supported by no member of `Hs`
(a member's one vote names a block compatible with `B`, and supports only that block's
ancestors), and no member is an equivocator; the members are late voters, so the equivocators,
the supporters of that block and `Hs` are disjoint sets of late voters, and twice the score is at
most twice the late voters less `Hs`, which is less than the late voters. Lemma 77 is the same
with the votes on `B`'s chain and `Φ.F ⪯ B`, concluding `B ⪯ C'`.


Lemma 77's `hPathF` dropped as the brief says, and its `hF` (`Φ.F ⪯ B`) and `hSlot` (every vote
of the pool has the slot `s − 1`) deleted as unread.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees;
- `A`: the AC state before the update; `A'`: the AC state after it; `Φ`: the frame;
- `t`: the time of the update; `s`: the slot of the update; `B`: the block; `Hs`: the
  validators whose votes are compatible with `B`.

Read aloud: when every member of `Hs` has exactly one slot-`(s − 1)` vote in the pool, stamped
before the late cutoff, for a block compatible with `B`, and fewer than twice `Hs` validators have
a vote in the pool, then the confirmation the update of slot `s` saves for slot `s − 1`, when it
saves one, does not conflict with `B`. -/
theorem lem77c_update_confirmation_compatible_of_majority (C : Config) (P : Provisional V)
    (A A' : ACState V) (Φ : Frame V) (t : Time) (s : Slot) (B : Block V) (Hs : Finset V)
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- no two blocks of `Φ.tree` share a root
    (hRoots : RootsNameBlocksIn Φ.tree)
    -- each member of `Hs` has exactly one slot-`(s − 1)` vote in `A`'s pool, stamped before the
    -- late cutoff, and every block of `Φ.tree` named by its head is compatible with `B`
    (hHs : ∀ u ∈ Hs, ∃ vote ∈ A.pool (s - 1), vote.val_index = u ∧
      (∃ τ : Stamp, A.timestamp_vote vote = some τ ∧
        τ < ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp)) ∧
      (∀ vote' ∈ A.pool (s - 1), vote'.val_index = u → vote' = vote) ∧
      ∀ D ∈ Φ.tree, D.root = vote.head → D.compatible B = true)
    -- the validators with a slot-`(s − 1)` vote in `A`'s pool are fewer than twice `Hs`
    (hVoters : voters_count (A.pool (s - 1)) < 2 * Hs.card)
    -- the confirmation update of slot `s` answers `A'`
    (hUpdate : update_confirmation C P A Φ t s = .ok A') :
    -- then the confirmation saved for slot `s − 1`, when there is one, is compatible with `B`
    ∀ C' : Block V, A'.saved_confirmation (s - 1) = some C' → C'.compatible B = true :=
  GoldilocksCorrectness.Proofs.Routines.lem77c_update_confirmation_compatible_of_majority C P A A'
    Φ t s B Hs hs hRoots hHs hVoters hUpdate

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- **The record after `advance`.** `advance Φ old C?` is the old record `old`, or `C?` is some
block `C` and `advance Φ old C?` is `C`.

The variables:
- `Φ`: the frame; `old`: the record of the confirmed tip; `C?`: the confirmation.

Read aloud: the record after an update is the old record or the confirmation saved. -/
theorem advance_cases (Φ : Frame V) (old : Block V) (C? : Option (Block V)) :
    advance Φ old C? = old ∨ ∃ C : Block V, C? = some C ∧ advance Φ old C? = C :=
  GoldilocksCorrectness.Proofs.Routines.advance_cases Φ old C?

omit [Fintype V] [RootOrder] in
/-- **The confirmed tip's two cases.** The confirmed tip `ac_confirmed A Φ` is the record
`A.latest_confirmed` when the record is in `Φ.tree`, and `Φ.F` when it is not.

The variables:
- `A`: the AC state; `Φ`: the frame.

Read aloud: the confirmed tip is the record when the record is in the frame's tree, the
finalized block otherwise. -/
theorem ac_confirmed_cases (A : ACState V) (Φ : Frame V) :
    (A.latest_confirmed ∈ Φ.tree ∧ ac_confirmed A Φ = A.latest_confirmed) ∨
      (A.latest_confirmed ∉ Φ.tree ∧ ac_confirmed A Φ = Φ.F) :=
  GoldilocksCorrectness.Proofs.Routines.ac_confirmed_cases A Φ

/-- **The update writes the record once.** The confirmation update of a slot `s ≥ 1` that answers
`A'` keeps the record of the confirmed tip, or writes as the record the confirmation of slot
`s − 1` it saves, which no live lock of its input `A` vetoes.

Why: the update writes the record once, in its fourth step, under the tests that a confirmation
was saved and that no live lock of the input's lock entries vetoes it, as `advance` of the old
record with that confirmation, which is the old record or the confirmation.

The variables:
- `C`: the parameters; `P`: the values; `A`, `A'`: the AC state before and after the update;
- `Φ`: the frame; `t`: the time; `s`: the slot of the update.

Read aloud: the update keeps the record, or writes the confirmation it saves, which no live lock
vetoes. -/
theorem update_confirmation_latest_confirmed (C : Config) (P : Provisional V)
    (A A' : ACState V) (Φ : Frame V) (t : Time) (s : Slot)
    -- the update is of a slot after slot `0`
    (hs : s ≠ 0)
    -- the update answers `A'`
    (hUpdate : update_confirmation C P A Φ t s = .ok A') :
    A'.latest_confirmed = A.latest_confirmed ∨
      (A'.saved_confirmation (s - 1) = some A'.latest_confirmed ∧
        live_lock_vetoes A Φ t A'.latest_confirmed = false) :=
  GoldilocksCorrectness.Proofs.Routines.update_confirmation_latest_confirmed C P A A' Φ t s hs
    hUpdate

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Routine fact: the revocation keeps a live entry fewer than half of the committee oppose.**
For the revocation of slot `s' ≥ 1`, a live entry `e` of `A` on a block other than the genesis
block whose opponents among the votes of slot `s' − 1`, counted twice, are fewer than the
committee of `s' − 1`, is an entry of the answer. Section 3.2's "the entry is unchanged".

Why: `e`'s block is a candidate of `moved_entry`, and every candidate is an ancestor of it or it,
so it is the deepest candidate, and the entry moves to itself.

The variables:
- `P`: the values; `A`, `A'`: the AC state before and after the revocation; `Φ`: the frame;
  `t`: the time; `s'`: the slot of the revocation; `e`: the entry;
- `hs'`: the slot is not `0`; `hrev`: the revocation answers `A'`; `he`, `hlive`: `e` is an entry
  of `A`, live at `t`; `hgen`: its block is not the genesis block; `hopp`: its block's opponents,
  counted twice, are fewer than the committee of slot `s' − 1`.

Read aloud: the lock on `B` survives the revocation when fewer than half of the committee voted
against `B`. -/
theorem revoke_locks_keeps_entry (P : Provisional V) (A A' : ACState V) (Φ : Frame V) (t : Time)
    (s' : Slot) (e : LockEntry V)
    (hs' : s' ≠ 0) (hrev : revoke_locks P A Φ t s' = .ok A')
    (he : e ∈ A.lock_entries) (hlive : is_live Φ t e = true) (hgen : e.B ≠ Block.genesis)
    (hopp : ∀ opp : Finset V,
      opponents A Φ (A.pool (s' - 1)) (equivocators (A.pool (s' - 1))) e.B = .ok opp →
      2 * |opp| < |P.committee (s' - 1)|) :
    e ∈ A'.lock_entries :=
  GoldilocksCorrectness.Proofs.Routines.revoke_locks_keeps_entry P A A' Φ t s' e hs' hrev he hlive
    hgen hopp

/-- **Routine fact: the update under a live lock on `B`, with the record in the frame's tree.**
When the update of slot `s' ≥ 1` answers `A'` from an input `A` holding a live lock entry on `B`,
with the record `B` or a descendant of `B` and a block of the frame's tree: the record stays `B`
or a descendant of `B`; every fast block of `A'` is compatible with `B`; every lock entry of `A'`
is one of `A` or is on a block compatible with `B`; and the confirmation saved, when there is
one, is compatible with `B` or is vetoed by a live lock of `A`. Section 3.2's update step.

Why: a saved confirmation `H` that no live lock vetoes is compatible with `B`, since the entry on
`B` does not veto it; the fast blocks and a new lock are ancestors of `H` or `H`. When `H` is an
ancestor of `B`, `advance` keeps the record because the record is in the frame's tree.

The variables:
- `C`, `P`: the parameters and the values; `A`, `A'`: the AC state before and after the update;
  `Φ`: the frame; `t`: the time; `s'`: the slot of the update; `B`: the locked block; `d`: the
  lock's deadline;
- `hs'`: the slot is not `0`; `hUpdate`: the update answers `A'`; `hlock`, `hlive`: `A` holds the
  entry `⟨B, d⟩`, live at `t`; `hin`: the record is a block of the frame's tree; `hold`: the
  record is `B` or a descendant of `B`.

Read aloud: whatever the update was shown, with the lock on `B` live and the record on `B`'s
chain in the frame's tree, it cannot record, fast-confirm or lock anything off `B`'s chain. -/
theorem update_confirmation_with_live_lock_of_mem (C : Config) (P : Provisional V)
    (A A' : ACState V) (Φ : Frame V) (t : Time) (s' : Slot) (B : Block V) (d : Time)
    (hs' : s' ≠ 0) (hUpdate : update_confirmation C P A Φ t s' = .ok A')
    (hlock : LockEntry.mk B d ∈ A.lock_entries) (hlive : is_live Φ t (LockEntry.mk B d) = true)
    (hin : A.latest_confirmed ∈ Φ.tree) (hold : B.AncestorEq A.latest_confirmed) :
    B.AncestorEq A'.latest_confirmed ∧
    (∀ D ∈ A'.fast_blocks, D.compatible B = true) ∧
    (∀ e ∈ A'.lock_entries, e ∈ A.lock_entries ∨ e.B.compatible B = true) ∧
    (∀ C' : Block V, A'.saved_confirmation (s' - 1) = some C' →
      C'.compatible B = true ∨ live_lock_vetoes A Φ t C' = true) :=
  GoldilocksCorrectness.Proofs.Routines.update_confirmation_with_live_lock_of_mem C P A A' Φ t s'
    B d hs' hUpdate hlock hlive hin hold

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] in
/-- **Routine fact: the block an entry is moved to has fewer than half of the committee opposing
it.** When `moved_entry P A Φ votes equivocators s' e` answers the entry `e'`, the opponents of
`e'.B` among `votes` (outside `equivocators`) are computed and, counted twice, are fewer than the
committee of slot `s' − 1`; `e'.B` is a block of `Φ.tree`, `e.B` or an ancestor of `e.B`; and `e'`
keeps `e`'s deadline.

Why: `moved_entry` answers the deepest of its candidates, the blocks of `Φ.tree` other than the
genesis block that are `e.B` or an ancestor of it and whose opponents, counted twice, are fewer than
the committee; the answer keeps the deadline.


Against the brief's template, the opponents' bound is the existential "the opponents are computed,
and counted twice are fewer than the committee", which gives the template's universal form, since
`opponents` is a function; the existential is what `revoked_entries_compatible_of_majority` reads.

The variables:
- `P`: the values, with the committees; `A`: the AC state; `Φ`: the frame; `votes`,
  `equivocators`: the votes counted and the validators counted out; `s'`: the slot of the
  revocation; `e`: the entry moved; `e'`: the entry answered.

Read aloud: the block an entry is moved to has fewer than half of the committee opposing it. -/
theorem moved_entry_opponents_lt {P : Provisional V} {A : ACState V} {Φ : Frame V}
    {votes : Finset (GoldfishVote V)} {equivocators : Finset V} {s' : Slot}
    {e e' : LockEntry V}
    -- `moved_entry` moves `e` to `e'`
    (h : moved_entry P A Φ votes equivocators s' e = .ok (some e')) :
    (∃ opp : Finset V, opponents A Φ votes equivocators e'.B = .ok opp ∧
      2 * |opp| < |P.committee (s' - 1)|) ∧
    e'.B ∈ Φ.tree ∧ e'.B.AncestorEq e.B ∧ e'.d = e.d :=
  GoldilocksCorrectness.Proofs.Routines.moved_entry_opponents_lt h

end

end GoldilocksCorrectness.Statements.Routines
