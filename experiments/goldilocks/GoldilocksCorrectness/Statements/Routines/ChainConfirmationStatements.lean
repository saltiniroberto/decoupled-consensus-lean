module
public import GoldilocksCorrectness.Proofs.Routines.Lemma77

@[expose] public section

/-!
# The statements about the confirmation update over a chain

The audited statements about the confirmation update `update_confirmation` when the votes of a
voter majority support a block's chain rather than name the block: Lemma 77, the saved
confirmation is that block or a descendant of it, and the kit fact
`saved_confirmation_F_ancestorEq`, the saved confirmation is the frame's finalized block or a
descendant of it. Both are proved in `GoldilocksCorrectness/Proofs/Routines/Lemma77.lean`. Lemma
77's hypothesis on the voters is stated with `EarlySupporterOf`, defined in
`GoldilocksCorrectness/Statements/Executions/SupporterDefs.lean`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 77, the confirmation update over a chain, routine form.** The confirmation the update
of slot `s` saves for the slot `s − 1`, when it saves one, is `B` or a descendant of `B`, when the
roots of `Φ.tree` name its blocks, `Φ.F` is `B` or an ancestor of `B` with every block between them
in `Φ.tree`, every member of `Hs` has exactly one slot-`(s − 1)` vote in `A`'s pool, early, with
its head a block of `Φ.tree` that is `B` or a descendant of `B`, every vote of the pool has the slot
`s − 1`, and fewer than twice `Hs` validators have a vote in the pool.

Why: every early vote is a late vote, so the votes of `Hs` are support votes, each its validator's
only one, and the validators counted are fewer than twice `Hs`. Lemma 1 makes the walk from `Φ.F`
end at `B` or a descendant of `B`; the update saves the walk's end, when it is eligible, or
nothing. This is Lemma 25 with the votes on `B`'s chain in place of votes for `B`, without its
conditions that `B` is not the genesis block and that no live lock conflicts with `B`, which only
the confirmed tip reads.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees;
- `A`: the AC state before the update; `A'`: the AC state after it; `Φ`: the frame;
- `t`: the time of the update; `s`: the slot of the update; `B`: the block whose chain the votes
  support; `Hs`: the validators voting early for `B`'s chain.

Read aloud: when every member of `Hs` has exactly one slot-`(s − 1)` vote in the pool, early, for a
block of `Φ.tree` on `B`'s chain, every vote of the pool has the slot `s − 1`, fewer than twice `Hs`
validators have a vote in it, and `Φ.F` is `B` or an ancestor of `B` with every block between them
in `Φ.tree`, then the confirmation the update of slot `s` saves for slot `s − 1`, when it saves
one, is `B` or a descendant of `B`. -/
theorem lem77_update_confirmation_extends_voter_majority_chain (C : Config) (P : Provisional V)
    (A A' : ACState V) (Φ : Frame V) (t : Time) (s : Slot) (B : Block V) (Hs : Finset V)
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- no two blocks of `Φ.tree` share a root
    (hRoots : RootsNameBlocksIn Φ.tree)
    -- `Φ.F` is `B` or an ancestor of `B`
    (hF : Φ.F.AncestorEq B)
    -- every block from `Φ.F` to `B` is in `Φ.tree`
    (hPathF : ∀ P' : Block V, Φ.F.AncestorEq P' → P'.AncestorEq B → P' ∈ Φ.tree)
    -- each member of `Hs` has exactly one slot-`(s − 1)` vote in `A`'s pool, early, with its head
    -- a block of `Φ.tree` that is `B` or a descendant of `B`
    (hHs : ∀ v ∈ Hs, EarlySupporterOf C A Φ (s - 1) B v)
    -- every vote of `A`'s slot-`(s − 1)` pool has the slot `s − 1`
    (hSlot : ∀ vote ∈ A.pool (s - 1), vote.slot = s - 1)
    -- the validators with a slot-`(s − 1)` vote in `A`'s pool are fewer than twice `Hs`
    (hVoters : voters_count (A.pool (s - 1)) < 2 * Hs.card)
    -- the confirmation update of slot `s` answers `A'`
    (hUpdate : update_confirmation C P A Φ t s = .ok A') :
    -- then the confirmation saved for slot `s − 1`, when there is one, is on `B`'s chain
    ∀ C' : Block V, A'.saved_confirmation (s - 1) = some C' → B.AncestorEq C' :=
  GoldilocksCorrectness.Proofs.Routines.lem77_update_confirmation_extends_voter_majority_chain C P
    A A' Φ t s B Hs hs hRoots hF hPathF hHs hSlot hVoters hUpdate

/-- **The saved confirmation descends from the frame's finalized block.** The confirmation the
update of slot `s` saves for the slot `s − 1`, when it saves one, is `Φ.F` or a descendant of
`Φ.F`.

Why: the saved block is the end of the walk `ghost` from `Φ.F`, which is `Φ.F` or a descendant of
it.

The variables:
- `C`: the configuration; `P`: the provisional parameters;
- `A`: the AC state before the update; `A'`: the AC state after it; `Φ`: the frame;
- `t`: the time of the update; `s`: the slot of the update.

Read aloud: the confirmation the update saves is `Φ.F` or a descendant of it. -/
theorem saved_confirmation_F_ancestorEq (C : Config) (P : Provisional V) (A A' : ACState V)
    (Φ : Frame V) (t : Time) (s : Slot)
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- the confirmation update of slot `s` answers `A'`
    (hUpdate : update_confirmation C P A Φ t s = .ok A') :
    -- then the confirmation saved for slot `s − 1`, when there is one, descends from `Φ.F`
    ∀ C' : Block V, A'.saved_confirmation (s - 1) = some C' → Φ.F.AncestorEq C' :=
  GoldilocksCorrectness.Proofs.Routines.saved_confirmation_F_ancestorEq C P A A' Φ t s hs hUpdate

end GoldilocksCorrectness.Statements.Routines
