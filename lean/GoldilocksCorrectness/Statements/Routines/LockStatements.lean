module
public import GoldilocksCorrectness.Proofs.Routines.Lemma5
public import GoldilocksCorrectness.Proofs.Routines.Lemma6
public import GoldilocksCorrectness.Proofs.Routines.Lemma7
public import GoldilocksCorrectness.Proofs.Routines.Lemma38

@[expose] public section

/-!
# The statements about the revocation of the locks and the anchor

The audited statements about the revocation `revoke_locks` (Lemma 5, and Lemma 38, the entries it
leaves are input entries moved to ancestors), the anchor `get_anchor` and the start of a walk in
the viable tree, each proved in its own file under `GoldilocksCorrectness/Proofs/Routines/`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks

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
    ∀ e ∈ A'.lock_entries, e.B ∈ Φ.tree ∧ e.B.compatible R = true :=
  GoldilocksCorrectness.Proofs.Routines.lem5_revoke_locks_entries_compatible P A A' Φ t s R Hs hs
    hRoots hHs hHalf hRevoke

omit [Fintype V] in
/-- **Lemma 6, the anchor is compatible with a block every live lock is compatible with.** The
anchor `get_anchor A Φ t` is compatible with `R`, when the block of every lock entry of `A` live
at `t` is compatible with `R`, and `Φ.fc_root` is compatible with `R`.

Why: the anchor is either `Φ.fc_root`, or a locked block, which is an ancestor of the block of a
live entry, or that block; an ancestor of a block compatible with `R` is compatible with `R`.

The variables:
- `A`: the AC state; `Φ`: the frame; `t`: the time the anchor is read at;
- `R`: the block. -/
theorem lem6_get_anchor_compatible (A : ACState V) (Φ : Frame V) (t : Time) (R : Block V)
    -- the block of every lock entry of `A` live at `t` is compatible with `R`
    (hEntries : ∀ e ∈ A.lock_entries, is_live Φ t e = true → e.B.compatible R = true)
    -- `Φ.fc_root` is compatible with `R`
    (hRoot : Φ.fc_root.compatible R = true) :
    -- then the anchor is compatible with `R`
    (get_anchor A Φ t).compatible R = true :=
  GoldilocksCorrectness.Proofs.Routines.lem6_get_anchor_compatible A Φ t R hEntries hRoot

omit [Fintype V] [RootOrder] in
/-- **Lemma 7, a start compatible with a block starts towards it in the viable tree.** A start
`X` compatible with `R` starts towards `R` in the viable tree of `tree`, when `Φ.fc_root` is an
ancestor of `X` or `X`, every block after `X` up to `R` is in `tree`, and `tree` holds a viable
head `W` of the frame that is `R` or a descendant of `R`.

Why: when `R` is `X` or an ancestor of `X`, that is the first case of `StartsTowards`. Otherwise
`X` is an ancestor of `R`, and every block `P` after `X` up to `R` is in `tree`, has `Φ.fc_root`
as an ancestor through `X`, and is an ancestor of `W` through `R`: it is in the viable tree.

The variables:
- `Φ`: the frame; `tree`: the tree whose viable tree is walked;
- `X`: the start; `R`: the block the walk is to reach; `W`: the viable head. -/
theorem lem7_startsTowards_of_compatible (Φ : Frame V) (tree : Finset (Block V))
    (X R W : Block V)
    -- `X` is compatible with `R`
    (hXR : X.compatible R = true)
    -- `Φ.fc_root` is `X` or an ancestor of `X`
    (hRootX : Φ.fc_root.AncestorEq X)
    -- every block after `X` up to `R`, `R` included, is in `tree`
    (hPath : ∀ P : Block V, X.AncestorEq P → P ≠ X → P.AncestorEq R → P ∈ tree)
    -- `W` is a block of `tree` and a viable head of the frame
    (hW : W ∈ tree ∧ W ∈ Φ.viable_heads)
    -- `W` is `R` or a descendant of `R`
    (hRW : R.AncestorEq W) :
    -- then `X` starts towards `R` in the viable tree of `tree`
    StartsTowards X R (viable_tree Φ tree) :=
  GoldilocksCorrectness.Proofs.Routines.lem7_startsTowards_of_compatible Φ tree X R W hXR hRootX
    hPath hW hRW

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
      e'.B.AncestorEq e.B ∧ e'.B ∈ Φ.tree :=
  GoldilocksCorrectness.Proofs.Routines.lem38_revoke_locks_entries_moved P A A' Φ t s hs hRevoke

end GoldilocksCorrectness.Statements.Routines
