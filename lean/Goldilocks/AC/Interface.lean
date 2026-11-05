module
public import Goldilocks.AC.Confirmation

@[expose] public section

/-!
# The interface of the available chain

The routines the node calls on the available chain: on each tick, on a Goldfish vote, on a block
the finality gadget accepted, to build a proposal, to give the finality gadget a source and a
head, and to read the confirmed tip.

This file declares, in the namespace `Goldilocks`:

- `ac_on_tick`, `ac_on_message` and `ac_on_block`;
- `Proposal V` and `ac_proposal`, what a proposal of the available chain holds;
- `FGInput V` and `ac_to_fg`, the source and the head the available chain gives the finality
  gadget;
- `ac_confirmed`, the confirmed tip.

This file holds definitions only.
-/

open scoped DC

open DC (DRE)

namespace Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The tick and the receipts -/

/-- The tick of the available chain at the time `t`, in the slot `s := C.slot t`, for the
validator `v`:

1. the lock entries whose deadline is at most `t` are deleted;
2. at the vote time `C.t_ s + C.Δ`, when `awake_for_vote` holds, the locks are revoked against the
   votes of slot `s − 1` (`revoke_locks`), and then the Goldfish vote duty runs (`goldfish_vote`);
3. at the support cutoff `C.t_ s + 2 * C.Δ`, when `awake_for_confirmation` holds, the
   confirmation update of slot `s − 1` runs (`update_confirmation`).

`awake_for_vote` and `awake_for_confirmation` are the node's wake rule tests for those two times:
the node computes them from the time since which it has been awake, which the available chain
does not read.

Raises when one of the three routines does. -/
@[no_expose] def ac_on_tick (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V) (t : Time) (v : V)
    (awake_for_vote awake_for_confirmation : Bool) : DREB V (ACState V) := do
  let mut A := A
  let s := C.slot t
  A.lock_entries ← {e ∈ A.lock_entries | t < e.d}
  if t = C.t_ s + C.Δ && awake_for_vote then
    A ⇐ revoke_locks P A Φ t s
    A ⇐ goldfish_vote C P A Φ t v
  if t = C.t_ s + 2 * C.Δ && awake_for_confirmation then
    A ⇐ update_confirmation C P A Φ t s
  return A

/-- The receipt of the Goldfish vote `vote` at the time `t`: its admission (`on_goldfish_vote`). -/
@[no_expose] def ac_on_message (C : Config) (P : Provisional V) (A : ACState V) (t : Time)
    (vote : GoldfishVote V) : ACState V :=
  on_goldfish_vote C P A t vote

/-- The receipt at the time `t` of the block `B`, which the finality gadget has accepted: `B` is
stamped with `t`, and each Goldfish vote of `B.votes` is admitted in list order
(`on_goldfish_vote`). -/
@[no_expose] def ac_on_block (C : Config) (P : Provisional V) (A : ACState V) (t : Time) (B : Block V) :
    ACState V := Id.run do
  let mut A := A
  A.timestamp_block[B] ← t
  for vote in B.votes do
    A ← on_goldfish_vote C P A t vote
  return A

/-! ## The proposal and the source -/

/-- What a proposal of the available chain holds. -/
structure Proposal (V : Type) where
  /-- The parent of the proposed block. -/
  H : Block V
  /-- The Goldfish votes the block includes. -/
  votes : List (GoldfishVote V)
  /-- The votes of `votes` that resolve, in the same order. -/
  support_votes : List (GoldfishVote V)

/-- The proposal of the available chain at the time `t`, the start of the slot `s := C.slot t`:
`votes` is `A`'s list of the votes of slot `s − 1`; `support_votes` is the votes of that list
whose resolution time (`A.tau`) is not `none`, in list order; and `H` is the head (`get_head`) for
the slot `s − 1` with those votes. At `s = 0` the slot `s − 1` reads as slot `0`.

Raises when a resolution time or the head does: when a vote of the list or a block of `Φ.tree` has
no stamp, or when two blocks of `Φ.tree` share a root. -/
@[no_expose] def ac_proposal (C : Config) (A : ACState V) (Φ : Frame V) (t : Time) : DRE (Proposal V) := do
  let s := C.slot t
  let votes := A.gf_votes[s - 1]
  let support_votes ← votes.filterM fun vote => do return (← A.tau Φ vote) ≠ none
  let H ← get_head C A Φ t votes.toFinset support_votes.toFinset (s - 1)
  return Proposal.mk (H := H) (votes := votes) (support_votes := support_votes)

/-- What the available chain gives the finality gadget. -/
structure FGInput (V : Type) where
  /-- The source: a block the latest confirmation update locked by its fast test, or `none`. -/
  source : Option (Block V)
  /-- The head. -/
  head : Block V

/-- The source and the head the available chain gives the finality gadget at the time `t`, in the
slot `s := C.slot t`: `head` is the head (`get_head`) for the slot `s` with `A`'s votes of slot
`s` and those of them whose resolution time (`A.tau`) is not `none`; `source` is the deepest block
(`Block.deepest?`) of `A.fast_blocks` that is in the viable tree of `Φ.tree`, or `none` when there
is none.

Raises when a resolution time or the head does: when a vote of slot `s` or a block of `Φ.tree` has
no stamp, or when two blocks of `Φ.tree` share a root. -/
@[no_expose] def ac_to_fg (C : Config) (A : ACState V) (Φ : Frame V) (t : Time) : DRE (FGInput V) := do
  let s := C.slot t
  let votes := A.gf_votes[s]
  let support_votes ← votes.filterM fun vote => do return (← A.tau Φ vote) ≠ none
  let head ← get_head C A Φ t votes.toFinset support_votes.toFinset s
  let source := Block.deepest? (A.fast_blocks ∩ viable_tree Φ Φ.tree)
  return FGInput.mk (source := source) (head := head)

/-! ## The confirmed tip -/

/-- The confirmed tip: the record `A.latest_confirmed` when it is in `Φ.tree`, and `Φ.F`
otherwise. -/
@[no_expose] def ac_confirmed (A : ACState V) (Φ : Frame V) : Block V := Id.run do
  if A.latest_confirmed ∈ Φ.tree then
    return A.latest_confirmed
  return Φ.F

end Goldilocks
