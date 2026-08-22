import Spec.Consensus1.Fig3AvailableConfirmation

/-!
# Figure 2 — the Goldfish duties and store handlers

`on_tick`, `process_block`, `process_goldfish_vote`, `propose_block` and `goldfish_vote`. The
handlers change the store in place; only the two duties concern the validator running the
node, written `ℓ` in the draft and `i` here — a node whose `ℓ` holds no duty for the slot
simply does not run them.

The `-- line n` comments use Figure 2's own line numbering, in the draft as of 2026-08-22.
The routines appear callee-first; the figure's order is `on_tick`, `process_block`,
`process_goldfish_vote`, `propose_block`, `goldfish_vote`.

**Figure 3 comes first in the import order** although it is the later figure: `on_tick` line
8 calls `update_confirmation`. The file names keep the draft's numbers.

## `ℓ` is `i`, and the proposer test is a parameter

The draft writes `ℓ` for the validator running the node. This subtree writes `i`, as the
previous rendering did, and nothing else in it uses that letter.

Line 3 asks whether `ℓ` "is the slot-`s` proposer". Proposer assignment is outside the
draft's scope — Section 1 says only that a slot "has an assigned proposer" — so `on_tick`
takes the test as a parameter. `propose_block` itself is fully rendered; it is only *whether
to run it* that is not.

## What a duty returns

The draft's duties broadcast and then process their own object: `broadcast B;
process_block(Σ, B)`. Broadcasting is a send, and there is no network layer here, so each
duty returns the pair — the object it would broadcast, and the store with that object already
processed. Nothing is lost and the send is left to whoever wires this up.

## Two collisions with `Finset`, and where each lands

**Line 30's `for all B ∈ Σ.T` is a fold.** A `Finset` has no `ForIn` instance and
`Finset.toList` needs `Classical.choice`, so there is no computable loop over one. Line 31
accumulates a *union*, which is commutative and associative, so `Finset.fold` is exactly the
right instrument and the result does not depend on an order — which is why the draft can write
the loop over a set at all.

**Line 25 crosses from `Finset` to `List`, under an assumed order.** The block's carried
votes are a `List`: a `Finset` is a quotient, and a quotient cannot appear in an inductive's
constructor, so `Block` could not hold one. The store's `Σ.gf_votes[·]` is a `Finset`, as the
draft says. `Finset.toList` would cross for free but needs `Classical.choice` — there is no
canonical representative to pick — so the crossing is `Finset.toSortedList` (`FinsetM.lean`),
`Finset.sort` under an ambient `LinearOrder (GoldfishVote Validator)` (Roberto, 2026-08-23):
sorting is
permutation-invariant, so it descends to the quotient and yields one canonical list,
computably. Nothing reads the list's order — votes are consumed as sets on arrival — so the
assumption is inert protocol-wise, and realistic instances have one (validators are keys,
blocks are hashes). The first form used `toList` and paid `noncomputable` on `propose_block`
and `on_tick`; git history has it. The alternative both forms declined, holding the store's
votes as lists, would make "at most two distinct votes per validator" a property of a list
and put a `toFinset` at every counting site.

## `process_block` here is the Goldfish layer's

Figure 7 extends it with two lines: the post-state and `update_finality`. That version is
`FG.processBlock`, and it is the protocol's; this one is what Section 2 defines. See
`Fig1GoldfishWalk.lean` on why the layers are namespaces.
-/

set_option autoImplicit false

namespace Consensus1

namespace Goldfish

variable {Validator : Type}

section Handlers
variable [DecidableEq Validator] [Committees Validator] [TieBreak Validator] [Params]
  [LinearOrder (GoldfishVote Validator)]

open Params

/-- `process_goldfish_vote(Σ, vote)` (Figure 2, lines 15–20): record a slot-`k` vote with its
    processing time, unless it is from the future, already held, or a third vote by a
    validator already seen equivocating.

    Line 18 is where the draft's "at most two distinct votes per validator" is maintained:
    "two witness the equivocation; nothing reads a third". -/
def processGoldfishVote (S : Store Validator) (vote : GoldfishVote Validator) :
    Store Validator := Id.run do
  let mut S := S
  -- line 16
  if vote.slot > S.s ∨ vote ∈ S.gfVotes[vote.slot] then
    return S                                                   -- line 17
  -- line 18: two distinct votes by this validator are already held
  if ∃ a ∈ S.gfVotes[vote.slot], ∃ b ∈ S.gfVotes[vote.slot],
      a.validator = vote.validator ∧ b.validator = vote.validator ∧ a ≠ b then
    return S                                                   -- line 19
  S.gfVotes[vote.slot] ← S.gfVotes[vote.slot] ∪ {vote}         -- line 20
  S.gfVoteTime[vote] ← some S.t
  return S

/-- `process_block(Σ, B)` (Figure 2, lines 9–14): accept a block whose slot has started,
    stamp it, and fold in every Goldfish vote it carries.

    A block from the future is dropped and nothing else is checked: the draft's admission at
    this layer is the slot test alone. The carried votes go through
    `process_goldfish_vote`, so each is subject to that routine's own three tests. -/
def processBlock (S : Store Validator) (B : Block Validator) : Store Validator := Id.run do
  let mut S := S
  if B.slot > S.s then                                         -- line 10
    return S                                                   -- line 11
  S.T ← S.T ∪ {B}                                              -- line 12
  S.blockTime[B] ← some S.t
  for vote in B.gfVotes do                                     -- line 13
    S ← processGoldfishVote S vote                             -- line 14
  return S

/-- `propose_block(Σ)` (Figure 2, lines 21–26), run at `t_s`: take every held slot-`(s−1)`
    vote, run the fork choice on it, and build a block on the head carrying **all** of those
    votes.

    Two things the draft points out at the line. The proposer applies no freeze — "everything
    held: the tick precedes anything timestamped `t_s`" — and it carries "everything, not only
    the pre-freeze part", which is what makes the block a view-merge channel for its
    receivers.

    The block's root is a parameter: it is the post-state root, and what the post-state *is*
    only becomes defined at Section 5, where `process_block` computes it. Section 2's proposer
    cannot know it, and the draft does not say what it puts there.

    `ResultOrExcept` because the walk is, and the carried list is `votes` sorted by the
    ambient order; see the module header on both. -/
def proposeBlock (i : Validator) (S : Store Validator) (root : Nat) :
    ResultOrExcept (Block Validator × Store Validator) := do
  let s := S.s                                                 -- line 22
  let votes := S.gfVotes[s - 1]                                -- line 23
  let H ← getHead S votes (s - 1)                              -- line 24
  -- line 25: a block with `B.parent = H`, `B.slot = s`, `B.gf_votes = votes`
  let B := Block.mk (parent := H) (slot := s) (root := root)
    (gfVotes := votes.toSortedList) (attestations := [])
  -- line 26: `broadcast B; process_block(Σ, B)` — see the module header on the return
  return (B, processBlock S B)

/-- `goldfish_vote(Σ)` (Figure 2, lines 27–34), run at `t_s + Δ`: vote for the head of the
    merged view, if this validator is on the slot's committee.

    The merge is lines 29–31: the slot-`(s−1)` votes held before the *previous* slot's view
    freeze at `t_{s−1} + 3Δ`, together with everything carried by any slot-`s` block
    processed so far. That second part is the view merge — the proposal supplies its own view
    rather than a forced target. -/
def goldfishVote (i : Validator) (S : Store Validator) :
    ResultOrExcept (Option (GoldfishVote Validator) × Store Validator) := do
  let s := S.s                                                 -- line 28
  -- line 29: held before the freeze at `t_{s−1} + 3Δ`
  let held := {vote ∈ S.gfVotes[s - 1] |
    (S.gfVoteTime vote).any (· < slotStart (s - 1) + 3 * (Δ : Int))}
  -- lines 30–31, the view merge: every slot-`s` block's carried votes, unioned in. A fold
  -- rather than a loop — see the module header
  let carried : Finset (GoldfishVote Validator) :=
    ({B ∈ S.T | B.slot = s}).fold (· ∪ ·) ∅ (fun B => B.gfVotes.toFinset)
  let votes := held ∪ carried
  let H ← getHead S votes (s - 1)                              -- line 32
  if i ∈ (Committees.K s : Finset Validator) then              -- line 33
    -- line 34: `vote ← (ℓ, s, H); broadcast vote; process_goldfish_vote(Σ, vote)`
    let vote : GoldfishVote Validator := ⟨i, s, H⟩
    return (some vote, processGoldfishVote S vote)
  return (none, S)

/-- `on_tick(Σ, t)` (Figure 2, lines 1–8): set the clock and the slot, then run whichever of
    the slot's actions this instant is.

    `isProposer` is the parameter of line 3; see the module header. The three actions are
    exclusive because the draft's instants are distinct: a proposal at `t_s`, a vote at
    `t_s + Δ`, a confirmation evaluation at `t_s + 2Δ` — which is also `t_{s−1} + 6Δ`, the
    evaluation of the *previous* slot, and that is the slot line 8 passes.

    The duties' broadcasts are dropped here: `on_tick` returns only the store, so the objects
    a tick would emit are not visible to its caller. That is the one place this rendering
    loses something the draft has, and it is what a network layer would have to restore.

    `ResultOrExcept` because all three actions are. The binds are written through `:=` —
    the plain arrow is the assignment macro's, as in `ghost`. -/
def onTick (i : Validator) (S : Store Validator) (t : Int) (root : Nat)
    (isProposer : Nat → Validator → Bool) : ResultOrExcept (Store Validator) := do
  let mut S := S
  let s := (t / (4 * (Δ : Int))).toNat                         -- line 2: `s ← ⌊t/(4Δ)⌋`
  S.t ← t
  S.s ← s
  if s > 0 ∧ t = slotStart s ∧ isProposer s i then             -- line 3
    S := (← proposeBlock i S root).2                           -- line 4
  if s > 0 ∧ t = slotStart s + (Δ : Int) then                  -- line 5
    S := (← goldfishVote i S).2                                -- line 6
  if s > 0 ∧ t = slotStart s + 2 * (Δ : Int) then              -- line 7
    S := (← updateConfirmation S (s - 1))                      -- line 8
  return S

end Handlers

end Goldfish

end Consensus1
