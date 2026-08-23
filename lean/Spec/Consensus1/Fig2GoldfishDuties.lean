import Mathlib.Data.Finset.Union
import Spec.Consensus1.Fig3AvailableConfirmation
import Spec.Consensus1.Fig5SGDuty

/-!
# Figure 2 — the Goldfish duties and store handlers

`on_tick`, `process_block`, `process_goldfish_vote`, `propose_block` and `goldfish_vote`. The
handlers change the store in place; only the two duties concern the validator running the
node, written `ℓ` in the draft and `i` here — a node whose `ℓ` holds no duty for the slot
simply does not run them.

The `-- line n` comments use Figure 2's own line numbering, in the draft as of 2026-08-22.
The routines appear callee-first; the figure's order is `on_tick`, `process_block`,
`process_goldfish_vote`, `propose_block`, `goldfish_vote`.

**Figures 3, 4 and 5 come first in the import order** although they are the later figures:
`on_tick` line 8 calls `update_confirmation`, and Section 3.4's added line calls `sg_vote`.
The file names keep the draft's numbers.

## `ℓ` is `i`, and the proposer test is a parameter

The draft writes `ℓ` for the validator running the node. This subtree writes `i`, as the
previous rendering did, and nothing else in it uses that letter.

Line 3 asks whether `ℓ` "is the slot-`s` proposer". Proposer assignment is outside the
draft's scope — Section 1 says only that a slot "has an assigned proposer" — so `on_tick`
takes the test as a parameter. `propose_block` itself is fully rendered; it is only *whether
to run it* that is not.

## What a duty returns

The draft's duties broadcast and then process their own object: `broadcast B;
process_block(Σ, B)`. Broadcasting is a send, and there is no network layer here, so a duty
returns a `DutyResult` — the store with the object already processed, and the messages to
broadcast — the state-and-send shape of a lean-sts step result (`NodeStepResult` in the
framework, `DutyResult` in `Store.lean`), so the wiring layer can consume a duty without
reshaping it (Roberto, 2026-08-23). Nothing is lost and the send is left to whoever wires
this up. The two handlers stay `Store → Store`: the figure gives them no broadcast line, and
Section 1's "an honest node relays every object it processes" is network behaviour, the
wiring layer's to render.

## Two collisions with `Finset`, and where each lands

**Line 30's `for all B ∈ Σ.T` is an order-free union, written as one.** Line 31
accumulates a union, so the loop's whole effect is `biUnion` — the standard name for it —
and the loop spelling adds nothing (Roberto, 2026-08-23, retiring the `for all` macros; a
bare fold and the macros preceded it, git history has both). A loop that were *not*
order-free would use the nondeterministic `for` of `Nondet.lean` instead, every visitation
order among the outcomes.

**Line 25 crosses from `Finset` to `List` by a pick.** The block's carried votes are a
`List`: a `Finset` is a quotient, and a quotient cannot appear in an inductive's
constructor, so `Block` could not hold one. The store's `Σ.gf_votes[·]` is a `Finset`, as
the draft says. The crossing is `let gfList ←ᵖ listings votes` — the proposer's list order
is a genuine nondeterministic choice, since the draft fixes none (Roberto, 2026-08-23). Two
earlier forms are in git history: `Finset.toList`, which cost `noncomputable`, and
`Finset.toSortedList` under an assumed `LinearOrder` on votes — an assumption the pick
deletes. The alternative all forms declined, holding the store's votes as lists, would make
"at most two distinct votes per validator" a property of a list and put a `toFinset` at
every counting site.

## `process_block` here is Figure 2's

Figure 7 extends it with two lines: the post-state and `update_finality`. That reading,
`S.processBlock`, is the protocol's; this one is what Section 2 defines — hence
`Fig2.processBlock`. See `Fig1GoldfishWalk.lean` on the figure-named readings.
-/

set_option autoImplicit false

namespace Consensus1

/-- The root a proposer writes into its block, as an assumed function of the block's parent
    and its slot (Roberto, 2026-08-23; before it, the root was a parameter threaded through
    `on_tick`). The draft calls a block's root its post-state root, and the post-state only
    becomes defined at Section 5 — so this layer can only assume the function exists, and
    nothing constrains its answer, exactly as nothing constrains the root a received block
    claims (`Model.lean`, the `B.root` section). -/
class RootComputation (Validator : Type) [Roots] where
  /-- The root of the block being built, from its parent and its slot. -/
  compute : Block Validator → Nat → Root

variable {Validator : Type} [Roots] [DecidableEq Validator] [Committees Validator] [Params]
  [RootComputation Validator] [SGSchedule]

open Params

/-- `process_goldfish_vote(Σ, vote)` (Figure 2, lines 15–20): record a slot-`k` vote with its
    processing time, unless it is from the future, already held, or a third vote by a
    validator already seen equivocating.

    Line 18 is where the draft's "at most two distinct votes per validator" is maintained:
    "two witness the equivocation; nothing reads a third". -/
def Store.processGoldfishVote (S : Store Validator) (vote : GoldfishVote Validator) :
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
def Fig2.processBlock (S : Store Validator) (B : Block Validator) : Store Validator :=
    Id.run do
  let mut S := S
  if B.slot > S.s then                                         -- line 10
    return S                                                   -- line 11
  S.T ← S.T ∪ {B}                                              -- line 12
  S.blockTime[B] ← some S.t
  for vote in B.gfVotes do                                     -- line 13
    S ← S.processGoldfishVote vote                             -- line 14
  return S

/-- `propose_block(Σ)` (Figure 2, lines 21–26), run at `t_s`: take every held slot-`(s−1)`
    vote, run the fork choice on it, and build a block on the head carrying **all** of those
    votes.

    Two things the draft points out at the line. The proposer applies no freeze — "everything
    held: the tick precedes anything timestamped `t_s`" — and it carries "everything, not only
    the pre-freeze part", which is what makes the block a view-merge channel for its
    receivers.

    The block's root is computed, not chosen: `RootComputation.compute H s`, the assumed
    function of the block's parent and its slot — the draft does not say what the proposer
    puts there, so the function's answer is unconstrained.

    `NDRE` because the walk is, and the carried list is a picked listing of `votes` — its
    order a nondeterministic choice the draft leaves open; see the module header on both.

    "Run at `t_s`" is an input precondition, a hypothesis the caller supplies, not something
    the duty tests (Roberto, 2026-08-23; `onSGFGVotingAction` in the second rendering is the
    precedent). The autoparam tactic is `solve_by_elim` over the `And` projections rather
    than bare `assumption`, so a caller holding the instant *inside a conjunction* — a
    dependent `if` on a several-part condition, as `on_tick`'s — discharges it with no
    `have` (Roberto, 2026-08-23, second pass). -/
def Store.proposeBlock (i : Validator) (S : Store Validator)
    (_ : S.t = slotStart S.s := by solve_by_elim [And.left, And.right]) :
    NDRE (DutyResult Validator) := do
  let s := S.s                                                 -- line 22
  let votes := S.gfVotes[s - 1]                                -- line 23
  let H ← Fig1.getHead S votes (s - 1)                         -- line 24
  -- line 25: a block with `B.parent = H`, `B.slot = s`, `B.gf_votes = votes`
  let gfList ←ᵖ listings votes
  let B := Block.mk (parent := H) (slot := s) (root := RootComputation.compute H s)
    (gfVotes := gfList) (attestations := [])
  -- line 26: `broadcast B; process_block(Σ, B)` — see the module header on the return
  return { state := Fig2.processBlock S B, send := {Message.block B} }

/-- `goldfish_vote(Σ)` (Figure 2, lines 27–34), run at `t_s + Δ`: vote for the head of the
    merged view, if this validator is on the slot's committee.

    The merge is lines 29–31: the slot-`(s−1)` votes held before the *previous* slot's view
    freeze at `t_{s−1} + 3Δ`, together with everything carried by any slot-`s` block
    processed so far. That second part is the view merge — the proposal supplies its own view
    rather than a forced target.

    A validator off the slot's committee sends nothing, which the empty `send` says — no
    `Option` needed.

    "Run at `t_s + Δ`" is an input precondition, as `propose_block`'s instant is, with the
    same conjunction-projecting tactic. -/
def Store.goldfishVote (i : Validator) (S : Store Validator)
    (_ : S.t = slotStart S.s + (Δ : Int) := by solve_by_elim [And.left, And.right]) :
    NDRE (DutyResult Validator) := do
  let s := S.s                                                 -- line 28
  -- line 29: held before the freeze at `t_{s−1} + 3Δ`; the timestamp read raises
  let mut votes ← {vote ∈ᴹ S.gfVotes[s - 1] |
    (← S.gfVoteTime[vote]) < slotStart (s - 1) + 3 * (Δ : Int)}
  -- lines 30–31, the view merge: the loop is an order-free union — see the module header
  votes ← votes ∪ ({B ∈ S.T | B.slot = s}).biUnion fun B => B.gfVotes.toFinset
  let H ← Fig1.getHead S votes (s - 1)                         -- line 32
  if i ∈ Committees.K s then              -- line 33
    -- line 34: `vote ← (ℓ, s, H); broadcast vote; process_goldfish_vote(Σ, vote)`
    let vote := GoldfishVote.mk (validator := i) (slot := s) (target := H)
    return { state := S.processGoldfishVote vote, send := {Message.gfVote vote} }
  return { state := S, send := ∅ }

/-- `on_tick(Σ, t)` (Figure 2, lines 1–8): set the clock and the slot, then run whichever of
    the slot's actions this instant is.

    `isProposer` is the parameter of line 3; see the module header. The three actions are
    exclusive because the draft's instants are distinct: a proposal at `t_s`, a vote at
    `t_s + Δ`, a confirmation evaluation at `t_s + 2Δ` — which is also `t_{s−1} + 6Δ`, the
    evaluation of the *previous* slot, and that is the slot line 8 passes.

    A `DutyResult` too, so nothing a tick emits is lost to the caller. Each action branch
    returns its result directly (Roberto, 2026-08-23): the three instants are mutually
    exclusive — distinct multiples of `Δ` — so at most one branch runs, and a tick at no
    action instant returns the re-clocked store with nothing to send.

    Each branch discharges its action's instant precondition from its own dependent `if`:
    the clock was written just above, so `S.t` reduces to `t` whatever came before, and the
    duties' autoparam tactic projects the instant out of the branch's conjunction, so no
    branch restates anything. Line 7 writes the figure's `t_s + 2Δ` as `t_{s−1} + 6Δ`, equal
    whenever `s > 0` and the form line 8's precondition wants; the docstring above line 8
    already said the two coincide. Section 3.4's SG line dispatches on the assumed
    `SGSchedule`; the draft fixes no relation between `a_r` and the Goldfish instants, so on
    a schedule that collided, branch order would decide — the draft's instants are taken as
    distinct.

    `ResultOrExcept` because all three actions are. -/
def Store.onTick (i : Validator) (S : Store Validator) (t : Int)
    (isProposer : Nat → Validator → Bool) : NDRE (DutyResult Validator) := do
  let mut S := S
  let s := (t / (4 * (Δ : Int))).toNat                         -- line 2: `s ← ⌊t/(4Δ)⌋`
  S.t ← t
  S.s ← s
  if h : s > 0 ∧ t = slotStart s ∧ isProposer s i then         -- line 3
    return ← S.proposeBlock i                                  -- line 4
  if h : s > 0 ∧ t = slotStart s + (Δ : Int) then              -- line 5
    return ← S.goldfishVote i                                  -- line 6
  -- line 7: the figure's `t_s + 2Δ`, written `t_{s−1} + 6Δ` — equal whenever `s > 0`
  if h : s > 0 ∧ t = slotStart (s - 1) + 6 * (Δ : Int) then
    let S' ← S.updateConfirmation (s - 1)                      -- line 8
    return { state := S', send := ∅ }
  -- Section 3.4's line: at `t = a_r` for the current round, run `sg_vote`
  if h : t = SGSchedule.a (round s) then
    return S.sgVote i
  return { state := S, send := ∅ }

end Consensus1
