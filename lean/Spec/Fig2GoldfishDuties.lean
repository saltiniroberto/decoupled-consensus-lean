import Mathlib.Data.Finset.Union
import Spec.Fig3AvailableConfirmation
import Spec.Defs.Duty

/-!
# Figure 2 — the Goldfish duties and store handlers

`on_tick`, `process_block`, `process_goldfish_vote`, `propose_block` and `goldfish_vote`. The
handlers change the store in place; only the two duties concern the validator running the
node, written `ℓ` in the protocol and `i` here — a node whose `ℓ` holds no duty for the slot
simply does not run them.

The `-- line n` comments number the algorithm's lines.
The routines appear callee-first; the figure's order is `on_tick`, `process_block`,
`process_goldfish_vote`, `propose_block`, `goldfish_vote`.

**Figure 3 comes first in the import order** although it is the later figure: `on_tick`
line 8 calls `update_confirmation`. The file names keep the protocol's numbers.

## `ℓ` is `i`, and the proposer test is a parameter

The protocol writes `ℓ` for the validator running the node. This subtree writes `i`, and
nothing else in it uses that letter.

Line 3 asks whether `ℓ` "is the slot-`s` proposer". Proposer assignment is outside this
specification's scope — a slot simply *has* an assigned proposer — so `on_tick`
takes the test as a parameter. `propose_block` itself is fully rendered; it is only *whether
to run it* that is not.

## How a duty broadcasts

The protocol's duties broadcast and then process their own object: `broadcast B;
process_block(Σ, B)`. That line renders verbatim: a duty runs in
`NDREB` (`Duty.lean`) — the outbox threaded over `NDRE` — taking the store and returning
the store, with `broadcast` the protocol's own verb. No caller unions sends: an earlier
duty's broadcasts are already in the outbox when a later one runs. The boundary object
`DutyResult` survives only in `NDREB.outcomes`, where the sts wiring consumes a duty as a
relation. The two handlers stay
`Store → Store`: the algorithm gives them no broadcast line, and "an honest node
relays every object it processes" is network behaviour, the wiring layer's to render.

## Two collisions with `Finset`, and where each lands

**Line 30's `for all B ∈ Σ.T` is an order-free union, written as one.** Line 31
accumulates a union, so the loop's whole effect is `biUnion` — the standard name for it —
and the loop spelling adds nothing. A loop that were *not*
order-free would use the nondeterministic `for` of `Nondet.lean` instead, every visitation
order among the outcomes.

**Line 25 crosses from `Finset` to `List` by a pick.** The block's carried votes are a
`List`: a `Finset` is a quotient, and a quotient cannot appear in an inductive's
constructor, so `Block` could not hold one. The store's `Σ.gf_votes[·]` is a `Finset`, as
the protocol says. The crossing is `let gfList ←ᵖ listings votes` — the proposer's list order
is a genuine nondeterministic choice, since the protocol fixes none. The alternative —
holding the store's votes as lists — would make
"at most two distinct votes per validator" a property of a list and put a `toFinset` at
every counting site.

## `process_block` and `on_tick` here are Figure 2's

Figure 7 extends `process_block` with two lines: the post-state and `update_finality`. That
reading, `S.processBlock`, is the protocol's; this one is the availability layer's —
hence `Fig2.processBlock`. Likewise `on_tick`: the SG layer extends it with one line — at
`t = a_r`, run `sg_vote` — and that reading, `S.onTick` (`Fig5SGDuty.lean`), is the
protocol's; this one is the figure's, hence `Fig2.onTick`. See `Fig1GoldfishWalk.lean` on
the figure-named readings.

## Extract

[fig:Fig2GoldfishDuties] defines the store handlers and the two duties. The handlers
take the store and change it in place. Only the two duties concern the validator
running the node, written `i`; a node whose `i` holds no duty for the slot simply does
not run them. A duty broadcasts its own object and returns the store with that object
already processed; delivering the broadcasts is left to whoever wires this up.

To run the fork choice in slot `s`, a voter at `t_s + Δ` uses the slot-`(s − 1)` votes
it saw before the view freeze at `t_{s−1} + 3Δ`, together with the votes carried by any
slot-`s` block processed so far. That second part is the view merge: the proposal
supplies its own view rather than a forced target. The proposer does not apply the
freeze, and instead uses every held vote when running the fork choice at `t_s`.

`process_block(Σ, B)` and `process_goldfish_vote(Σ, vote)` run once per object, after
every dependency of that object is already in the store: a block's parent, and a vote's
target block.

-/

set_option autoImplicit false

namespace Consensus1

/-- The root a proposer writes into its block, as an assumed function of the block's parent
    and its slot. The protocol calls a block's root its post-state root, and the
    post-state belongs to the finality layer — so this layer can only assume the function
    exists, and
    nothing constrains its answer, exactly as nothing constrains the root a received block
    claims (`Model.lean`, the `B.root` section). -/
class RootComputation (Validator : Type) [Roots] where
  /-- The root of the block being built, from its parent and its slot. -/
  compute : Block Validator → Nat → Root

variable {Validator : Type} [Roots] [DecidableEq Validator] [Committees Validator] [Params]
  [RootComputation Validator]

open Params

/-- `process_goldfish_vote(Σ, vote)`: record a slot-`k` vote with its
    processing time, unless it is from the future, already held, or a third vote by a
    validator already seen equivocating.

    Line 18 is where the protocol's "at most two distinct votes per validator" is maintained:
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

/-- `process_block(Σ, B)`: accept a block whose slot has started,
    stamp it, and fold in every Goldfish vote it carries.

    A block from the future is dropped and nothing else is checked: the protocol's admission at
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

/-- `propose_block(Σ)`, run at `t_s`: take every held slot-`(s−1)`
    vote, run the fork choice on it, and build a block on the head carrying **all** of those
    votes.

    Two things the protocol points out at the line. The proposer applies no freeze — "everything
    held: the tick precedes anything timestamped `t_s`" — and it carries "everything, not only
    the pre-freeze part", which is what makes the block a view-merge channel for its
    receivers.

    The block's root is computed, not chosen: `RootComputation.compute H s`, the assumed
    function of the block's parent and its slot — the protocol does not say what the proposer
    puts there, so the function's answer is unconstrained.

    `NDREB` as every duty; the walk and the picked listing of `votes` — its order a
    nondeterministic choice the protocol leaves open — live underneath it.

    "Run at `t_s`" is an input precondition, a hypothesis the caller supplies, not something
    the duty tests. The autoparam tactic is `solve_by_elim` over the `And` projections rather
    than bare `assumption`, so a caller holding the instant *inside a conjunction* — a
    dependent `if` on a several-part condition, as `on_tick`'s — discharges it with no
    `have`. -/
def Store.proposeBlock (i : Validator) (S : Store Validator)
    (_ : S.t = slotStart S.s := by solve_by_elim [And.left, And.right]) :
    NDREB Validator (Store Validator) := do
  let s := S.s                                                 -- line 22
  let votes := S.gfVotes[s - 1]                                -- line 23
  let H ← Fig1.getHead S votes (s - 1)                         -- line 24
  -- line 25: a block with `B.parent = H`, `B.slot = s`, `B.gf_votes = votes`
  let gfList ←ᵖ listings votes
  let B := Block.mk (parent := H) (slot := s) (root := RootComputation.compute H s)
    (gfVotes := gfList) (attestations := [])
  broadcast (Message.block B)                                  -- line 26
  return Fig2.processBlock S B

/-- `goldfish_vote(Σ)`, run at `t_s + Δ`: vote for the head of the
    merged view, if this validator is on the slot's committee.

    The merge is lines 29–31: the slot-`(s−1)` votes held before the *previous* slot's view
    freeze at `t_{s−1} + 3Δ`, together with everything carried by any slot-`s` block
    processed so far. That second part is the view merge — the proposal supplies its own view
    rather than a forced target.

    A validator off the slot's committee broadcasts nothing and returns the store
    unchanged.

    "Run at `t_s + Δ`" is an input precondition, as `propose_block`'s instant is, with the
    same conjunction-projecting tactic. -/
def Store.goldfishVote (i : Validator) (S : Store Validator)
    (_ : S.t = slotStart S.s + (Δ : Int) := by solve_by_elim [And.left, And.right]) :
    NDREB Validator (Store Validator) := do
  let s := S.s                                                 -- line 28
  -- line 29: held before the freeze at `t_{s−1} + 3Δ`; the timestamp read raises
  let mut votes ← {vote ∈ᴹ S.gfVotes[s - 1] |
    (← S.gfVoteTime[vote]) < slotStart (s - 1) + 3 * (Δ : Int)}
  -- lines 30–31, the view merge: the loop is an order-free union — see the module header
  votes ← votes ∪ ({B ∈ S.T | B.slot = s}).biUnion fun B => B.gfVotes.toFinset
  let H ← Fig1.getHead S votes (s - 1)                         -- line 32
  if i ∈ Committees.K s then                                   -- line 33
    -- line 34: `vote ← (ℓ, s, H); broadcast vote; process_goldfish_vote(Σ, vote)`
    let vote := GoldfishVote.mk (validator := i) (slot := s) (target := H)
    broadcast (Message.gfVote vote)
    return S.processGoldfishVote vote
  return S

/-- `on_tick(Σ, t)`: set the clock and the slot, then run whichever of
    the slot's actions this instant is.

    This is the availability layer's reading. The SG layer extends it with one line — at `t = a_r`, run
    `sg_vote` — and that reading, `S.onTick` (`Fig5SGDuty.lean`), is the protocol's.

    `isProposer` is the parameter of line 3; see the module header. The three actions are
    exclusive because the protocol's instants are distinct: a proposal at `t_s`, a vote at
    `t_s + Δ`, a confirmation evaluation at `t_s + 2Δ` — which is also `t_{s−1} + 6Δ`, the
    evaluation of the *previous* slot, and that is the slot line 8 passes.

    A `NDREB` duty too, so whatever an action broadcasts is in the outbox. Each action
    branch returns its store directly: the three instants are
    mutually exclusive — distinct multiples of `Δ` — so at most one branch runs, and a
    tick at no action instant returns the re-clocked store having broadcast nothing.

    Each branch discharges its action's instant precondition from its own dependent `if`:
    the clock was written just above, so `S.t` reduces to `t` whatever came before, and the
    duties' autoparam tactic projects the instant out of the branch's conjunction, so no
    branch restates anything. Line 7 writes the figure's `t_s + 2Δ` as `t_{s−1} + 6Δ`, equal
    whenever `s > 0` and the form line 8's precondition wants; the docstring above line 8
    already said the two coincide. -/
def Fig2.onTick (i : Validator) (S : Store Validator) (t : Int)
    (isProposer : Nat → Validator → Bool) : NDREB Validator (Store Validator) := do
  let mut S := S
  let s := (t / (4 * (Δ : Int))).toNat                         -- line 2: `s ← ⌊t/(4Δ)⌋`
  S.t ← t
  S.s ← s
  if _ : s > 0 ∧ t = slotStart s ∧ isProposer s i then         -- line 3
    return ← S.proposeBlock i                                  -- line 4
  if _ : s > 0 ∧ t = slotStart s + (Δ : Int) then              -- line 5
    return ← S.goldfishVote i                                  -- line 6
  -- line 7: the figure's `t_s + 2Δ`, written `t_{s−1} + 6Δ` — equal whenever `s > 0`
  if _ : s > 0 ∧ t = slotStart (s - 1) + 6 * (Δ : Int) then
    return ← S.updateConfirmation (s - 1)                      -- line 8
  return S

end Consensus1
