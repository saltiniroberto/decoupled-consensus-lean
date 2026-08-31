import Spec.«10_AvailableConfirmation»

/-!
# The validator's duties, and the tick that runs them

`propose_block`, `goldfish_vote` and `on_tick`. This is the last file of the specification,
because a duty calls the whole of it: the head comes from `get_head` (`09_Healing.lean`), the
confirmation from `update_confirmation` (`10_AvailableConfirmation.lean`), the pairs a round's
attestation carries from `08_FinalityVote.lean`.

## Why the duties come last

The specification is in dependency order, one definition per routine, so a file may only name
what an earlier file defines. The duties name almost everything, so they are last; `on_tick`
names the duties, so it is last within the file. Nothing here is redefined by anything.

## `ℓ` is `Σ.id`

The protocol writes `ℓ` for the validator running the node. This rendering reads it off
the store — `Σ.id`, fixed at `gen` — so no duty takes an identity parameter; the tick's
proposer test reads the assumed assignment, `proposer(Σ.s) = ℓ` (`Proposers`,
`Model.lean`).

## How a duty broadcasts

The protocol's duties broadcast and then process their own object: `broadcast B;
process_block(Σ, B)`. That line renders verbatim: a duty runs in
`NDREB` (`Nondet.lean`) — the outbox threaded over `NDRE` — taking the store and returning
the store, with `broadcast` the protocol's own verb. No caller unions sends: an earlier
duty's broadcasts are already in the outbox when a later one runs. The boundary object
`DutyResult` survives only in `NDREB.outcomes`, where the sts wiring consumes a duty as a
relation. The handlers stay broadcast-free: the algorithm gives them no broadcast line,
and "an honest node relays every object it processes" is network behaviour, the wiring
layer's to render.

## Three collisions with `Finset`, and where each lands

**The view merge's `for all B ∈ Σ.T` is the nondeterministic `for`.** A `Finset` fixes
no iteration order, so the `for` of `Nondet.lean` picks a listing — every visitation
order among the outcomes. The merge's body is an order-free union, so every listing
converges to one vote set and the outcome set is a singleton; the loop spelling is the
figure's.

**The proposal's vote set crosses from `Finset` to `List` by a pick.** The block's carried votes are a
`List`: a `Finset` is a quotient, and a quotient cannot appear in an inductive's
constructor, so `Block` could not hold one. The store's `Σ.gf_votes k` is a `Finset`, as
the protocol says. The crossing is `let gfList ←ᵖ votes.toLists` — the proposer's list order
is a genuine nondeterministic choice, since the protocol fixes none. The alternative —
holding the store's votes as lists — would make
"at most two distinct votes per validator" a property of a list and put a `toFinset` at
every counting site.

**The carried attestations cross the same way**, `let attList ←ᵖ carried.toLists`.

## Extract

Only the duties concern the validator running the node, written `ℓ`; a node whose `ℓ` holds
no duty for the slot simply does not run them. A duty broadcasts its own object and returns
the store with that object already processed; delivering the broadcasts is left to whoever
wires this up.

To run the fork choice in slot `s`, a voter at `t_s + Δ` uses the slot-`s−1` votes it saw
before the view freeze at `t_{s−1} + 3Δ`, together with the votes carried by any slot-`s`
block processed so far. That second part is the view merge: the proposal supplies its own view
rather than a forced target. The proposer does not apply the freeze, and instead uses every
held vote when running the fork choice at `t_s`.
-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [BlockIds] [BlockIdentity Validator] [DecidableEq Validator] [Electorate Validator]
  [Committees Validator] [Proposers Validator] [Params]

open Params

/-! ## New figure — The clock and the slot's duties -/
/-! ## Figure `set_clock(Σ, t)` -/
/-- Move the store's clock to `t` and
    with it the slot, `s = ⌊t/(4Δ)⌋`.

    Every reading of `on_tick` begins here, and every line of every reading tests `Σ.t` and
    `Σ.s` afterwards, so an instant is always compared against the tick that is running. A
    layer that adds a line to the tick reuses this rather than writing the two assignments
    again. -/
def Store.setClock (S : Store Validator) (t : Int) : Store Validator := Id.run do
  let mut S := S
  S.t ← t
  S.s ← (t / (4 * (Δ : Int))).toNat                            -- `s ← ⌊t/(4Δ)⌋`
  return S

/-! ## Figure `propose_block(Σ)` -/
/-- Run at `t_s`: take every held slot-`(s−1)`
    vote, run the fork choice on it, and build a block on the head carrying **all** of those
    votes — and every resolved attestation not already on the head's chain.

    Two things the protocol points out at the vote lines. The proposer applies no freeze —
    "everything
    held: the tick precedes anything timestamped `t_s`" — and it carries "everything, not only
    the pre-freeze part", which is what makes the block a view-merge channel for its
    receivers.

    The carried attestations are drawn from the whole pool — rendered as the union of the
    rounds up to `round(Σ.s)`, which is the whole pool, the handler admitting no later
    round — keeping the resolved ones (an empty confirmed block resolves at receipt) that no block of
    the chain ending at `H` already carries.

    `NDREB` as every duty; the walk and the picked listings of `votes` and of the carried
    attestations — each order a
    nondeterministic choice the protocol leaves open — live underneath it.

    "Run at `t_s`" is an input precondition, a hypothesis the caller supplies, not something
    the duty tests. The autoparam tactic is `solve_by_elim` over the `And` projections rather
    than bare `assumption`, so a caller holding the instant *inside a conjunction* — a
    dependent `if` on a several-part condition, as `on_tick`'s — discharges it with no
    `have`. -/
def Store.proposeBlock (S : Store Validator)
    (_ : S.t = slotStart S.s := by solve_by_elim [And.left, And.right]) :
    NDREB Validator (Store Validator) := do
  let s := S.s                                      -- runs at `t_s`
  let votes := {e.vote | e ∈ S.gfVotes[s - 1]}
  let supportVotes := {vote ∈ votes | S.resolved vote}
  let H ← S.getHead votes supportVotes (s - 1)
  -- the resolved attestations no block of `H`'s chain carries
  let carried := {e.vote | e ∈ S.allAttestations,
    S.resolvedAtt e.vote ∧ ¬ S.T.chainCarries e.vote H}
  -- a block with `B.parent = H`, `B.slot = s`, `B.proposer = ℓ`, `B.gf_votes = votes`
  let gfList ←ᵖ votes.toLists
  let attList ←ᵖ carried.toLists
  let B := Block.mk (parent := ↑H) (slot := s) (proposer := ↑S.id)
    (gfVotes := gfList) (attestations := attList)
  broadcast (Message.block B)
  return (← S.processBlock B)

/-! ## Figure `goldfish_vote(Σ)` — runs at `t_s + Δ` -/
/-- Run at `t_s + Δ`: vote for the head of the
    merged view, if this validator is on the slot's committee.

    The merge: the slot-`(s−1)` votes held before the *previous* slot's view
    freeze at `t_{s−1} + 3Δ`, together with everything carried by any slot-`s` block
    processed so far. That second part is the view merge — the proposal supplies its own view
    rather than a forced target.

    A validator off the slot's committee broadcasts nothing and returns the store
    unchanged.

    "Run at `t_s + Δ`" is an input precondition, as `propose_block`'s instant is, with the
    same conjunction-projecting tactic. -/
def Store.goldfishVote (S : Store Validator)
    (_ : S.t = slotStart S.s + (Δ : Int) := by solve_by_elim [And.left, And.right]) :
    NDREB Validator (Store Validator) := do
  let s := S.s
  -- held before the freeze at `t_{s−1} + 3Δ`, and resolved before it
  let mut votes := {e.vote | e ∈ S.gfVotes[s - 1],
    e.time < slotStart (s - 1) + 3 * (Δ : Int)}
  let mut supportVotes := {e.vote | e ∈ S.gfVotes[s - 1],
    S.resolvedBefore e (slotStart (s - 1) + 3 * (Δ : Int))}
  -- the view merge: each processed slot-`s` block offers its carried slot-`(s−1)` votes
  let slotBlocks ← {B ∈ᴹ S.T.keys | (← S.slotOf B) = s}
  for B in slotBlocks do
    let included := {a ∈ (← S.T[B]).gfVotes.toFinset | a.slot = s - 1}
    let includedResolved := {a ∈ included | S.resolved a}
    votes ← votes ∪ included
    supportVotes ← supportVotes ∪ includedResolved
  let H ← S.getHead votes supportVotes (s - 1)
  if S.id ∈ Committees.K s then
    -- `vote ← (ℓ, s, H); broadcast vote; process_goldfish_vote(Σ, vote)`
    let vote := GoldfishVote.mk (validator := S.id) (slot := s) (target := H)
    broadcast (Message.gfVote vote)
    return S.processGoldfishVote vote
  return S

/-! ## New figure — The tick -/
/-! ## Figure `goldfish_on_tick(Σ)` -/
/-- The slot actions of this layer:
    whichever of them the clock now stands at, or nothing.

    The instants are mutually exclusive — distinct multiples of `Δ`: a proposal at `t_s`, a
    vote at `t_s + Δ` — so at most one branch runs, and a tick at neither instant returns
    the store having broadcast nothing. Each branch returns its store directly, and
    discharges its action's instant precondition from its own dependent `if`.

    It reads the clock rather than taking the time, so a layer that runs its own lines first
    can call it afterwards and both see the same tick. The proposer test reads the assumed
    assignment: `proposer(Σ.s) = ℓ` (`Proposers`, `Model.lean`). A `NDREB` duty, so
    whatever an action
    broadcasts is in the outbox. -/
def Store.goldfishOnTick (S : Store Validator) :
    NDREB Validator (Store Validator) := do
  let mut S := S
  if _ : S.s > 0 ∧ S.t = slotStart S.s ∧ Proposers.proposer S.s = S.id then
    return (← S.proposeBlock)
  if _ : S.s > 0 ∧ S.t = slotStart S.s + (Δ : Int) then
    return (← S.goldfishVote)
  return S

/-! ## Figure `on_tick(Σ, t)` -/
/-- `on_tick(Σ, t)` at this layer: the
    clock, then the slot's two duties, then the round's two vote instants.

    The clock first, as in every reading — `Σ.t` and `Σ.s` are what each line below tests, so
    an instant is compared against the tick that is running, never the one before it.

    Then the slot-`(s−1)` confirmation evaluation at `t_s + 2Δ`, which is `t_{s−1} + 6Δ` —
    before the round's vote lines, which can share its tick: what a validator signs rests
    on this tick's confirmation, never the previous one's.

    Then the round's votes, this rendering's one deviation from the protocol's
    single-instant `attest` — the FG and SG halves are computed at two instants and
    assembled into the one attestation. At the round's action instant `a_r`
    (`heightDecisionTime`): `get_fg_vote` derives the FG vote's fields, the client rules
    fill the two pairs — finality first, so the height rule reads this attestation's own
    lock — `record_attestation` makes them durable, and the pairs are staged as
    `Σ.height_pair` and `Σ.finality_pair`. At `sgfg_voting(Σ.id, r)`, this validator's own
    time, which the schedule assumes rather than fixes: the confirmed block is computed by
    `get_sg_vote`, the round's one combined attestation is assembled from it and the
    staged pairs, broadcast — the only line in the spec that puts an attestation on the
    wire — and processed into this store's own pool. `A_G2` is derived at each of the two
    instants, both past `Γ_2`. A block's grade is fixed there, but the *deepest* grade-2
    block of the filtered tree is not: the tree can change between the instants, so the
    two halves may read different `A_G2` where the protocol's single `attest` reads one —
    a consequence of the two-instant split, not an extra decision.

    The reading is written out rather than composed onto the Goldfish layer's tick: a call
    can only put the new lines wholly before or wholly after. What it
    reuses are the two halves that reading is itself made of — `set_clock` and
    `goldfish_on_tick` — so nothing is written twice.

    The `[SGSchedule Validator]` binder is for the attestation time. -/
def Store.onTick [SGSchedule Validator] (S : Store Validator) (t : Int) :
    NDREB Validator (Store Validator) := do
  let mut S := S
  S ← S.setClock t
  let r := round S.s
  S ⇐ S.goldfishOnTick
  -- the slot-`(s−1)` confirmation is evaluated at `t_s + 2Δ = t_{s−1} + 6Δ`, before any
  -- vote of the same tick, so `attest`'s halves see this tick's confirmation
  if S.s > 0 ∧ S.t = slotStart S.s + 2 * (Δ : Int) then
    S ⇐ S.updateConfirmation (S.s - 1)
  -- the FG vote is decided at `a_r` and staged
  if S.t = heightDecisionTime r then
    let fgv ← S.getFGVote r (← S.deepestG2 r)
    let fp := S.history.finalityPair fgv.h_j fgv.J fgv.h_F
    let hp := S.history.heightPair fgv.heightInputs fp
    S.history ← S.history.recordAttestation hp fp
    S.heightPair ← hp
    S.finalityPair ← fp
  -- the attestation goes out at this validator's own time, its confirmed block computed then
  if S.t = SGSchedule.sgfgVoting S.id r then
    let C_sg ← S.getSGVote r (← S.deepestG2 r)
    let a := Attestation.mk (validator := S.id) (round := r) (confirmed := some C_sg)
      (heightPair := S.heightPair) (finalityPair := S.finalityPair)
    broadcast (Message.attestation a)
    S := S.processSGVote a
  return S

end DC
