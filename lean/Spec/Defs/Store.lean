import Spec.«06_StateTransition»
import Spec.Defs.Raise
import Spec.Defs.SigningHistory

/-!
# The store

What a node keeps: messages and their arrival times, and the caches the layers
maintain over them. The store grows in three layers, each only ever *adding* fields and
handler lines, never renaming — so there is one `Store` here, with each field's docstring
naming the layer it arrives in.

    Σ = (t, s, T, timestamp[·], gf_votes[·], live_confirmed, latest_confirmed)   availability
      + sg_votes[·]                                                              SG
      + σ[·], F, h_F, J, h_j, h_max                                              finality
      + root_proposal[·], sg_root[·]                                            healing
      + H, i                                                                     this spec's own

## The protocol's `Σ` is written `S`

`Σ` is a reserved token in Lean (the dependent-pair binder), not a usable identifier.
Store-valued variables are named `S` throughout, and nothing else in this subtree uses that
letter for a Lean binder.

## Timestamps: the votes carry theirs, blocks keep the one map

The protocol writes one `Σ.timestamp(x)` over every kind of object. Lean has no such sum
here, so the stamp lives where the object does. A stored vote — Goldfish or SG — carries
its time in its own element: `Σ.gf_votes[k]` and `Σ.sg_votes[r]` hold `TimestampedVote`s,
vote and instant together, so a stored vote without a stamp is unrepresentable and every
timestamp comparison is a pure filter. Blocks keep the one `TimeMap`, `Option Int` under
the hood, `none` meaning "not processed" — which also stands in for the protocol's
`Σ.timestamp(B_gen) = −∞`: genesis is in `Σ.T` from the start with no stamp, and the two
readings agree because **no rendered rule reads a block's timestamp at all**, the map
written by `process_block` and read by nothing, exactly as in the protocol. With no rule
reading any `TimeMap`, the raising bracket read `Σ.timestamp[x]` lost its readers and is
parked in `OldDefs.lean`.

## What the type does not enforce

The protocol says `gf_votes[k]` and `sg_votes[r]` each "keep at most two distinct votes per
validator, which is all any rule reads". That is a property of the handlers, which drop a
third, and not of the type: a `Finset` cannot express it. `process_goldfish_vote` and
`process_sg_vote` are where it is maintained, and each says so.

Likewise `Σ.F ⪯ Σ.J`, that `Σ.T` is parent-closed, and that `Σ.σ` is defined on exactly
`Σ.T` — all invariants of the reachable stores, and all facts for `Analysis/` rather than
facts of this structure.

## How the indexed fields are read

`Σ.σ[B]` wears the protocol's brackets and **raises** — the next
paragraph. The vote tables are total maps read by application: `Σ.gf_votes k` and
`Σ.sg_votes r` are sets, empty if nothing was processed. The indexed writes keep the
protocol's brackets — `Σ.gf_votes[k] ← …` — through the assignment macros, which
consult no instance.

The state map is not total, and `Σ.σ[B]` **raises**: it returns
`DRE (ChainState Validator)`, so `let σB ← Σ.σ[B]` propagates a block the map does
not record, and a routine that reads the map carries `DRE`. `B ∈ Σ.σ` is the
membership — definitionally `(Σ.σ B).isSome` — and it is what "is it recorded?" is spelled
with, `= none` being unavailable on a raising read. The raw `Option` stays reachable by
application, `Σ.σ B`, because the map *is* a function; its one reader is the walk predicate
inside `S.getHead`, which cannot carry the monad — set-builders raise instead, through the
`FinsetM` fold machinery.

A name is needed on each
map type because instances resolve on a type's head constant, and a bare function type has
none.

## Extract — Definition (Store)

The store is

`Σ = (t, s, T, timestamp[·], gf_votes[·], live_confirmed, latest_confirmed)`

and the later layers add their fields to it — `sg_votes[·]` with the SG layer, the
state map `σ[·]` with the finality state `(F, h_F, J, h_j, h_max)` with the finality
layer, and the round-root bookkeeping `root_proposal[·]` and `sg_root[·]` with the
healing layer. Later layers only ever add fields and lines; they never rename either.

## Extract

`Σ.T` is the tree of processed blocks and `Σ.gf_votes[k]` the set of processed slot-`k`
votes, each vote stored with the time at which it was processed; `Σ.timestamp(x)` is
that time. `Σ.gf_votes[k]` keeps at most two distinct votes per
validator, which is all any rule reads; the same holds for `Σ.sg_votes[r]`, the
processed round-`r` SG votes — likewise timestamped — where two distinct heads from one
validator in one round are an equivocation. SG votes travel only on the wire: blocks do not carry them, and
they never enter a Goldfish vote set. `Σ.live_confirmed` is the block the last
evaluated slot confirmed. `Σ.latest_confirmed` is the monotone record the node exposes;
no rule in this protocol reads it.

Initially `Σ.T = {B_gen}` and `Σ.live_confirmed = Σ.latest_confirmed = B_gen`; other
fields are empty. The store keeps messages and their arrival times, and nothing else:
every rule below is a timestamp comparison on this one pool. A validator has
equivocated as of `t` when `Σ.gf_votes[k]` holds two of its votes both timestamped
before `t`, so its equivocation-detection time is the later of the two stamps, and one
cutoff decides which votes are timely and which equivocations are.

`process_block(Σ, B)` and `process_goldfish_vote(Σ, vote)` run once per object, after
every dependency of that object is already in the store: a block's parent, and a vote's
target block. A carried vote may name a block the receiver does not hold; acquiring it
is outside the store, so that vote reaches the store when it is finally processed, not
when its block did.

-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [Roots] [DecidableEq Validator]

/-! ### The two named map types, and how each is read -/

/-- A processing-time map: `Σ.timestamp(x)` restricted to one kind of object — the
    blocks', the one remaining. A named type, so a raising bracket read can resolve on
    it (the read itself is parked in `OldDefs.lean`, nothing reading a timestamp map any
    more); a `def` and not an `abbrev`, or the name would unfold away before the
    lookup. -/
def TimeMap (α : Type) := (x : α) → Option Int

/-- The finality layer's block-state map. Named for the same reason as `TimeMap`. -/
def StateMap (Validator : Type) := (B : Block Validator) → Option (ChainState Validator)

/-- `B ∈ σ`: the map records a state for `B`. -/
scoped instance stateMapMembership :
    Membership (Block Validator) (StateMap Validator) where
  mem σ B := (σ B).isSome

/-- The membership is a `Bool` in disguise, so an `if B ∉ S.σ` can test it. -/
scoped instance (σ : StateMap Validator) (B : Block Validator) : Decidable (B ∈ σ) :=
  inferInstanceAs (Decidable ((σ B).isSome = true))

/-- `σ[B]`, the raising read: the state recorded for `B`, or the failure. In a `do` block
    over `DRE`, `let σB ← S.σ[B]` propagates a block the map does not record. The
    raw `Option` stays reachable by application, `S.σ B`. -/
scoped instance stateMapGetElem :
    GetElem (StateMap Validator) (Block Validator)
      (DRE (ChainState Validator)) (fun _ _ => True) where
  getElem σ B _ := if h : B ∈ σ then .ok ((σ B).get h) else .error .error

/-- A timestamped vote: a stored vote and the time the store processed it. A named
    structure, where a bare product would name nothing. `α` is what was voted: a
    `GoldfishVote` in `Σ.gf_votes[·]`, an `SGHeadVote` in `Σ.sg_votes[·]`. -/
structure TimestampedVote (α : Type) where
  /-- The stored vote. -/
  vote : α
  /-- When it was processed. -/
  time : Int
deriving DecidableEq

/-- A stored SG vote: who voted, and the block its head names. Only a vote whose head
    is a block is stored — `process_sg_vote` drops an empty head — so the stored head is
    a `Block`, not an `Option`; the wire object (`SGVote`, `Model.lean`) keeps `⊥`. -/
structure SGHeadVote (Validator : Type) where
  /-- The voting validator. -/
  validator : Validator
  /-- The block the vote's head names. -/
  head : Block Validator
deriving DecidableEq

/-- The store, every layer's fields at once.

    "The store keeps messages and their arrival times, and nothing else. Every rule below is
    a timestamp comparison on this one pool." -/
structure Store (Validator : Type) where
  /-- `Σ.t`, the clock: the time the last `on_tick` set. Starts below `0` — the protocol leaves
      the initial value unstated, and every scheduled instant is at least `0` — at `-1`. -/
  t : Int
  /-- `Σ.s`, the current slot, set by the same `on_tick`. -/
  s : Nat
  /-- `Σ.T`, the tree of processed blocks. -/
  T : Finset (Block Validator)
  /-- `Σ.timestamp(B)` for a block: when it was processed, `none` if it was not. Written by
      `process_block`; read by nothing, in this protocol. See the module header. -/
  blockTime : TimeMap (Block Validator)
  /-- `Σ.gf_votes[k]`, the processed slot-`k` Goldfish votes, each stored with the time
      it was processed. The entries' times are what the freeze in `goldfish_vote` and
      both cutoffs in `update_confirmation` read. -/
  gfVotes : (k : Nat) → Finset (TimestampedVote (GoldfishVote Validator))
  /-- `Σ.live_confirmed`, the block the last evaluated slot confirmed. -/
  liveConfirmed : Block Validator
  /-- `Σ.latest_confirmed`, the monotone record the node exposes. "No rule in this protocol
      reads it" — it is written by `update_confirmation` and nothing else touches it. -/
  latestConfirmed : Block Validator
  /-- `Σ.sg_votes[r]`, the processed round-`r` SG votes (SG layer), each a `SGHeadVote` —
      only votes whose head is a block are stored — with the time it was processed.
      `latest` selects by round rather than by time; the healing scores read the
      times. -/
  sgVotes : (r : Int) → Finset (TimestampedVote (SGHeadVote Validator))
  /-- `Σ.σ[B]`, the stored post-state of each processed block (finality layer). Absent outside
      `Σ.T`; that it is defined on exactly `Σ.T` is an invariant, not a fact of the type. -/
  σ : StateMap Validator
  /-- `Σ.F`, the finalized block (finality layer). -/
  F : Block Validator
  /-- `Σ.h_F`, its height. -/
  h_F : Nat
  /-- `Σ.J`, the justified block rooting the fork choice (finality layer). -/
  J : Block Validator
  /-- `Σ.h_j`, its height. -/
  h_j : Nat
  /-- `Σ.h_max`, the greatest state height in the live tree. It "otherwise only grows", and
      is recomputed inside the new live tree whenever `Σ.F` advances. -/
  h_max : Nat
  /-- `Σ.root_proposal[r]` (healing layer): the proposal root carried by the first round-`r`
      opening block processed, `⊥` while no opening block has arrived. -/
  rootProposal : (r : Nat) → Option (Block Validator)
  /-- `Σ.sg_root[r]` (healing layer): the round's stored SG root (`get_sg_root`,
      `09_Healing.lean`), `⊥` before the scheduled write. -/
  sgRoot : (r : Nat) → Option (Block Validator)
  /-- `Σ.H`, the validator's durable signing record — **not a field of the protocol's store**:
      the record behind the finality-vote rules, its type in `SigningHistory.lean` and
      its use in `08_FinalityVote.lean`. Written only by those rules. -/
  H : SigningHistory Validator
  /-- `Σ.i`, the validator running this node — the protocol's `ℓ`, which its figures treat
      as ambient and **its store does not list**. A field here, so a duty can read its
      own identity instead of taking it as a parameter. Written by nothing: fixed at
      `gen`. -/
  i : Validator

/-- The initial store: `Σ.T = {B_gen}`, `Σ.live_confirmed = Σ.latest_confirmed = B_gen`,
    "other fields are empty".

    Three values the protocol fixes elsewhere, or by "empty", and this has to write out: the
    clock starts at `-1`, below every scheduled instant, since `on_tick` is what sets it; the
    genesis block's state is the initial chain state (`ChainState.gen`); and the finality caches
    start where that state does, `(B_gen, 0)` for both pairs with `h_max = 1`, since genesis
    "is justified and finalized at height 0, and every chain starts at height 1".

    Genesis has no timestamp: the protocol's `−∞` and this `none` agree, nothing reading a
    block's timestamp.

    Takes the one thing "empty" cannot supply: whose node this store is. -/
def Store.gen (i : Validator) : Store Validator where
  t := -1
  s := 0
  T := {.genesis}
  blockTime := fun _ => none
  gfVotes := fun _ => ∅
  liveConfirmed := .genesis
  latestConfirmed := .genesis
  sgVotes := fun _ => ∅
  σ := fun B => if B = .genesis then some .gen else none
  F := .genesis
  h_F := 0
  J := .genesis
  h_j := 0
  h_max := 1
  rootProposal := fun _ => none
  sgRoot := fun _ => none
  H := SigningHistory.gen
  i := i

/-! ## The live tree

The finality layer's other derived set, the processed finality evidence
`E_F(Σ) = {(Σ.σ[B].F, Σ.σ[B].h_F) : B ∈ Σ.T}`, is **not** rendered: no figure reads it, and
under this subtree's rule a definition lands with its first consumer. -/

/-- `T_F(Σ) = {B ∈ Σ.T : Σ.F ⪯ B}`, the *live tree*: the processed blocks at or below the
    finalized one. "It retains every processed block; the live tree is derived below the
    finalized block" — so nothing is ever removed from `Σ.T`, and this is the view every
    later rule uses in its place. -/
def Store.liveTree (S : Store Validator) : Finset (Block Validator) :=
  {B ∈ S.T | S.F ⪯ B}


/-! ## The duty boundary object

Not protocol content: the protocol's duties `broadcast` and return nothing. Duties run in
`NDREB` (`Nondet.lean`) — they broadcast into the monad's outbox and return the store — and
this structure survives at the consumption boundary alone: `NDREB.outcomes` packages a
run's store and outbox as one value, the state-and-send shape of a lean-sts step result
(`NodeStepResult` in the framework), so the wiring layer consumes a duty without
reshaping it. -/

/-- What a duty's run produces, at the boundary: the store afterwards, and everything it
    broadcast. Built only by `NDREB.outcomes`; no duty returns one. -/
structure DutyResult (Validator : Type) [Roots] where
  /-- The store afterwards. -/
  state : Store Validator
  /-- The messages broadcast, for the network to deliver. -/
  send : Finset (Message Validator)

end DC
