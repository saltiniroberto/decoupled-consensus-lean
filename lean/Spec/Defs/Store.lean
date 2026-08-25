import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Option
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
      + head[·], equiv[·], root_proposal[·], sg_root[·]                          healing
      + H, i                                                                     this spec's own

## The protocol's `Σ` is written `S`

`Σ` is a reserved token in Lean (the dependent-pair binder), not a usable identifier.
Store-valued variables are named `S` throughout, and nothing else in this subtree uses that
letter for a Lean binder.

## Timestamps: two maps, and the timed entries

The protocol writes one `Σ.timestamp(x)` over every kind of object. Lean has no such sum
here, so the stamp lives where the object does. A stored Goldfish vote carries its time
in its own entry — `Σ.gf_votes[k][i]` is a `VoteTime`, vote and instant together, so a
stored vote without a stamp is unrepresentable and the freeze and cutoff filters are
pure. Blocks and SG votes keep a `TimeMap` each, `Option Int` under the hood, `none`
meaning "not processed". That also stands in for the protocol's
`Σ.timestamp(B_gen) = −∞`: genesis is in `Σ.T` from the start with no stamp, and the two
readings agree because **no rendered rule reads a block's timestamp at all** — the block
map is written by `process_block` and read by nothing, exactly as in the protocol. An SG
vote's timestamp is read on a vote drawn from a `sg_votes[·]` set, so always on a
processed one — which is why the bracket read `Σ.timestamp[x]` **raises**, exactly as
`Σ.σ[B]` does: an unstamped held vote marks a store the handlers cannot build, and the
failure reaches the caller instead of the vote silently failing a cutoff. The raw
`Option` stays reachable by application, `S.sgVoteTime vote`.

## What the type does not enforce

The protocol says `sg_votes[r]` keeps "at most two distinct votes per validator, which
is all any rule reads". That is a property of its handler, which drops a third, and not
of the type: a `Finset` cannot express it. `process_sg_vote` is where it is maintained,
and it says so. (`gf_votes[·]` needs no such rule: one vote per slot and validator is a
fact of its type — a second differing vote writes `gf_equiv[·]` instead of being
stored.)

Likewise `Σ.F ⪯ Σ.J`, that `Σ.T` is parent-closed, and that `Σ.σ` is defined on exactly
`Σ.T` — all invariants of the reachable stores, and all facts for `Analysis/` rather than
facts of this structure.

## How the indexed fields are read

`Σ.σ[B]` and `Σ.timestamp[x]` wear the protocol's brackets and **raise** — the next
paragraph. The total maps are plain functions read by application: `Σ.sg_votes r` is a
set, empty if nothing was processed; `Σ.gf_votes k i` is an `Option` entry tested
against `⊥`, and the duties build their views from the collected `gf_votes_at(Σ, k)`
below; `Σ.gf_equiv k i` likewise. The two-level writes keep the protocol's brackets —
`Σ.gf_votes[k][i] ← …` — through the assignment macros, which consult no instance.

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

`Σ = (t, s, T, timestamp[·], gf_votes[·], gf_equiv[·], live_confirmed, latest_confirmed)`

and the later layers add their fields to it — `sg_votes[·]` with the SG layer, the
state map `σ[·]` with the finality state `(F, h_F, J, h_j, h_max)` with the finality
layer, and the per-round bookkeeping `head[·]`, `equiv[·]`, `root_proposal[·]`,
`sg_root[·]` with the healing layer. Later layers only ever add fields and lines; they
never rename either.

## Extract

`Σ.T` is the tree of processed blocks, timestamped: `Σ.timestamp(x)` is the time at
which object `x` was processed into the store. `Σ.gf_votes[k][i]` is the first slot-`k`
vote processed from validator `i`, stored together with the time at which it was
processed; a later differing slot-`k` vote from `i` is not stored — `Σ.gf_equiv[k][i]`
takes the time at which the first such vote was processed, once. `Σ.sg_votes[r]`, the
processed round-`r` SG votes, keeps at most two distinct votes per validator, which is
all any rule reads: two distinct heads from one validator in one round are an
equivocation. SG votes travel only on the wire: blocks do not carry them, and they
never enter a Goldfish vote set. `Σ.live_confirmed` is the block the last evaluated
slot confirmed. `Σ.latest_confirmed` is the monotone record the node exposes; no rule
in this protocol reads it.

Initially `Σ.T = {B_gen}` and `Σ.live_confirmed = Σ.latest_confirmed = B_gen`; other
fields are empty. The store keeps messages and their arrival times, and nothing else:
every rule below is a timestamp comparison on this one pool. A validator has
equivocated in slot `k` as of `t` when `Σ.gf_equiv[k][i]` is before `t`, and one cutoff
decides which votes are timely and which equivocations are.

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

/-- A processing-time map, one per kind of object: `Σ.timestamp(x)` restricted to that
    kind. A named type, so that the raising bracket read below resolves — instances
    resolve on a type's head constant, and a bare function type has none. A `def` and
    not an `abbrev`, or the name would unfold away before the lookup. -/
def TimeMap (α : Type) := (x : α) → Option Int

/-- `times[x]`, the raising read: when `x` was processed, or the failure if it was not.
    The raw `Option` stays reachable by application, the map being a function. -/
scoped instance timeMapGetElem {α : Type} :
    GetElem (TimeMap α) α (DRE Int) (fun _ _ => True) where
  getElem times x _ := if h : (times x).isSome then .ok ((times x).get h) else .error .error

/-- The optional instant is set and lies before `c` — how a per-validator time entry such
    as `Σ.gf_equiv[k][i]` is compared against a cutoff; an absent entry is before nothing.
    A named predicate rather than the inline `∃ t ∈ o, t < c`: a set-builder's decidability
    search fails on the anonymous `∃` over an `Option` (measured), and the keyed instance
    below is found where the anonymous one is not. -/
def timeBefore (o : Option Int) (c : Int) : Prop := ∃ t ∈ o, t < c

instance (o : Option Int) (c : Int) : Decidable (timeBefore o c) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

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

/-- A timed vote entry: a stored vote and the time the store processed it. A named
    structure, where a bare product would name nothing. `α` is what was voted: a
    `GoldfishVote` in `Σ.gf_votes[·]`, a head block in the healing bookkeeping
    `Σ.head[·]`. -/
structure VoteTime (α : Type) where
  /-- The stored vote. -/
  vote : α
  /-- When it was processed. -/
  time : Int
deriving DecidableEq

/-- The pair every Goldfish fork-choice rule consumes: the votes it may score, and the
    validators it must treat as equivocators. The duties build one from the store — the
    proposer as of its run, the voter at its freeze and then merged with the block-carried
    votes (`merge_view`, `02_GoldfishDuties.lean`) — and pass it down to `get_head`. -/
structure GoldfishView (Validator : Type) [Roots] where
  /-- The votes in view. -/
  votes : Finset (GoldfishVote Validator)
  /-- The validators the view holds equivocating. -/
  equivocators : Finset Validator

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
  /-- `Σ.gf_votes[k][i]`: the first slot-`k` vote processed from validator `i`, with the
      time it was processed, absent while none — one stored vote per slot and validator.
      The entry's time is what the freeze in `goldfish_vote` and both cutoffs in
      `update_confirmation` read. A later differing vote is not stored; it writes
      `Σ.gf_equiv[k][i]` instead. -/
  gfVotes : (k : Nat) → (i : Validator) → Option (VoteTime (GoldfishVote Validator))
  /-- `Σ.gf_equiv[k][i]`: the time at which a slot-`k` vote from `i` differing from its
      stored one was first processed — the first equivocation; absent while none. It
      stands where a second stored vote used to witness an equivocation. -/
  gfEquiv : (k : Nat) → (i : Validator) → Option Int
  /-- `Σ.live_confirmed`, the block the last evaluated slot confirmed. -/
  liveConfirmed : Block Validator
  /-- `Σ.latest_confirmed`, the monotone record the node exposes. "No rule in this protocol
      reads it" — it is written by `update_confirmation` and nothing else touches it. -/
  latestConfirmed : Block Validator
  /-- `Σ.sg_votes[r]`, the processed round-`r` SG votes (SG layer). -/
  sgVotes : (r : Nat) → Finset (SGVote Validator)
  /-- `Σ.timestamp(vote)` for an SG vote (SG layer). Written by `process_sg_vote`; no
      rendered rule reads it, `latest` selecting by round rather than by time. -/
  sgVoteTime : TimeMap (SGVote Validator)
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
  /-- `Σ.head[r][i]` (healing layer): the first nonempty head processed from validator `i`'s
      round-`r` attestations, with its processing time; absent while none. Indexed by `Int`:
      round `r` grades its round-`(r−1)` entries (`09_Healing.lean`), and round `0` must
      find round `−1` empty — a `Nat` index would truncate `0 − 1` back to `0`. -/
  head : (r : Int) → (i : Validator) → Option (VoteTime (Block Validator))
  /-- `Σ.equiv[r][i]` (healing layer): the time at which a head different from
      `Σ.head[r][i]`'s was first processed from validator `i` in round `r`; absent while
      none. Indexed by `Int` for the same reason as `head`. -/
  equiv : (r : Int) → (i : Validator) → Option Int
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
  gfVotes := fun _ _ => none
  gfEquiv := fun _ _ => none
  liveConfirmed := .genesis
  latestConfirmed := .genesis
  sgVotes := fun _ => ∅
  sgVoteTime := fun _ => none
  σ := fun B => if B = .genesis then some .gen else none
  F := .genesis
  h_F := 0
  J := .genesis
  h_j := 0
  h_max := 1
  head := fun _ _ => none
  equiv := fun _ _ => none
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

/-- `gf_votes_at(Σ, k)`: the stored slot-`k` votes of the slot's committee, as one set —
    what the proposer's view holds. One vote per validator is stored, so the set holds at
    most one vote per committee member. A stored vote from a validator outside `K_k` is
    not collected: no rule reads one — every score and count filters by `K_k`. -/
def Store.gfVotesAt [Committees Validator] (S : Store Validator) (k : Nat) :
    Finset (GoldfishVote Validator) :=
  (Committees.K k).biUnion fun v => ((S.gfVotes k v).map (·.vote)).toFinset

/-- `gf_votes_before(Σ, k, c)`: the stored slot-`k` votes of the slot's committee whose
    entries were processed before instant `c` — the view a cutoff sees. -/
def Store.gfVotesBefore [Committees Validator] (S : Store Validator) (k : Nat) (c : Int) :
    Finset (GoldfishVote Validator) :=
  (Committees.K k).biUnion fun v =>
    (((S.gfVotes k v).filter fun e => e.time < c).map (·.vote)).toFinset


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
