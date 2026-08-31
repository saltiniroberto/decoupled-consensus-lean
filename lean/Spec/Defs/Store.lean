import Mathlib.Data.Finmap
import Spec.«06_StateTransition»
import Spec.Defs.Raise
import Spec.Defs.SigningHistory

/-!
# The store

What a node keeps: messages and their arrival times, and the caches the layers
maintain over them. The store grows in layers, each only ever *adding* fields and
handler lines, never renaming — so there is one `Store` here, with each field's docstring
naming the layer it arrives in. The graded layer adds nothing: "the store does not cache
a view, a quorum set, a support score, a grade, an anchor, a viable tree, or a filtered
tree — each is derived when used."

    Σ = (t, s, T, timestamp[·], gf_votes[·], live_confirmed, latest_confirmed)   availability
      + attestations[·]                                                          SG
      + σ[·], F, J, h_j, h_max                                                   finality
      + pending, height_pair, finality_pair, history, id                         this spec's own

## The protocol's `Σ` is written `S`

`Σ` is a reserved token in Lean (the dependent-pair binder), not a usable identifier.
Store-valued variables are named `S` throughout, and nothing else in this subtree uses that
letter for a Lean binder.

## Timestamps: the votes carry theirs, blocks keep the one map

The protocol writes one `Σ.timestamp(x)` over every kind of object. Lean has no such sum
here, so the stamp lives where the object does. A stored vote — Goldfish or an attestation —
carries its time in its own element: `Σ.gf_votes[k]` and `Σ.attestations[r]` hold
`TimestampedVote`s,
vote and instant together, so a stored vote without a stamp is unrepresentable and every
timestamp comparison is a pure filter. Blocks keep the one `TimeMap`, keyed by identifier, `Option Int`
under the hood, `none` meaning "not processed" — which also stands in for the protocol's
`Σ.timestamp(B_gen) = −∞`: genesis is in `Σ.T` from the start with no stamp, and both readings
give it the same effect, since the only rules that read a block's stamp take a maximum against
a vote's — `−∞` contributes nothing to one — or ask whether the stamp precedes an instant,
where `none` answers as `−∞` does.

Those rules are the two `Σ.resolution_time` readings below and the grade-0 veto's freeze
(`09_Healing.lean`). The raising
bracket read `Σ.timestamp[x]` still has none and stays parked in `OldDefs.lean`.

## Resolution time is when a vote becomes countable

A Goldfish vote names its target by identifier, so a node can hold the vote without holding the
block. `Σ.resolution_time(vote)` is the later of the two stamps, and `⊥` — the protocol's
`+∞` — while the target is not processed at all.

Two things read it, and they read it differently. A *time bound* — `goldfish_vote`'s view
freeze, `update_confirmation`'s support cutoff — asks whether the vote had resolved by an
instant, which is `Σ.resolved_before`. Finiteness — `propose_block`, and the view merge — asks
only whether it has resolved, which is `Σ.resolved`: the max is finite exactly when the target
is a processed block, so that test needs no stamp and works on a vote carried by a block, which
has no arrival stamp of its own.

Why the bound and not the vote's own stamp: the freeze exists so that honest validators
evaluating at one instant agree on the vote set. A vote that arrived early whose target arrived
late is held by both and countable by neither, and only the later of the two stamps says so.

An attestation has its own reading, `Σ.resolution_time(a)`: an empty confirmed block
resolves at receipt, a named one when the store holds its block, and the pair fields
never take part.
The grades read the timed form; `latest`, the view checks and `propose_block`'s carry test
read only finiteness, which is `Σ.resolved_att`.

## `Σ.T` is a map, and ancestry is read off it

A block names its parent by identifier (`Model.lean`), so no block is a chain and ancestry is
not a question about two values. `Σ.T` is therefore a `Finmap` from identifier to block, and
one field carries everything the protocol asks of the tree: the block an identifier names
(`Σ.T[b]`, the raising read), whether one has been processed (`b ∈ Σ.T`), the finite set of
those that have (`Σ.T.keys`, which every derived view ranges over), and admission
(`Σ.T.insert`).

Ancestry lives here for the same reason, written `b ⪯[S] c`, `b ≺[S] c` and `b ∼[S] c` — the
protocol's three relations with the store they are read against named. Each is a `Bool`: the
walk climbs parent links from `c`, and it terminates without any assumption about `S`, because
each step erases the key it just visited and `Σ.T.keys.card` decreases. So `false` is the right
answer in each of the three ways the walk can stop — `c` is not a processed block, genesis is
reached without meeting `b`, or the parent links cycle and the walk runs into an erased key —
and no fact about `S` is owed to make the answer sound. `b ⪯[S] b` holds whether or not `b` has
been processed, the equality being tested before the lookup.

## What the type does not enforce

The protocol says `gf_votes[k]` keeps at most two distinct votes per validator, and
`attestations[r]` at most two attestations with distinct confirmed blocks per validator —
attestations differing only in their pair fields are one vote. That is a property of the
handlers, which drop a third, and not of the type: a `Finset` cannot express it.
`process_goldfish_vote` and `process_sg_vote` are where it is maintained, and each says so.

Likewise `Σ.F ⪯[Σ] Σ.J`, that `Σ.T` is parent-closed, that every entry answers to its own
key — `Σ.T[b].id = b` — and that `Σ.σ` is defined on exactly `Σ.T.keys`: all invariants of the
reachable stores, and all facts for `Analysis/` rather than facts of this structure.

## How the indexed fields are read

Every indexed field is read with the protocol's brackets. `Σ.T[b]` and `Σ.σ[b]` **raise** —
the next paragraph. The others are total, so their reads owe nothing: `Σ.gf_votes[k]` and
`Σ.attestations[r]` are sets, empty if nothing was processed. The field
types are left bare — `(k : Nat) → Finset …` — the `GetElem` instances above being
declared on the function types themselves; the indexed *writes* consult no instance at
all, the assignment macros expanding to `Function.update`.

`Σ.attestations[·]` is indexed by `Int` and reads at either index: the grades read round
`r`'s predecessor, where round `0` must read round `−1` as itself rather than truncate
to `0`, while the handler holds its round as a `Nat`.

Neither `Σ.T` nor `Σ.σ` is total, and both bracket reads **raise**: `Σ.T[b]` returns
`DRE (Block Validator)` and `Σ.σ[b]` returns `DRE (ChainState Validator)`, so
`let B ← Σ.T[b]` propagates an identifier the store does not hold, and a routine that reads
either carries `DRE`. `b ∈ Σ.T` and `b ∈ Σ.σ` are the memberships, and they are what "is it
recorded?" is spelled with, `= none` being unavailable on a raising read. Ancestry alone does not go
through the brackets: it reads `Σ.T.lookup` and stays a `Bool`, which is what keeps it and the
scores that call it out of the monad. Everything else that wants a field of a processed block
goes through `Σ.T[b]` — `Σ.parent_of` and `Σ.slot_of` included, which is why both raise.

The raw `Option` behind `Σ.σ` stays reachable by application, `Σ.σ b`, because that map *is* a
function; its one reader is the walk predicate inside `S.getHead`, which cannot carry the
monad — set-builders raise instead, through the `FinsetM` fold machinery.

`TimeMap` and `StateMap` are named for their raising reads' sake, a `def` and not an
`abbrev` so the name survives to the instance lookup. `BlockMap` is an `abbrev` instead:
`Finmap` is a distinctive enough head for the instance to resolve on, and unfolding is what
keeps `Finmap`'s own API — `lookup`, `keys`, `insert`, `erase` — available on `Σ.T` unchanged.
The total maps need no name, their `GetElem` instances being declared on the function types
themselves.

## Extract — Definition (Store)

The store is

`Σ = (t, s, T, timestamp[·], gf_votes[·], live_confirmed, latest_confirmed)`

and the later layers add their fields to it — the attestation pool `attestations[·]`
with the SG layer, and the
state map `σ[·]` with the finality state `(F, J, h_j, h_max)` with the finality
layer. Later layers only ever add fields and lines; they never rename either, and the
graded layer adds nothing: the store does not cache a view, a quorum set, a support
score, a grade, an anchor, a viable tree, or a filtered tree — each is derived when
used.

## Extract

`Σ.T` is the tree of processed blocks and `Σ.gf_votes[k]` the set of processed slot-`k`
votes, each vote stored with the time at which it was processed; `Σ.timestamp(x)` is
that time. `Σ.gf_votes[k]` keeps at most two distinct votes per
validator, which is all any rule reads. `Σ.attestations[r]` is the pool of processed
round-`r` attestations — likewise timestamped — keeping at most two attestations with
distinct confirmed blocks per validator: attestations differing only in their pair fields
are one vote, an empty confirmed block is a value the pool holds, and two distinct
confirmed blocks from one validator
in one round are an equivocation. Attestations never enter a Goldfish vote
set. `Σ.live_confirmed` is the block the last
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

variable {Validator : Type} [BlockIds] [BlockIdentity Validator]
  [DecidableEq Validator]

/-! ### The two named map types, and how each is read -/

/-- A processing-time map: `Σ.timestamp(x)` restricted to one kind of object — the
    blocks', the one remaining. A named type, so a raising bracket read can resolve on
    it (the read itself is parked in `OldDefs.lean`, nothing reading a timestamp map any
    more); a `def` and not an `abbrev`, or the name would unfold away before the
    lookup. -/
def TimeMap (α : Type) := (x : α) → Option Int

/-- `Σ.T`: the processed blocks, keyed by identifier. An `abbrev`, so `Finmap`'s own
    `lookup`, `keys`, `insert` and `erase` apply to `Σ.T` unchanged. -/
abbrev BlockMap (Validator : Type) :=
  Finmap (fun _ : BlockId => Block Validator)

/-- `f[k]`: the set at an index of a `Nat`-indexed set map — `Σ.gf_votes[k]`. Validity
    is `True`, every index having a set, so `get_elem_tactic` closes it with `trivial`
    and a read owes nothing. The field types stay bare: an instance on the function type
    itself is enough, no named map type in the way (measured). -/
scoped instance natSetMapGetElem {α : Type} :
    GetElem ((k : Nat) → Finset α) Nat (Finset α) (fun _ _ => True) where
  getElem f k _ := f k

/-- `f[r]`: the same read on an `Int`-indexed set map — `Σ.sg_votes[r]`, indexed by `Int`
    so round `0` reads round `−1` as itself rather than truncating. -/
scoped instance intSetMapGetElem {α : Type} :
    GetElem ((r : Int) → Finset α) Int (Finset α) (fun _ _ => True) where
  getElem f r _ := f r

/-- `f[r]` on an `Int`-indexed set map at a `Nat` index: a routine holding a slot or
    round as a `Nat` reads without writing the coercion. -/
scoped instance intSetMapNatGetElem {α : Type} :
    GetElem ((r : Int) → Finset α) Nat (Finset α) (fun _ _ => True) where
  getElem f r _ := f (r : Int)

/-- The finality layer's chain-state map, keyed by identifier. Named for the same reason as
    `TimeMap`. -/
def StateMap (Validator : Type) :=
  (b : BlockId) → Option (ChainState Validator)

/-- `b ∈ σ`: the map records a state for `b`. -/
scoped instance stateMapMembership :
    Membership BlockId (StateMap Validator) where
  mem σ b := (σ b).isSome

/-- The membership is a `Bool` in disguise, so an `if b ∉ S.σ` can test it. -/
scoped instance (σ : StateMap Validator) (b : BlockId) : Decidable (b ∈ σ) :=
  inferInstanceAs (Decidable ((σ b).isSome = true))

/-- `σ[b]`, the raising read: the state recorded for `b`, or the failure. In a `do` block
    over `DRE`, `let σB ← S.σ[b]` propagates a block the map does not record. The
    raw `Option` stays reachable by application, `S.σ b`. -/
scoped instance stateMapGetElem :
    GetElem (StateMap Validator) BlockId
      (DRE (ChainState Validator)) (fun _ _ => True) where
  getElem σ b _ := if h : b ∈ σ then .ok ((σ b).get h) else .error .error

/-- `T[b]`, the raising read: the block `b` names, or the failure. In a `do` block over
    `DRE`, `let B ← S.T[b]` propagates an identifier the store does not hold. `Finmap.lookup`
    stays available for the readers that must not raise — ancestry, and the walks over it. -/
scoped instance blockMapGetElem :
    GetElem (BlockMap Validator) BlockId (DRE (Block Validator)) (fun _ _ => True) where
  getElem T b _ :=
    if h : b ∈ T then .ok ((T.lookup b).get (Finmap.lookup_isSome.mpr h)) else .error .error

/-- `T.reaches b c`: climb the parent links from `c`, and report whether `b` is met. The walk
    behind `b ⪯[S] c`; see the module header for what its `false` means.

    Each step erases the key it just visited, so `T.keys.card` strictly decreases and the walk
    terminates on any map at all — no acyclicity, no parent-closure, no slot condition. The
    erasure is also what makes a cycle answer correctly: the cycle is consumed, the next lookup
    fails, and `b` off the cycle is reported absent, which it is.

    `c = b` is tested before the lookup, so ancestry is reflexive whether or not `c` has been
    processed. -/
def BlockMap.reaches (T : BlockMap Validator) (b c : BlockId) : Bool :=
  if c = b then true
  else if hc : c ∈ T then
    let B := (T.lookup c).get (Finmap.lookup_isSome.mpr hc)
    if hp : B.parent.isSome then BlockMap.reaches (T.erase c) b (B.parent.get hp)
    else false
  else false
termination_by T.keys.card
decreasing_by
  simp only [Finmap.keys_erase]
  exact Finset.card_erase_lt_of_mem (Finmap.mem_keys.mpr hc)

/-- `T.chainCarries a c`: some block of the chain ending at `c` carries the attestation `a` —
    the "on `H`'s chain" test of `propose_block`. The same erase-based walk as
    `BlockMap.reaches`, terminating on any map at all for the same reason. -/
def BlockMap.chainCarries (T : BlockMap Validator)
    (a : Attestation Validator) (c : BlockId) : Bool :=
  if hc : c ∈ T then
    let B := (T.lookup c).get (Finmap.lookup_isSome.mpr hc)
    if a ∈ B.attestations then true
    else if hp : B.parent.isSome then BlockMap.chainCarries (T.erase c) a (B.parent.get hp)
    else false
  else false
termination_by T.keys.card
decreasing_by
  simp only [Finmap.keys_erase]
  exact Finset.card_erase_lt_of_mem (Finmap.mem_keys.mpr hc)

/-- A timestamped vote: a stored vote and the time the store processed it. A named
    structure, where a bare product would name nothing. `α` is what was voted: a
    `GoldfishVote` in `Σ.gf_votes[·]`, an `Attestation` in `Σ.attestations[·]`. -/
structure TimestampedVote (α : Type) where
  /-- The stored vote. -/
  vote : α
  /-- When it was processed. -/
  time : Int
deriving DecidableEq

/-- The store, every layer's fields at once.

    "The store keeps messages and their arrival times, and nothing else. Every rule below is
    a timestamp comparison on this one pool." -/
structure Store (Validator : Type) where
  /-- `Σ.t`, the clock: the time the last `on_tick` set. `Σ.t = Σ.s = 0` initially. -/
  t : Int
  /-- `Σ.s`, the current slot, set by the same `on_tick`. -/
  s : Nat
  /-- `Σ.T`, the processed blocks, keyed by identifier. -/
  T : BlockMap Validator
  /-- `Σ.timestamp(B)` for a block: when it was processed, `none` if it was not, keyed by
      identifier. Written by `process_block`, and read by `Σ.resolution_time` alone. See the
      module header. -/
  blockTime : TimeMap BlockId
  /-- `Σ.gf_votes[k]`, the processed slot-`k` Goldfish votes, each stored with the time
      it was processed. The entries' times are what the freeze in `goldfish_vote` and
      both cutoffs in `update_confirmation` read. -/
  gfVotes : (k : Nat) → Finset (TimestampedVote (GoldfishVote Validator))
  /-- `Σ.live_confirmed`, the block the last evaluated slot confirmed. -/
  liveConfirmed : BlockId
  /-- `Σ.latest_confirmed`, the monotone record the node exposes: `update_confirmation`
      (`10_AvailableConfirmation.lean`) advances it exactly when the new confirmation
      descends from it. No rule of the protocol reads it. -/
  latestConfirmed : BlockId
  /-- `Σ.height_pair`, the height pair decided at the round's action instant `a_r` and
      staged until the attestation goes out at this validator's own voting time — this
      rendering's one deviation from the protocol's single-instant `attest`: the FG vote
      is computed at `a_r`, the SG vote's confirmed block at the voting time, and the two are assembled into
      one attestation there (`Store.onTick`, `11_Duties.lean`). `HeightPair.empty` at
      `gen`: nothing signed yet. -/
  heightPair : HeightPair
  /-- `Σ.finality_pair`, the finality pair decided and staged beside `Σ.height_pair`, at
      the same instant and for the same reason. -/
  finalityPair : FinalityPair

  /-- `Σ.pending`, the blocks received whose parent the store did not yet hold — **a
      field the protocol's store does not have** (Roberto, 2026-09-01): the protocol
      assumes a block is handled "after every dependency of that object is already in the
      store", and this spec renders the mechanism instead. `process_block`
      (`07_FGStore.lean`) is its only writer: a block waits here until its parent's
      admission drains it, and a block that can never be admitted simply stays. -/
  pending : Finset (Block Validator)

  /-- `Σ.attestations[r]`, the pool of processed round-`r` attestations (SG layer), each
      with the time it was processed. At most two attestations with distinct confirmed
      blocks per validator — attestations differing only in their pair fields are one
      vote, and an empty confirmed block is a value the pool holds (`process_sg_vote`, `05_SGDuty.lean`).
      `latest` selects by round rather than by time; the grades read the times. -/
  attestations : (r : Int) → Finset (TimestampedVote (Attestation Validator))
  /-- `Σ.σ[b]`, the stored post-state of each processed block (finality layer). Absent outside
      `Σ.T`; that it is defined on exactly `Σ.T.keys` is an invariant, not a fact of the
      type. -/
  σ : StateMap Validator
  /-- `Σ.F`, the finalized block (finality layer). Its height is not a store field: the
      height of a finalization is read off a chain state, in `get_fg_vote`. -/
  F : BlockId
  /-- `Σ.J`, the justified block rooting the fork choice (finality layer). -/
  J : BlockId
  /-- `Σ.h_j`, its height. -/
  h_j : Nat
  /-- `Σ.h_max`, the greatest state height the store has seen offered: `update_finality`
      takes the maximum against each offered height, and it is never lowered. -/
  h_max : Nat
  /-- `Σ.history`, the anti-slashing record `Λ` — **not a field of the protocol's store**:
      the protocol keeps `Λ` beside the store, its type in `SigningHistory.lean` and the
      rules that read and write it in `08_FinalityVote.lean`. Written only by
      `record_attestation`. -/
  history : SigningHistory
  /-- `Σ.id`, the validator running this node — the protocol's `ℓ`, which its figures treat
      as ambient and **its store does not list**. A field here, so a duty can read its
      own identity instead of taking it as a parameter. Written by nothing: fixed at
      `gen`. -/
  id : Validator

/-- The initial store: `Σ.T = {B_gen}`, `Σ.live_confirmed = Σ.latest_confirmed = B_gen`,
    "other fields are empty".

    Two values the protocol fixes elsewhere, and this has to write out: the
    genesis block's state is the initial chain state (`ChainState.gen`); and the finality caches
    start where that state does, `F = J = B_gen` with `h_j = 0` and `h_max = 1`, since genesis
    "is justified and finalized at height 0, and every chain starts at height 1".
    `Σ.t = Σ.s = 0` initially.

    Genesis has no timestamp: the protocol's `−∞` and this `none` agree, nothing reading a
    block's timestamp.

    Takes the one thing "empty" cannot supply: whose node this store is. -/
def Store.gen (i : Validator) : Store Validator where
  t := 0
  s := 0
  T := Finmap.singleton (genesisId Validator) Block.genesis
  blockTime := fun _ => none
  gfVotes := fun _ => ∅
  liveConfirmed := genesisId Validator
  latestConfirmed := genesisId Validator
  heightPair := .empty
  finalityPair := .empty
  pending := ∅
  attestations := fun _ => ∅
  σ := fun b => if b = genesisId Validator then some .gen else none
  F := genesisId Validator
  J := genesisId Validator
  h_j := 0
  h_max := 1
  history := SigningHistory.gen
  id := i

/-- `Σ.resolution_time(vote)`: the later of the vote's own stamp and its target's, and `⊥`
    for the protocol's `+∞` while `Σ.T` does not hold the target. See the module header on why
    the later of the two is the instant that matters.

    `Σ.timestamp(B_gen) = −∞` is the `⊥` the store records for genesis, and it enters the
    maximum as the vote's own stamp, contributing nothing — which is what `−∞` does. -/
def Store.resolutionTime (S : Store Validator)
    (e : TimestampedVote (GoldfishVote Validator)) : Option Int :=
  if e.vote.target ∉ S.T then ⊥
  else some (max e.time ((S.blockTime e.vote.target).getD e.time))

/-- `Σ.resolution_time(vote) < c`: the vote has resolved, and resolved before `c`. -/
def Store.resolvedBefore (S : Store Validator)
    (e : TimestampedVote (GoldfishVote Validator)) (c : Int) : Bool :=
  (S.resolutionTime e).any (fun t => t < c)

/-- `Σ.resolution_time(vote) < +∞`: the vote has resolved at all, which asks only that `Σ.T`
    hold its target — a maximum of two stamps is finite exactly when both are, and a
    processed block always has one.

    It takes the bare vote, not a stored entry, because it needs no arrival stamp: the votes a
    block carries have none of their own, and this is the test the view merge applies to
    them. -/
def Store.resolved (S : Store Validator) (a : GoldfishVote Validator) : Bool :=
  a.target ∈ S.T

/-- `Σ.resolution_time(a)` for a stored attestation: its own stamp when the confirmed
    block is empty — it resolves at receipt — the later of its stamp and the confirmed
    block's when the store holds it, and `⊥`, the protocol's `+∞`, otherwise. The pair fields never
    take part. -/
def Store.resolutionTimeAtt (S : Store Validator)
    (e : TimestampedVote (Attestation Validator)) : Option Int := Id.run do
  if _ : e.vote.confirmed ≠ ⊥ then
    let C := e.vote.confirmed.value
    if C ∉ S.T then
      return ⊥
    return some (max e.time ((S.blockTime C).getD e.time))
  return some e.time                        -- an empty confirmed block resolves at receipt

/-- `Σ.resolution_time(a) < +∞` for a bare attestation: an empty confirmed block resolves
    at receipt, and a named one asks only that `Σ.T` hold its block — the finiteness reading, needing
    no stamp, as `Σ.resolved` is for a Goldfish vote. -/
def Store.resolvedAtt (S : Store Validator) (a : Attestation Validator) : Bool :=
  a.confirmed.all (· ∈ S.T)

/-- The identifier `b`'s parent names, `⊥` at genesis. The read is the bracket's, so an
    identifier the store does not hold **raises** rather than answering: the walks read the
    parent links through this, and a walk stepping onto a block the store has never processed
    is not a case the protocol has. -/
def Store.parentOf (S : Store Validator) (b : BlockId) : DRE (Option BlockId) := do
  return (← S.T[b]).parent

/-- The slot of the block `b` names, through the same bracket, and raising for the same
    reason. Its callers range over `Σ.T.keys` or over a tree drawn from it, so the failure is
    unreachable where they stand — which is a fact for `Analysis/`, not a licence to answer
    silently here. -/
def Store.slotOf (S : Store Validator) (b : BlockId) : DRE Nat := do
  return (← S.T[b]).slot

/-! ## Ancestry, relative to the store

The protocol's three relations, each a `Bool` and each naming the store it is read against.
`BlockMap.reaches` above is the walk; these are the spellings the figures use. -/

/-- `b ⪯[S] c`: `b = c`, or `b` names an ancestor of the block `c` names, read off the parent
    links `S` has processed — the protocol's reflexive ancestry. -/
def Store.preceq (S : Store Validator) (b c : BlockId) : Bool :=
  BlockMap.reaches S.T b c

@[inherit_doc] scoped notation:50 b:51 " ⪯[" S:max "] " c:51 => Store.preceq S b c

/-- `b ≺[S] c`: strict ancestry — `b ⪯[S] c` and `b ≠ c`. `c` is a *descendant* of `b` when
    `b ⪯[S] c`, so descendant is reflexive and `≺[S]` is the strict half. -/
def Store.prec (S : Store Validator) (b c : BlockId) : Bool :=
  S.preceq b c && b != c

@[inherit_doc] scoped notation:50 b:51 " ≺[" S:max "] " c:51 => Store.prec S b c

/-- `b ∼[S] c`: *compatible* — `b ⪯[S] c` or `c ⪯[S] b`, the two lie on one chain of `S`. The
    protocol's blocks *conflict* otherwise; no named relation renders that, `¬ ∼[S]`
    sufficing so far. -/
def Store.compatible (S : Store Validator) (b c : BlockId) : Bool :=
  S.preceq b c || S.preceq c b

@[inherit_doc] scoped notation:50 b:51 " ∼[" S:max "] " c:51 => Store.compatible S b c

/-- Every attestation the store holds, as one set: the round pools up to `round(Σ.s)`
    unioned — the whole pool, since `process_sg_vote` admits no later round. The union
    itself is this vocabulary definition's, so a spec body reads the one name — the
    protocol's `all_attestations(Σ)`. -/
def Store.allAttestations [Params] (S : Store Validator) :
    Finset (TimestampedVote (Attestation Validator)) :=
  (Finset.range (round S.s + 1)).biUnion (fun k => S.attestations[k])

/-! ## The live tree

The finality layer's other derived set, the processed finality evidence
`E_F(Σ) = {(Σ.σ[b].F, Σ.σ[b].h_F) : b ∈ Σ.T}`, is **not** rendered: no figure reads it, and
under this subtree's rule a definition lands with its first consumer. -/

/-- `T_F(Σ) = {B ∈ Σ.T : Σ.F ⪯ B}`, the *live tree*, as identifiers: the processed blocks at or below the
    finalized one. "It retains every processed block; the live tree is derived below the
    finalized block" — so nothing is ever removed from `Σ.T`, and this is the view every
    later rule uses in its place. -/
def Store.liveTree (S : Store Validator) : Finset BlockId :=
  {b ∈ S.T.keys | S.F ⪯[S] b}


/-! ## The duty boundary object

Not protocol content: the protocol's duties `broadcast` and return nothing. Duties run in
`NDREB` (`Nondet.lean`) — they broadcast into the monad's outbox and return the store — and
this structure survives at the consumption boundary alone: `NDREB.outcomes` packages a
run's store and outbox as one value, the state-and-send shape of a lean-sts step result
(`NodeStepResult` in the framework), so the wiring layer consumes a duty without
reshaping it. -/

/-- What a duty's run produces, at the boundary: the store afterwards, and everything it
    broadcast. Built only by `NDREB.outcomes`; no duty returns one. -/
structure DutyResult (Validator : Type) [BlockIds] where
  /-- The store afterwards. -/
  state : Store Validator
  /-- The messages broadcast, for the network to deliver. -/
  send : Finset (Message Validator)

end DC
