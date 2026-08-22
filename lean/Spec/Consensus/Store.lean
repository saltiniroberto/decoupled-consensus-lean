import Spec.Consensus.Fig6StateTransition
import Spec.Consensus.Raise

/-!
# The store

Definition 1 of the draft, together with the two fields later sections add to it. The draft
builds the store in three layers and is explicit that the layers only ever *add*: "later
sections add fields to this store and add lines to these handlers; they never rename either."
So there is one `Store` here, with each field's docstring naming the layer it arrives in.

    Σ = (t, s, T, timestamp[·], gf_votes[·], live_confirmed, latest_confirmed)   § 2.2
      + sg_votes[·]                                                             § 3.2
      + σ[·], F, h_F, J, h_j, h_max                                             § 5.1

## The draft's `Σ` is written `S`

`Σ` is a reserved token in Lean (the dependent-pair binder), not a usable identifier.
Store-valued variables are named `S` throughout, and nothing else in this subtree uses that
letter for a Lean binder.

## Timestamps are three maps, not one

The draft writes one `Σ.timestamp(x)` over every kind of object. Lean has no such sum here,
so there is one map per kind — blocks, Goldfish votes, SG votes — and `Σ.timestamp(x)` is
rendered as whichever one `x` belongs to. Nothing is lost: every rule reads the timestamp of
an object whose kind is fixed by the line it appears on.

Each map is `Option Int`-valued, `none` meaning "not processed". That also stands in for the
draft's `Σ.timestamp(B_gen) = −∞`: genesis is in `Σ.T` from the start with no stamp, and the
two readings agree because **no rendered rule reads a block's timestamp at all** — the block
map is written by `process_block` and read by nothing, exactly as in the draft. Vote
timestamps are read, always on a vote drawn from a `gf_votes[·]` or `sg_votes[·]` set, so
always on a processed one.

## What the type does not enforce

The draft says `gf_votes[k]` and `sg_votes[r]` each "keep at most two distinct votes per
validator, which is all any rule reads". That is a property of the handlers, which drop a
third, and not of the type: a `Finset` cannot express it. `process_goldfish_vote` and
`process_sg_vote` are where it is maintained, and each says so.

Likewise `Σ.F ⪯ Σ.J`, that `Σ.T` is parent-closed, and that `Σ.σ` is defined on exactly
`Σ.T` — all invariants of the reachable stores, and all facts for `Analysis/` rather than
facts of this structure.

## How the three indexed fields are read

`Σ.gf_votes[k]`, `Σ.sg_votes[r]` and `Σ.σ[B]` are all written with the draft's brackets, and
each gets there differently.

The two vote tables are **total**: every index has a set, empty if nothing was processed. So
`VoteTable` carries a `GetElem` whose validity is `True`, closed by `get_elem_tactic`'s own
`trivial`, and a read owes nothing.

The state map is not total, and `Σ.σ[B]` **raises**: it returns
`ResultOrExcept (ChainState Validator)`, so `let σB ← Σ.σ[B]` propagates a block the map does
not record, and a routine that reads the map carries `ResultOrExcept`. `B ∈ Σ.σ` is the
membership — definitionally `(Σ.σ B).isSome` — and it is what "is it recorded?" is spelled
with, `= none` being unavailable on a raising read. The raw `Option` stays reachable by
application, `Σ.σ B`, because the map *is* a function; that is what lets a set-builder read
the map without dragging `ResultOrExcept` into it.

All of this is the arrangement the previous rendering arrived at over 2026-08-21 and -22;
`CONTEXT.md` records what else was tried and why each was set aside. A name is needed on each
map type because instances resolve on a type's head constant, and a bare function type has
none.
-/

set_option autoImplicit false

namespace Consensus

variable {Validator : Type}

/-! ### The three map types, and how each is read -/

/-- A per-index set of processed objects: `Σ.gf_votes[·]` and `Σ.sg_votes[·]`. A named type,
    so that `Σ.gf_votes[k]` resolves — instances resolve on a type's head constant, and a
    bare function type has none. A `def` and not an `abbrev`, or the name would unfold away
    before the lookup. -/
def VoteTable (α : Type) := Nat → Finset α

/-- `table[k]`: the set at an index. Validity is `True` — every index has a set — so
    `get_elem_tactic` closes it with `trivial` and a read owes nothing. -/
scoped instance voteTableGetElem {α : Type} :
    GetElem (VoteTable α) Nat (Finset α) (fun _ _ => True) where
  getElem tbl k _ := tbl k

/-- The block-state map of Section 5.1. Named for the same reason as `VoteTable`. -/
def StateMap (Validator : Type) := Block Validator → Option (ChainState Validator)

/-- `B ∈ σ`: the map records a state for `B`. -/
scoped instance stateMapMembership :
    Membership (Block Validator) (StateMap Validator) where
  mem σ B := (σ B).isSome

/-- The membership is a `Bool` in disguise, so an `if B ∉ S.σ` can test it. -/
scoped instance (σ : StateMap Validator) (B : Block Validator) : Decidable (B ∈ σ) :=
  inferInstanceAs (Decidable ((σ B).isSome = true))

/-- `σ[B]`, the raising read: the state recorded for `B`, or the failure. In a `do` block
    over `ResultOrExcept`, `let σB ← S.σ[B]` propagates a block the map does not record. The
    raw `Option` stays reachable by application, `S.σ B`. -/
scoped instance stateMapGetElem :
    GetElem (StateMap Validator) (Block Validator)
      (ResultOrExcept (ChainState Validator)) (fun _ _ => True) where
  getElem σ B _ := if h : B ∈ σ then .ok ((σ B).get h) else .error .error

/-- The store (Definition 1 of the draft, with the fields Sections 3.2 and 5.1 add).

    "The store keeps messages and their arrival times, and nothing else. Every rule below is
    a timestamp comparison on this one pool." -/
structure Store (Validator : Type) where
  /-- `Σ.t`, the clock: the time the last `on_tick` set. Starts below `0` — the draft leaves
      the initial value unstated, and every scheduled instant is at least `0` — at `-1`. -/
  t : Int
  /-- `Σ.s`, the current slot, set by the same `on_tick`. -/
  s : Nat
  /-- `Σ.T`, the tree of processed blocks. -/
  T : Finset (Block Validator)
  /-- `Σ.timestamp(B)` for a block: when it was processed, `none` if it was not. Written by
      `process_block`; read by nothing, in this draft. See the module header. -/
  blockTime : Block Validator → Option Int
  /-- `Σ.gf_votes[k]`, the processed slot-`k` Goldfish votes. -/
  gfVotes : VoteTable (GoldfishVote Validator)
  /-- `Σ.timestamp(vote)` for a Goldfish vote. This is the map every Goldfish rule reads:
      the freeze in `goldfish_vote`, and both cutoffs in `update_confirmation`. -/
  gfVoteTime : GoldfishVote Validator → Option Int
  /-- `Σ.live_confirmed`, the block the last evaluated slot confirmed. -/
  liveConfirmed : Block Validator
  /-- `Σ.latest_confirmed`, the monotone record the node exposes. "No rule in this protocol
      reads it" — it is written by `update_confirmation` and nothing else touches it. -/
  latestConfirmed : Block Validator
  /-- `Σ.sg_votes[r]`, the processed round-`r` SG votes (Section 3.2). -/
  sgVotes : VoteTable (SGVote Validator)
  /-- `Σ.timestamp(vote)` for an SG vote (Section 3.2). Written by `process_sg_vote`; no
      rendered rule reads it, `latest` selecting by round rather than by time. -/
  sgVoteTime : SGVote Validator → Option Int
  /-- `Σ.σ[B]`, the stored post-state of each processed block (Section 5.1). Absent outside
      `Σ.T`; that it is defined on exactly `Σ.T` is an invariant, not a fact of the type. -/
  σ : StateMap Validator
  /-- `Σ.F`, the finalized block (Section 5.1). -/
  F : Block Validator
  /-- `Σ.h_F`, its height. -/
  h_F : Nat
  /-- `Σ.J`, the justified block rooting the fork choice (Section 5.1). -/
  J : Block Validator
  /-- `Σ.h_j`, its height. -/
  h_j : Nat
  /-- `Σ.h_max`, the greatest state height in the live tree. It "otherwise only grows", and
      is recomputed inside the new live tree whenever `Σ.F` advances. -/
  h_max : Nat

/-- The initial store: `Σ.T = {B_gen}`, `Σ.live_confirmed = Σ.latest_confirmed = B_gen`,
    "other fields are empty".

    Three values the draft fixes elsewhere, or by "empty", and this has to write out: the
    clock starts at `-1`, below every scheduled instant, since `on_tick` is what sets it; the
    genesis block's state is the initial chain state of Definition 4; and the finality caches
    start where that state does, `(B_gen, 0)` for both pairs with `h_max = 1`, since genesis
    "is justified and finalized at height 0, and every chain starts at height 1".

    Genesis has no timestamp: the draft's `−∞` and this `none` agree, nothing reading a
    block's timestamp. -/
def Store.gen [DecidableEq Validator] : Store Validator where
  t := -1
  s := 0
  T := {.genesis}
  blockTime := fun _ => none
  gfVotes := fun _ => ∅
  gfVoteTime := fun _ => none
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

/-! ## The live tree

Section 5.1's other derived set, the processed finality evidence
`E_F(Σ) = {(Σ.σ[B].F, Σ.σ[B].h_F) : B ∈ Σ.T}`, is **not** rendered: no figure reads it, and
under this subtree's rule a definition lands with its first consumer. -/

section Derived
variable [DecidableEq Validator]

/-- `T_F(Σ) = {B ∈ Σ.T : Σ.F ⪯ B}`, the *live tree*: the processed blocks at or below the
    finalized one. "It retains every processed block; the live tree is derived below the
    finalized block" — so nothing is ever removed from `Σ.T`, and this is the view every
    later rule uses in its place. -/
def Store.liveTree (S : Store Validator) : Finset (Block Validator) :=
  {B ∈ S.T | S.F ⪯ B}

end Derived

end Consensus
