import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Lattice.Basic

/-!
# The common substrate, and the wire objects

The substrate of the specification: everything the algorithm files read and no
algorithm of their own. A definition lands here at the moment an algorithm file first
consumes it, so everything below has a consumer under `Spec/` — save `BlockTree`, which
waits for the walks it is meant for. Docstrings are
self-contained: each definition's own text is what it means.

## What this file fixes

A fixed validator set `V`; slot `s` starts at `t_s = 4Δs` and has an assigned proposer and a
fixed committee `K_s ⊆ V`. Every block has a slot, a proposer, and its parent's *identifier*; the
blocks a node has processed form a parent-closed tree rooted at `B_gen`. Ancestry — `B ⪯ C`,
`B ≺ C`, and compatibility — is therefore a question about a store rather than about two
values, and lives in `Defs/Store.lean`.

Two things deliberately **not** rendered, each for a reason:

* `t_GST` and the delivery bound as a *property*. `Δ` is a constant here; that objects arrive
  within it is a fact about executions, and there is no execution layer yet;
* depth — no algorithm reads it: the walk's tie is a pick, and "the deepest block" of a
  set is its `⪯`-maximal one (`deepest`, `09_Healing.lean`), no depth measure involved.

## Blocks carry no root

The protocol's blocks carry a post-state root, read in one place: `update_finality`'s lex
comparison of justification events. With blocks named by identifier, the identifier is the
fixed tie-break that comparison needs — `BlockIds` carries the linear order — and a root
field would go unread, so no rendering of roots remains: not the field, not the abstract
type, not the assumed computation a proposer would fill the field with. Whether a block's
claimed root matches the post-state it evaluates to was in any case a validity question
this rendering never asked, exactly as it does not ask whether a block was signed by its
slot's proposer — `B.proposer` is a carried claim, and `state_transition`'s assertion
about it is enforced at `process_block`'s admission (`07_FGStore.lean`).

## A block is named, not embedded

A block carries its parent's identifier, not its parent. `BlockIds` fixes the type of
identifiers — abstract, as `Root` is, and in an implementation a hash — and `BlockIdentity`,
which cannot be stated until `Block` exists, supplies the injective `id` computing a block's
own. Injectivity is the one thing assumed about identifiers, and the reason a vote naming `b`
names one block.

Two consequences run through the whole file. Nothing nests, so every equality is
`deriving DecidableEq` and no decision procedure is written by hand. And `HeightPair` and
`FinalityPair` no longer mention `Validator` at all, so they no longer take the parameter.

`B_gen` is a definition rather than a constructor, so genesis is never a case to match on.

## `⊥`

The protocol writes `⊥` for an absent block or height: the empty target, the empty
confirmed block, the
absent latest round. That is `Option.none` here, given the `⊥` spelling by a scoped `Bot`
instance. Spec bodies test absence as the protocol writes it — `x ≠ ⊥`, never `.isSome` —
and a raising body extracts by the lift in `Raise.lean`, `let y ← x`.

## Extract

A fixed validator set `V` is given, each validator with a fixed positive integer weight
`w(v)`; for `S ⊆ V` write `w(S)` for the total weight, and `W = w(V)`. Slot `s` starts
at `t_s = 4Δs` and has an assigned proposer and a fixed committee `K_s ⊆ V`. After
`t_GST`, `Δ` is a strict delivery bound, and an honest node relays every object it
processes. A scheduled action uses the store immediately before its public time.

Every block `B` has a slot `B.slot`, a proposer `B.proposer`, and an identifier `B.id`,
and names
its parent by identifier: `B.parent`, absent at `B_gen`. Distinct blocks have distinct
identifiers. Processed blocks form a parent-closed tree rooted at `B_gen`. Write `B ⪯ C`
when `B = C` or `B` is an ancestor of `C`, and `B ≺ C` for strict ancestry — both read
off the parent links a node has processed. Two blocks are compatible when one is an
ancestor of the other, and they conflict otherwise. The deepest block of a set is one
with no strict descendant in it; where the protocol uses the phrase, the set lies on one
chain, so there is exactly one.

Slot `s` has these public actions:

| `t_s` | proposal |
| `t_s + Δ` | Goldfish vote |
| `t_s + 2Δ` | support cutoff |
| `t_s + 3Δ` | view freeze |
| `t_s + 6Δ` | slot-`s` confirmation evaluation |

Because `t_s + 6Δ = t_{s+1} + 2Δ`, the last action is also the support action of slot
`s + 1`.

A Goldfish vote is a tuple `(v, s, B)` from validator `v ∈ K_s` naming the target `B`,
where `B.slot ≤ s`. A block `B` carries `B.parent`, `B.slot`, and a set `B.gf_votes` of
slot-`(B.slot − 1)` Goldfish votes. There is no proposal envelope: the block is the only
wire object a proposer emits, and `B.gf_votes` is the only relay channel in the
protocol.

-/

set_option autoImplicit false

namespace DC

/-- `⊥` for an absent block, height or confirmed block, as the protocol writes it. Scoped, so it cannot
    leak into a file that means something else by `⊥`. -/
scoped instance {α : Type} : Bot (Option α) := ⟨none⟩

/-! ## Validators and weights -/

/-- The protocol's model of validators: a fixed set `V`, and a fixed positive integer weight
    `w(i)` for each member.

    A class, so that `w(·)`, `W` and `q` read as the protocol writes them with no parameter
    threaded through every signature. -/
class Electorate (Validator : Type) where
  /-- The validator set `V`. -/
  V : Finset Validator
  /-- Validator `i`'s fixed weight `w(i)`. -/
  w : (i : Validator) → Nat
  /-- Weights are positive. -/
  w_pos : ∀ i ∈ V, 0 < w i

variable {Validator : Type} [DecidableEq Validator]

-- one section, the file's only one: `[Electorate]` scoped to its consumers, or it rides
-- along unused into every later declaration that mentions `Validator`
section Electorate
variable [Electorate Validator]

/-- `w(S) = ∑_{i ∈ S} w(i)`. -/
def weight (S : Finset Validator) : Nat := ∑ i ∈ S, Electorate.w i

@[inherit_doc] scoped notation:max "w(" S ")" => weight S


/-- `W = w(V)`, the total weight. -/
def W (Validator : Type) [Electorate Validator] : Nat :=
  w(Electorate.V (Validator := Validator))

/-- `q = ⌈2W/3⌉`, the finality layer's quorum threshold, written in `Nat` arithmetic. A set is a
    quorum when its weight is at least `q`.

    The vote rules' thresholds are not constants: Goldfish's is `2·score > voters` and the
    SG rule's is `2·support > W_r`, each a strict majority of a *denominator the rule
    computes*, so each is written where it is used. -/
def q (Validator : Type) [Electorate Validator] : Nat := (2 * W Validator + 2) / 3

/-- `S` is a *quorum*: `w(S) ≥ q`.

    A predicate taking the set, rather than a bare `q`: `W` and `q` are constants of the
    electorate and nothing in their types mentions `Validator`, so written bare they leave
    the electorate undetermined. The notation below restores the protocol's spelling at the use
    site. -/
def Quorum (S : Finset Validator) : Prop := w(S) ≥ q Validator

@[inherit_doc] scoped notation:50 "w(" S ")≥q" => Quorum S

instance (S : Finset Validator) : Decidable (Quorum S) := inferInstanceAs (Decidable (_ ≥ _))

/-- `m = ⌊W/2⌋ + 1`, the majority threshold, written in `Nat` arithmetic: a weight of at
    least `m` is a strict majority of the total weight `W`. The healing layer's grades
    (`09_Healing.lean`) compare support scores against it. -/
def m (Validator : Type) [Electorate Validator] : Nat := W Validator / 2 + 1

end Electorate


/-- Each slot's committee `K_s ⊆ V`, whose members cast that slot's Goldfish
    votes. How committees are drawn is outside the protocol's scope — a VRF, a public shuffle,
    anything — so the assignment is a class, the way `Electorate` is.

    That `K_s ⊆ V` is not enforced by the type. It is a fact about the assignment, and no
    rendered figure needs it: every rule reads `K_s` directly. -/
class Committees (Validator : Type) where
  /-- The committee of the given slot. -/
  K : (s : Nat) → Finset Validator

/-- Each slot's assigned proposer. How proposers are drawn is outside the protocol's
    scope, as committees are, so the assignment is a class — and `state_transition`'s
    assertion `B.proposer = proposer(B.slot)`, together with `on_tick`'s "is `ℓ` the
    slot-`s` proposer" test, is what reads it. -/
class Proposers (Validator : Type) where
  /-- The assigned proposer of the given slot. -/
  proposer : (s : Nat) → Validator

/-! ## The protocol constants, the schedule, and rounds -/

/-- The protocol's constants.

    `Δ` is the delivery bound, and every scheduled instant is a multiple of it. `R` is the
    round length. `K` and `D` are the finality layer's nonjustifiability constants: on entry into
    a height, `nj ← (K ∣ h) ∧ (h − h_F > D)` — in this protocol a *stored* flag on the chain
    state. `ηSG` is the SG expiry window `latest` reads, in rounds. -/
class Params where
  /-- The delivery bound. -/
  Δ : Nat
  /-- The number of slots in a round. -/
  R : Nat
  /-- Every `K`-th height is eligible to be nonjustifiable. -/
  K : Nat
  /-- Justification is disabled at such a height only once `h − h_F` exceeds this. -/
  D : Nat
  /-- The SG expiry window, in rounds. -/
  ηSG : Nat
  /-- `Δ > 0`. -/
  Δ_pos : 0 < Δ
  /-- `R ≥ 2`: the round's action instant `a_r` lands inside the round's own second
      slot. -/
  R_ge : 2 ≤ R
  /-- `K ≥ 2`. -/
  K_ge : 2 ≤ K
  /-- `D ≥ 1`. -/
  D_ge : 1 ≤ D
  /-- `ηSG ≥ 1`. -/
  ηSG_ge : 1 ≤ ηSG

/-- `t_s = 4Δs`, the start of slot `s`. An `Int`, because these instants are
    compared against the store's clock, which starts below zero. -/
def slotStart [Params] (s : Nat) : Int := 4 * (Params.Δ : Int) * (s : Int)

/-- `round(s) = ⌊s/R⌋`, the round of slot `s`. Round `r` consists of slots
    `rR, …, rR + R − 1`, and slot `rR` is its *opening slot*. -/
def round [Params] (s : Nat) : Nat := s / Params.R

/-- The opening slot of round `r`: the first of the `R` slots the round consists of, `rR`. -/
def openingSlot [Params] (r : Nat) : Nat := r * Params.R

/-- The start of round `r`: the start of its opening slot, `t_{rR}`. -/
def roundStart [Params] (r : Nat) : Int := slotStart (openingSlot r)

/-- `Γ_j`, the grade instants of round `r`: `Γ_j = roundStart r + jΔ`. Round `r` grades
    the received round-`(r−1)` attestations at its four grade instants, `j ∈ {−1, 0, 1, 2}`
    (`09_Healing.lean`); the definition is total over `j`, and only those four are the
    protocol's. -/
def Γ [Params] (j : Int) (r : Nat) : Int := roundStart r + j * (Params.Δ : Int)

/-- The round's action instant: `2Δ` into the round's second slot, which is the tick at
    which the opening slot's confirmation is evaluated. One fixed time per round, at which the
    validator settles what it will sign for the round — this spec decides the FG vote's two
    pairs there (`Store.onTick`, `11_Duties.lean`, through `get_fg_vote` and the client
    rules of `08_FinalityVote.lean`), which is what the name says, while the attestation
    carrying them goes out later, at the validator's own `sgfgVoting` time below, with the
    SG head computed then.

    Written from the slot rather than as `roundStart r + 6Δ`, the two being the same instant,
    because what the choice of instant rests on is the confirmation: the FG vote is
    decided against a confirmation computed in the same tick (`Store.onTick`,
    `11_Duties.lean`). The round's second slot exists because `Params` requires `R ≥ 2`.

    The formula is fixed, so this is a definition and not a field of `SGSchedule` below. That
    class carries the part of the schedule the protocol leaves open, and no instance should be
    able to move this instant. Taking `[Params]` alone, it also mentions no validator, so a
    routine tests it without carrying the class. -/
def heightDecisionTime [Params] (r : Nat) : Int :=
  slotStart (openingSlot r + 1) + 2 * (Params.Δ : Int)

/-- The assumed part of the round schedule (`heightDecisionTime`, above, is the fixed
    part): the time
    each validator sends its attestation (`Attestation`, below) for each round — a
    public parameter of the protocol, no formula fixed, and a public parameter is
    exactly an ambient class, as `Committees` is. The assignment is total: every
    validator has an attestation time in every round. Two constraints bound each time,
    `sgfgVoting_ge` and `sgfgVoting_lt`: it is at or after the round's SG vote time and
    before the next round begins, `a_r ≤ sgfgVoting i r < roundStart (r + 1)`. -/
class SGSchedule (Validator : Type) [Params] where
  /-- The time validator `i` sends its attestation for round `r`. -/
  sgfgVoting : (i : Validator) → (r : Nat) → Int
  /-- No attestation time precedes the round's SG vote time:
      `a_r ≤ sgfgVoting i r`. -/
  sgfgVoting_ge : ∀ (i : Validator) (r : Nat), heightDecisionTime r ≤ sgfgVoting i r
  /-- Every attestation time falls before the next round begins:
      `sgfgVoting i r < roundStart (r + 1)`. -/
  sgfgVoting_lt : ∀ (i : Validator) (r : Nat), sgfgVoting i r < roundStart (r + 1)

/-- The type a block is named by. A block does not carry it: it is computed from the block,
    by the injective function `BlockIdentity` supplies once `Block` exists. What a block *does*
    carry is its parent's identifier, so nothing on the wire carries a block and no walk is
    possible where the store lacks an ancestor.

    The type is assumed with no formula — in an implementation an identifier is a
    hash — and this class carries what the rules ask of it: the type, the decision
    every rule that compares two identifiers needs, and a linear order — the fixed
    tie-break `update_finality`'s lex comparison of justification events reads, where the
    protocol compares post-state roots and this rendering carries none (the module
    header says why). -/
class BlockIds where
  /-- The type of identifiers. -/
  BlockId : Type
  /-- Identifiers are distinguishable. -/
  decEq : DecidableEq BlockId
  /-- The linear order the lex comparison reads. -/
  ord : LinearOrder BlockId

export BlockIds (BlockId)

/-- Equality on `BlockId`, as an instance. -/
scoped instance [BlockIds] : DecidableEq BlockId := BlockIds.decEq

/-- The order on `BlockId`, as an instance. -/
scoped instance [BlockIds] : LinearOrder BlockId := BlockIds.ord

/-! ## The wire objects

Nothing nests. A block names its parent by identifier, a Goldfish vote names its target by
identifier, and an attestation names identifiers in its confirmed block and in both of its pairs. So each
type stands alone, declared in dependency order, and `deriving DecidableEq` writes every
equality. -/

/-- A Goldfish vote: the tuple `(v, s, p)` from a validator `v ∈ K_s` naming the target `p`,
    whose slot is at most `s`.

    None of it is a fact of the type — not `v ∈ K_s`, not the slot condition, not even that any
    processed block answers to `b`. Each is a condition on a well-formed vote, and a store can
    receive a malformed one: `process_goldfish_vote` is where committee membership is tested,
    once, at admission. The signature is not modelled; `validator` stands in for it. -/
structure GoldfishVote (Validator : Type) [BlockIds] where
  /-- The voting committee member. -/
  validator : Validator
  /-- The slot the vote belongs to. -/
  slot : Nat
  /-- The identifier of the block the vote targets. -/
  target : BlockId
deriving DecidableEq

/-- An attestation's height pair `(height, target)`: a *target vote* `(h, T)` with
    `T ≠ ⊥`, an *empty-target vote* `(h, ⊥)`, or the empty pair `(⊥, ⊥)`. `(⊥, T)` is not a
    case, which is why this is an inductive type rather than two `Option` fields. -/
inductive HeightPair [BlockIds] where
  /-- A target vote `(h, T)`. -/
  | target (h : Nat) (T : BlockId)
  /-- An empty-target vote `(h, ⊥)`. -/
  | emptyTarget (h : Nat)
  /-- The empty pair `(⊥, ⊥)`. -/
  | empty
deriving DecidableEq

/-- An attestation's finality pair: `(h_f, T_f)` with `T_f ≠ ⊥`, or the empty pair. -/
inductive FinalityPair [BlockIds] where
  /-- `(h_f, T_f)` with `T_f ≠ ⊥`. -/
  | pair (h : Nat) (T : BlockId)
  /-- The empty pair. -/
  | empty
deriving DecidableEq

/-- A combined attestation: the tuple
    `(validator, round, confirmed, height, target, finalize_height, finalize_target)` — the SG
    vote extended with the four finality-relevant fields, signed by `validator`. The height
    and finality components are carried as the protocol's two pairs, which is what makes the
    unwritable combination — a height `⊥` under a named target — unrepresentable. The
    signature itself is not modelled; the `validator` field stands in for it. -/
structure Attestation (Validator : Type) [BlockIds] where
  /-- The signing validator. -/
  validator : Validator
  /-- The round the attestation belongs to. -/
  round : Nat
  /-- `confirmed`: the confirmed block's identifier or `⊥`, the SG vote's own field. -/
  confirmed : Option BlockId
  /-- The height pair `(height, target)`. -/
  heightPair : HeightPair
  /-- The finality pair `(finalize_height, finalize_target)`. -/
  finalityPair : FinalityPair
deriving DecidableEq

/-- A block: its parent's identifier — `⊥` at `B_gen` — a slot, its proposer, the Goldfish
    votes of the *previous* slot, and the combined
    attestations its proposer included.

    `B.gf_votes` is the protocol's only relay channel: there is no proposal envelope, the block
    being the only wire object a proposer emits.

    A block is no longer its own chain. It names one block, by identifier, and what that
    identifier resolves to is a question for a store — which is why ancestry lives with the
    store (`Defs/Store.lean`) and not here.

    Four deliberate gaps against the protocol's sentences, each a fact about validity rather
    than about the datatype, and so not enforced here: a block's slot is not forced to exceed
    its parent's and its proposer is not forced to be its slot's — both are
    `state_transition` assertions, enforced at `process_block`'s admission; the carried
    votes are not forced to be of slot `B.slot − 1`; nothing forces a
    parent to exist at all; and the proposer's signature is not modelled — whether a block was
    signed by its slot's proposer is a fact for the execution layer, when one exists. -/
structure Block (Validator : Type) [BlockIds] where
  /-- The parent's identifier, `⊥` at `B_gen`. -/
  parent : Option BlockId
  /-- The slot the block belongs to. -/
  slot : Nat
  /-- The proposing validator, `⊥` at `B_gen`. A carried claim, as every field is. -/
  proposer : Option Validator
  /-- The carried Goldfish votes, of slot `B.slot − 1`. -/
  gfVotes : List (GoldfishVote Validator)
  /-- The combined attestations the proposer included. -/
  attestations : List (Attestation Validator)
deriving DecidableEq

/-- `B_gen`: no parent, slot `0`, no proposer, nothing carried. A definition rather
    than a constructor, so genesis is never a case to match on, and its identifier is derived
    like every other block's — `Block.genesis.id`, with nothing assumed about it. -/
def Block.genesis {Validator : Type} [BlockIds] : Block Validator where
  parent := ⊥
  slot := 0
  proposer := ⊥
  gfVotes := []
  attestations := []

/-- What names a block. `id` is the function every wire object's identifier comes from, and
    `id_inj` says distinct blocks are named distinctly.

    That injectivity is the whole content of the class, and it is what separates an identifier
    from a root: a root is a *claim* a block carries and nothing checks, while an identifier is
    computed from the block. The protocol leans on it — a vote naming `b` must name one block,
    or `Σ.T[b]` is not a lookup — so it is assumed, and it is the only thing assumed.

    In an implementation `id` is a hash, and injectivity is collision-freedom. This class comes
    after `Block` because it cannot be stated before; `BlockIds`, which `Block` itself needs,
    carries only the type. -/
class BlockIdentity (Validator : Type) [BlockIds] where
  /-- The identifier a block is named by. -/
  id : Block Validator → BlockId
  /-- Distinct blocks are named distinctly. -/
  id_inj : Function.Injective id

/-- `B.id`, the identifier `B` is named by. -/
abbrev Block.id {Validator : Type} [BlockIds] [BlockIdentity Validator]
    (B : Block Validator) : BlockId :=
  BlockIdentity.id B

/-- `B_gen`'s identifier. Derived like every other, nothing assumed about it. Written out with
    the validator type, because `Block.genesis.id` leaves it undetermined: the type of an
    identifier does not mention `Validator`, so nothing in the expression fixes which `id` is
    meant. -/
abbrev genesisId (Validator : Type) [BlockIds] [BlockIdentity Validator] : BlockId :=
  (Block.genesis : Block Validator).id

/-- A wire message: what a duty broadcasts. The protocol's wire objects as one type — the
    shape a lean-sts protocol wants, one message type per protocol — so a duty's step result
    can name what it sends.

    There is no standalone SG-vote message: the SG vote is the `(validator, round, confirmed)`
    projection of an attestation, and the attestation is what travels. -/
inductive Message (Validator : Type) [BlockIds] where
  /-- A proposed block. -/
  | block (B : Block Validator)
  /-- A Goldfish vote. -/
  | gfVote (v : GoldfishVote Validator)
  /-- An attestation. -/
  | attestation (a : Attestation Validator)
deriving DecidableEq

variable [BlockIds]

namespace HeightPair

/-- The height a height pair signs; `⊥` for the empty pair. -/
def h : HeightPair → Option Nat
  | .target height _ => some height
  | .emptyTarget height => some height
  | .empty => ⊥

/-- The named target a height pair signs; `⊥` for an empty-target vote and for the empty
    pair. -/
def T : HeightPair → Option BlockId
  | .target _ b => some b
  | .emptyTarget _ => ⊥
  | .empty => ⊥

end HeightPair

namespace FinalityPair

/-- The height a finality pair signs; `⊥` for the empty pair. -/
def h : FinalityPair → Option Nat
  | .pair height _ => some height
  | .empty => ⊥

/-- The target a finality pair signs; `⊥` for the empty pair. -/
def T : FinalityPair → Option BlockId
  | .pair _ b => some b
  | .empty => ⊥

end FinalityPair

/-! ## A rooted set of blocks -/

/-- A block tree: a root, and the blocks a walk may descend through, both named by
    identifier. The two travel together — every walk in the protocol starts at a root and takes
    its children from a set, and each layer supplies its own pair. The blocks themselves come
    from the store the walk runs against.

    Nothing is enforced. That the root lies in `blocks`, that `blocks` is closed under
    parents, that it is a tree at all: each is a fact about the pairs the protocol builds,
    for `Analysis/` to state, not a fact of this type. A walk over a pair that is none of
    those things still runs; it simply answers what its own steps say. -/
structure BlockTree [BlockIds] where
  /-- The identifier a walk starts from. -/
  root : BlockId
  /-- The identifiers it may descend through. -/
  blocks : Finset BlockId
deriving DecidableEq

end DC
