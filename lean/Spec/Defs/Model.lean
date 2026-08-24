import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Lattice.Basic

/-!
# The common substrate, and the wire objects

The substrate of the specification: everything the algorithm files read and no
algorithm of their own. A definition lands here at the moment an algorithm file first
consumes it, so everything below has a consumer under `Spec/`. Docstrings are
self-contained: each definition's own text is what it means.

## What this file fixes

A fixed validator set `V`; slot `s` starts at `t_s = 4Δs` and has an assigned proposer and a
fixed committee `K_s ⊆ V`. Every block has a root, a slot and a parent, and processed blocks
form a parent-closed tree rooted at `B_gen`. `B ⪯ C` is ancestry, `B ≺ C` strict ancestry,
and two blocks are *compatible* when one is an ancestor of the other.

Three things deliberately **not** rendered, each for a reason:

* the assigned proposer. Which validator proposes in a slot is outside the protocol's scope, so
  `on_tick` takes the test as a parameter (Figure 2);
* `t_GST` and the delivery bound as a *property*. `Δ` is a constant here; that objects arrive
  within it is a fact about executions, and there is no execution layer yet;
* depth — no algorithm reads it: `ghost` breaks ties by root order, not by depth.

## `B.root` is a field of an abstract type `Root`

The protocol gives every block a root — the finality layer's post-state root — and this rendering
reads it in one place: `update_finality` compares justifications in the lex order
`(h_j, J.root)`. What a root *is* the protocol never says, so the type is abstract: the `Roots`
class carries the type, the linear order the lex comparison needs, and the root `B_gen`
carries — the protocol says "every block `B` has a root" and its genesis is a block. The
walk's tie-break is **not** read off the root: the tie is a nondeterministic pick in
`01_GoldfishWalk.lean`, every resolution among the outcomes, a root order being one.

Nothing constrains a block's root to match the post-state it would compute: the block
*claims* a root — the proposer's own claim is the assumed `RootComputation` of Figure 2 —
and whether the claim is true is a validity question this rendering does not ask, exactly as
it does not ask whether a block was signed by its slot's proposer.

Every inductive in the mutual family takes the `[Roots]` binder, `HeightPair` and
`FinalityPair` included: mutual inductives must share one parameter list, so the two that
never mention a root carry the instance anyway.

## Block equality is decided by hand

`deriving DecidableEq` does not reach a mutual family nested through `List` and `Option`;
measured. So the decision procedure is written out below, under
"Decidable equality, written out", with the soundness theorems the instances need — the one
kind of proof a `Spec/` file is allowed to hold. Nothing in this subtree is `noncomputable`.

## `⊥`

The protocol writes `⊥` for an absent block or height: the empty target, the empty head, the
absent latest round. That is `Option.none` here, given the `⊥` spelling by a scoped `Bot`
instance. Spec bodies test absence as the protocol writes it — `x ≠ ⊥`, never `.isSome` —
and a raising body extracts by the lift in `Raise.lean`, `let y ← x`.

## Extract

A fixed validator set `V` is given, each validator with a fixed positive integer weight
`w(v)`; for `S ⊆ V` write `w(S)` for the total weight, and `W = w(V)`. Slot `s` starts
at `t_s = 4Δs` and has an assigned proposer and a fixed committee `K_s ⊆ V`. After
`t_GST`, `Δ` is a strict delivery bound, and an honest node relays every object it
processes. A scheduled action uses the store immediately before its public time.

Every block `B` has a root `B.root`, slot `B.slot`, and parent `B.parent`. Processed
blocks form a parent-closed tree rooted at `B_gen`. Write `B ⪯ C` when `B = C` or `B` is
an ancestor of `C`, and `B ≺ C` for strict ancestry. Two blocks are compatible when one
is an ancestor of the other, and they conflict otherwise. The depth of a block is the
number of parent edges from genesis; "deepest" means maximum depth, ties by a fixed
root order.

Slot `s` has these public actions:

| `t_s` | proposal |
| `t_s + Δ` | Goldfish vote |
| `t_s + 2Δ` | support cutoff |
| `t_s + 3Δ` | view freeze |
| `t_s + 6Δ` | slot-`s` confirmation evaluation |

Because `t_s + 6Δ = t_{s+1} + 2Δ`, the last action is also the support action of slot
`s + 1`.

A Goldfish vote is a tuple `(v, s, B)` from validator `v ∈ K_s` with target `B`, where
`B.slot ≤ s`. A block `B` carries `B.parent`, `B.slot`, and a set `B.gf_votes` of
slot-`(B.slot − 1)` Goldfish votes. There is no proposal envelope: the block is the only
wire object a proposer emits, and `B.gf_votes` is the only relay channel in the
protocol.

-/

set_option autoImplicit false

namespace DC

/-- `⊥` for an absent block, height or head, as the protocol writes it. Scoped, so it cannot
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
  w : Validator → Nat
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

    The protocol's other thresholds are not constants: Goldfish's gate is `2·score > voters` and
    the SG gate is `2·support > W_r`, each a strict majority of a *denominator the rule
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

end Electorate


/-- Each slot's committee `K_s ⊆ V`, whose members cast that slot's Goldfish
    votes. How committees are drawn is outside the protocol's scope — a VRF, a public shuffle,
    anything — so the assignment is a class, the way `Electorate` is.

    That `K_s ⊆ V` is not enforced by the type. It is a fact about the assignment, and no
    rendered figure needs it: every rule reads `K_s` directly. -/
class Committees (Validator : Type) where
  /-- The committee of the given slot. -/
  K : Nat → Finset Validator

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
  /-- `R ≥ 1`. -/
  R_ge : 1 ≤ R
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

/-- `a_r`, each round's SG vote time: `6Δ` after the beginning of the round — the round
    begins at its opening slot `rR`, so `a_r = t_{rR} + 6Δ`. That instant is also
    `t_{rR+1} + 2Δ`, the tick at which slot `rR`'s confirmation is evaluated; the two
    actions compose (`Store.onTick`, `05_SGDuty.lean`). -/
def SGSchedule.a [Params] (r : Nat) : Int :=
  slotStart (r * Params.R) + 6 * (Params.Δ : Int)

/-! ## Roots -/

/-- The vocabulary of roots. `Root` is the type of the protocol's
    post-state roots, abstract — the protocol never says what a root is or how one is computed.
    `ord` is the linear order `update_finality`'s lex comparison `(h_j, J.root)` reads.
    `genesisRoot` is `B_gen`'s: the protocol says every block has a root, and its genesis is a
    block. The module header says what a root does and does not promise. -/
class Roots where
  /-- The type of roots. -/
  Root : Type
  /-- `B_gen`'s root. -/
  genesisRoot : Root
  /-- The linear order the lex comparison reads. -/
  ord : LinearOrder Root

export Roots (Root)

/-- The order on `Root`, as an instance. -/
scoped instance [Roots] : LinearOrder Root := Roots.ord

/-! ## The wire objects, as one mutual family

Three of the protocol's objects name each other. A block carries Goldfish votes and
attestations; a Goldfish vote names its target block; an attestation names blocks in its head
and in both of its pairs. -/

mutual

/-- A block. Genesis has no parent, slot `0`, the
    `Roots.genesisRoot` and nothing carried; every other block has a parent, a slot, a root —
    the post-state root, see the module header — a list of Goldfish votes of the *previous*
    slot, and a list of combined attestations. Chains are in bijection with their tips and
    the protocol identifies the two, so this type is both.

    `B.gf_votes` is the protocol's only relay channel: "there is no proposal envelope: the block
    is the only wire object a proposer emits".

    Three deliberate gaps against the protocol's sentences, each a fact about validity rather
    than about the datatype, and so not enforced here: a block's slot is not forced to exceed
    its parent's; the carried votes are not forced to be of slot `B.slot − 1`; and the
    proposer's signature is not modelled — proposer assignment is outside the protocol's scope,
    and whether a block was signed by its slot's proposer is a fact for the execution layer,
    when one exists. -/
inductive Block (Validator : Type) [Roots] where
  /-- `B_gen`. -/
  | genesis
  /-- Every other block. -/
  | mk (parent : Block Validator) (slot : Nat) (root : Root)
      (gfVotes : List (GoldfishVote Validator))
      (attestations : List (Attestation Validator))

/-- A Goldfish vote: the tuple `(v, s, B)` from a validator `v ∈ K_s` with
    target `B`, where `B.slot ≤ s`.

    Neither `v ∈ K_s` nor `B.slot ≤ s` is a fact of the type: they are conditions on a
    well-formed vote, every rule that counts votes tests committee membership itself, and a
    store can receive a malformed vote. The signature is not modelled; `validator` stands in
    for it, as in `Block`. -/
structure GoldfishVote (Validator : Type) [Roots] where
  /-- The voting committee member. -/
  validator : Validator
  /-- The slot the vote belongs to. -/
  slot : Nat
  /-- The block the vote targets. -/
  target : Block Validator

/-- A combined attestation: the tuple
    `(validator, round, head, height, target, finalize_height, finalize_target)` — the SG
    vote extended with the four finality-relevant fields, signed by `validator`. The height
    and finality components are carried as the protocol's two pairs, which is what makes the
    unwritable combination — a height `⊥` under a named target — unrepresentable. The
    signature itself is not modelled; the `validator` field stands in for it, as in `Block`. -/
structure Attestation (Validator : Type) [Roots] where
  /-- The signing validator. -/
  validator : Validator
  /-- The round the attestation belongs to. -/
  round : Nat
  /-- The head: a block or `⊥`, the SG vote's own field. -/
  head : Option (Block Validator)
  /-- The height pair `(height, target)`. -/
  heightPair : HeightPair Validator
  /-- The finality pair `(finalize_height, finalize_target)`. -/
  finalityPair : FinalityPair Validator

/-- An attestation's height pair `(height, target)`: a *target vote* `(h, T)` with
    `T ≠ ⊥`, an *empty-target vote* `(h, ⊥)`, or the empty pair `(⊥, ⊥)`. `(⊥, T)` is not a
    case, which is why this is an inductive type rather than two `Option` fields. -/
inductive HeightPair (Validator : Type) [Roots] where
  /-- A target vote `(h, T)`. -/
  | target (h : Nat) (T : Block Validator)
  /-- An empty-target vote `(h, ⊥)`. -/
  | emptyTarget (h : Nat)
  /-- The empty pair `(⊥, ⊥)`. -/
  | empty

/-- An attestation's finality pair: `(h_f, T_f)` with `T_f ≠ ⊥`, or the empty pair. -/
inductive FinalityPair (Validator : Type) [Roots] where
  /-- `(h_f, T_f)` with `T_f ≠ ⊥`. -/
  | pair (h : Nat) (T : Block Validator)
  /-- The empty pair. -/
  | empty

end

variable [Roots]

/-- An SG vote: the tuple `(v, r, H)` from a validator `v ∈ V` with head `H`,
    a block or `⊥`. Not part of the mutual family above, and it needs no hand-written
    equality: no block carries SG votes, so nothing nests. The protocol is explicit that they
    travel only on the wire — "blocks do not carry them, and they never enter a Goldfish vote
    set". -/
structure SGVote (Validator : Type) where
  /-- The signing validator. -/
  validator : Validator
  /-- The round the vote belongs to. -/
  round : Nat
  /-- The head: a block, or `⊥` in an adversarial vote. -/
  head : Option (Block Validator)

/-! ### Decidable equality, written out

Eight functions: `attListBeq`, `gfVoteListBeq` and `optBlockBeq` carry the `List` and
`Option` nesting, which is precisely what the deriving handler will not generate. Termination
is inferred. The `…Beq_iff` soundness theorems below are what the `DecidableEq` instances are
built from.

`SGVote` is not here: nothing nests through it, so its equality is one line off the block's,
below the section. -/

mutual

/-- Structural equality of blocks. -/
def blockBeq : Block Validator → Block Validator → Bool
  | .genesis, .genesis => true
  | .mk p s rt vs as, .mk p' s' rt' vs' as' =>
      blockBeq p p' && s == s' && decide (rt = rt') && gfVoteListBeq vs vs' && attListBeq as as'
  | _, _ => false

/-- Structural equality of Goldfish votes. -/
def gfVoteBeq : GoldfishVote Validator → GoldfishVote Validator → Bool
  | ⟨v, s, B⟩, ⟨v', s', B'⟩ => decide (v = v') && s == s' && blockBeq B B'

/-- The `List` half of the nesting, once: a block's carried Goldfish votes. -/
def gfVoteListBeq : List (GoldfishVote Validator) → List (GoldfishVote Validator) → Bool
  | [], [] => true
  | a :: as, b :: bs => gfVoteBeq a b && gfVoteListBeq as bs
  | _, _ => false

/-- Structural equality of attestations. -/
def attBeq : Attestation Validator → Attestation Validator → Bool
  | ⟨v, rd, hd, hp, fp⟩, ⟨v', rd', hd', hp', fp'⟩ =>
      decide (v = v') && rd == rd' && optBlockBeq hd hd' && heightPairBeq hp hp' &&
        finalityPairBeq fp fp'

/-- The `List` half of the nesting, again: a block's attestations, compared pairwise. -/
def attListBeq : List (Attestation Validator) → List (Attestation Validator) → Bool
  | [], [] => true
  | a :: as, b :: bs => attBeq a b && attListBeq as bs
  | _, _ => false

/-- The `Option` half of the nesting: an attestation's head. -/
def optBlockBeq : Option (Block Validator) → Option (Block Validator) → Bool
  | none, none => true
  | some a, some b => blockBeq a b
  | _, _ => false

/-- Structural equality of height pairs. -/
def heightPairBeq : HeightPair Validator → HeightPair Validator → Bool
  | .target h T, .target h' T' => h == h' && blockBeq T T'
  | .emptyTarget h, .emptyTarget h' => h == h'
  | .empty, .empty => true
  | _, _ => false

/-- Structural equality of finality pairs. -/
def finalityPairBeq : FinalityPair Validator → FinalityPair Validator → Bool
  | .pair h T, .pair h' T' => h == h' && blockBeq T T'
  | .empty, .empty => true
  | _, _ => false

end

mutual

/-- `blockBeq` decides equality of blocks. -/
theorem blockBeq_iff : ∀ (a b : Block Validator), blockBeq a b = true ↔ a = b
  | .genesis, .genesis => by simp [blockBeq]
  | .genesis, .mk .. => by simp [blockBeq]
  | .mk .., .genesis => by simp [blockBeq]
  | .mk p s rt vs as, .mk p' s' rt' vs' as' => by
      rw [blockBeq, Block.mk.injEq]
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
      rw [blockBeq_iff p p', gfVoteListBeq_iff vs vs', attListBeq_iff as as']
      simp only [beq_iff_eq, decide_eq_true_eq]
      simp only [and_assoc]

/-- `gfVoteBeq` decides equality of Goldfish votes. -/
theorem gfVoteBeq_iff : ∀ (a b : GoldfishVote Validator), gfVoteBeq a b = true ↔ a = b
  | ⟨v, s, B⟩, ⟨v', s', B'⟩ => by
      rw [gfVoteBeq, GoldfishVote.mk.injEq]
      rw [Bool.and_eq_true, Bool.and_eq_true]
      rw [blockBeq_iff B B']
      simp only [beq_iff_eq, decide_eq_true_eq]
      simp only [and_assoc]

/-- `gfVoteListBeq` decides equality of Goldfish-vote lists. -/
theorem gfVoteListBeq_iff :
    ∀ (a b : List (GoldfishVote Validator)), gfVoteListBeq a b = true ↔ a = b
  | [], [] => by simp [gfVoteListBeq]
  | [], _ :: _ => by simp [gfVoteListBeq]
  | _ :: _, [] => by simp [gfVoteListBeq]
  | a :: as, b :: bs => by
      rw [gfVoteListBeq, Bool.and_eq_true, gfVoteBeq_iff a b, gfVoteListBeq_iff as bs]
      simp

/-- `attBeq` decides equality of attestations. -/
theorem attBeq_iff : ∀ (a b : Attestation Validator), attBeq a b = true ↔ a = b
  | ⟨v, rd, hd, hp, fp⟩, ⟨v', rd', hd', hp', fp'⟩ => by
      rw [attBeq, Attestation.mk.injEq]
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
      rw [optBlockBeq_iff hd hd', heightPairBeq_iff hp hp', finalityPairBeq_iff fp fp']
      simp only [beq_iff_eq, decide_eq_true_eq]
      simp only [and_assoc]

/-- `attListBeq` decides equality of attestation lists. -/
theorem attListBeq_iff :
    ∀ (a b : List (Attestation Validator)), attListBeq a b = true ↔ a = b
  | [], [] => by simp [attListBeq]
  | [], _ :: _ => by simp [attListBeq]
  | _ :: _, [] => by simp [attListBeq]
  | a :: as, b :: bs => by
      rw [attListBeq, Bool.and_eq_true, attBeq_iff a b, attListBeq_iff as bs]
      simp

/-- `optBlockBeq` decides equality of optional blocks. -/
theorem optBlockBeq_iff : ∀ (a b : Option (Block Validator)), optBlockBeq a b = true ↔ a = b
  | none, none => by simp [optBlockBeq]
  | none, some _ => by simp [optBlockBeq]
  | some _, none => by simp [optBlockBeq]
  | some a, some b => by rw [optBlockBeq, blockBeq_iff a b]; simp

/-- `heightPairBeq` decides equality of height pairs. -/
theorem heightPairBeq_iff : ∀ (a b : HeightPair Validator), heightPairBeq a b = true ↔ a = b
  | .target h T, .target h' T' => by
      rw [heightPairBeq, Bool.and_eq_true, blockBeq_iff T T']
      simp only [beq_iff_eq, HeightPair.target.injEq]
  | .emptyTarget _, .emptyTarget _ => by simp [heightPairBeq]
  | .empty, .empty => by simp [heightPairBeq]
  | .target .., .emptyTarget _ => by simp [heightPairBeq]
  | .target .., .empty => by simp [heightPairBeq]
  | .emptyTarget _, .target .. => by simp [heightPairBeq]
  | .emptyTarget _, .empty => by simp [heightPairBeq]
  | .empty, .target .. => by simp [heightPairBeq]
  | .empty, .emptyTarget _ => by simp [heightPairBeq]

/-- `finalityPairBeq` decides equality of finality pairs. -/
theorem finalityPairBeq_iff :
    ∀ (a b : FinalityPair Validator), finalityPairBeq a b = true ↔ a = b
  | .pair h T, .pair h' T' => by
      rw [finalityPairBeq, Bool.and_eq_true, blockBeq_iff T T']
      simp only [beq_iff_eq, FinalityPair.pair.injEq]
  | .empty, .empty => by simp [finalityPairBeq]
  | .pair .., .empty => by simp [finalityPairBeq]
  | .empty, .pair .. => by simp [finalityPairBeq]

end

instance : DecidableEq (Block Validator) := fun a b => decidable_of_iff _ (blockBeq_iff a b)

instance : DecidableEq (GoldfishVote Validator) :=
  fun a b => decidable_of_iff _ (gfVoteBeq_iff a b)

instance : DecidableEq (Attestation Validator) :=
  fun a b => decidable_of_iff _ (attBeq_iff a b)

instance : DecidableEq (HeightPair Validator) :=
  fun a b => decidable_of_iff _ (heightPairBeq_iff a b)

instance : DecidableEq (FinalityPair Validator) :=
  fun a b => decidable_of_iff _ (finalityPairBeq_iff a b)

/-- SG votes need no hand-written equality: nothing nests through them, so once blocks are
    decidable the structure's own fields are. Written out rather than derived only because
    `deriving` runs at the declaration, which is above this section. -/
instance : DecidableEq (SGVote Validator) := fun a b =>
  decidable_of_iff (a.validator = b.validator ∧ a.round = b.round ∧ a.head = b.head)
    (by cases a; cases b; simp)

/-- A wire message: what a duty broadcasts. The protocol's wire objects as one type — the
    shape a lean-sts protocol wants, one message type per protocol — so a duty's step result
    can name what it sends. The equality instance is derived, sitting below the
    hand-written ones it needs.

    Attestations travel on the wire: a signed attestation goes from signer to proposer,
    so `Store.fgVote` can be a duty that broadcasts what it signs, and a block carries
    the ones its proposer includes. -/
inductive Message (Validator : Type) [Roots] where
  /-- A proposed block. -/
  | block (B : Block Validator)
  /-- A Goldfish vote. -/
  | gfVote (v : GoldfishVote Validator)
  /-- An SG vote. -/
  | sgVote (v : SGVote Validator)
  /-- An attestation, traveling from signer to proposer. -/
  | attestation (a : Attestation Validator)
deriving DecidableEq


namespace Block

/-- `B.parent`, `⊥` at genesis. -/
def parent : Block Validator → Option (Block Validator)
  | .genesis => ⊥
  | .mk p _ _ _ _ => some p

/-- `B.slot`. Genesis is at slot 0. -/
def slot : Block Validator → Nat
  | .genesis => 0
  | .mk _ s _ _ _ => s

/-- `B.root`, the post-state root; `Roots.genesisRoot` at genesis. See the module header on
    what the root is for and what carrying one does not promise. -/
def root : Block Validator → Root
  | .genesis => Roots.genesisRoot
  | .mk _ _ rt _ _ => rt

/-- `B.gf_votes`, the carried Goldfish votes of slot `B.slot − 1`. Empty at genesis. -/
def gfVotes : Block Validator → List (GoldfishVote Validator)
  | .genesis => []
  | .mk _ _ _ vs _ => vs

/-- `B.attestations`. Empty at genesis. -/
def attestations : Block Validator → List (Attestation Validator)
  | .genesis => []
  | .mk _ _ _ _ as => as

end Block

/-! ## Ancestry -/

/-- The block and all of its ancestors, nearest first. Structural recursion on the parent
    link, so `⪯` needs no termination argument and no slot hypothesis. -/
def ancestors : Block Validator → List (Block Validator)
  | .genesis => [.genesis]
  | .mk p s rt vs as => .mk p s rt vs as :: ancestors p

/-- `B ⪯ C`: `B = C`, or `B` is an ancestor of `C` — the protocol's reflexive
    ancestry. -/
def Preceq (a b : Block Validator) : Prop := a ∈ ancestors b

@[inherit_doc] scoped infix:50 " ⪯ " => Preceq

instance : DecidableRel (Preceq (Validator := Validator)) :=
  fun a b => inferInstanceAs (Decidable (a ∈ ancestors b))

/-- `B ≺ C`: strict ancestry — `B ⪯ C` and `B ≠ C`. `C` is a *descendant* of `B` when
    `B ⪯ C`, so descendant is reflexive and `≺` is the strict half. -/
def Prec (a b : Block Validator) : Prop := a ⪯ b ∧ a ≠ b

@[inherit_doc] scoped infix:50 " ≺ " => Prec

instance : DecidableRel (Prec (Validator := Validator)) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- `B ∼ C`: *compatible* — `B ⪯ C` or `C ⪯ B`, the two lie on one chain. The protocol's
    blocks *conflict* otherwise; no named relation renders that, `¬ ∼` sufficing so far. -/
def Compatible (a b : Block Validator) : Prop := a ⪯ b ∨ b ⪯ a

@[inherit_doc] scoped infix:50 " ∼ " => Compatible

instance : DecidableRel (Compatible (Validator := Validator)) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

end DC
