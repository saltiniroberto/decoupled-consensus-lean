import Spec.Consensus.Fig1StateTransition
import Spec.Consensus.Raise

/-!
# Figure 2 — Finality store

The store of Definition 7, the candidate tree, root and head of Definition 8, and Figure 2's
five handlers: `on_slot`, `on_block`, `process_updates`, `fork_choice_root` and `get_head`.
A node tracks the blocks it has accepted and the finality values that root its fork choice;
blocks are replayed with Figure 1's `stateTransition`.

The `-- line n` comments use Figure 2's own line numbering, in the draft as of 2026-08-19.
The routines appear callee-first; the figure's order is `on_slot`, `on_block`,
`process_updates`, `fork_choice_root`, `get_head`.

## The draft's `Σ` is written `S`

`Σ` is a reserved token in Lean (the dependent-pair binder), not a usable identifier.
Store-valued variables are named `S` throughout, and nothing else in this subtree uses that
letter for a Lean binder.

## The state map is `Option`-valued

Definition 7 has `σ[·]` assign each accepted block its post-state. A total function
`Block → ChainState` would invent states for unaccepted blocks, so the field is
`Block → Option (ChainState Validator)` and an unaccepted block maps to `none`. That the
map is defined exactly on `T` is then a fact to prove about reachable stores, not a fact of
the type.

## `root_proposal[r]` registers only a nonempty root

The field is `Nat → Option (Block Validator)`: `none` until a round-`r` opening block
carrying a nonempty proposal root is processed, then that first root, permanently.
Definition 13 as drafted lets the round's *first* opening block claim the entry even with
`⊥`; conditioning the write on a nonempty root instead (Roberto, 2026-08-20) is what keeps
this a single `Option` — a two-level `Option` distinguishing "unset" from "set to `⊥`"
preceded it, and git history has it. The two rules differ only under an equivocating
opening proposer whose first-processed block carries `⊥`: the draft's rule then pins `⊥`,
this one adopts the equivocator's later nonempty root. The paper sentence to match is "the
proposal root of the first round-`r` opening block carrying one". The field is
Definition 10's; it lands here because Figure 2's `on_block` is its first writer.

## Two `let some … | return S` lines in `on_block`, both the reject exit

A parentless `B` — genesis — is the figure's `B.parent ∉ Σ.T` case, taken before the slot
test rather than inside line 7's disjunction; the effect is the same, the store unchanged.
And the parent's recorded state is read through the map's `Option`, so a parent in `T`
that the map misses also rejects — unreachable once the map-domain coherence invariant is
proved, the same seam the old rendering documents.

## What is general lives elsewhere

Two things were carved out on 2026-08-21, so that this file says what Figure 2 says: the
failure vocabulary — one payload-free `Error`, and `ResultOrExcept` — is in `Raise.lean`, and
`Finset.filterM`, the filter that propagates a monad's effect, is in `FinsetM.lean`. Neither
renders anything of the draft. What stays here is the state map's own reads, `B ∈ S.σ` and
`S.σ[B]`, because the map is Definition 7's field.

## Totality, and the one way a handler fails

A block that fails admission leaves the store unchanged — except for the root-proposal
registration of lines 5–6, which the figure runs *before* the admission test, and this
rendering does too. So admission is not a failure.

What *is* a failure: reading the state map at a block it does not record. `viableLeaves`
does that per leaf, so `process_updates`, `on_block`, `get_head` and the candidate tree all
return `ResultOrExcept`, and a missing entry propagates to the caller instead of being
silently read as "not viable" (Roberto, 2026-08-21; the total reading is commit `ebd7626`).
On a store that keeps the map defined on every accepted block — the coherence invariant,
which `Analysis/` proves of every reachable store — no handler here can fail.
-/

set_option autoImplicit false

namespace Consensus

variable {Validator Ω : Type}

/-- What can be done with the draft's `Ω`: choose one block from a nonempty set. The
    subtype carries the membership proof, so anything chosen is one of the candidates —
    Definition 8's `get_head(Σ, Ω) ∈ C(Σ)`.

    Unspecified: only the input and output types are given, and the draft's Section 5 is
    what will say how the choice is made. A class rather than an `opaque` definition so
    that it stays computable relative to an instance — an `opaque` chooser would need to
    produce an element of a nonempty `Finset`, whose only witness is `Exists.choose`, and
    that makes every caller `noncomputable` (measured 2026-08-21). -/
class Selection (Validator Ω : Type) where
  /-- Choose from a nonempty set, using the validator's available-chain data. -/
  select : Ω → (s : Finset (Block Validator)) → s.Nonempty → {B // B ∈ s}

/-- The store (Definition 7 of the draft), in the draft's field order:
    `Σ = (s, T, σ[·], F, J, h_j, h_max)` — written `S`, see the module header — plus
    Definition 10's timed extension `(t, head[·], equiv[·], root_proposal[·], sg_root[·],
    action_root[·])`, the draft's `Σ += (…)`, landed field by field as Figures 2 and 4–6
    consumed it. Initially the per-round maps are empty; the scheduled hooks fill each
    round's entries, fixed after their scheduled writes. -/
structure Store (Validator Ω : Type) where
  /-- `s`, the current slot. -/
  s : Nat
  /-- `T`, the tree of accepted blocks. -/
  T : Finset (Block Validator)
  /-- `σ[·]`, the state map: the post-state of each accepted block, `none` on a block
      outside `T` — see the module header. Read `S.σ B`. -/
  σ : Block Validator → Option (ChainState Validator)
  /-- `F`, the finalized block the store has adopted. Always accepted. -/
  F : Block Validator
  /-- `J`, the justified block rooting the store's fork choice. Always accepted. -/
  J : Block Validator
  /-- `h_j`, the height of the justified pair `(J, h_j)`. -/
  h_j : Nat
  /-- `h_max`, the greatest state-height the store has ever accepted. -/
  h_max : Nat
  /-- `root_proposal[·]` (Definition 10; here because `on_block` writes it): per round,
      `none` until an opening block of that round carrying a nonempty proposal root is
      processed, then that first root. See the module header for the deviation from
      Definition 13's first-block rule. -/
  rootProposal : Nat → Option (Block Validator)
  /-- `head[·]` (Definition 10; read by Figure 4's scores, written by Figure 6's
      `on_attestation`): per round and validator, the first processed nonempty attestation
      head with its processing time, `none` until one arrives. -/
  head : Nat → Validator → Option (Block Validator × Int)
  /-- `equiv[·]` (Definition 10; read by Figure 4, written by Figure 6): per round and
      validator, the time at which a head different from the stored one was first
      processed — the equivocation time — `none` while none was. -/
  equiv : Nat → Validator → Option Int
  /-- `vote[·]`: per **slot** and validator, the first processed Goldfish vote with its
      processing time, `none` until one arrives. Written by `on_goldfish_vote`
      (`Goldfish.lean`), read by the counting there.

      **Beyond Definition 10** (Roberto, 2026-08-22): the draft's timed store keeps this
      bookkeeping for attestation heads and not for Goldfish votes, and Section 5, which
      would need it, is undrafted. The shape is `head[·]`'s exactly — first write wins, the
      time recorded beside the value — one level down, keyed by slot rather than round,
      because a Goldfish vote belongs to a slot. -/
  vote : Nat → Validator → Option (Block Validator × Int)
  /-- `vote_equiv[·]`: per slot and validator, the time at which a Goldfish vote for a
      *different* block was first processed — the vote-equivocation time — `none` while none
      was. `equiv[·]`'s shape, and beyond Definition 10 for the same reason as `vote[·]`.

      Separate from `equiv[·]`: that one records equivocation in attestation heads, this one
      in raw votes, and the draft's Definition 3 and Definition 4 are separate objects with
      separate signatures. A validator can equivocate in one and not the other. -/
  voteEquiv : Nat → Validator → Option Int
  /-- `sg_root[·]` (Definition 10; written by Figure 6 at the opening slot's vote time,
      read by Figure 5's `get_walk_root`): per round, the SG root derived at `t_r + Δ`,
      `none` until that write. Fixed after it. -/
  sgRoot : Nat → Option (Block Validator)
  /-- `action_root[·]` (Definition 10; written by Figure 6 at `a_r`): per round, the root
      Figure 5's `get_action_root` derived there — the anchor of the round's SG and FG
      outputs, which the draft's Section 6 will read. `none` until that write. -/
  actionRoot : Nat → Option (Block Validator)
  /-- `Σ.t` (Definition 10), the clock: the current time, set by every `on_tick`. Starts
      below time 0 — the draft leaves the initial value unstated, and `on_tick`'s
      precondition `Σ.t < t` must pass at `t = 0` — at `-1`, an arbitrary such value. -/
  t : Int
  /-- `ω`, the draft's "available-chain data that selects among the candidates". Its type
      `Ω` is a parameter of the store and stays abstract until the draft's Section 5 says
      what the data is; what can be *done* with it is the `Selection` class below.

      **A store field, beyond Definitions 7 and 10** (Roberto, 2026-08-20): the draft
      passes `Ω` to `get_head` as call-time input, and the old rendering kept it ambient
      by typeclass and out of the store; carrying it here instead makes every selection —
      `get_head`, the deepest-picks, Section 5's confirmation when it lands — a function
      of the store alone. -/
  ω : Ω
  /-- The round's Goldfish walk: from a walk start, over a candidate set, to the block the
      round confirms. **Only its type is given here** — the draft's Section 5 will define
      the walk, and until then a store value supplies whatever function it likes.

      The result type is what the walk promises (Roberto, 2026-08-21): the block it returns
      lies in `candidates ∪ {walkStart}`, so a walk that finds nowhere to go stays where it
      started. Written as the disjunction that union unfolds to, because `Finset` union
      needs `DecidableEq` and `Store` takes no instance parameters.

      A field rather than an `opaque` definition, so that no inhabitation witness is needed
      and the walk stays computable; and a field rather than a `Selection` method, so that
      it can differ per store value. Beyond Definitions 7 and 10, like `ω` above: the draft
      does not make the walk a store component. -/
  goldfishConfirmation : (walkStart : Block Validator) →
    (candidates : Finset (Block Validator)) →
    {B // B ∈ candidates ∨ B = walkStart}

/-! ### `B ∈ S.σ` and `S.σ[B]` — the membership, and the read that raises

The draft writes `Σ.σ[B]` unconditionally, its map being defined exactly on the accepted
blocks. Here the field is `Option`-valued, so a read has to say what it does when the entry
is absent, and **`S.σ[B]` raises** (Roberto, 2026-08-21): it returns
`ResultOrExcept (ChainState Validator)`, so in a `do` block over that monad
`let σB ← S.σ[B]` propagates a missing entry to the caller with no proof written anywhere and
no check either. The draft's own spelling, and no proof obligation at the call — which is
what lets a caller write any imperative body it likes and dispatch at the end.

`B ∈ S.σ` stays, meaning "the map is defined at `B`" (definitionally `(S.σ B).isSome`). It
is what `stateAt` tests, what `viableLeaves` asks below, and what the coherence invariant of
`Analysis/` is stated over. The proof-carrying read that used to be `S.σ[B]` has no notation
any more — write `(S.σ B).get h`, as `viableLeaves` does.

There is exactly one `[]` per collection because `GetElem`'s element type and validity
predicate are both `outParam`, so the two readings cannot coexist under one bracket. A
raising `S.σ⟦B⟧` beside a checked `S.σ[B]` was the first arrangement, commits `b13dc9f` to
`78dbcec`; this is the second, and it is the draft's spelling.

The side condition is `True`, discharged by `get_elem_tactic`'s own `trivial`, so no
`get_elem_tactic` extension is needed and none is installed. `S.σ[B]?` and `S.σ[B]!` are
gone with the checked read: neither means anything once `[]` is already total.

One hazard, measured on the old rendering: `rw` on a store inside a bracket read fails with
"motive is not type correct" where `simp only` succeeds. -/

/-- `B ∈ σ`: the map is defined at `B`. -/
scoped instance stateMapMembership :
    Membership (Block Validator) (Block Validator → Option (ChainState Validator)) where
  mem σ B := (σ B).isSome

/-- The membership is a `Bool` in disguise, so an `if _ : B ∈ S.σ` can test it. -/
scoped instance (σ : Block Validator → Option (ChainState Validator)) (B : Block Validator) :
    Decidable (B ∈ σ) :=
  inferInstanceAs (Decidable ((σ B).isSome = true))

/-- `σ[B]`, the read behind the bracket: the state recorded for `B`, or the failure. -/
def stateAt (σ : Block Validator → Option (ChainState Validator)) (B : Block Validator) :
    ResultOrExcept (ChainState Validator) :=
  if h : B ∈ σ then .ok ((σ B).get h) else .error .error

/-- `σ[B]`: the raising read. The validity predicate is `True` — the bracket owes nothing,
    the failure being in the result type instead — so `get_elem_tactic` closes it with
    `trivial` and a call site writes nothing. -/
scoped instance stateMapGetElem :
    GetElem (Block Validator → Option (ChainState Validator)) (Block Validator)
      (ResultOrExcept (ChainState Validator)) (fun _ _ => True) where
  getElem σ B _ := stateAt σ B

section StoreDefs
variable [DecidableEq Validator]

/-- The genesis store: `s = 0`, `T = {B_gen}`, `σ[B_gen]` the genesis state,
    `F = B_gen`, `(J, h_j) = (B_gen, 0)`, `h_max = 1`. The per-round maps start empty.
    The fields the draft's genesis prose does not fix are the two beyond Definitions 7
    and 10 — the validator's selection data and its walk — so they are the arguments. -/
def Store.gen (ω : Ω)
    (goldfishConfirmation : (walkStart : Block Validator) →
      (candidates : Finset (Block Validator)) → {B // B ∈ candidates ∨ B = walkStart}) :
    Store Validator Ω where
  s := 0
  T := {.genesis}
  σ := fun B => if B = .genesis then some .gen else none
  F := .genesis
  J := .genesis
  h_j := 0
  h_max := 1
  rootProposal := fun _ => none
  head := fun _ _ => none
  equiv := fun _ _ => none
  vote := fun _ _ => none
  voteEquiv := fun _ _ => none
  sgRoot := fun _ => none
  actionRoot := fun _ => none
  t := -1
  ω := ω
  goldfishConfirmation := goldfishConfirmation

/-- `L` is a *leaf* of `Σ.T` (Definition 8 of the draft): an accepted block without
    accepted children. "Without accepted children" is written
    `∀ C ∈ S.T, C.parent ≠ some L` — no accepted block names `L` as its parent. -/
def Store.isLeaf (S : Store Validator Ω) (L : Block Validator) : Prop :=
  L ∈ S.T ∧ ∀ C ∈ S.T, C.parent ≠ some L

instance (S : Store Validator Ω) (L : Block Validator) : Decidable (S.isLeaf L) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The leaves of `Σ.T`, as a set. -/
def Store.leaves (S : Store Validator Ω) : Finset (Block Validator) :=
  {L ∈ S.T | S.isLeaf L}

/-- The leaves whose recorded state-height is at least `Σ.h_max − 1`: the leaves that
    witness a branch reaching within one height of the store's frontier. Definition 8's
    viability is "some viable leaf descends from this block", and both of its readers —
    `candidateTree` and `process_updates`' finalize test — say it that way.

    **This is where the rendering raises** (Roberto, 2026-08-21): the height is read with
    `Σ.σ[L]`, so a leaf the map does not record fails, and the failure propagates to whoever
    asked. It is the only place in the file that reads the state map for a height, and
    everything downstream is `ResultOrExcept` because of it — `candidateTree`,
    `process_updates`, `get_head`, every root of Figure 5, `on_block`, `on_tick`.

    Treating a missing entry as *not viable* instead — `(S.σ L).any …`, total — was the
    previous reading, commit `ebd7626`. The two agree on any store that keeps the coherence
    invariant; raising is the strict one, and it cannot answer a fork choice wrongly if the
    invariant is ever violated.

    `Finset.filterM` is what carries the failure out of a set; see its own docstring on why
    `Finset.fold` is the only route and what its two instances mean. -/
def Store.viableLeaves (S : Store Validator Ω) :
    ResultOrExcept (Finset (Block Validator)) :=
  S.leaves.filterM fun L => do
    return (← S.σ[L]).h ≥ S.h_max - 1

/-- `fork_choice_root(Σ)` (Figure 2, lines 20–23), Definition 8's fork-choice root: `Σ.J`
    while the justified pair sits one height under the store's frontier —
    `Σ.h_max = Σ.h_j + 1` — and `Σ.F` otherwise. -/
def Store.forkChoiceRoot (S : Store Validator Ω) : Block Validator := Id.run do
  if S.h_max = S.h_j + 1 then                                 -- line 21
    return S.J                                                -- line 22
  return S.F                                                  -- line 23

/-- `C(Σ)` (Definition 8 of the draft): the candidate tree, within which fork choice
    selects a head. A block is in it when it descends from the fork-choice root and some
    viable leaf descends from it. The second condition is inherited by ancestors, so it
    makes the set prefix-closed above the root: the draft's observation, not an extra
    clause.

    **The draft's `V(Σ)` is not a definition here.** Its viable-blocks set has exactly two
    readers, this one and `process_updates`' finalize test, and each writes its condition
    out over `viableLeaves` (Roberto, 2026-08-20).

    **One bind above a pure `filter`, not `filterM`** (Roberto, 2026-08-21). Both compile and
    give the same set, `viableLeaves` not depending on `B` — but `filterM` puts the read
    inside the predicate, so it re-derives the viable leaves once per accepted block and the
    state map is read `|Σ.T|` times over instead of once. Binding once also says the true
    thing: viability is a property of the store, computed before the filter, not part of the
    per-block condition. `52193b1` has the `filterM` version.

    The arrow cannot be inlined into the `filter` itself. `(← e)` lifts to the nearest
    enclosing `do` statement, and inside `fun B => …` there is none, so Lean reports "Cannot
    lift nested action over a binder" rather than silently moving the read out of the
    predicate. Its suggestion to add a `do` does not apply either: `Finset.filter` takes a
    pure predicate, which is what `filterM` exists for. Where no binder intervenes the inline
    form is fine — `candidateTreeFrom` below writes `(← S.candidateTree).filter …`. -/
def Store.candidateTree (S : Store Validator Ω) :
    ResultOrExcept (Finset (Block Validator)) := do
  let viableLeaves ← S.viableLeaves
  return {B ∈ S.T | S.forkChoiceRoot ⪯ B ∧ ∃ L ∈ viableLeaves, B ⪯ L}

/-- The blocks a walk from `R` may occupy: `R` itself, together with the candidates
    descending from it.

    **`R` is in the result unconditionally** (Roberto, 2026-08-20), even when `R` is not a
    candidate — a walk from `R` must be able to stay where it starts. So this is not a
    subset of `C(Σ)`, and it is never empty, which is what makes a selection over it
    total. -/
def Store.candidateTreeFrom (S : Store Validator Ω) (R : Block Validator) :
    ResultOrExcept (Finset (Block Validator)) := do
  return {B ∈ (← S.candidateTree) | R ⪯ B} ∪ {R}

end StoreDefs

/-! ## The handlers -/

/-- `on_slot(Σ, s)` (Figure 2, lines 1–3): advance the store's slot at the start of slot
    `s`, before any block of that slot is processed. -/
def onSlot (S : Store Validator Ω) (s : Nat) : Store Validator Ω := Id.run do
  let mut S := S
  S.s ← s                                                     -- line 2
  return S                                                    -- line 3

section Handlers
variable [DecidableEq Validator] [Electorate Validator] [Params] [BlockHash Validator]

/-- `process_updates(Σ, σ)` (Figure 2, lines 12–19): fold an offered post-state into the
    store. Raise `h_max`; replace the justified pair when the offer dominates in
    `(h, hash)` order and descends from `Σ.F`; advance the finalized block only to a viable
    proper descendant of `Σ.F` below `Σ.J`, pruning every accepted block conflicting with
    the new `Σ.F` — the pruned blocks remain available as signed evidence, outside this
    store. -/
def processUpdates (S : Store Validator Ω) (σ : ChainState Validator) :
    ResultOrExcept (Store Validator Ω) := do
  let mut S := S
  S.h_max ← max S.h_max σ.h                                   -- line 13
  -- line 14: `(σ.h_j, hash(σ.J)) > (Σ.h_j, hash(Σ.J))` is the strict lexicographic
  -- order, written out
  if S.F ⪯ σ.J ∧ (S.h_j < σ.h_j ∨ (σ.h_j = S.h_j ∧ hash(S.J) < hash(σ.J))) then
    S.J ← σ.J                                                 -- line 15
    S.h_j ← σ.h_j
  -- line 16. The draft's `σ.F ∈ V(Σ)` is written out over `viableLeaves` — see
  -- `candidateTree` on why `V(Σ)` is not a definition here. Note it is *not*
  -- `σ.F ∈ C(Σ)`: this block lies below `Σ.J`, so it need not descend from the
  -- fork-choice root.
  let VL ← S.viableLeaves
  if S.F ≺ σ.F ∧ σ.F ⪯ S.J ∧ ∃ L ∈ VL, σ.F ⪯ L then
    S.F ← σ.F                                                 -- line 17
    S.T ← {B ∈ S.T | B ∼ S.F}                                 -- line 18, the figure's own set
  return S                                                    -- line 19

/-- `on_block(Σ, B)` (Figure 2, lines 4–11). Lines 5–6 register the round's root proposal
    from the first opening block processed that carries one — before the admission test, so
    a block rejected below still claims its round's entry. Admission then wants the slot
    started, the parent accepted, and `B` descending from `Σ.F`; an admitted block is
    replayed with Figure 1's transition, stored, and its post-state offered to
    `process_updates`. -/
def onBlock (S : Store Validator Ω) (B : Block Validator) :
    ResultOrExcept (Store Validator Ω) := do
  let mut S := S
  -- line 5, strengthened: only a nonempty proposal root registers — see the module header
  if B.isOpening ∧ S.rootProposal (round B.slot) = none ∧ B.proposalRoot ≠ none then
    S.rootProposal[round B.slot] ← B.proposalRoot             -- line 6
  -- line 7: `if B.slot > Σ.s or B.parent ∉ Σ.T or Σ.F ⪯̸ B then return Σ`. A parentless
  -- `B` — genesis — is the `B.parent ∉ Σ.T` case, taken first; see the module header.
  let some p := B.parent | return S
  if B.slot > S.s ∨ p ∉ S.T ∨ ¬ S.F ⪯ B then
    return S                                                  -- line 8
  -- line 9: `Σ.σ[B] ← state_transition(Σ.σ[B.parent], B)`. The parent's state is read
  -- through the map's `Option`; a parent the map misses rejects — see the module header.
  let some σp := S.σ p | return S
  let σ' := stateTransition σp B
  S.σ[B] ← some σ'
  S.T ← S.T ∪ {B}                                             -- line 10
  return ← processUpdates S σ'                                -- line 11

end Handlers

/-- `get_head(Σ, Ω)` (Figure 2, lines 24–25): a block in `C(Σ)`, selected using the
    store's own available-chain data `ω`, through the unspecified `Selection.select`. On an
    empty candidate tree — not excluded by the types, though a store the handlers built
    keeps its fork-choice root viable — the fork-choice root is returned, so the *selection*
    never fails. Deriving the candidate tree can, which is why the result is
    `ResultOrExcept`. -/
def getHead [DecidableEq Validator] [Selection Validator Ω] (S : Store Validator Ω) :
    ResultOrExcept (Block Validator) := do
  let CT ← S.candidateTree
  if h : CT.Nonempty then return (Selection.select S.ω CT h).val
  return S.forkChoiceRoot

end Consensus
