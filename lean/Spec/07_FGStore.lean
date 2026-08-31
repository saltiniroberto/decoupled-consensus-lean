import Spec.«05_SGDuty»
import Spec.«02_GoldfishStore»

/-!
# The finality gadget in the fork choice

Viability, and the finality layer's routines: `process_block`, `update_finality`,
`get_fg_root`, `get_filtered_block_tree`, `goldfish_eligible`, and the Goldfish fork
choice they instantiate.

**This is the protocol for `process_block`.** The fork choice is assembled one layer up:
`get_head` (`09_Healing.lean`) walks the tree the graded layer builds, and both of that
tree's ingredients are defined here — `Store.goldfishEligible`, the condition the walk
tests, and `Store.getFilteredBlockTree`, the viable blocks at or below the FG root, the
set the tree carries.

## What this layer adds

The store gains `Σ.σ[·]` and the finality state `(Σ.F, Σ.J, Σ.h_j,
Σ.h_max)` — all already fields of `Store`, which carries every layer's at once. The
store keeps no `h_F`: the height of a finalization is read off a chain state, in
`get_fg_vote`. Two lines join
`process_block`: the post-state write, and `update_finality`, each marked "new at this
layer" in the figure and here.

And the walk no longer starts at genesis over everything. It starts at
`fork_choice_root(Σ)` over `get_filtered_block_tree(Σ)`, and the Goldfish eligibility
condition gains a third
disjunct — a child whose state height is below `Σ.h_max − 1` is eligible without a majority.

## `Σ.F ⪯[Σ] Σ.J` is claimed, not enforced

"`Σ.F` advances only to a viable proper descendant of itself below `Σ.J`, so `Σ.F ⪯ Σ.J`
always holds and finalization never reverts." That is a property of `update_finality`,
whose advance test asks exactly those three things, and an invariant of the reachable
stores — not a fact of the `Store` type. `Analysis/` is where it belongs.

## Reading the state map, and where that lands

Viability and the eligibility condition's
height clause read `Σ.σ[W].h` and `Σ.σ[B].h`. The bracket raises when the
map does not record the block, so a routine reading it carries `DRE` —
`processBlock`, `updateFinality`, `viable`, `getFilteredBlockTree`, `goldfishEligible` and
`getHead` all do, and `getFGRoot` alone does not, reading no map. A missing entry
reaches the caller instead of becoming a silent answer; on a store whose `Σ.σ` covers `Σ.T`
nothing raises at all, and that theorem belongs to `Analysis/`.

A failure crosses a *set* through the fold machinery of the two `FinsetM` files:
`Finset.filterM` collects viability's witnesses. `ghost`'s condition slot is `DRE`, so
`get_head` passes
`goldfish_eligible` itself, raising reads included — the rendering carries no deviation
there.

## Extract

The store adds a block state map `Σ.σ[·]` and finality state
`(Σ.F, Σ.J, Σ.h_j, Σ.h_max)`. It retains every processed block; the live tree is
derived below the finalized block,

[eq:T_F]

[fig:07_FGStore] extends the block handler: it admits a block only when it is not from
the future, not already processed, its parent is held, and it descends from the
finalized block; then it computes and stores the post-state and
folds it into the finality caches with `update_finality(Σ, σ)`. The pair `(Σ.J, Σ.h_j)`
tracks the lex-greatest justification event compatible with the finalized block. `Σ.F`
advances only to a viable proper descendant of itself below `Σ.J`, so `Σ.F ⪯ Σ.J`
always holds and finalization never reverts. `Σ.h_max` takes the offered height and is
never lowered.

## Extract — Definition (Viability)

A live block is viable when it has a live descendant whose state height is at most one
below the current maximum:

`V(Σ) = {B ∈ T_F(Σ) : ∃ W ∈ T_F(Σ), B ⪯ W, Σ.σ[W].h ≥ Σ.h_max − 1}`

## Extract

Fork choice uses
two derived views: `fork_choice_root(Σ)`, the block the walk starts from, and
`get_filtered_block_tree(Σ)`, the viable blocks below it, which limit the selectable
children. Goldfish starts at the root even if the root is not in the filtered tree.

At this layer `goldfish_eligible` gains one clause: a child whose state height is below
`Σ.h_max − 1` is eligible without a majority.

Available confirmation is not a separate walk over the live tree. It takes the root it starts
from and the blocks it may step onto from the same place `get_head` takes them, so it inherits
this layer's height filter, and whatever a later layer puts in place of it. What it keeps of
its own are the votes it scores and its eligibility condition, which has no current-slot
escape.

-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [BlockIds] [BlockIdentity Validator] [DecidableEq Validator] [Electorate Validator]
  [Committees Validator] [Proposers Validator] [Params]

open Params

/-! ## Viability -/

/-- `V(Σ) = {B ∈ T_F(Σ) : ∃W ∈ T_F(Σ), B ⪯ W, Σ.σ[W].h ≥ Σ.h_max − 1}`: a
    live block is *viable* when it has a live descendant whose state height is at most one
    below the current maximum.

    The witnesses `W` are collected first — the live blocks whose recorded height reaches
    `Σ.h_max − 1` — and the set-builder then asks for a descendant among them. The collection
    reads `Σ.σ[W]` per live block through `Finset.filterM`, so a live block the map does not
    record raises rather than silently failing to witness. -/
def Store.viable (S : Store Validator) : DRE (Finset BlockId) := do
  let witnesses ← {W ∈ᴹ S.liveTree | (← S.σ[W]).h ≥ S.h_max - 1}
  return {B ∈ S.liveTree | ∃ W ∈ witnesses, B ⪯[S] W}

/-! ## The store handler, extended -/

/-! ## Figure -/
/-- Fold one offered post-state into the
    finality caches.

    Three steps, in the figure's order. `Σ.h_max` takes the offered height and **is never
    lowered**. The justified pair
    is replaced when the offer dominates in the lex order — the protocol's
    `(h_j, J.root)`, whose tie-break this rendering reads off the identifiers, blocks
    carrying no root (`Model.lean`) — **and** descends
    from the finalized block: "the pair `(Σ.J, Σ.h_j)` tracks the lex-greatest justification
    event compatible with the finalized block". Then `Σ.F` advances, only to a viable proper
    descendant of itself below `Σ.J`.

    One read raises: the advance test's viability, whose `(← viable S)` is evaluated before
    the conjunction is tested — the `←` lifts above the `if` — so the routine raises on a
    store with an unrecorded live block even when `σ.F` offers no advance; on a store where
    nothing raises the two readings agree. -/
def Store.updateFinality (S : Store Validator) (σ : ChainState Validator) :
    DRE (Store Validator) := do
  let mut S := S
  S.h_max ← max S.h_max σ.h
  -- `(σ.h_j, σ.J.root) > (Σ.h_j, Σ.J.root)`, the lex order written out — the tie on the
  -- identifiers, blocks carrying no root
  if S.F ⪯[S] σ.J ∧ (S.h_j < σ.h_j ∨ (σ.h_j = S.h_j ∧ S.J < σ.J)) then
    S.J ← σ.J
    S.h_j ← σ.h_j
  if S.F ≺[S] σ.F ∧ σ.F ⪯[S] S.J ∧ σ.F ∈ (← S.viable) then
    S.F ← σ.F
  return S

/-- `B` is *wanted*: not from the future, not already processed, and naming a parent —
    the admission tests that read nothing of the parent. A wanted block whose parent is
    missing is what waits in `Σ.pending`; `admissible` below is this plus the
    parent-side tests. -/
def Store.wanted (S : Store Validator) (B : Block Validator) : Prop :=
  B.slot ≤ S.s ∧ B.id ∉ S.T ∧ B.parent ≠ ⊥

instance (S : Store Validator) (B : Block Validator) : Decidable (S.wanted B) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `B` is *admissible*: wanted with its parent held, and the parent-side tests hold —
    the block descends from the finalized block (read at the parent: `Σ.F ⪯ B` climbs
    `B`'s own links, and `B` is not yet in `Σ.T`; `Σ.F = B` is not a case, a processed
    `Σ.F` never sharing an identifier with an unprocessed block), and the two facts the
    state transition asserts — the slot's proposer, and `B.parent.slot < B.slot`, the
    parent's slot read through `Σ.T[P]`, which **raises** where the store holds nothing —
    unreachable behind the membership test, as every bracket read is. `DRE Bool`, the
    `goldfish_eligible` shape. The drain in `process_block` selects by this, which is
    what keeps a block that can never be admitted from being picked forever. -/
def Store.admissible (S : Store Validator) (B : Block Validator) : DRE Bool := do
  if S.wanted B then
    let P ← B.parent                    -- a wanted block names a parent; the lift extracts
    if P ∈ S.T then
      return (S.F ⪯[S] P) ∧ B.proposer = ↑(Proposers.proposer B.slot : Validator) ∧
        (← S.T[P]).slot < B.slot
  return false

/-! ## Figure -/
/-- Admit one block whose turn has come: one test — `admissible`, the admission's whole
    condition — and then the writes: the post-state from the parent's, the tree, the
    stamp, the carried votes, `update_finality`. An inadmissible block leaves the store
    unchanged.

    The two reads behind the test raise where the test cannot have passed: `B.parent`'s
    extraction, which `admissible`'s witness names, and `Σ.σ[parent]`, whose coverage of
    the held parent is the map-covers-tree invariant — a fact for `Analysis/`, not a
    licence to answer silently here. -/
def Store.admitBlock (S : Store Validator) (B : Block Validator) :
    DRE (Store Validator) := do
  let mut S := S
  if ¬ (← S.admissible B) then
    return S
  let parent ← B.parent
  let σp ← S.σ[parent]
  -- `Σ.σ[B] ← state_transition(Σ.σ[B.parent], B)` — new at this layer
  S.σ[B.id] ← some (stateTransition σp B)
  -- `Σ.T ← Σ.T ∪ {B}`: the map admits `B` under its identifier
  S.T ← S.T.insert B.id B
  S.blockTime[B.id] ← some S.t
  for vote in B.gfVotes do
    S ← S.processGoldfishVote vote
  -- `update_finality(Σ, Σ.σ[B])` — new at this layer
  return (← S.updateFinality (← S.σ[B.id]))

/-! ## Figure -/
/-- The block handler: a block whose parent is not yet held **waits** in `Σ.pending` —
    the mechanism behind the protocol's "after every dependency of that object is already
    in the store" (Roberto, 2026-09-01) — everything else is admitted or rejected as the
    admission says, and every admission **drains** the buffer: as long as some pending
    block has become admissible, one is picked, removed and admitted, so a parent's
    arrival releases its waiting descendants in cascade.

    The drain's pick is a genuine nondeterministic choice — the protocol fixes no order —
    which is what puts the handler in `NDRE`. Its loop is bounded by `|Σ.pending|`, the
    `ghost` shape: each pass consumes one pending block, so the bound is never reached
    with an admissible block still waiting. A pending block that never becomes
    admissible — its branch does not descend from the finalized block, say — is never
    picked, and simply stays. -/
def Store.processBlock (S : Store Validator) (B : Block Validator) :
    NDRE (Store Validator) := do
  let mut S := S
  -- only a block the admission would otherwise take waits for its parent: the future and
  -- the re-received are turned away, as ever
  if S.wanted B then
    let P ← B.parent                    -- a wanted block names a parent; the lift extracts
    if P ∉ S.T then
      S.pending ← S.pending ∪ {B}
      return S
  S ⇐ S.admitBlock B
  -- the drain: while some pending block has become admissible, one is admitted
  for _ in [:|S.pending|] do
    let ready ← {C ∈ᴹ S.pending | (← S.admissible C)}
    if ready = ∅ then
      return S
    let C ←ᵖ ready
    S.pending ← S.pending.erase C
    S ⇐ S.admitBlock C
  return S

/-! ## The two derived views, and the redefined fork choice -/

/-! ## Figure -/
/-- `Σ.J` while the justified pair sits one
    height under the store's frontier, and `Σ.F` otherwise. The only routine of this layer
    that reads no state map, and so the only one that does not raise. -/
def Store.getFGRoot (S : Store Validator) : BlockId := Id.run do
  if S.h_max = S.h_j + 1 then
    return S.J
  return S.F

/-! ## Figure -/
/-- The viable blocks at or below the
    fork-choice root, which "limit the selectable children".

    "Goldfish starts at the root even if the root is not in the filtered tree" — so this set
    is a constraint on the walk's *children*, not on its anchor, and the anchor is passed
    separately by `get_head`. It raises exactly where `viable` does.

    It is what the healing layer builds on: that layer's reading is this one with the grade-0
    veto applied. There is no earlier one — before this layer the walk descended `Σ.T`. -/
def Store.getFilteredBlockTree (S : Store Validator) :
    DRE (Finset BlockId) := do
  let root := S.getFGRoot
  return {B ∈ (← S.viable) | root ⪯[S] B}

/-! ## Figure -/
/-- The Goldfish eligibility condition
    with its third disjunct — "a child whose state height is below
    `Σ.h_max − 1` is eligible without a majority".

    That clause is what lets the walk descend past blocks nobody has voted on yet, which is
    what makes the height filter a filter rather than a wall.

    It raises: the height it tests is `Σ.σ[B].h`, and a block the map does not record has
    none — and it is what `get_head` hands the walk, `ghost`'s condition slot being
    `DRE`.

    This is the reading every caller wants, and the healing layer's walk carries it
    unchanged.

    `B` is an identifier, so the last disjunct compares the slot of the block it names,
    `Σ.slot_of(B)` — a second raising read, through the same bracket as the height. -/
def Store.goldfishEligible (S : Store Validator)
    (votes supportVotes : Finset (GoldfishVote Validator))
    (s : Nat) (B : BlockId) : DRE Bool := do
  let σB ← S.σ[B]
  -- `voters_count ← |{v ∈ V : votes holds a vote by v}|` — a `let`, as the
  -- figure writes it. The denominator counts every sender, resolved or not
  let votersCount := |{v ∈ Electorate.V | ∃ a ∈ votes, a.validator = v}|
  return σB.h < S.h_max - 1 ∨
    2 * S.goldfishScore votes supportVotes s B > votersCount ∨ (← S.slotOf B) = S.s

/-! ## Figure -/
/-- The shared walk, instantiated
    with the Goldfish score and the eligibility condition above. It sits here, and not beside
    `ghost`, because the condition does: this is the file that defines it. -/
def Store.goldfishForkChoice (S : Store Validator)
    (tree : BlockTree)
    (votes supportVotes : Finset (GoldfishVote Validator))
    (s : Nat) :
    NDRE BlockId :=
  S.ghost tree (S.goldfishScore votes supportVotes s)
    (S.goldfishEligible votes supportVotes s)

end DC
