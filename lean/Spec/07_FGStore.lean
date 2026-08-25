import Spec.«05_SGDuty»
import Spec.«02_GoldfishDuties»

/-!
# The finality gadget in the fork choice

Viability, and the finality layer's routines: `process_block` extended, `update_finality`, `fork_choice_root`,
`get_filtered_block_tree`, `goldfish_eligible` extended, and `get_head` redefined.

**This is the protocol.** Where a routine here shares a name with an earlier file's,
this is the reading a caller wants, and it bears the plain `Store` name: `S.processBlock`,
`S.goldfishEligible`, and the fork choice `S.getHead`. The superseded readings are
named by their file's number — `Fig2.processBlock`, `Fig1.goldfishEligible`,
`Fig1.getHead`, `Fig4.getHead`. See `01_GoldfishWalk.lean` on the scheme.

## What this layer adds

The store gains `Σ.σ[·]` and the finality state `(Σ.F, Σ.h_F, Σ.J, Σ.h_j,
Σ.h_max)` — all already fields of `Store`, which carries every layer's at once. Two lines join
`process_block`: the post-state write, and `update_finality`, each marked "new at this
layer" in the figure and here.

And the walk no longer starts at genesis over everything. It starts at
`fork_choice_root(Σ)` over `get_filtered_block_tree(Σ)`, and the Goldfish gate gains a third
disjunct — a child whose state height is below `Σ.h_max − 1` is eligible without a majority.

## `Σ.F ⪯ Σ.J` is claimed, not enforced

"`Σ.F` advances only to a viable proper descendant of itself below `Σ.J`, so `Σ.F ⪯ Σ.J`
always holds and finalization never reverts." That is a property of `update_finality`,
whose advance test asks exactly those three things, and an invariant of the reachable
stores — not a fact of the `Store` type. `Analysis/` is where it belongs.

## Reading the state map, and where that lands

Viability, `update_finality`'s recomputation of `Σ.h_max` and the eligibility condition's
height clause read `Σ.σ[W].h` and `Σ.σ[B].h`. The bracket raises when the
map does not record the block, so a routine reading it carries `DRE` —
`processBlock`, `updateFinality`, `viable`, `getFilteredBlockTree`, `goldfishEligible` and
`getHead` all do, and `forkChoiceRoot` alone does not, reading no map. A missing entry
reaches the caller instead of becoming a silent answer; on a store whose `Σ.σ` covers `Σ.T`
nothing raises at all, and that theorem belongs to `Analysis/`.

A failure crosses a *set* through the fold machinery of the two `FinsetM` files:
`Finset.filterM` collects viability's witnesses, and `Finset.imageM` collects the
recomputation's heights. `ghost`'s condition slot is `DRE`, so `get_head` passes
`goldfish_eligible` itself, raising reads included — the rendering carries no deviation
there.

## Extract

The store adds a block state map `Σ.σ[·]` and finality state
`(Σ.F, Σ.h_F, Σ.J, Σ.h_j, Σ.h_max)`. It retains every processed block; the live tree is
derived below the finalized block,

[eq:T_F]

[fig:07_FGStore] extends the block handler: it computes and stores the post-state,
then folds it into the finality caches with `update_finality(Σ, σ)`. The pair `(Σ.J, Σ.h_j)`
tracks the lex-greatest justification event compatible with the finalized block. `Σ.F`
advances only to a viable proper descendant of itself below `Σ.J`, so `Σ.F ⪯ Σ.J`
always holds and finalization never reverts. When it advances, `Σ.h_max` is recomputed
inside the new live tree; it otherwise only grows.

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
`Σ.h_max − 1` is eligible without a majority. Available confirmation runs its own walk
from `Σ.F` over `T_F(Σ)`; it uses neither the SG root nor the filtered tree.

-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [Roots] [DecidableEq Validator] [Electorate Validator]
  [Committees Validator] [Params]

open Params

/-! ## Viability -/

/-- `V(Σ) = {B ∈ T_F(Σ) : ∃W ∈ T_F(Σ), B ⪯ W, Σ.σ[W].h ≥ Σ.h_max − 1}`: a
    live block is *viable* when it has a live descendant whose state height is at most one
    below the current maximum.

    The witnesses `W` are collected first — the live blocks whose recorded height reaches
    `Σ.h_max − 1` — and the set-builder then asks for a descendant among them. The collection
    reads `Σ.σ[W]` per live block through `Finset.filterM`, so a live block the map does not
    record raises rather than silently failing to witness. -/
def Store.viable (S : Store Validator) : DRE (Finset (Block Validator)) := do
  let witnesses ← {W ∈ᴹ S.liveTree | (← S.σ[W]).h ≥ S.h_max - 1}
  return {B ∈ S.liveTree | ∃ W ∈ witnesses, B ⪯ W}

/-! ## The store handler, extended -/

/-! ## Figure -/
/-- Fold one offered post-state into the
    finality caches.

    Three steps, in the figure's order. `Σ.h_max` takes the offered height. The justified pair
    is replaced when the offer dominates in the lex order `(h_j, J.root)` **and** descends
    from the finalized block — "the pair `(Σ.J, Σ.h_j)` tracks the lex-greatest justification
    event compatible with the finalized block". Then `Σ.F` advances, only to a viable proper
    descendant of itself below `Σ.J`, and `Σ.h_max` is recomputed inside the live tree the
    advance just shrank.

    Two reads raise. The advance test's viability, whose `(← viable S)` is evaluated before
    the conjunction is tested — the `←` lifts above the `if` — so the routine raises on a
    store with an unrecorded live block even when `σ.F` offers no advance; on a store where
    nothing raises the two readings agree. And the recomputation's heights, collected
    through `Finset.imageM`, so a live block the map does not record fails the
    recomputation rather than contributing a placeholder.

    The recomputed maximum is over the recorded heights of the *new* live tree, so it can
    go down; the unconditional `max` at entry cannot. -/
def Store.updateFinality (S : Store Validator) (σ : ChainState Validator) :
    DRE (Store Validator) := do
  let mut S := S
  S.h_max ← max S.h_max σ.h
  -- `(σ.h_j, σ.J.root) > (Σ.h_j, Σ.J.root)`, the lex order written out
  if S.F ⪯ σ.J ∧ (S.h_j < σ.h_j ∨ (σ.h_j = S.h_j ∧ S.J.root < σ.J.root)) then
    S.J ← σ.J
    S.h_j ← σ.h_j
  if S.F ≺ σ.F ∧ σ.F ⪯ S.J ∧ σ.F ∈ (← S.viable) then
    S.F ← σ.F
    S.h_F ← σ.h_F
    -- `max{Σ.σ[B].h : B ∈ T_F(Σ)}`, in the live tree that just shrank
    S.h_max ← (← S.liveTree.imageM fun B => do return (← S.σ[B]).h).max.getD 0
  return S

/-! ## Figure -/
/-- The Goldfish handler (`Fig2.processBlock`) with the two lines
    this layer adds — the post-state write, and `update_finality`.

    The post-state is computed from the parent's, and the parent's is read with the raising
    bracket: a block whose parent the map does not record cannot be evaluated. The protocol says
    the handler runs "after every dependency of that object is already in the store: a block's
    parent, and a vote's target block", so on a store that respects that, the read cannot
    fail.

    A parentless block — genesis — has no parent state to read, and the figure does not cover
    it: genesis is in `Σ.T` from the start and is never processed. This rendering rejects it,
    leaving the store unchanged, which is the same thing every other admission failure does. -/
def Store.processBlock (S : Store Validator) (B : Block Validator) :
    DRE (Store Validator) := do
  let mut S := S
  if B.slot > S.s then
    return S
  -- `Σ.σ[B] ← state_transition(Σ.σ[B.parent], B)` — new at this layer
  if B.parent ≠ ⊥ then
    let σp ← S.σ[(← B.parent)]
    S.σ[B] ← some (stateTransition σp B)
  else
    return S
  S.T ← S.T ∪ {B}
  S.blockTime[B] ← some S.t
  for vote in B.gfVotes do
    S ← S.processGoldfishVote vote
  -- `update_finality(Σ, Σ.σ[B])` — new at this layer
  return ← S.updateFinality (← S.σ[B])

/-! ## The two derived views, and the redefined fork choice -/

/-! ## Figure -/
/-- `Σ.J` while the justified pair sits one
    height under the store's frontier, and `Σ.F` otherwise. The only routine of this layer
    that reads no state map, and so the only one that does not raise. -/
def Store.forkChoiceRoot (S : Store Validator) : Block Validator := Id.run do
  if S.h_max = S.h_j + 1 then
    return S.J
  return S.F

/-! ## Figure -/
/-- The viable blocks at or below the
    fork-choice root, which "limit the selectable children".

    "Goldfish starts at the root even if the root is not in the filtered tree" — so this set
    is a constraint on the walk's *children*, not on its anchor, and the anchor is passed
    separately by `get_head`. It raises exactly where `viable` does. -/
def Store.getFilteredBlockTree (S : Store Validator) :
    DRE (Finset (Block Validator)) := do
  let root := S.forkChoiceRoot
  return {B ∈ (← S.viable) | root ⪯ B}

/-! ## Figure -/
/-- The Goldfish eligibility condition
    (`Fig1.goldfishEligible`) with a third disjunct — "a child whose state height is below
    `Σ.h_max − 1` is eligible without a majority".

    That clause is what lets the walk descend past blocks nobody has voted on yet, which is
    what makes the height filter a filter rather than a wall.

    It raises: the height it tests is `Σ.σ[B].h`, and a block the map does not record has
    none — and it is what `get_head` hands the walk, `ghost`'s condition slot being
    `DRE`. In `Store` for dot notation, its bare name unique to this layer. -/
def Store.goldfishEligible (S : Store Validator) (view : GoldfishView Validator)
    (s : Nat) (B : Block Validator) : DRE Bool := do
  let σB ← S.σ[B]
  -- `voters_count ← |{v ∈ K_s : the view holds a vote by v}|` — a `let`, as the
  -- figure writes it
  let votersCount := |{v ∈ Committees.K s | ∃ a ∈ view.votes, a.validator = v}|
  return σB.h < S.h_max - 1 ∨
    2 * goldfishScore view s B > votersCount ∨ B.slot = S.s

/-! ## Figure -/
/-- The protocol's fork choice. The SG walk
    selects the anchor from the fork-choice root over the filtered tree, and the Goldfish walk
    selects a descendant of it over the same tree. It raises where the filtered tree does.

    The walk receives `goldfish_eligible` itself: `ghost`'s condition slot is
    `DRE`, so the extended condition — which raises, reading `Σ.σ[B].h` — passes
    directly.

    It bears the plain `Store` name — `S.getHead votes k` — because it is the reading a
    caller wants; the superseded ones are `Fig1.getHead` and `Fig4.getHead`. -/
def Store.getHead (S : Store Validator) (view : GoldfishView Validator) (k : Nat) :
    NDRE (Block Validator) := do
  let root := S.forkChoiceRoot
  let tree ← S.getFilteredBlockTree
  let anchor ← S.majorityForkChoice root tree (round S.s)
  ghost anchor tree (goldfishScore view k) (S.goldfishEligible view k)

end DC
