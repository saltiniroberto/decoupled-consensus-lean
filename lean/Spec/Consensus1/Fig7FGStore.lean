import Spec.Consensus1.Fig5SGDuty
import Spec.Consensus1.Fig2GoldfishDuties

/-!
# Figure 7 — the finality gadget in the fork choice

Definition 5 and Figure 7: `process_block` extended, `update_finality`, `fork_choice_root`,
`get_filtered_block_tree`, `goldfish_eligible` extended, and `get_head` redefined.

**This is the protocol.** Where a routine here has the same name as one in an earlier layer,
this is the one a caller wants: `FG.processBlock`, `FG.goldfishEligible`, `FG.getHead`. See
`Fig1GoldfishWalk.lean` on why the layers are namespaces.

The `-- line n` comments use Figure 7's own line numbering, in the draft as of 2026-08-22.

## What this layer adds

Section 5.1: the store gains `Σ.σ[·]` and the finality state `(Σ.F, Σ.h_F, Σ.J, Σ.h_j,
Σ.h_max)` — all already fields of `Store`, which carries every layer's at once. Two lines join
`process_block`: the post-state at line 4, and `update_finality` at line 8, each marked "new
at this layer" in the figure and here.

Section 5.2: the walk no longer starts at genesis over everything. It starts at
`fork_choice_root(Σ)` over `get_filtered_block_tree(Σ)`, and the Goldfish gate gains a third
disjunct — a child whose state height is below `Σ.h_max − 1` is eligible without a majority.

## `Σ.F ⪯ Σ.J` is claimed, not enforced

"`Σ.F` advances only to a viable proper descendant of itself below `Σ.J`, so `Σ.F ⪯ Σ.J`
always holds and finalization never reverts." That is a property of `update_finality`, which
tests exactly those three things at line 13, and an invariant of the reachable stores — not a
fact of the `Store` type. `Analysis/` is where it belongs.

## Reading the state map, and where that lands

Definition 5 and lines 15 and 25 read `Σ.σ[W].h` and `Σ.σ[B].h`. The bracket raises when the
map does not record the block, so a routine reading it carries `ResultOrExcept` —
`processBlock`, `updateFinality`, `viable`, `getFilteredBlockTree`, `goldfishEligible` and
`getHead` all do, and `forkChoiceRoot` alone does not, reading no map. A missing entry
reaches the caller instead of becoming a silent answer; on a store whose `Σ.σ` covers `Σ.T`
nothing raises at all, and that theorem belongs to `Analysis/`.

A failure crosses a *set* through the fold machinery of the two `FinsetM` files:
`Finset.filterM` collects Definition 5's witnesses, and `Finset.imageM` collects line 15's
heights. The one read the monad cannot reach is inside `get_head`'s walk — see its docstring,
this subtree's one named deviation.
-/

set_option autoImplicit false

namespace Consensus1

namespace FG

variable {Validator : Type}

section ForkChoice
variable [DecidableEq Validator] [Electorate Validator] [Committees Validator]
  [Selection Validator] [Params]

open Params

/-! ## Definition 5 — viability -/

/-- `V(Σ) = {B ∈ T_F(Σ) : ∃W ∈ T_F(Σ), B ⪯ W, Σ.σ[W].h ≥ Σ.h_max − 1}` (Definition 5): a
    live block is *viable* when it has a live descendant whose state height is at most one
    below the current maximum.

    Definition 5's `W` are collected first — the live blocks whose recorded height reaches
    `Σ.h_max − 1` — and the set-builder then asks for a descendant among them. The collection
    reads `Σ.σ[W]` per live block through `Finset.filterM`, so a live block the map does not
    record raises rather than silently failing to witness. -/
def viable (S : Store Validator) : ResultOrExcept (Finset (Block Validator)) := do
  let witnesses ← S.liveTree.filterM fun W => do
    return (← S.σ[W]).h ≥ S.h_max - 1
  return {B ∈ S.liveTree | ∃ W ∈ witnesses, B ⪯ W}

/-! ## The store handler, extended -/

/-- `update_finality(Σ, σ)` (Figure 7, lines 9–15): fold one offered post-state into the
    finality caches.

    Three steps, in the figure's order. `Σ.h_max` takes the offered height. The justified pair
    is replaced when the offer dominates in the lex order `(h_j, J.root)` **and** descends
    from the finalized block — "the pair `(Σ.J, Σ.h_j)` tracks the lex-greatest justification
    event compatible with the finalized block". Then `Σ.F` advances, only to a viable proper
    descendant of itself below `Σ.J`, and `Σ.h_max` is recomputed inside the live tree the
    advance just shrank.

    Two reads raise. Line 13's viability, whose `(← viable S)` is evaluated before the
    conjunction is tested — the `←` lifts above the `if` — so the routine raises on a store
    with an unrecorded live block even when `σ.F` offers no advance; on a store where nothing
    raises the two readings agree. And line 15's heights, collected through `Finset.imageM`,
    so a live block the map does not record fails the recomputation rather than contributing
    a placeholder.

    Line 15's maximum is over the recorded heights of the *new* live tree, so it can go down;
    line 10's cannot. -/
def updateFinality (S : Store Validator) (σ : ChainState Validator) :
    ResultOrExcept (Store Validator) := do
  let mut S := S
  S.h_max ← max S.h_max σ.h                                    -- line 10
  -- line 11: `(σ.h_j, σ.J.root) > (Σ.h_j, Σ.J.root)`, the lex order written out
  if S.F ⪯ σ.J ∧ (S.h_j < σ.h_j ∨ (σ.h_j = S.h_j ∧ S.J.root < σ.J.root)) then
    S.J ← σ.J                                                  -- line 12
    S.h_j ← σ.h_j
  if S.F ≺ σ.F ∧ σ.F ⪯ S.J ∧ σ.F ∈ (← viable S) then           -- line 13
    S.F ← σ.F                                                  -- line 14
    S.h_F ← σ.h_F
    -- line 15: `max{Σ.σ[B].h : B ∈ T_F(Σ)}`, in the live tree that just shrank
    S.h_max ← (← S.liveTree.imageM fun B => do return (← S.σ[B]).h).max.getD 0
  return S

/-- `process_block(Σ, B)` (Figure 7, lines 1–8): Figure 2's handler with the two lines this
    layer adds — the post-state at line 4, and `update_finality` at line 8.

    The post-state is computed from the parent's, and the parent's is read with the raising
    bracket: a block whose parent the map does not record cannot be evaluated. The draft says
    the handler runs "after every dependency of that object is already in the store: a block's
    parent, and a vote's target block", so on a store that respects that, the read cannot
    fail.

    A parentless block — genesis — has no parent state to read, and the figure does not cover
    it: genesis is in `Σ.T` from the start and is never processed. This rendering rejects it,
    leaving the store unchanged, which is the same thing every other admission failure does. -/
def processBlock (S : Store Validator) (B : Block Validator) :
    ResultOrExcept (Store Validator) := do
  let mut S := S
  if B.slot > S.s then                                         -- line 2
    return S                                                   -- line 3
  -- line 4: `Σ.σ[B] ← state_transition(Σ.σ[B.parent], B)` — new at this layer
  if hp : (B.parent).isSome then
    let σp ← S.σ[(B.parent).get hp]
    S.σ[B] ← some (stateTransition σp B)
  else
    return S
  S.T ← S.T ∪ {B}                                              -- line 5
  S.blockTime[B] ← some S.t
  for vote in B.gfVotes do                                     -- line 6
    S ← Goldfish.processGoldfishVote S vote                     -- line 7
  -- line 8: `update_finality(Σ, Σ.σ[B])` — new at this layer
  return ← updateFinality S (← S.σ[B])

/-! ## The two derived views, and the redefined fork choice -/

/-- `fork_choice_root(Σ)` (Figure 7, lines 16–19): `Σ.J` while the justified pair sits one
    height under the store's frontier, and `Σ.F` otherwise. The only routine of this layer
    that reads no state map, and so the only one that does not raise. -/
def forkChoiceRoot (S : Store Validator) : Block Validator := Id.run do
  if S.h_max = S.h_j + 1 then                                  -- line 17
    return S.J                                                 -- line 18
  return S.F                                                   -- line 19

/-- `get_filtered_block_tree(Σ)` (Figure 7, lines 20–22): the viable blocks at or below the
    fork-choice root, which "limit the selectable children".

    "Goldfish starts at the root even if the root is not in the filtered tree" — so this set
    is a constraint on the walk's *children*, not on its anchor, and the anchor is passed
    separately at line 27. It raises exactly where `viable` does. -/
def getFilteredBlockTree (S : Store Validator) :
    ResultOrExcept (Finset (Block Validator)) := do
  let root := forkChoiceRoot S                                 -- line 21
  return {B ∈ (← viable S) | root ⪯ B}                         -- line 22

/-- `goldfish_eligible(Σ, votes, s, B)` (Figure 7, lines 23–25): Figure 1's gate with a third
    disjunct — "a child whose state height is below `Σ.h_max − 1` is eligible without a
    majority".

    That clause is what lets the walk descend past blocks nobody has voted on yet, which is
    what makes the height filter a filter rather than a wall.

    It raises: the height it tests is `Σ.σ[B].h`, and a block the map does not record has
    none. Figure 1's gate is total, having no state to read. -/
def goldfishEligible (S : Store Validator) (votes : Finset (GoldfishVote Validator)) (s : Nat)
    (B : Block Validator) : ResultOrExcept Bool := do
  let σB ← S.σ[B]
  -- line 25
  return σB.h < S.h_max - 1 ∨
    2 * Goldfish.score votes s B > Goldfish.votersCount votes s ∨ B.slot = S.s

/-- `get_head(Σ, votes, k)` (Figure 7, lines 26–29): the protocol's fork choice. The SG walk
    selects the anchor from the fork-choice root over the filtered tree, and the Goldfish walk
    selects a descendant of it over the same tree. It raises where the filtered tree does.

    **The extended eligibility condition is not what `ghost` receives here**, and that is a
    deviation worth stating plainly. `ghost` takes a `Block → Bool` predicate; this layer's
    condition returns `ResultOrExcept Bool` — it reads `Σ.σ[B].h` — so the two do not compose.
    What the walk is given instead is the same condition with the height clause read through
    the raw `Option`: a block the map does not record fails the height clause rather than
    failing the walk.

    On a store whose `Σ.σ` covers `Σ.T` the two readings agree, and the filtered tree is a
    subset of `Σ.T`, so every block the walk can reach is recorded. Making the walk itself
    raise would mean a monadic `ghost`, and that needs the loop to carry the monad — which is
    a change to Figure 1, not to this line. Left as it is, with the disagreement named. -/
def getHead (S : Store Validator) (votes : Finset (GoldfishVote Validator)) (k : Nat) :
    ResultOrExcept (Block Validator) := do
  let root := forkChoiceRoot S                                 -- line 27
  let tree ← getFilteredBlockTree S
  let anchor := SG.majorityForkChoice S root tree (round S.s)   -- line 28
  -- line 29, with the eligibility condition as described above
  return ghost anchor tree (Goldfish.score votes k)
    (fun B => (S.σ B).any (fun σB => σB.h < S.h_max - 1) ∨
      2 * Goldfish.score votes k B > Goldfish.votersCount votes k ∨ B.slot = S.s)

end ForkChoice

end FG

end Consensus1
