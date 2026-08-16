import Spec.Fig1SlotReplay
import Spec.Timeouts.Defs

/-!
# The companion paper's Figure 2 (`hft:alg:store`) — store and fork-choice root

`full/height_filter_and_timeouts.tex`, Figure 2 (`hft:alg:store`), lines 520–566:
`on_block`, `update_justified`, `update_finalized` and `get_confirmed`. The store record,
its genesis value and the viable subtree are in `Spec/Timeouts/Defs.lean`, which also
records why this paper's store is the one encoded.

All notation comes from `Spec/Defs/Notation.lean`; read that first.

## The routines come callee-first

The figure prints `on_block` first; Lean needs `update_justified` and `update_finalized`
declared before the routine that calls them. Nothing else about the order is meant.

## Deviations from the figure's own spelling

**The asserts leave the store unchanged.** The figure opens `on_block` with
`assert B.parent ∈ Σ.T` and `assert Σ.F ⪯ B`. A block failing either is not accepted —
that is the reading the paper's own proofs use ("the `on_block` finality-ancestor assertion
accepts such a maximum-height block", Theorem 10, `hft:thm:orderindep`) — so each assert is
rendered as `return S` with the store untouched.

**`state_transition` here can reject, and rejection leaves the store unchanged.** The
figure's `state_transition` is the companion paper's own (its Figure 1,
`hft:alg:state-machine`), which is total. This project runs the store over the healing
paper's transition instead — `stateTransition` of Figure 1 (`alg:state-replay`), the
declared hybrid — and that one returns `invalid` on a block that does not extend the
parent state or does not advance the slot. An `invalid` is treated as a failed assert:
`return S`. For that reason the transition is evaluated *before* the figure's
`Σ.T ← Σ.T ∪ {B}`, so a rejected block never enters `T`; among the store writes themselves
the figure's order is kept — `T` before `hmax`, `hmax` before either update, so the
viability filter inside `update_finalized` sees both the new block and the new maximum,
which is what the surrounding prose requires and what Lemma 7 (`hft:lem:F-viable`)'s proof
uses.

**`σ[B.parent]` is read through the map's `Option`.** The `let some σP :=` line has no
counterpart in the figure, which reads the map knowing `B.parent ∈ Σ.T`. Once the
map-domain coherence invariant is proved the branch is unreachable; until then it too is a
failed assert.

**`get_confirmed` is a relation, not a function.** The figure's `Ω` is "whatever extra
information the validator uses to disambiguate among viable descendants" — deliberately
unspecified. `GetConfirmed S B` holds of exactly the blocks the figure's return line
admits, and a choice of `Ω` is a choice among them. The framework sets the precedent:
`Protocol.step` is a relation for the same reason. Capitalized like every `Prop` here.
-/

set_option autoImplicit false

namespace Decoupled

variable {Node Root : Type}

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-- `update_justified(Σ, J', h')` (Figure 2, `hft:alg:store`, lines 543–548): the
    `F`-filter, then the running max on the justification key. The figure's
    `(h', hash(J')) > (Σ.h_j, hash(Σ.J))` is the strict lexicographic order, written out. -/
def updateJustified (S : Store Node Root) (J' : Blk Node Root) (h' : Nat) :
    Store Node Root := Id.run do
  let mut S := S
  if S.F ⪯ J' ∧ (S.h_j < h' ∨ (h' = S.h_j ∧ hash(S.J) < hash(J'))) then  -- line 544
    S.J ← J'                                                             -- line 545
    S.h_j ← h'                                                           -- line 545
  return S                                                               -- line 547

/-- `update_finalized(Σ, F')` (Figure 2, `hft:alg:store`, lines 551–556). The figure's
    `F' ≻ Σ.F` is written `S.F ≺ F'`; the last conjunct is the viability check the
    surrounding prose names. -/
def updateFinalized (S : Store Node Root) (F' : Blk Node Root) :
    Store Node Root := Id.run do
  let mut S := S
  if S.F ≺ F' ∧ F' ⪯ S.J ∧ F' ∈ viableTree S then                        -- line 552
    S.F ← F'                                                             -- line 553
  return S                                                               -- line 555

/-- `on_block(Σ, B)` (Figure 2, `hft:alg:store`, lines 530–540). Admits a block whose
    parent is accepted and which descends from the store-finalized block, replays it from
    its parent's state, and offers the resulting justified pair and finalized block to the
    two updates. See the module header for the three rendering decisions: asserts as
    `return S`, the `Option` read of `σ[B.parent]`, and an `invalid` transition rejecting
    the block before it enters `T`. -/
def onBlock (S : Store Node Root) (B : Blk Node Root) : Store Node Root := Id.run do
  let mut S := S
  let some P := B.parent | return S           -- line 531: assert B.parent ∈ Σ.T …
  if P ∉ S.T ∨ ¬ S.F ⪯ B then                 -- … and line 532: assert Σ.F ⪯ B
    return S
  let some σP := S.σ P | return S             -- the Option read; see the module header
  let .state σ' := stateTransition σP B       -- line 534: σ' ← state_transition(Σ.σ[B.parent], B)
    | return S                                -- the hybrid's rejection; see the module header
  S.T ← S.T ∪ {B}                             -- line 533
  S.σ[B] ← some σ'                            -- line 535
  S.hmax ← max S.hmax σ'.h                    -- line 536
  S ← updateJustified S σ'.J σ'.h_j           -- line 537
  S ← updateFinalized S σ'.F                  -- line 538
  return S                                    -- line 539

/-- `R`, `get_confirmed`'s walk-from block (Figure 2, `hft:alg:store`, line 560): the
    store root while it sits at the frontier — `hmax = h_j + 1`, the figure's comment —
    and the store-finalized block once a timeout has moved some chain one height further.
    The figure binds `R` inside `get_confirmed`; it is its own function here so the
    cascade rule is nameable outside the figure. -/
def Store.R (S : Store Node Root) : Blk Node Root :=
  if S.hmax = S.h_j + 1 then S.J else S.F                                -- line 560

/-- `get_confirmed(Σ, Ω)` (Figure 2, `hft:alg:store`, lines 559–562), as the relation the
    figure's return line defines — see the module header on `Ω`. The walk-from block `R`
    is `Store.R` above. -/
def GetConfirmed (S : Store Node Root) (B : Blk Node Root) : Prop :=
  B ∈ viableTree S ∧ S.R ⪯ B ∧ (get st from S.σ B; st.h ≥ S.hmax - 1)    -- line 561

end

end Decoupled
