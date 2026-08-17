import Spec.Fig1SlotReplay
import Spec.Defs.Store

/-!
# The companion paper's Figure 2 (`hft:alg:store`) — store and fork-choice root

`full/height_filter_and_timeouts.tex`, Figure 2 (`hft:alg:store`), lines 520–566:
`on_block`, `update_justified`, `update_finalized` and `get_confirmed`. The store record,
its genesis value and the viable subtree are in `Spec/Defs/Store.lean`, which also
records why this paper's store is the one encoded.

All notation comes from `Spec/Defs/Notation.lean`; read that first.

## The routines come callee-first

The figure prints `on_block` first; Lean needs `update_justified` and `update_finalized`
declared before the routine that calls them. Nothing else about the order is meant.

## The one rendering decision: a block that fails admission leaves the store unchanged

The figure writes two asserts (`B.parent ∈ Σ.T`, `Σ.F ⪯ B`) over a total
`state_transition` (its own Figure 1, `hft:alg:state-machine`). Here the transition is the
healing paper's — Figure 1 (`alg:state-replay`), the declared hybrid — which returns
`invalid` on a block that does not extend the parent state or does not advance the slot,
and the state map is `Option`-valued. So admission can fail three ways: a failed assert,
a parent without a recorded state (`Store.replay` returns `invalid` for it; unreachable
once the map-domain coherence invariant is proved), and an `invalid` replay. All three
take the same exit, `return S` with the store untouched — the reading the paper's own
proofs use ("the `on_block` finality-ancestor assertion accepts such a maximum-height
block", Theorem 10, `hft:thm:orderindep`).

Enforcing that decision orders the routine: the replay is tested before the figure's
`Σ.T ← Σ.T ∪ {B}`, so a rejected block never enters `T`. Among the store writes themselves
the figure's order is kept — `T` before `hmax`, `hmax` before either update — so the
viability filter inside `update_finalized` sees both the new block and the new maximum,
which is what the surrounding prose requires and what Lemma 7 (`hft:lem:F-viable`)'s proof
uses.

## The remaining deviation

**`get_confirmed` is a relation first, and a function on top.** The figure's `Ω` is
"whatever extra information the validator uses to disambiguate among viable descendants" —
deliberately unspecified — so the specification is the relation `GetConfirmed S B`, which
holds of exactly the blocks the figure's return line admits; a choice of `Ω` is a choice
among them, and the framework sets the precedent, `Protocol.step` being a relation for the
same reason. Capitalized like every `Prop` here. Beside it (2026-08-17, on instruction)
sit `getConfirmedSet` — the same blocks as a computable `Finset`, `mem_getConfirmedSet`
pinning the two together — and `getConfirmed`, the paper's `get_confirmed(Σ, Ω)` as a
deterministic function with `Ω` ambient through the `Omega` class of
`Spec/Defs/Store.lean`, where the design and its two accepted costs are recorded.
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

/-- `state_transition(Σ.σ[B.parent], B)` (Figure 2, `hft:alg:store`, line 534) with the
    map's `Option` folded in: `invalid` when `B` has no parent or the parent has no
    recorded state. The figure reads the map knowing `B.parent ∈ Σ.T`; once the map-domain
    coherence invariant is proved, the `invalid` from a missing entry cannot arise for a
    block `on_block`'s checks accept. -/
def Store.replay (S : Store Node Root) (B : Blk Node Root) : TransitionResult Node Root :=
  if let some σP := B.parent.bind S.σ then stateTransition σP B else invalid

/-- `on_block(Σ, B)` (Figure 2, `hft:alg:store`, lines 530–540). Admits a block whose
    parent is accepted and which descends from the store-finalized block, replays it from
    its parent's state, and offers the resulting justified pair and finalized block to the
    two updates. See the module header for the one rendering decision: a block that fails
    admission — either assert, or an `invalid` replay — leaves the store unchanged, which
    is why the replay is tested before the figure's `Σ.T ← Σ.T ∪ {B}`. -/
def onBlock (S : Store Node Root) (B : Blk Node Root) : Store Node Root := Id.run do
  let mut S := S
  if let some P := B.parent then                -- `B.parent` may be `⊥`; genesis is rejected
    if P ∈ S.T ∧ S.F ⪯ B then                   -- lines 531–532: the two asserts
      if let .state σ' := S.replay B then       -- line 534: σ' ← state_transition(Σ.σ[B.parent], B)
        S.T ← S.T ∪ {B}                         -- line 533
        S.σ[B] ← some σ'                        -- line 535
        S.hmax ← max S.hmax σ'.h                -- line 536
        S ← updateJustified S σ'.J σ'.h_j       -- line 537
        S ← updateFinalized S σ'.F              -- line 538
  return S                                      -- line 539

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

section
variable [DecidableEq Node] [DecidableEq Root]

/-- The candidate set of `get_confirmed` (Figure 2, `hft:alg:store`, line 561): the blocks
    some `Ω` could pick. Computable; `mem_getConfirmedSet` says membership is exactly the
    relation `GetConfirmed`, so the two views cannot drift apart. -/
def getConfirmedSet (S : Store Node Root) : Finset (Blk Node Root) :=
  (viableTree S).filter fun B => S.R ⪯ B ∧ (S.σ B).any fun st => st.h ≥ S.hmax - 1

/-- The candidate set is the relation: a statement over `GetConfirmed` and one over
    membership in `getConfirmedSet` say the same thing. -/
theorem mem_getConfirmedSet {S : Store Node Root} {B : Blk Node Root} :
    B ∈ getConfirmedSet S ↔ GetConfirmed S B := by
  unfold getConfirmedSet GetConfirmed
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    cases hσ : S.σ B with
    | none => rw [hσ] at h3; exact absurd h3 (by simp)
    | some st =>
        rw [hσ] at h3
        exact ⟨st, rfl, by simpa using h3⟩
  · rintro ⟨h1, h2, st, hst, h3⟩
    have hst' : S.σ B = some st := hst
    refine ⟨h1, h2, ?_⟩
    rw [hst']
    simp
    omega

/-- `get_confirmed(Σ, Ω)` (Figure 2, `hft:alg:store`, lines 559–562) as a deterministic
    function of the store, `Ω` ambient — see `Omega`'s docstring in `Spec/Defs/Store.lean`
    for the design and its two accepted costs. The nonemptiness argument is Corollary 1's
    obligation (`hft:cor:getConfirmed-total`): for an arbitrary store the candidate set can
    be empty; for held stores it is discharged by the store invariants. -/
def getConfirmed [Omega Node Root] (S : Store Node Root)
    (h : (getConfirmedSet S).Nonempty) : Blk Node Root :=
  (Omega.choose (getConfirmedSet S) h).val

/-- Whatever the function returns, the relation admits: every statement over
    `GetConfirmed` applies to the function's output unchanged. -/
theorem getConfirmed_spec [Omega Node Root] (S : Store Node Root)
    (h : (getConfirmedSet S).Nonempty) :
    GetConfirmed S (getConfirmed S h) :=
  mem_getConfirmedSet.mp (Omega.choose (getConfirmedSet S) h).property

end

end Decoupled
