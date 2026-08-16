import Spec.Defs.Basic

/-!
# The vocabulary the companion paper's store reads

*Simplex-Style Finality with Height Filtering and Timeouts*
(`full/height_filter_and_timeouts.tex` in the same pinned submodule; its labels are cited
with the `hft:` prefix, which `make cites` checks against that paper's own `.aux`).

**Why a second paper.** Decision, Roberto, 2026-08-16: the store this project encodes is the
companion paper's incremental one — Figure 2 (`hft:alg:store`), a stateful store updated as
blocks arrive — not the healing paper's raw-evidence store with derived fork choice
(Figure 3, `alg:store`, of `height_filter_healing.tex`, which stays unencoded). The chain
layer is unchanged: the store runs over this project's `ChainState` and `stateTransition`,
that is, over `height_filter_healing.tex`'s Figures 1 (`alg:state-replay`) and 2
(`alg:attestation-processing`). So the store layer's contract is the companion paper, and
the chain layer's contract remains the healing paper. `CONTEXT.md` records what the choice
defers (the healing paper's Lemma 12, Theorem 7 and the recovery sections, which are about
the raw store and merge).

This file carries what that figure reads and is not itself the figure: the store record
and its genesis value, the viable subtree, and the hash the justification tiebreak
compares. The figure's routines are in `Spec/Timeouts/Fig2Store.lean`.

## The paper's `Σ` is written `S`

`Σ` is a reserved token in Lean (the dependent-pair binder), not a usable identifier —
measured: `def f (Σ : Nat)` is a parse error. Store-valued variables are named `S`
throughout, and nothing else in this project uses that letter for a Lean binder.

## The state map is `Option`-valued

Definition 10 (`hft:def:store`) has `σ` assign "each accepted block its per-chain
post-state". A total function `Blk → ChainState` would invent states for unaccepted blocks,
so the field is `Blk → Option (ChainState Node Root)` and an unaccepted block maps to
`none`. That the map is defined exactly on `T` is then a fact to prove about reachable
stores, not a fact of the type — the same split as the six invariants over
`BlockPostState`.

## `hash` is abstract

The paper's blocks are identified with their hashes, and the store key
`(Σ.h_j, hash(Σ.J))` reads the hash only as a tiebreak. Here `Blk` is content-identified
(see `Spec/Defs/Basic.lean`), so the tiebreak needs a function this project does not
otherwise have; `BlockHash` supplies it abstractly. Only the value is assumed — no
injectivity, because Figure 2 (`hft:alg:store`) reads nothing more. The paper's
collision-freedom idealization joins the class when a proof needs it, and not before.
-/

set_option autoImplicit false

namespace Decoupled

variable {Node Root : Type}

/-- The hash the store key compares. Definition 10 (`hft:def:store`): "The store key
    associated with the root is `(Σ.h_j, hash(Σ.J))`." Abstract, `Nat`-valued; see the
    module header for why no injectivity is assumed yet. -/
class BlockHash (Node Root : Type) where
  /-- `hash(B)`. -/
  hash : Blk Node Root → Nat

@[inherit_doc] scoped notation:max "hash(" B ")" => BlockHash.hash B

/-- Definition 10 (`hft:def:store`): `Σ = (σ, T, F, J, h_j, hmax)`, in the paper's order.
    The paper's `Σ` is written `S` in this project — see the module header. -/
structure Store (Node Root : Type) where
  /-- `σ`, the state map, assigning each accepted block its per-chain post-state. `none`
      on a block outside `T` — see the module header. -/
  σ : Blk Node Root → Option (ChainState Node Root)
  /-- `T`, the block tree: the set of accepted blocks. -/
  T : Finset (Blk Node Root)
  /-- `F`, the store-finalized block. -/
  F : Blk Node Root
  /-- `J`, the store root: the block of the highest-key justification ever observed. -/
  J : Blk Node Root
  /-- `h_j`, the height component of that justification key. -/
  h_j : Nat
  /-- `hmax`, the maximum state-height `σ[B].h` over `B ∈ T`. -/
  hmax : Nat

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node]

/-- The genesis store, as Definition 10 (`hft:def:store`) states it and Figure 2
    (`hft:alg:store`, lines 526–527) repeats it: `T = {genesis}`, `F = J = genesis`,
    `h_j = 0`, `hmax = 1` — matching `σ[genesis].h = 1` — and `σ[genesis] = σ_gen`, which
    is `ChainState.gen` (Definition 13, `def:chain-state`, of the healing paper; the two
    papers state the same initial chain state). -/
def Store.gen : Store Node Root where
  σ := fun B => if B = .genesis then some .gen else none
  T := {.genesis}
  F := .genesis
  J := .genesis
  h_j := 0
  hmax := 1

/-- Definition 11 (`hft:def:viable`), by its own closed form: "Equivalently,
    `B ∈ T'(Σ)` iff some leaf `L ⪰ B` has `σ[L].h ≥ Σ.hmax − 1`." A leaf is a block of `T`
    with no proper descendant in `T`, written `∀ C ∈ S.T, ¬ L ≺ C`. The definition's
    recursive form (a leaf is viable iff its state-height meets the bound; an internal
    block iff some descendant is viable) is equivalent by that same sentence, and is left
    to prove, not encoded.

    `σ[L].h` is read through the map's `Option` by `Option.any`, false on an unmapped `L`;
    a member of `T` that the map misses is the coherence invariant's business, not this
    definition's. -/
def viableTree (S : Store Node Root) : Finset (Blk Node Root) :=
  S.T.filter fun B => ∃ L ∈ S.T, (∀ C ∈ S.T, ¬ L ≺ C) ∧ B ⪯ L ∧
    (S.σ L).any fun st => st.h ≥ S.hmax - 1

end

end Decoupled
