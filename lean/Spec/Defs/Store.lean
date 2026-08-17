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
compares. The figure's routines are in `Spec/HftFig2Store.lean`.

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

/-- **The paper's collision-freedom idealization**, as a separate class so that only the
    results that need it carry it — the same treatment `PositiveWeight`
    (`Analysis/Proofs/Weights.lean`) gets.

    The companion paper identifies a block with its hash ("The paper's blocks are identified
    with their hashes", module header above), so in its model this holds by construction. Here
    `Blk` is content-identified and `hash` is an abstract function, so the identification has to
    be assumed where a proof relies on it.

    One result relies on it: Theorem 10 (`hft:thm:orderindep`)'s claim that two nodes agree on
    `Σ.J`. `update_justified` breaks ties on `hash(J)`, so two distinct blocks justified at one
    height with equal hashes would leave the store root decided by arrival order, and neither
    that nor the resulting conflict is a Definition 9 (`hft:def:slashing`) violation — that
    definition is E1 and has no rule about two targets at one height. Everything else in
    Section 3.1 is proved without this class. -/
class HashInjective (Node Root : Type) [BlockHash Node Root] : Prop where
  /-- Distinct blocks have distinct hashes. -/
  inj : ∀ B B' : Blk Node Root, hash(B) = hash(B') → B = B'

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

/-! ## Definition 10's `B ∈ σ` and `σ[B]`, through `Membership` and `GetElem`

The paper writes `Σ.σ[B]` for the state the store records for `B`, and writes it
unconditionally, because in its model the map is defined exactly on the accepted blocks. Here
the field is `Option`-valued — see the module header for why — so a bare read owes a proof that
`B` is recorded, and that proof needs a name of its own.

Both come from standard classes, so this adds no syntax:

* `B ∈ S.σ` — `Membership` on the map, "the map is defined at `B`". Definitionally
  `(S.σ B).isSome`.
* `S.σ[B] : ChainState Node Root` — `GetElem`. `xs[i]` elaborates to
  `getElem xs i (by get_elem_tactic)`, and `get_elem_tactic` tries `assumption` before
  anything else, so the side condition `B ∈ S.σ` comes from the context.
* `S.σ[B]? : Option (ChainState Node Root)` — which **is** `S.σ B`, definitionally.
* `S.σ[B]!` would panic, and nothing uses it.

The instances are on the **map's type** rather than on `Store`, which is what makes the
notation read `S.σ[B]` and not `S[B]`, and all are `scoped`.

## Two hazards, both measured

**`∈` says two different things about this one field.** In `B ∈ S.σ` the element is a *key*;
in `st ∈ S.σ B` — core's `Option` membership, which means `S.σ B = some st` — it is a *value*.
No ambiguity reaches the elaborator, the container types being different, but the two readings
sit close enough that this note exists.

The `Membership` dead end `CONTEXT.md` records for 2026-08-16 does **not** apply: that one
gave `Finset α` a second instance and lost, because the element type is an `outParam` driven
by the container and resolution does not backtrack. A function type has no competing instance.

**The `∀ x ∈ s` binder does not reach the bracket.** `∀ B ∈ S.σ, S.σ[B].h ≥ 1` fails, because
that is `∀ B, B ∈ S.σ → …` and an arrow's antecedent is not a binder, so `assumption` has
nothing to find. Write `∀ B (_ : B ∈ S.σ), …`. This is the bracket's property, not the
instance's — `(S.σ B).isSome` fails the same way.

## And the friction that keeps this out of the proof layer

The read carries its proof, so `rw` on a store inside one fails with "motive is not type
correct" where `simp only` succeeds — `CONTEXT.md`'s 2026-08-15 entry on
`TransitionResult.get`, measured again for this shape. Only statements of record use it.

`Spec/Defs/Notation.lean`'s `idxAssign` claims `ident noWs "[" term "]" " ← " term` as a
`doElem`, which is how `on_block` writes `S.σ[B] ← some σ'`. That macro still wins in `do`
position; the build is what checks it. -/

/-- `B ∈ σ`: the map is defined at `B`. -/
scoped instance stateMapMembership :
    Membership (Blk Node Root) (Blk Node Root → Option (ChainState Node Root)) where
  mem σ B := (σ B).isSome

/-- `σ[B]`: the state recorded for `B`, given that `B` is recorded. -/
scoped instance stateMapGetElem :
    GetElem (Blk Node Root → Option (ChainState Node Root)) (Blk Node Root)
      (ChainState Node Root) (fun σ B => B ∈ σ) where
  getElem σ B h := (σ B).get h

/-- `σ[B]?`: the same read with no side condition, which is the map itself. -/
scoped instance stateMapGetElemOpt :
    GetElem? (Blk Node Root → Option (ChainState Node Root)) (Blk Node Root)
      (ChainState Node Root) (fun σ B => B ∈ σ) where
  getElem? σ B := σ B

/-- The two agree, which is what lets the core `getElem?_pos`/`getElem?_neg` lemmas fire. -/
scoped instance stateMapLawfulGetElem :
    LawfulGetElem (Blk Node Root → Option (ChainState Node Root)) (Blk Node Root)
      (ChainState Node Root) (fun σ B => B ∈ σ) where
  getElem?_def σ B _ := by
    by_cases hb : B ∈ σ
    · rw [dif_pos hb]
      exact (Option.some_get hb).symm
    · rw [dif_neg hb]
      have hb' : ¬ (σ B).isSome = true := hb
      have h2 : σ B = none := by simpa using hb'
      exact h2

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
