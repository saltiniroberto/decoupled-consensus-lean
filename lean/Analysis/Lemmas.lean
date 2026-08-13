import Analysis.Proofs.Weights
import Analysis.Proofs.SlotClosure
import Analysis.Proofs.Ancestry

/-!
# The paper's numbered lemmas

*Height Filtering and Healing for a Simplex-Style Finality Variant*
(`height_filter_healing.tex`). Statements of record, one per numbered lemma, proved against the
specification in `Spec`.

**Being added one at a time**, each audited against the paper by itself. Nine of them were written
in one pass on 2026-08-13 and withdrawn the same day, on instruction; `CONTEXT.md` records that.
The groundwork below is kept from that pass, because re-deriving it is the expensive part.

**Declarations are ordered by the paper's lemma number**, not by when they landed.

**This file holds statements only.** Every proof is a one-line call into `Analysis/Proofs/`, so a
statement can be read against the paper with nothing between it and the reader. Definitions the
statements need — `BlockPostState`, Definition 20's `actionState` — live there too. And there is no
`variable` at section level: each declaration spells out its own binders, so its signature is
readable where it stands rather than assembled from context above it.

**Present so far: Lemmas 1, 2, 3 and 4.** Lemmas 1 to 3 are proved; Lemma 4 is stated with its
proof outstanding. Two notions came with Lemma 3: `BlockPostState` and Definition 20's
`actionState`.

## The lemmas, and what each waits on

Section 2 "Model and quorum weights" (lines 196–534), Section 3 "Deterministic finality state
machine" (535–980) and Section 4 "Accountable safety" (981–1197). Theorem 5
(`thm:accountable-safety`) is in Section 4 too but is not a lemma, so it is not one of these.

| № | `\label` | Lines | Statable today? |
| --- | --- | --- | --- |
| 1 | `lem:integer-thresholds` | 313–322 | **yes, and proved** — landed |
| 2 | `lem:quorum-intersection` | 342–352 | **yes, and proved** — landed, both sentences |
| 3 | `lem:empty-slot-noop` | 879–891 | **yes, as a `theorem`** — landed |
| 4 | `lem:finalized-before-justified` | 920–931 | **yes, over a block post-state** — landed, proof outstanding |
| 5 | `lem:target-uniqueness` | 967–973 | no — Defs. 21 and 11 |
| 6 | `lem:height-progression` | 987–994 | **in part, and nothing is missing** — see below |
| 7 | `lem:height-target-freshness` | 1002–1009 | no — `σ[·]` at a named earlier block |
| 8 | `lem:chain-target-uniqueness` | 1029–1041 | likely yes, over two block post-states |
| 9 | `lem:target-bit-compression` | 1061–1073 | no — the paper gives it no formal shape |
| 10 | `lem:past-finalized` | 1092–1101 | no — Defs. 21 and 11 |
| 11 | `lem:finalized-chain` | 1139–1146 | no — Def. 21 |

**`BlockPostState` replaces `σ[B]` in most places, which is what unblocked Lemma 3.** The paper
writes `σ[B]` where it needs "the state of the chain ending at `B`". A block post-state *is* such a
state, and its own `L` field names that `B`, so a statement of the form "for the chain ending at
`B`" becomes "for a block post-state `σ`, with `B = σ.L`". Nothing about the store or the
state-root function is needed for that reading.

`σ[·]` as a *map* is still needed where a lemma reaches a **named earlier block's** state rather
than the current one — Lemma 7's "the chain's post-state at `T`" is the clear case, `T` being an
ancestor of `B`. Getting at that needs either Figure 3's map or a lemma relating `BlockPostState`
to ancestors.

So the count of five waiting on `σ[B]` was pessimistic. Lemmas 3 and 4 are written down over
`BlockPostState`; Lemmas 8 and 10 look expressible over it too, and each will be checked when it is
reached rather than assumed here. Lemma 6's increment half remains independently statable, needing only
`advanceHeight`.

## What the specification does not yet carry

| Absent | Paper | Waited on by |
| --- | --- | --- |
| certificates, and "finalized at height `h`" | Def. 21 (`def:certificates`) | 5, 6, 10, 11 |
| the slashing conditions E1 and E2 | Def. 11 (`def:slashing`) | 5, 10 |
| `σ[·]` as a map, for a *named earlier* block's state | Figure 3 (`alg:store`), `derive_block_states` | 7 |

**Assumption 1's Byzantine weight `b` is not on that list, and Lemma 1 is why.** `Electorate`
carries `V`, `w` and `w_pos` only, so `b` has no rendering — but a *quantity* arrives with its
defining inequality, and quantifying over every `b` with `3 * b < W` is both faithful and stronger
than the paper's sentence about the one actual Byzantine weight. So it costs a hypothesis, not a
`def … : Prop`.

That is the line to keep in mind for the rest: an absent **definition** — certificates, the
slashing conditions, `σ[·]` — has no properties to quantify over, so a statement naming it can only
be a `def … : Prop`. An absent **quantity with a stated bound** is just a universally quantified
variable, and the statement stays a `theorem`.

**Two notions the paper numbers are not on it**, because the state machine already pins them
down: state-height (Def. 6, `def:state-height`) and the current-height target (Def. 7,
`def:current-height-target`) are `σ.h` and `σ.T_h` of the replayed state. Worth knowing before
anyone models them separately.

**Why `σ[·]` is not a fold of `stateTransition`**, which is what makes `BlockPostState` the
honest substitute rather than a shortcut. Measured against `height_filter_healing.tex:1555-1577`:
the map is built by `derive_block_states` in Figure 3 (`alg:store`), and a block enters it only
when all of

    structural_precheck(x, B, B.parent) = valid          -- Definition 24's first part
    state_transition(σ[B.parent], B) ≠ invalid
    B's claimed post-state root = root(σ')               -- needs a state-root function

hold, over the objects of a store `S` whose clock admits the block's slot. A withdrawn earlier pass
defined `replayChain` as the plain fold and called it `σ[B]`; it omitted the precheck and the
claimed-root check, so it accepted a block whose `claimedRoot` disagrees with its own post-state,
which Figure 3 rejects. `BlockPostState` omits the same two checks but does not claim to be
`σ[·]` — it is only a superset of it, which is why a theorem over it is stronger rather than wrong.

Note also that Definition 24 governs *when* `state_transition` is called and that it is total; the
map itself is Figure 3's. An earlier note here said the replay belonged in `Spec` under
Definition 24. It does not.

## Two shapes, when statements do start landing

Every lemma written down but unproved is one state — `MAPPING.md` marks it 🔨 *stated*. The Lean
shape is forced by how much vocabulary exists and is not a difference in progress:

* a `theorem` here, proved in `Proofs/` — by a real argument if there is one, by `sorry` if not.
  `make dev` allows the `sorry` and counts it; `make check` refuses it.
* a `def … : Prop` in `Proofs/`, taking the absent notion as an argument, where the sentence is not
  expressible at all. It must not be a `theorem`: over an unconstrained argument the claim would be
  *false* rather than unproved, and a `sorry` would hide that.

`make check` catches only the first shape, so green means "no `sorry`", not "the paper's results
are proved". `MAPPING.md` is what answers the second question.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

/-! ## Section 2 — model and quorum weights -/

/-- **Lemma 1** (`lem:integer-thresholds`, lines 313–322): the honest weight reaches every protocol
    threshold.

    Read aloud: all honest validators together can form either threshold, while the Byzantine
    validators alone can form neither.

    `b` is Assumption 1 (`ass:fixed-electorate`)'s Byzantine weight, and `3 * b < W` is that
    assumption's bound. `Electorate` carries no `b`, so it is a parameter here — but unlike an
    absent *definition*, a number arrives with its defining inequality, so this is a `theorem` and
    not a `def … : Prop`. Quantifying over every `b` under the bound is stronger than the paper's
    sentence about the one actual Byzantine weight, and implies it.

    Two notes on `Nat`. Both subtractions are truncated, which is harmless: `3 * b < W` forces
    `b < W`, and `2 * q ≥ W` holds for every `W ≥ 1`. And `W = 0` is excluded by the same
    hypothesis — at `W = 0` the claim `q ≥ m` is false, since `q = 0` while `m = 1`. -/
theorem lemIntegerThresholds {Node : Type} [Electorate Node]
    (b : Nat) (hb : 3 * b < W Node) :
    W Node - b ≥ q Node ∧ q Node ≥ m Node ∧ m Node > b ∧ q Node > b ∧
      2 * q Node - W Node > b :=
  Proofs.integerThresholds b hb

/-- **Lemma 2** (`lem:quorum-intersection`, lines 342–352): two quorums intersect in weight at
    least `2q - W`.

    Read aloud: two finality quorums share enough weight to expose a fault if they certify
    incompatible claims.

    `Q ⊆ V` and `Q' ⊆ V` are the paper's own side conditions — it says "any two quorums
    `Q, Q' ⊆ V`". Both are needed: `Quorum` constrains a set's weight, not its membership, and a
    quorum reaching outside the electorate could weigh more than `W`.

    The `Nat` subtraction is truncated, which costs nothing: where `2q ≤ W` the bound is `≥ 0`,
    and Lemma 1 is what says `2q - W` is in fact positive. -/
theorem lemQuorumIntersection {Node : Type} [DecidableEq Node] [Electorate Node]
    {Q Q' : Finset Node} (hQV : Q ⊆ Electorate.V) (hQ'V : Q' ⊆ Electorate.V)
    (hQ : w(Q)≥q) (hQ' : w(Q')≥q) :
    w(Q ∩ Q') ≥ 2 * q Node - W Node :=
  Proofs.quorumIntersection hQV hQ'V hQ hQ'

/-- **Lemma 2**'s second sentence: "consequently their intersection contains non-Byzantine weight
    under Assumption 1 (`ass:fixed-electorate`)".

    Separate from `lemQuorumIntersection` because it needs that assumption's Byzantine weight `b`
    and the bound `3 * b < W`, which the first sentence does not. -/
theorem lemQuorumIntersectionNonByzantine {Node : Type} [DecidableEq Node] [Electorate Node]
    {Q Q' : Finset Node} (hQV : Q ⊆ Electorate.V) (hQ'V : Q' ⊆ Electorate.V)
    (hQ : w(Q)≥q) (hQ' : w(Q')≥q) (b : Nat) (hb : 3 * b < W Node) :
    w(Q ∩ Q') > b :=
  Proofs.quorumIntersectionNonByzantine hQV hQ'V hQ hQ' b hb

/-! ## Section 3 — deterministic finality state machine -/

/-- **Lemma 3** (`lem:empty-slot-noop`, lines 879–891): an empty slot never changes height,
    finality, or participation.

    Read aloud: closing empty slots can name a pending target, but can never advance the chain.

    Stated as **one record equation** rather than as the paper's list of fields that do not move.
    That says what `s` and `T_h` become, which the list leaves free, and it says nothing else moves
    — a field added to `ChainState` later cannot weaken it, where it would silently weaken a
    conjunction. `lemEmptySlotNoopFields` below is the paper's own phrasing, derived from this.

    The paper compares `σ_a[X]` with `σ[X]`. Definition 20 makes the first `process_slots` of the
    second, so this is a claim about `process_slots` over a block post-state, and needs neither
    Figure 3 nor Definition 20 as an argument. `BlockPostState` and `actionState` are declared in
    `Analysis/Proofs/SlotClosure.lean`.

    **One hypothesis the paper does not write, and one it implies.** `BlockPostState σ` is the
    reachability its prose leaves implicit — over an arbitrary state the claim is false, since the
    height-event check can fire. `PositiveWeight Node` is needed too, because on an empty
    electorate `q = ⌈2W/3⌉` is `0`, every set is a quorum and no branch is ever blocked — but that
    one is not an addition: either of the paper's fault bounds gives it, and
    `PositiveWeight.ofFaultBound` is that step.

    Against those, `BlockPostState` admits more states than `σ[·]`, so in that respect the
    statement is stronger than the paper's.

    `T_h` is left open rather than pinned exactly. Pinning it needs the induction to split `n = 0`
    from `n ≥ 1`, and nothing yet needs to know *which* target was named. -/
theorem lemEmptySlotNoop {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [PositiveWeight Node] {σ : ChainState Node Root} (t : Time)
    (h : BlockPostState σ) :
    ∃ Th, (Th = σ.T_h ∨ Th = some σ.L) ∧
      actionState σ t = { σ with s := max σ.s t, T_h := Th } :=
  Proofs.emptySlotNoop t h

/-- **Lemma 3** in the paper's own phrasing: the fields it lists as unchanged. Derived from the
    record equation above, and kept so a reader checking the Lean against the `.tex` finds the
    list. -/
theorem lemEmptySlotNoopFields {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [PositiveWeight Node] {σ : ChainState Node Root} (t : Time)
    (h : BlockPostState σ) :
    let σa := actionState σ t
    σa.L = σ.L ∧ σa.h = σ.h ∧ σa.s_h = σ.s_h ∧ σa.nj = σ.nj ∧
    σa.J = σ.J ∧ σa.h_j = σ.h_j ∧ σa.F = σ.F ∧ σa.h_F = σ.h_F ∧ σa.P = σ.P ∧
    σa.targetParticipation = σ.targetParticipation ∧ σa.progress = σ.progress := by
  obtain ⟨Th, -, heq⟩ := lemEmptySlotNoop t h
  rw [heq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Lemma 4** (`lem:finalized-before-justified`, lines 920–931): the finalized block precedes the
    justified and latest blocks.

    Read aloud: the finalized block is the justified block or an ancestor of it, the justified
    block is the latest block or an ancestor of it, and the finalized height is at most the
    justified height, which is below the state height. Or, in the paper's own summary: finality
    never moves off the current chain or ahead of its latest justification.

    **The proof is outstanding**, a `sorry` in `Analysis/Proofs/Ancestry.lean`, which says what it
    needs: a further invariant about the named target, which the paper asserts in prose inside its
    own proof.

    **Narrower than the paper's sentence in one respect.** The paper says "every reachable block
    post-state *and finality action state*"; this covers the block post-state. The other half is a
    corollary of Lemma 3 once this is proved — `actionState` moves only `s` and `T_h`, so it moves
    none of the six fields named here — and it will be added then rather than guessed at now. -/
theorem lemFinalizedBeforeJustified {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] {σ : ChainState Node Root} (h : BlockPostState σ) :
    σ.F ⪯ σ.J ∧ σ.J ⪯ σ.L ∧ σ.h_F ≤ σ.h_j ∧ σ.h_j < σ.h :=
  Proofs.finalizedBeforeJustified h

end Decoupled
