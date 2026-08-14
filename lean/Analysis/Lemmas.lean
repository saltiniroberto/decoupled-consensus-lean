import Analysis.Vocabulary
import Analysis.Proofs.Weights
import Analysis.Proofs.SlotClosure
import Analysis.Proofs.Ancestry
import Analysis.Proofs.Certificates
import Analysis.Proofs.Freshness

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

**Present so far: Lemmas 1 to 7**, all proved and each covering its paper sentence in full. Two
notions came with Lemma 3,
`BlockPostState` and Definition 20's `actionState`, and Lemmas 5 and 6 brought the entries of
`Analysis/Vocabulary.lean` — Definition 11's E2 and Definition 21's justification and progress
certificates.

**One theorem per lemma sentence.** Where a sentence names two subjects — Lemma 4's block
post-state and finality action state — they are conjuncts of one theorem, not two declarations. A
second declaration is for a second *sentence*, as with Lemma 2's "consequently", which needs an
assumption its first sentence does not, or for the paper's own alternative phrasing of a statement
already made, as with `lemEmptySlotNoopFields`.

## The lemmas, and what each waits on

Section 2 "Model and quorum weights" (lines 196–534), Section 3 "Deterministic finality state
machine" (535–980) and Section 4 "Accountable safety" (981–1197). Theorem 5
(`thm:accountable-safety`) is in Section 4 too but is not a lemma, so it is not one of these.

| № | `\label` | Lines | Statable today? |
| --- | --- | --- | --- |
| 1 | `lem:integer-thresholds` | 313–322 | **yes, and proved** — landed |
| 2 | `lem:quorum-intersection` | 342–352 | **yes, and proved** — landed, both sentences |
| 3 | `lem:empty-slot-noop` | 879–891 | **yes, as a `theorem`** — landed |
| 4 | `lem:finalized-before-justified` | 920–931 | **yes, both subjects** — landed and proved |
| 5 | `lem:target-uniqueness` | 967–973 | **yes, and proved** — landed; Defs. 21 and 11 rendered in part |
| 6 | `lem:height-progression` | 987–994 | **yes, in full, and proved** — landed |
| 7 | `lem:height-target-freshness` | 1002–1009 | **yes, in full, and proved** — stated over `postState` |
| 8 | `lem:chain-target-uniqueness` | 1029–1041 | likely yes, over two block post-states |
| 9 | `lem:target-bit-compression` | 1061–1073 | no — the paper gives it no formal shape |
| 10 | `lem:past-finalized` | 1092–1101 | no — Defs. 21 and 11 |
| 11 | `lem:finalized-chain` | 1139–1146 | no — Def. 21 |

**`BlockPostState` replaces `σ[B]` in most places, which is what unblocked Lemma 3.** The paper
writes `σ[B]` where it needs "the state of the chain ending at `B`". A block post-state *is* such a
state, and its own `L` field names that `B`, so a statement of the form "for the chain ending at
`B`" becomes "for a block post-state `σ`, with `B = σ.L`". Nothing about the store or the
state-root function is needed for that reading.

`σ[·]` as a *map* looked necessary wherever a lemma reaches a **named earlier block's** state rather
than the current one. It is not. Lemma 7's "the chain's post-state at `T`" is that case, and
`postState` (`Analysis/Proofs/SlotClosure.lean`) closes it: it replays a block's own chain, so it is
a function of the block, and `postState T = .state σT` names *the* post-state of `T` outright.
`Analysis/Proofs/Determinism.lean` relates it to `BlockPostState` in both directions, which is what
lets a proof carried out over the predicate be stated over the function. Figure 3 is still needed for
what a *store* accepts; it is not needed to name a block's state.

So the count of five waiting on `σ[B]` was pessimistic. Lemmas 3, 4 and 6 are written down over
`BlockPostState`, and Lemma 5's certificates use it too; Lemmas 8 and 10 look expressible over it,
and each will be checked when it is reached rather than assumed here.

## What the specification does not yet carry

| Absent | Paper | Waited on by |
| --- | --- | --- |
| the finality certificate, and "finalized at height `h`" | Def. 21 (`def:certificates`) | 10, 11 |
| the slashing condition E1 | Def. 11 (`def:slashing`) | 10 |
| `σ[·]` as a map, for what a *store* accepts | Figure 3 (`alg:store`), `derive_block_states` | nothing yet |

Definition 11's E2 and Definition 21's justification and progress certificates are no longer on
that list: Lemmas 5 and 6 needed them and they are in `Analysis/Vocabulary.lean`. The rest of each definition stays
absent until a statement needs it, for the reason that file's docstring gives — a declaration no
statement mentions is an unaudited claim about what the paper means.

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

    Read aloud: in a block post-state and in any of its finality action states alike, the finalized
    block is the justified block or an ancestor of it, the justified block is the latest block or an
    ancestor of it, and the finalized height is at most the justified height, which is below the
    state height. Or, in the paper's own summary: finality never moves off the current chain or
    ahead of its latest justification.

    **Both subjects the paper names**, "every reachable block post-state *and finality action
    state*", in one theorem — the second conjunct is the action state's. `actionState` is
    Definition 20 (`def:finality-action-state`)'s state, which is `process_slots` of a block
    post-state; quantifying over every `t` is stronger than the paper's sentence about the one
    action slot, and implies it.

    Proved in `Analysis/Proofs/Ancestry.lean`, from `Chained`: these four claims plus a fifth, that
    a named target lies between `J` and `L`. The fifth is what makes the induction go through and is
    not part of the paper's sentence — the paper asserts it in prose inside its own proof.

    **No threshold hypothesis, where Lemma 3 needs one.** `Chained` is preserved by every branch of
    the height-event check whether or not the branch fires, and survives slot closure whatever the
    tallies hold, so no quorum and no `PositiveWeight` enters. Lemma 3's `Settled` is different: it
    is a claim that the branches *stay blocked*, which fails outright when `q = 0`. -/
theorem lemFinalizedBeforeJustified {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] {σ : ChainState Node Root} (h : BlockPostState σ) (t : Time) :
    let σa := actionState σ t
    (σ.F ⪯ σ.J ∧ σ.J ⪯ σ.L ∧ σ.h_F ≤ σ.h_j ∧ σ.h_j < σ.h) ∧
      (σa.F ⪯ σa.J ∧ σa.J ⪯ σa.L ∧ σa.h_F ≤ σa.h_j ∧ σa.h_j < σa.h) :=
  Proofs.finalizedBeforeJustified h t

/-- **Lemma 5** (`lem:target-uniqueness`, lines 967–973): one height cannot justify two targets.

    Read aloud: if two conflicting blocks each have a justification certificate at the same height,
    then some set of validators of weight at least `2q - W` each signed both of those targets at
    that height, which is E2. Or, in the paper's own summary: one finality height cannot justify two
    forks without exposing one quorum intersection.

    **The "unless" of the paper's sentence is the conclusion, not a hypothesis.** The paper says the
    two certificates cannot both exist "unless validators of total weight at least `2q - W` violate
    E2", and that is what this returns: the set, its weight, and the pair of attestations from each
    validator in it. Nothing is assumed about the fault bound, so nothing has to be — the claim is
    that the evidence exists, not that it is impossible.

    **The evidence is `IncludedOn` the two chains**, `x` on `B` and `y` on `B'`. A bare attestation
    value proves nothing to a consumer that only ever sees blocks, so the conclusion says where each
    one was carried.

    `JustificationCertificate`, `IncludedOn` and `E2` are in `Analysis/Vocabulary.lean`, which
    records what each renders and what it leaves out.

    **Only the quorum clause of each certificate is read** by the proof in
    `Analysis/Proofs/Certificates.lean`. The height-event invocation clause is not touched, so this
    lemma says nothing about it and cannot be cited for it. -/
theorem lemTargetUniqueness {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] (B B' T T' : Blk Node Root) (h : Nat)
    (hJC : JustificationCertificate B h T) (hJC' : JustificationCertificate B' h T')
    (hconf : Conflicts T T') :
    ∃ S : Finset Node, w(S) ≥ 2 * q Node - W Node ∧
      ∀ i ∈ S, ∃ x y : Attestation Node Root,
        x.validator = i ∧ y.validator = i ∧ IncludedOn x B ∧ IncludedOn y B' ∧ E2 x y :=
  Proofs.targetUniqueness B B' T T' h hJC hJC' hconf

/-- **Lemma 6** (`lem:height-progression`, lines 987–994): a certificate advances the height by one.

    Read aloud: if a block's transition changes the height at all, then it raises it by exactly one,
    and the block carries either a justification certificate or a progress certificate for the height
    it left. Or, in the paper's own summary: a chain cannot skip a finality height or advance it
    without a quorum.

    **The paper's whole sentence**, both halves: the increment, and "requires a justification
    certificate or progress certificate". The two certificates are in `Analysis/Vocabulary.lean`.

    "Counted using the fixed validator weights" needs no rendering of its own. `Electorate` fixes `V`
    and `w`, and both certificates count with them, which is Assumption 1's fixed electorate.

    **The paper's "every height transition" is covered by quantifying over `state_transition`.** A
    height transition can only happen at a height-event check, and there are two kinds of those: the
    block's own, which is this transition's last phase, and one per closed empty slot. Lemma 3 is
    what rules the second kind out from a block post-state — the empty-slot checks do not fire — so
    every height transition is a block's, and this covers them all.

    `PositiveWeight Node` for the same reason Lemma 3 needs it: with `q = 0` every empty slot
    advances the height, and then a block after two empty slots raises it by more than one, making
    the first half false. The paper's proof cites Assumption 1 at exactly this point.

    Proved in `Analysis/Proofs/Certificates.lean`. The certificate half needs a third invariant,
    `Witnessed` in `Analysis/Proofs/Witnessed.lean`: a set participation bit has an included
    attestation behind it. Without it a fired branch is a fact about bits, and a certificate is a
    claim about attestations. -/
theorem lemHeightProgression {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [PositiveWeight Node] {σp σ : ChainState Node Root}
    (B : Blk Node Root) (hp : BlockPostState σp) (ht : stateTransition σp B = .state σ)
    (hne : σ.h ≠ σp.h) :
    σ.h = σp.h + 1 ∧
      (JustificationCertificate B σp.h σ.J ∨ ProgressCertificate B σp.h) :=
  Proofs.heightProgression B hp ht hne

/-- **Lemma 7** (`lem:height-target-freshness`, lines 1002–1009): a target bit names the
    current-height target.

    Read aloud: for every validator whose target bit is counted, the vote behind it names the stored
    current-height target, that target is a strict ancestor of the chain's latest block, and the
    target's own post-state is at this height. Or, in the paper's own summary: a target bit always
    refers to the first block of the current height, and is processed only by a later block.

    The paper's "on a chain ending at `B`" is the hypothesis: `σ` is where replaying `B`'s own chain
    ends. Its `h` is `σ.h`, and its `B` is `σ.L`, which `stateTransition_L` puts at `B`. The first
    four conjuncts are the paper's `T = T_h` together with what makes `T` the *counted* vote's
    target; then `≺ B`; then the post-state claim.

    **"The chain's post-state at `T`" is a definite description**, and the last conjunct renders it
    in one equation: the height of the post-state at `T` is `σ.h`. `postState` is a function of the
    block, so the state it names is *the* post-state, and `toOption` is what lets the conjunct say
    so without quantifying over that state; being an equation against `some` it also carries "the
    replay did not fail". Figure 3's `σ[·]` is not needed for any of it, and neither is a uniqueness
    lemma at the use site.

    Proved in `Analysis/Proofs/Freshness.lean`, from a fourth invariant, `Fresh`: a named target is
    on the chain and has a post-state at the current height. Strictness sits outside that invariant
    because it is false at genesis, where `T_h = some genesis` and `L = genesis` — which is exactly
    the case this lemma's own hypothesis excludes, no bit being set there.

    The hypothesis is weaker than the paper's "accepted block", because `postState` replays the
    transition alone and Figure 3 checks three further things. That makes this statement stronger;
    `postState`'s own docstring in `Analysis/Proofs/SlotClosure.lean` says which checks are absent. -/
theorem lemHeightTargetFreshness {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [PositiveWeight Node] {σ : ChainState Node Root}
    {B : Blk Node Root} (hp : postState B = .state σ) :
    ∀ i ∈ σ.Qtarget, ∃ T a, σ.T_h = some T ∧ a.validator = i ∧
      a.heightPair = .target σ.h T ∧ IncludedOn a σ.L ∧ T ≺ σ.L ∧
      (postState T).map ChainState.h = some σ.h :=
  Proofs.heightTargetFreshness (Proofs.blockPostState_of_postState B hp)

end Decoupled
