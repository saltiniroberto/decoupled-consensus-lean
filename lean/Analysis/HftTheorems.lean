import StsMultisetLog.Spec.Execution
import Spec.Protocol
import Analysis.Vocabulary
import Analysis.Proofs.Irreversibility

/-!
# The companion paper's numbered theorems — its Section 3.1

*Simplex-Style Finality with Height Filtering and Timeouts*
(`full/height_filter_and_timeouts.tex`, labels cited with the `hft:` prefix). Statements of
record for the six theorem environments of its Section 3.1, "Store invariants and safety",
against the store of `Spec/HftFig2Store.lean`. The section's lemmas and corollary are not
stated; per the selection rule in `CONTEXT.md`, a lemma gets stated when a proof demands it
or on instruction. The rules of `Analysis/Theorems.lean` apply unchanged: each docstring
carries the paper's sentence verbatim, and there is no section-level `variable`.

**Stated on instruction, 2026-08-16; Theorem 3 is proved, the other five are `sorry`.**
So `make dev` counts five here and `make check` fails until they are proved; each proof,
when it lands, becomes a one-line call into `Analysis/Proofs/`, as Theorem 3's is.

## Shared rendering decisions

**Time is the execution.** All six statements quantify over `Exec protocol sched` — the
framework's infinite executions of the node protocol (`Spec/Protocol.lean`) — a validator
and its steps, on instruction (2026-08-16): "at all future times" is a later step of the
same execution, "at all times" is every step, and Theorem 10's "the same available set of
blocks … in any parent-first order" reads each validator's received-block list out of the
execution with `deliveredBlocks`. Each docstring names the store-level core its proof will
establish, phrased with the fold vocabulary of `Analysis/Vocabulary.lean` (`onBlocks`,
`Store.Reachable`, `ParentFirst`) — a validator's store is the fold of what was delivered
to it, so the execution statement follows from its core by walking the steps, as
Theorem 3's proof does. No statement carries an honesty, timing or fairness assumption:
all six are timeless in the framework's classification, and hold of corrupted validators
too, whose `adversarial` action touches only the message log while their store follows
the protocol's reaction.

**"Unless `≥ n/3` validators are slashable" is the accountable disjunct.** The same
rendering as `thmAccountableSafety`: the claim holds, or a set of weight at least `2q − W`
signed slashable pairs. The paper counts validators where this project weighs them
(Definition 3, `def:validator-weights`), and `2q − W` is the weight the intersection of two
`q`-quorums must carry — the count analogue is exactly `n/3`. Slashable is **E1 alone**: the
companion paper's Definition 9 (`hft:def:slashing`) is the single rule E1, the same relation
healing's Definition 11 (`def:slashing`) E1 renders, and it has no E2. Each signer's two
messages are pinned to evidence the statement can name: inclusion on a chain the store
accepted, or on the named finalizing chain where the theorem has one. In the disjunct the
slashable set is written `A`, its members `v`, and the attestation pair `a`/`b` — `x` is
the execution, `i` and `j` are steps, and `q` is the quorum threshold, so none of the
healing files' letters for these are free here.

**"Finalized at height `h_f` on any chain" is a recorded pair.** As in
`thmAccountableSafety`: a chain `B_F` whose replayed post-state records `(F, h_F)` — the
weaker hypothesis, so the statements are stronger than the paper's.

**"Processed by the node" is a recorded state.** `σ[B]` exists in the validator's store's
map. For Theorem 8's "a block `B` is processed by `on_block`", the block is additionally
new at step `i` and recorded at step `i + 1`, so the sentence is about the step that
accepts it.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

/-- **Theorem 3** (`hft:thm:finperm`, lines 583–585): local irreversibility of finality,
    stated on an execution — the first to be, and the rest of the file followed.

    > Once a node sets `Σ.F = F`, `Σ.F` descends from `F` at all future times.

    Read aloud: in any execution of the node protocol, under any schedule, a validator's
    store-finalized block at any step is an ancestor of its store-finalized block at every
    later step.

    Noun by noun. "A node" is a validator `p`, whose store after `i` steps is
    `x[i][p].st` — `Spec/Protocol.lean` makes the store the node state. "Sets `Σ.F = F`":
    `F` is `(x[i][p].st).F`, no binder needed. "At all future times": every step `j ≥ i`
    of the execution. "Descends from" is `⪯`, reflexive as Definition 5
    (`def:block-chain`) makes it, so a step that leaves the store alone counts.

    No honesty, timing or fairness hypothesis: the property is timeless in the framework's
    classification, like accountable safety, and `p` ranges over corrupted validators too —
    corruption in this framework decides what may be *signed* (`Action.adversarial`
    touches only the log), while every change to a validator's own store goes through the
    protocol's reaction, hence through `on_block`. The store-level core is
    `Proofs.onBlocks_F`: `S.F ⪯ (onBlocks S Bs).F` for an arbitrary store `S` — this
    theorem over one fold, needing no reachability because `update_finalized`'s condition
    `F' ≻ Σ.F` is per-step.

    Proved in `Analysis/Proofs/Irreversibility.lean`: `F` moves only inside
    `update_finalized`, whose own condition supplies the `⪯`; the execution walk is
    `Step.elim` per step and `Nat.le_induction` across them. -/
theorem thmLocalIrreversibility {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [BlockHash Node Root]
    {sched : Schedule Node} (x : Exec (protocol (Node := Node) (Root := Root)) sched)
    (p : Node) {i j : Nat} (hij : i ≤ j) :
    (x[i][p].st).F ⪯ (x[j][p].st).F :=
  Proofs.localIrreversibility x p hij

/-- **Theorem 4** (`hft:thm:fleqr`, lines 591–593): `F ⪯ J`, stated on an execution — on
    instruction, 2026-08-16, like Theorem 3.

    > The store maintains `Σ.F ⪯ Σ.J` at all times.

    Read aloud: at every step of any execution of the node protocol, under any schedule,
    every validator's store-finalized block is an ancestor of its store root.

    Noun by noun. "The store" is `x[i][p].st`, validator `p`'s store after `i` steps.
    "Maintains … at all times" is the quantification over `i` — and unlike the store-level
    form, no hypothesis is left: this is an invariant, and what carried it there as
    `S.Reachable` is carried here by the execution itself, whose `init` field starts every
    validator at the genesis store, where `F = J = genesis`. Timeless, and over corrupted
    validators too, for the reason in Theorem 3's docstring. The store-level core the
    proof will establish is the previous statement of record:
    `S.Reachable → S.F ⪯ S.J`. -/
theorem thmFPreceqJ {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [BlockHash Node Root]
    {sched : Schedule Node} (x : Exec (protocol (Node := Node) (Root := Root)) sched)
    (p : Node) (i : Nat) :
    (x[i][p].st).F ⪯ (x[i][p].st).J := sorry

/-- **Theorem 7** (`hft:thm:fcconsistency`, lines 638–640): fork-choice consistency.

    > Once a node sets `Σ.F = F`, `getConfirmed(Σ, Ω)` returns a block descending from `F`
    > at all future times, for every `Ω`.

    Read aloud: once the store finalizes a block, every confirmation it ever offers from
    then on sits below that block.

    Noun by noun. "Once a node sets `Σ.F = F`": `F` is `(x[i][p].st).F`, validator `p`'s
    store-finalized block at step `i`. "At all future times": every step `j ≥ i`.
    "Returns … for every `Ω`": every `C` with `GetConfirmed (x[j][p].st) C` — the relation
    holds of exactly the blocks some `Ω` could pick, so quantifying over its solutions is
    quantifying over `Ω`. The store-level core the proof will establish is the previous
    statement of record: `S.Reachable → GetConfirmed (onBlocks S Bs) C → S.F ⪯ C`. -/
theorem thmForkChoiceConsistency {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [BlockHash Node Root]
    {sched : Schedule Node} (x : Exec (protocol (Node := Node) (Root := Root)) sched)
    (p : Node) {i j : Nat} (hij : i ≤ j)
    {C : Blk Node Root} (hC : GetConfirmed (x[j][p].st) C) :
    (x[i][p].st).F ⪯ C := sorry

/-- **Theorem 8** (`hft:thm:finlive`, lines 683–685): local acceptance of finality updates.

    > Unless `≥ n/3` validators are slashable: if a block `B` is processed by `on_block`
    > and `σ[B].F = F'`, then after processing `Σ.F ⪰ F'`.

    Read aloud: when the store accepts a block whose replayed state records `F'` as
    finalized, the store's own finalized block ends at or below on `F'`'s chain — or a
    third of the validators exposed themselves.

    Noun by noun. "A block `B` is processed by `on_block`": `B` is new to `p`'s store at
    step `i` and has a recorded state at step `i + 1` — the `get` hypothesis reads `σ[B]`
    out of the later store, and the one action that can make the difference is a delivery
    to `p` running `on_block`. "`σ[B].F = F'`": that recorded state's `F`. "After
    processing `Σ.F ⪰ F'`": `F' ⪯ (x[i + 1][p].st).F`. "Unless `≥ n/3` validators are
    slashable": the accountable disjunct of the module header, both messages of each
    signer included on blocks the step-`i + 1` store accepted. The store-level core is the
    previous statement of record, over one `onBlock` call on a reachable store. -/
theorem thmFinalityAcceptance {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [BlockHash Node Root] [PositiveWeight Node]
    {sched : Schedule Node} (x : Exec (protocol (Node := Node) (Root := Root)) sched)
    (p : Node) (i : Nat) {B F' : Blk Node Root}
    (hnew : B ∉ (x[i][p].st).T)
    (hB : get σB from (x[i + 1][p].st).σ B; σB.F = F') :
    F' ⪯ (x[i + 1][p].st).F ∨
      ∃ A : Finset Node, w(A) ≥ 2 * q Node - W Node ∧
        ∀ v ∈ A, ∃ a b : Attestation Node Root, a.validator = v ∧ b.validator = v ∧
          (∃ Ca ∈ (x[i + 1][p].st).T, IncludedOn a Ca) ∧
          (∃ Cb ∈ (x[i + 1][p].st).T, IncludedOn b Cb) ∧ E1 a b := sorry

/-- **Theorem 9** (`hft:thm:lockin`, lines 695–697): lock-in.

    > Unless `≥ n/3` validators are slashable: if block `F` is finalized at height `h_f` on
    > any chain, and some block `B` with `σ[B].J = F` and `σ[B].h_j = h_f` has been
    > processed by the node, then `Σ.J ⪰ F` at all future times, `F ∈ T'(Σ)` at all future
    > times, and `getConfirmed(Σ, Ω)` always returns a descendant of `F`, for every `Ω`.

    Read aloud: once a finalized block's justification has been seen on some processed
    chain, the store root stays at or below it on its chain, it stays viable, and every
    confirmation descends from it — or a third of the validators exposed themselves.

    Noun by noun. "Finalized at height `h_f` on any chain": the recorded pair on `B_F`'s
    replayed post-state, the module header's rendering. "Some block `B` with `σ[B].J = F`
    and `σ[B].h_j = h_f` has been processed by the node": `B` has a recorded state in `p`'s
    store at step `i`, with those two fields — the `get` hypothesis. "At all future times"
    and "always": every step `j ≥ i`, the three claims conjoined under one `j`. "For every
    `Ω`": as in Theorem 7. The disjunct's evidence is included on `B_F`'s chain or on a
    block the step-`j` store accepted, each message independently, since which quorum sits
    where depends on the case. -/
theorem thmLockIn {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [BlockHash Node Root] [PositiveWeight Node]
    {sched : Schedule Node} (x : Exec (protocol (Node := Node) (Root := Root)) sched)
    (p : Node) {i : Nat}
    {B_F F : Blk Node Root} {h_f : Nat} {B : Blk Node Root}
    (hBF : postState B_F ≠ invalid)
    (hF : (postState' B_F).F = F) (hhf : (postState' B_F).h_F = h_f)
    (hB : get σB from (x[i][p].st).σ B; σB.J = F ∧ σB.h_j = h_f)
    {j : Nat} (hij : i ≤ j) :
    (F ⪯ (x[j][p].st).J ∧ F ∈ viableTree (x[j][p].st) ∧
      ∀ C, GetConfirmed (x[j][p].st) C → F ⪯ C) ∨
      ∃ A : Finset Node, w(A) ≥ 2 * q Node - W Node ∧
        ∀ v ∈ A, ∃ a b : Attestation Node Root, a.validator = v ∧ b.validator = v ∧
          (IncludedOn a B_F ∨ ∃ Ca ∈ (x[j][p].st).T, IncludedOn a Ca) ∧
          (IncludedOn b B_F ∨ ∃ Cb ∈ (x[j][p].st).T, IncludedOn b Cb) ∧ E1 a b := sorry

/-- **Theorem 10** (`hft:thm:orderindep`, lines 705–709): order independence.

    > Unless `≥ n/3` validators are slashable: the observable store view after folding the
    > same available set of blocks through `on_block` in any parent-first order depends
    > only on that set, not on the order. In particular, two nodes with the same available
    > blocks agree on `(F, J, h_j, hmax)`, on the accepted subtree rooted at `F`, and hence
    > on the possible outputs of `getConfirmed`.

    Read aloud: two nodes that received the same blocks, each in some parent-respecting
    order, agree on everything fork choice reads — or a third of the validators exposed
    themselves.

    Noun by noun. "Two nodes with the same available blocks": two validators `p` and `p'`
    of one execution, at steps `i` and `j` — what each has folded is its delivered-block
    list, `deliveredBlocks`, and a validator's store is exactly that fold, so "the same
    available set" is the two lists being permutations of each other (`List.Perm`). "In
    any parent-first order": each list `ParentFirst`. "The observable store view" is
    spelled out as the paper's own "in particular" list: the four fields, membership of
    the subtree rooted at `F` — the two `F`s being equal by the first conjunct — and the
    outputs of `get_confirmed`. The paper's third sentence, that the nodes may disagree
    outside `F`'s subtree, is a caveat rather than a claim, and is not stated; agreement
    of the recorded states on the shared subtree is derivable (replay is deterministic)
    and is likewise not stated. The disjunct's evidence is included on a block accepted by
    either of the two stores. The second validator is `p'`, not `q`, which names the
    quorum threshold. -/
theorem thmOrderIndependence {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [BlockHash Node Root] [PositiveWeight Node]
    {sched : Schedule Node} (x : Exec (protocol (Node := Node) (Root := Root)) sched)
    {p p' : Node} {i j : Nat}
    (hperm : (deliveredBlocks x p i).Perm (deliveredBlocks x p' j))
    (hp : ParentFirst (deliveredBlocks x p i))
    (hp' : ParentFirst (deliveredBlocks x p' j)) :
    ((x[i][p].st).F = (x[j][p'].st).F ∧
     (x[i][p].st).J = (x[j][p'].st).J ∧
     (x[i][p].st).h_j = (x[j][p'].st).h_j ∧
     (x[i][p].st).hmax = (x[j][p'].st).hmax ∧
     (∀ C, (x[i][p].st).F ⪯ C → (C ∈ (x[i][p].st).T ↔ C ∈ (x[j][p'].st).T)) ∧
     (∀ C, GetConfirmed (x[i][p].st) C ↔ GetConfirmed (x[j][p'].st) C)) ∨
      ∃ A : Finset Node, w(A) ≥ 2 * q Node - W Node ∧
        ∀ v ∈ A, ∃ a b : Attestation Node Root, a.validator = v ∧ b.validator = v ∧
          (∃ Ca, (Ca ∈ (x[i][p].st).T ∨ Ca ∈ (x[j][p'].st).T) ∧ IncludedOn a Ca) ∧
          (∃ Cb, (Cb ∈ (x[i][p].st).T ∨ Cb ∈ (x[j][p'].st).T) ∧ IncludedOn b Cb) ∧
          E1 a b := sorry

end Decoupled
