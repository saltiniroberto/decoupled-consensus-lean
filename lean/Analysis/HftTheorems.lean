import StsMultisetLog.Spec.Execution
import Spec.Protocol
import Analysis.Vocabulary

/-!
# The companion paper's numbered theorems — its Section 3.1

*Simplex-Style Finality with Height Filtering and Timeouts*
(`full/height_filter_and_timeouts.tex`, labels cited with the `hft:` prefix). Statements of
record for the six theorem environments of its Section 3.1, "Store invariants and safety",
against the store of `Spec/HftFig2Store.lean`. The section's lemmas and corollary are not
stated; per the selection rule in `CONTEXT.md`, a lemma gets stated when a proof demands it
or on instruction. The rules of `Analysis/Theorems.lean` apply unchanged: each docstring
carries the paper's sentence verbatim, and there is no section-level `variable`.

**Statements only, on instruction (Roberto, 2026-08-16): every proof is a `sorry`.** So
`make dev` counts six here and `make check` fails until they are proved; each proof, when it
lands, becomes a one-line call into `Analysis/Proofs/`.

## Shared rendering decisions

**Time is the received-block sequence — except in Theorems 3 and 4, which are on
executions.** `on_block` is the store's only mutator, so "at all future times" is "after
any further `onBlocks`", and "the store maintains … at all times" is a hypothesis
`S.Reachable`; both notions are in `Analysis/Vocabulary.lean`. Theorems 3 and 4 instead
read time as the steps of a framework execution of the node protocol
(`Spec/Protocol.lean`), on instruction — each quantifies over `Exec protocol sched` and a
validator, and each docstring names the store-level core its proof will establish.

**"Unless `≥ n/3` validators are slashable" is the accountable disjunct.** The same
rendering as `thmAccountableSafety`: the claim holds, or a set of weight at least `2q − W`
signed slashable pairs. The paper counts validators where this project weighs them
(Definition 3, `def:validator-weights`), and `2q − W` is the weight the intersection of two
`q`-quorums must carry — the count analogue is exactly `n/3`. Slashable is **E1 alone**: the
companion paper's Definition 9 (`hft:def:slashing`) is the single rule E1, the same relation
healing's Definition 11 (`def:slashing`) E1 renders, and it has no E2. Each signer's two
messages are pinned to evidence the statement can name: inclusion on a chain the store
accepted, or on the named finalizing chain where the theorem has one. The slashable set is
written `A`, because `S` names the store in this file.

**"Finalized at height `h_f` on any chain" is a recorded pair.** As in
`thmAccountableSafety`: a chain `B_F` whose replayed post-state records `(F, h_F)` — the
weaker hypothesis, so the statements are stronger than the paper's.

**"Processed by the node" is a recorded state.** `σ[B]` exists in the store's map. For
Theorem 8's "a block `B` is processed by `on_block`", the block is additionally new
(`B ∉ S.T`), so the sentence is about the call that accepts it.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

/-- **Theorem 3** (`hft:thm:finperm`, lines 583–585): local irreversibility of finality,
    stated on an execution — on instruction, 2026-08-16; the other five theorems are
    store-level for now.

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
    protocol's reaction, hence through `on_block`. The store-level core the proof will
    establish is `S.F ⪯ (onBlocks S Bs).F` for an arbitrary store `S` — this theorem over
    one fold, needing no reachability because `update_finalized`'s condition `F' ≻ Σ.F` is
    per-step. -/
theorem thmLocalIrreversibility {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [BlockHash Node Root]
    {sched : Schedule Node} (x : Exec (protocol (Node := Node) (Root := Root)) sched)
    (p : Node) {i j : Nat} (hij : i ≤ j) :
    (x[i][p].st).F ⪯ (x[j][p].st).F := sorry

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

    Noun by noun. "Once a node sets `Σ.F = F`": `S` reachable, `F` is `S.F`. "At all future
    times": the store `onBlocks S Bs`. "Returns … for every `Ω`": every `C` with
    `GetConfirmed (onBlocks S Bs) C` — the relation holds of exactly the blocks some `Ω`
    could pick, so quantifying over its solutions is quantifying over `Ω`. -/
theorem thmForkChoiceConsistency {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [BlockHash Node Root]
    {S : Store Node Root} (hS : S.Reachable) {Bs : List (Blk Node Root)}
    {C : Blk Node Root} (hC : GetConfirmed (onBlocks S Bs) C) :
    S.F ⪯ C := sorry

/-- **Theorem 8** (`hft:thm:finlive`, lines 683–685): local acceptance of finality updates.

    > Unless `≥ n/3` validators are slashable: if a block `B` is processed by `on_block`
    > and `σ[B].F = F'`, then after processing `Σ.F ⪰ F'`.

    Read aloud: when the store accepts a block whose replayed state records `F'` as
    finalized, the store's own finalized block ends at or below on `F'`'s chain — or a
    third of the validators exposed themselves.

    Noun by noun. "A block `B` is processed by `on_block`": `B` is new (`B ∉ S.T`) and the
    call leaves it a recorded state — the `get` hypothesis reads `σ[B]` out of the
    post-call map. "`σ[B].F = F'`": that recorded state's `F`. "After processing
    `Σ.F ⪰ F'`": `F' ⪯ (onBlock S B).F`. "Unless `≥ n/3` validators are slashable": the
    accountable disjunct of the module header, both messages of each signer included on
    blocks the post-call store accepted. -/
theorem thmFinalityAcceptance {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [BlockHash Node Root] [PositiveWeight Node]
    {S : Store Node Root} (hS : S.Reachable) {B : Blk Node Root} {F' : Blk Node Root}
    (hnew : B ∉ S.T)
    (hB : get σB from (onBlock S B).σ B; σB.F = F') :
    F' ⪯ (onBlock S B).F ∨
      ∃ A : Finset Node, w(A) ≥ 2 * q Node - W Node ∧
        ∀ i ∈ A, ∃ x y : Attestation Node Root, x.validator = i ∧ y.validator = i ∧
          (∃ Cx ∈ (onBlock S B).T, IncludedOn x Cx) ∧
          (∃ Cy ∈ (onBlock S B).T, IncludedOn y Cy) ∧ E1 x y := sorry

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
    and `σ[B].h_j = h_f` has been processed": `B` has a recorded state in `S` with those
    two fields — the `get` hypothesis. "At all future times" and "always": the store
    `onBlocks S Bs`, the three claims conjoined under one `Bs`. "For every `Ω`": as in
    Theorem 7. The disjunct's evidence is included on `B_F`'s chain or on a block the
    future store accepted, each message independently, since which quorum sits where
    depends on the case. -/
theorem thmLockIn {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [BlockHash Node Root] [PositiveWeight Node]
    {S : Store Node Root} (hS : S.Reachable)
    {B_F F : Blk Node Root} {h_f : Nat} {B : Blk Node Root}
    (hBF : postState B_F ≠ invalid)
    (hF : (postState' B_F).F = F) (hhf : (postState' B_F).h_F = h_f)
    (hB : get σB from S.σ B; σB.J = F ∧ σB.h_j = h_f)
    (Bs : List (Blk Node Root)) :
    (F ⪯ (onBlocks S Bs).J ∧ F ∈ viableTree (onBlocks S Bs) ∧
      ∀ C, GetConfirmed (onBlocks S Bs) C → F ⪯ C) ∨
      ∃ A : Finset Node, w(A) ≥ 2 * q Node - W Node ∧
        ∀ i ∈ A, ∃ x y : Attestation Node Root, x.validator = i ∧ y.validator = i ∧
          (IncludedOn x B_F ∨ ∃ Cx ∈ (onBlocks S Bs).T, IncludedOn x Cx) ∧
          (IncludedOn y B_F ∨ ∃ Cy ∈ (onBlocks S Bs).T, IncludedOn y Cy) ∧ E1 x y := sorry

/-- **Theorem 10** (`hft:thm:orderindep`, lines 705–709): order independence.

    > Unless `≥ n/3` validators are slashable: the observable store view after folding the
    > same available set of blocks through `on_block` in any parent-first order depends
    > only on that set, not on the order. In particular, two nodes with the same available
    > blocks agree on `(F, J, h_j, hmax)`, on the accepted subtree rooted at `F`, and hence
    > on the possible outputs of `getConfirmed`.

    Read aloud: two nodes that received the same blocks, each in some parent-respecting
    order, agree on everything fork choice reads — or a third of the validators exposed
    themselves.

    Noun by noun. "The same available set … in any parent-first order": two lists that are
    permutations of each other (`List.Perm`), each `ParentFirst`, each folded from the
    genesis store. "The observable store view" is spelled out as the paper's own "in
    particular" list: the four fields, membership of the subtree rooted at `F` — the two
    `F`s being equal by the first conjunct — and the outputs of `get_confirmed`. The
    paper's third sentence, that the nodes may disagree outside `F`'s subtree, is a caveat
    rather than a claim, and is not stated; agreement of the recorded states on the shared
    subtree is derivable (replay is deterministic) and is likewise not stated. The
    disjunct's evidence is included on a block accepted by either of the two stores. -/
theorem thmOrderIndependence {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [BlockHash Node Root] [PositiveWeight Node]
    {Bs₁ Bs₂ : List (Blk Node Root)} (hperm : Bs₁.Perm Bs₂)
    (hp₁ : ParentFirst Bs₁) (hp₂ : ParentFirst Bs₂) :
    ((onBlocks Store.gen Bs₁).F = (onBlocks Store.gen Bs₂).F ∧
     (onBlocks Store.gen Bs₁).J = (onBlocks Store.gen Bs₂).J ∧
     (onBlocks Store.gen Bs₁).h_j = (onBlocks Store.gen Bs₂).h_j ∧
     (onBlocks Store.gen Bs₁).hmax = (onBlocks Store.gen Bs₂).hmax ∧
     (∀ C, (onBlocks Store.gen Bs₁).F ⪯ C →
       (C ∈ (onBlocks Store.gen Bs₁).T ↔ C ∈ (onBlocks Store.gen Bs₂).T)) ∧
     (∀ C, GetConfirmed (onBlocks Store.gen Bs₁) C ↔
       GetConfirmed (onBlocks Store.gen Bs₂) C)) ∨
      ∃ A : Finset Node, w(A) ≥ 2 * q Node - W Node ∧
        ∀ i ∈ A, ∃ x y : Attestation Node Root, x.validator = i ∧ y.validator = i ∧
          (∃ Cx, (Cx ∈ (onBlocks Store.gen Bs₁).T ∨ Cx ∈ (onBlocks Store.gen Bs₂).T) ∧
            IncludedOn x Cx) ∧
          (∃ Cy, (Cy ∈ (onBlocks Store.gen Bs₁).T ∨ Cy ∈ (onBlocks Store.gen Bs₂).T) ∧
            IncludedOn y Cy) ∧ E1 x y := sorry

end Decoupled
