import StsMultisetLog.Spec.Execution
import Spec.Protocol
import Analysis.Vocabulary
import Analysis.Proofs.Irreversibility
import Analysis.Proofs.StoreInvariants
import Analysis.Proofs.Acceptance
import Analysis.Proofs.LockIn
import Analysis.Proofs.OrderIndependence

/-!
# The companion paper's numbered theorems — its Section 3.1

*Simplex-Style Finality with Height Filtering and Timeouts*
(`full/height_filter_and_timeouts.tex`, labels cited with the `hft:` prefix). Statements of
record for the six theorem environments of its Section 3.1, "Store invariants and safety",
against the store of `Spec/HftFig2Store.lean`. The section's lemmas and corollary are not
stated; per the selection rule in `CONTEXT.md`, a lemma gets stated when a proof demands it
or on instruction. The rules of `Analysis/Theorems.lean` apply unchanged: each docstring
carries the paper's sentence verbatim, and there is no section-level `variable`.

**Stated on instruction, 2026-08-16; all six are proved as of 2026-08-17.** Each proof is a
one-line call into `Analysis/Proofs/`, and each of the six is kernel-clean —
`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for all of them.

Theorem 10 carries one assumption the other five do not, `[HashInjective Node Root]`, added
to its statement on 2026-08-17 in Roberto's absence; its docstring says what it is and why,
and `CONTEXT.md` records the alternative that was rejected.

## Shared rendering decisions

**Time is the execution.** All six statements quantify over `Exec protocol sched` — the
framework's infinite executions of the node protocol (`Spec/Protocol.lean`) — a validator
and the stores it holds, on instruction (2026-08-16), named through the reachability
vocabulary of `Analysis/Vocabulary.lean` (2026-08-17): "at all times" is `Reaches x p S`,
and "once …, at all future times" is `ReachesFrom x p S S'`. Theorem 10 keeps explicit
steps, through `storeAt`, because its "the same available set of blocks … in any
parent-first order" reads each validator's received-block list out of the execution with
`deliveredBlocks`, a prefix-length notion. Each docstring names the store-level core its proof will
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
absent from an earlier held store, so the processing call lies between the two stores the
statement names.
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

    Noun by noun. "A node" is a validator `p` — `Spec/Protocol.lean` makes the store the
    node state, and `Reaches`/`ReachesFrom` in `Analysis/Vocabulary.lean` name the stores
    it holds as `x` runs. "Sets `Σ.F = F`": `F` is `S.F`, `S` being any store `p` holds.
    "At all future times": every `S'` the same validator holds at the same or a later
    step — `ReachesFrom x p S S'`. "Descends from" is `⪯`, reflexive as Definition 5
    (`def:block-chain`) makes it, so a step that leaves the store alone counts, and so
    does the same-step pair.

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
    {sched : Schedule Node} {x : Exec (protocol (Node := Node) (Root := Root)) sched}
    {p : Node} {S S' : Store Node Root} (h : ReachesFrom x p S S') :
    S.F ⪯ S'.F :=
  Proofs.reachesFrom_F h

/-- **Theorem 4** (`hft:thm:fleqr`, lines 591–593): `F ⪯ J`, stated on an execution — on
    instruction, 2026-08-16, like Theorem 3.

    > The store maintains `Σ.F ⪯ Σ.J` at all times.

    Read aloud: at every step of any execution of the node protocol, under any schedule,
    every validator's store-finalized block is an ancestor of its store root.

    Noun by noun. "The store" is any store `S` that validator `p` holds as `x` runs —
    `Reaches x p S`, the reachability vocabulary of `Analysis/Vocabulary.lean`.
    "Maintains … at all times" is that quantification — and unlike the store-level form,
    no further hypothesis is left: this is an invariant, and what carried it there as
    `S.Reachable` is carried here by the execution itself, whose `init` field starts every
    validator at the genesis store, where `F = J = genesis`. Timeless, and over corrupted
    validators too, for the reason in Theorem 3's docstring. The store-level core is
    `Proofs.reachable_FJ` — the previous statement of record, `S.Reachable → S.F ⪯ S.J`.

    Proved in `Analysis/Proofs/StoreInvariants.lean`: each mutator's own condition is the
    conclusion it must re-establish — `update_justified` moves `J` only past the
    `F`-filter, `update_finalized` moves `F` only under `F' ⪯ Σ.J` — and the execution
    walk is `exec_node_invariant`, the reusable walker that file introduces. -/
theorem thmFPreceqJ {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [BlockHash Node Root]
    {sched : Schedule Node} {x : Exec (protocol (Node := Node) (Root := Root)) sched}
    {p : Node} {S : Store Node Root} (h : Reaches x p S) :
    S.F ⪯ S.J :=
  Proofs.reaches_FJ h

/-- **Theorem 7** (`hft:thm:fcconsistency`, lines 638–640): fork-choice consistency.

    > Once a node sets `Σ.F = F`, `getConfirmed(Σ, Ω)` returns a block descending from `F`
    > at all future times, for every `Ω`.

    Read aloud: once the store finalizes a block, every confirmation it ever offers from
    then on sits below that block.

    Noun by noun. "Once a node sets `Σ.F = F`": `F` is `S.F`, `S` being any store
    validator `p` holds. "At all future times": every `S'` with `ReachesFrom x p S S'`.
    "Returns … for every `Ω`": every `C` with `GetConfirmed S' C` — the relation holds of
    exactly the blocks some `Ω` could pick, so quantifying over its solutions is
    quantifying over `Ω`. The store-level core is `Proofs.getConfirmed_F`, over any store
    with `F ⪯ J`.

    Proved in `Analysis/Proofs/StoreInvariants.lean`, riding Theorems 3 and 4:
    `get_confirmed`'s own second conjunct is `R ⪯ C`, the walk-from block `R` is `J` or
    `F` — either at or above `F` once `F ⪯ J` is in hand — and Theorem 3 carries the
    earlier store's `F` up to the later one's. -/
theorem thmForkChoiceConsistency {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [BlockHash Node Root]
    {sched : Schedule Node} {x : Exec (protocol (Node := Node) (Root := Root)) sched}
    {p : Node} {S S' : Store Node Root} (h : ReachesFrom x p S S')
    {C : Blk Node Root} (hC : GetConfirmed S' C) :
    S.F ⪯ C :=
  Proofs.forkChoiceConsistency h hC

/-- **Theorem 8** (`hft:thm:finlive`, lines 683–685): local acceptance of finality updates.

    > Unless `≥ n/3` validators are slashable: if a block `B` is processed by `on_block`
    > and `σ[B].F = F'`, then after processing `Σ.F ⪰ F'`.

    Read aloud: when the store accepts a block whose replayed state records `F'` as
    finalized, the store's own finalized block ends at or below on `F'`'s chain — or a
    third of the validators exposed themselves.

    Noun by noun. "A block `B` is processed by `on_block`": `B` is absent from a store
    the node holds (`B ∉ S.T`) and recorded in a later one — the `get` hypothesis reads
    `σ[B]` out of `S'` — so the processing call lies between the two, a delivery to `p`
    running `on_block` being the one action that can make the difference. "`σ[B].F = F'`":
    that recorded state's `F`. "After processing `Σ.F ⪰ F'`": `F' ⪯ S'.F` — stated at the
    recording store rather than at the accepting step, the same claim once Theorem 3's
    monotonicity is in hand, and the readable one. "Unless `≥ n/3` validators are
    slashable": the accountable disjunct of the module header, both messages of each
    signer included on blocks `S'` accepted. The store-level core is the previous
    statement of record, over one `onBlock` call on a reachable store. -/
theorem thmFinalityAcceptance {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [BlockHash Node Root] [PositiveWeight Node]
    {sched : Schedule Node} {x : Exec (protocol (Node := Node) (Root := Root)) sched}
    {p : Node} {S S' : Store Node Root} (h : ReachesFrom x p S S')
    {B F' : Blk Node Root} (hnew : B ∉ S.T)
    (hB : get σB from S'.σ B; σB.F = F') :
    F' ⪯ S'.F ∨
      ∃ A : Finset Node, w(A) ≥ 2 * q Node - W Node ∧
        ∀ v ∈ A, ∃ a b : Attestation Node Root, a.validator = v ∧ b.validator = v ∧
          (∃ Ca ∈ S'.T, IncludedOn a Ca) ∧
          (∃ Cb ∈ S'.T, IncludedOn b Cb) ∧ E1 a b :=
  Proofs.finalityAcceptance h hnew hB

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
    and `σ[B].h_j = h_f` has been processed by the node": `B` has a recorded state, with
    those two fields, in a store `S` the node holds — the `get` hypothesis. "At all future
    times" and "always": every `S'` with `ReachesFrom x p S S'`, the three claims conjoined
    under one `S'`. "For every `Ω`": as in Theorem 7. The disjunct's evidence is included
    on `B_F`'s chain or on a block `S'` accepted, each message independently, since which
    quorum sits where depends on the case. -/
theorem thmLockIn {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [BlockHash Node Root] [PositiveWeight Node]
    {sched : Schedule Node} {x : Exec (protocol (Node := Node) (Root := Root)) sched}
    {p : Node} {S S' : Store Node Root} (h : ReachesFrom x p S S')
    {B_F F : Blk Node Root} {h_f : Nat} {B : Blk Node Root}
    (hBF : postState B_F ≠ invalid)
    (hF : (postState' B_F).F = F) (hhf : (postState' B_F).h_F = h_f)
    (hB : get σB from S.σ B; σB.J = F ∧ σB.h_j = h_f) :
    (F ⪯ S'.J ∧ F ∈ viableTree S' ∧
      ∀ C, GetConfirmed S' C → F ⪯ C) ∨
      ∃ A : Finset Node, w(A) ≥ 2 * q Node - W Node ∧
        ∀ v ∈ A, ∃ a b : Attestation Node Root, a.validator = v ∧ b.validator = v ∧
          (IncludedOn a B_F ∨ ∃ Ca ∈ S'.T, IncludedOn a Ca) ∧
          (IncludedOn b B_F ∨ ∃ Cb ∈ S'.T, IncludedOn b Cb) ∧ E1 a b :=
  Proofs.lockIn h hBF hF hhf hB

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
    quorum threshold. Unlike the other five statements, the steps stay explicit — spelled
    `storeAt` — because `deliveredBlocks` is a prefix of the execution and must name how
    far each validator has run.

    **`[HashInjective Node Root]` was added to this statement on 2026-08-17, in Roberto's
    absence, and is the one statement change in this file since it was written.** It is the
    paper's collision-freedom idealization (`Spec/Defs/Store.lean`), carried by this theorem
    alone — the same treatment `PositiveWeight` gets, and for the same reason: only the
    results that need an assumption should pay for it. Without it the `Σ.J` conjunct is
    false and not by a slashable event. `update_justified` breaks its tie on `hash(J)`, so
    two distinct blocks justified at one height with equal hashes leave the store root
    decided by arrival order, and Definition 9 (`hft:def:slashing`) is E1 alone and says
    nothing about two targets at one height, so the disjunct cannot absorb it. The paper
    identifies a block with its hash, so in its own model the assumption is free.
    `CONTEXT.md` records the alternative that was rejected — folding injectivity into
    `BlockHash`, which would have made the other five theorems pay for it too.

    Proved in `Analysis/Proofs/OrderIndependence.lean`, over the fold; a validator's store
    is that fold by `Proofs.storeAt_eq_fold`. -/
theorem thmOrderIndependence {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [BlockHash Node Root] [PositiveWeight Node]
    [HashInjective Node Root]
    {sched : Schedule Node} {x : Exec (protocol (Node := Node) (Root := Root)) sched}
    {p p' : Node} {i j : Nat}
    (hperm : (deliveredBlocks x p i).Perm (deliveredBlocks x p' j))
    (hp : ParentFirst (deliveredBlocks x p i))
    (hp' : ParentFirst (deliveredBlocks x p' j)) :
    ((storeAt x p i).F = (storeAt x p' j).F ∧
     (storeAt x p i).J = (storeAt x p' j).J ∧
     (storeAt x p i).h_j = (storeAt x p' j).h_j ∧
     (storeAt x p i).hmax = (storeAt x p' j).hmax ∧
     (∀ C, (storeAt x p i).F ⪯ C → (C ∈ (storeAt x p i).T ↔ C ∈ (storeAt x p' j).T)) ∧
     (∀ C, GetConfirmed (storeAt x p i) C ↔ GetConfirmed (storeAt x p' j) C)) ∨
      ∃ A : Finset Node, w(A) ≥ 2 * q Node - W Node ∧
        ∀ v ∈ A, ∃ a b : Attestation Node Root, a.validator = v ∧ b.validator = v ∧
          (∃ Ca, (Ca ∈ (storeAt x p i).T ∨ Ca ∈ (storeAt x p' j).T) ∧ IncludedOn a Ca) ∧
          (∃ Cb, (Cb ∈ (storeAt x p i).T ∨ Cb ∈ (storeAt x p' j).T) ∧ IncludedOn b Cb) ∧
          E1 a b :=
  Proofs.orderIndependence hperm hp hp'

end Decoupled
