import Analysis.Proofs.SlotClosure
import Spec.HftFig2Store
import Spec.Protocol
import StsMultisetLog.Spec.Execution

/-!
# The vocabulary the statements need, which no figure reads

`Spec/` holds the figure translations and the numbered definitions those figures read.
Definition 11 (`def:slashing`) and Definition 21 (`def:certificates`) are not among them —
`MAPPING.md` lists the first under "stated but not read by a figure", and the second is read by
the store and the results rather than by Figures 1 or 2. They are still the paper's numbered
definitions, and a statement that mentions them has to mean the paper's own notion, so they are
written here rather than inside a proof file.

**Definitions only, no lemmas.** This file plus `Spec/` is the whole surface a reader has to audit
to know what the statements in `Analysis/Lemmas.lean` *mean*. Anything proved about these notions
belongs under `Analysis/Proofs/`.

**Only the parts a landed statement uses.** Definition 11's E2 landed with Lemma 5, the
justification and progress certificates with Lemmas 5 and 6, and E1 with Lemma 10. A declaration
no statement mentions is an unaudited claim about what the paper means, which is why each waited.
Definition 21's **finality certificate is absent again**: it was rendered when Lemmas 10 and 11
were first stated (commit `f284635`), and removed the next day when their finalization hypothesis
became the recorded pair `(F, h_F)` on a post-state, which no longer mentions it. Restore it from
that commit when a statement needs the certificate as an object.

## `σ[·]` is replaced by `BlockPostState`, which makes the certificates weaker

Definition 21 asks for "the direct height-event invocation that set `(J, h_j) = (T, h)`" — a state
on the chain, which the paper reaches through `σ[·]`. This project has no `σ[·]`: Figure 3
(`alg:store`), which builds it, is not rendered. `BlockPostState` stands in, as it does in
`Analysis/Lemmas.lean`, and it admits more states than `σ[·]` does — it omits Figure 3's structural
precheck and claimed-root check.

So a certificate here is **easier** to have than the paper's. In a *hypothesis*, which is where
Lemma 5 puts it, that makes the result stronger. Note the direction before moving one of these
definitions into a conclusion, where it would make the result weaker instead.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

section
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root]

/-! ## Definition 11 (`def:slashing`) — the second slashing condition -/

/-- Definition 11 (`def:slashing`), **E2**: both height pairs have height `h`, both targets are
    nonempty, and the targets differ.

    "Both targets are nonempty" is carried by the constructor: `HeightPair.target` is the pair
    `(h, T)` with `T ≠ ⊥`, and a `timeout` or `empty` pair cannot match it.

    E2 is a condition on a pair of attestations, not on one validator. Definition 11's "two signed
    attestations **by one validator** are slashable" is the caller's to state, which is what
    `lemTargetUniqueness` does by pinning both validators to the same `i`. -/
def E2 (x y : Attestation Node Root) : Prop :=
  ∃ h T T', x.heightPair = .target h T ∧ y.heightPair = .target h T' ∧ T ≠ T'

/-- Definition 11 (`def:slashing`), **E1**: one finality pair is `(h, T)` with `T ≠ ⊥`, while the
    other height pair is `(h, T')` with `T' ≠ T`, including `T' = ⊥`.

    `x` carries the finality pair and `y` the height pair, so the definition is asymmetric where
    E2 is not; a caller wanting either order says so. "`T ≠ ⊥`" is carried by the constructor:
    `FinalityPair.commit` is the pair with a block. "`(h, T')` … including `T' = ⊥`" is two
    constructors: `.target h T'` with `T' ≠ T`, or `.timeout h` — the explicit-timeout case the
    paper's Lemma 10 proof singles out. "An empty height pair has height `⊥`, so it conflicts
    with neither pair" is `.empty` matching neither arm.

    "The two conflicting fields may occur in the same signed attestation": nothing here stops
    `x = y`. As with E2, Definition 11's "by one validator" is the caller's to state. -/
def E1 (x y : Attestation Node Root) : Prop :=
  ∃ h T, x.finalityPair = .commit h T ∧
    ((∃ T', y.heightPair = .target h T' ∧ T' ≠ T) ∨ y.heightPair = .timeout h)

end

section
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]

/-! ## Definition 21 (`def:certificates`) — the justification and progress certificates -/

/-- An attestation carried by some block on the chain ending at `B`. This is the "inclusion" of
    Definition 21's "their valid inclusions on one chain".

    The *valid* half of "valid inclusion" is Definition 9 (`def:valid-attestation-inclusion`),
    which is membership of the named validator in `V` once signatures are the `validator` field —
    and the certificate below carries that as `Q ⊆ V` on the signer set instead. -/
def IncludedOn (a : Attestation Node Root) (B : Blk Node Root) : Prop :=
  ∃ Y, Y ⪯ B ∧ a ∈ Y.attestations

/-- Definition 21 (`def:certificates`)'s **justification certificate** `JC(h, T)`, on the chain
    ending at `B`. Two clauses, as the paper lists them:

    * distinct signed exact-target attestations of weight at least `q`, included on that chain —
      "distinct" is `Q` being a `Finset` of validators, one attestation each;
    * the direct height-event invocation that set `(J, h_j) = (T, h)`, as a block post-state on
      that chain recording those two values.

    The second clause is what makes "a target quorum at a nonjustifiable height is not a JC" hold:
    at a nonjustifiable height the target branch does not fire, so no state records the pair.

    `BlockPostState` stands in for the paper's `σ[·]` here — see the module docstring for what that
    changes and in which direction. -/
def JustificationCertificate (B : Blk Node Root) (h : Nat) (T : Blk Node Root) : Prop :=
  (∃ Q : Finset Node, Q ⊆ Electorate.V ∧ w(Q)≥q ∧
    ∀ i ∈ Q, ∃ a : Attestation Node Root,
      a.validator = i ∧ a.heightPair = .target h T ∧ IncludedOn a B) ∧
  (∃ σ : ChainState Node Root, BlockPostState σ ∧ σ.L ⪯ B ∧ σ.J = T ∧ σ.h_j = h)

/-- Definition 21 (`def:certificates`)'s **progress certificate** `PC(h)`, on the chain ending at
    `B`. Two clauses, as the paper lists them:

    * distinct signed height-`h` attestations of weight at least `q`, included on that chain. Any
      height pair at `h` counts, exact target or timeout — `Attestation.height` reads the height out
      of either, and the empty pair has height `⊥` and so counts for no `h`;
    * the direct height-event invocation that advanced height without a new justification, as a
      transition out of height `h` on that chain that leaves `J` alone.

    `σ.J = σp.J` is what identifies the progress branch: the justification branch always writes `J`.

    `X ⪯ B` says the transition's own block is on the chain, which is what `JustificationCertificate`
    says as `σ.L ⪯ B` — the two are the same requirement, a successful transition leaving `σ.L = X`.

    The paper's "setting the progress bits" is not a third clause here. Which bits a state holds is
    a fact about the transition rather than a further requirement on the certificate, and it is
    `process_attestation` that sets them; a statement that asked for the bits as well would be
    asking for the same thing twice. -/
def ProgressCertificate (B : Blk Node Root) (h : Nat) : Prop :=
  (∃ Q : Finset Node, Q ⊆ Electorate.V ∧ w(Q)≥q ∧
    ∀ i ∈ Q, ∃ a : Attestation Node Root,
      a.validator = i ∧ a.height = some h ∧ IncludedOn a B) ∧
  (∃ (σp σ : ChainState Node Root) (X : Blk Node Root),
    BlockPostState σp ∧ X ⪯ B ∧ stateTransition σp X = .state σ ∧
      σp.h = h ∧ σ.h = h + 1 ∧ σ.J = σp.J)

end

section
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-! ## The store theorems' temporal vocabulary

The companion paper's store theorems (`Analysis/HftTheorems.lean`) are claims about one
node's store over time, and are stated over the framework's executions of the node
protocol (`Spec/Protocol.lean`). `deliveredBlocks` reads a validator's received-block
list out of an execution; the fold vocabulary — `onBlocks`, `Store.Reachable`,
`ParentFirst` — is what the statements' *store-level cores* are phrased with, since
`on_block` is the store's only mutator and a validator's store is the fold of what was
delivered to it. `storeAt`, `Reaches` and `ReachesFrom` (Roberto, 2026-08-17) name a
validator's store at a step and its reachability over an execution, so an execution
statement reads as the paper's sentence — "the store maintains … at all times",
"once … , at all future times" — rather than as index arithmetic. -/

/-- The store after receiving `Bs`, oldest first: `on_block` folded over the list — the
    "folding … through `on_block`" of Theorem 10 (`hft:thm:orderindep`). At the store
    level, "at all future times" is "after any further `onBlocks`". -/
def onBlocks (S : Store Node Root) (Bs : List (Blk Node Root)) : Store Node Root :=
  Bs.foldl onBlock S

/-- A store the node can hold: reached from the genesis store by some sequence of receipts.
    The execution statements need no such hypothesis — an execution starts every validator
    at `Store.gen` — so this is the store-level cores' spelling of what the execution
    carries by construction. -/
def Store.Reachable (S : Store Node Root) : Prop :=
  ∃ Bs : List (Blk Node Root), S = onBlocks Store.gen Bs

/-- Theorem 10 (`hft:thm:orderindep`)'s "parent-first order": every block's parent is
    genesis — accepted already in the genesis store — or appears earlier in the list. -/
def ParentFirst (Bs : List (Blk Node Root)) : Prop :=
  ∀ (i : Nat) (hi : i < Bs.length) (P : Blk Node Root),
    Bs[i].parent = some P → P = .genesis ∨ P ∈ Bs.take i

/-- The blocks delivered to `p` in the first `i` steps of `x`, oldest first — the list
    `on_block` was fed, a `deliver` to `p` being the one action that runs the store's
    `receive`. Theorem 10 (`hft:thm:orderindep`)'s "the same available set of blocks …
    in any parent-first order" quantifies over these lists. -/
def deliveredBlocks {sched : Schedule Node}
    (x : Exec (protocol (Node := Node) (Root := Root)) sched) (p : Node) :
    Nat → List (Blk Node Root)
  | 0 => []
  | i + 1 =>
      deliveredBlocks x p i ++
        match x.lbl i with
        | .deliver q m => if q = p then (match m.msg with | .block B => [B]) else []
        | _ => []

/-- Validator `p`'s store after `i` steps of `x`. -/
def storeAt {sched : Schedule Node}
    (x : Exec (protocol (Node := Node) (Root := Root)) sched) (p : Node)
    (i : Nat) : Store Node Root :=
  x[i][p].st

/-- `p` holds the store `S` at some step of `x`: reachability of a store, for one node,
    over one execution. The execution statements' "the node['s store]" and "at all
    times". The fold-level counterpart is `Store.Reachable`; that every store a node
    reaches over an execution is `Store.Reachable` is a fact to prove, not part of this
    definition. -/
def Reaches {sched : Schedule Node}
    (x : Exec (protocol (Node := Node) (Root := Root)) sched) (p : Node)
    (S : Store Node Root) : Prop :=
  ∃ i, storeAt x p i = S

/-- `p` holds `S`, and at the same or a later step holds `S'`. The execution statements'
    "once … , at all future times": what holds of every such pair holds from the moment
    of `S` onward. Same-step pairs are included, so a reflexive conclusion loses
    nothing. -/
def ReachesFrom {sched : Schedule Node}
    (x : Exec (protocol (Node := Node) (Root := Root)) sched) (p : Node)
    (S S' : Store Node Root) : Prop :=
  ∃ i j, i ≤ j ∧ storeAt x p i = S ∧ storeAt x p j = S'

end

end Decoupled
