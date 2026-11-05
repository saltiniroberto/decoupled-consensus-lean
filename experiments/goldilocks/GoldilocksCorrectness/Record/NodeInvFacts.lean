module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ACStoreDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.NodeDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.FGStateDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.RecordDefs
public import GoldilocksCorrectness.Statements.Routines.WalkDefs

@[expose] public section

/-!
# The facts of the model's node invariant

`NodeInvFacts M` holds, for a model `M`, what its node invariant `M.nodeInv C P X n` owes. Five
fields are structural: a node's initial state satisfies the invariant; a tick at a time no earlier
than the clock, a wake and a delivery keep it, with the validator, and with the clock as each one
sets it; and from a state satisfying it, a tick at a time no earlier than the clock has an outcome
and no failing one. Fifteen fields are its consequences: each says that a node state satisfying the
invariant satisfies one condition on node states, written over the record's node readers. This
file holds the structure only.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Record

open DC (DRE)
open Goldilocks (Config Provisional External RootOrder NamedObject Time)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)
open GoldilocksCorrectness.Record.Statements.Routines (PoolKeyed PoolStamped TreeClosed TreeStamped
  AttestationsValid StampOrder FinalizedAncestorJustified JustificationCacheBounds JustifiedHeight
  JustifiedInTree LockBelowJustified RecordConsistent PoolAttestationsWellFormed)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The facts of the node invariant of `M`.

Read aloud: the model `M`'s node invariant holds of every initial state, is kept by the node's
routines, makes the tick answer, and gives the conditions the proofs read. -/
structure NodeInvFacts (M : GoldilocksModel V) : Prop where
  /-- A node's initial state satisfies the node invariant.

      Read aloud: a node of any validator starts from a state satisfying the invariant. -/
  initial_nodeInv : ∀ (C : Config) (P : Provisional V) (X : External V) (v : V),
    M.nodeInv C P X (M.initial C v)

  /-- Every answer `(n', sent)` of the tick of a node state `n` satisfying the invariant, at a time
      `t` no earlier than `n`'s clock, satisfies the invariant, has `n`'s validator, and has the
      clock `t`.

      Read aloud: a tick at a time no earlier than the clock, from a state satisfying the
      invariant, answers a state satisfying it, with the same validator and the clock set to the
      tick's time. -/
  tick_nodeInv : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (t : Time), M.nodeInv C P X n → n.t ≤ t →
      ∀ (n' : M.N) (sent : List (NamedObject V)), .ok (n', sent) ∈ M.tick C P X n t →
        M.nodeInv C P X n' ∧ n'.v = n.v ∧ n'.t = t

  /-- Waking a node state `n` satisfying the invariant at a time `t` no earlier than its clock
      gives a state satisfying it, with `n`'s validator and the clock `t`.

      Read aloud: waking at a time not earlier than the clock keeps the invariant and the
      validator and sets the clock to that time. -/
  wake_nodeInv : ∀ (C : Config) (P : Provisional V) (X : External V) (n : M.N) (t : Time),
    M.nodeInv C P X n → n.t ≤ t →
      M.nodeInv C P X (M.wake n t) ∧ (M.wake n t).v = n.v ∧ (M.wake n t).t = t

  /-- Delivering an object `o` to a node state `n` satisfying the invariant gives a state
      satisfying it, with `n`'s validator and `n`'s clock.

      Read aloud: a delivery keeps the invariant, the validator and the clock. -/
  receive_nodeInv : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (o : NamedObject V), M.nodeInv C P X n →
      M.nodeInv C P X (M.receive C P X n o) ∧ (M.receive C P X n o).v = n.v ∧
        (M.receive C P X n o).t = n.t

  /-- The tick of a node state `n` satisfying the invariant, at a time `t` no earlier than `n`'s
      clock, has an outcome, and no outcome of it is a failure.

      Read aloud: from a state satisfying the invariant, a tick at a time no earlier than the clock
      has an outcome and no failing one. -/
  tick_ok : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (t : Time), M.nodeInv C P X n → n.t ≤ t →
      (∃ r : DRE (M.N × List (NamedObject V)), r ∈ M.tick C P X n t) ∧
        ∀ e : DC.Error, .error e ∉ M.tick C P X n t

  /-- The node invariant gives its clock-free part.

      Read aloud: a state satisfying the invariant satisfies its clock-free part. -/
  nodeInv_core : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInv C P X n → M.nodeInvCore C P X n

  /-- Every answer `(n', sent)` of the tick of a node state `n` satisfying the clock-free part, at
      ANY time `t`, satisfies the clock-free part, has `n`'s validator, and has the clock `t`.

      Read aloud: a tick at any time, from a state satisfying the clock-free part, answers a state
      satisfying it, with the same validator and the clock set to the tick's time. -/
  tick_nodeInvCore : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (t : Time), M.nodeInvCore C P X n →
      ∀ (n' : M.N) (sent : List (NamedObject V)), .ok (n', sent) ∈ M.tick C P X n t →
        M.nodeInvCore C P X n' ∧ n'.v = n.v ∧ n'.t = t

  /-- Waking a node state `n` satisfying the clock-free part at ANY time `t` gives a state
      satisfying it, with `n`'s validator and the clock `t`.

      Read aloud: a wake at any time keeps the clock-free part and the validator and sets the clock
      to that time. -/
  wake_nodeInvCore : ∀ (C : Config) (P : Provisional V) (X : External V) (n : M.N) (t : Time),
    M.nodeInvCore C P X n →
      M.nodeInvCore C P X (M.wake n t) ∧ (M.wake n t).v = n.v ∧ (M.wake n t).t = t

  /-- Delivering an object `o` to a node state `n` satisfying the clock-free part gives a state
      satisfying it, with `n`'s validator and `n`'s clock.

      Read aloud: a delivery keeps the clock-free part, the validator and the clock. -/
  receive_nodeInvCore : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (o : NamedObject V), M.nodeInvCore C P X n →
      M.nodeInvCore C P X (M.receive C P X n o) ∧ (M.receive C P X n o).v = n.v ∧
        (M.receive C P X n o).t = n.t

  /-- A node state `n` satisfying the clock-free part `M.nodeInvCore C P X n` satisfies
      `TreeClosed M P X n`.

      Read aloud: under the clock-free part, the tree is closed under parents, and each of its
      blocks passed the checks that read the block alone. -/
  nodeInvCore_treeClosed : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInvCore C P X n → TreeClosed M P X n

  /-- A node state `n` satisfying the clock-free part `M.nodeInvCore C P X n` satisfies
      `PoolKeyed M P n`. Added for a validator in the adversary set, whose clock the environment does not keep
      from going back, so that only the clock-free part of Lemma 11 holds for it.

      Read aloud: under the clock-free part, every vote of the pool filed under a slot has that slot and a validator of that slot's committee. -/
  nodeInvCore_poolKeyed : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInvCore C P X n → PoolKeyed M P n

  /-- A node state `n` satisfying the clock-free part `M.nodeInvCore C P X n` satisfies
      `TreeStamped M n`. Added for a validator in the adversary set, whose clock the environment does not keep
      from going back, so that only the clock-free part of Lemma 11 holds for it.

      Read aloud: under the clock-free part, every block of the tree is stamped. -/
  nodeInvCore_treeStamped : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInvCore C P X n → TreeStamped M n

  /-- A node state `n` satisfying the clock-free part `M.nodeInvCore C P X n` satisfies
      `RootsNameBlocksIn n.tree`. Added for a validator in the adversary set, whose clock the environment does not keep
      from going back, so that only the clock-free part of Lemma 11 holds for it.

      Read aloud: under the clock-free part, no two blocks of the tree share a root. -/
  nodeInvCore_rootsNameBlocksIn : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInvCore C P X n → RootsNameBlocksIn n.tree

  /-- A node state `n` satisfying the clock-free part `M.nodeInvCore C P X n` satisfies
      `FinalizedAncestorJustified M n`. Added for a validator in the adversary set, whose clock the environment does not keep
      from going back, so that only the clock-free part of Lemma 11 holds for it.

      Read aloud: under the clock-free part, the finalized block is the justified block or an ancestor of it. -/
  nodeInvCore_finalizedAncestorJustified : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInvCore C P X n → FinalizedAncestorJustified M n

  /-- A node state `n` satisfying the clock-free part `M.nodeInvCore C P X n` satisfies
      `JustificationCacheBounds M C n`. Added for a validator in the adversary set, whose clock the environment does not keep
      from going back, so that only the clock-free part of Lemma 11 holds for it.

      Read aloud: under the clock-free part, no accepted block that is the finalized block or a descendant of it has a justification height greater than the node's. -/
  nodeInvCore_justificationCacheBounds : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInvCore C P X n → JustificationCacheBounds M C n

  /-- A node state `n` satisfying the clock-free part `M.nodeInvCore C P X n` satisfies
      `JustifiedHeight M C n`. Added for a validator in the adversary set, whose clock the environment does not keep
      from going back, so that only the clock-free part of Lemma 11 holds for it.

      Read aloud: under the clock-free part, the justified block is the genesis block or has the chain-state height `n.justifiedHeight`. -/
  nodeInvCore_justifiedHeight : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInvCore C P X n → JustifiedHeight M C n

  /-- A node state `n` satisfying the clock-free part `M.nodeInvCore C P X n` satisfies
      `JustifiedInTree M n`. Added for a validator in the adversary set, whose clock the environment does not keep
      from going back, so that only the clock-free part of Lemma 11 holds for it.

      Read aloud: under the clock-free part, the justified block is accepted. -/
  nodeInvCore_justifiedInTree : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInvCore C P X n → JustifiedInTree M n

  /-- A node state `n` satisfying the clock-free part `M.nodeInvCore C P X n` satisfies
      `LockBelowJustified M n`. Added for a validator in the adversary set, whose clock the environment does not keep
      from going back, so that only the clock-free part of Lemma 11 holds for it.

      Read aloud: under the clock-free part, every lock of the anti-slashing record is at a height at most `n.justifiedHeight`. -/
  nodeInvCore_lockBelowJustified : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInvCore C P X n → LockBelowJustified M n

  /-- A node state `n` satisfying the clock-free part `M.nodeInvCore C P X n` satisfies
      `RecordConsistent M n`. Added for a validator in the adversary set, whose clock the environment does not keep
      from going back, so that only the clock-free part of Lemma 11 holds for it.

      Read aloud: under the clock-free part, the anti-slashing record is consistent. -/
  nodeInvCore_recordConsistent : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInvCore C P X n → RecordConsistent M n

  /-- A node state `n` satisfying the model's node invariant `M.nodeInv C P X n` satisfies this:
      every Goldfish vote `n` holds under a slot `s` has the slot `s` and a validator of slot `s`'s
      committee (`PoolKeyed M P n`).

      Read aloud: under the invariant, every vote the node holds under a slot has that slot and a
      committee member of it as its validator. -/
  nodeInv_poolKeyed : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInv C P X n → PoolKeyed M P n

  /-- A node state `n` satisfying the model's node invariant `M.nodeInv C P X n` satisfies this:
      every Goldfish vote `n` holds has a stamp in `n` (`PoolStamped M n`).

      Read aloud: under the invariant, every vote the node holds is stamped. -/
  nodeInv_poolStamped : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInv C P X n → PoolStamped M n

  /-- A node state `n` satisfying the model's node invariant `M.nodeInv C P X n` satisfies this: the
      genesis block is in the tree `n.tree`, and every other block of the tree has its parent in the
      tree, is well formed, has the proposer of its slot, and has a parent of an earlier slot
      (`TreeClosed M P X n`).

      Read aloud: under the invariant, the tree is closed under parents, and each of its blocks
      passed the checks that read the block alone. -/
  nodeInv_treeClosed : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInv C P X n → TreeClosed M P X n

  /-- A node state `n` satisfying the model's node invariant `M.nodeInv C P X n` satisfies this: the
      finalized block `n.finalized` is in the tree `n.tree`.

      Read aloud: under the invariant, the finalized block is accepted. -/
  nodeInv_finalized_mem_tree : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInv C P X n → n.finalized ∈ n.tree

  /-- A node state `n` satisfying the model's node invariant `M.nodeInv C P X n` satisfies this:
      every block of the tree `n.tree` has a stamp in `n` (`TreeStamped M n`).

      Read aloud: under the invariant, every block of the tree is stamped. -/
  nodeInv_treeStamped : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInv C P X n → TreeStamped M n

  /-- A node state `n` satisfying the model's node invariant `M.nodeInv C P X n` satisfies this:
      every attestation a non-genesis block `B` of the tree `n.tree` includes is valid against the
      chain state `M.chainStateOf C B.parent` of the block's parent (`AttestationsValid M C n`).

      Read aloud: under the invariant, every attestation a block of the tree includes is valid
      against the chain state of the block's parent. -/
  nodeInv_attestationsValid : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInv C P X n → AttestationsValid M C n

  /-- A node state `n` satisfying the model's node invariant `M.nodeInv C P X n` satisfies this:
      every non-genesis block of the tree `n.tree` and its parent are stamped, the parent no later
      than the block (`StampOrder M n`).

      Read aloud: under the invariant, a block of the tree is stamped no earlier than its parent. -/
  nodeInv_stampOrder : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInv C P X n → StampOrder M n

  /-- A node state `n` satisfying the model's node invariant `M.nodeInv C P X n` satisfies this: no
      two blocks of the tree `n.tree` share a root (`RootsNameBlocksIn n.tree`).

      Read aloud: under the invariant, no two blocks of the tree have the same root. -/
  nodeInv_rootsNameBlocksIn : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInv C P X n → RootsNameBlocksIn n.tree

  /-- A node state `n` satisfying the model's node invariant `M.nodeInv C P X n` satisfies this: the
      finalized block `n.finalized` is the justified block `n.justified` or an ancestor of it
      (`FinalizedAncestorJustified M n`).

      Read aloud: under the invariant, the finalized block is the justified block or an ancestor of
      it. -/
  nodeInv_finalizedAncestorJustified :
    ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
      M.nodeInv C P X n → FinalizedAncestorJustified M n

  /-- A node state `n` satisfying the model's node invariant `M.nodeInv C P X n` satisfies this: no
      block `B` of the tree `n.tree` that is the finalized block `n.finalized` or a descendant of it
      has a justification height `(M.chainStateOf C B).h_j` greater than the node's justification
      height `n.justifiedHeight` (`JustificationCacheBounds M C n`).

      Read aloud: under the invariant, no accepted block that is the finalized block or a descendant
      of it has a justification height greater than the node's. -/
  nodeInv_justificationCacheBounds : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInv C P X n → JustificationCacheBounds M C n

  /-- A node state `n` satisfying the model's node invariant `M.nodeInv C P X n` satisfies this: the
      justified block `n.justified` is the genesis block, or its chain-state height `(M.chainStateOf
      C n.justified).h` is the node's justification height `n.justifiedHeight` (`JustifiedHeight M C
      n`).

      Read aloud: under the invariant, the justified block is the genesis block or has the
      chain-state height `n.justifiedHeight`. -/
  nodeInv_justifiedHeight : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInv C P X n → JustifiedHeight M C n

  /-- A node state `n` satisfying the model's node invariant `M.nodeInv C P X n` satisfies this: the
      justified block `n.justified` is in the tree `n.tree` (`JustifiedInTree M n`).

      Read aloud: under the invariant, the justified block is accepted. -/
  nodeInv_justifiedInTree : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInv C P X n → JustifiedInTree M n

  /-- A node state `n` satisfying the model's node invariant `M.nodeInv C P X n` satisfies this:
      whenever the anti-slashing record of `n` holds a lock at a height `h`, `h` is at most the
      node's justification height `n.justifiedHeight` (`LockBelowJustified M n`).

      Read aloud: under the invariant, every lock of the anti-slashing record is at a height at most
      `n.justifiedHeight`. -/
  nodeInv_lockBelowJustified : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInv C P X n → LockBelowJustified M n

  /-- A node state `n` satisfying the model's node invariant `M.nodeInv C P X n` satisfies this: the
      anti-slashing record of `n` is consistent (`RecordConsistent M n`).

      Read aloud: under the invariant, the anti-slashing record is consistent. -/
  nodeInv_recordConsistent : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInv C P X n → RecordConsistent M n

  /-- A node state `n` satisfying the model's node invariant `M.nodeInv C P X n` satisfies this:
      every attestation the node has received, `n.attestationsHeld`, is well formed
      (`PoolAttestationsWellFormed M n`).

      Read aloud: under the invariant, every attestation the node holds is well formed. -/
  nodeInv_poolAttestationsWellFormed :
    ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
      M.nodeInv C P X n → PoolAttestationsWellFormed M n

end GoldilocksCorrectness.Record
