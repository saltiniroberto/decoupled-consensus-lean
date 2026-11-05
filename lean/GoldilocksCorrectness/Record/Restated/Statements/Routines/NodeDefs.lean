module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.ModelGoldilocks

@[expose] public section

/-!
# Conditions on a node state, over a model

The conditions `TreeClosed`, `TreeStamped`, `StampsBounded`, `StampOrder`,
`PoolAttestationsWellFormed` and `LockBelowJustified` of
`GoldilocksCorrectness/Statements/Routines/NodeDefs.lean` over a model `M`, each a condition on a
node state `n : M.N` read through the record's node readers. The page's other definitions have no
twin: the node invariant `NodeInv` is the record's member `M.nodeInv`, and the confirmed tip
`confirmedOf n` is the member `M.ac_confirmed n`. At the spec's model each condition is the landed
definition (the equations `goldilocks_…`, in the simp set `record_goldilocks`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `TreeClosed M P X n`: the genesis block is in the tree `n.tree`, and every other block of the
tree has its parent in the tree, is well formed, has the proposer of its slot, and has a parent of
an earlier slot.

The variables:
- `M`: the model;
- `P`: the values given to the node; `X`: the digest; `n`: the node state.

Read aloud: the tree is closed under parents, and each of its blocks passed the checks that read
the block alone. -/
def TreeClosed (M : GoldilocksModel V) (P : Provisional V) (X : External V) (n : M.N) : Prop :=
  Block.genesis ∈ n.tree ∧
    ∀ B ∈ n.tree, B ≠ Block.genesis →
      B.parent ∈ n.tree ∧ M.block_well_formed P X B = true ∧
        B.proposer? = some (P.proposer B.slot) ∧ B.parent.slot < B.slot

/-- `TreeStamped M n`: every block of the tree `n.tree` has a stamp in `n`.

The variables:
- `M`: the model;
- `n`: the node state.

Read aloud: every block of the tree is stamped. -/
def TreeStamped (M : GoldilocksModel V) (n : M.N) : Prop :=
  ∀ B ∈ n.tree, n.blockStamp B ≠ none

/-- `StampsBounded M n`: the stamp of every block of the tree, and of every Goldfish vote the node
holds, is at most the node's clock `n.t`.

The variables:
- `M`: the model;
- `n`: the node state.

Read aloud: nothing the node holds is stamped later than its clock. -/
def StampsBounded (M : GoldilocksModel V) (n : M.N) : Prop :=
  (∀ B ∈ n.tree, ∀ τ : Stamp, n.blockStamp B = some τ → τ ≤ (n.t : Stamp)) ∧
    ∀ s : Slot, ∀ vote ∈ n.votesHeld s, ∀ τ : Stamp,
      n.voteStamp vote = some τ → τ ≤ (n.t : Stamp)

/-- `StampOrder M n`: every non-genesis block of the tree and its parent are stamped, the parent
no later than the block.

The variables:
- `M`: the model;
- `n`: the node state.

Read aloud: a block of the tree is stamped no earlier than its parent. -/
def StampOrder (M : GoldilocksModel V) (n : M.N) : Prop :=
  ∀ B ∈ n.tree, B ≠ Block.genesis →
    ∃ τ τ' : Stamp, n.blockStamp B.parent = some τ ∧
      n.blockStamp B = some τ' ∧ τ ≤ τ'

/-- `PoolAttestationsWellFormed M n`: every attestation the node state `n` has received,
`n.attestationsHeld`, is well formed (`M.attestation_well_formed`).

The variables:
- `M`: the model;
- `n`: the node state.

Read aloud: every attestation the node holds is well formed. -/
def PoolAttestationsWellFormed (M : GoldilocksModel V) (n : M.N) : Prop :=
  ∀ a ∈ n.attestationsHeld, M.attestation_well_formed a = true

/-- `LockBelowJustified M n`: whenever the anti-slashing record of the node state `n` holds a lock
at a height `h`, `h` is at most the node's justification height `n.justifiedHeight`.

The variables:
- `M`: the model;
- `n`: the node state.

Read aloud: a lock of the record at a height means the node's justification height is at least
that height. -/
def LockBelowJustified (M : GoldilocksModel V) (n : M.N) : Prop :=
  ∀ (h : Height) (T : BlockId), n.sentLock h = some T → h ≤ n.justifiedHeight

/-! ## At the spec's model -/

/-- At the spec's model, `TreeClosed` is the landed definition.

The variables:
- `P`, `X`, `n`: as in `TreeClosed`, at the spec's model.

Read aloud: the spec's model has the landed `TreeClosed`. -/
@[record_goldilocks]
theorem goldilocks_TreeClosed (P : Provisional V) (X : External V) (n : NodeState V) :
    GoldilocksCorrectness.Statements.Routines.TreeClosed P X n.S =
      TreeClosed (Model.goldilocks (V := V)) P X n := rfl

/-- At the spec's model, `TreeStamped` is the landed definition.

The variables:
- `n`: as in `TreeStamped`, at the spec's model.

Read aloud: the spec's model has the landed `TreeStamped`. -/
@[record_goldilocks]
theorem goldilocks_TreeStamped (n : NodeState V) :
    GoldilocksCorrectness.Statements.Routines.TreeStamped n =
      TreeStamped (Model.goldilocks (V := V)) n := rfl

/-- At the spec's model, `StampsBounded` is the landed definition.

The variables:
- `n`: as in `StampsBounded`, at the spec's model.

Read aloud: the spec's model has the landed `StampsBounded`. -/
@[record_goldilocks]
theorem goldilocks_StampsBounded (n : NodeState V) :
    GoldilocksCorrectness.Statements.Routines.StampsBounded n =
      StampsBounded (Model.goldilocks (V := V)) n := rfl

/-- At the spec's model, `StampOrder` is the landed definition.

The variables:
- `n`: as in `StampOrder`, at the spec's model.

Read aloud: the spec's model has the landed `StampOrder`. -/
@[record_goldilocks]
theorem goldilocks_StampOrder (n : NodeState V) :
    GoldilocksCorrectness.Statements.Routines.StampOrder n =
      StampOrder (Model.goldilocks (V := V)) n := rfl

/-- At the spec's model, `PoolAttestationsWellFormed` is the landed definition.

The variables:
- `n`: as in `PoolAttestationsWellFormed`, at the spec's model.

Read aloud: the spec's model has the landed `PoolAttestationsWellFormed`. -/
@[record_goldilocks]
theorem goldilocks_PoolAttestationsWellFormed (n : NodeState V) :
    GoldilocksCorrectness.Statements.Routines.PoolAttestationsWellFormed n.S =
      PoolAttestationsWellFormed (Model.goldilocks (V := V)) n := rfl

/-- At the spec's model, `LockBelowJustified` is the landed definition.

The variables:
- `n`: as in `LockBelowJustified`, at the spec's model.

Read aloud: the spec's model has the landed `LockBelowJustified`. -/
@[record_goldilocks]
theorem goldilocks_LockBelowJustified (n : NodeState V) :
    GoldilocksCorrectness.Statements.Routines.LockBelowJustified n =
      LockBelowJustified (Model.goldilocks (V := V)) n := rfl

end GoldilocksCorrectness.Record.Statements.Routines
