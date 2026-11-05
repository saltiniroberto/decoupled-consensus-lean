module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Statements.Routines.FGStateDefs
public import GoldilocksCorrectness.Statements.Executions.HeightInvariantDefs
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.RunFactsDefs
public import GoldilocksCorrectness.Statements.AbstractTrace.DeliveryDefs
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs

@[expose] public section

/-!
# HeightInvariantDefs, over a model

The definition of `GoldilocksCorrectness/Statements/Executions/HeightInvariantDefs.lean` over a
model `M`: the justified block of a node state entered its height. The record has no reader for the
chain states a node holds; the chain state of the justified block is its own, `M.chainStateOf C
n.justified`, so the condition takes the parameters `C`. At the spec's model it is the landed
definition when the node's chain states of its tree are the blocks' own and its justified block is
in its tree (`goldilocks_JustifiedIsEntry`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GoldilocksCorrectness.Record.Statements.Executions

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V)

/-- `JustifiedIsEntry M C n`: the justified block `n.justified` of the node state `n` is the
genesis block, or the block `T_h` of its chain state `M.chainStateOf C n.justified`, the
block that took its chain into its height, is `n.justified` itself.

The variables:
- `M`: the model;
- `C`: the parameters; `n`: the node state.

Read aloud: the justified block is the genesis block or entered its height. -/
def JustifiedIsEntry (C : Config) (n : M.N) : Prop :=
  n.justified = Block.genesis ∨ (M.chainStateOf C n.justified).T_h = n.justified

end GoldilocksCorrectness.Record.Statements.Executions

