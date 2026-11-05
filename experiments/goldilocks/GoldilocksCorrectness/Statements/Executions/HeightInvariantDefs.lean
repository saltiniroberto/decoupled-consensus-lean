module
public import Goldilocks.FG.State

@[expose] public section

/-!
# The justified block entered its height: the definition

`JustifiedIsEntry S`: the justified block of the FG state `S` is the genesis block, or it is the
block that took its own chain into its height. Lemma 57b
(`GoldilocksCorrectness/Statements/Executions/HeightInvariantStatements.lean`) says every
validator's FG state satisfies it at every step.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Statements.Executions

open Goldilocks

variable {V : Type} [DecidableEq V]

/-- `JustifiedIsEntry S`: the justified block `S.J` of the FG state `S` is the genesis block, or
the `T_h` of the chain state `S` holds for it, the block that took its chain into its height, is
`S.J` itself.

The variables:
- `S`: the FG state.

Read aloud: the justified block is the genesis block or entered its height. -/
def JustifiedIsEntry (S : FGState V) : Prop :=
  S.J = Block.genesis ∨ (S.σ S.J).T_h = S.J

end GoldilocksCorrectness.Statements.Executions
