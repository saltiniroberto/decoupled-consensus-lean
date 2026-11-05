module
public import GoldilocksCorrectness.Statements.Executions.InvariantDefs
public import GoldilocksCorrectness.Statements.Routines.FGStateDefs

@[expose] public section

/-!
# The vocabulary of the statements about accountable safety over executions

The definition the statements about accountable safety over executions read
(`AccountableStatements.lean`): `FinalizedFromChain C S`, the finalized block of the FG state `S`
is the finalized block of the chain state of a block of its tree.


-/

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

end GoldilocksCorrectness.Statements.Executions
