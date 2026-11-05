module
public import GoldilocksCorrectness.Statements.Executions.HealedAttestationDefs

@[expose] public section

/-!
# The finality caches after the healed round: the definition

`CachesOnChain S Sched x s₀ H n`, the invariant the statements of
`HealedCachesStatements.lean` carry along an execution: the node's justification height is
greater than `H`, its justified block is an entry block of the honest chain at that height, and
its finalized block is the justified block or an ancestor of it.


-/

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `CachesOnChain S Sched x s₀ H n`: the justification height `n.S.h_j` of the node state `n` is
greater than `H`; its justified block `n.S.J` is on the honest chain from slot `s₀`, is an entry
block, and has the chain-state height `n.S.h_j`; its finalized block `n.S.F` is `n.S.J` or an
ancestor of it.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot of the honest
  chain; `H`: the threshold; `n`: the node state.

Read aloud: the node's justification height is greater than `H`; its justified block is on the
honest chain, is an entry block, and has its height equal to the justification height; its
finalized block is the justified block or an ancestor of it. -/
def CachesOnChain (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (s₀ H : ℕ) (n : NodeState V) : Prop :=
  H < n.S.h_j ∧ OnHonestChain S Sched x s₀ n.S.J ∧ IsEntry S.C n.S.J ∧
    (chainStateOf S.C n.S.J).h = n.S.h_j ∧ n.S.F.AncestorEq n.S.J

end GoldilocksCorrectness.Statements.Executions
