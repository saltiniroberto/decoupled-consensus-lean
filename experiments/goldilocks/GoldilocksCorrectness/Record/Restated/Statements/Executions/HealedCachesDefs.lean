module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedAttestationDefs
public import GoldilocksCorrectness.Statements.Executions.HealedCachesDefs

@[expose] public section

/-!
# HealedCachesDefs, over a model

The definition of `GoldilocksCorrectness/Statements/Executions/HealedCachesDefs.lean` over a model
`M`: a node state's justification height, justified block and finalized block on the honest chain of
an execution of `protocolOf M S`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (IsEntry)

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

/-- `CachesOnChain M S Sched x s₀ H n`: the justification height `n.justifiedHeight` of the node
state `n` is greater than `H`; its justified block `n.justified` is on the honest chain from slot
`s₀`, is an entry block, and has the chain-state height `n.justifiedHeight`; its finalized block
`n.finalized` is `n.justified` or an ancestor of it.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot of the honest
  chain; `H`: the threshold; `n`: the node state.

Read aloud: the node's justification height is greater than `H`; its justified block is on the
honest chain, is an entry block, and has its height equal to the justification height; its
finalized block is the justified block or an ancestor of it. -/
def CachesOnChain (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (s₀ H : ℕ) (n : M.N) : Prop :=
  H < n.justifiedHeight ∧ OnHonestChain M S A x s₀ n.justified ∧ IsEntry M S.C n.justified ∧
    (M.chainStateOf S.C n.justified).h = n.justifiedHeight ∧ n.finalized.AncestorEq n.justified

end GoldilocksCorrectness.Record.Statements.Executions

