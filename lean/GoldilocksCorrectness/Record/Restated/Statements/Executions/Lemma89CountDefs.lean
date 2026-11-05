module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.Lemma89Defs
public import GoldilocksCorrectness.Statements.Executions.Lemma89CountDefs

@[expose] public section

/-!
# Lemma89CountDefs, over a model

The definition of `GoldilocksCorrectness/Statements/Executions/Lemma89CountDefs.lean` over a model
`M`, for an execution `x` of `protocolOf M S`: the proposals of two consecutive honest round opening
slots rise in chain-state height.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

/-- `RisingAt M S Sched x rs i`: every proposal of the first slot of opening `i + 1` has a greater
chain-state height than every proposal of the first slot of opening `i`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `rs`: the rounds of the honest round opening slots; `i`: the
  opening.

Read aloud: the next opening's proposal is higher. -/
def RisingAt (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (rs : ℕ → ℕ) (i : ℕ) : Prop :=
  ∀ B B' : Block V, ProposalAt M S x (rs i * S.C.R) B →
    ProposalAt M S x (rs (i + 1) * S.C.R) B' →
    (M.chainStateOf S.C B).h < (M.chainStateOf S.C B').h

end GoldilocksCorrectness.Record.Statements.Executions

