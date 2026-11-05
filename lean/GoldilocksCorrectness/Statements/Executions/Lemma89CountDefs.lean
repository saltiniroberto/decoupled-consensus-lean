module
public import GoldilocksCorrectness.Statements.Executions.Lemma89Defs

@[expose] public section

/-!
# Lemma 89: the definitions of the climb's count

The definitions the climb's count reads on the premise the recount supports, copied from
`scratch/goldilocks_healed/probe_recount_1.lean`:

- `RisingAt S Sched x rs i`, the next opening's proposal higher than this opening's.

The climb's premise is the span premise of record, `OpeningsOutsideWaitsAndWindows`
.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `RisingAt S Sched x rs i`: every proposal of the first slot of opening `i + 1` has a greater
chain-state height than every proposal of the first slot of opening `i`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `rs`: the rounds of the honest round opening slots; `i`: the
  opening.

Read aloud: the next opening's proposal is higher. -/
def RisingAt (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (rs : ℕ → ℕ) (i : ℕ) : Prop :=
  ∀ B B' : Block V, ProposalAt S Sched x (rs i * S.C.R) B →
    ProposalAt S Sched x (rs (i + 1) * S.C.R) B' →
    (chainStateOf S.C B).h < (chainStateOf S.C B').h

end GoldilocksCorrectness.Statements.Executions
