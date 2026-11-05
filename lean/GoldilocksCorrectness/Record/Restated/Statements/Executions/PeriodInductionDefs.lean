module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncResilienceChainBlockDefs
public import GoldilocksCorrectness.Statements.Executions.PeriodInductionDefs

@[expose] public section

/-!
# PeriodInductionDefs, over a model

The definition of `GoldilocksCorrectness/Statements/Executions/PeriodInductionDefs.lean` over a
model `M`: the votes of a slot are due by the support cutoff, read at the model's times.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

section Kit

variable (S : Setup V)

/-- `VotesDueByCutoff M S Δs b₀ b₁ s'`: the slot-`s'` honest votes, put on the wire at
`M.voteTime S.C s'`, are due by the support cutoff of `s'` around the period: their ordinary
deadline `M.supportCutoff S.C s'` is at or before `b₀`, or the period plus its recovery
`max (Δ S) Δs` ends by that support cutoff.

The variables:
- `M`: the model;
- `S`: the setup; `Δs`: the sync delay; `b₀`, `b₁`: the start and the end of the period; `s'`: the
  slot of the votes.

The recovery after the period is `max (Δ S) Δs`;

Read aloud: the update of slot `s'` sees every honest vote of `s'` as an early vote. -/
def VotesDueByCutoff (Δs b₀ b₁ s' : ℕ) : Prop :=
  M.supportCutoff S.C s' ≤ b₀ ∨ b₁ + max (Δ S) Δs ≤ M.supportCutoff S.C s'

end Kit

section After

variable (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)

end After

end GoldilocksCorrectness.Record.Statements.Executions

