module
public import GoldilocksCorrectness.Statements.Executions.AsyncResilienceChainBlockDefs

@[expose] public section

/-! The originals
stay byte-identical;

- `VotesDueByCutoff`, a new condition: the slot-`s'` honest votes are due by the support cutoff of
  `s'` around the period.

 `PeriodInvOfChainBlockDueByCutoff`, the
copy of `PeriodInvOfChainBlock` whose seventh clause read `VotesDueByCutoff S b₀ b₁ s'`, was itself
the original of `PeriodInvCompatDueByCutoff`
and was deleted then.
-/

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (voteTime supportCutoff)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

section Kit

variable (S : Setup V)

/-- `VotesDueByCutoff S b₀ b₁ s'`: the slot-`s'` honest votes, put on the wire at `voteTime S s'`,
are due by the support cutoff of `s'` around the period: their ordinary deadline `supportCutoff S s'`
is at or before `b₀`, or the period has ended by their vote time. With `GST ≤ voteTime S s'` this is
`deadlineOutside (Δ S) GST b₀ b₁ (voteTime S s') ≤ supportCutoff S s'`.

The variables:
- `S`: the setup; `b₀`, `b₁`: the start and the end of the period; `s'`: the slot of the votes.

Read aloud: the update of slot `s'` sees every honest vote of `s'` as an early vote. -/
def VotesDueByCutoff (b₀ b₁ s' : ℕ) : Prop :=
  supportCutoff S s' ≤ b₀ ∨ b₁ ≤ voteTime S s'

end Kit

section After

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

end After

end GoldilocksCorrectness.Statements.Executions
