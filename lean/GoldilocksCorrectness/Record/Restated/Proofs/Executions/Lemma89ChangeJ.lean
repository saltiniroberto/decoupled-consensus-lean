module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89Stability
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.Lemma89Defs

@[expose] public section

/-!
# Lemma89ChangeJ, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89ChangeJ.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: a step with no rise of
`head_height_floor` and the greatest chain-state height not one past the justification height after
it is no fork-choice change. The page's routine-level theorems are the facts' fields or have their
twins in phase A.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **A finality move is no fork-choice change.** When, after the step `j`, `w`'s greatest chain-state
height `hMax M S.C n` is not `h_j + 1` (so its root is its finalized block) and its
`head_height_floor` did not rise, the step `j` is no `ForkChoiceChangeStep` of `w`, whatever its
finalized block did at `j`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`: the setup, the activity, the execution; `w`: the validator; `j`: the step.

Read aloud: a step that leaves `w` with its greatest chain-state height other than `h_j + 1` and
does not raise its `head_height_floor` is not a fork-choice change, even when the finalized block
moves onto the justified block. -/
theorem finality_move_not_change (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (w : V) (j : ℕ)
    (hm : hMax M S.C (x.st (j + 1) w) ≠ (x.st (j + 1) w).justifiedHeight + 1)
    (hfl : M.head_height_floor (x.st (j + 1) w) ≤ M.head_height_floor (x.st j w)) :
    ¬ ForkChoiceChangeStep M S A x w j := by
  rintro (⟨-, h2, -⟩ | h)
  · exact hm h2
  · exact absurd hfl (Nat.not_le.mpr h)

end GoldilocksCorrectness.Record.Proofs.Executions

