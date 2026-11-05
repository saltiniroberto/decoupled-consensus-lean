module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Stability

@[expose] public section

/-!
# Lemma 89: the fork-choice change does not count a finality move

The fact about `ForkChoiceChangeAt` copied
from `scratch/goldilocks_healed/probe_fmoves_1.lean`:

- `finality_move_not_change`: a step with `h_max ≠ h_j + 1` after it and no rise of
  `head_height_floor` is no fork-choice change.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **A finality move is no fork-choice change.** When, after `t`, `w`'s `h_max` is not `h_j + 1`
(so its root is its finalized block) and its `head_height_floor` did not rise, `w` has no
`ForkChoiceChangeAt` at `t`, whatever its finalized block did at `t`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `w`: the validator; `t`: the time.

Read aloud: a step that leaves `w` with `h_max` other than `h_j + 1` and does not raise its least
viable height is not a fork-choice change, even when the finalized block moves
onto the justified block. -/
theorem finality_move_not_change (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (w : V) (t : ℕ)
    (hm : (stateBefore x (t + 1) w).S.h_max ≠ (stateBefore x (t + 1) w).S.h_j + 1)
    (hfl : head_height_floor (stateBefore x (t + 1) w).S ≤
      head_height_floor (stateBefore x t w).S) :
    ¬ ForkChoiceChangeAt S Sched x w t := by
  rintro (⟨-, h2, -⟩ | h)
  · exact hm h2
  · exact absurd hfl (Nat.not_le.mpr h)

end GoldilocksCorrectness.Proofs.Executions
