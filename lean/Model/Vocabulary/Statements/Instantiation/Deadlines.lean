module
public import Model.Vocabulary.Execution.Setup

@[expose] public section

/-!
# Finality deadlines

The finality startup and inclusion deadline formulas, in rounds, as functions of the recurrence gap
and the height parameters.
-/

namespace DecoupledConsensusModel.Statements.Instantiation

open DecoupledConsensusModel DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/- The startup lag for finality liveness, in rounds. -/
def finalityStartup (S : Setup V) (gap : Round) (extra : Nat) : Round :=
  1 + (S.cfg.D + S.cfg.K + 5) * (7 * gap + 22 + 4 * extra) +
    3 * (7 * gap + 22 + 4 * extra) + gap + 5

/- The finality deadline after a common finalized block, in rounds. -/
def finalityDeadline (S : Setup V) (gap : Round) (extra : Nat) : Round :=
  (S.cfg.D + S.cfg.K + 2) *
    (4 * (7 * gap + 22 + 4 * extra) + 4 * gap + 7 +
      (S.cfg.D + S.cfg.K + 5) * (gap + 1))

end DecoupledConsensusModel.Statements.Instantiation

end
