import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveSince
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Justified heights at the switch round and the after-phase step

The condition that honest justified heights at the switch round reach the height of the deadline
round's anchor, and the after-phase step of the invariant from the base anchor on, stated over a
model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every anchor `T_D` of the deadline round, every step `n_W` that is the tick step at the
    switch round's action instant, and every validator `v` honest through `n_W`, the justified
    height of `v`'s store after `n_W` steps is at least the height of `T_D`. -/
def BaseJustifiedHighAtSwitchRound (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tE : Int) (gap : Nat) : Prop :=
  ∀ T_D : NamedBlock V, Restated.AnchorAtRound M S Sched x tGAT tE (Restated.deadlineRoundW M S tGAT gap) T_D →
    ∀ n_W : Nat, Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) →
    ∀ v : V, Restated.HonestThrough M Sched x n_W v →
      (M.derive_named S.E S.cfg T_D).h ≤ (x[n_W][v].st).st.core.h_j

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- From the invariant with the target clause since the switch round at a round `r` from the switch
    round on, with switch step `n_W` and an anchor `T` that is `T_W` or a descendant of it, the same
    invariant holds at round `r + 1` with the same switch step and an anchor that is `T` or a
    descendant of it. -/
def AfterPhaseStepOverActiveSetsSinceFrom (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (n_W : Nat) (T_W : NamedBlock V) : Prop :=
  ∀ (r : Round) (n : Nat) (T : NamedBlock V), Restated.switchRound M S tE ≤ r →
    Block.Preceq T_W.erase T.erase →
    Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x r n n_W T →
    ∃ (n' : Nat) (T' : NamedBlock V),
      Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x (r + 1) n' n_W T' ∧
        Block.Preceq T.erase T'.erase

end

end DecoupledConsensusModel.Sts.Restated
