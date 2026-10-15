import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bInvariantActiveSinceW

/-!
# The re-based deadline round and the justified height at the switch round

The round `rebasedDeadlineRoundW` and the condition `BaseJustifiedHighAtSwitchRoundW` on the
justified heights at the switch round, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- The re-based deadline round: `gap + 1` rounds after `deadlineRoundW S tGAT gap`. -/
noncomputable def rebasedDeadlineRoundW (M : Record.Model V) (S : Setup V) (tGAT : Int) (gap : Nat) : Round :=
  Restated.deadlineRoundW M S tGAT gap + gap + 1

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- For every anchor `T_D'` of the re-based deadline round, every tick step `n_W` at the switch
    round's action time and every validator `v` honest through `n_W`, the justified height `v`'s
    store holds after `n_W` steps is at least the chain-state height of `T_D'`. -/
def BaseJustifiedHighAtSwitchRoundW (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tE : Int) (gap : Nat) : Prop :=
  ∀ T_D' : NamedBlock V,
    Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D' →
    ∀ n_W : Nat, Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) →
    ∀ v : V, Restated.HonestThrough M Sched x n_W v →
      (M.derive_named S.E S.cfg T_D').h ≤ (x[n_W][v].st).st.core.h_j

end

end DecoupledConsensusModel.Sts.Restated
