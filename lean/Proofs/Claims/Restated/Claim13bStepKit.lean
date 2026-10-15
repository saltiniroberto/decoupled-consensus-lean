import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Record.Wiring

/-!
# The finalized block is an ancestor of the justified block

At every configuration of an execution, every validator's finalized block is an ancestor of its
justified block and of the root its finality-gadget layer computes, stated over a model
`M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After any number of steps, every validator's finalized block is an ancestor of its justified
    block. -/
theorem F_preceq_J_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (i : Nat) (v : V) :
    Block.Preceq (x[i][v].st).st.core.F (x[i][v].st).st.core.J := by
  obtain ⟨w, hw, hwv⟩ := Record.stateBeforeOf_runOfM M S Sched x facts.nd.wake_events_or_id v i
  have h := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBefore facts
    (Setup.alwaysAwake S) (Record.runOfM M S Sched x v i) (Record.veventsOf M S Sched x v i).length v
    w hw
  rwa [hwv] at h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After any number of steps, every validator's finalized block is an ancestor of the FG root of
    its store. -/
theorem F_preceq_fgRoot_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (i : Nat) (v : V) :
    Block.Preceq (x[i][v].st).st.core.F
      (M.get_fg_root (M.toHealing (x[i][v].st).st.core).toFG) := by
  by_cases h : (x[i][v].st).st.core.h_max = (x[i][v].st).st.core.h_j + 1
  · rw [facts.fc.get_fg_root_toHealing_of_eq _ h]
    exact Restated.F_preceq_J_sts facts S Sched x i v
  · rw [facts.fc.get_fg_root_toHealing_of_ne _ h]
    exact Proofs.ModelProperties.Preceq_self _

end

end DecoupledConsensusModel.Sts.Restated
