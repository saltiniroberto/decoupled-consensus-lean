import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Conditions.Claim13bInvariantActiveSince
import Model.Record.Wiring

/-!
# The finalized block is an ancestor of the justified block

Over a model `M : Record.Model V`, in every validator's store after any number of sts steps.
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

/-- After any number of sts steps, in any validator's store, the finalized block is an ancestor of
    the justified block. -/
theorem finalized_preceq_justified_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (v : V) :
    Block.Preceq (x[i][v].st).st.core.F (x[i][v].st).st.core.J := by
  refine Record.inv_sts M S Sched x (fun n => Block.Preceq n.st.core.F n.st.core.J) ?_ ?_ ?_ ?_ i v
  · intro u
    show Block.Preceq (M.initial (Setup.alwaysAwake S) u).st.core.F
      (M.initial (Setup.alwaysAwake S) u).st.core.J
    rw [facts.nd.initial_st, facts.hd.initial_core_F, facts.hd.initial_core_J]
    exact Proofs.ModelProperties.Preceq_self (Block.genesis : Block V)
  · intro n h
    show Block.Preceq (M.wake n).st.core.F (M.wake n).st.core.J
    rw [(facts.nd.wake_st_record n).1]
    exact h
  · intro u n t out hout h
    exact facts.nd.frozen_tick_preceq (Setup.alwaysAwake S) u n t h out hout
  · intro n o n' hn' h
    exact facts.nd.frozen_process_preceq (Setup.alwaysAwake S) n o h n' hn'

end

end DecoupledConsensusModel.Sts.Restated
