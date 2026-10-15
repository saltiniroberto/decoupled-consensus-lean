import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Model.Conditions.Vocabulary_Execution_Runtime
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Objects
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# The node invariant and repeated receipts along the sts execution

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: every node state
of the sts execution satisfies the node invariant, and a receipt of an object the store has already
recorded leaves the node state unchanged.
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

/-- After any number of steps of the sts execution `x`, every validator's node state satisfies the
    whole node invariant. -/
theorem nodeInvariant_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (w : V) :
    Restated.Vocabulary.Proofs.NamedRuntime.NodeInvariant M (Setup.alwaysAwake S) (x[i][w].st) :=
  Record.inv_sts M S Sched x
    (Restated.Vocabulary.Proofs.NamedRuntime.NodeInvariant M (Setup.alwaysAwake S))
    (fun u => Restated.Vocabulary.Proofs.NamedRuntime.initial_invariant facts (Setup.alwaysAwake S) u)
    (fun m hm =>
      ⟨by rw [(facts.nd.wake_st_record m).1]; exact hm.1,
        by rw [(facts.nd.wake_st_record m).2]; exact hm.2.1,
        facts.nd.wake_cache_clipped m hm.2.2⟩)
    (fun u m t out hout hm =>
      ⟨facts.nd.confirmation_invariant_tick (Setup.alwaysAwake S) u m t hm.1 out hout,
        facts.nd.record_invariant_tick (Setup.alwaysAwake S) u m t hm.2.1 out hout,
        facts.nd.cache_clipped_tick (Setup.alwaysAwake S) u m t out hout⟩)
    (fun m o m' hm' hm =>
      ⟨(facts.nd.invariants_process (Setup.alwaysAwake S) m o hm.1 hm.2.1 m' hm').1,
        (facts.nd.invariants_process (Setup.alwaysAwake S) m o hm.1 hm.2.1 m' hm').2,
        facts.nd.cache_clipped_process (Setup.alwaysAwake S) m o m' hm'⟩)
    i w

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Delivering to a validator an object its store has already recorded can only leave its node state
    unchanged: every outcome of the receipt is the node state it started from. -/
theorem process_of_processed_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (w : V) (o : NamedObject V)
    (hp : Restated.Vocabulary.Execution.Object.processed M (x[i][w].st).st o = true) :
    ∀ n', M.process (Setup.alwaysAwake S) (x[i][w].st) o ⇢ n' → n' = x[i][w].st := by
  have _hr_0 : M.reachedNode (x[i][w].st) := Record.reachedNode_sts facts S Sched x i w
  have hinv := Restated.nodeInvariant_sts facts S Sched x i w
  refine facts.nd.process_node_of_store_id _ _ o ?_ hinv.2.2
  cases o with
  | block B =>
      have hB : B ∈ (x[i][w].st).st.bodies := of_decide_eq_true hp
      exact facts.nd.process_block_of_mem_bodies _ _ B hinv.1.1.1.1 hB
  | gfVote u =>
      have hu : u ∈ (M.store_pool (x[i][w].st).st.core u.slot) :=
        (facts.sto.mem_pool_iff _ _ _).2 (of_decide_eq_true hp)
      exact facts.nd.process_gfVote_of_mem_pool _ _ u hu
  | attest a =>
      have ha : a ∈ (x[i][w].st).st.sg_rows a.round := of_decide_eq_true hp
      exact facts.nd.process_attest_of_mem_rows _ _ a hinv.1.1.1.2.2.2.1 ha

end

end DecoupledConsensusModel.Sts.Restated
