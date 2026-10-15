import Proofs.Vocabulary.Protocol.Schedule.HeldSkipProducers
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_ReceiptCallsBase
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Vocabulary.Protocol.Grades.NamedDuties
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Record.Wiring

/-!
# New bodies after a tick or a block call

A body that a tick or a block call adds was inserted by the block core, which fixes the tree
membership and the finalized block that follow, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedOutageHistory
open DecoupledConsensusModel.Proofs.NamedOutageHistory.HeldSkipProducers
open Execution Execution.NamedReceiptCalls Protocol

/-- For every outcome `out` of `v`'s tick at `t` from the node state `n`, if `B` is not among the
    bodies of `n`'s store and is among the bodies of `out`'s store, then `B` is among the bodies the
    block core returns on `n`'s store with its clock set to `t` and `B`, and that core's finalized
    block is the finalized block of `out`'s store. -/
theorem Vocabulary.Proofs.NamedOutageHistory.HeldSkipProducers.tick_new_body_core (facts : Record.Facts M)
    (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    (B : NamedBlock V) (hpre : B ∉ n.st.bodies)
    (hpost : B ∈ out.1.st.bodies) :
    B ∈ (M.ns_process_block_core S.E S.hc S.cfg
        (M.ns_setClock S.E n.st t) B).bodies ∧
      (M.ns_process_block_core S.E S.hc S.cfg
        (M.ns_setClock S.E n.st t) B).core.F = out.1.st.core.F :=
  facts.nd.tick_new_body_core S v n t out hout B hpre hpost

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedOutageHistory
open DecoupledConsensusModel.Proofs.NamedOutageHistory.HeldSkipProducers
open Execution Execution.NamedReceiptCalls Protocol

/-- For every path `W` of `rho`, if `before` is the input of the block call of `B` at `v` at the
    `j`-th event of `rho` read along `W`, and `B` is not among `before`'s bodies but is among those
    of the store the core call returns, then `B`'s erasure is not in `before`'s tree and is in the
    tree of that store. -/
theorem Vocabulary.Proofs.NamedOutageHistory.HeldSkipProducers.fresh_core_of_bodies (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (j : Nat) (v : V)
    (B : NamedBlock V) (before : M.NS)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hcall : Restated.Vocabulary.Execution.NamedReceiptCalls.blockCallAt M S rho W j v B before)
    (hpre : B ∉ before.bodies) (hbody : B ∈ (M.postCore S before B).bodies) :
    B.erase ∉ before.core.T ∧ B.erase ∈ (M.postCore S before B).core.T := by
  have hco : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg before :=
    (Restated.Vocabulary.Proofs.NamedReceiptCallsBase.block_call_before_invariant facts S rho W hW
      hcall).1.1
  have hnew : B.erase ∉ before.core.T := by
    intro hmem
    apply hpre
    have h := facts.nd.postCore_bodies_of_erase_mem S before B hmem
    rw [← h]
    exact hbody
  have hcoPost : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (M.postCore S before B) :=
    facts.nd.coherent_postCore S before B hco
  refine ⟨hnew, ?_⟩
  rw [hcoPost.1]
  exact Finset.mem_image_of_mem NamedBlock.erase hbody

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedOutageHistory
open DecoupledConsensusModel.Proofs.NamedOutageHistory.HeldSkipProducers
open Execution Execution.NamedReceiptCalls Protocol

/-- For every path `W` of `rho`, if `v` accepts the block `B` at the `j`-th event of `rho`, at time
    `t`, read along `W`, then for some store `before` that is the input of the block call of `B` at
    `v` at that event, `B`'s erasure is not in `before`'s tree, it is in the tree of the store the
    core call returns on `before`, and that store's finalized block is an ancestor of, or is, the
    finalized block of `v`'s store in `W (j + 1)`. -/
theorem Vocabulary.Proofs.NamedOutageHistory.HeldSkipProducers.accepted_block_fresh_call (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (j : Nat) (v : V)
    (B : NamedBlock V) (t : Time) :
    ∀ W, Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W →
    Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W j v (.block B) t →
    ∃ before : M.NS,
      Restated.Vocabulary.Execution.NamedReceiptCalls.blockCallAt M S rho W j v B before ∧
      B.erase ∉ before.core.T ∧
      B.erase ∈ (M.postCore S before B).core.T ∧
      Block.Preceq (M.postCore S before B).core.F
        (W (j + 1) v).st.core.F := by
  intro W hW hacc
  obtain ⟨⟨hidx, -⟩, hpre0, hpost0⟩ := hacc
  have hpre : B ∉ (W j v).st.bodies := of_decide_eq_false hpre0
  have hpost : B ∈ (W (j + 1) v).st.bodies := of_decide_eq_true hpost0
  change Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong M S rho W j v (.block B) at hidx
  rcases hidx with ⟨tt, hi, out, hout, hWout, hB⟩ | ⟨tt, hi⟩
  · have hcall := Restated.Vocabulary.Proofs.NamedReceiptCallsBase.blockCallAt_self facts S rho hi
      W hW ⟨out, hout, hWout, hB⟩
    rw [hWout] at hpost
    obtain ⟨hbody, hF⟩ :=
      Restated.Vocabulary.Proofs.NamedOutageHistory.HeldSkipProducers.tick_new_body_core facts
        S v (W j v) tt out hout B hpre hpost
    have hbody' : B ∈ (M.postCore S (M.ns_setClock S.E (W j v).st tt) B).bodies := by
      rw [facts.nd.postCore_eq_process_block_core]
      exact hbody
    have hpre' : B ∉ (M.ns_setClock S.E (W j v).st tt).bodies := by
      rw [facts.hd.ModelProperties_setClock_bodies]
      exact hpre
    obtain ⟨hnew, hin⟩ :=
      Restated.Vocabulary.Proofs.NamedOutageHistory.HeldSkipProducers.fresh_core_of_bodies facts
        S rho j v B _ W hW hcall hpre' hbody'
    refine ⟨_, hcall, hnew, hin, ?_⟩
    rw [hWout, facts.nd.postCore_eq_process_block_core, hF]
    unfold Block.Preceq
    exact Block.preceq_self _
  · have hcall := Restated.Vocabulary.Proofs.NamedReceiptCallsBase.blockCallAt_delivery facts S rho hi
      W hW
    rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho hi (W j) (hW j).1
        (W (j + 1)) (hW j).2
      with hproc | ⟨-, hw⟩
    · have hst := facts.nd.process_st S (W j v) (.block B) (W (j + 1) v) hproc
      rw [hst, facts.nd.make_grades_compatible_with_finalized_bodies, facts.nd.process_block]
        at hpost
      have hbody : B ∈ (M.postCore S (W j v).st B).bodies := by
        by_contra hn
        rw [facts.nd.on_block_with_eq_postCore_of_not_new S (W j v).st B (fun h => hn h.2)]
          at hpost
        exact hn hpost
      obtain ⟨hnew, hin⟩ :=
        Restated.Vocabulary.Proofs.NamedOutageHistory.HeldSkipProducers.fresh_core_of_bodies facts
          S rho j v B _ W hW hcall hpre hbody
      refine ⟨_, hcall, hnew, hin, ?_⟩
      rw [hst, facts.nd.make_grades_compatible_with_finalized_core_F, facts.nd.process_block,
        facts.hd.on_block_with_core_F,
        ← facts.nd.postCore_eq_process_block_core]
      unfold Block.Preceq
      exact Block.preceq_self _
    · rw [hw] at hpost
      exact absurd hpost hpre

end

end DecoupledConsensusModel.Sts.Restated
