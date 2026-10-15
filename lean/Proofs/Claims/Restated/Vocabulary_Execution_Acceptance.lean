import Proofs.Vocabulary.Execution.Acceptance
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_ReceiptCalls
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Objects
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Record.Wiring

/-!
# Every processed object has an accepting event

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, along a path `W`
of a run: an object a store has processed is the genesis block or was accepted at an earlier event,
with the forms for named blocks, erased blocks and Goldfish votes.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution

/-- Along every path `W` of `rho`, if `v`'s store in `W n` has processed `o`, then `o` is the
    genesis block, or `v` accepted `o` at some event `i < n` of `rho`, read along `W`. -/
theorem Vocabulary.Protocol.genesis_or_acceptsAt_of_processed (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) :
    forall (n : Nat) (o : Object V),
      Restated.Vocabulary.Execution.Object.processed M (W n v).st o = true ->
        o = Object.block NamedBlock.genesis ∨
          exists i : Nat, i < n ∧ exists t : Time, Restated.Vocabulary.Execution.Run.acceptsAt M S rho W i v o t := by
  intro n
  induction n with
  | zero =>
      intro o hprocessed
      have h0 : W 0 = fun v => M.initial S v := by
        have h := (hW 0).1
        rw [Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_zero facts] at h
        exact Set.mem_singleton_iff.mp h
      rw [h0] at hprocessed
      cases o with
      | block B =>
          simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] at hprocessed
          rw [facts.nd.initial_st, facts.hd.initial_bodies] at hprocessed
          exact Or.inl (congrArg Object.block (Finset.mem_singleton.mp hprocessed))
      | gfVote u =>
          simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] at hprocessed
          rw [facts.nd.initial_st, ← facts.sto.mem_pool_iff] at hprocessed
          exact absurd hprocessed (facts.hd.initial_core_not_mem_pool _ u)
      | attest a =>
          simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] at hprocessed
          rw [facts.nd.initial_st, facts.hd.initial_sg_rows] at hprocessed
          simp only [List.not_mem_nil] at hprocessed
  | succ n ih =>
      intro o hpost
      by_cases hpre : Restated.Vocabulary.Execution.Object.processed M (W n v).st o = true
      · rcases ih o hpre with hgen | ⟨i, hi, t, haccepts⟩
        · exact Or.inl hgen
        · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, t, haccepts⟩
      · have hpreFalse : Restated.Vocabulary.Execution.Object.processed M (W n v).st o = false :=
          Bool.eq_false_of_not_eq_true hpre
        obtain ⟨t, hacc⟩ := Restated.Vocabulary.Proofs.NamedReceiptCalls.new_marker_accepts facts S rho n v o
          W hW hpreFalse hpost
        exact Or.inr ⟨n, Nat.lt_succ_self n, t, hacc⟩

end

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution

/-- Along every path `W` of `rho`, if `v`'s store in `W n` has processed the block `B`, then `B` is
    genesis, or `v` accepted `B` at some event `i < n`, read along `W`. -/
theorem Vocabulary.Protocol.acceptsAt_block_of_processed (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (n : Nat) (B : NamedBlock V)
    (hprocessed : Restated.Vocabulary.Execution.Object.processed M (W n v).st (.block B) = true) :
    B = NamedBlock.genesis ∨
      exists i : Nat, i < n ∧ exists t : Time,
        Restated.Vocabulary.Execution.Run.acceptsAt M S rho W i v (.block B) t := by
  rcases Restated.Vocabulary.Protocol.genesis_or_acceptsAt_of_processed facts S rho v W hW n (.block B) hprocessed with
    hgen | haccepts
  · exact Or.inl (NamedObject.block.inj hgen)
  · exact Or.inr haccepts

end

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution

/-- Along every path `W` of `rho`, if the block `B` is in the tree of `v`'s store in `W n`, then `B`
    is genesis, or it is the erasure of a named block `D` that `v` accepted at some event `i < n`,
    read along `W`. -/
theorem Vocabulary.Protocol.acceptsAt_block_of_processed_erased (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (n : Nat) {B : Block V}
    (hprocessed : B ∈ (W n v).st.core.T) :
    B = Block.genesis ∨
      exists D : NamedBlock V, D.erase = B ∧
        exists i : Nat, i < n ∧ exists t : Time,
          Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (.block D) t := by
  obtain ⟨D, hD, hDB⟩ := Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts
    S rho n v (W n) (hW n).1 hprocessed
  have hprocessedD : Restated.Vocabulary.Execution.Object.processed M (W n v).st (.block D) = true := by
    simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq]
    exact hD
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho v W hW n D hprocessedD with hgen | hacc
  · left
    rw [← hDB, hgen]
    exact Proofs.ModelProperties.erase_genesis
  · right
    exact ⟨D, hDB, hacc⟩

end

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution

/-- Along every path `W` of `rho`, if `v`'s store in `W n` has processed the Goldfish vote `u`, then
    `v` accepted `u` at some event `i < n`, read along `W`. -/
theorem Vocabulary.Protocol.acceptsAt_gfVote_of_processed (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (n : Nat) (u : GoldfishVote V)
    (hprocessed : Restated.Vocabulary.Execution.Object.processed M (W n v).st (.gfVote u) = true) :
    exists i : Nat, i < n ∧ exists t : Time,
      Restated.Vocabulary.Execution.Run.acceptsAt M S rho W i v (.gfVote u) t := by
  rcases Restated.Vocabulary.Protocol.genesis_or_acceptsAt_of_processed facts S rho v W hW n (.gfVote u) hprocessed with
    hgen | haccepts
  · cases hgen
  · exact haccepts

end

end DecoupledConsensusModel.Sts.Restated
