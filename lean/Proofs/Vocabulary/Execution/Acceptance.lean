module
public import Proofs.Vocabulary.Execution.ReceiptCalls
public import Proofs.Vocabulary.Protocol.Handlers.StoreBridge
public import Proofs.Vocabulary.ModelProperties.NamedReceipt_processed
public import Proofs.Vocabulary.ModelProperties.NamedNode_initial
public import Proofs.Vocabulary.ModelProperties.NamedStore_initial
public import Proofs.Vocabulary.ModelProperties.NamedBlock_erase
import Proofs.Vocabulary.Execution.Runtime
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# First-acceptance provenance along a run

Every object processed at a run prefix has an earlier accepting event (`Run.acceptsAt`), except the
genesis block, which is in every initial store. Goldfish votes and attestations start in empty pools
and have no exception.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Prefix provenance -/


/-- Every object processed at a run prefix has an earlier accepting event, except the genesis block,
    which is in the initial store. -/
theorem genesis_or_acceptsAt_of_processed (S : Setup V) (rho : Run V) (v : V) :
    forall (n : Nat) (o : Object V),
      Object.processed (rho.stateBefore S n v).st o = true ->
        o = Object.block NamedBlock.genesis ∨
          exists i : Nat, i < n ∧ exists t : Time, Run.acceptsAt S rho i v o t := by
  intro n
  induction n with
  | zero =>
      intro o hprocessed
      cases o with
      | block B =>
          change NamedReceipt.processed (NamedNode.initial : NamedNodeState V).st (.block B) = true
            at hprocessed
          rw [Proofs.ModelProperties.initial_st, Proofs.ModelProperties.processed_block_eq_true_iff,
            Proofs.ModelProperties.initial_bodies] at hprocessed
          exact Or.inl (congrArg Object.block (Finset.mem_singleton.mp hprocessed))
      | gfVote u =>
          change NamedReceipt.processed (NamedNode.initial : NamedNodeState V).st (.gfVote u) = true
            at hprocessed
          rw [Proofs.ModelProperties.initial_st, Proofs.ModelProperties.processed_gfVote_eq_true_iff]
            at hprocessed
          exact absurd hprocessed (Proofs.ModelProperties.initial_core_not_mem_pool _ u)
      | attest a =>
          change NamedReceipt.processed (NamedNode.initial : NamedNodeState V).st (.attest a) = true
            at hprocessed
          rw [Proofs.ModelProperties.initial_st, Proofs.ModelProperties.processed_attest_eq_true_iff,
            Proofs.ModelProperties.initial_sg_rows] at hprocessed
          simp only [List.not_mem_nil] at hprocessed
  | succ n ih =>
      intro o hpost
      by_cases hpre : Object.processed (rho.stateBefore S n v).st o = true
      · rcases ih o hpre with hgen | ⟨i, hi, t, haccepts⟩
        · exact Or.inl hgen
        · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, t, haccepts⟩
      · have hpreFalse : Object.processed (rho.stateBefore S n v).st o = false :=
          Bool.eq_false_of_not_eq_true hpre
        obtain ⟨t, hacc⟩ := Proofs.NamedReceiptCalls.new_marker_accepts S rho n v o hpreFalse hpost
        exact Or.inr ⟨n, Nat.lt_succ_self n, t, hacc⟩

/-- A processed block other than genesis has an earlier accepting event. -/
theorem acceptsAt_block_of_processed (S : Setup V) (rho : Run V) (v : V)
    (n : Nat) (B : NamedBlock V)
    (hprocessed : Object.processed (rho.stateBefore S n v).st (.block B) = true) :
    B = NamedBlock.genesis ∨
      exists i : Nat, i < n ∧ exists t : Time,
        Run.acceptsAt S rho i v (.block B) t := by
  rcases genesis_or_acceptsAt_of_processed S rho v n (.block B) hprocessed with
    hgen | haccepts
  · exact Or.inl (NamedObject.block.inj hgen)
  · exact Or.inr haccepts

/-- A block in the erased tree at a run prefix is genesis, or the erasure of a named block with an
    earlier accepting event. -/
theorem acceptsAt_block_of_processed_erased (S : Setup V) (rho : Run V) (v : V)
    (n : Nat) {B : Block V}
    (hprocessed : B ∈ (rho.stateBefore S n v).st.core.T) :
    B = Block.genesis ∨
      exists D : NamedBlock V, D.erase = B ∧
        exists i : Nat, i < n ∧ exists t : Time,
          NamedRun.acceptsAt S rho i v (.block D) t := by
  obtain ⟨D, hD, hDB⟩ := Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore
    S rho n v hprocessed
  have hprocessedD : Object.processed (rho.stateBefore S n v).st (.block D) = true := by
    exact (Proofs.ModelProperties.processed_block_eq_true_iff _ D).mpr hD
  rcases acceptsAt_block_of_processed S rho v n D hprocessedD with hgen | hacc
  · left
    rw [← hDB, hgen]
    exact Proofs.ModelProperties.erase_genesis
  · right
    exact ⟨D, hDB, hacc⟩

/-- A processed Goldfish vote has an earlier accepting event. -/
theorem acceptsAt_gfVote_of_processed (S : Setup V) (rho : Run V) (v : V)
    (n : Nat) (u : GoldfishVote V)
    (hprocessed : Object.processed (rho.stateBefore S n v).st (.gfVote u) = true) :
    exists i : Nat, i < n ∧ exists t : Time,
      Run.acceptsAt S rho i v (.gfVote u) t := by
  rcases genesis_or_acceptsAt_of_processed S rho v n (.gfVote u) hprocessed with
    hgen | haccepts
  · cases hgen
  · exact haccepts

#print axioms acceptsAt_block_of_processed_erased

end Protocol
end DecoupledConsensusModel

end
