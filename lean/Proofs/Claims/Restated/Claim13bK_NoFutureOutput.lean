import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundWindow
import Proofs.Claims.Restated.Claim13bK_ProposalVotesPivot
import Proofs.Claims.Restated.Claim13bK_ProposalVotesTreeFacts
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRecord
import Proofs.Claims.Restated.Claim13beRoute3_4
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bModel_Block_preceq

/-!
# Blocks of a slot not yet started

Trees of validators are closed under parents, ancestors have smaller slots, and before slot `s`'s
proposal instant no output holds a block of slot `s`, stated over a model `M : Record.Model V` and
its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "pSB% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open Framework.StsMultisetLog

/-- After any number of sts steps, every block of a validator's tree that has a parent has that
    parent in the same tree. -/
theorem parent_mem_tree_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (v : V) :
    ∀ B ∈ (x[i][v].st).st.core.T, B.parent? = none ∨ B.parent ∈ (x[i][v].st).st.core.T := by
  have hpc := (pSB% parentClosed_of_inv') facts (Restated.nodeInvariant_sts facts S Sched x i v)
  unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
  rw [facts.sto.toHealing_gs_T] at hpc
  exact hpc.2

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open Framework.StsMultisetLog

/-- After any number of sts steps, if `C` is a block of a validator's tree and `X ⪯ C`, the slot of
    `X` is at most the slot of `C`. -/
theorem preceq_slot_le_of_mem_tree_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (v : V) {C X : Block V}
    (hC : C ∈ (x[i][v].st).st.core.T) (hXC : Block.Preceq X C) : X.slot ≤ C.slot :=
  preceq_slot_le_of_parentClosed (Restated.parent_mem_tree_sts facts S Sched x i v)
    (fun _ hD hne => Restated.parent_slot_lt_of_mem_tree_sts facts S Sched x i v hD hne) C hC X hXC

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open Framework.StsMultisetLog

/-- If step `i`'s instant is strictly before slot `s`'s proposal instant, every block of any
    validator's tree after `i` steps is of a slot strictly before `s`. -/
theorem tree_slot_lt_of_time_lt_proposal (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {s : Slot} (v : V) {i : Nat}
    (hi : (x[i].time : Int) < M.proposal_time S.E s) {C : Block V}
    (hC : C ∈ (x[i][v].st).st.core.T) : C.slot < s := by
  have hCs : C.slot ≤ (x[i][v].st).st.core.s := Restated.treeSlotBounded_sts facts S Sched x i v C hC
  have hclock : S.E.slotOf (x[i][v].st).st.core.t ≤ S.E.slotOf (x[i].time : Int) :=
    slotOf_mono_sts S (Restated.clock_le_time_sts facts S Sched x i v)
  have hstart : (x[i].time : Int) < slotStart S.E.Δ s := by
    rw [slotStart_closed, ← Restated.proposal_time_closed_g1 facts S s]
    exact hi
  have htime : S.E.slotOf (x[i].time : Int) < s :=
    slotOf_lt_of_lt_slotStart S (Int.natCast_nonneg _) hstart
  rw [Restated.slotOfClock_sts facts S Sched x i v] at hCs
  exact lt_of_le_of_lt (le_trans hCs hclock) htime

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open Framework.StsMultisetLog

/-- After any number of sts steps, a validator's stable output is a block of its tree. -/
theorem get_stable_mem_tree_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (v : V) :
    M.get_stable (x[i][v].st).st.core ∈ (x[i][v].st).st.core.T := by
  rcases facts.hd.get_stable_eq_or (x[i][v].st).st.core with h | h
  · rw [h]; exact (Restated.records_mem_tree_sts facts S Sched x v i).1
  · rw [h]; exact (Restated.nodeInvariant_sts facts S Sched x i v).1.1.2.1

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open Framework.StsMultisetLog

/-- After any number of sts steps, a validator's confirmed output is a block of its tree. -/
theorem get_confirmed_mem_tree_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (v : V) :
    M.get_confirmed (x[i][v].st).st.core ∈ (x[i][v].st).st.core.T := by
  rcases facts.hd.get_confirmed_eq_or (x[i][v].st).st.core with h | h
  · rw [h]; exact (Restated.records_mem_tree_sts facts S Sched x v i).2
  · rw [h]; exact Restated.get_stable_mem_tree_sts facts S Sched x i v

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open Framework.StsMultisetLog

/-- If step `i`'s instant is strictly before slot `s`'s proposal instant and `B` is of slot `s`,
    then `B` is an ancestor of no block of any validator's tree after `i` steps. -/
theorem not_preceq_mem_tree_before_proposal (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {s : Slot} (v : V) {i : Nat}
    (hi : (x[i].time : Int) < M.proposal_time S.E s) {B C : Block V}
    (hBs : B.slot = s) (hC : C ∈ (x[i][v].st).st.core.T) : ¬ Block.Preceq B C := by
  intro hBC
  have h1 := Restated.preceq_slot_le_of_mem_tree_sts facts S Sched x i v hC hBC
  have h2 := Restated.tree_slot_lt_of_time_lt_proposal facts S Sched x v hi hC
  rw [hBs] at h1
  exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open Framework.StsMultisetLog

/-- At every step whose instant is strictly before slot `s`'s proposal instant, a block of slot `s`
    sent by `s`'s proposer is an ancestor of neither the confirmed nor the stable output of any
    validator. -/
theorem not_preceq_output_before_proposal (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {s : Slot} {k : Nat} {B : Block V}
    (hB : Restated.proposedBlockAtStep M S x k s B) (v : V) {i : Nat}
    (hi : (x[i].time : Int) < M.proposal_time S.E s) :
    ¬ Block.Preceq B (M.get_confirmed (x[i][v].st).st.core) ∧
      ¬ Block.Preceq B (M.get_stable (x[i][v].st).st.core) := by
  obtain ⟨B', -, hBe, hBs, -⟩ := hB
  have hslot : B.slot = s := by rw [← hBe, Proofs.NamedWire.erase_slot, hBs]
  exact ⟨Restated.not_preceq_mem_tree_before_proposal facts S Sched x v hi hslot
      (Restated.get_confirmed_mem_tree_sts facts S Sched x i v),
    Restated.not_preceq_mem_tree_before_proposal facts S Sched x v hi hslot
      (Restated.get_stable_mem_tree_sts facts S Sched x i v)⟩

end

end DecoupledConsensusModel.Sts.Restated
