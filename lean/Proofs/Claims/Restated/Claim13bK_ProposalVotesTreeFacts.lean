import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ProposalVotesPivot
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.Claim13beRoute3_4
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Vocabulary_Execution_Acceptance
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockAdmission
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bK_ProposalVotesPivot
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Record.Wiring

/-!
# The trees read by the proposal and vote duties

The trees the proposal and vote duties read are the node's own, they are root-injective below for an
honest validator, and no block of the voter's tree is a child of a block of the vote's slot; stated
over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p51% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_51)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The store slot `s`'s proposal duty reads holds exactly the blocks the node held before the tick. -/
theorem proposalStoreAt_T_eq_before (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) :
    (Restated.proposalStoreAt M S before s).T = before.st.core.T := by
  rw [Restated.proposalStoreAt, facts.hd.Sts_setClock_core_T]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The store slot `s`'s vote duty reads holds exactly the blocks the node held before the tick. -/
theorem voteStoreAt_T_eq_before (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) :
    (Restated.voteStoreAt M S before s).T = before.st.core.T := by
  rw [Restated.voteStoreAt, facts.hd.Sts_setClock_core_T]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `Restated.RootCollisionFreeInLog`, if `w` is honest through the instant of step `n` and
    every block of `Tr` is in `w`'s tree after `n` steps, then two blocks with equal roots, each an
    ancestor of or equal to a block of `Tr`, are equal. -/
theorem rootInjectiveBelow_of_subset_tree (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (hroot : Restated.RootCollisionFreeInLog M S Sched x)
    {n : Nat} {w : V} (hw : Restated.HonestThrough M Sched x n w) {Tr : Finset (Block V)}
    (hsub : Tr ⊆ (x[n][w].st).st.core.T) :
    RootInjectiveBelow Tr := by
  refine rootInjectiveBelow_intro ?_
  intro A C B₁ B₂ hB₁ hAB₁ hB₂ hCB₂ hAC
  obtain ⟨D₁, hD₁, rfl⟩ := Restated.exists_named_of_mem_tree facts S Sched x n w (hsub hB₁)
  obtain ⟨D₂, hD₂, rfl⟩ := Restated.exists_named_of_mem_tree facts S Sched x n w (hsub hB₂)
  exact RootInjectiveOnAncestors.eq_of_root_eq
    (Restated.rootInjectiveOnAncestors_of_collisionFreeInLog facts S Sched x hroot D₁ D₂
      (Restated.blockInLog_of_mem_bodies facts S Sched hw hD₁) (Restated.blockInLog_of_mem_bodies facts S Sched hw hD₂))
    hAB₁ hCB₂ hAC

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- On a valid execution, if `w` is honest through the instant of step `k`, the tree `w`'s proposal
    duty for slot `s` descends, at the read made from `w`'s node state after `k` steps, is
    root-injective below. -/
theorem rootInjectiveBelow_proposalTree_of_honest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) {k : Nat} {w : V}
    (hw : Restated.HonestThrough M Sched x k w) (s : Slot) :
    RootInjectiveBelow
      (M.get_filtered_block_tree (M.toHealing (Restated.proposalStoreAt M S (x[k][w].st) s)).toFG) := by
  refine Restated.rootInjectiveBelow_of_subset_tree facts S Sched x hexec.idealization hw ?_
  intro C hC
  have h := facts.fc.get_filtered_block_tree_subset _ hC
  have e : (Restated.proposalStoreAt M S (x[k][w].st) s).T = (x[k][w].st).st.core.T :=
    Restated.proposalStoreAt_T_eq_before facts S (x[k][w].st) s
  rw [← e]
  rw [facts.sto.toHealing_gs_T] at h
  exact h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- On a valid execution, if slot `s`'s proposer is honest through slot `s`'s vote instant and step
    `k` is the sts tick at slot `s`'s proposal instant, the tree the proposer's proposal duty
    descends at its read from step `k` is root-injective below. -/
theorem rootInjectiveBelow_proposalTree (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) {s : Slot}
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    {k : Nat} (hk : Restated.tickStepAt M x k (M.proposal_time S.E s)) :
    RootInjectiveBelow
      (M.get_filtered_block_tree
        (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)).toFG) := by
  refine Restated.rootInjectiveBelow_proposalTree_of_honest facts S Sched x hexec ?_ s
  intro t ht
  have h1 := (Restated.tickStepAt_time facts x hk).2
  have h2 := Restated.proposal_time_le_vote_time_g1 facts S s
  exact hprop t (by linarith)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- On a valid execution, if `w` is honest through the instant of step `mr`, every tree `w`'s vote
    duty for slot `s` can descend, at the read made from `w`'s node state after `mr` steps, is
    root-injective below. -/
theorem rootInjectiveBelow_voteTree_of_honest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) {mr : Nat} {w : V}
    (hw : Restated.HonestThrough M Sched x mr w) (s : Slot) :
    ∀ T : Finset (Block V),
      Restated.voteTreeOf M S.E (Restated.voteStoreAt M S (x[mr][w].st) s) ⇢ T →
      RootInjectiveBelow T := by
  intro T hT
  refine Restated.rootInjectiveBelow_of_subset_tree facts S Sched x hexec.idealization hw ?_
  intro C hC
  have h := facts.hd.Sts_voter_filtered_block_tree_subset S.E
    (Restated.voteStoreAt M S (x[mr][w].st) s) _ T hT hC
  rw [Restated.voteStoreAt_T_eq_before facts] at h
  exact h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- On a valid execution with monotone corruption, if `v` is in `HonSlot S Sched s` and step `mr` is
    the sts tick at slot `s`'s vote instant, every tree `v`'s slot-`s` vote duty can descend is
    root-injective below. -/
theorem rootInjectiveBelow_voteTree (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption)
    {s : Slot} {v : V} (hv : v ∈ Restated.HonSlot M S Sched s)
    {mr : Nat} (hmr : Restated.tickStepAt M x mr (M.vote_time S.E s)) :
    ∀ T : Finset (Block V),
      Restated.voteTreeOf M S.E (Restated.voteStoreAt M S (x[mr][v].st) s) ⇢ T →
      RootInjectiveBelow T := by
  refine Restated.rootInjectiveBelow_voteTree_of_honest facts S Sched x hexec
    (Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hv ?_) s
  have h1 := (Restated.tickStepAt_time facts x hmr).2
  have h2 := Restated.vote_time_le_confirmation_time_g1 facts S s
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every block other than genesis in any validator's tree after any number of sts steps has its
    parent at a slot strictly before its own. -/
theorem parent_slot_lt_of_mem_tree_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (n : Nat) (w : V) {C : Block V}
    (hC : C ∈ (x[n][w].st).st.core.T) (hne : C ≠ Block.genesis) :
    C.parent.slot < C.slot := by
  obtain ⟨w₁, hw₁, hwv⟩ := Record.stateBeforeOf_runOfM M S Sched x facts.nd.wake_events_or_id w n
  obtain ⟨W, hW, hWn⟩ := (p51% exists_onePath_through₅₁) (Setup.alwaysAwake S)
    (Record.runOfM M S Sched x w n) _ w₁ hw₁
  have hC' : C ∈ (W (Record.veventsOf M S Sched x w n).length w).st.core.T := by
    rw [hWn, hwv]
    exact hC
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed_erased facts (Setup.alwaysAwake S)
      (Record.runOfM M S Sched x w n) w W hW _ hC' with hgen | ⟨D, hDe, i, -, t, hacc⟩
  · exact absurd hgen hne
  · have h := Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts (Setup.alwaysAwake S)
      W hW hacc
    rw [hDe] at h
    exact h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `mr` is the sts tick at slot `s`'s vote instant and `B` is a block of slot `s`, no block
    of any tree `v`'s slot-`s` vote duty can descend has `B` as its parent. -/
theorem voteTree_no_child_of_slot (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {s : Slot} {mr : Nat}
    (hmr : Restated.tickStepAt M x mr (M.vote_time S.E s)) (v : V) {B : Block V}
    (hBslot : B.slot = s) :
    ∀ T : Finset (Block V),
      Restated.voteTreeOf M S.E (Restated.voteStoreAt M S (x[mr][v].st) s) ⇢ T →
      ∀ C ∈ T, C.parent? ≠ some B := by
  intro T hT C hC hpar
  have hCT : C ∈ (x[mr][v].st).st.core.T := by
    have h := facts.hd.Sts_voter_filtered_block_tree_subset S.E
      (Restated.voteStoreAt M S (x[mr][v].st) s) _ T hT hC
    rw [Restated.voteStoreAt_T_eq_before facts] at h
    exact h
  have hstore : (x[mr][v].st).st.core.s ≤ s := by
    refine Restated.store_slot_le_of_clock_le facts S Sched x mr v ?_
    have h1 := (Restated.tickStepAt_time facts x hmr).2
    have h2 := Restated.clock_le_time_sts facts S Sched x mr v
    linarith
  have hCs : C.slot ≤ s := le_trans (Restated.treeSlotBounded_sts facts S Sched x mr v C hCT) hstore
  have hlt := Restated.parent_slot_lt_of_mem_tree_sts facts S Sched x mr v hCT (ne_genesis_of_parent?_eq_some hpar)
  rw [Proofs.parent_eq_of_parent? hpar, hBslot] at hlt
  exact absurd (lt_of_lt_of_le hlt hCs) (lt_irrefl s)

end

end DecoupledConsensusModel.Sts.Restated
