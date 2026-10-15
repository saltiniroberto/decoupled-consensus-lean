import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_BlockEmission
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13beRoute3_7
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_VocabularyAssumptions
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_7

/-!
# Blocks in a store were sent, and carry valid votes

Theorems over an execution of a model `M : Record.Model V`: a non-genesis body of a store was sent,
a block in a store's tree carries well-formed votes, a merged vote view is valid, the root
idealization holds at honest stores, and honest heads are blocks in play.
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

/-- If a validator's store after `m` steps holds a named block other than genesis among its bodies,
    then some step at or before `m` has, in the sent log, a signed message whose payload is that
    block. -/
theorem carried_vote_envelope (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (m : Nat) (v : V) {D : NamedBlock V}
    (hne : D ≠ NamedBlock.genesis) (hD : D ∈ (x[m][v].st).st.bodies) :
    ∃ (j : Nat) (sm : SignedMsg V (NamedObject V)), j ≤ m ∧ sm ∈ x[j].sent ∧
      sm.msg = NamedObject.block D := by
  obtain ⟨i, him, hcase⟩ := Restated.block_sent_of_mem_tree facts S Sched x hne hD
  rcases hcase with ⟨sm, hlbl, hmsg⟩ | ⟨τ, hlbl, haw, out₁, hout, hst, hem⟩
  · exact ⟨i, sm, le_of_lt him, (Restated.sent_of_deliver facts S Sched x hlbl).1, hmsg⟩
  · exact ⟨i + 1, ⟨v, NamedObject.block D⟩, Nat.succ_le_of_lt him,
      Restated.mem_sent_of_tick_of_state facts S Sched x hlbl haw
        (facts.nd.tick_send_eq_of_state (Setup.alwaysAwake S) v _ (τ : Int))
        hout hst hem, rfl⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every block of any validator's tree at any step, each of the block's support votes is one of
    its raw votes, and each of its raw votes names a validator in the committee of that vote's slot. -/
theorem treeBlock_carried_ok (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (m : Nat) (v : V) {Bl : Block V} (hBl : Bl ∈ (x[m][v].st).st.core.T) :
    (∀ u ∈ Bl.gf_support_votes, u ∈ Bl.gf_votes) ∧
      (∀ u ∈ Bl.gf_votes, u.val_index ∈ S.E.committee u.slot) := by
  obtain ⟨D, hD, hDe⟩ := Restated.exists_named_of_mem_tree facts S Sched x m v hBl
  subst hDe
  by_cases hne : D = NamedBlock.genesis
  · subst hne
    rw [Proofs.NamedWire.erase_goldfish_support, Proofs.NamedWire.erase_goldfish_votes,
      named_genesis_gf_votes]
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · simp [NamedBlock.gf_support_votes] at hu
    · simp at hu
  · obtain ⟨i, him, hcase⟩ := Restated.block_sent_of_mem_tree facts S Sched x hne hD
    rcases hcase with ⟨sm, hlbl, hmsg⟩ | ⟨τ, hlbl, haw, out₁, hout, -, hem⟩
    · obtain ⟨-, hsup, hcomm⟩ := (hexec.wire i v sm hlbl).1 D hmsg
      rw [Proofs.NamedWire.erase_goldfish_support, Proofs.NamedWire.erase_goldfish_votes]
      exact ⟨hsup, hcomm⟩
    · have _hr_w := Record.reachedNode_wakeStage facts S Sched x i v (τ : Int)
      have _hv_w := Record.runs_as_wakeStage facts S Sched x i v (τ : Int)
      obtain ⟨-, hprop⟩ :=
        facts.nd.block_mem_on_tick_emit (Setup.alwaysAwake S) v _
          (τ : Int) out₁ hout hem
      rw [Record.wakeStage_st facts, Record.wakeStage_cache facts] at hprop
      obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (x[i][v].st).st.core.toHealing
        (τ : Int) (x[i][v].st).cache
      obtain ⟨P, hP⟩ : ∃ P, M.duties_propose_block_with (M.frameContract c) S.E S.hc S.cfg
          ((Setup.alwaysAwake S).node v) (M.ns_setClock S.E (x[i][v].st).st (τ : Int)) ⇢ P := by
        have hbm := facts.nd.block_mem_on_tick_emit (Setup.alwaysAwake S) v _ (τ : Int) out₁ hout hem
        obtain ⟨P, hP⟩ := facts.dt.propose_block_with_nonempty (Setup.alwaysAwake S) v _ (τ : Int)
          out₁ hout hbm.1.1 hbm.1.2.1 hbm.1.2.2
          (facts.nd.block_mem_on_tick_emit_awake (Setup.alwaysAwake S) v _ (τ : Int) out₁ hout hem) c
          (by rw [Record.wakeStage_st facts, Record.wakeStage_cache facts]; exact hc)
        rw [Record.wakeStage_st facts] at hP
        exact ⟨P, hP⟩
      obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.frameContract c) .poolAndCarried S.E
        S.hc ((Setup.alwaysAwake S).node v) (M.ns_setClock S.E (x[i][v].st).st (τ : Int))
      have hp := facts.dt.proposal_with_of_propose_block_with _ _ _ _ _ _ P hP (hprop c hc P hP)
        o ho
      refine ⟨?_, ?_⟩
      · simpa only [Proofs.NamedWire.erase_goldfish_support,
          Proofs.NamedWire.erase_goldfish_votes] using
          facts.dt.proposal_with_support_subset _ _ _ _ _ o ho hp
      · intro u hu
        rw [Proofs.NamedWire.erase_goldfish_votes] at hu
        rw [facts.dt.proposal_with_gf_votes _ _ _ _ _ _ o ho hp] at hu
        have hpool : u ∈ (M.store_pool (x[i][v].st).st.core)
            ((M.ns_setClock S.E (x[i][v].st).st (τ : Int)).core.s - 1) := by
          rw [facts.sto.mem_store_pool_iff]
          rw [facts.hd.setClock_core_gf_votes] at hu
          exact hu
        have hslot := Restated.slot_of_mem_pool_sts facts S Sched x i v hpool
        have hpool' : u ∈ (M.store_pool (x[i][v].st).st.core u.slot) := by rw [hslot]; exact hpool
        obtain ⟨j, -, -, h0, h1⟩ := Restated.accepts_of_mem_pool facts S Sched x hpool'
        exact (Restated.stamp_eq_clock_of_flip_gfVote facts S Sched x h0 h1).2.2

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every outcome of the merged view that slot `(s + 1)`'s vote duty reads at `v`'s store after `mr`
    steps has every vote of slot `s`, naming a member of slot `s`'s committee. -/
theorem voteSetValid_phase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot} {mr : Nat} {v : V} :
    ∀ W, Restated.voteViewOf M S.E (Restated.voteStoreAt M S (x[mr][v].st) (s + 1)) ⇢ W →
      Protocol.VoteSetValid S.E ((Restated.voteStoreAt M S (x[mr][v].st) (s + 1)).s - 1) W := by
  intro W hW
  rw [Restated.voteStoreAt_slot facts, Nat.add_sub_cancel]
  intro u hu
  have hW' : M.voter_view S.E
      (M.toHealing (Restated.voteStoreAt M S (x[mr][v].st) (s + 1))).toFG.toSG.toGoldfishStore
      (s + 1) ⇢ W := by
    have h := hW
    simp only [Restated.voteViewOf, Restated.voteStoreAt_slot facts S (x[mr][v].st) (s + 1)] at h
    exact h
  rcases facts.fc.voter_view_cases _ _ _ W hW' hu with ⟨hu, -⟩ | ⟨Bl, hBl, -, huv, huslot⟩
  · rw [facts.sto.toHealing_gs_pool, Nat.add_sub_cancel, Restated.voteStoreAt,
      facts.hd.Sts_setClock_core_pool] at hu
    have hpool : u ∈ (M.store_pool (x[mr][v].st).st.core s) := hu
    have hslot : u.slot = s := Restated.slot_of_mem_pool_sts facts S Sched x mr v hpool
    have hpool' : u ∈ (M.store_pool (x[mr][v].st).st.core u.slot) := by rw [hslot]; exact hpool
    obtain ⟨j, -, -, h0, h1⟩ := Restated.accepts_of_mem_pool facts S Sched x hpool'
    have hcomm := (Restated.stamp_eq_clock_of_flip_gfVote facts S Sched x h0 h1).2.2
    rw [hslot] at hcomm
    exact ⟨hslot, hcomm⟩
  · rw [Nat.add_sub_cancel] at huslot
    rw [facts.sto.toHealing_gs_T, Restated.voteStoreAt, facts.hd.Sts_setClock_core_T] at hBl
    have hcomm := (Restated.treeBlock_carried_ok facts S Sched x hexec mr v hBl).2 u huv
    rw [huslot] at hcomm
    exact ⟨huslot, hcomm⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `TreeIdealizes` holds at `v`'s store after `mr` steps when `v` is honest through step `mr`: a
    block of `v`'s tree that resolves to itself and whose root is the root of a named block in play
    is a descendant of `B` whenever that named block's erasure is. -/
theorem treeIdealizes_phase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {mr : Nat} {v : V} (hv : Restated.HonestThrough M Sched x mr v) {B : Block V} :
    Restated.TreeIdealizes M S Sched x v mr B := by
  intro X H hfind hH hroot hHB
  have hXT : X ∈ (x[mr][v].st).st.core.T := Proofs.HealingLemmas.find?_mem hfind
  obtain ⟨D, hD, hDe⟩ := Restated.exists_named_of_mem_tree facts S Sched x mr v hXT
  have hinj := Restated.rootInjectiveOnAncestors_of_collisionFreeInLog facts S Sched x hexec.idealization D H
    (Restated.blockInLog_of_mem_bodies facts S Sched hv hD) hH
  have hHroot : H.erase.root = H.root := Proofs.NamedWire.erase_root H
  have heq : X = H.erase := by
    refine RootInjectiveOnAncestors.eq_of_root_eq hinj ?_
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) ?_
    · rw [hDe]; exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)
    · rw [hHroot]; exact hroot
  rw [heq]
  exact hHB

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every member of `HonSlot S Sched s` and every head `G` its slot-`s` vote duty can select,
    some named block the execution put in play has erasure `G`. -/
theorem headsInPlay_phase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (hmono : Sched.MonotoneCorruption) {s : Slot} {m : Nat}
    (hmc : (x[m].time : Int) ≤ M.confirmation_time S.E s) :
    ∀ v' ∈ Restated.HonSlot M S Sched s, ∀ G : Block V,
      Restated.gfHeadFrom M S (x[m][v'].st) s ⇢ G →
      ∃ H : NamedBlock V, Restated.blockInLog M S Sched x H ∧ H.erase = G := by
  intro v' hv' G hG
  have hv'h : Restated.HonestThrough M Sched x m v' :=
    Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hv' hmc
  obtain ⟨H, hH, hHe⟩ :=
    Restated.exists_named_of_mem_tree facts S Sched x m v'
      (Restated.gfHeadFrom_mem_tree facts S Sched x m v' s G hG)
  exact ⟨H, Restated.blockInLog_of_mem_bodies facts S Sched hv'h hH, hHe⟩

end

end DecoupledConsensusModel.Sts.Restated
