module
public import Proofs.Vocabulary.Protocol.Grades.RelativeOneChain
public import Proofs.Vocabulary.Protocol.ChainState.FGRootWitness
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ActionConfirmationCore
public import Proofs.Vocabulary.Protocol.Grades.Q31_actionSGBlock_tiers
public import Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader
public import Proofs.Vocabulary.Protocol.Grades.RelativeSupporter
public import Proofs.Vocabulary.Protocol.Grades.ProposalLifecycleCore
import Proofs.Vocabulary.Execution.RecoveryActionLiveSourceSplit
import Proofs.Vocabulary.Protocol.Schedule.WeakProcessedTree

@[expose] public section


/-!
# Stored heights and candidate paths at a vote duty

At an honest vote-duty read, a held run block is stored at its derived height, and a processed
descendant at the reader's height band puts a block, and the path to it from the voter anchor, in
the voter candidate tree.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakJoint

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]


/-- An honest validator's vote-duty read stores every run block it holds at that block's derived
    height. -/
theorem storedHeight_of_runBlock_mem_voteDutyRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {X : NamedBlock V}
    (hXrun : RunBlock S rho X)
    (hXmem : X.erase ∈
      (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.T) :
    ((Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.σ X.erase).h =
      (Protocol.derive_named S.E S.cfg X).h := by
  obtain ⟨X', hX', hX'erase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.vote_time S.E s) w (by
        simpa only [Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock] using hXmem)
  have hX'run : RunBlock S rho X' := by
    obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted
      (Protocol.vote_time S.E s)
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw
    change X' ∈ (NamedRun.stateBefore S rho i w).st.bodies
    rw [← hi]
    exact hX'
  have hX'eq : X' = X :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      X' X hX'run hXrun X' X (Or.inl (Proofs.NamedAncestry.named_self X'))
        (Or.inr (Proofs.NamedAncestry.named_self X)) (by
          rw [← Proofs.NamedWire.erase_root X', ← Proofs.NamedWire.erase_root X, hX'erase])
  have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
    S rho (Protocol.vote_time S.E s) w X (by simpa only [hX'eq] using hX')
  simpa only [Internal.NamedRecoveryRead.voteDutyRead,
    NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom,
    Protocol.NamedStore.setClock] using congrArg (fun st => st.h) hview

#print axioms storedHeight_of_runBlock_mem_voteDutyRead

/-- If `D` is a processed descendant of `C` with `h_max - 1 ≤ σ(D).h` in `w`'s slot-`s + 1`
    vote-duty read, and `C` is a descendant of that read's FG root, then `C` and every block
    strictly between `w`'s voter anchor and `C` are in `w`'s voter candidate tree. -/
theorem namedCandidatePath_of_processedBandDescendant_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {C D : Block V}
    (hCD : Block.Preceq C D)
    (hDprocessed : D ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s)
    (hband : (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
      ((Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.σ D).h)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C) :
    C ∈ voterCandidateTreeAt S rho w (s + 1) ∧
      ∀ B : Block V,
        Block.Preceq (voterAnchorAt S rho w (s + 1)) B →
        B ≠ voterAnchorAt S rho w (s + 1) →
        Block.Preceq B C → B ≠ C →
        B ∈ voterCandidateTreeAt S rho w (s + 1) := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)
  have hDread : D ∈ Protocol.voter_processed_block_tree S.E
      read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s := by
    simpa only [read, Internal.NamedRecoveryRead.voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Protocol.Store.toHealing, Run.storeBeforeTime] using hDprocessed
  have hancestor : ∀ B : Block V, Block.Preceq B D →
      B ∈ Protocol.voter_processed_block_tree S.E
        read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s := by
    intro B hBD
    have hanc := WeakGoldfish.ancestorProcessed_of_voterProcessed
      S adm hw (s := s) (B := D) hDprocessed B hBD
    simpa only [read, Internal.NamedRecoveryRead.voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Protocol.Store.toHealing, Run.storeBeforeTime] using hanc
  have hFroot : Block.Preceq read.st.core.F
      (Protocol.get_fg_root read.st.core.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F
      (st := read.st.core.toHealing.toFG) (by
        simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock, Block.Preceq, Protocol.Store.toHealing] using
            (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
              S rho (Protocol.vote_time S.E (s + 1)) w))
  have hmem : ∀ B : Block V,
      Block.Preceq (Protocol.get_fg_root read.st.core.toHealing.toFG) B →
      Block.Preceq B C →
      B ∈ voterCandidateTreeAt S rho w (s + 1) := by
    intro B hrootB hBC
    change B ∈ Protocol.get_filtered_block_tree_from
      read.st.core.toHealing.toFG
      (Protocol.voter_processed_block_tree S.E
        read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
    simp only [Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨⟨hancestor B (Block.preceq_trans hBC hCD),
      Block.preceq_trans hFroot hrootB⟩,
      D, hDread, Block.preceq_trans hBC hCD, hband⟩, hrootB⟩
  refine ⟨hmem C hroot (Block.preceq_self C), ?_⟩
  intro B hAB _ hBC _
  have hrootAnchor : Block.Preceq
      (Protocol.get_fg_root read.st.core.toHealing.toFG)
      (voterAnchorAt S rho w (s + 1)) :=
    NamedOutageClosure.fg_root_preceq_anchor S.E S.hc
      read.st.core.toHealing (S.hc.round_of read.st.core.s)
      (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing
        (S.hc.round_of read.st.core.s)).g1
  exact hmem B (Block.preceq_trans hrootAnchor hAB) hBC

theorem namedCandidatePath_of_processedBandDescendant
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {C D : Block V}
    (hCD : Block.Preceq C D)
    (hDprocessed : D ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s)
    (hband : (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
      ((Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.σ D).h)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C) :
    C ∈ voterCandidateTreeAt S rho w (s + 1) ∧
      ∀ B : Block V,
        Block.Preceq (voterAnchorAt S rho w (s + 1)) B →
        B ≠ voterAnchorAt S rho w (s + 1) →
        Block.Preceq B C → B ≠ C →
        B ∈ voterCandidateTreeAt S rho w (s + 1) :=
  namedCandidatePath_of_processedBandDescendant_core
    S adm.toNamedAdmissibleCore hw hCD hDprocessed hband hroot

#print axioms namedCandidatePath_of_processedBandDescendant_core

#print axioms namedCandidatePath_of_processedBandDescendant


end WeakJoint
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
