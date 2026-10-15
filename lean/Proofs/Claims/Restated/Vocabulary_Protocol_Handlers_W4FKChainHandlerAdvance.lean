import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_FinalityComparison
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_StoreFinalityUpgrade
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_HMaxMonotone
import Proofs.Vocabulary.Protocol.Handlers.Invariants
import Proofs.Vocabulary.Protocol.Handlers.Invariants2
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Assumptions_Weight
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Admissible
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Run
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Model.Conditions.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Record.Wiring

/-!
# Finality and the block handler

The block handler either moves the store's finalized block to a descendant of the block's own
finalized checkpoint or leaves the store unchanged, and it keeps every held body's finalized
checkpoint an ancestor of the store's finalized block, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Protocol (ChainState HeightConfig derive_named named_transition)

/-- For every path `W` of `rho`, if the run blocks read along `W` expose no slashable weight and are
    free of root collisions, `st` is coherent with a body at its highest height and carries named
    provenance, `B` and every body of `st` are run blocks read along `W`, and `B`'s parent is held,
    then `B`'s finalized checkpoint is an ancestor of the finalized block the handler leaves, or the
    handler leaves the store unchanged. -/
theorem Vocabulary.Proofs.HealingSurface.onBlockUsing_candidateFinality_preceq (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hsb : Restated.Vocabulary.Execution.SlashableBound M S rho W) (hcf : Restated.Vocabulary.Execution.RootCollisionFree M S rho W)
    {st : M.NS} {B : NamedBlock V}
    (hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg st)
    (hmax : ∃ D ∈ st.bodies, (M.derive_named S.E S.cfg D).h = st.core.h_max)
    (hprov : Restated.Vocabulary.Proofs.Bridges.NamedProvenance M S st)
    (hBrun : Restated.Vocabulary.Execution.RunBlock M S rho W B)
    (hRun : ∀ D ∈ st.bodies, Restated.Vocabulary.Execution.RunBlock M S rho W D)
    (hparent : B.parent ∈ st.bodies) (hn : M.reachedStore st := by trivial) :
    Block.Preceq (M.derive_named S.E S.cfg B).F
        (M.on_block_using S.E st.core B.erase
          (fun ps => M.named_transition S.E S.cfg ps B)).F ∨
      M.on_block_using S.E st.core B.erase
        (fun ps => M.named_transition S.E S.cfg ps B) = st.core := by
  by_cases h1 : st.core.s < B.erase.slot ∨ B.erase ∈ st.core.T ∨
      B.erase.parent ∉ st.core.T
  · exact Or.inr (facts.hd.on_block_using_of_rejected _ _ _ _ (Or.inl h1))
  by_cases h2 : (!Block.preceq st.core.F B.erase) = true
  · exact Or.inr (facts.hd.on_block_using_of_rejected _ _ _ _ (Or.inr (Or.inl h2)))
  by_cases h3 : B.erase.proposer? ≠ some (S.E.proposer B.erase.slot)
  · exact Or.inr
      (facts.hd.on_block_using_of_rejected _ _ _ _ (Or.inr (Or.inr (Or.inl h3))))
  by_cases h4 : ¬ (B.erase.parent.slot < B.erase.slot)
  · exact Or.inr
      (facts.hd.on_block_using_of_rejected _ _ _ _ (Or.inr (Or.inr (Or.inr h4))))
  rcases facts.hd.raw_eq_or_accepted S.E st.core B.erase
      (fun ps => M.named_transition S.E S.cfg ps B) with hraw |
    ⟨unpacked, huT, huF, huJ, huHj, huMax, huσ, hkeep, -, -, hhandler⟩
  · exact Or.inr hraw
  left
  have hslotLt : B.erase.parent.slot < B.erase.slot := not_not.mp h4
  have hBne : B ≠ NamedBlock.genesis := by
    intro hg
    subst hg
    rw [Proofs.ModelProperties.erase_genesis, Proofs.ModelProperties.parent_genesis] at hslotLt
    exact lt_irrefl _ hslotLt
  set sigma : M.CS := M.derive_named S.E S.cfg B with hsigmaDef
  have hparentSigma : st.core.σ B.erase.parent = M.derive_named S.E S.cfg B.parent := by
    rw [Proofs.NamedWire.erase_parent]
    exact hcoh.2.2.2.2 B.parent hparent
  have hsigmaAt : unpacked.σ B.erase = sigma := by
    rw [huσ]
    show (if B.erase = B.erase then
      M.named_transition S.E S.cfg (st.core.σ B.erase.parent) B
      else st.core.σ B.erase) = sigma
    rw [if_pos rfl, hparentSigma, hsigmaDef]
    exact (facts.csAdded.derive_named_of_not_genesis S.E S.cfg B hBne).symm
  rw [hhandler, hsigmaAt]
  have hchainFJ : Block.preceq sigma.F sigma.J = true :=
    facts.csAdded.derive_named_finalized_preceq_justified S.E S.cfg B
  have hFB : Block.Preceq st.core.F B.erase := by
    refine Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp ?_
    cases hb : Block.preceq st.core.F B.erase
    · exact absurd (by rw [hb]; rfl) h2
    · rfl
  have hparentT : B.erase.parent ∈ st.core.T := by
    by_contra hn
    exact h1 (Or.inr (Or.inr hn))
  have hchain := facts.cs.chainOrder_derive_named S.E S.cfg B
  have hcandB : Block.Preceq sigma.F B.erase :=
    (facts.cs.derive_named_anchors_preceq S.E S.cfg B).1
  have hmono : Block.Preceq st.core.F
      (M.update_finality unpacked sigma).F := by
    have h := facts.hd.update_finality_F unpacked sigma
    rw [huF] at h
    exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp h
  rcases Proofs.ModelProperties.Preceq_linear hcandB hFB with hcandF | hFcand
  · exact Proofs.ModelProperties.Preceq_trans hcandF hmono
  by_cases hEq : st.core.F = sigma.F
  · exact Proofs.ModelProperties.Preceq_trans
      (by rw [hEq]; exact Proofs.ModelProperties.Preceq_self _) hmono
  have hprec : Block.prec st.core.F sigma.F = true :=
    Proofs.ModelProperties.prec_eq_true_of_ne_of_Preceq hEq hFcand
  have hFJsigma : Block.Preceq unpacked.F sigma.J := by
    rw [huF]
    exact Proofs.ModelProperties.Preceq_trans hFcand
      (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp hchainFJ)
  have hc2 : Block.preceq sigma.F
      (if Block.preceq unpacked.F sigma.J && decide (Protocol.HeightId.mk unpacked.h_j
          unpacked.J.root < Protocol.HeightId.mk sigma.h_j sigma.J.root)
        then sigma.J else unpacked.J) = true := by
    by_cases hmerge : (Block.preceq unpacked.F sigma.J &&
        decide (Protocol.HeightId.mk unpacked.h_j unpacked.J.root <
          Protocol.HeightId.mk sigma.h_j sigma.J.root)) = true
    · rw [if_pos hmerge]
      exact hchainFJ
    · rw [if_neg hmerge, huJ]
      refine Restated.Vocabulary.Proofs.StoreFinality.upgrade_of_height_le facts hW hsb hcf hBrun hRun hprov
        ⟨rfl, rfl⟩ ?_
      have hlex : ¬ (Protocol.HeightId.mk unpacked.h_j unpacked.J.root <
          Protocol.HeightId.mk sigma.h_j sigma.J.root) := by
        intro hlt
        exact hmerge (by
          rw [Bool.and_eq_true]
          exact ⟨Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hFJsigma, decide_eq_true hlt⟩)
      have hle : sigma.h_j ≤ unpacked.h_j :=
        heightId_height_le_of_le (not_lt.mp hlex)
      rw [huHj] at hle
      exact le_trans hchain.heights_ordered hle
  have hmemT : sigma.F ∈ unpacked.T := by
    rw [huT]
    have hcases : ∀ {A C : Block V}, Block.Preceq A C → A = C ∨ Block.Preceq A C.parent := by
      intro A C h
      cases C with
      | genesis =>
          left
          simpa only [Block.Preceq, Block.preceq, decide_eq_true_eq] using h
      | node p s r gv sv ats i =>
          simp only [Block.Preceq, Block.preceq, Bool.or_eq_true,
            decide_eq_true_eq] at h
          rcases h with rfl | hp
          · exact Or.inl rfl
          · exact Or.inr (by simpa only [Block.Preceq, Block.parent] using hp)
    have hclosed : ∀ C ∈ st.core.T, C.parent? = none ∨ C.parent ∈ st.core.T := by
      intro C hC
      rw [hcoh.1] at hC ⊢
      obtain ⟨N, hN, rfl⟩ := Finset.mem_image.mp hC
      right
      rw [Proofs.NamedWire.erase_parent]
      exact Finset.mem_image_of_mem NamedBlock.erase (hcoh.2.2.1.2 N hN)
    rcases hcases hcandB with heq | hpar
    · rw [heq]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Proofs.Records.mem_of_preceq hclosed _ _ hparentT
          (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hpar))
  have hviable : sigma.F ∈ M.viable_tree unpacked.σ unpacked.F
      (max unpacked.h_max sigma.h) unpacked.T := by
    rw [facts.fc.mem_viable_tree_iff]
    refine ⟨⟨hmemT, by rw [huF]; exact hFcand⟩, ?_⟩
    by_cases hhigh : sigma.h < st.core.h_max
    · obtain ⟨D, hDb, hDh⟩ := hmax
      have hDrun := hRun D hDb
      have hDne : D.erase ≠ B.erase := by
        intro hDB
        have hDeq : D = B :=
          Restated.Vocabulary.Execution.NamedRootCollisionFree.root_injective hcf D B hDrun hBrun D B
            (Or.inl (Proofs.NamedAncestry.named_self D))
            (Or.inr (Proofs.NamedAncestry.named_self B))
            (by rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root B, hDB])
        rw [hDeq] at hDh
        exact absurd hDh (Nat.ne_of_lt hhigh)
      have hheightLt : (M.derive_named S.E S.cfg B).h_F <
          (M.derive_named S.E S.cfg D).h := by
        rw [hDh]
        exact lt_trans (lt_of_le_of_lt hchain.heights_ordered hchain.justified_below_height)
          hhigh
      have hFD : Block.Preceq sigma.F D.erase :=
        Restated.Vocabulary.Proofs.NamedFinalizationBridge.finalized_preceq_of_height_lt facts S rho W hW D B hsb hcf
          hDrun hBrun hheightLt
      refine ⟨D.erase, ?_, hFD, ?_⟩
      · rw [huT]
        refine Finset.mem_insert_of_mem ?_
        rw [hcoh.1]
        exact Finset.mem_image_of_mem NamedBlock.erase hDb
      · have hsigmaD : unpacked.σ D.erase = M.derive_named S.E S.cfg D := by
          rw [huσ]
          show (if D.erase = B.erase then
            M.named_transition S.E S.cfg (st.core.σ B.erase.parent) B
            else st.core.σ D.erase) = M.derive_named S.E S.cfg D
          rw [if_neg hDne]
          exact hcoh.2.2.2.2 D hDb
        rw [hsigmaD, hDh, huMax, max_eq_left (le_of_lt hhigh)]
        exact Nat.sub_le _ _
    · refine ⟨B.erase, ?_, hcandB, ?_⟩
      · rw [huT]; exact Finset.mem_insert_self _ _
      · rw [hsigmaAt, huMax, max_eq_right (Nat.le_of_not_lt hhigh)]
        exact Nat.sub_le _ _
  rw [facts.hd.update_finality_F_of_conditions unpacked sigma
    (by
      rw [← hsigmaAt]
      exact facts.hd.chainStateInTree_of_derived S.E S.cfg st B unpacked hcoh.2.2.2.2 hcoh.1 hparent
        hkeep (by
          rw [huσ]
          show (if B.erase = B.erase then
            M.named_transition S.E S.cfg (st.core.σ B.erase.parent) B
            else st.core.σ B.erase) = _
          exact if_pos rfl) hn)
    (by rw [huF]; exact hprec) hc2 hviable]
  exact Proofs.ModelProperties.Preceq_self _

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Protocol (ChainState HeightConfig derive_named named_transition)

/-- For every path `W` of `rho` along which the run blocks expose no slashable weight and are free
    of root collisions, if `st` is coherent with a body at its highest height and carries named
    provenance, its bodies and `B` (once held) are run blocks read along `W`, and every held body's
    finalized checkpoint is an ancestor of `st`'s finalized block, then the same holds after the
    block core processes `B`. -/
theorem Vocabulary.Proofs.HealingSurface.processBlockCore_advance (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hsb : Restated.Vocabulary.Execution.SlashableBound M S rho W) (hcf : Restated.Vocabulary.Execution.RootCollisionFree M S rho W)
    {st : M.NS} {B : NamedBlock V}
    (hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg st)
    (hmax : ∃ D ∈ st.bodies, (M.derive_named S.E S.cfg D).h = st.core.h_max)
    (hprov : Restated.Vocabulary.Proofs.Bridges.NamedProvenance M S st)
    (hBrun : B ∈ (M.ns_process_block_core S.E S.hc S.cfg st B).bodies →
      Restated.Vocabulary.Execution.RunBlock M S rho W B)
    (hRun : ∀ D ∈ st.bodies, Restated.Vocabulary.Execution.RunBlock M S rho W D)
    (hinv : ∀ D ∈ st.bodies,
      Block.Preceq (M.derive_named S.E S.cfg D).F st.core.F) (hn : M.reachedStore st := by trivial) :
    ∀ D ∈ (M.ns_process_block_core S.E S.hc S.cfg st B).bodies,
      Block.Preceq (M.derive_named S.E S.cfg D).F
        (M.ns_process_block_core S.E S.hc S.cfg st B).core.F := by
  have hmonoStore :=
    facts.hd.process_block_core_F S.E S.hc S.cfg st B
  by_cases hp : B.parent ∈ st.bodies
  · set after : M.S := M.on_block_checked_using
      (fun current => M.on_block_using S.E current B.erase
        (fun ps => M.named_transition S.E S.cfg ps B)) S.hc st.core B.erase
        with hafterDef
    have hsame : M.sameCore (M.ns_process_block_core S.E S.hc S.cfg st B).core
        (M.commitBlock st after B).core :=
      facts.hd.process_block_core_of_parent_mem S.E S.hc S.cfg hp
    have hbodies : (M.ns_process_block_core S.E S.hc S.cfg st B).bodies =
        (M.commitBlock st (M.ns_process_block_core S.E S.hc S.cfg st B).core B).bodies :=
      facts.hd.process_block_core_bodies_eq_commit S.E S.hc S.cfg hp
    have hcoreEq : (M.commitBlock st after B).core = after :=
      facts.hd.commit_core st after B
        (facts.hd.on_block_checked_using_store_part S.E S.hc S.cfg st B)
    have hTeq : (M.ns_process_block_core S.E S.hc S.cfg st B).core.T = after.T :=
      (facts.hd.sameCore_T hsame).trans (congrArg _ hcoreEq)
    have hFeq : (M.ns_process_block_core S.E S.hc S.cfg st B).core.F = after.F :=
      (facts.hd.sameCore_F hsame).trans (congrArg _ hcoreEq)
    have hmono : Block.Preceq st.core.F after.F := by
      rw [← hFeq]
      exact hmonoStore
    have hnewF : ∀ hgrow : B.erase ∉ st.core.T ∧ B.erase ∈ after.T,
        Block.Preceq (M.derive_named S.E S.cfg B).F after.F := by
      intro hgrow
      obtain ⟨hfresh, hpost⟩ := hgrow
      have hBmem : B ∈
          (M.ns_process_block_core S.E S.hc S.cfg st B).bodies := by
        rw [hbodies]
        exact facts.hd.mem_commitBlock_bodies_of_fresh S.E S.hc S.cfg rfl
          ⟨hfresh, by rw [hTeq]; exact hpost⟩
      by_cases hadm : M.carried_attestations_admissible S.hc B.erase = true
      · have hafter : after = M.on_block_using S.E st.core B.erase
            (fun ps => M.named_transition S.E S.cfg ps B) := by
          rw [hafterDef]
          exact facts.hd.on_block_checked_using_of_admissible _ S.hc st.core hadm
        rcases Restated.Vocabulary.Proofs.HealingSurface.onBlockUsing_candidateFinality_preceq facts S hW hsb hcf hcoh hmax hprov
          (hBrun hBmem) hRun hp hn with hgood | hnoop
        · rw [hafter]; exact hgood
        · exact absurd (by rw [hafter, hnoop] at hpost; exact hpost) hfresh
      · have hafter : after = st.core := by
          rw [hafterDef]
          exact facts.hd.on_block_checked_using_of_not_admissible _ S.hc st.core hadm
        exact absurd (by rw [hafter] at hpost; exact hpost) hfresh
    rw [hbodies, hFeq]
    intro D hD
    have hheld : B ∈ (M.commitBlock st (M.ns_process_block_core S.E S.hc S.cfg st B).core B).bodies →
        B.erase ∈ st.core.T → B ∈ st.bodies := by
      intro hB hT
      rw [hcoh.1, Finset.mem_image] at hT
      obtain ⟨X, hX, hXe⟩ := hT
      have hroot : X.root = B.root := by
        rw [← Proofs.NamedWire.erase_root X, hXe, Proofs.NamedWire.erase_root B]
      have hXB : X = B := hcf.root_injective X B (hRun X hX) (hBrun (by rw [hbodies]; exact hB)) X B
        (Or.inl (Proofs.NamedAncestry.named_self X)) (Or.inr (Proofs.NamedAncestry.named_self B)) hroot
      exact hXB ▸ hX
    rcases facts.hd.mem_commitBlock_bodies S.E S.hc S.cfg rfl hheld hD with ⟨hgrow, rfl⟩ | hDold
    · exact hnewF ⟨hgrow.1, by rw [← hTeq]; exact hgrow.2⟩
    · exact Proofs.ModelProperties.Preceq_trans (hinv D hDold) hmono
  · rw [facts.hd.process_block_core_of_parent_not_mem S.E S.hc S.cfg hp]
    exact hinv

end

end DecoupledConsensusModel.Sts.Restated
