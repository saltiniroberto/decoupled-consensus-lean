import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Record.Wiring

/-!
# The proposal parent and the proposer's read

The parent a proposer selects, compared with the anchor, the SG root and the head walk of the same
node state of the proposer's read, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC in
private theorem returns_map_elim {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol

/-- For every node state `n` of slot `s`'s proposal-duty read, every proposal input `input` computed
    from `n`, every support view `L` of the proposer at `n`'s slot, and every head `H` the grade
    contract of `n`'s cache walks to on `n`'s store with `L` as the votes, the parent field of
    `input` is `H`. -/
theorem Vocabulary.Proofs.HealingSurface.proposedParent_eq_get_head_with_anchor (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (s : Slot) :
    ∀ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.proposalDutyRead M S rho s,
    ∀ input : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
        (S.node (S.E.proposer s)) (M.toHealing n.st.core) ⇢ input →
    ∀ L : List (GoldfishVote V),
      M.proposer_support_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
        n.st.core.s ⇢ L →
    ∀ H : Block V,
      M.get_head_with
        (M.gradeContract n.cache)
        S.E S.hc (M.toHealing n.st.core)
        (M.proposer_view
          (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
          n.st.core.s).toFinset
        L.toFinset
        (n.st.core.s - 1) ⇢ H →
    input.parent = H := by
  intro n _ input hinput L hL H hH
  have hL' : M.proposer_support_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s ⇢ L := by
    rw [facts.sto.toHealing_s]; exact hL
  have hH' : M.get_head_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
        (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s).toFinset
      L.toFinset ((M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s - 1) ⇢ H := by
    rw [facts.sto.toHealing_s]; exact hH
  exact facts.dt.with_proposal_input_id_parent (M.gradeContract n.cache) S.E S.hc
    (S.node (S.E.proposer s)) (M.toHealing n.st.core) input hinput L hL' H hH'

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol

/-- For every node state `n` of slot `s`'s proposal-duty read and every anchor `A0` that `n` can
    give at the round of `n`'s slot, `A0` is the FG root of `n`'s store, or the grade-1 block `root`
    of `n`'s frame at that round has active prefix `A` in the filtered block tree and `A0` is `A`. -/
theorem Vocabulary.Proofs.HealingSurface.proposalAnchor_cases (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (s : Slot) : ∀ w₁ ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.proposalDutyRead M S rho s,
    ∀ A0 : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S w₁
        ((M.round_of S.hc w₁.st.core.s)) ⇢ A0 →
    A0 =
        M.get_fg_root
          (M.toHealing w₁.st.core).toFG ∨
      ∃ root A,
        (M.readFrame w₁.cache
          (M.toHealing w₁.st.core)
          ((M.round_of S.hc w₁.st.core.s))).g1 =
          some (some root) ∧
        M.activePrefix
          (M.get_filtered_block_tree
            (M.toHealing w₁.st.core).toFG) root = some A ∧
        A0 = A := by
  intro n _ A0 hA0
  obtain ⟨g, hg, rfl⟩ := returns_map_elim _ _ _ hA0
  obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing n.st.core)
    (M.round_of S.hc n.st.core.s)
    (M.readFrame n.cache (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s)).g1
  rw [facts.nd.ModelProperties_gradeContract_read_anchor n.cache S.E S.hc (M.toHealing n.st.core)
    (M.round_of S.hc n.st.core.s) g hg a ha]
  exact facts.gr.anchor_cases S.E S.hc _ _ _ a ha

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol

/-- For every node state `n` of slot `s`'s proposal-duty read, every SG root `R` the grade contract
    of `n`'s cache reads on `n`'s store at the round of `n`'s slot is an ancestor of, or is, the
    parent field of every proposal input computed from `n`. -/
theorem Vocabulary.Proofs.HealingSurface.sgRootWith_preceq_proposedParent (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (s : Slot) :
    ∀ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.proposalDutyRead M S rho s,
    ∀ R : Block V,
      M.get_sg_root_with
        (M.gradeContract n.cache)
        S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc n.st.core.s) ⇢ R →
    ∀ input : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
        (S.node (S.E.proposer s)) (M.toHealing n.st.core) ⇢ input →
    Block.Preceq R input.parent := by
  intro n hn R hR input hinput
  obtain ⟨L, hL⟩ := facts.fc.proposer_support_view_nonempty
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core)
    (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s).toFinset
    L.toFinset (n.st.core.s - 1)
  rw [Restated.Vocabulary.Proofs.HealingSurface.proposedParent_eq_get_head_with_anchor facts S rho s
    n hn input hinput L hL H hH]
  have hR' : M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ R := by
    rw [Record.Model.HS.s, facts.sto.toHealing_s]; exact hR
  exact Restated.Vocabulary.Proofs.HealingSurface.get_sg_root_with_preceq_get_head_with facts
    (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core) _ _ _ R hR' H hH

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol

/-- For every node state `n` of slot `s`'s proposal-duty read, every anchor `A0` that `n` can give
    at the round of `n`'s slot is an ancestor of, or is, the parent field of every proposal input
    computed from `n`. -/
theorem Vocabulary.Proofs.HealingSurface.proposalAnchor_preceq_proposedParent (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (s : Slot) :
    ∀ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.proposalDutyRead M S rho s,
    ∀ A0 : Block V,
      Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
        (M.round_of S.hc n.st.core.s) ⇢ A0 →
    ∀ input : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
        (S.node (S.E.proposer s)) (M.toHealing n.st.core) ⇢ input →
    Block.Preceq A0 input.parent := by
  intro n hn A0 hA0 input hinput
  obtain ⟨g, hg, rfl⟩ := returns_map_elim _ _ _ hA0
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s)
  have hRg : R = g.anchor :=
    facts.fc.get_sg_root_with_eq_read_anchor _ _ _ _ _ g hg R hR
  rw [← hRg]
  exact Restated.Vocabulary.Proofs.HealingSurface.sgRootWith_preceq_proposedParent facts S rho s
    n hn R hR input hinput

end

end DecoupledConsensusModel.Sts.Restated
