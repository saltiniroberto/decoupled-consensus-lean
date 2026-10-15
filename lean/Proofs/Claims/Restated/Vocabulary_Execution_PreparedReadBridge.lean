import Proofs.Vocabulary.Execution.PreparedReadBridge
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedResult23Statements
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Record.Wiring

/-!
# Anchors, roots and the vote-duty head

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, each read for
every outcome of every call: the vote-duty anchor and the confirmation anchor are the FG root or the
active prefix of a completed grade-1 root, and the SG root, the anchor and the FG root are each an
ancestor of, or the same block as, the in-tree head of the vote duty.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
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

/-- For every prepared read `n` of `v` at slot `s`'s vote time and every anchor `A0` that `n` can
    give at the round of its slot, `A0` is the FG root of `n`'s store, or the round's frame read
    from `n`'s cache has a completed grade-1 root whose active prefix in the store's filtered tree
    is a block `A`, and `A0` is `A`. -/
theorem Vocabulary.Proofs.HealingSurface.voterAnchorAt_cases (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (s : Slot) :
    ∀ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho v s,
    ∀ A0, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ A0 →
    A0 = M.get_fg_root (M.toHealing n.st.core).toFG ∨
      ∃ root A,
        (M.readFrame n.cache
          (M.toHealing n.st.core)
          ((M.round_of S.hc n.st.core.s))).g1 =
          some (some root) ∧
        M.activePrefix
          (M.get_filtered_block_tree
            (M.toHealing n.st.core).toFG) root = some A ∧
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

/-- For every confirmation input read `n` of `v` at slot `s` and every confirmation anchor `A0` that
    `n` can give, `A0` is the FG root of `n`'s store, or the round's frame read from `n`'s cache has
    a completed grade-1 root whose active prefix in the store's filtered tree is a block `A`, and
    `A0` is `A`. -/
theorem Vocabulary.Proofs.HealingSurface.confirmationAnchorAt_cases (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (s : Slot) :
    ∀ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.confirmationInputRead M S rho v s,
    ∀ A0, Restated.Vocabulary.Internal.namedConfirmationAnchor M S n ⇢ A0 →
    A0 = M.get_fg_root (M.toHealing n.st.core).toFG ∨
      ∃ root A,
        (M.readFrame n.cache
          (M.toHealing n.st.core)
          ((M.round_of S.hc n.st.core.s))).g1 =
          some (some root) ∧
        M.activePrefix
          (M.get_filtered_block_tree
            (M.toHealing n.st.core).toFG) root = some A ∧
        A0 = A := by
  intro n _ A0 hA0
  have h := (facts.nd.gradeContract_sgRoot_eq_frameAnchor n.cache S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s) A0).1 hA0
  exact facts.gr.anchor_cases S.E S.hc _ _ _ A0 h

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol

/-- For every prepared read `n` of `v` at slot `s`'s vote time, every SG root `R` under the grade
    contract of `n`'s cache at `n`'s store and the round of its slot is an ancestor of, or the same
    block as, every in-tree head `H` computed from `n` with every outcome of the voter's filtered
    tree and of the two voter views. -/
theorem Vocabulary.Proofs.HealingSurface.sgRootWith_preceq_voterHeadAt (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (s : Slot) :
    ∀ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho v s,
    ∀ R, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        ((M.round_of S.hc n.st.core.s)) ⇢ R →
    ∀ T, M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L, M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L', M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
        n.st.core.s ⇢ L' →
    ∀ H, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        T L L' (n.st.core.s - 1) ⇢ H →
    Block.Preceq R H := by
  intro n _ R hR T _ L _ L' _ H hH
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s)
  rw [facts.fc.get_sg_root_with_eq_read_anchor _ _ _ _ _ G hG R hR]
  have hG' : (M.gradeContract n.cache).read S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s) ⇢ G := by
    rw [facts.sto.toHealing_s]; exact hG
  exact facts.fc.read_anchor_preceq_get_head_in_tree_with_layer _ _ _ _ T L L' _ G hG' H hH

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol

/-- For every prepared read `n` of `v` at slot `s`'s vote time, every anchor `A0` that `n` can give
    at the round of its slot is an ancestor of, or the same block as, every in-tree head `H`
    computed from `n` with every outcome of the voter's filtered tree and of the two voter views. -/
theorem Vocabulary.Proofs.HealingSurface.voterAnchorAt_preceq_voterHeadAt (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (s : Slot) :
    ∀ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho v s,
    ∀ A0, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ A0 →
    ∀ T, M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L, M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L', M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
        n.st.core.s ⇢ L' →
    ∀ H, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        T L L' (n.st.core.s - 1) ⇢ H →
    Block.Preceq A0 H := by
  intro n _ A0 hA0 T _ L _ L' _ H hH
  obtain ⟨g, hg, rfl⟩ := returns_map_elim _ _ _ hA0
  have hg' : (M.gradeContract n.cache).read S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s) ⇢ g := by
    rw [facts.sto.toHealing_s]; exact hg
  exact facts.fc.read_anchor_preceq_get_head_in_tree_with_layer _ _ _ _ T L L' _ g hg' H hH

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol

/-- For every prepared read `n` of `v` at slot `s`'s vote time, the FG root of `n`'s store is an
    ancestor of, or the same block as, every in-tree head `H` computed from `n` with every outcome
    of the voter's filtered tree and of the two voter views. -/
theorem Vocabulary.Proofs.HealingSurface.fgRoot_preceq_voterHeadAt (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (s : Slot) :
    ∀ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho v s,
    ∀ T, M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L, M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L', M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
        n.st.core.s ⇢ L' →
    ∀ H, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        T L L' (n.st.core.s - 1) ⇢ H →
    Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) H := by
  intro n hn T hT L hL L' hL' H hH
  obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing n.st.core)
    (M.round_of S.hc n.st.core.s)
    (M.readFrame n.cache (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s)).g1
  have hR := (facts.nd.gradeContract_sgRoot_eq_frameAnchor n.cache S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s) a).2 ha
  exact Proofs.ModelProperties.Preceq_trans
    (facts.fc.fg_root_Preceq_get_sg_root_with_gradeContract
      n.cache S.E S.hc (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s) a hR)
    (Restated.Vocabulary.Proofs.HealingSurface.sgRootWith_preceq_voterHeadAt facts S rho v s n hn
      a hR T hT L hL L' hL' H hH)

end

end DecoupledConsensusModel.Sts.Restated
