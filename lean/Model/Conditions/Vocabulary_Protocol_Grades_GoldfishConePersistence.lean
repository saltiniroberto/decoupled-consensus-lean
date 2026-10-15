import Proofs.Vocabulary.Protocol.Grades.GoldfishConePersistence
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedResult23Statements
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Record.Wiring

/-!
# Goldfish cone inputs

The conditions on a voter's or a confirmer's read that keep a block in the Goldfish cone, over a
model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open Protocol

/-- At the vote read `n`, `C` is in every voter filtered tree of `n`'s store, `n`'s FG root is an
    ancestor of `C`, every anchor of `n` is compatible with `C`, and every block strictly between
    such an anchor and `C` is in such a tree. -/
structure Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs (M : Record.Model V)
    (S : Setup V) (rho : Record.Run V) (s : Slot) (C : Block V) (w : V) (n : M.N) : Prop where
  candidate : ∀ T, M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T → C ∈ T
  root : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) C
  anchor : ∀ A, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ A →
    Block.compatible A C = true
  path : ∀ A, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ A →
    ∀ T, M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ D : Block V,
    Block.Preceq A D → D ≠ A → Block.Preceq D C → D ≠ C → D ∈ T

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open Protocol

/-- At the confirmation input read `n`, `C` is in `n`'s filtered tree, `n`'s FG root is an ancestor
    of `C`, every confirmation anchor of `n` is compatible with `C`, and every block strictly
    between such an anchor and `C` is in `n`'s filtered tree. -/
structure Vocabulary.Proofs.HealingSurface.GoldfishConeConfirmationInputs (M : Record.Model V)
    (S : Setup V) (rho : Record.Run V) (s : Slot) (C : Block V) (w : V) (n : M.N) : Prop where
  candidate : C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n
  root : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) C
  anchor : ∀ A, Restated.Vocabulary.Internal.namedConfirmationAnchor M S n ⇢ A →
    Block.compatible A C = true
  path : ∀ A, Restated.Vocabulary.Internal.namedConfirmationAnchor M S n ⇢ A →
    ∀ D : Block V,
    Block.Preceq A D → D ≠ A → Block.Preceq D C → D ≠ C →
    D ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open Protocol

/-- At the vote read `n`, for every anchor `A` and voter filtered tree `T` of `n`: either `n`'s FG
    root is an ancestor of `C`, `C ∈ T` and every block strictly between `A` and `C` is in `T`, or
    `C` is an ancestor of that FG root; and every anchor of `n` is compatible with `C`. -/
structure Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs' (M : Record.Model V)
    (S : Setup V) (rho : Record.Run V) (s : Slot) (C : Block V) (w : V) (n : M.N) : Prop where
  rootSide : ∀ A, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ A →
    ∀ T, M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    (Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) C ∧
      C ∈ T ∧
      ∀ D : Block V,
        Block.Preceq A D → D ≠ A → Block.Preceq D C → D ≠ C → D ∈ T) ∨
    Block.Preceq C (M.get_fg_root (M.toHealing n.st.core).toFG)
  anchor : ∀ A, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ A →
    Block.compatible A C = true

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open Protocol

/-- `DecoupledConsensusModel.Proofs.HealingSurface.GoldfishConeVoteInputs` holds exactly when
    `Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs` holds at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs_vocabulary_eq (S : Setup V) (rho : Run V) (s : Slot) (C : Block V) (w : V) :
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.GoldfishConeVoteInputs (V := V) S rho s C w ↔ Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) s C w
      (_root_.DecoupledConsensusModel.Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)) := by
  constructor
  · intro h
    refine ⟨?_, h.root, ?_, ?_⟩
    · intro T hT
      simp only [Record.Model.vocabulary, Record.returns_pure] at hT
      subst hT
      exact h.candidate
    · intro A hA
      rw [Vocabulary.Internal.PhaseGrades.nodeAnchor_vocabulary_eq, Record.returns_pure] at hA
      subst hA
      exact h.anchor
    · intro A hA T hT
      rw [Vocabulary.Internal.PhaseGrades.nodeAnchor_vocabulary_eq, Record.returns_pure] at hA
      simp only [Record.Model.vocabulary, Record.returns_pure] at hT
      subst hA hT
      exact h.path
  · intro h
    exact ⟨h.candidate _ ((Record.returns_pure _ _).2 rfl), h.root,
      h.anchor _
        (by rw [Vocabulary.Internal.PhaseGrades.nodeAnchor_vocabulary_eq, Record.returns_pure]; rfl),
      h.path _
        (by rw [Vocabulary.Internal.PhaseGrades.nodeAnchor_vocabulary_eq, Record.returns_pure]; rfl)
        _ ((Record.returns_pure _ _).2 rfl)⟩

/-- `DecoupledConsensusModel.Proofs.HealingSurface.GoldfishConeConfirmationInputs` holds exactly
    when `Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeConfirmationInputs` holds at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.GoldfishConeConfirmationInputs_vocabulary_eq (S : Setup V) (rho : Run V) (s : Slot) (C : Block V) (w : V) :
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.GoldfishConeConfirmationInputs (V := V) S rho s C w ↔ Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeConfirmationInputs (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) s C w
      (_root_.DecoupledConsensusModel.Internal.NamedRecoveryRead.confirmationInputRead S rho w s) := by
  constructor
  · intro h
    refine ⟨h.candidate, h.root, ?_, ?_⟩
    · intro A hA
      rw [Vocabulary.Internal.namedConfirmationAnchor_vocabulary_eq, Record.returns_pure] at hA
      subst hA
      exact h.anchor
    · intro A hA
      rw [Vocabulary.Internal.namedConfirmationAnchor_vocabulary_eq, Record.returns_pure] at hA
      subst hA
      exact h.path
  · intro h
    exact ⟨h.candidate, h.root,
      h.anchor _
        (by rw [Vocabulary.Internal.namedConfirmationAnchor_vocabulary_eq, Record.returns_pure]),
      h.path _
        (by rw [Vocabulary.Internal.namedConfirmationAnchor_vocabulary_eq, Record.returns_pure])⟩

/-- `DecoupledConsensusModel.Proofs.HealingSurface.GoldfishConeVoteInputs'` holds exactly when
    `Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs'` holds at the model
    `Record.Model.vocabulary`, at `w`'s vote-duty read of slot `s + 1`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs'_vocabulary_eq (S : Setup V) (rho : Run V) (s : Slot) (C : Block V) (w : V) :
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.GoldfishConeVoteInputs' (V := V) S rho s C w ↔ Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs' (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) s C w
      (_root_.DecoupledConsensusModel.Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro A hA T hT
      rw [Vocabulary.Internal.PhaseGrades.nodeAnchor_vocabulary_eq, Record.returns_pure] at hA
      simp only [Record.Model.vocabulary, Record.returns_pure] at hT
      subst hA hT
      exact h.rootSide
    · intro A hA
      rw [Vocabulary.Internal.PhaseGrades.nodeAnchor_vocabulary_eq, Record.returns_pure] at hA
      subst hA
      exact h.anchor
  · intro h
    exact ⟨h.rootSide _
        (by rw [Vocabulary.Internal.PhaseGrades.nodeAnchor_vocabulary_eq, Record.returns_pure]; rfl)
        _ ((Record.returns_pure _ _).2 rfl),
      h.anchor _
        (by rw [Vocabulary.Internal.PhaseGrades.nodeAnchor_vocabulary_eq, Record.returns_pure]; rfl)⟩

end

end DecoupledConsensusModel.Sts.Restated
