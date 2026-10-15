import Proofs.Vocabulary.Internal.Definitions.NamedLifecycle
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedProposalPivot
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Record.Wiring

/-!
# Grade, candidate tree and anchor reads of a run

The G1 grade at a reader's read, a voter's candidate trees and anchors at its vote duty read, and
the facts on the confirmation input read and the frozen vote at a round's opening, stated over a
model `M : Record.Model V`, and their counterparts at `Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
  DecoupledConsensusModel.Internal.PhaseGrades
  DecoupledConsensusModel.Internal.NamedRecoveryRead DecoupledConsensusModel.Protocol

/-- For every node state `n` that `w` can hold before round `r`'s G1 instant, every outcome of the
    phase grade of `n`'s store for `B` at round `r` and grade G1 is `true`. -/
def Vocabulary.Proofs.HealingSurface.namedG1At (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (w : V) (r : Round) (B : Block V) : Prop :=
  ∀ n ∈ Restated.Vocabulary.Internal.PhaseGrades.readAt M S rho (M.domain S.E S.hc r .g1) w,
    ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc n.st r .g1 B ⇢ b →
      b = true

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
  DecoupledConsensusModel.Internal.PhaseGrades
  DecoupledConsensusModel.Internal.NamedRecoveryRead DecoupledConsensusModel.Protocol

/-- The set of trees `T` such that, for some vote duty read `n` of `v` at slot `k`, `T` is an
    outcome of the voter's filtered block tree of `n`'s store at its slot. -/
def Vocabulary.Proofs.HealingSurface.voterCandidateTreeAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (v : V) (k : Slot) :
    DC.NDR (Finset (Block V)) :=
  {T | ∃ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho v k,
    M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T}

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
  DecoupledConsensusModel.Internal.PhaseGrades
  DecoupledConsensusModel.Internal.NamedRecoveryRead DecoupledConsensusModel.Protocol

/-- The set of blocks `a` such that, for some vote duty read `n` of `v` at slot `k`, `a` is an
    outcome of the anchor of `n` at the round of `n`'s slot. -/
def Vocabulary.Proofs.HealingSurface.voterAnchorAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (v : V) (k : Slot) :
    DC.NDR (Block V) :=
  {a | ∃ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho v k,
    Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ a}

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
  DecoupledConsensusModel.Internal.PhaseGrades
  DecoupledConsensusModel.Internal.NamedRecoveryRead DecoupledConsensusModel.Protocol

/-- Facts on every confirmation input read of `v` at slot `s` that place `P`'s block relative to the
    read's FG root, its SG root and its filtered tree. -/
structure Vocabulary.Proofs.HealingSurface.NamedSGOpeningConfirmationRead (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (s : Slot) (v : V)
    (P : NamedBlock V) : Prop where
  root : ∀ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.confirmationInputRead M S rho v s,
    Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) P.erase
  anchor : ∀ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.confirmationInputRead M S rho v s,
    ∀ a : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc n.st.core.s) ⇢ a →
      Block.Preceq a P.erase
  candidate : ∀ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.confirmationInputRead M S rho v s,
    P.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
  DecoupledConsensusModel.Internal.PhaseGrades
  DecoupledConsensusModel.Internal.NamedRecoveryRead DecoupledConsensusModel.Protocol

/-- Facts on the voter read `m` at slot `s + 1`'s vote instant and the proposer read `n` of slot
    `s + 1`: `P`'s block and `A` in the voter's candidate trees, the voter's anchors compatible with
    both, the pivot transfer between `n` and `m`, and the Goldfish votes `P`'s block does not
    include sent by equivocators. -/
structure Vocabulary.Proofs.HealingSurface.NamedSGOpeningFrozenVoteAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (s : Slot) (A : Block V)
    (v : V) (P : NamedBlock V) (n m : M.N) : Prop where
  proposalCandidate : ∀ T : Finset (Block V),
    M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T → P.erase ∈ T
  pivotCandidate : ∀ T : Finset (Block V),
    M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T → A ∈ T.erase P.erase
  pivotAnchorCompatible : ∀ a : Block V,
    Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S m (M.round_of S.hc m.st.core.s) ⇢ a →
    Block.compatible a A = true
  proposalAnchorCompatible : ∀ a : Block V,
    Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S m (M.round_of S.hc m.st.core.s) ⇢ a →
    Block.compatible a P.erase = true
  pivotPath : ∀ a : Block V,
    Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S m (M.round_of S.hc m.st.core.s) ⇢ a →
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T →
    Block.Preceq a A →
    ∀ C : Block V, Block.Preceq a C → C ≠ a → Block.Preceq C A → C ∈ T.erase P.erase
  suffix : Restated.Vocabulary.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer M S rho (s + 1) A v P n m
  rawExtra : ∀ vv : Finset (GoldfishVote V),
    M.voter_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore (s + 1) ⇢ vv →
    ∀ u, u ∈ vv →
    u ∉ P.erase.gf_votes.toFinset →
    M.equivocates P.erase.gf_votes.toFinset u.val_index = true

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
  DecoupledConsensusModel.Internal.PhaseGrades
  DecoupledConsensusModel.Internal.NamedRecoveryRead DecoupledConsensusModel.Protocol

/-- At `Record.Model.vocabulary` and a run embedded by `Record.Run.ofVocabulary`, the restated
    `namedG1At` holds exactly when `DecoupledConsensusModel.Proofs.HealingSurface.namedG1At` does. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.namedG1At_vocabulary_eq (S : Setup V) (rho : Run V) (w : V) (r : Round) (B : Block V) :
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.namedG1At (V := V) S rho w r B ↔ Restated.Vocabulary.Proofs.HealingSurface.namedG1At (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) w r B := by
  simp only [Restated.Vocabulary.Proofs.HealingSurface.namedG1At,
    Vocabulary.Internal.PhaseGrades.readAt_vocabulary_eq,
    Vocabulary.Internal.PhaseGrades.storeGrade_vocabulary_eq, Record.returns_pure]
  exact ⟨fun h n hn b hb => by obtain rfl := hn; obtain rfl := hb; exact h,
    fun h => h _ rfl _ rfl⟩

/-- At `Record.Model.vocabulary` and a run embedded by `Record.Run.ofVocabulary`, the restated
    `voterCandidateTreeAt` is the singleton of the value of
    `DecoupledConsensusModel.Proofs.HealingSurface.voterCandidateTreeAt`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.voterCandidateTreeAt_vocabulary_eq (S : Setup V) (rho : Run V) (v : V) (k : Slot) :
    Restated.Vocabulary.Proofs.HealingSurface.voterCandidateTreeAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) v k =
      {_root_.DecoupledConsensusModel.Proofs.HealingSurface.voterCandidateTreeAt (V := V) S rho v k} := by
  ext T
  rw [Restated.Vocabulary.Proofs.HealingSurface.voterCandidateTreeAt,
    Vocabulary.Internal.NamedRecoveryRead.voteDutyRead_vocabulary_eq]
  constructor
  · rintro ⟨n, hn, hT⟩
    obtain rfl := Set.mem_singleton_iff.mp hn
    obtain rfl := (Record.returns_pure _ _).1 hT
    exact Set.mem_singleton _
  · intro h
    obtain rfl := Set.mem_singleton_iff.mp h
    exact ⟨_, Set.mem_singleton _, (Record.returns_pure _ _).2 rfl⟩

/-- At `Record.Model.vocabulary` and a run embedded by `Record.Run.ofVocabulary`, the restated
    `voterAnchorAt` is the singleton of the value of
    `DecoupledConsensusModel.Proofs.HealingSurface.voterAnchorAt`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.voterAnchorAt_vocabulary_eq (S : Setup V) (rho : Run V) (v : V) (k : Slot) :
    Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) v k =
      {_root_.DecoupledConsensusModel.Proofs.HealingSurface.voterAnchorAt (V := V) S rho v k} := by
  ext a
  rw [Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt,
    Vocabulary.Internal.NamedRecoveryRead.voteDutyRead_vocabulary_eq]
  constructor
  · rintro ⟨n, hn, ha⟩
    obtain rfl := Set.mem_singleton_iff.mp hn
    rw [Vocabulary.Internal.PhaseGrades.nodeAnchor_vocabulary_eq, Record.returns_pure] at ha
    exact Set.mem_singleton_iff.mpr ha
  · intro h
    obtain rfl := Set.mem_singleton_iff.mp h
    refine ⟨_, Set.mem_singleton _, ?_⟩
    rw [Vocabulary.Internal.PhaseGrades.nodeAnchor_vocabulary_eq, Record.returns_pure]
    rfl

/-- At `Record.Model.vocabulary` and a run embedded by `Record.Run.ofVocabulary`, the restated
    `NamedSGOpeningConfirmationRead` holds exactly when
    `DecoupledConsensusModel.Proofs.HealingSurface.NamedSGOpeningConfirmationRead` does. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.NamedSGOpeningConfirmationRead_vocabulary_eq (S : Setup V) (rho : Run V) (s : Slot) (v : V) (P : NamedBlock V) :
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.NamedSGOpeningConfirmationRead (V := V) S rho s v P ↔ Restated.Vocabulary.Proofs.HealingSurface.NamedSGOpeningConfirmationRead (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) s v P := by
  constructor
  · intro h
    refine ⟨fun n hn => ?_, fun n hn => ?_, fun n hn => ?_⟩ <;>
      (rw [Vocabulary.Internal.NamedRecoveryRead.confirmationInputRead_vocabulary_eq] at hn
       obtain rfl := Set.mem_singleton_iff.mp hn)
    · exact h.root
    · intro a ha
      obtain rfl := (Record.returns_pure _ _).1 ha
      exact h.anchor
    · exact h.candidate
  · intro h
    have hn : _root_.DecoupledConsensusModel.Internal.NamedRecoveryRead.confirmationInputRead S rho v s ∈
        Restated.Vocabulary.Internal.NamedRecoveryRead.confirmationInputRead (V := V) Record.Model.vocabulary
          S (Record.Run.ofVocabulary rho) v s := by
      rw [Vocabulary.Internal.NamedRecoveryRead.confirmationInputRead_vocabulary_eq]; rfl
    exact ⟨h.root _ hn, h.anchor _ hn _ ((Record.returns_pure _ _).2 rfl), h.candidate _ hn⟩

/-- At `Record.Model.vocabulary`,
    `DecoupledConsensusModel.Proofs.HealingSurface.NamedSGOpeningFrozenVoteAt` holds exactly when
    the restated `NamedSGOpeningFrozenVoteAt` holds at the one proposer read of slot `s + 1` and the
    one read of `v` at slot `s + 1`'s vote instant. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.NamedSGOpeningFrozenVoteAt_vocabulary_eq (S : Setup V) (rho : Run V) (s : Slot) (A : Block V) (v : V) (P : NamedBlock V) :
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.NamedSGOpeningFrozenVoteAt (V := V) S rho s A v P ↔
      Restated.Vocabulary.Proofs.HealingSurface.NamedSGOpeningFrozenVoteAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) s A v P
        (_root_.DecoupledConsensusModel.Internal.NamedRecoveryRead.proposalDutyRead S rho (s + 1))
        (_root_.DecoupledConsensusModel.Internal.NamedRecoveryRead.voteDutyRead S rho v (s + 1)) := by
  have hanc : ∀ (n : NamedNodeState V) (a : Block V),
      Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor (V := V) Record.Model.vocabulary S n
        ((Record.Model.vocabulary (V := V)).round_of S.hc n.st.core.s) ⇢ a ↔
      a = _root_.DecoupledConsensusModel.Internal.PhaseGrades.nodeAnchor (V := V) S n
        (S.hc.round_of n.st.core.s) := fun n a => by
    rw [Vocabulary.Internal.PhaseGrades.nodeAnchor_vocabulary_eq, Record.returns_pure]; rfl
  have hsuf := Vocabulary.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer_vocabulary_eq S rho
    (s + 1) A v P
  constructor
  · intro h
    refine ⟨fun T hT => ?_, fun T hT => ?_, fun a ha => ?_, fun a ha => ?_,
      fun a ha T hT h1 C h2 h3 h4 => ?_, hsuf.1 h.suffix, fun vv hvv u hu h1 => ?_⟩
    · obtain rfl := (Record.returns_pure _ _).1 hT; exact h.proposalCandidate
    · obtain rfl := (Record.returns_pure _ _).1 hT; exact h.pivotCandidate
    · obtain rfl := (hanc _ _).1 ha; exact h.pivotAnchorCompatible
    · obtain rfl := (hanc _ _).1 ha; exact h.proposalAnchorCompatible
    · obtain rfl := (hanc _ _).1 ha
      obtain rfl := (Record.returns_pure _ _).1 hT
      exact h.pivotPath h1 C h2 h3 h4
    · obtain rfl := (Record.returns_pure _ _).1 hvv; exact h.rawExtra u hu h1
  · intro h
    exact ⟨h.proposalCandidate _ ((Record.returns_pure _ _).2 rfl),
      h.pivotCandidate _ ((Record.returns_pure _ _).2 rfl),
      h.pivotAnchorCompatible _ ((hanc _ _).2 rfl),
      h.proposalAnchorCompatible _ ((hanc _ _).2 rfl),
      h.pivotPath _ ((hanc _ _).2 rfl) _ ((Record.returns_pure _ _).2 rfl),
      hsuf.2 h.suffix,
      h.rawExtra _ ((Record.returns_pure _ _).2 rfl)⟩

end

end DecoupledConsensusModel.Sts.Restated
