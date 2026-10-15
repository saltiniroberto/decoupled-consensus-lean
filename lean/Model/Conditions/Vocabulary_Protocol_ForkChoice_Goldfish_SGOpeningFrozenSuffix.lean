import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedProposalPivot
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_ProposalSnapshotBridge
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# Inputs of the frozen proposal suffix comparison

The anchor, tree and candidate-score facts at a proposer's read and a voter's read that the frozen
suffix comparison of an SG opening takes, over a model `M : Record.Model V`.
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
open Internal
open Execution
open Protocol

/-- Every anchor the proposer read `n` gives is an ancestor of `pivot`, `pivot` is in the filtered
    tree of the voter read `m`, `P` is in every voter candidate tree of `m`, and `pivot` and `P` are
    compatible with every anchor `m` gives. -/
structure Vocabulary.Proofs.HealingSurface.NamedFrozenProposalSuffixCoreInputs (M : Record.Model V)
    (S : Setup V) (rho : Record.Run V) (s : Slot)
    (pivot : Block V) (v : V) (P : NamedBlock V) (n m : M.N) : Prop where
  sourceAnchor : ∀ A, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
      ((M.round_of S.hc n.st.core.s)) ⇢ A → Block.Preceq A pivot
  pivotTarget : pivot ∈ M.get_filtered_block_tree
    (M.toHealing m.st.core).toFG
  proposalCandidate : ∀ T, M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T →
    P.erase ∈ T
  pivotAnchorCompatible : ∀ A, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S m
      ((M.round_of S.hc m.st.core.s)) ⇢ A → Block.compatible A pivot = true
  proposalAnchorCompatible : ∀ A, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S m
      ((M.round_of S.hc m.st.core.s)) ⇢ A → Block.compatible A P.erase = true

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution
open Protocol

/-- The fields of `NamedFrozenProposalSuffixCoreInputs` at the reads `n` and `m`, and the stores of
    `n` and `m` have the same `h_max`. -/
structure Vocabulary.Proofs.HealingSurface.NamedFrozenProposalSuffixInputs (M : Record.Model V)
    (S : Setup V) (rho : Record.Run V) (s : Slot)
    (pivot : Block V) (v : V) (P : NamedBlock V) (n m : M.N) : Prop
    extends Restated.Vocabulary.Proofs.HealingSurface.NamedFrozenProposalSuffixCoreInputs M S rho s pivot v P n m where
  sameHMax : n.st.core.h_max = m.st.core.h_max

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution
open Protocol

/-- For every block `C` in the filtered trees of the proposer read `n` and of `vs`, and every voter
    view and support view `vs` can give at slot `s`, the tree of `ps` extended by the proposal's
    Goldfish votes and support votes scores `C` as those views do. -/
def Vocabulary.Proofs.HealingSurface.NamedProposalCandidateScoreBridge (M : Record.Model V)
    (S : Setup V) (rho : Record.Run V) (s : Slot) (v : V) (P : NamedBlock V) (n : M.N) (ps vs : M.S) :
    Prop :=
  ∀ C : Block V,
    C ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG →
    C ∈ M.get_filtered_block_tree (M.toHealing vs).toFG →
    ∀ Y, M.voter_view S.E (M.toHealing vs).toFG.toSG.toGoldfishStore s ⇢ Y →
    ∀ Z, M.voter_support_view S.E (M.toHealing vs).toFG.toSG.toGoldfishStore s ⇢ Z →
    Restated.Vocabulary.Protocol.CandidateScorePreservingViewExtension M
      ps.T
      vs.T
      P.erase.gf_votes.toFinset
      P.erase.gf_support_votes.toFinset
      Y Z C

end

end DecoupledConsensusModel.Sts.Restated
