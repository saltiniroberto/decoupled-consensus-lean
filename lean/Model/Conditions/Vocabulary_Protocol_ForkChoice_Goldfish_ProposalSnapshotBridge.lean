import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalSnapshotBridge
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Candidate score preserving view extension

The condition that moving between two voter views preserves the score of a candidate block, over a
model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution

/-- Moving between the source and target views, in both directions, preserves participation,
    equivocation and the support votes that target `C`. -/
structure Vocabulary.Protocol.CandidateScorePreservingViewExtension (M : Record.Model V)
    (sourceTree targetTree : Finset (Block V))
    (sourceRaw sourceSupport targetRaw targetSupport :
      Finset (GoldfishVote V)) (C : Block V) : Prop where
  raw_subset : sourceRaw ⊆ targetRaw
  raw_extra_equiv : ∀ u ∈ targetRaw, u ∉ sourceRaw →
    M.equivocates sourceRaw u.val_index = true
  forward : ∀ u ∈ sourceSupport, ∀ b : Bool, M.targets_under sourceTree C u ⇢ b →
    b = true →
      (u ∈ targetSupport ∧
        ∀ b' : Bool, M.targets_under targetTree C u ⇢ b' → b' = true) ∨
      M.equivocates targetRaw u.val_index = true
  backward : ∀ u ∈ targetSupport, ∀ b : Bool, M.targets_under targetTree C u ⇢ b →
    b = true →
      (u ∈ sourceSupport ∧
        ∀ b' : Bool, M.targets_under sourceTree C u ⇢ b' → b' = true) ∨
      M.equivocates sourceRaw u.val_index = true

end

end DecoupledConsensusModel.Sts.Restated
