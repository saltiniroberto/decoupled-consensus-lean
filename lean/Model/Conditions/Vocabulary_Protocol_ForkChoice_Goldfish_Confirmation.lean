import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Confirmation
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Confirmation numerator and cross-view facts

The shape of the confirmation numerator, and what one node's confirmation count needs of another
node's view, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol
open Internal
open DecoupledConsensusModel.Execution

/-- `votes` is the early set filtered by the late set holding no second vote by the same validator,
    with `early ⊆ late`. -/
structure Vocabulary.Protocol.Numerator (M : Record.Model V) (early late votes : Finset (GoldfishVote V)) : Prop where
  /-- The early votes are among the late votes. -/
  early_late : early ⊆ late
  /-- `votes` are the early votes whose validator has no second vote in the late set. -/
  filtered : votes = early.filter (fun u => M.no_second_vote_in late u = true)

end

section
open DecoupledConsensusModel.Protocol
open Internal
open DecoupledConsensusModel.Execution

/-- What one node's confirmation count, from `votesv` and the tree `Tv`, needs of another node's
    late view `latew` and tree `Tw`. -/
structure Vocabulary.Protocol.CrossView (M : Record.Model V) (Tv Tw : Finset (Block V)) (votesv latew : Finset (GoldfishVote V)) :
    Prop where
  /-- A counted vote reaches the other late view, or that view already holds an
  equivocation by the vote's validator. -/
  transfer : ∀ u ∈ votesv,
    u ∈ latew ∨ M.equivocates latew u.val_index = true
  /-- The two trees agree whenever both resolve a counted vote's target. -/
  resolve : ∀ u ∈ votesv, ∀ B C : Block V,
    Block.find? Tv u.head = some B → Block.find? Tw u.head = some C → B = C

end

end DecoupledConsensusModel.Sts.Restated
