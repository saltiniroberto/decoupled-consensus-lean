import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Adoption
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_ModelVocabulary_Goldfish_ForkChoice
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Adoption
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Confirmation
import Model.Record.Wiring

/-!
# The Goldfish fork choice captures a confirmed block

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: under the score
and transport conditions of a confirmation of `B`, every outcome of the Goldfish fork choice from an
anchor `A` compatible with `B` is a descendant of `B` or `B` itself.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Protocol
open Internal
open Protocol (ChainState)

/-- If the source votes are the numerator of `sourceEarly` and `sourceLate`, the transport from
    source to target holds for `B`, for every outcome `g` of `B`'s Goldfish score at the source the
    count of source late voters is less than `2 * g`, the target support is among the target votes,
    `A` and `B` are compatible, and every block strictly between `A` and `B` is in `tree` when `A`
    is an ancestor of `B`, then `B` is an ancestor of, or the same block as, every outcome `X` of
    the Goldfish fork choice from `A` at the target. -/
theorem Vocabulary.Protocol.goldfish_fork_choice_captures_of_confirmation (facts : Record.Facts M)
    (E : Env V) (σ : Block V → M.CS) (h_max : Height)
    (sourceTree targetTree tree : Finset (Block V)) (cur : Slot)
    (sourceEarly sourceLate sourceVotes targetVotes targetSupport :
      Finset (GoldfishVote V)) (s : Slot) {A B : Block V}
    (hN : Restated.Vocabulary.Protocol.Numerator M sourceEarly sourceLate sourceVotes)
    (hT : Restated.Vocabulary.Protocol.AdoptionTransport M sourceTree targetTree sourceVotes sourceLate
      targetVotes targetSupport B)
    (heligible : ∀ g : ℕ, M.goldfish_score E sourceTree sourceVotes sourceVotes s B ⇢ g →
      M.voters_count E sourceLate s < 2 * g)
    (hsub : targetSupport ⊆ targetVotes)
    (hcompatible : Block.compatible A B = true)
    (hpath : Block.Preceq A B →
      ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B →
        C ∈ tree) :
    ∀ X : Block V, M.goldfish_fork_choice E σ h_max targetTree cur A tree
        targetVotes targetSupport s ⇢ X → Block.Preceq B X := by
  intro X hX
  have hS := fun u => facts.fc.targets_under_nonempty sourceTree B u
  have hTt := fun u => facts.fc.targets_under_nonempty targetTree B u
  let tS : GoldfishVote V → Bool := fun u => Classical.choose (hS u)
  let tT : GoldfishVote V → Bool := fun u => Classical.choose (hTt u)
  have htS : ∀ u, M.targets_under sourceTree B u ⇢ tS u := fun u => Classical.choose_spec (hS u)
  have htT : ∀ u, M.targets_under targetTree B u ⇢ tT u := fun u => Classical.choose_spec (hTt u)
  obtain ⟨g, hg⟩ := facts.fc.goldfish_score_nonempty E sourceTree sourceVotes sourceVotes s B
  obtain ⟨sS, hsS⟩ := facts.fc.raw_supporters_nonempty sourceTree sourceVotes sourceVotes s B
  obtain ⟨sT, hsT⟩ := facts.fc.raw_supporters_nonempty targetTree targetVotes targetSupport s B
  have hforward : ∀ u ∈ sourceVotes, tS u = true →
      (u ∈ targetSupport ∧ tT u = true) ∨ M.equivocates targetVotes u.val_index = true := by
    intro u hu htu
    rcases hT.forward u hu (tS u) (htS u) htu with ⟨hmem, hall⟩ | heq
    · exact Or.inl ⟨hmem, hall (tT u) (htT u)⟩
    · exact Or.inr heq
  have hadopt := facts.fc.confirmation_adoption hN.early_late hN.filtered tS htS tT htT hforward
    hT.backward g hg (heligible g hg) sS hsS sT hsT
  exact facts.fc.goldfish_fork_choice_captures_supporter_majority E σ h_max targetTree tree cur
    targetVotes targetSupport s hsub sT hsT hadopt.2 hcompatible hpath X hX

end

end DecoupledConsensusModel.Sts.Restated
