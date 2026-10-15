import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Confirmation
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_ModelVocabulary_Goldfish_ForkChoice
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Confirmation
import Model.Record.Wiring

/-!
# Goldfish supporters

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: membership in the
Goldfish supporters of a block, and the supporters of a block contained in those of each of its
ancestors.
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
open DecoupledConsensusModel.Execution

/-- For every outcome `R` of the supporters of `B` and every choice `t` of one outcome of the
    supporter test `M.targets_under T B u` per vote `u`, `x` is in `R` exactly when `x` does not
    equivocate in `votes` and has a vote `u` in `support_votes` of slot `s` with `t u = true`. -/
theorem Vocabulary.Protocol.mem_supporters_iff (facts : Record.Facts M) {E : Env V} {T : Finset (Block V)}
    {votes support_votes : Finset (GoldfishVote V)} {s : Slot} {B : Block V} {x : V}
    (R : Finset V)
    (hR : Restated.Vocabulary.Protocol.goldfishSupporters M E T votes support_votes s B ⇢ R)
    (t : GoldfishVote V → Bool) (ht : ∀ u, M.targets_under T B u ⇢ t u) :
    x ∈ R ↔
      M.equivocates votes x = false ∧
      ∃ u ∈ M.votes_by support_votes x, u.slot = s ∧ t u = true :=
  facts.fc.mem_supporters_iff (_E := E) R hR t ht

end

section
open DecoupledConsensusModel.Protocol
open Internal
open DecoupledConsensusModel.Execution

/-- If `C` is an ancestor of `B`, every outcome of the supporters of `B` is contained in every
    outcome of the supporters of `C`. -/
theorem Vocabulary.Protocol.supporters_mono (facts : Record.Facts M) (E : Env V) (T : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) {C B : Block V}
    (h : Block.preceq C B = true) :
    ∀ RB, Restated.Vocabulary.Protocol.goldfishSupporters M E T votes support_votes s B ⇢ RB →
    ∀ RC, Restated.Vocabulary.Protocol.goldfishSupporters M E T votes support_votes s C ⇢ RC →
      RB ⊆ RC := by
  intro RB hRB RC hRC x hx
  choose tB htB using fun u => facts.fc.targets_under_nonempty T B u
  choose tC htC using fun u => facts.fc.targets_under_nonempty T C u
  rw [Restated.Vocabulary.Protocol.mem_supporters_iff facts RB hRB tB htB] at hx
  rw [Restated.Vocabulary.Protocol.mem_supporters_iff facts RC hRC tC htC]
  obtain ⟨hne, u, hu, hslot, htar⟩ := hx
  obtain ⟨B', hfind, hslot', hpre⟩ := (facts.fc.targets_under_iff (tB u) (htB u)).mp htar
  exact ⟨hne, u, hu, hslot, (facts.fc.targets_under_iff (tC u) (htC u)).mpr
    ⟨B', hfind, hslot', Block.preceq_trans h hpre⟩⟩

end

end DecoupledConsensusModel.Sts.Restated
