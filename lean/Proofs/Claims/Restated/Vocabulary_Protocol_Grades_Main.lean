import Proofs.Vocabulary.Protocol.Grades.Main
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring

/-!
# The live confirmation under a grade contract

When the confirmation update under a grade contract confirms exactly a block `B`, stated over a
model `M : Record.Model V`.
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
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- If `votes` is an outcome of the slot-`s` counted votes of `st` and gives `B` honest support from
    `Hon`, the late vote set of slot `s` is valid, and `A` is an outcome of the anchor under
    `contract` that is an ancestor of `B` with every block strictly between `A` and `B` in the
    confirmation tree, then every outcome `st'` of the confirmation update under `contract` at slot
    `s` confirms exactly `B`. -/
theorem Vocabulary.Protocol.live_confirmed_eq_with (facts : Record.Facts M) (contract : M.Contract) (E : Env V)
    (hc : HealConfig) (st : M.S)
    (s : Slot) (Hon : Finset V) (B : Block V)
    (votes : Finset (GoldfishVote V)) (hvotes : Restated.Vocabulary.Protocol.confVotes M E st s ⇢ votes)
    (hsup : HonestSupport E st.T votes s Hon B)
    (hvalid : Protocol.VoteSetValid E s (Restated.Vocabulary.Protocol.confLate M E st s))
    (A : Block V) (hA : Restated.Vocabulary.Protocol.confAnchorWith M contract E hc st ⇢ A)
    (hpre : Block.Preceq A B)
    (hpath : ∀ C : Block V, Block.Preceq A C →
      C ≠ A → Block.Preceq C B → C ∈ Restated.Vocabulary.Protocol.confTree M st) :
    ∀ st', M.update_confirmation_with contract E hc st s ⇢ st' → st'.live_confirmed = B := by
  intro st' hst'
  obtain ⟨e, he, rfl⟩ := returns_map_elim _ _ _ hvotes
  obtain ⟨tm, htm, rfl⟩ := returns_map_elim _ _ _ he
  exact facts.hd.live_confirmed_eq_with contract E hc st s Hon B tm htm hsup hvalid A hA hpre hpath
    st' hst'

end

end DecoupledConsensusModel.Sts.Restated
