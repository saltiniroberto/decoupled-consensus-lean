import Proofs.Vocabulary.Protocol.Grades.ProposalLifecycleCore
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring

/-!
# Confirmation under a grade contract

The condition that a store's confirmation update under a grade contract selects a block that passes
the confirmation test, stated over a model `M : Record.Model V`, and its agreement with the
definition of the same name at `Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution
open Internal.NamedRecoveryRead

/-- Every store the confirmation update of `st` at slot `s` under `contract` can return has `B` as
    its live confirmed block (`selected`); and for every outcome `A` of `confAnchorWith`, every
    outcome `u` of `confVotes`, every score function `sc` read from the Goldfish score with `u`, and
    every outcome `H` of the GHOST walk from `A` in `confTree` with the test that `confCount` is
    less than twice the score, `H` passes that test (`genuine`). -/
structure Vocabulary.Protocol.GenuineConfirmationWith (M : Record.Model V) (contract : M.Contract)
    (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot)
    (B : Block V) : Prop where
  selected : ∀ st' : M.S, M.update_confirmation_with contract E hc st s ⇢ st' →
    st'.live_confirmed = B
  genuine : ∀ A : Block V, Restated.Vocabulary.Protocol.confAnchorWith M contract E hc st ⇢ A →
    ∀ u : Finset (GoldfishVote V), Restated.Vocabulary.Protocol.confVotes M E st s ⇢ u →
    ∀ sc : Block V → Nat, (∀ B', M.goldfish_score E st.T u u s B' ⇢ sc B') →
    ∀ H : Block V, M.ghost A (Restated.Vocabulary.Protocol.confTree M st) sc
      (fun B' => decide (Restated.Vocabulary.Protocol.confCount M E st s < 2 * sc B')) ⇢ H →
    decide (Restated.Vocabulary.Protocol.confCount M E st s < 2 * sc H) = true

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution
open Internal.NamedRecoveryRead

/-- `DecoupledConsensusModel.Protocol.GenuineConfirmationWith` holds exactly when its form over the
    record holds at `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.GenuineConfirmationWith_vocabulary_eq (contract : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) (B : Block V) :
    _root_.DecoupledConsensusModel.Protocol.GenuineConfirmationWith (V := V) contract E hc st s B ↔ Restated.Vocabulary.Protocol.GenuineConfirmationWith (V := V) Record.Model.vocabulary contract E hc st s B :=
  by
  constructor
  · intro h
    refine ⟨fun st' hst' => ?_, fun A hA u hu sc hsc H hH => ?_⟩
    · obtain rfl := (Record.returns_pure _ _).1 hst'
      exact h.selected
    · rw [Vocabulary.Protocol.confAnchorWith_vocabulary_eq] at hA
      rw [Vocabulary.Protocol.confVotes_vocabulary_eq] at hu
      obtain rfl := (Record.returns_pure _ _).1 hA
      obtain rfl := (Record.returns_pure _ _).1 hu
      have hsc' : sc = _root_.DecoupledConsensusModel.Protocol.confScore E st s :=
        funext fun B' => (Record.returns_pure _ _).1 (hsc B')
      subst hsc'
      obtain rfl := (Record.returns_pure _ _).1 hH
      exact h.genuine
  · intro h
    refine ⟨h.selected _ ((Record.returns_pure _ _).2 rfl), ?_⟩
    exact h.genuine _ (by rw [Vocabulary.Protocol.confAnchorWith_vocabulary_eq]; exact (Record.returns_pure _ _).2 rfl)
      _ (by rw [Vocabulary.Protocol.confVotes_vocabulary_eq]; exact (Record.returns_pure _ _).2 rfl)
      (_root_.DecoupledConsensusModel.Protocol.confScore E st s)
      (fun B' => (Record.returns_pure _ _).2 rfl) _ ((Record.returns_pure _ _).2 rfl)

end

end DecoupledConsensusModel.Sts.Restated
