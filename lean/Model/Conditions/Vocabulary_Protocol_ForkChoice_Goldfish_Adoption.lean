import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Adoption
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring

/-!
# Vote transport and confirmation of a block

The conditions that transfer one confirmation count to an ordinary voter view, and that a store's
confirmation update confirms a block whose confirmation walk passes the eligibility test, over a
model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol
open Internal
open Protocol (ChainState)

/-- The delivery and resolution facts that transfer one confirmation count, from `sourceVotes` and
    `sourceLate`, to the voter views `targetVotes` and `targetSupport`. -/
structure Vocabulary.Protocol.AdoptionTransport (M : Record.Model V) (sourceTree targetTree : Finset (Block V))
    (sourceVotes sourceLate targetVotes targetSupport : Finset (GoldfishVote V))
    (B : Block V) : Prop where
  /-- A vote of `sourceVotes` that targets `B` in `sourceTree` is in `targetSupport` and targets `B`
      in `targetTree`, or its validator equivocates in `targetVotes`. -/
  forward : ∀ u ∈ sourceVotes, ∀ b : Bool, M.targets_under sourceTree B u ⇢ b →
    b = true →
      (u ∈ targetSupport ∧
        ∀ b' : Bool, M.targets_under targetTree B u ⇢ b' → b' = true) ∨
        M.equivocates targetVotes u.val_index = true
  /-- Every vote of `targetVotes` is in `sourceLate`, or its validator equivocates in `sourceLate`. -/
  backward : ∀ u ∈ targetVotes,
    u ∈ sourceLate ∨ M.equivocates sourceLate u.val_index = true

end

section
open DecoupledConsensusModel.Protocol
open Internal
open Protocol (ChainState)

/-- Every store the confirmation update of `st` at slot `s` under `contract` can return has `B` as
    its live confirmed block, and every outcome of the confirmation walk passes the eligibility test
    `confCount < 2 · score`. -/
structure Vocabulary.Protocol.GenuineConfirmation (M : Record.Model V) (E : Env V) (hc : Protocol.HealConfig)
    (st : M.S) (s : Slot) (B : Block V)
    (contract : M.Contract) : Prop where
  selected : ∀ st' : M.S, M.update_confirmation_with contract E hc st s ⇢ st' →
    st'.live_confirmed = B
  genuine : ∀ A : Block V, Restated.Vocabulary.Protocol.confAnchorWith M contract E hc st ⇢ A →
    ∀ u : Finset (GoldfishVote V), Restated.Vocabulary.Protocol.confVotes M E st s ⇢ u →
    ∀ sc : Block V → Nat, (∀ B', M.goldfish_score E st.T u u s B' ⇢ sc B') →
    ∀ H : Block V, M.ghost A (Restated.Vocabulary.Protocol.confTree M st) sc
      (fun B' => decide (Restated.Vocabulary.Protocol.confCount M E st s < 2 * sc B')) ⇢ H →
    decide (Restated.Vocabulary.Protocol.confCount M E st s < 2 * sc H) = true

end

section
open DecoupledConsensusModel.Protocol
open Internal
open Protocol (ChainState)

/-- `DecoupledConsensusModel.Protocol.AdoptionTransport` holds exactly when
    `Restated.Vocabulary.Protocol.AdoptionTransport` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.AdoptionTransport_vocabulary_eq (sourceTree targetTree : Finset (Block V)) (sourceVotes sourceLate targetVotes targetSupport : Finset (GoldfishVote V)) (B : Block V) :
    _root_.DecoupledConsensusModel.Protocol.AdoptionTransport (V := V) sourceTree targetTree sourceVotes sourceLate targetVotes targetSupport B ↔ Restated.Vocabulary.Protocol.AdoptionTransport (V := V) Record.Model.vocabulary sourceTree targetTree sourceVotes sourceLate targetVotes targetSupport B :=
  by
  constructor <;> intro h <;> cases h <;> constructor <;>
    (try simp only [record_vocabulary, Record.Model.vocabulary, Record.returns_pure, forall_eq] at *) <;> assumption

/-- `DecoupledConsensusModel.Protocol.GenuineConfirmation` holds exactly when
    `Restated.Vocabulary.Protocol.GenuineConfirmation` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.GenuineConfirmation_vocabulary_eq (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) (B : Block V) (contract : Protocol.GradeContract V) :
    _root_.DecoupledConsensusModel.Protocol.GenuineConfirmation (V := V) E hc st s B contract ↔ Restated.Vocabulary.Protocol.GenuineConfirmation (V := V) Record.Model.vocabulary E hc st s B contract := by
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
