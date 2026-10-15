import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedConfirmationWalk
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ConfirmationScore
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Record.Wiring

/-!
# Confirmation walk and confirmation at a slot

The GHOST walk the confirmation duty tests at a slot, and the condition that a validator's
confirmation at that slot is the walk's block and passes the eligibility test, over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Internal
open Execution NamedRecoveryRead

/-- The outcomes of the confirmation walk on `n` at slot `s`: the GHOST walk from an outcome of the
    SG root over the filtered tree of `n`'s core store, with a score function built from one outcome
    of `confirmationVotes` and the test that the voter count of the late confirmation votes is less
    than twice the score. -/
def Vocabulary.Internal.namedConfirmationWalk (M : Record.Model V) (S : Setup V) (n : M.N) (s : Slot) :
    DC.NDRE (Block V) := do
  let st := n.st.core
  let A ← M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc
    (M.toHealing st) (M.round_of S.hc st.s)
  let X ← Restated.Vocabulary.Internal.confirmationVotes M S.E st s
  let sc ← (ExceptT.lift {sc : Block V → Nat | ∀ B, M.goldfish_score S.E st.T X X s B ⇢ sc B} :
    DC.NDRE (Block V → Nat))
  M.ghost A (M.get_filtered_block_tree (M.toHealing st).toFG) sc
    (fun B => decide (M.voters_count S.E (Restated.Vocabulary.Internal.confirmationLate M S.E st s) s <
      2 * sc B))

end

section
open DecoupledConsensusModel.Internal
open Execution NamedRecoveryRead

/-- For every confirmation read `n` prepared from `v`'s node state in `w₁` at slot `s`'s
    confirmation time and every outcome `W` of its confirmation walk, the confirmation of `v`'s
    store in `w₂` is `W`, and `W` passes the eligibility test. -/
def Vocabulary.Internal.GenuineConfirmationAt (M : Record.Model V) (S : Setup V) (ρ : Record.Run V) (v : V) (s : Slot)
    (w₁ w₂ : V → M.N) : Prop :=
  let t := M.confirmation_time S.E s
  ∀ n : M.N, (∃ c : M.Cache, M.onPhaseTick S.E S.hc (w₁ v).st.core.toHealing t (w₁ v).cache ⇢ c ∧
    n = M.mkNode (M.ns_setClock S.E (w₁ v).st t) (w₁ v).record c) →
  let st := n.st.core
  ∀ A : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc
    (M.toHealing st) (M.round_of S.hc st.s) ⇢ A →
  ∀ X : Finset (GoldfishVote V), Restated.Vocabulary.Internal.confirmationVotes M S.E st s ⇢ X →
  ∀ sc : Block V → Nat, (∀ B, M.goldfish_score S.E st.T X X s B ⇢ sc B) →
  let el := fun B => decide (M.voters_count S.E
    (Restated.Vocabulary.Internal.confirmationLate M S.E st s) s < 2 * sc B)
  ∀ W : Block V, M.ghost A (M.get_filtered_block_tree (M.toHealing st).toFG) sc el ⇢ W →
  (w₂ v).st.live_confirmed = W ∧ el W = true

end

section
open DecoupledConsensusModel.Internal
open Execution NamedRecoveryRead

/-- At the model `Record.Model.vocabulary`, the only function giving every block `B` an outcome of its
    Goldfish score, with `DecoupledConsensusModel.Internal.confirmationVotes` in both vote
    arguments, is `DecoupledConsensusModel.Internal.confirmationScore`. -/
theorem Vocabulary.Internal.confirmationScore_choice_vocabulary (E : Env V)
    (st : (Record.Model.vocabulary (V := V)).S) (s : Slot) :
    {sc : Block V → Nat | ∀ B, (Record.Model.vocabulary (V := V)).goldfish_score E st.T
        (_root_.DecoupledConsensusModel.Internal.confirmationVotes E st s)
        (_root_.DecoupledConsensusModel.Internal.confirmationVotes E st s) s B ⇢ sc B} =
      {_root_.DecoupledConsensusModel.Internal.confirmationScore (V := V) E st s} := by
  ext sc
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    funext B
    exact (Record.returns_pure _ _).1 (h B)
  · intro h B
    subst h
    exact (Record.returns_pure _ _).2 rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Internal.namedConfirmationWalk` has the
    single outcome `DecoupledConsensusModel.Internal.namedConfirmationWalk`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.namedConfirmationWalk_vocabulary_eq (S : Setup V) (n : NamedNodeState V) (s : Slot) :
    Restated.Vocabulary.Internal.namedConfirmationWalk (V := V) Record.Model.vocabulary S n s =
      pure (_root_.DecoupledConsensusModel.Internal.namedConfirmationWalk (V := V) S n s) := by
  show ((pure _ : DC.NDRE (Block V)) >>= fun A => _) = _
  rw [pure_bind, Vocabulary.Internal.confirmationVotes_vocabulary_eq, pure_bind,
    Vocabulary.Internal.confirmationScore_choice_vocabulary, ← Set.pure_def, ExceptT.lift_pure,
    pure_bind]
  rfl

/-- `DecoupledConsensusModel.Internal.GenuineConfirmationAt` holds exactly when
    `Restated.Vocabulary.Internal.GenuineConfirmationAt` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.GenuineConfirmationAt_vocabulary_eq (S : Setup V) (ρ : Run V) (v : V) (s : Slot) :
    _root_.DecoupledConsensusModel.Internal.GenuineConfirmationAt (V := V) S ρ v s ↔
      Restated.Vocabulary.Internal.GenuineConfirmationAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ) v s
        (NamedRun.stateBeforeTime S ρ (Protocol.confirmation_time S.E s))
        (NamedRun.readAt S ρ (Protocol.confirmation_time S.E s)) := by
  have hset : ∀ n : NamedNodeState V,
      (∃ c : (Record.Model.vocabulary (V := V)).Cache,
        (Record.Model.vocabulary (V := V)).onPhaseTick S.E S.hc
          (NamedRun.stateBeforeTime S ρ (Protocol.confirmation_time S.E s) v).st.core.toHealing
          (Protocol.confirmation_time S.E s)
          (NamedRun.stateBeforeTime S ρ (Protocol.confirmation_time S.E s) v).cache ⇢ c ∧
        n = (Record.Model.vocabulary (V := V)).mkNode
          ((Record.Model.vocabulary (V := V)).ns_setClock S.E
            (NamedRun.stateBeforeTime S ρ (Protocol.confirmation_time S.E s) v).st
            (Protocol.confirmation_time S.E s))
          (NamedRun.stateBeforeTime S ρ (Protocol.confirmation_time S.E s) v).record c) ↔
      n = _root_.DecoupledConsensusModel.Internal.NamedRecoveryRead.confirmationInputRead S ρ v s := by
    have key := Vocabulary.Execution.NamedActionReads.confirmationReadAt_vocabulary_eq S ρ v
      (Protocol.confirmation_time S.E s)
    intro n
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hmem : _ ∈ Restated.Vocabulary.Execution.NamedActionReads.confirmationReadAt
          Record.Model.vocabulary S (Record.Run.ofVocabulary ρ) v (Protocol.confirmation_time S.E s) :=
        ⟨_, by rw [Vocabulary.Execution.NamedRun.stateBeforeTime_vocabulary_eq]; exact Set.mem_singleton _,
          c, hc, rfl⟩
      rw [key] at hmem
      exact hmem
    · intro hn
      have hmem : n ∈ Restated.Vocabulary.Execution.NamedActionReads.confirmationReadAt
          Record.Model.vocabulary S (Record.Run.ofVocabulary ρ) v (Protocol.confirmation_time S.E s) := by
        rw [key]; exact hn
      obtain ⟨w, hw, c, hc, rfl⟩ := hmem
      rw [Vocabulary.Execution.NamedRun.stateBeforeTime_vocabulary_eq] at hw
      obtain rfl := Set.mem_singleton_iff.mp hw
      exact ⟨c, hc, rfl⟩
  constructor
  · intro h n hn st A hA X hX sc hsc el W hW
    obtain rfl := (hset n).1 hn
    obtain rfl := (Record.returns_pure _ _).1 hA
    rw [Vocabulary.Internal.confirmationVotes_vocabulary_eq, Record.returns_pure] at hX
    subst hX
    have hsc' : sc = _root_.DecoupledConsensusModel.Internal.confirmationScore S.E _ s :=
      funext fun B => (Record.returns_pure _ _).1 (hsc B)
    subst hsc'
    obtain rfl := (Record.returns_pure _ _).1 hW
    exact h
  · intro h
    exact h _ ((hset _).2 rfl) _ ((Record.returns_pure _ _).2 rfl) _
      (by rw [Vocabulary.Internal.confirmationVotes_vocabulary_eq]; exact (Record.returns_pure _ _).2 rfl)
      _ (fun B => (Record.returns_pure _ _).2 rfl) _ ((Record.returns_pure _ _).2 rfl)

end

end DecoupledConsensusModel.Sts.Restated
