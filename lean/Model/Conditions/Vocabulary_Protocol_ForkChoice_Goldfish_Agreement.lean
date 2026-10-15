import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Agreement
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Record.Wiring

/-!
# Cone support and the voter's candidate tree

The honest support of a cone of targets, the voter's candidate tree, and the condition that a
proposal extends the voter's tree as its head, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open Protocol
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Proofs.HealingSurface (voterAnchorAt voterCandidateTreeAt)

/-- Honest support in the tree `T`, from the slot-`s` votes, for the blocks satisfying `tgt`. -/
structure Vocabulary.Proofs.Optimistic.ConeSupport (M : Record.Model V) (E : Env V) (T : Finset (Block V))
    (votes support late : Finset (GoldfishVote V)) (s : Slot) (Hon : Finset V)
    (tgt : Block V → Prop) : Prop where
  /-- `|K_s| < 2·|K_s ∩ H|`: honest members are a strict majority of slot `s`'s committee. -/
  majority : (E.committee s).card < 2 * ((E.committee s) ∩ Hon).card
  /-- The counted votes are among the late votes. -/
  counted : votes ⊆ late
  /-- The support votes are among the raw votes. -/
  sub : support ⊆ votes
  /-- An honest committee member does not equivocate in the raw votes. -/
  no_equiv : ∀ x ∈ E.committee s, x ∈ Hon → M.equivocates votes x = false
  /-- Every honest committee member has a slot-`s` support vote whose target resolves in `T` to a
      block `X` no later than the vote's slot with `tgt X`. -/
  vote : ∀ x ∈ E.committee s, x ∈ Hon → ∃ u ∈ support, u.val_index = x ∧ u.slot = s ∧
    ∃ X : Block V, Block.find? T u.head = some X ∧ X.slot ≤ u.slot ∧ tgt X

/-- Honest support in the tree `T`, from the slot-`s` votes, for the blocks satisfying `tgt`,
    counted against the voters of the late votes: the late voters are fewer than twice the honest
    committee members. -/
structure Vocabulary.Proofs.Optimistic.ConeSupportCount (M : Record.Model V) (E : Env V)
    (T : Finset (Block V)) (votes support late : Finset (GoldfishVote V)) (s : Slot)
    (Hon : Finset V) (tgt : Block V → Prop) : Prop where
  /-- The voters of the late votes are fewer than twice the honest members of slot `s`'s
      committee. -/
  count : M.voters_count E late s < 2 * ((E.committee s) ∩ Hon).card
  /-- The counted votes are among the late votes. -/
  counted : votes ⊆ late
  /-- The support votes are among the raw votes. -/
  sub : support ⊆ votes
  /-- An honest committee member does not equivocate in the raw votes. -/
  no_equiv : ∀ x ∈ E.committee s, x ∈ Hon → M.equivocates votes x = false
  /-- Every honest committee member has a slot-`s` support vote whose target resolves in `T` to a
      block `X` no later than the vote's slot with `tgt X`. -/
  vote : ∀ x ∈ E.committee s, x ∈ Hon → ∃ u ∈ support, u.val_index = x ∧ u.slot = s ∧
    ∃ X : Block V, Block.find? T u.head = some X ∧ X.slot ≤ u.slot ∧ tgt X

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open Protocol
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Proofs.HealingSurface (voterAnchorAt voterCandidateTreeAt)

/-- The outcomes of the filtered block tree of `st`'s FG store over an outcome of the
    processed-block tree of the voter at slot `st.s`. -/
def Vocabulary.Proofs.Optimistic.voter_candidate_tree (M : Record.Model V) (E : Env V) (st : M.HS) :
    DC.NDRE (Finset (Block V)) := do
  let P ← M.voter_processed_block_tree E st.toFG.toSG.toGoldfishStore st.s
  pure (M.get_filtered_block_tree_from st.toFG P)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open Protocol
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Proofs.HealingSurface (voterAnchorAt voterCandidateTreeAt)

/-- At the prepared vote read `n`, the proposal `B` has parent `H`, is new to `tree₀`, and is the
    voter's head over the voter tree `tree₀` with `B` added. -/
structure Vocabulary.Proofs.Optimistic.NamedVoteStoreExtends (M : Record.Model V) (S : Setup V) (ρ : Record.Run V) (v : V) (s : Slot)
    (n : M.N) (tree₀ : Finset (Block V)) (H : Block V) (B : NamedBlock V) : Prop where
  /-- The proposal's slot is the slot of the read's store. -/
  cur : B.slot = n.st.core.s
  /-- The proposal's parent is `H`. -/
  parent : B.erase.parent? = some H
  /-- Every outcome of the voter's filtered block tree is `tree₀` with the proposal added. -/
  tree : ∀ T, M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T → T = insert B.erase tree₀
  /-- The proposal is not in `tree₀`. -/
  fresh : B.erase ∉ tree₀
  /-- No block of `tree₀` has the proposal as its parent. -/
  leaf : ∀ C ∈ tree₀, C.parent? ≠ some B.erase
  /-- Every outcome of the voter's head over the voter tree and the two voter views is the proposal. -/
  head : ∀ T, M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ W, M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ W →
    ∀ U, M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ U →
    ∀ X, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      T W U (n.st.core.s - 1) ⇢ X → X = B.erase

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open Protocol
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Proofs.HealingSurface (voterAnchorAt voterCandidateTreeAt)

/-- `DecoupledConsensusModel.Proofs.Optimistic.ConeSupport` holds exactly when
    `Restated.Vocabulary.Proofs.Optimistic.ConeSupport` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.Optimistic.ConeSupport_vocabulary_eq (E : Env V) (T : Finset (Block V)) (votes support late : Finset (GoldfishVote V)) (s : Slot) (Hon : Finset V) (tgt : Block V → Prop) :
    _root_.DecoupledConsensusModel.Proofs.Optimistic.ConeSupport (V := V) E T votes support late s Hon tgt ↔ Restated.Vocabulary.Proofs.Optimistic.ConeSupport (V := V) Record.Model.vocabulary E T votes support late s Hon tgt :=
  by
  constructor <;> intro h <;> cases h <;> constructor <;>
    (try simp only [record_vocabulary] at *) <;> assumption

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree`
    has the single outcome `DecoupledConsensusModel.Proofs.Optimistic.voter_candidate_tree`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.Optimistic.voter_candidate_tree_vocabulary_eq (E : Env V) (st : Protocol.HealingStore V) :
    Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree (V := V) Record.Model.vocabulary E st =
      pure (_root_.DecoupledConsensusModel.Proofs.Optimistic.voter_candidate_tree (V := V) E st) := by
  simp only [Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree, Record.Model.vocabulary,
    pure_bind]
  rfl

/-- `DecoupledConsensusModel.Proofs.Optimistic.NamedVoteStoreExtends` holds exactly when
    `Restated.Vocabulary.Proofs.Optimistic.NamedVoteStoreExtends` holds at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.Optimistic.NamedVoteStoreExtends_vocabulary_eq (S : Setup V) (ρ : Run V) (v : V) (s : Slot) (tree₀ : Finset (Block V)) (H : Block V) (B : NamedBlock V) :
    _root_.DecoupledConsensusModel.Proofs.Optimistic.NamedVoteStoreExtends (V := V) S ρ v s tree₀ H B ↔ Restated.Vocabulary.Proofs.Optimistic.NamedVoteStoreExtends (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ) v s
        (_root_.DecoupledConsensusModel.Internal.NamedRecoveryRead.voteDutyRead S ρ v s) tree₀ H B := by
  constructor
  · intro h
    refine ⟨h.cur, h.parent, ?_, h.fresh, h.leaf, ?_⟩
    · intro T hT
      simp only [Record.Model.vocabulary, Record.returns_pure] at hT
      subst hT
      exact h.tree
    · intro T hT W hW U hU X hX
      simp only [Record.Model.vocabulary, Record.returns_pure] at hT hW hU hX
      subst hT hW hU hX
      exact h.head
  · intro h
    exact ⟨h.cur, h.parent, h.tree _ ((Record.returns_pure _ _).2 rfl), h.fresh, h.leaf,
      h.head _ ((Record.returns_pure _ _).2 rfl) _ ((Record.returns_pure _ _).2 rfl)
        _ ((Record.returns_pure _ _).2 rfl) _ ((Record.returns_pure _ _).2 rfl)⟩

end

end DecoupledConsensusModel.Sts.Restated
