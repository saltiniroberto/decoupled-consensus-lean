import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Agreement
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Record.Wiring

/-!
# A Goldfish vote names the proposal it extends

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: when a proposal
extends the voter's store at a prepared vote read and the voter is in the committee of the read's
slot, every outcome of the Goldfish vote duty is the voter's vote for the proposal's root.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open Protocol
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Proofs.HealingSurface (voterAnchorAt voterCandidateTreeAt)

/-- For every prepared vote read `w₁` of `v` at slot `s`, if the proposal `B` extends the voter's
    store at `w₁` (with `tree₀` and `H`) and `v`'s validator is in the committee of `w₁`'s slot,
    then every outcome `D` of the Goldfish vote duty at `w₁` under `w₁`'s grade contract returns
    `v`'s vote at that slot for the root of `B`'s block. -/
theorem Vocabulary.Proofs.Optimistic.goldfish_vote_eq_extends_with (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V) (v : V) (s : Slot)
    {tree₀ : Finset (Block V)} {H : Block V} {B : NamedBlock V} :
    ∀ w₁ ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S ρ v s,
    (hal : Restated.Vocabulary.Proofs.Optimistic.NamedVoteStoreExtends M S ρ v s w₁ tree₀ H B) →
    (hcom : (S.node v).val_index ∈ S.E.committee w₁.st.core.s) →
    ∀ D : M.NS × Option (GoldfishVote V),
    M.duties_goldfish_vote_with (M.gradeContract w₁.cache) S.E S.hc (S.node v) w₁.st ⇢ D →
    D.2 = some ⟨(S.node v).val_index, w₁.st.core.s, B.erase.root⟩ := by
  intro w₁ _ hal hcom D hD
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E w₁.st.core w₁.st.core.s
  obtain ⟨W, hW⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing w₁.st.core).toFG.toSG.toGoldfishStore w₁.st.core.s
  obtain ⟨U, hU⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing w₁.st.core).toFG.toSG.toGoldfishStore w₁.st.core.s
  obtain ⟨X, hX⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract w₁.cache) S.E
    S.hc (M.toHealing w₁.st.core) T W U (w₁.st.core.s - 1)
  rw [facts.fc.goldfish_vote_with_snd_of_mem_committee _ _ _ _ _ hcom D hD T hT W hW U hU X hX,
    hal.head T hT W hW U hU X hX]

end

end DecoupledConsensusModel.Sts.Restated
