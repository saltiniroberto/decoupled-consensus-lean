import Proofs.Vocabulary.Protocol.ForkChoice.Views.VoteSetValidityCore
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_FinalityGadget_Crossing
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Model.Record.Wiring

/-!
# Validity of vote sets

The proposer's view, the late confirmation votes and the voter view of a store are valid vote sets,
stated over a model `M : Record.Model V`.
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
open Execution

/-- If the pools of `st` carry their slot stamps and their committee memberships, then the
    proposer's view of `st` at slot `s` is a valid vote set for slot `s - 1`. -/
theorem Vocabulary.Protocol.voteSetValid_proposer_view (facts : Record.Facts M) {E : Env V} {st : M.S}
    (hslots : Restated.Vocabulary.Protocol.PoolStamps M st) (hcommittee : Restated.Vocabulary.Protocol.CommitteePools M E st) (s : Slot) :
    Protocol.VoteSetValid E (s - 1)
      (M.proposer_view (M.toHealing st).toFG.toSG.toGoldfishStore s).toFinset := by
  rw [facts.fc.proposer_view_toFinset, facts.sto.toHealing_gs_pool]
  intro u hu
  have hu' := (facts.sto.mem_store_pool_iff st (s - 1) u).mp hu
  exact ⟨hslots.slot (s - 1) u hu', hcommittee (s - 1) u hu'⟩

end

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution

/-- If the pools of `st` carry their slot stamps and their committee memberships, then the late
    confirmation votes `confLate` of `st` at slot `s` are a valid vote set for slot `s`. -/
theorem Vocabulary.Protocol.voteSetValid_confLate (facts : Record.Facts M) {E : Env V} {st : M.S}
    (hslots : Restated.Vocabulary.Protocol.PoolStamps M st) (hcommittee : Restated.Vocabulary.Protocol.CommitteePools M E st) (s : Slot) :
    Protocol.VoteSetValid E s (Restated.Vocabulary.Protocol.confLate M E st s) := by
  intro u hu
  rw [Restated.Vocabulary.Protocol.confLate, beforeCutoff, Finset.mem_filter] at hu
  have hu' := (facts.sto.mem_store_pool_iff st s u).mp hu.1
  exact ⟨hslots.slot s u hu', hcommittee s u hu'⟩

end

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution

/-- If the pool of `st` at slot `s − 1` is a valid vote set for slot `s − 1`, and every Goldfish
    vote included in a block of `st`'s tree has its signer in that vote's slot's committee, then
    every outcome `Y` of the slot-`s` raw voter view of `st` is a valid vote set for slot `s − 1`. -/
theorem Vocabulary.Protocol.voteSetValid_voter_view_of_carried (facts : Record.Facts M) {E : Env V} {st : M.S}
    (s : Slot)
    (hpool : Protocol.VoteSetValid E (s - 1) ((M.store_pool st (s - 1))))
    (hcarried : ∀ B ∈ st.T, ∀ u ∈ B.gf_votes,
      u.val_index ∈ E.committee u.slot) :
    ∀ Y, M.voter_view E (M.toHealing st).toFG.toSG.toGoldfishStore s ⇢ Y →
    Protocol.VoteSetValid E (s - 1) Y := by
  intro Y hY u hu
  rcases facts.fc.voter_view_cases_beforeCutoff E _ s Y hY hu with hpoolArm | ⟨X, hXT, -, huX, hus⟩
  · apply hpool
    rw [beforeCutoff, Finset.mem_filter, facts.sto.toHealing_gs_pool] at hpoolArm
    exact hpoolArm.1
  · refine ⟨hus, ?_⟩
    rw [facts.sto.toHealing_gs_T] at hXT
    have hcommittee := hcarried X hXT u huX
    simpa only [hus] using hcommittee

end

end DecoupledConsensusModel.Sts.Restated
