import Proofs.Vocabulary.Execution.RecoveryActionLiveSourceSplit
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RecoveryCapturedActionCarrier
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Record.Wiring

/-!
# The `live_confirmed` block written at an action

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: the
`live_confirmed` block of the store an action read gives is either a block that passes
`Restated.Vocabulary.Protocol.GenuineConfirmationWith` for the tick store at the opening slot's
confirmation time, or the FG root of that tick store.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Protocol

/-- For every world `w` that can hold before round `r`'s action time and every node state `n` that
    `v`'s action read from `w` can give, either some block `C` passes
    `Restated.Vocabulary.Protocol.GenuineConfirmationWith`, with the grade contract of `n`'s cache,
    for the tick store `v` holds in `w` at the opening slot's confirmation time, and `C` is the
    `live_confirmed` of `n`'s core store; or the FG root of that tick store is that
    `live_confirmed`. -/
theorem Vocabulary.Proofs.HealingSurface.actionStoreAt_liveConfirmed_genuine_or_fgRoot (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    (∃ C : Block V,
      Restated.Vocabulary.Protocol.GenuineConfirmationWith M
        (M.gradeContract n.cache)
        S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w v).st.core
          (M.confirmation_time S.E (M.opening_slot S.hc r)))
        ((M.opening_slot S.hc r)) C ∧
      C = n.st.core.live_confirmed) ∨
    (∃ R : Block V,
      R = M.get_fg_root
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w v).st.core
          (M.confirmation_time S.E (M.opening_slot S.hc r)))).toFG ∧
      R = n.st.core.live_confirmed) := by
  intro w hw n hn
  have hcore := Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_eq_update_confirmation_confStore
    facts S rho v r w hw n hn
  by_cases hroot : n.st.core.live_confirmed = M.get_fg_root
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w v).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc r)))).toFG
  · exact Or.inr ⟨_, rfl, hroot.symm⟩
  · refine Or.inl ⟨n.st.core.live_confirmed,
      ⟨fun st' hst' => by
        obtain ⟨s0, hs0, hs0X⟩ := hcore st' hst'
        rw [← hs0X, hs0, facts.nd.store_with_cache_core_live_confirmed], ?_⟩, rfl⟩
    intro A hA u hu sc hsc H hH
    obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract n.cache) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w v).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc r))) (M.opening_slot S.hc r)
    obtain ⟨e, he, rfl⟩ := returns_map_elim _ _ _ hu
    obtain ⟨tm, htm, rfl⟩ := returns_map_elim _ _ _ he
    rcases facts.hd.update_confirmation_with_live_confirmed_genuine_or_fgRoot
        (M.gradeContract n.cache) S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w v).st.core
          (M.confirmation_time S.E (M.opening_slot S.hc r)))
        (M.opening_slot S.hc r) tm htm A hA sc hsc H hH X hX with ⟨C, -, hC⟩ | hfg
    · exact hC
    · obtain ⟨s0, hs0, hs0X⟩ := hcore X hX
      exact absurd (by rw [hs0, facts.nd.store_with_cache_core_live_confirmed, hs0X]; exact hfg) hroot

end

end DecoupledConsensusModel.Sts.Restated
