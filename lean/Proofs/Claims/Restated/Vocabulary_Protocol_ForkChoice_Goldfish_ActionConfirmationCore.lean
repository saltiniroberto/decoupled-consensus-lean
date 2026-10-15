import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ActionConfirmationCore
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Record.Wiring

/-!
# The action store and the opening confirmation store

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: the store of an
action read is a named store with the read's cache written in, whose core store is the confirmation
write, for the round's opening slot, of the tick store at that slot's confirmation time; and the FG
root read at the action is that tick store's.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface

/-- For every world `w` that can hold before round `r`'s action time, every node state `n` that
    `v`'s action read from `w` can give, and every outcome `X` of the confirmation write, for the
    opening slot of `r`, of the tick store `v` holds in `w` at that slot's confirmation time, with
    the grade contract of `n`'s cache, `n`'s store is some named store `st` with `n`'s cache written
    in, and `st`'s core store is `X`. -/
theorem Vocabulary.Proofs.HealingSurface.actionStoreAt_eq_update_confirmation_openingConfStore (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    ∀ X, M.update_confirmation_with (M.gradeContract n.cache) S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w v).st.core
          (M.confirmation_time S.E (M.opening_slot S.hc r)))
        ((M.opening_slot S.hc r)) ⇢ X →
    ∃ st : M.NS, n.st = M.store_with_cache st n.cache ∧ st.core = X := by
  intro w hw n hn X hX
  have hsc : (Restated.Vocabulary.Execution.Setup.a M S r) =
      M.support_cutoff S.E ((M.opening_slot S.hc r) + 1) :=
    Restated.Vocabulary.Protocol.a_eq_support_cutoff_succ facts S.hc S.E r
  have hslot : S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S r)) = (M.opening_slot S.hc r) + 1 := by
    rw [hsc]
    exact facts.sch.slotOf_support_cutoff S.E _
  have hidx : S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S r)) - 1 = (M.opening_slot S.hc r) := by
    rw [hslot]; simp
  have hconf : (Restated.Vocabulary.Execution.Setup.a M S r) = M.confirmation_time S.E ((M.opening_slot S.hc r)) :=
    Restated.Vocabulary.Protocol.a_eq_confirmation_time facts S.hc S.E r
  obtain ⟨c, hc, st, hst, rfl⟩ := hn
  rw [facts.nd.mkNode_cache] at hX
  refine ⟨st, by rw [facts.nd.mkNode_st, facts.nd.mkNode_cache], ?_⟩
  have htick : Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w v).st.core
      (M.confirmation_time S.E (M.opening_slot S.hc r)) =
      (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S r)).core := by
    rw [facts.hd.setClock_core_eq_store_with_t_s, hconf]
    rfl
  rw [htick] at hX
  have hst' : M.duties_update_confirmation_with (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S r))
      (M.opening_slot S.hc r) ⇢ st := by
    rw [← hidx]
    exact hst
  exact facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst' X hX

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface

/-- For every world `w` that can hold before round `r`'s action time and every node state `n` that
    `v`'s action read from `w` can give, the FG root of `n`'s store is the FG root of the tick store
    `v` holds in `w` at the confirmation time of `r`'s opening slot. -/
theorem Vocabulary.Proofs.HealingSurface.actionStoreAt_fgRoot_eq_openingConfStore (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    M.get_fg_root (M.toHealing n.st.core).toFG =
      M.get_fg_root
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w v).st.core
          (M.confirmation_time S.E (M.opening_slot S.hc r)))).toFG := by
  intro w hw n hn
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w v).st.core
      (M.confirmation_time S.E (M.opening_slot S.hc r))) (M.opening_slot S.hc r)
  obtain ⟨st, hst, hstX⟩ :=
    Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_eq_update_confirmation_openingConfStore
      facts S rho v r w hw n hn X hX
  rw [hst, facts.nd.store_with_cache_get_fg_root, hstX]
  exact facts.dt.update_confirmation_with_toHealing_fg_root _ _ _ _ _ X hX

end

end DecoupledConsensusModel.Sts.Restated
