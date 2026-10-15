import Proofs.Vocabulary.Protocol.Grades.RecoveryCapturedActionCarrier
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionConfirmationCore
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Record.Wiring

/-!
# The action store and the confirmation write

The store of a round action's read is the confirmation write on the store before it, with the read's
cache written in, stated over a model `M : Record.Model V`.
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
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open Protocol
open Proofs.HealingLemmas

/-- For every world `w` before round `r`'s action time, every node state `n` of `v`'s action read
    from `w`, and every outcome `X` of the confirmation write for round `r`'s opening slot, with the
    grade contract of `n`'s cache, on the store `v`'s tick in `w` gives at that slot's confirmation
    time, `n`'s store is some named store `st` with `n`'s cache written in, and `st`'s core store is
    `X`. -/
theorem Vocabulary.Proofs.HealingSurface.actionStoreAt_eq_update_confirmation_confStore (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    ∀ X, M.update_confirmation_with (M.gradeContract n.cache) S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w v).st.core
          (M.confirmation_time S.E (M.opening_slot S.hc r)))
        ((M.opening_slot S.hc r)) ⇢ X →
    ∃ st : M.NS, n.st = M.store_with_cache st n.cache ∧ st.core = X :=
  Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_eq_update_confirmation_openingConfStore facts S rho v r

end

end DecoupledConsensusModel.Sts.Restated
