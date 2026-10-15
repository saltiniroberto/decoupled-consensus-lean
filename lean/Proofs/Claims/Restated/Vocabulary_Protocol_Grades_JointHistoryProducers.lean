import Proofs.Vocabulary.Protocol.Grades.JointHistoryProducers
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_CacheProvenance
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_CacheProvenance
import Model.Record.Wiring

/-!
# The grade-2 candidate of an action read

The grade-2 block of an action read is an ancestor of a G2 root the same validator froze at an
earlier event, stated over a model `M : Record.Model V`.
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
open DecoupledConsensusModel.Proofs.NamedOutageHistory
open DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryProducersTime
open Execution Internal.NamedOutageEntry Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

/-- For every world `w₁` before event `i` of `rho` and every node state `n` of the round-`r` action
    read from `v`'s node state in `w₁`, if the grade-2 block on `n` can be `q`, then some event `j`
    before event `i` is `v`'s tick at `M.domain S.E S.hc r .g2`, and some world `w` before event
    `j`, from which the events `j` to `i - 1` of `rho` can lead to `w₁`, has every outcome of the G2
    root frozen from `v`'s store for round `r` equal to `some raw`, with `q` an ancestor of `raw`. -/
theorem Vocabulary.Proofs.NamedOutageHistory.JointHistoryProducersTime.q2_capture_at_action_read (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (i : Nat) (v : V) (r : Round) {q : Block V} :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    ∀ n ∈ Restated.Vocabulary.Internal.NamedOutageEntry.actionReadFrom M S (w₁ v) r,
    M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core) r ⇢ some q →
    ∃ (j : Nat) (raw : Block V),
      j < i ∧
      rho.events[j]? = some (.tick v (M.domain S.E S.hc r .g2)) ∧
      ∃ w ∈ Record.stateBeforeOf M S rho j,
      w₁ ∈ ((rho.events.drop j).take (i - j)).foldlM (Record.worldStepOf M S) w ∧
      (∀ fr : Option (Block V), M.freezeRoot S.E (M.gradeView (M.toHealing (w v).st.core))
        (w v).st.core.F S.hc.η_SG r
        (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) ⇢ fr → fr = some raw) ∧
      Block.Preceq q raw := by
  intro w₁ hw₁ n hn hQ
  obtain ⟨c, hc, st, hst, rfl⟩ := hn
  exact facts.grRun.q2_capture_at_action_read S rho i v r q w₁ hw₁ c hc st hst hQ

end

end DecoupledConsensusModel.Sts.Restated
