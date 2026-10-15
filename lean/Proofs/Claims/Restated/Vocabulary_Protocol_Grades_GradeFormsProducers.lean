import Proofs.Vocabulary.Protocol.Grades.GradeFormsProducers
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_FinalizedViable
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_JointHistoryProducers
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_FrozenRootOrder
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Record.Wiring

/-!
# The FG root and the grade-2 candidate of a read

The FG root is in the filtered block tree of every store before a time, and the grade-2 candidate of
an action read comes from a G2 root the same validator froze earlier, stated over a model
`M : Record.Model V`.
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
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades DecoupledConsensusModel.Protocol

/-- In every world `w₁` before time `t`, the FG root of `v`'s FG view is in its filtered block tree. -/
theorem Vocabulary.Proofs.HealingSurface.named_fgRoot_mem_filtered_stateBeforeTime (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t, 
    M.get_fg_root
        (M.toHealing (w₁ v).st.core).toFG ∈
      M.get_filtered_block_tree
        (M.toHealing (w₁ v).st.core).toFG := by
  intro w₁ hw₁
  by_cases hgate : (w₁ v).st.core.h_max = (w₁ v).st.core.h_j + 1
  · exact Restated.Vocabulary.Proofs.NamedOutageClosure.justifiedRoot_mem_filtered facts S rho t v
      w₁ hw₁ hgate
  · have hroot : M.get_fg_root (M.toHealing (w₁ v).st.core).toFG = (w₁ v).st.core.F :=
      facts.fc.get_fg_root_toHealing_of_ne (w₁ v).st.core hgate
    rw [hroot]
    exact Restated.Vocabulary.Proofs.finalizedViable_mem_filtered facts hroot
      (Restated.Vocabulary.Proofs.NamedFinalizedViable.finalizedViable_stateBeforeTime facts S rho t v
        w₁ hw₁)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades DecoupledConsensusModel.Protocol

/-- For every world `w₁` before event `i` of `rho` and every node state `n` of the round-`r` action
    read from `v`'s node state in `w₁`, if the grade-2 block on `n` can be `B`, then some event `j`
    before event `i` is `v`'s tick at `M.domain S.E S.hc r .g2`, and some world `w` before event
    `j`, from which the events `j` to `i - 1` of `rho` can lead to `w₁`, has every outcome of the G2
    root frozen from `v`'s store for round `r` equal to `some raw`, with `B` an ancestor of `raw`. -/
theorem Vocabulary.Proofs.HealingSurface.contractQ2_capture_at_action_index (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) (r : Round) {B : Block V} :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w₁ v) r,
    M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core) r ⇢ some B →
    ∃ j raw, j < i ∧
      rho.events[j]? = some (.tick v (M.domain S.E S.hc r .g2)) ∧
      ∃ w ∈ Record.stateBeforeOf M S rho j,
      w₁ ∈ ((rho.events.drop j).take (i - j)).foldlM (Record.worldStepOf M S) w ∧
      (∀ fr : Option (Block V), M.freezeRoot S.E
        (M.gradeView (M.toHealing (w v).st.core))
        (w v).st.core.F S.hc.η_SG r
        (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) ⇢ fr → fr = some raw) ∧
      Block.Preceq B raw :=
  fun w₁ hw₁ n hn hQ =>
    Restated.Vocabulary.Proofs.NamedOutageHistory.JointHistoryProducersTime.q2_capture_at_action_read facts
      S rho i v r w₁ hw₁ n hn hQ

end

end DecoupledConsensusModel.Sts.Restated
