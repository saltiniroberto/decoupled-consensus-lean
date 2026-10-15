import Proofs.Vocabulary.Protocol.Grades.Interpolation
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# The anchor and the frame result after a phase tick

The FG root is an ancestor of every SG anchor, and the phase tick at a time keeps the frame results
of that time's round, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage
open DecoupledConsensusModel.Protocol
set_option linter.unusedSectionVars false

/-- The FG root of `st` is an ancestor of, or is, every outcome `a` of the SG anchor at round `r`
    with the grade-1 input `g1`. -/
theorem Vocabulary.Proofs.NamedOutageClosure.fg_root_preceq_anchor (facts : Record.Facts M) (E : Env V) (hc : Protocol.HealConfig)
    (st : M.HS) (r : Round) (g1 : Option (Option (Block V))) :
    ∀ a, M.anchor E hc st r g1 ⇢ a → Block.Preceq (M.get_fg_root st.toFG) a :=
  facts.gr.preceq_anchor_of_fgRoot E hc st r g1 (Proofs.ModelProperties.Preceq_self _)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage
open DecoupledConsensusModel.Protocol
set_option linter.unusedSectionVars false

/-- For every world `w₁` before time `u`, if the frame `v`'s node state in `w₁` reads for round `r`
    has the result `root` at phase `p`, and `u`'s slot is in round `r`, then for every outcome `c`
    of the phase tick at `u` on that node state, the frame `c` reads for round `r` on that store
    with its clock set to `u` has the same result. -/
theorem Vocabulary.Proofs.NamedOutageClosure.frame_phase_prepared_eq (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V) (r : Round)
    (p : Phase) (u : Time) (hround : (M.round_of S.hc (S.E.slotOf u)) = r)
    (root : Option (Block V)) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho u,
    M.phaseResult (M.readFrame (w₁ v).cache (M.toHealing (w₁ v).st.core) r) p = some root →
    ∀ c, M.onPhaseTick S.E S.hc (w₁ v).st.core.toHealing u (w₁ v).cache ⇢ c →
    M.phaseResult (M.readFrame c (M.toHealing (M.ns_setClock S.E (w₁ v).st u).core) r) p =
      some root :=
  facts.grRun.frame_phase_prepared_eq_of_outcomes S rho v r p u hround root

end

end DecoupledConsensusModel.Sts.Restated
