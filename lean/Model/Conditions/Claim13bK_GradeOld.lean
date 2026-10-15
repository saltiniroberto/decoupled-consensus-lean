import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_GradeOld

/-!
# The SG blocks of a round in the trees of the next round's readers

The condition `FreshSGHeadsAtLate`, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every honest active attester `v` of round `r + 1`, every phase of round `r + 1` whose domain
    time is no later than `S.a (r + 1)`, the last step `m` before that time, every member `v_1` of
    `freshAttestersW` for round `r` at step `m`, and every round-`r` attestation `a` that `v_1`'s
    action can compute from its node state at step `n`: the block `a` names, held by `v_1` at step
    `n + 1`, is in `v`'s tree at `m` under its root, stamped before the phase's late cutoff, and
    compatible with `v`'s finalized block at `m`. -/
def FreshSGHeadsAtLate (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (r : Round) (n : Nat) : Prop :=
  ∀ v ∈ Restated.HonRound M S Sched (r + 1),
  ∀ p : Protocol.Phase, M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) →
  ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p) →
  ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m, ∀ C : NamedBlock V,
    C ∈ (x[n + 1][v_1].st).st.bodies →
    ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
    a.confirmed = some C.root →
    Block.find? (x[m][v].st).st.core.T C.root = some C.erase ∧
    stampedBefore (x[m][v].st).st.core.timestamp_block
      (M.late S.E S.hc (r + 1) p) C.erase = true ∧
    Block.compatible C.erase (x[m][v].st).st.core.F = true

end

end DecoupledConsensusModel.Sts.Restated
