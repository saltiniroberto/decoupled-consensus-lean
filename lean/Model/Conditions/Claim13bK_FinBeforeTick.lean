import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Interface
import Model.Record.Wiring

/-!
# A finalized block of smaller height than the anchor's

The condition `StepFinalizedCrossingUnderAnchor`, stated over a model `M : Record.Model V`.
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

/-- Whatever a validator honest through step `n₁` has finalized, at any step `n₁` up to `n + 1`, at
    a recorded height less than the anchor's, is an ancestor of the anchor `T`. -/
def StepFinalizedCrossingUnderAnchor (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) (n : Nat) (T : NamedBlock V) : Prop :=
  ∀ (v : V) (n₁ : Nat), n₁ ≤ n + 1 → Restated.HonestThrough M Sched x n₁ v →
    ((x[n₁][v].st).st.core.σ (x[n₁][v].st).st.core.F).h < (M.derive_named S.E S.cfg T).h →
    Block.Preceq (x[n₁][v].st).st.core.F T.erase

end

end DecoupledConsensusModel.Sts.Restated
