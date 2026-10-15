import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Interface
import Model.Record.Wiring

/-!
# A justified block of smaller height than the anchor's

The condition `StepJustifiedRootUnderAnchor`, stated over a model `M : Record.Model V`.
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

/-- At every step `n₁` from `n + 1` to `n'`, for every validator `v` honest through it: if `v`'s
    running height maximum is one more than its justified height and that justified height is less
    than the anchor's, then `v`'s justified block is an ancestor of the anchor `T`. -/
def StepJustifiedRootUnderAnchor (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) (n n' : Nat) (T : NamedBlock V) : Prop :=
  ∀ (v : V) (n₁ : Nat), n + 1 ≤ n₁ → n₁ ≤ n' → Restated.HonestThrough M Sched x n₁ v →
    (x[n₁][v].st).st.core.h_max = (x[n₁][v].st).st.core.h_j + 1 →
    (x[n₁][v].st).st.core.h_j < (M.derive_named S.E S.cfg T).h →
    Block.Preceq (x[n₁][v].st).st.core.J T.erase

end

end DecoupledConsensusModel.Sts.Restated
