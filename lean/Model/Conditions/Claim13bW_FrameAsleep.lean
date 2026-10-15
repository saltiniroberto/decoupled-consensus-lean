import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Phase results written while awake

The condition `FramePhaseAwake` on a validator's cache, stated over a model `M : Record.Model V`.
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

/-- Whenever the cache `c` holds `some (some root)` for a round `r₁` and a phase `p`, `v` is awake
    at that phase's domain time. -/
def FramePhaseAwake (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (v : V) (c : M.Cache) : Prop :=
  ∀ (r₁ : Round) (p : Protocol.Phase) (root : Block V),
    M.phaseResult (M.cacheAtRound c r₁) p = some (some root) →
      v ∈ Sched.awake (M.domain S.E S.hc r₁ p)

end

end DecoupledConsensusModel.Sts.Restated
