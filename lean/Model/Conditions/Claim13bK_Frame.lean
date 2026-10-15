import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bInvariant
import Model.Record.Wiring

/-!
# Where a phase result of a cache comes from

The condition `FramePhaseProvenance`, stated over a model `M : Record.Model V`.
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

/-- For every round `r₁`, phase `p` and block `root` such that the cache `c` holds
    `some (some root)` for `r₁` and `p`, there are a step `m`, the last one before that phase's
    domain time, and a block `B` with `root ⪯ B` such that every outcome of the grade test of `B` on
    `v`'s store after `m` steps, with that phase's cutoffs, is `true`. -/
def FramePhaseProvenance (M : Record.Model V) (S : Setup V) {Sched : Schedule V} (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (c : M.Cache) : Prop :=
  ∀ (r₁ : Round) (p : Protocol.Phase) (root : Block V),
    M.phaseResult (M.cacheAtRound c r₁) p = some (some root) →
    ∃ (m : Nat) (B : Block V), Restated.stepBeforeInstant M x m (M.domain S.E S.hc r₁ p) ∧
      (∀ b : Bool, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
        (x[m][v].st).st.core.F S.hc.η_SG r₁ (M.early S.E S.hc r₁ p)
        (M.late S.E S.hc r₁ p) B ⇢ b → b = true) ∧
      Block.Preceq root B

end

end DecoupledConsensusModel.Sts.Restated
