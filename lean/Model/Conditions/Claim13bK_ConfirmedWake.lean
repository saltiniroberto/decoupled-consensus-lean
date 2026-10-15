import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bK_ConfirmedRecord
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedWake

/-!
# The latest stable and confirmed blocks at the round after the switch round

The conditions `FramePhaseAwakeProvenance` on a cache's phase results and
`RecordsSettledAtSettleTick`, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- Whenever the cache `c` holds `some (some root)` for a round `r₁` and a phase `p`, the schedule
    has `v` awake at that phase's domain time of round `r₁`. -/
def FramePhaseAwakeProvenance (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (v : V)
    (c : M.Cache) : Prop :=
  ∀ (r₁ : Round) (p : Protocol.Phase) (root : Block V),
    M.phaseResult (M.cacheAtRound c r₁) p = some (some root) →
    v ∈ Sched.awake (M.domain S.E S.hc r₁ p)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- For every round `r` after the switch round, every tick step `n` at round `r`'s action time, and
    every validator `v` not held by the adversary at that time, if `r` is the round after the switch
    round, then `v`'s `latest_stable` and `latest_confirmed` after `n + 1` steps are ancestors of
    every honest head from slot `slot(S.a r) + 2` on. -/
def RecordsSettledAtSettleTick (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) : Prop :=
  ∀ (r : Round) (n : Nat) (v : V), Restated.switchRound M S tE + 1 ≤ r →
    Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r)) →
    v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)) →
    r = Restated.switchRound M S tE + 1 →
    Restated.RecordsAncestorOfHonestHeads M S Sched x v (n + 1)

end

end DecoupledConsensusModel.Sts.Restated
