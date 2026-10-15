import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Claims.Restated.RunAll
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Proofs.Claims.Spec2Claims.Claim13bStepSGMove
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Constants
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_83

/-!
# Clear FG sources and anchors at a round

The condition that a clear FG source at a round `r` lies on one chain with the anchor, and the
anchors of a round, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- For every member `q` of `HonRound S Sched r`, every round-`r` action read `n` computed from
    `q`'s node state at step `n₀`, and every block `Cfg` the action FG source at `n` can return, if
    `Cfg` is an ancestor of the confirmed block of `n`'s store, then `Cfg` and `T` lie on one chain. -/
def BaseClearFGSourceCompatibleWithAnchorAtRound (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) (n₀ : Nat) (T : NamedBlock V) : Prop :=
  ∀ q ∈ Restated.HonRound M S Sched r,
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (x[n₀][q].st) r,
    ∀ Cfg : Block V,
    Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) n ⇢ some Cfg →
    Block.Preceq Cfg (M.toHealing n.st.core).live_confirmed →
    Block.compatible Cfg T.erase = true

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- `T` is a round-`r` anchor: for some validator `v`, some step `N` with `S.a r ≤ x[N].time ≤ tE`
    and some tick step `n₀` at `S.a r`, `T` is the checkpoint of a regime of the run named by `v`
    and `N`, read along the path of that run that `x` follows, whose seed round is at most `r`, and
    `topHonestRow S Sched x n₀ ≤ h(T)`. -/
def AnchorAtRound (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (r : Round) (T : NamedBlock V) : Prop :=
  ∃ (v : V) (N n₀ : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V) (ta : Int)
    (Cfg Tprev : NamedBlock V) (c0 : Round),
    Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) ∧ (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) ∧ (x[N].time : Int) ≤ tE ∧
    Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 ∧
    a.round ≤ r ∧
    Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h

end

end DecoupledConsensusModel.Sts.Restated
