import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Proofs.Claims.Spec2Claims.Claim13bStepSGMove
import Model.Record.Wiring

/-!
# Clear FG sources at the switch round

The condition that a clear FG source at the switch round lies on one chain with the anchor, stated
over a model `M : Record.Model V`.
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

/-- For every member `q` of `HonRound` at the switch round, every round-`rW` action read `n`
    computed from `q`'s node state at step `n₀`, and every block `Cfg` the action FG source at `n`
    can return, if `Cfg` is an ancestor of the confirmed block of `n`'s store, then `Cfg` and `T`
    lie on one chain. -/
def BaseClearFGSourceCompatibleWithAnchor (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (n₀ : Nat) (T : NamedBlock V) : Prop :=
  ∀ q ∈ Restated.HonRound M S Sched (Restated.switchRound M S tE),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (x[n₀][q].st) (Restated.switchRound M S tE),
    ∀ Cfg : Block V,
    Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) n ⇢ some Cfg →
    Block.Preceq Cfg (M.toHealing n.st.core).live_confirmed →
    Block.compatible Cfg T.erase = true

end

end DecoupledConsensusModel.Sts.Restated
