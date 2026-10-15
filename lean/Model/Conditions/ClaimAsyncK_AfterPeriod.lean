import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.ClaimAsyncK_AfterPeriod

/-!
# The round invariant after the period

The round invariant at a round `ρ` after the period, stated over a model `M : Record.Model V`.
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
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- At the tick step at `S.a ρ`, every validator awake at every instant of round `ρ`'s attester
    window and honest through the step after the tick computes only round-`ρ` attestations that name
    `P` or a descendant of `P`, and whose height pair, when it is a vote, is bound to a root whose
    blocks on the wire are ancestors or descendants of `P`. -/
def RoundAttestsAll (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (P : Block V) (ρ : Nat) : Prop :=
  ∀ n : Nat, Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ)) →
    ∀ u ∈ Restated.activeRoundW M S Sched ρ, Restated.HonestThrough M Sched x (n + 1) u →
    ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][u].st) u ρ,
      (∀ C : NamedBlock V, C ∈ (x[n + 1][u].st).st.bodies →
          a.confirmed = some C.root →
          Block.Preceq P C.erase) ∧
      (∀ (h : Height) (root : BlockId) (tmo : Bool),
          a.height_pair = NamedHeightPair.vote h root tmo →
          ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = root →
            Block.Compatible P C.erase)

end

end DecoupledConsensusModel.Sts.Restated
