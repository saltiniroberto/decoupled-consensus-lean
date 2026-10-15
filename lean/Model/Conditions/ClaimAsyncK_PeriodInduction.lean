import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_ClaimStableThroughAsyncPeriod
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.ClaimAsyncK_NoConflictingQuorum

/-!
# The round invariant

The round invariant at a round `ρ`, stated over a model `M : Record.Model V`.
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

/-- At the tick step at `S.a ρ`, every member of `activeRoundWThroughNext S Sched r` honest through
    the step after the tick and awake throughout `[Protocol.early S.E S.hc ρ .g2 − Δ, S.a ρ]`
    computes only round-`ρ` attestations that name `P` or a descendant of `P`, and whose height
    pair, when it is a vote, is bound to a root whose blocks on the wire are ancestors or
    descendants of `P`. -/
def RoundAttestsAbove (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (r : Nat) (P : Block V) (ρ : Nat) : Prop :=
  ∀ n : Nat, Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ)) →
    ∀ u ∈ Restated.activeRoundWThroughNext M S Sched r, Restated.HonestThrough M Sched x (n + 1) u →
    u ∈ Sched.awakeThroughout (M.early S.E S.hc ρ .g2 - S.E.Δ) ((Restated.Vocabulary.Execution.Setup.a M S ρ)) →
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
