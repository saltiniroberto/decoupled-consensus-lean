import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The hand-over facts

The facts about an execution, at the ticks of rounds `r` and `r + 1`, that place honest
attestations, height votes and store blocks relative to a block `P`, stated over a model
`M : Record.Model V`.
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

/-- Facts about the execution `x` up to the tick at round `r + 1`'s action instant that place the
    honest attestations, the height votes and the finalized and justified blocks of honest stores
    relative to the block `P`. -/
structure StableHandover (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Nat) (P : Block V) : Prop where
  /-- Every round-`r` or round-`(r + 1)` attestation computed at that round's tick by a validator
      awake throughout the round's attester window and honest through the step after the tick names
      a block `C` with `P ⪯ C`. -/
  covers : ∀ ρ : Nat, (ρ = r ∨ ρ = r + 1) → ∀ n : Nat, Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ)) →
    ∀ u ∈ Restated.activeRoundW M S Sched ρ, Restated.HonestThrough M Sched x (n + 1) u →
    ∀ C : NamedBlock V, C ∈ (x[n + 1][u].st).st.bodies →
    ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][u].st) u ρ,
      a.confirmed = some C.root →
      Block.Preceq P C.erase
  /-- Every height vote in the sent log right after the round-`(r + 1)` tick, signed by a validator
      honest through that step, is bound to a root whose blocks on the wire are ancestors or
      descendants of `P`, or is for a height less than every honest store's justified height at that
      step. -/
  entries : ∀ n : Nat, Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
    ∀ (u : V) (a : NamedAttestation V) (h : Height) (root : BlockId) (tmo : Bool),
    Restated.HonestThrough M Sched x (n + 1) u → a.val_index = u →
    (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
    a.height_pair = NamedHeightPair.vote h root tmo →
    ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = root →
      Block.Compatible P C.erase ∨
        ∀ w : V, Restated.HonestThrough M Sched x (n + 1) w → h < (x[n + 1][w].st).st.core.h_j
  /-- Right after the round-`(r + 1)` tick, every honest store's finalized block and justified block
      are each an ancestor or a descendant of `P`. -/
  roots : ∀ n : Nat, Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
    ∀ w : V, Restated.HonestThrough M Sched x (n + 1) w →
      Block.Compatible P (x[n + 1][w].st).st.core.F ∧
      Block.Compatible P (x[n + 1][w].st).st.core.J

end

end DecoupledConsensusModel.Sts.Restated
