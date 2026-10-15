import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_72

/-!
# Honest height rows and the deadline round

The honest height rows of the sent log, the highest of them, and the deadline round, stated over a
model `M : Record.Model V`.
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
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Some validator, honest through some step `n' ≤ n₀ + 1`, has in the sent log `x[n'].sent` an
    attestation signed by itself whose height pair is a vote at height `h`. -/
def HonestRowAt (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (n₀ : Nat) (h : Height) : Prop :=
  ∃ (v : V) (n' : Nat) (a : NamedAttestation V) (entry : BlockId) (tmo : Bool),
    n' ≤ n₀ + 1 ∧ Restated.HonestThrough M Sched x n' v ∧ a.val_index = v ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n'].sent ∧
      a.height_pair = NamedHeightPair.vote h entry tmo

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
open Classical

/-- The highest height `h` with `HonestRowAt M S Sched x n₀ h`, searched up to the largest `Σ.h_max`
    any validator holds after `n₀ + 1` steps; it is `0` when there is none. -/
noncomputable def topHonestRow (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (n₀ : Nat) : Height :=
  Nat.findGreatest (Restated.HonestRowAt M S Sched x n₀)
    ((Finset.univ : Finset V).sup fun w : V => (x[n₀ + 1][w].st).st.core.h_max)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- The deadline round: `roundAt S tGAT + η_SG + 1 + (1 + (D + K + 5) · L)`, with
    `L = progressLag' gap S.extraRounds`. -/
noncomputable def deadlineRoundW (M : Record.Model V) (S : Setup V) (tGAT : Int) (gap : Nat) : Round :=
  Restated.roundAt M S tGAT + S.hc.η_SG + 1 +
    (1 + (S.cfg.D + S.cfg.K + 5) * Proofs.HealingSurface.progressLag' gap S.extraRounds)

end

end DecoupledConsensusModel.Sts.Restated
