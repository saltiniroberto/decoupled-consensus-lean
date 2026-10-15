module
public import Proofs.Vocabulary.Internal.Definitions.NamedCertificates
public import Proofs.Vocabulary.Internal.Definitions.NamedLifecycle
public import Proofs.Vocabulary.Internal.AlignedRound
public import Proofs.Vocabulary.Internal.ModelVocabulary.MajoritySG.ForkChoice
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.NamedBlocks

@[expose] public section

/-!
# Grade-delivery and certificate predicates

The run-level predicates of the healing argument: grade delivery between honest readers
(`HonestGradeDelivery`, `GradeRoundReady`, `gstLagged`), `HonestNoDoubleTarget`, and the certificate
predicates `RunAttestation`, `Certificate`, `ReleasedThrough`, `PermanentlyCrossedFrom` and
`UnreleasedCertificateStaleFrom`.
-/


namespace DecoupledConsensusModel
namespace Internal
namespace HealingSurface

open Execution
open Protocol (GradeView HealConfig)
open Protocol (SGVote)
open PhaseGrades NamedRecoveryRead DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## Grade delivery -/


/-- Delivery by `t + Δ`, between every ordered pair of honest readers, of the sends from the opening
    of round `r`'s G2 support window to its G0 domain read. -/
def HonestGradeDelivery (S : Setup V) (ρ : Run V) (r : Round) : Prop :=
  NamedHealthyWindowDelivery S ρ (early S.E S.hc r .g2) (domain S.E S.hc r .g0)


/-- Rounds of synchrony needed before the first round whose grades can be delivered. -/
def readyLag : Nat := 1

theorem readyLag_pos : 0 < readyLag := by decide


/-- GST shifted by `readyLag` rounds. -/
def gstLagged (S : Setup V) : Time :=
  S.E.t_GST + 4 * S.E.Δ * (S.hc.R * readyLag : Nat)

/-- GST is at most the opening of round `r`'s G2 support window, and round `r`'s G0 domain read is
    within the run's horizon. -/
def GradeRoundReady (S : Setup V) (ρ : Run V) (r : Round) : Prop :=
  S.E.t_GST ≤ early S.E S.hc r .g2 ∧
    domain S.E S.hc r .g0 ≤ ρ.horizon


/-- No honest validator emits two attestations with different targets at the same height, counting
    both the height pair and the finality pair (`targetsAt`). -/
def HonestNoDoubleTarget (S : Setup V) (ρ : Run V) : Prop :=
  ∀ v ∈ ρ.honest, ∀ (a a' : NamedAttestation V) (t t' : Time),
    ρ.emits S v (Object.attest a) t → ρ.emits S v (Object.attest a') t' →
      ∀ (h : Height) (T T' : BlockId),
        T ∈ targetsAt a.erase h → T' ∈ targetsAt a'.erase h → T = T'


/-! ## Certificates -/

/-- An attestation the run puts in play: delivered as an object, or included in a run block's chain. -/
def RunAttestation (S : Setup V) (ρ : Run V) (a : NamedAttestation V) : Prop :=
  Object.attest a ∈ NamedRun.objects ρ ∨
    ∃ B : NamedBlock V, RunBlock S ρ B ∧ a ∈ Protocol.named_chain_attestations B

/-- A height-`h` certificate for target `T`: validators of weight at least `q` signed the vote `h T`
    in attestations the run puts in play. -/
def Certificate (S : Setup V) (ρ : Run V) (h : Height) (T : BlockId) : Prop :=
  ∃ Q : Finset V, S.E.q ≤ S.E.electorate.weightOf Q ∧
    ∀ v ∈ Q, ∃ a : NamedAttestation V, RunAttestation S ρ a ∧
      a.val_index = v ∧ a.height_pair = NamedHeightPair.vote h T false


/-- Some honest store installed `(h, T)` as its justification at a time at most `t`. -/
def ReleasedThrough (S : Setup V) (ρ : Run V) (h : Height)
    (T : BlockId) (t : Time) : Prop :=
  ∃ v ∈ ρ.honest, ∃ u : Time, u ≤ t ∧
    (ρ.storeAt S v u).h_j = h ∧ (ρ.storeAt S v u).J.root = T

/-- At `t`, every honest store has justified height greater than `h`. -/
def HonestStoresCrossedAt (S : Setup V) (ρ : Run V)
    (h : Height) (t : Time) : Prop :=
  ∀ v ∈ ρ.honest, h < (ρ.storeAt S v t).h_j

/-- At every time from `t` to the horizon, every honest store has justified height greater than `h`. -/
def PermanentlyCrossedFrom (S : Setup V) (ρ : Run V)
    (h : Height) (t : Time) : Prop :=
  ∀ u : Time, t ≤ u → u ≤ ρ.horizon →
    ∀ v ∈ ρ.honest, h < (ρ.storeAt S v u).h_j

/-- A certificate for `(h, T)` exists in the run, no honest store installed it by `t`, and every
    honest store stays past height `h` from `t` on. -/
def UnreleasedCertificateStaleFrom (S : Setup V) (ρ : Run V)
    (h : Height) (T : BlockId) (t : Time) : Prop :=
  Certificate S ρ h T ∧ ¬ ReleasedThrough S ρ h T t ∧
    PermanentlyCrossedFrom S ρ h t


end HealingSurface
end Internal
end DecoupledConsensusModel

end
