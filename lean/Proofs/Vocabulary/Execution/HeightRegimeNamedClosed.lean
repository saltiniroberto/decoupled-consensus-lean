module
public import Proofs.Vocabulary.Protocol.Grades.RecoveryInitialSourceNamedHistory
public import Proofs.Vocabulary.Protocol.Grades.VoterAnchorSourceInputs
public import Proofs.Vocabulary.Protocol.ChainState.Emission
public import Proofs.Vocabulary.Protocol.Grades.RecoveryDelayedSourceSeed
public import Proofs.Vocabulary.Protocol.Duties.Inputs.FGSourceRawGrade

@[expose] public section

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- For every honest attestation whose round action precedes event index `first`, whose height pair
    targets a run block `R` of derived height `blocked`, and whose action's FG confirmation witness
    is `R`: `R` is an ancestor of `T` once some honest reader has `h_max` greater than `blocked` and
    FG root `R`. -/
def NamedOldTargetRootBelowRun
    (S : Setup V) (rho : Run V) (first : Nat) (blocked : Height)
    (T : NamedBlock V) : Prop :=
  ∀ (a : NamedAttestation V) (ta : Time), a.val_index ∈ rho.honest →
    NamedRun.emits S rho a.val_index (Object.attest a) ta →
    strictEventIndex rho (S.a a.round) < first →
    ∀ R : NamedBlock V, RunBlock S rho R →
      (Protocol.derive_named S.E S.cfg R).h = blocked →
      a.height_pair.erase = HeightPair.target blocked R.erase.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
        some R.erase →
      ∀ w ∈ rho.honest, ∀ time : Time,
        blocked < (rho.storeBeforeTime S w time).h_max →
        Protocol.get_fg_root
          (rho.storeBeforeTime S w time).core.toHealing.toFG = R.erase →
        NamedBlock.Preceq R T


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
