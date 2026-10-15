module
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedOutageEntry
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.NamedActionReads

@[expose] public section

/-!
# Honest round voters and the confirmation read

The honest voters of a round and of older rounds, the weight inequality `GradeFormingMajority`, and
the confirmation and action reads.
-/
namespace DecoupledConsensusModel.Internal.NamedOutageEntry
open Execution DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Whether `v` emitted its round-`k` attestation at a tick at the action time of round `k`. -/
def emittedInRound (S : Setup V) (rho : NamedRun V) (v : V) (k : Round) : Bool :=
  (List.range rho.events.length).any (fun i =>
    match rho.events[i]? with
    | some (.tick u t) =>
      if u = v ∧ t = S.a k then
        (NamedRun.emittedAt S rho i v t).any (fun o =>
          match o with
          | .attest a => decide (a.val_index = v ∧ a.round = k)
          | _ => false)
      else false
    | _ => false)

def honestRoundVoters (S : Setup V) (rho : NamedRun V) (k : Round) : Finset V :=
  rho.honest.filter (fun v => emittedInRound S rho v k)

/-- The honest voters of the rounds from `r − η_SG` to `r − 2`. -/
def historicalHonestVoters (S : Setup V) (rho : NamedRun V) (r : Round) : Finset V :=
  ((Finset.range r).filter (fun k => r - S.hc.η_SG ≤ k ∧ k + 1 < r)).biUnion
    (fun k => honestRoundVoters S rho k)

/-- The voters of `historicalHonestVoters` that did not vote in round `r − 1`. -/
def staleHistoricalVoters (S : Setup V) (rho : NamedRun V) (r : Round) : Finset V :=
  historicalHonestVoters S rho r \ honestRoundVoters S rho (r - 1)

/-- The weight of the faulty validators together with `staleHistoricalVoters` is less than the
    weight of the honest voters of round `r − 1`. -/
def GradeFormingMajority (S : Setup V) (rho : NamedRun V) (r : Round) : Prop :=
  S.E.electorate.weightOf ((Finset.univ \ rho.honest) ∪
      staleHistoricalVoters S rho r) <
    S.E.electorate.weightOf (honestRoundVoters S rho (r - 1))


/-- `v`'s confirmation read at `t`. -/
def confirmationReadAt (S : Setup V) (rho : NamedRun V) (v : V) (t : Time) :
    NamedNodeState V :=
  Execution.NamedActionReads.confirmationReadAt S rho v t


def preparedCache (S : Setup V) (before : NamedNodeState V) (t : Time) : Cache V :=
  Execution.NamedActionReads.preparedCache S before t

def actionReadFrom (S : Setup V) (before : NamedNodeState V) (r : Round) :
    NamedNodeState V :=
  Execution.NamedActionReads.actionReadFrom S before r

end DecoupledConsensusModel.Internal.NamedOutageEntry

end
