module
public import Proofs.Vocabulary.Internal.Legacy.Assumptions.Weight
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Admissible

@[expose] public section

/-!
# Asynchronous period and awake participation

The accountable bound, the execution premises of one asynchronous period `[b0, b1]`, and the
awake-weight condition `AwakeGradeMajority`.
-/
namespace DecoupledConsensusModel.Internal.NamedOutageEntry
open Execution DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]


/-- The accountable bound `Execution.SlashableBound` over a named run. -/
abbrev SlashableBound (S : Setup V) (rho : NamedRun V) : Prop :=
  Execution.SlashableBound S rho

/-- One asynchronous period `[b0, b1]` inside the run's horizon: a valid execution under partial
    synchrony, healthy delivery through `b0`, GST no later than `b1`, and `b0` a public time. -/
structure OutageExecution (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) : Prop where
  execution : Execution.ExecutionValid S rho
  synchrony : Execution.PartialSynchrony S rho
  interval : 0 ≤ b0 ∧ b0 ≤ b1 ∧ b1 ≤ rho.horizon
  healthy : NamedHealthyPrefixDelivery S rho b0
  
  gst : S.E.t_GST ≤ b1
  
  boundaryPublic : Execution.PublicTime S b0

def RoundCovered (S : Setup V) (rho : NamedRun V) (r : Round) : Prop :=
  (0 ≤ S.a r ∧ S.a r ≤ rho.horizon) ∨
    ∃ p : Phase, 0 ≤ domain S.E S.hc r p ∧ domain S.E S.hc r p ≤ rho.horizon

/-- The honest validators awake at round `k`. -/
def honestAwakeAt (S : Setup V) (rho : NamedRun V) (k : Round) : Finset V :=
  rho.honest.filter (fun v => (S.node v).awake k)

/-- The honest validators awake at some round from `r − η_SG` to `r − 2` but not at `r − 1`. -/
def staleAwake (S : Setup V) (rho : NamedRun V) (r : Round) : Finset V :=
  (((Finset.range r).filter (fun k => r - S.hc.η_SG ≤ k ∧ k + 1 < r)).biUnion
    (fun k => honestAwakeAt S rho k)) \ honestAwakeAt S rho (r - 1)


/-- The weight of the faulty validators together with `staleAwake` is less than the weight of the
    honest validators awake at round `r − 1`. -/
def AwakeGradeMajority (S : Setup V) (rho : NamedRun V) (r : Round) : Prop :=
  S.E.electorate.weightOf ((Finset.univ \ rho.honest) ∪ staleAwake S rho r) <
    S.E.electorate.weightOf (honestAwakeAt S rho (r - 1))

def AwakeGradeMajorityThroughout (S : Setup V) (rho : NamedRun V) : Prop :=
  ∀ r, 0 < r → RoundCovered S rho r → AwakeGradeMajority S rho r

end DecoupledConsensusModel.Internal.NamedOutageEntry

end
