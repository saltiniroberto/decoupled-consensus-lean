module
public import Model.Vocabulary.Execution.Setup

@[expose] public section

/-!
# The fixed data of a run

`Setup` bundles the environment, the parameters and the node identities. `PublicTime` is the tick
schedule: the natural multiples of `Δ`.
-/

namespace DecoupledConsensusModel
namespace Execution

open Protocol (HeightConfig)

variable {V : Type} [DecidableEq V] [Fintype V]

namespace Setup

variable (S : Setup V)

end Setup


/-- A public time: a natural multiple of `Δ`, an instant at which every honest node ticks. -/
def PublicTime (S : Setup V) (t : Time) : Prop :=
  ∃ k : Nat, t = (k : Time) * S.E.Δ

/-- The timeout delay is `2 + extraRounds` rounds; the default `extraRounds = 0` gives two rounds. -/
def TimeoutDelayBound (S : Setup V) (extraRounds : Nat := 0) : Prop :=
  S.cfg.timeoutDelay = (2 + extraRounds) * S.hc.R

namespace Setup

def extraRounds (S : Setup V) : Nat := S.cfg.timeoutDelay / S.hc.R - 2

theorem timeoutDelayBound (S : Setup V) : TimeoutDelayBound S S.extraRounds := by
  unfold TimeoutDelayBound extraRounds
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le (by decide : 0 < 3) S.hc.R_ge_three
  have hquot : 2 ≤ S.cfg.timeoutDelay / S.hc.R :=
    (Nat.le_div_iff_mul_le hRpos).2 S.timeout_rounds.2
  have hdiv : S.cfg.timeoutDelay =
      (S.cfg.timeoutDelay / S.hc.R) * S.hc.R :=
    (Nat.div_mul_cancel S.timeout_rounds.1).symm
  have hsum : 2 + (S.cfg.timeoutDelay / S.hc.R - 2) =
      S.cfg.timeoutDelay / S.hc.R := by
    omega
  calc
    S.cfg.timeoutDelay = (S.cfg.timeoutDelay / S.hc.R) * S.hc.R := hdiv
    _ = (2 + (S.cfg.timeoutDelay / S.hc.R - 2)) * S.hc.R := by rw [hsum]

end Setup

end Execution
end DecoupledConsensusModel

end
