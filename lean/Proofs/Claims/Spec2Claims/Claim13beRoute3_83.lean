import Proofs.Claims.Spec2Claims.Claim13beRoute3_76
import Proofs.Claims.Spec2Claims.Claim13bModel_frameGradeRead_attest

/-!
# The anchor of a round

The round-`r` anchor `AnchorAtRound`, the condition `BaseClearFGSourceCompatibleWithAnchorAtRound`
that a clear FG source lies on one chain with it, and two round inequalities over `Nat`.
-/

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every index into an sts execution is valid, so `get_elem_tactic` is answered by `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

section AtRn

open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- For every member `q` of `HonRound S Sched r` and every block `Cfg` that is `q`'s round-`r`
    action FG source, read from `q`'s node state at step `n₀`, if `Cfg` is an ancestor of that
    action read's confirmed block, then `Cfg` and `T` lie on one chain. -/
def BaseClearFGSourceCompatibleWithAnchorAtRound (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (r : Round) (n₀ : Nat) (T : NamedBlock V) : Prop :=
  ∀ q ∈ HonRound S Sched r, ∀ Cfg : Block V,
    actionFGSourceFrom S (x[n₀][q].st) r = some Cfg →
    Block.Preceq Cfg (actionHealingStore S (x[n₀][q].st) r).live_confirmed →
    Block.compatible Cfg T.erase = true

/-- If `1 ≤ X`, then `R + η + 2 + 1 ≤ R + η + 1 + (1 + X)`. -/
theorem deadline_three_l83 (R η X : Nat) (hX : 1 ≤ X) : R + η + 2 + 1 ≤ R + η + 1 + (1 + X) := by
  omega

/-- `1 ≤ (D + K + 5) · (7 · g + 22 + 4 · e)`. -/
theorem lag_pos_l83 (D K g e : Nat) : 1 ≤ (D + K + 5) * (7 * g + 22 + 4 * e) :=
  Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

/-- `T` is a round-`r` anchor: for some validator `v`, some step `N` with `S.a r ≤ x[N].time ≤ tE`
    and some tick step `n₀` at `S.a r`, `T` is the checkpoint of a `NamedHeightRegimeRunOn` regime
    over the run of the first `N` steps with the validators not held at `x[N].time` as honest, from
    base round `roundAt S tGAT + η_SG + 2`, whose seed round is at most `r`, and
    `topHonestRow S Sched x n₀` is at most `T`'s chain-state height. -/
def AnchorAtRound (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (tGAT tE : Int) (r : Round) (T : NamedBlock V) : Prop :=
  ∃ (v : V) (N n₀ : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V) (ta : Int)
    (Cfg Tprev : NamedBlock V) (c0 : Round),
    tickStepAt x n₀ (S.a r) ∧ S.a r ≤ (x[N].time : Int) ∧ (x[N].time : Int) ≤ tE ∧
    NamedHeightRegimeRunOn (Setup.alwaysAwake S)
      ({ runAll S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Run V)
      (notHeldAt Sched) Finset.univ Finset.univ
      (roundAt S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 ∧
    a.round ≤ r ∧
    topHonestRow S Sched x n₀ ≤ (Protocol.derive_named S.E S.cfg T).h

end AtRn

end DecoupledConsensusModel.Sts
