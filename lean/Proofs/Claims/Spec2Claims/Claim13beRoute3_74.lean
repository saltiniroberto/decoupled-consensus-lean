import Proofs.Claims.Spec2Claims.Claim13beRoute3_72

/-!
# Previous-round SG compatibility with the checkpoint

The condition `BasePreviousRoundSGCompatibleWithAnchorAtRound` on the round-`(r − 1)` SG blocks, and
two round inequalities over `Nat`.
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

section AtRn

open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- In `R_N`, every validator not held at `S.a (r − 1)` that emits its round-`(r − 1)` attestation
    has its SG block on one chain with `T`'s erasure. -/
def BasePreviousRoundSGCompatibleWithAnchorAtRound (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (v : V) (r : Round) (N : Nat) (T : NamedBlock V) :
    Prop :=
  HonestSGEmissionsCompatibleAtRoundOn (Setup.alwaysAwake S)
    ({ runAll S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Run V)
    (notHeldAt Sched) (r - 1) T.erase

/-- If `a ≤ r`, then `a + 1 ≤ r − 1`, or `a = r − 1`, or `a = r`. -/
theorem round_cases_l74 (a r : Nat) (h : a ≤ r) : a + 1 ≤ r - 1 ∨ a = r - 1 ∨ a = r := by
  omega

/-- If `0 < a` and `a ≤ r`, then `a − 1 ≤ r − 1` and `1 ≤ r`. -/
theorem pred_le_pred_pos_l74 (a r : Nat) (ha : 0 < a) (h : a ≤ r) : a - 1 ≤ r - 1 ∧ 1 ≤ r := by
  omega

end AtRn

end DecoupledConsensusModel.Sts
