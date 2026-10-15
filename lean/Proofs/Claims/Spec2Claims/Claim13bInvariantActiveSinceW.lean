import Proofs.Claims.Spec2Claims.Claim13beRoute3_83
import Proofs.Claims.Spec2Claims.Claim13bK_ConeChain
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclG1

/-!
# The re-based deadline round

`rebasedDeadlineRoundW S tGAT gap` is the round `gap + 1` rounds after `deadlineRoundW S tGAT gap`,
and `BaseJustifiedHighAtSwitchRoundW` says that at the switch round's tick every honest store's
justified height is at least the height of an anchor at that round. The file also holds the round
arithmetic over `Nat` they use.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An index into an sts execution is always valid, so `get_elem_tactic` is answered by
    `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

section AtRn

open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-! ## The re-based deadline round -/

/-- `d ≤ d + g + 1`, over `Nat`. -/
theorem rebased_nat_le_l0W (d g : Nat) : d ≤ d + g + 1 := by omega

/-- If `d + 2L + 2 = c` and `c + g ≤ w`, then `d + g + 1 ≤ w`, over `Nat`. -/
theorem rebased_nat_le_switch_l0W (d L g c w : Nat) (hs : d + 2 * L + 2 = c) (hη : c + g ≤ w) :
    d + g + 1 ≤ w := by omega

/-- If `d + g + 1 ≤ w`, then `d + g ≤ w`, over `Nat`. -/
theorem rebased_nat_gap_l0W (d g w : Nat) (h : d + g + 1 ≤ w) : d + g ≤ w := by omega

/-- If `c ≤ d + g`, then `c + 1 ≤ d + g + 1`, over `Nat`. -/
theorem rebased_nat_window_l0W (d g c : Nat) (h : c ≤ d + g) : c + 1 ≤ d + g + 1 := by omega

/-- The round `gap + 1` rounds after the deadline round `deadlineRoundW S tGAT gap`. -/
noncomputable def rebasedDeadlineRoundW (S : Setup V) (tGAT : Int) (gap : Nat) : Round :=
  deadlineRoundW S tGAT gap + gap + 1

set_option linter.unusedVariables false in
/-- For every anchor `T_D'` at the round `rebasedDeadlineRoundW S tGAT gap`, every step `n_W` that
    is the tick at the switch round's action instant, and every validator `v` honest through `n_W`,
    the justified height `v`'s store holds after `n_W` steps is at least the chain-state height of
    `T_D'`. -/
def BaseJustifiedHighAtSwitchRoundW (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tGAT tE : Int) (gap : Nat) : Prop :=
  ∀ T_D' : NamedBlock V,
    AnchorAtRound S Sched x tGAT tE (rebasedDeadlineRoundW S tGAT gap) T_D' →
    ∀ n_W : Nat, tickStepAt x n_W (S.a (switchRound S tE)) →
    ∀ v : V, HonestThrough Sched x n_W v →
      (Protocol.derive_named S.E S.cfg T_D').h ≤ (x[n_W][v].st).st.core.h_j

end AtRn

end DecoupledConsensusModel.Sts
