import Proofs.Claims.Spec2Claims.Claim13bK_ProposalVotesPivot
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG2
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_initial_inclG2
import Proofs.Claims.Spec2Claims.Claim13bModel_Store_pool
import Proofs.Claims.Spec2Claims.Claim13bK_ProposalAdoption
import Proofs.Claims.Spec2Claims.Claim13bModel_propose_block_with_inclG2
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_view
import Proofs.Claims.Spec2Claims.Claim13bModel_proposer_view
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_resolved
import Proofs.Claims.Spec2Claims.Claim13bModel_view_freeze
import Proofs.Claims.Spec2Claims.Claim13bModel_Block_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_author
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG2b
import Proofs.Claims.Spec2Claims.Claim13bModel_targets_under
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_erase

/-!
# Slot and instant arithmetic

Arithmetic facts over `Nat` and `Int` about slots and multiples of `4Δ`, and the fact that a slot
starting strictly before another is an earlier slot.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An index into an sts execution is always valid, so `get_elem_tactic` is answered by
    `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## Arithmetic over `Nat` -/

/-- For `1 ≤ a`, the integer cast of `a − 1` is the cast of `a` minus one. -/
theorem nat_sub_one_cast_g2 {a : Nat} (h : 1 ≤ a) : ((a - 1 : Nat) : Int) = (a : Int) - 1 := by
  omega

/-- For `2 ≤ a`, `a − 1` is positive. -/
theorem nat_pos_sub_one_g2 {a : Nat} (h : 2 ≤ a) : 0 < a - 1 := by omega

/-- If `a − 1 ≤ b < a`, then neither `a − 1 < b − 1` nor `b < a − 1`. -/
theorem nat_window_g2 {a b : Nat} (h1 : a - 1 ≤ b) (h2 : b < a) :
    ¬ (a - 1 < b - 1 ∨ b < a - 1) := by omega

/-- No multiple of `4Δ` lies in `[6Δ, 8Δ)`: for `Δ > 0` and `0 ≤ k < 2Δ`, `4Δz = 6Δ + k` is
    impossible. -/
theorem no_four_multiple_g2 {Δ z k : Int} (hd : 0 < Δ) (hk0 : 0 ≤ k) (hk1 : k < 2 * Δ)
    (h : 4 * Δ * z = 6 * Δ + k) : False := by
  rcases le_or_gt z 1 with hz | hz
  · have : Δ * z ≤ Δ * 1 := mul_le_mul_of_nonneg_left hz hd.le
    linarith
  · have hz2 : (2 : Int) ≤ z := hz
    have : Δ * 2 ≤ Δ * z := mul_le_mul_of_nonneg_left hz2 hd.le
    linarith

section Premises

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) (tE : Int)
    (hexec : ExecutionValid S Sched (interface S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : TimeDiverges x)
    (hcatch : CatchUpOnWake S x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + healingLengthη S gap ≤ tE)
    (hsync : SynchronyFromWake S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : roundSleepinessW S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : CommonViewOfFinalizedDescendantsAt S Sched x tGAT)
    (hcs : committeeSleepinessW S Sched tE)
    (hcom : HonestCommittees S Sched (interface S Sched))
    (hw : WakesAtActionInstants S Sched) (hs : SleepsAfterActionInstants S Sched)
    (hrec : strongOpeningsRecurFrom S Sched tGAT tE gap)
    (hprev : ∀ r : Round, rebasedDeadlineRoundW S tGAT gap ≤ r → r ≤ switchRound S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      S.a r ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      NamedHeightRegimeRunOn (Setup.alwaysAwake S)
        ({ runAll S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Run V)
        (notHeldAt Sched) Finset.univ Finset.univ
        (roundAt S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → BasePreviousRoundSGCompatibleWithAnchorAtRound S Sched x v r N T)
    (hclear : ∀ r : Round, rebasedDeadlineRoundW S tGAT gap ≤ r → r ≤ switchRound S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      S.a r ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      NamedHeightRegimeRunOn (Setup.alwaysAwake S)
        ({ runAll S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Run V)
        (notHeldAt Sched) Finset.univ Finset.univ
        (roundAt S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → tickStepAt x n₀ (S.a r) →
      BaseClearFGSourceCompatibleWithAnchorAtRound S Sched x r n₀ T)
    (hB' : BaseJustifiedHighAtSwitchRoundW S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : tickStepAt x n_W (S.a (switchRound S tE)))
    {T_W : NamedBlock V} (hAW : AnchorAtRound S Sched x tGAT tE (switchRound S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      Protocol.vote_time S.E (S.hc.opening_slot (switchRound S tE) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → HonestThrough Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)

include hexec hmono htd hcatch hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec
  hprev hclear hB' hnW hAW hJswitch

end Premises

section

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

/-- A slot whose start is strictly before another's is an earlier slot. -/
theorem slot_lt_of_slotStart_lt_g2 {a b : Slot}
    (h : slotStart S.E.Δ a < slotStart S.E.Δ b) : a < b := by
  have hd := S.E.Δ_pos
  rw [slotStart_closed, slotStart_closed] at h
  by_contra hcon
  have hle : ((b : Nat) : Int) ≤ ((a : Nat) : Int) := by exact_mod_cast Nat.le_of_not_lt hcon
  have : 4 * S.E.Δ * ((b : Nat) : Int) ≤ 4 * S.E.Δ * ((a : Nat) : Int) :=
    mul_le_mul_of_nonneg_left hle (by linarith)
  linarith

end

section PremisesViews

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) (tE : Int)
    (hexec : ExecutionValid S Sched (interface S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : TimeDiverges x)
    (hcatch : CatchUpOnWake S x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + healingLengthη S gap ≤ tE)
    (hsync : SynchronyFromWake S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hmult : AwakeAtMultiples S Sched) (hcv : CommonViewOfFinalizedDescendantsAt S Sched x tGAT)
    (hcs : committeeSleepinessW S Sched tE)
    (hw : WakesAtActionInstants S Sched)
    {n_W : Nat} (hnW : tickStepAt x n_W (S.a (switchRound S tE)))

include hexec hmono htd hcatch hgst hlen hsync hthird hphase hmult hcv hcs hw hnW

set_option linter.unusedSectionVars false

end PremisesViews

end DecoupledConsensusModel.Sts
