import Proofs.Claims.Spec2Claims.Claim13beRoute3_93
import Proofs.Claims.Spec2Claims.Claim13bK_HjMono
import Proofs.Claims.Spec2Claims.Claim13bModel_targetReady
import Proofs.Claims.Spec2Claims.Claim13bModel_weightOf

/-!
# Round arithmetic for the window steps

Some validator is not held where the adversary holds less than a third of the weight, and the round
and slot inequalities over `Nat` that the window steps read.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

variable {V : Type} [DecidableEq V] [Fintype V]

section Rows

/-- Every index into an sts execution is valid, so `get_elem_tactic` is answered by `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If the adversary holds less than a third of the total weight at every instant up to `tL`, and
    `t ≤ tL`, then some validator is in `notHeldAt Sched t`. -/
theorem exists_notHeld_f2c (S : Setup V) (Sched : Schedule V) {tL t : Int}
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (ht : t ≤ tL) : ∃ u : V, u ∈ notHeldAt Sched t := by
  by_contra hne
  push Not at hne
  have huniv : Sched.adv t = Finset.univ :=
    Finset.eq_univ_of_forall (fun u => by
      by_contra hu
      exact hne u (mem_notHeldAt.mpr hu))
  have h := hthird t ht
  rw [huniv] at h
  have hw : S.E.electorate.weightOf (Finset.univ : Finset V) = S.E.electorate.totalWeight :=
    weightOf_univ _
  omega

/-- If `d + 2 ≤ w`, `d' ≤ w`, `w ≤ r₀` and `r₀ + 1 ≤ q`, then the listed bounds on `q` and `q − 1`
    hold. -/
theorem nat_rowsPlanned_f2c (d d' w r₀ q : Nat) (h1 : d + 2 ≤ w) (h2 : d' ≤ w) (h3 : w ≤ r₀)
    (h4 : r₀ + 1 ≤ q) :
    1 ≤ q ∧ d' + 1 ≤ q ∧ d + 3 ≤ q ∧ r₀ + (q - 1 - r₀) = q - 1 ∧ w ≤ q - 1 ∧
      q - 1 + 1 = q ∧ d + 2 ≤ q ∧ w ≤ q := by
  omega

end Rows

section WindowStep

/-- Every index into an sts execution is valid, so `get_elem_tactic` is answered by `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `d + 2 ≤ w ≤ r₀` and `r₀ + 2 ≤ c`, then the listed bounds on `c`, `c − 1` and `c − 2` hold. -/
theorem nat_windowStep_f2c (d w r₀ c : Nat) (h1 : d + 2 ≤ w) (h2 : w ≤ r₀) (h3 : r₀ + 2 ≤ c) :
    d + 4 ≤ c ∧ r₀ + 1 ≤ c ∧ r₀ + 1 ≤ c - 1 ∧ c - 1 - 1 = c - 2 ∧ d + 2 ≤ c ∧
      d + 2 ≤ c - 1 ∧ w ≤ c - 1 ∧ w ≤ c - 2 ∧ 1 ≤ c ∧ 1 ≤ c - 1 := by
  omega

/-- If `0 < R` and `s / R + 2 ≤ c`, then `s ≤ (c − 1)·R`. -/
theorem nat_slotPrev_f2c (R s c : Nat) (hR : 0 < R) (h : s / R + 2 ≤ c) : s ≤ (c - 1) * R := by
  have h1 : s < (s / R + 1) * R := by
    rw [Nat.add_mul, Nat.one_mul]; exact Nat.lt_div_mul_add hR
  have h2 : (s / R + 1) * R ≤ (c - 1) * R := Nat.mul_le_mul_right R (by omega)
  omega

end WindowStep

section AfterTimeout

/-- Every index into an sts execution is valid, so `get_elem_tactic` is answered by `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `d + 2 ≤ w ≤ r₀ ≤ c`, `2 ≤ m` and `c + m ≤ c'`, then the listed bounds on `c`, `c'` and
    `c' − 1` hold. -/
theorem nat_afterTimeout_f2c (d w r₀ c c' m : Nat) (h1 : d + 2 ≤ w) (h2 : w ≤ r₀) (h3 : r₀ ≤ c)
    (hm : 2 ≤ m) (hlo : c + m ≤ c') :
    d + 2 ≤ c ∧ d + 4 ≤ c' ∧ c + 1 ≤ c' ∧ r₀ + 1 ≤ c' ∧ r₀ + 1 ≤ c' - 1 ∧
      c' - 1 - 1 = c' - 2 ∧ d + 2 ≤ c' := by
  omega

end AfterTimeout

end DecoupledConsensusModel.Sts
