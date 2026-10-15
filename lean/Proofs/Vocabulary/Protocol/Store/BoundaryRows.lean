module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RetainedRows
import Proofs.Vocabulary.Execution.HealthyLocalFacts
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Schedule arithmetic -/

/-- With `3 ≤ S.hc.R`, round `q`'s action time plus `Δ` is at most round `(q + 1)`'s grade-2 early
    cutoff. -/
theorem source_deadline_le_next_early (S : Setup V) (q : Round) (hR : 3 ≤ S.hc.R) :
    S.a q + S.E.Δ ≤ early S.E S.hc (q + 1) .g2 := by
  have hRcast : (3 : Time) ≤ (S.hc.R : Time) := by exact_mod_cast hR
  have hmul : 12 * S.E.Δ ≤ 4 * S.E.Δ * (S.hc.R : Time) := by
    have h := Int.mul_le_mul_of_nonneg_left hRcast
      (Int.mul_nonneg (show (0 : Time) ≤ 4 by norm_num) S.E.Δ_pos.le)
    calc
      12 * S.E.Δ = (4 * S.E.Δ) * 3 := by ring
      _ ≤ 4 * S.E.Δ * (S.hc.R : Time) := h
  have hrest : S.E.Δ ≤ 4 * S.E.Δ * (S.hc.R : Time) - 11 * S.E.Δ := by
    calc
      S.E.Δ = 12 * S.E.Δ + -(11 * S.E.Δ) := by ring
      _ ≤ 4 * S.E.Δ * (S.hc.R : Time) + -(11 * S.E.Δ) := Int.add_le_add_right hmul _
      _ = _ := by ring
  have heq : early S.E S.hc (q + 1) .g2 =
      S.a q + 4 * S.E.Δ * (S.hc.R : Time) - 11 * S.E.Δ := by
    unfold early opening Phase.earlyOffset Protocol.proposal_time Env.t Setup.a
      Protocol.HealConfig.a Protocol.HealConfig.opening_slot slotStart
    push_cast
    ring
  calc
    S.a q + S.E.Δ ≤ S.a q + (4 * S.E.Δ * (S.hc.R : Time) - 11 * S.E.Δ) :=
      Int.add_le_add_left hrest _
    _ = early S.E S.hc (q + 1) .g2 := by rw [heq]; ring

/-- Round `q`'s grade-2 early cutoff is at most its grade-2 domain time. -/
theorem early_le_domain (S : Setup V) (q : Round) :
    early S.E S.hc q .g2 ≤ domain S.E S.hc q .g2 := by
  change opening S.E S.hc q + (-5) * S.E.Δ ≤ opening S.E S.hc q + (-1) * S.E.Δ
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (show (-5 : Time) ≤ -1 by decide) S.E.Δ_pos.le) _

theorem opening_mono (S : Setup V) {q r : Round} (h : q ≤ r) :
    opening S.E S.hc q ≤ opening S.E S.hc r :=
  Protocol.proposal_time_mono S.E (Nat.mul_le_mul_right _ h)

theorem early_le_opening (S : Setup V) (q : Round) :
    early S.E S.hc q .g2 ≤ opening S.E S.hc q := by
  change opening S.E S.hc q + (-5) * S.E.Δ ≤ opening S.E S.hc q
  have : (-5) * S.E.Δ ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg (by decide) S.E.Δ_pos.le
  simpa only [add_zero] using Int.add_le_add_left this (opening S.E S.hc q)

/-- With `3 ≤ S.hc.R` and `q < r`, round `q`'s action time plus `Δ` is at most round `r`'s grade-2
    early cutoff. -/
theorem action_delta_le_early (S : Setup V) {q r : Round} (hR : 3 ≤ S.hc.R) (hqr : q < r) :
    S.a q + S.E.Δ ≤ early S.E S.hc r .g2 := by
  refine (source_deadline_le_next_early S q hR).trans ?_
  change opening S.E S.hc (q + 1) + (-5) * S.E.Δ ≤ opening S.E S.hc r + (-5) * S.E.Δ
  exact Int.add_le_add_right (opening_mono S hqr) _

theorem action_le_domain (S : Setup V) {q r : Round} (hR : 3 ≤ S.hc.R) (hqr : q < r) :
    S.a q ≤ domain S.E S.hc r .g2 := by
  refine le_trans ?_ ((action_delta_le_early S hR hqr).trans (early_le_domain S r))
  simpa only [add_zero] using Int.add_le_add_left S.E.Δ_pos.le (S.a q)

/-- A raw grade input `y` of an honest sender `u` in `reader`'s store before `cut` is the SG vote of
    a row of `u` for a round of the latest window, emitted by `u` at that round's action time, which
    is before `cut`. -/
theorem rawInputs_trace (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (cut cutoff : Time) (reader : V) (eta r : Round) (u : V) (hu : u ∈ rho.honest)
    {y : Protocol.SGVote V}
    (hy : y ∈ DecoupledConsensusModel.Protocol.rawInputs
      (NamedRun.stateBeforeTime S rho cut reader).st.core.toHealing.gradeView eta r cutoff u) :
    ∃ a : NamedAttestation V, a.val_index = u ∧ a.round = y.round ∧
      Protocol.sgVote a.erase = y ∧ y.round ∈ Protocol.latest_window eta r ∧
      S.a a.round < cut ∧ NamedRun.emits S rho u (.attest a) (S.a a.round) := by
  obtain ⟨hpool, hfields⟩ := Finset.mem_filter.mp hy
  obtain ⟨k, hk, hyk⟩ := Finset.mem_biUnion.mp hpool
  obtain ⟨a, hround, hproj, hmem⟩ := pool_token_row S rho sch cut reader hyk
  have hyround : y.round = a.round := by rw [← hproj]; rfl
  have hval : a.val_index = u := by
    have hvy : y.val_index = u := hfields.1
    rw [← hproj] at hvy
    exact hvy
  subst hval
  obtain ⟨hlt, hem⟩ := honest_held_row_before_cut S rho sch auth cut reader hmem hu
  exact ⟨a, rfl, hyround.symm, hproj,
    by rw [hyround, hround]; exact List.mem_toFinset.mp hk, hlt, hem⟩


#print axioms action_delta_le_early


end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
