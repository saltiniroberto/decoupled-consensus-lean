module
public import GoldilocksCorrectness.Record.ScheduleFacts
public import GoldilocksCorrectness.Proofs.Routines.Schedule
import all Goldilocks.Config
import all Goldilocks.Node
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# The schedule's facts from the uniform spacing, and the spec's slot layout

- `UniformSchedule.scheduleFacts`: a slot layout spaced as Goldilocks is, whose quorum at each
  block is two thirds of the block's validators, satisfies `ScheduleFacts`. The proof reads the
  parameters' bounds `Δ_pos`, `Δ_F_ge`, `k_ge_two` and `R_covers` through the library's
  `one_le_Δ`, `Δ_cast` and `Δ_F_cast`.
- `uniformSchedule_goldilocks`, `fixedValidators_goldilocks`, `scheduleFacts_goldilocks`: the
  spec's slot layout `SlotLayout.goldilocks` is uniform, has fixed validators, and satisfies the
  schedule's facts. Each field of the first is one of the library's equalities of
  `Proofs/Routines/Schedule.lean`, or read off the spec's definitions (this page sees the bodies of
  the spec's times and of the library's).
- `quorumAt_eq_quorum`: with fixed validators, the quorum at every block is the spec's `quorum V`.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

open Goldilocks (Block quorum validator_count duty_window_start proposal_window_start)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff viewFreeze
  lateVoteCutoff dutyWindowStart proposalWindowStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ Δ_cast Δ_F_cast slotStart_cast
  duty_window_start_eq dutyWindowStart_eq_toNat)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The delays fit in a round: `6 * Δ S + Δ_F S ≤ 4 * Δ S * S.C.R`, the parameters' bound
`R_covers` on natural numbers.

The variables:
- `S`: the setup.

Read aloud: six delays and an attestation delay fit in the `S.C.R` slots of a round. -/
theorem six_Δ_add_Δ_F_le_round (S : Setup V) : 6 * Δ S + Δ_F S ≤ 4 * Δ S * S.C.R := by
  have h := S.C.R_covers
  have h1 := Δ_cast S
  have h2 := Δ_F_cast S
  have : ((6 * Δ S + Δ_F S : ℕ) : Int) ≤ ((4 * Δ S * S.C.R : ℕ) : Int) := by
    push_cast
    rw [h1, h2]
    exact h
  exact_mod_cast this

/-- **The schedule's facts from the uniform spacing.** A slot layout spaced as Goldilocks is
satisfies every fact of `ScheduleFacts` but the quorum's, which the hypothesis `hq` supplies.

The variables:
- `L`: the slot layout; `U`: it is spaced as Goldilocks is;
- `hq`: the quorum at each block is two thirds of the block's validators, rounded up.

Read aloud: a uniform slot layout whose quorum at each block is two thirds of the block's
validators satisfies the schedule's facts. -/
theorem UniformSchedule.scheduleFacts {L : SlotLayout V} (U : UniformSchedule L)
    (hq : ∀ B : Block V, L.quorumAt B = (2 * (L.validators B).card + 2) / 3) :
    ScheduleFacts L where
  slotStart_add_Δ_le_voteTime S s := by
    rw [U.voteTime_eq]
  voteTime_add_Δ_le_supportCutoff S s := by
    rw [U.voteTime_eq, U.supportCutoff_eq]
    omega
  supportCutoff_add_Δ_le_viewFreeze S s := by
    rw [U.supportCutoff_eq, U.viewFreeze_eq]
    omega
  viewFreeze_add_Δ_le_slotStart_succ S s := by
    rw [U.viewFreeze_eq, U.slotStart_eq S s, U.slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
    omega
  slotStart_zero S := by
    rw [U.slotStart_eq, Nat.mul_zero]
  slotStart_le_iff S s t := by
    have hq : 0 < 4 * Δ S := by have := one_le_Δ S; omega
    rw [U.slot_eq, U.slotStart_eq, Nat.le_div_iff_mul_le hq, Nat.mul_comm s]
  dutyWindowStart_succ_le_slotStart S s := by
    rw [U.dutyWindowStart_eq, U.slotStart_eq S s, U.slotStart_eq S (s + 1), Nat.mul_add,
      Nat.mul_one]
    have hk : 4 * Δ S * 2 ≤ 4 * Δ S * S.C.k := Nat.mul_le_mul_left _ S.C.k_ge_two
    omega
  dutyWindowStart_mono S s s' h := by
    rw [U.dutyWindowStart_eq S s, U.dutyWindowStart_eq S s', U.slotStart_eq S s,
      U.slotStart_eq S s']
    have := Nat.mul_le_mul_left (4 * Δ S) h
    omega
  dutyWindowStart_succ_le_proposalWindowStart S s := by
    rw [U.dutyWindowStart_eq, U.proposalWindowStart_eq, U.slotStart_eq S (s + 1),
      U.slotStart_eq S (s + 2), show s + 2 = (s + 1) + 1 from rfl, Nat.mul_add (4 * Δ S) (s + 1) 1,
      Nat.mul_add (4 * Δ S) S.C.k 1, Nat.mul_one]
    omega
  supportCutoff_succ_add_Δ_F_le_slotStart S s := by
    rw [U.supportCutoff_eq, U.slotStart_eq S (s + 1), U.slotStart_eq S (s + S.C.R), Nat.mul_add,
      Nat.mul_add, Nat.mul_one]
    have := six_Δ_add_Δ_F_le_round S
    omega
  supportCutoff_succ_le_lateVoteCutoff S s := by
    rw [U.supportCutoff_eq, U.lateVoteCutoff_eq, U.slotStart_eq S (s + 1), U.slotStart_eq S s,
      Nat.mul_add, Nat.mul_one]
    omega
  quorumAt_eq := hq

/-- The spec's slot layout is spaced uniformly: each field is one of the library's equalities of
`Proofs/Routines/Schedule.lean`, or read off the spec's definitions.

Read aloud: Goldilocks' slots are spaced as `UniformSchedule` says. -/
theorem uniformSchedule_goldilocks : UniformSchedule (SlotLayout.goldilocks : SlotLayout V) where
  slotStart_eq S s := GoldilocksCorrectness.Proofs.Routines.slotStart_eq S s
  voteTime_eq S s := GoldilocksCorrectness.Proofs.Routines.voteTime_eq S s
  supportCutoff_eq S s := by
    have h1 := GoldilocksCorrectness.Proofs.Routines.supportCutoff_eq S s
    have h2 := GoldilocksCorrectness.Proofs.Routines.voteTime_eq S s
    show supportCutoff S s = slotStart S s + 2 * Δ S
    omega
  viewFreeze_eq S s := GoldilocksCorrectness.Proofs.Routines.viewFreeze_eq S s
  lateVoteCutoff_eq S s := by
    have h1 := slotStart_cast S s
    have h2 := Δ_cast S
    have h3 : (0 : Int) ≤ S.C.t_ s := by rw [← h1]; exact Int.natCast_nonneg _
    have h4 : ((lateVoteCutoff S s : ℕ) : Int) = S.C.t_ s + 6 * S.C.Δ :=
      Int.toNat_of_nonneg (by have := S.C.Δ_pos; omega)
    show lateVoteCutoff S s = slotStart S s + 6 * Δ S
    omega
  dutyWindowStart_eq S s := by
    have h1 := slotStart_cast S s
    have h2 := Δ_cast S
    have hk : ((4 * Δ S * S.C.k : ℕ) : Int) = 4 * S.C.Δ * (S.C.k : Int) := by
      push_cast
      rw [h2]
    show dutyWindowStart S s = slotStart S s + Δ S - 4 * Δ S * S.C.k
    rw [dutyWindowStart_eq_toNat, duty_window_start_eq, ← h1, ← hk, ← h2, ← Nat.cast_add,
      Int.toNat_sub]
  proposalWindowStart_eq S s := by
    have h1 := slotStart_cast S s
    have h2 := Δ_cast S
    have hk : ((4 * Δ S * (S.C.k + 1) : ℕ) : Int) = 4 * S.C.Δ * ((S.C.k : Int) + 1) := by
      push_cast
      rw [h2]
    show (proposal_window_start S.C s).toNat = slotStart S s + Δ S - 4 * Δ S * (S.C.k + 1)
    show (S.C.t_ s + S.C.Δ - 4 * S.C.Δ * ((S.C.k : Int) + 1)).toNat = _
    rw [← h1, ← hk, ← h2, ← Nat.cast_add, Int.toNat_sub]
  slot_eq S t := GoldilocksCorrectness.Proofs.Routines.slot_natCast S t

/-- The spec's slot layout has fixed validators: every block's validator set is every validator,
by definition.

Read aloud: in Goldilocks, every block has every validator. -/
theorem fixedValidators_goldilocks : FixedValidators (SlotLayout.goldilocks : SlotLayout V) where
  validators_eq_univ _ := rfl

/-- The spec's slot layout satisfies the schedule's facts: it is uniform, and its quorum at every
block, `quorum V`, is two thirds of every validator.

Read aloud: Goldilocks' slot layout satisfies every fact the record asks of a slot layout. -/
theorem scheduleFacts_goldilocks : ScheduleFacts (SlotLayout.goldilocks : SlotLayout V) :=
  uniformSchedule_goldilocks.scheduleFacts (fun _ => rfl)

/-- **With fixed validators, the quorum at every block is `quorum V`.**

The variables:
- `L`: the slot layout; `Fx`: its every block has every validator; `SF`: its facts;
- `B`: the block.

Read aloud: when every block has every validator, the quorum at `B` is the spec's `quorum V`. -/
theorem quorumAt_eq_quorum {L : SlotLayout V} (Fx : FixedValidators L) (SF : ScheduleFacts L)
    (B : Block V) : L.quorumAt B = quorum V := by
  rw [SF.quorumAt_eq, Fx.validators_eq_univ]
  rfl

end GoldilocksCorrectness.Record
