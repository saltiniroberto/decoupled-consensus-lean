import Proofs.Claims.Spec2Claims.Claim13beRoute3_58
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RecoveryProposalWindow
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HeightProgressLadder
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG5
import Proofs.Claims.Spec2Claims.Claim13bModel_fg_source_with
import Proofs.Claims.Spec2Claims.Claim13bModel_actionStoreAt
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_attest

/-!
# Round arithmetic for the height-progress seed

The order of a round's domain instants, and the inequalities over `Nat` between the base, carrier
and endpoint rounds that the seed proofs use.
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

section SeedHeightProgress

open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic

local macro "shp% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.Grades.SeedHeightProgress)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- `domain q .g2 ≤ domain q p` for every phase `p`: the grade-2 domain instant is the earliest of a
    round's domain instants. -/
theorem domain_g2_le_domain_l67 (S : Setup V) (q : Round) (p : Phase) :
    DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2 ≤
      DecoupledConsensusModel.Protocol.domain S.E S.hc q p := by
  have hΔ := S.E.Δ_pos
  rw [DecoupledConsensusModel.Sts.domain_g2_eq_opening]
  cases p
  · rw [DecoupledConsensusModel.Sts.domain_g0_eq_opening]; linarith
  · rw [DecoupledConsensusModel.Sts.domain_g1_eq_opening]; linarith
  · rw [DecoupledConsensusModel.Sts.domain_g2_eq_opening]

/-- From `r0 ≤ base`, `base + 4 ≤ q` and `q + 2 ≤ q4`: `base < q`, `r0 + 1 ≤ q`, `base + 1 < q`,
    `base < q4`, `base + 1 < q4`, `r0 + 1 ≤ q + 1`, `r0 + 1 ≤ q4 − 1`, `r0 + 1 ≤ q4 + 1` and
    `r0 + 2 ≤ q4`. -/
theorem seedCloserLaterRounds_nat_l67 {r0 base q q4 : Nat} (hr0 : r0 ≤ base)
    (hbq : base + 4 ≤ q) (hq4 : q + 2 ≤ q4) :
    base < q ∧ r0 + 1 ≤ q ∧ base + 1 < q ∧ base < q4 ∧ base + 1 < q4 ∧
      r0 + 1 ≤ q + 1 ∧ r0 + 1 ≤ q4 - 1 ∧ r0 + 1 ≤ q4 + 1 ∧ r0 + 2 ≤ q4 := by
  omega

/-- From `q + 2·gap + 6 + 2·delayExtra ≤ endpoint`,
    `q + 2 + delayExtra ≤ q4 ≤ q + 2 + delayExtra + gap` and
    `q4 + 2 + delayExtra ≤ q5 ≤ q4 + 2 + delayExtra + gap`, the rounds `q4 + 2`, `q4 + 1`, `q + 1`,
    `q4 − 1`, `q4`, `q5 + 1` and `q5 − 1` are less than `endpoint`, and `q5 + 2 ≤ endpoint`. -/
theorem seedCloserReadsStrict_nat_l67 {base gap q q4 q5 endpoint delayExtra : Nat}
    (_hbaseq : base + 4 ≤ q)
    (hbudget : q + 2 * gap + 6 + 2 * delayExtra ≤ endpoint)
    (h4lo : q + 2 + delayExtra ≤ q4) (h4hi : q4 ≤ q + 2 + delayExtra + gap)
    (h5lo : q4 + 2 + delayExtra ≤ q5) (h5hi : q5 ≤ q4 + 2 + delayExtra + gap) :
    q4 + 2 < endpoint ∧ q4 + 1 < endpoint ∧ q + 1 < endpoint ∧ q4 - 1 < endpoint ∧
      q4 < endpoint ∧ q5 + 1 < endpoint ∧ q5 - 1 < endpoint ∧ q5 + 2 ≤ endpoint := by
  omega

/-- From `r0 ≤ base`, `base + 4 ≤ q1` and `q1 + 2 ≤ q2`: `base < q1 + 1`, `r0 + 1 ≤ q1 + 1`,
    `r0 + 1 ≤ q1`, `base < q2`, `base + 1 < q2`, `r0 + 1 ≤ q2 − 1` and `r0 + 1 ≤ q2 + 1`. -/
theorem seedAdoptionLaterRounds_nat_l67 {r0 base q1 q2 : Nat} (hr0 : r0 ≤ base)
    (h1 : base + 4 ≤ q1) (h2 : q1 + 2 ≤ q2) :
    base < q1 + 1 ∧ r0 + 1 ≤ q1 + 1 ∧ r0 + 1 ≤ q1 ∧ base < q2 ∧ base + 1 < q2 ∧
      r0 + 1 ≤ q2 - 1 ∧ r0 + 1 ≤ q2 + 1 := by
  omega

/-- From `base + 4 ≤ q1 ≤ base + 4 + gap`, `q1 + 2 ≤ q2 ≤ q1 + 2 + gap` and
    `q2 + 2 + delayExtra ≤ q3 ≤ q2 + 2 + delayExtra + gap`, the rounds `q1 + 2`, `q2 + 2`, `q3 + 2`,
    `q2 + 1`, `q2 − 1` and `q3 − 1` are less than `base + seedLag gap delayExtra`. -/
theorem seedAdoptionReadsStrict_nat_l67 {base gap q1 q2 q3 delayExtra : Nat}
    (hq1lo : base + 4 ≤ q1) (hq1hi : q1 ≤ base + 4 + gap)
    (hq2lo : q1 + 2 ≤ q2) (hq2hi : q2 ≤ q1 + 2 + gap)
    (hq3lo : q2 + 2 + delayExtra ≤ q3) (hq3hi : q3 ≤ q2 + 2 + delayExtra + gap) :
    q1 + 2 < base + seedLag gap delayExtra ∧ q2 + 2 < base + seedLag gap delayExtra ∧
      q3 + 2 < base + seedLag gap delayExtra ∧ q2 + 1 < base + seedLag gap delayExtra ∧
      q2 - 1 < base + seedLag gap delayExtra ∧ q3 - 1 < base + seedLag gap delayExtra := by
  simp only [seedLag]
  omega

end SeedHeightProgress

end DecoupledConsensusModel.Sts
