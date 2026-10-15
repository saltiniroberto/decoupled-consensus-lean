module
public import Proofs.Vocabulary.Execution.SeedPromotionAncestor
public import Proofs.Vocabulary.Execution.SeedFreshPromotion
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HeightProgressCompose
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Proofs.Vocabulary.ModelProperties.NamedBlock_parent

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Round arithmetic

Inequalities between round numbers, stated over `Nat`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}


private theorem seedPrevRound_nat {a b : Nat} (h : a + 1 + 2 ≤ b) :
    a + 1 ≤ b - 1 := by
  omega


private theorem seedLeafRounds_nat {base entry q endpoint : Nat}
    (hbe : base + 1 ≤ entry) (heq : entry + 2 + delayExtra ≤ q) (hq : q ≤ endpoint) :
    0 < entry ∧ 0 < q ∧ entry ≤ endpoint ∧ entry + 1 ≤ endpoint ∧
      q - 1 ≤ endpoint ∧ base + 1 ≤ entry + 1 ∧ base + 1 ≤ q - 1 ∧
        entry + 1 ≤ q - 1 ∧ base ≤ entry := by
  omega

private theorem seedCloserSelectRound4_nat {base gap q endpoint delayExtra : Nat}
    (hbaseq : base + 4 ≤ q)
    (hbudget : q + 2 * gap + 6 + 2 * delayExtra ≤ endpoint) :
    base < q + 2 + delayExtra ∧
      q + 2 + delayExtra + gap ≤ endpoint := by
  omega

private theorem seedCloserSelectRound5_nat {base gap q q4 endpoint delayExtra : Nat}
    (hbaseq : base + 4 ≤ q)
    (hbudget : q + 2 * gap + 6 + 2 * delayExtra ≤ endpoint)
    (hq4lo : q + 2 + delayExtra ≤ q4)
    (hq4hi : q4 ≤ q + 2 + delayExtra + gap) :
    base < q4 + 2 + delayExtra ∧
      q4 + 2 + delayExtra + gap ≤ endpoint := by
  omega

private theorem seedAdoptionSelectRound1_nat {base gap delayExtra : Nat} :
    base < base + 4 ∧
      base + 4 + gap ≤ base + (4 * gap + 12 + 2 * delayExtra) := by
  omega

private theorem seedAdoptionSelectRound2_nat {base gap q1 delayExtra : Nat}
    (hq1lo : base + 4 ≤ q1)
    (hq1hi : q1 ≤ base + 4 + gap) :
    base < q1 + 2 ∧
      q1 + 2 + gap ≤ base + (4 * gap + 12 + 2 * delayExtra) := by
  omega

private theorem seedAdoptionSelectRound3_nat {base gap q1 q2 delayExtra : Nat}
    (hq1lo : base + 4 ≤ q1)
    (hq1hi : q1 ≤ base + 4 + gap)
    (hq2lo : q1 + 2 ≤ q2)
    (hq2hi : q2 ≤ q1 + 2 + gap) :
    base < q2 + 2 + delayExtra ∧
      q2 + 2 + delayExtra + gap ≤ base + (4 * gap + 12 + 2 * delayExtra) := by
  omega

private theorem seedCloserRounds_nat {base gap q q4 q5 endpoint : Nat}
    (hbaseq : base + 4 ≤ q)
    (hbudget : q + 2 * gap + 6 + 2 * delayExtra ≤ endpoint)
    (h4lo : q + 2 + delayExtra ≤ q4) (h4hi : q4 ≤ q + 2 + delayExtra + gap)
    (h5lo : q4 + 2 + delayExtra ≤ q5) (h5hi : q5 ≤ q4 + 2 + delayExtra + gap) :
    base + 2 ≤ q ∧ q ≤ q4 ∧ q ≤ q5 ∧ q4 + 2 ≤ endpoint ∧
      q4 + 1 ≤ endpoint ∧ q4 ≤ endpoint ∧ q5 + 2 ≤ endpoint ∧
        q5 ≤ endpoint ∧ q4 - 1 ≤ endpoint ∧ base + 1 + 2 ≤ q4 ∧
          base + 1 ≤ q4 ∧ q + 1 ≤ q4 - 1 ∧ base + 1 ≤ q + 1 ∧
            q + 2 + delayExtra ≤ q4 ∧ q4 + 2 + delayExtra ≤ q5 ∧ base ≤ q := by
  omega

private theorem seedSourceFrameRounds_nat {base q q' : Nat}
    (hbase : base + 4 ≤ q) (hnext : q ≤ q') : base + 1 ≤ q' - 2 := by
  omega


set_option maxHeartbeats 1000000 in
/-! ## The seed on one premise about carriers -/


private theorem seedCoverRounds_nat {q : Nat} (h : 2 ≤ q) :
    q - 2 + 1 = q - 1 ∧ q - 1 + 1 = q ∧ q - 2 ≤ q - 1 ∧ q - 1 ≤ q ∧
      q - 2 ≤ q := by
  omega


private theorem seedAdoptionRounds_nat {base gap q1 q2 q3 : Nat}
    (h1lo : base + 4 ≤ q1) (h1hi : q1 ≤ base + 4 + gap)
    (h2lo : q1 + 2 ≤ q2) (h2hi : q2 ≤ q1 + 2 + gap)
    (h3lo : q2 + 2 + delayExtra ≤ q3) (h3hi : q3 ≤ q2 + 2 + delayExtra + gap) :
    q1 + 2 ≤ base + (4 * gap + 12 + 2 * delayExtra) ∧ q2 + 2 ≤ base + (4 * gap + 12 + 2 *
      delayExtra) ∧
      q3 + 2 ≤ base + (4 * gap + 12 + 2 * delayExtra) ∧ q3 ≤ base + (4 * gap + 12 + 2 * delayExtra)
        ∧
        q2 + 1 ≤ base + (4 * gap + 12 + 2 * delayExtra) ∧ q3 - 1 ≤ base + (4 * gap + 12 + 2 *
          delayExtra) ∧
          base + 1 + 1 ≤ q1 ∧ base + 1 + 1 ≤ q1 + 1 ∧
            q1 + 1 ≤ q2 ∧ q1 + 1 ≤ q3 ∧ base + 1 + 2 ≤ q2 ∧
              base + 1 ≤ q2 ∧ base + 4 ≤ q2 ∧ q2 + 2 + delayExtra ≤ q3 ∧
                q2 + 1 ≤ q3 - 1 ∧ 0 < q2 ∧ base ≤ q1 ∧ base ≤ q2 ∧
                  base + 1 ≤ q1 + 2 ∧ base + 1 ≤ q2 + 2 ∧
                    base + 1 ≤ q3 + 2 ∧ base + 1 ≤ q2 + 1 ∧
                      q2 + 2 * gap + 6 + 2 * delayExtra ≤ base + (4 * gap + 12 + 2 * delayExtra) ∧
                        q1 + 1 ≤ base + (4 * gap + 12 + 2 * delayExtra) ∧
                          q2 + 1 ≤ base + (4 * gap + 12 + 2 * delayExtra) ∧
                            base + 1 ≤ q1 - 2 ∧ base + 1 ≤ q2 - 2 ∧
                              2 ≤ q2 ∧ q1 ≤ q2 - 2 ∧ q1 ≤ q2 - 1 ∧
                                q2 - 2 ≤ q2 + 1 ∧ q2 - 1 ≤ q2 + 1 := by
  omega


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
