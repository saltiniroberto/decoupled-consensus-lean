import Proofs.Claims.Spec2Claims.Claim13beRoute3_55
import Proofs.Claims.Spec2Claims.Claim13bModel_freezeRoot
import Proofs.Claims.Spec2Claims.Claim13bModel_onPhaseTick_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_readFrame_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_clipResult
import Proofs.Vocabulary.ModelProperties.readFrame
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.Spec2Claims.Claim13bModel_activePrefix
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeView
import Proofs.Claims.Spec2Claims.Claim13bModel_sgVote
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAttestation_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_rawInputs
import Proofs.Claims.Spec2Claims.Claim13bModel_interpretedInputs
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_proposer_view
import Proofs.Claims.Spec2Claims.Claim13bModel_Store_pool
import Proofs.Claims.Spec2Claims.Claim13bModel_beforeCutoff
import Proofs.Claims.Spec2Claims.Claim13bModel_resolved
import Proofs.Vocabulary.ModelProperties.Store_toHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_get_head_with
import Proofs.Vocabulary.ModelProperties.get_sg_root_with
import Proofs.Vocabulary.ModelProperties.get_fg_root

/-!
# Round arithmetic for height progress

The inequalities over `Nat` between the start, carrier, seed and endpoint rounds that the
height-progress proofs use.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

section HeightProgressCompose

open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- If `start + 3 + delayExtra + gap ≤ endpoint`, then `start + 2 ≤ endpoint`, `start ≤ start + 2`,
    `start < start + 2` and `start < start + 3 + delayExtra`. -/
theorem lowPrelude_nat_l56 {start gap endpoint delayExtra : Nat}
    (h : start + 3 + delayExtra + gap ≤ endpoint) :
    start + 2 ≤ endpoint ∧ start ≤ start + 2 ∧ start < start + 2 ∧
      start < start + 3 + delayExtra := by
  omega

/-- If `start + 3 + delayExtra + gap ≤ endpoint` and `q` is between `start + 3 + delayExtra` and
    `start + 3 + delayExtra + gap`, then `q ≤ endpoint`, `0 < q`, `start + 2 ≤ q − 1`,
    `start ≤ q − 1`, `q − 1 ≤ endpoint`, `2 + delayExtra ≤ q`, `start < q` and `start + 2 ≤ q`. -/
theorem lowSelected_nat_l56 {start gap endpoint delayExtra q : Nat}
    (h : start + 3 + delayExtra + gap ≤ endpoint)
    (hlo : start + 3 + delayExtra ≤ q) (hhi : q ≤ start + 3 + delayExtra + gap) :
    q ≤ endpoint ∧ 0 < q ∧ start + 2 ≤ q - 1 ∧ start ≤ q - 1 ∧ q - 1 ≤ endpoint ∧
      2 + delayExtra ≤ q ∧ start < q ∧ start + 2 ≤ q := by
  omega

/-- The endpoint `start + progressLag' gap delayExtra` is at least `start`, `start + 1`,
    `start + 1 + 3·gap + 8 + 2·delayExtra`, `start + 1 + seedLag gap delayExtra`, that plus
    `3·gap + 8 + 2·delayExtra`, and `start + 3 + delayExtra + gap`. -/
theorem composeStaticBounds_nat_l56 (start gap delayExtra : Nat) :
    start ≤ start + progressLag' gap delayExtra ∧
      start + 1 ≤ start + progressLag' gap delayExtra ∧
        start + 1 + 3 * gap + 8 + 2 * delayExtra ≤ start + progressLag' gap delayExtra ∧
          start + 1 + seedLag gap delayExtra ≤ start + progressLag' gap delayExtra ∧
            (start + 1 + seedLag gap delayExtra) + 3 * gap + 8 + 2 * delayExtra ≤
                start + progressLag' gap delayExtra ∧
              start + 3 + delayExtra + gap ≤ start + progressLag' gap delayExtra := by
  simp only [progressLag', seedLag]
  omega

/-- If `start + 2 ≤ entry`, `entry + 2 + delayExtra ≤ q`, `q ≤ seedEnd` and
    `seedEnd + 3·gap + 8 + 2·delayExtra ≤ endpoint`, then `0 < entry`, `0 < q`, `start ≤ q − 2`,
    `start ≤ q − 1`, `q − 2 + 1 = q − 1`, `q − 1 + 1 = q`, `q`, `q − 1` and `q − 2` are at most
    `endpoint`, and `q − 1` and `q` plus `3·gap + 8 + 2·delayExtra` are at most `endpoint`. -/
theorem seedGradeBounds_nat_l56 {start entry q seedEnd endpoint gap delayExtra : Nat}
    (hentryLo : start + 2 ≤ entry) (hspace : entry + 2 + delayExtra ≤ q)
    (hqhi : q ≤ seedEnd) (hseedBound : seedEnd + 3 * gap + 8 + 2 * delayExtra ≤ endpoint) :
    0 < entry ∧ 0 < q ∧ start ≤ q - 2 ∧ start ≤ q - 1 ∧ q - 2 + 1 = q - 1 ∧ q - 1 + 1 = q ∧
      q ≤ endpoint ∧ q - 1 ≤ endpoint ∧ q - 2 ≤ endpoint ∧
        q - 1 + 3 * gap + 8 + 2 * delayExtra ≤ endpoint ∧
          q + 3 * gap + 8 + 2 * delayExtra ≤ endpoint := by
  omega

end HeightProgressCompose


end DecoupledConsensusModel.Sts
