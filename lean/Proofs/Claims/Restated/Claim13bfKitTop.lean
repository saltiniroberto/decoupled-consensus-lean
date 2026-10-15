import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Claim13bStepActiveAssembly
import Proofs.Claims.Restated.Claim13beRoute3_85f
import Proofs.Claims.Restated.Claim13bfJoint
import Proofs.Claims.Restated.Claim13bfKit
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsDerived
import Proofs.Claims.Restated.Constants
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepActiveAssembly
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_79
import Model.Conditions.Claim13beRoute3_82
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_JointBase

/-!
# Safety with catch-up on wake

Over a model `M : Record.Model V`: `Restated.claim13bfStatement M S Sched` holds, from the joint
invariant, with `hlow` supplied by `hlow_of_premises_l85f`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}


local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pKAS% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beKitActiveSince)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- `claim13bf_holds` at the healing length
    `healingLengthη M S gap + period`. -/
theorem claim13bf_holds_at (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (gap : Nat) (hgap : gap + 2 ≤ S.cfg.K)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tE : Int)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT)
    (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x)
    (hmult : AwakeAtMultiples S Sched)
    (hcatch : Restated.CatchUpOnWake M S x)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hsl : sleepinessW S Sched tE)
    (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE) :
    ∀ (v₁ v₂ : V) (i j : Nat),
      Restated.HonestThrough M Sched x i v₁ → Restated.HonestThrough M Sched x j v₂ →
      Block.Compatible (Restated.Read.finalized M x[i][v₁].st)
        (Restated.Read.finalized M x[j][v₂].st) := by
  have hcv := Restated.commonViewOfFinalizedDescendantsAt_of_catchUp facts S Sched x hexec hsync hcatch hmult
    htd hgst (tE := tE) (by have := Restated.delta_le_healingLengthη_add_period facts S gap; linarith)
    hawake
  exact Restated.claim13bf_conclusion_of_joint facts S Sched x tGAT tE gap hgap hlen hgst hmono hexec hsync
    hmult hcatch
    hcv htd hcom hthird
    hawake hrec hsl hrs hcs
    (Restated.hlow_of_premises_l85f facts S Sched x tGAT tE gap hgap hlen hgst hmono hexec hsync hmult
       hcv htd hcom hthird hawake hrec hsl hrs hcs)

/-- `Restated.claim13bfStatement M S Sched` holds, with the phase length
    `healingLengthη S gap + (constants S).period`: no two blocks finalized in the stores of two
    validators honest through their own steps conflict. -/
theorem claim13bf_holds (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) :
    Restated.claim13bfStatement M S Sched := by
  intro gap hgap
  refine ⟨Restated.healingLengthη M S gap + (Restated.constants M S).period, ?_, ?_⟩
  · have h0 := Restated.healingLengthη_nonneg facts S gap
    have h1 : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
    linarith
  · exact fun x tGAT tE hlen hgst hmono hexec hsync hmult hcatch htd hcom hthird
      hawake hrec hsl hrs hcs =>
      Restated.claim13bf_holds_at facts S Sched gap hgap x tGAT tE hlen hgst hmono hexec
        hsync hmult hcatch htd hcom hthird hawake hrec hsl hrs hcs

end

end DecoupledConsensusModel.Sts.Restated
