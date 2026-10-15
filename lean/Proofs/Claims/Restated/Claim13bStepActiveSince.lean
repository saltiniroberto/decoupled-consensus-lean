import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_FrameNew
import Proofs.Claims.Restated.Claim13bStepActiveAssembly
import Proofs.Claims.Restated.Claim13bStepFin
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveSince
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepActiveAssembly
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepFieldsAt
import Model.Conditions.Claim13bStepGrade
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The target clause since the switch round

The projection of the invariant with the target clause since the switch round to
`AfterPhaseInvariantOverActiveSetsTop`, and its `targetsSince` clause at round `r + 1`; stated over
a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Whenever the invariant with the target clause since the switch round holds at round `r`, step
    `n` and anchor `T`, the invariant `AfterPhaseInvariantOverActiveSetsTop` holds there too. -/
theorem AfterPhaseInvariantOverActiveSetsSince.toTop {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {r : Round} {n n_W : Nat} {T : NamedBlock V}
    (h : Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x r n n_W T) :
    Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T :=
  { tick := h.tick
    inPlay := h.inPlay
    anchorEntry := h.anchorEntry
    band := h.band
    sg := h.sg
    sgPairwise := h.sgPairwise
    heads := h.heads
    fin := h.fin
    grade1 := h.grade1
    heightCeiling := h.heightCeiling
    targetsTop := h.targetsTop }

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The clause `targetsSince` of `AfterPhaseInvariantOverActiveSetsSince` at round `r + 1`: for
    every choice `att` of the round-`(r + 1)` action attestations, every non-empty height vote first
    in the sent log after the step `n_W`, authored and signed at a step up to the round-`(r + 1)`
    tick's successor by a validator honest through its send, at a height at most the chain-state
    height of the round-`(r + 1)` anchor read along `att`, names a block that is an ancestor of that
    anchor. -/
theorem targetsSince_field_of_hypotheses_overActiveSets_ofFieldsAt (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
    {r : Round} {n n' n_W : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r)
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x r n n_W T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hf : Restated.StepFieldsAt M S Sched x tE r n n' T) :
    ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
    ∀ (w : V) (n₁ : Nat) (a : NamedAttestation V) (h' : Height) (entry : BlockId) (tmo : Bool),
      n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ w → a.val_index = w →
      (⟨w, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₁].sent →
      (⟨w, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x[n_W].sent →
      a.height_pair = NamedHeightPair.vote h' entry tmo →
      h' ≤ (M.derive_named S.E S.cfg (Restated.newAnchor M S Sched x r n' att T)).h →
      ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = entry →
      Block.Preceq C.erase (Restated.newAnchor M S Sched x r n' att T).erase := by
  intro att hatt
  have hctx : Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T := ⟨hr, hinv.toTop⟩
  exact Restated.targetsSince_field_at_succ_ofWakes facts S Sched x hexec hw hs hinv.tick hn' hatt
    hinv.inPlay
    (Restated.anchor_preceq_new_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hctx hcross hjust hn'
        att hatt)
    (fun q hq => hf.confirmedNew att hatt q
      (Restated.mem_honRound_of_mem_freshAttesters_ofWakes facts S Sched x hw hn' hq))
    (fun q hq => Restated.frameG2New_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hctx hcross hjust hn' hf
        att hatt q
      (Restated.mem_honRound_of_mem_freshAttesters_ofWakes facts S Sched x hw hn' hq))
    hinv.heightCeiling hinv.targetsSince

end

end DecoupledConsensusModel.Sts.Restated
