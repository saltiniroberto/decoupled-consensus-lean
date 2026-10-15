import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_72UpTo
import Proofs.Claims.Restated.Claim13beRoute3_73
import Proofs.Claims.Restated.Claim13beRoute3_73UpTo
import Proofs.Claims.Restated.Claim13beRoute3_74
import Proofs.Claims.Restated.Claim13beRoute3_74UpTo
import Proofs.Claims.Restated.Claim13beRoute3_75
import Proofs.Claims.Restated.Claim13beRoute3_75UpTo
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_8
import Proofs.Claims.Restated.Claim13beRoute3_80
import Proofs.Claims.Restated.Claim13beRoute3_80UpTo
import Proofs.Claims.Restated.Claim13beRoute3_81
import Proofs.Claims.Restated.Claim13beRoute3_81UpTo
import Proofs.Claims.Restated.Claim13beRoute3_82
import Proofs.Claims.Restated.Claim13beRoute3_83
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveSince
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepActiveAssembly
import Model.Conditions.Claim13bStepFieldsAt
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_79
import Model.Conditions.Claim13beRoute3_81
import Model.Conditions.Claim13beRoute3_82
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The switch-round invariant, with synchrony up to the switch round

The invariant `AfterPhaseInvariantOverActiveSetsSince` at the switch round's tick step, with
synchrony assumed only up to the confirmation time of the switch round's third slot. Stated over a
model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p72% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_72)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p73% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_73)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p74% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_74)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If every tick has an outcome, then under the listed premises and `hP`, with synchrony assumed
    only up to the confirmation time of the switch round's third slot, there is a step `n₀` that is
    the tick at the switch round's action instant and a switch-round anchor `T₀` such that
    `AfterPhaseInvariantOverActiveSetsSince` holds at round `rW`, step `n₀`, switch step `n₀` and
    anchor `T₀`. -/
theorem claim13beBaseOverActiveSetsSince_anchored_of_premises_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWakeBefore M S x
      (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))) (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hP : ∀ (v : V) (N : Nat),
      (x[N].time : Int) = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2) →
      ∀ nprev : V → M.N,
        (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
          (Restated.switchRound M S tE - 1)) →
        Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
          (Restated.runAllPath M S Sched x v N) nprev)
    (hclear : ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (x[N].time : Int)
        = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2) →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = Restated.switchRound M S tE →
      Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) →
      Restated.BaseClearFGSourceCompatibleWithAnchor M S Sched x tE n₀ T) :
    ∃ (n₀ : Nat) (T₀ : NamedBlock V), Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) ∧
      Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T₀ ∧
      Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x (Restated.switchRound M S tE) n₀ n₀ T₀ := by
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  obtain ⟨n₀, hn₀⟩ := Restated.exists_tick_at_switchRound facts S Sched x htd tE
  obtain ⟨v, -⟩ := exists_not_adv_l76 S Sched (hthird tE le_rfl)
  obtain ⟨N, hN, hNE, -, hrWN, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    (Restated.runAll M S Sched x v 0) hgst hlen' htd
  obtain ⟨blocked, first, i, a, ta, Cfg, T, Tprev, c0, hreg, harW, -, htop, hband⟩ :=
    Restated.switchRoundRegime_runAll_notHeld_upTo facts S Sched x v hsync hmono hawake hgst hcv hexec hmult hthird
      hcom hrec hlen' htd hn₀ hN
  have hfin := Restated.fin_at_switchRound_of_regime_upTo facts S Sched x v hsync hmono hawake hgst hcv hexec hmult
    hthird hcom hlen' htd hN hreg hn₀ htop
  have hchain : Restated.BaseSGOneChainAtSwitchRound M S Sched x v tE N :=
    Restated.baseSGOneChainAtSwitchRound_of_premises_upTo facts S Sched x v hsync hmono hawake hgst hcv hexec
      hmult hthird hcom hlen' htd hN hreg harW hn₀ htop (hP v N hN)
  have hgrade1 := Restated.grade1_at_switchRound_upTo facts S Sched x v hsync hmono hawake hgst hcv hexec hmult
    hthird hcom hlen' htd hN hreg harW hn₀ hfin
    (fun heq => Restated.basePreviousRoundSGCompatibleWithAnchor_of_belowOpeningVotes_upTo facts S Sched x v
      hsync hmono hawake hgst hcv hexec hmult hthird hcom hlen' htd hN hreg heq (hP v N hN))
  have hTop : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x (Restated.switchRound M S tE) n₀ T :=
    { tick := hn₀
      inPlay := Restated.inPlay_at_switchRound_of_regime facts S Sched x v hmono hreg
      anchorEntry := Restated.anchorEntry_at_switchRound_of_regime facts S Sched x v hmono hexec hreg
      band := hband
      sg := Restated.sg_at_switchRound_upTo facts S Sched x v hsync hmono hawake hgst hcv hexec hmult hthird hcom
        hlen' htd hN hreg harW hn₀
      sgPairwise := Restated.sgPairwise_at_switchRound facts S Sched x v hmono hexec hN hn₀ hchain
      heads := Restated.headsBelow_of_regime_upTo facts S Sched x v hsync hmono hawake hgst hcv hexec hmult hthird
        hcom hlen' htd hN hreg harW
      fin := hfin
      grade1 := fun w hw' p hp m hm B b hb hbt => hgrade1 w hw' p hp m hm B (hbt ▸ hb)
      heightCeiling := Restated.heightCeiling_of_topHonestRow facts S Sched x hexec.toUnforgeability htop
      targetsTop := Restated.targetsTop_at_switchRound_upTo facts S Sched x v hsync hmono hawake hgst hcv hexec hmult
        hthird hcom hlen' htd hN hreg hn₀ }
  refine ⟨n₀, T, hn₀,
    ⟨v, N, n₀, blocked, first, i, a, ta, Cfg, Tprev, c0, hn₀, hrWN, hNE, hreg, harW, htop⟩, ?_⟩
  exact
    { tick := hTop.tick
      inPlay := hTop.inPlay
      anchorEntry := hTop.anchorEntry
      band := hTop.band
      sg := hTop.sg
      sgPairwise := hTop.sgPairwise
      heads := hTop.heads
      fin := hTop.fin
      grade1 := hTop.grade1
      heightCeiling := hTop.heightCeiling
      targetsTop := hTop.targetsTop
      targetsSince := Restated.targetsSince_at_switchRound_upTo facts S Sched x v hsync hmono hawake hgst hcv hexec
        hmult hthird hcom hlen' htd hN hreg harW hn₀ (fun _ => hgrade1)
        (fun heq => hclear v N blocked first i a ta Cfg T Tprev c0 n₀ hN hreg heq hn₀) }

end

end DecoupledConsensusModel.Sts.Restated
