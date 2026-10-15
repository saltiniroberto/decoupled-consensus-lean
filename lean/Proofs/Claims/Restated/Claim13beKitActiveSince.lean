import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_73
import Proofs.Claims.Restated.Claim13beRoute3_74
import Proofs.Claims.Restated.Claim13beRoute3_75
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_8
import Proofs.Claims.Restated.Claim13beRoute3_80
import Proofs.Claims.Restated.Claim13beRoute3_81
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
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Restated.Claim13beRoute3_74NotHeld

/-!
# Safety from the invariant with the target clause since the switch round

The invariant `AfterPhaseInvariantOverActiveSetsSince` at the switch round, its extension to every
later round, and the conclusion that no two finalized blocks of honest validators conflict. Stated
over a model `M : Record.Model V`.
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

/-- For every round `r₀` and every time `t` there is a round at or after `r₀` whose action instant
    is strictly after `t`. -/
private theorem exists_action_gt_kas (facts : Record.Facts M) (S : Setup V) (r₀ : Round) (t : Int) :
    ∃ k : Nat, t < Restated.Vocabulary.Execution.Setup.a M S (r₀ + k) := by
  have hmono := Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S
  have h : ∀ k : Nat, Restated.Vocabulary.Execution.Setup.a M S r₀ + (k : Int)
      ≤ Restated.Vocabulary.Execution.Setup.a M S (r₀ + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hlt := hmono (Nat.lt_succ_self (r₀ + k))
      have hcast : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by push_cast; ring
      rw [← Nat.add_assoc, hcast]
      linarith [Int.add_one_le_iff.mpr hlt]
  refine ⟨(t - Restated.Vocabulary.Execution.Setup.a M S r₀).toNat + 1, ?_⟩
  have h1 := h ((t - Restated.Vocabulary.Execution.Setup.a M S r₀).toNat + 1)
  have h2 : t - Restated.Vocabulary.Execution.Setup.a M S r₀
      ≤ ((t - Restated.Vocabulary.Execution.Setup.a M S r₀).toNat : Int) := Int.self_le_toNat _
  have hcast : (((t - Restated.Vocabulary.Execution.Setup.a M S r₀).toNat + 1 : Nat) : Int)
      = ((t - Restated.Vocabulary.Execution.Setup.a M S r₀).toNat : Int) + 1 := by
    push_cast; ring
  rw [hcast] at h1
  linarith

/-- If every tick has an outcome, then under the listed premises and `hP`, there is a step `n₀` that
    is the tick at the switch round's action instant and a switch-round anchor `T₀` such that
    `AfterPhaseInvariantOverActiveSetsSince` holds at round `rW`, step `n₀`, switch step `n₀` and
    anchor `T₀`. -/
theorem claim13beBaseOverActiveSetsSince_anchored_of_premises (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
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
    Restated.switchRoundRegime_runAll_notHeld facts S Sched x v hsync hmono hawake hgst hcv hexec hmult hthird
      hcom hrec hlen' htd hn₀ hN
  have hfin := Restated.fin_at_switchRound_of_regime facts S Sched x v hsync hmono hawake hgst hcv hexec hmult
    hthird hcom hlen' htd hN hreg hn₀ htop
  have hchain : Restated.BaseSGOneChainAtSwitchRound M S Sched x v tE N :=
    Restated.baseSGOneChainAtSwitchRound_of_premises facts S Sched x v hsync hmono hawake hgst hcv hexec
      hmult hthird hcom hlen' htd hN hreg harW hn₀ htop (hP v N hN)
  have hgrade1 := Restated.grade1_at_switchRound_notHeld facts S Sched x v hsync hmono hawake hgst hcv hexec hmult
    hthird hcom hlen' htd hN hreg harW hn₀ hfin
    (fun heq => Restated.basePreviousRoundSGCompatibleWithAnchor_of_belowOpeningVotes facts S Sched x v
      hsync hmono hawake hgst hcv hexec hmult hthird hcom hlen' htd hN hreg heq (hP v N hN))
  have hTop : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x (Restated.switchRound M S tE) n₀ T :=
    { tick := hn₀
      inPlay := Restated.inPlay_at_switchRound_of_regime facts S Sched x v hmono hreg
      anchorEntry := Restated.anchorEntry_at_switchRound_of_regime facts S Sched x v hmono hexec hreg
      band := hband
      sg := Restated.sg_at_switchRound facts S Sched x v hsync hmono hawake hgst hcv hexec hmult hthird hcom
        hlen' htd hN hreg harW hn₀
      sgPairwise := Restated.sgPairwise_at_switchRound facts S Sched x v hmono hexec hN hn₀ hchain
      heads := Restated.headsBelow_of_regime facts S Sched x v hsync hmono hawake hgst hcv hexec hmult hthird
        hcom hlen' htd hN hreg harW
      fin := hfin
      grade1 := fun w hw' p _hpg1 hp m hm B b hb hbt => hgrade1 w p hp
        (fun h => (Finset.mem_sdiff.1 hw').2 (hmono _ _ hp h)) m hm B (hbt ▸ hb)
      grade1Performers := fun w hw' m hm B b hb hbt => hgrade1 w .g1
        (facts.gr.domain_le_action S _ .g1) (Finset.mem_sdiff.1 hw').2 m hm B (hbt ▸ hb)
      heightCeiling := Restated.heightCeiling_of_topHonestRow facts S Sched x hexec.toUnforgeability htop
      targetsTop := Restated.targetsTop_at_switchRound facts S Sched x v hsync hmono hawake hgst hcv hexec hmult
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
      grade1Performers := hTop.grade1Performers
      heightCeiling := hTop.heightCeiling
      targetsTop := hTop.targetsTop
      targetsSince := Restated.targetsSince_at_switchRound facts S Sched x v hsync hmono hawake hgst hcv hexec
        hmult hthird hcom hlen' htd hN hreg harW hn₀
        (fun _ w hw' p hp m hm B hB => hgrade1 w p hp (fun h => (Finset.mem_sdiff.1 hw').2 (hmono _ _ hp h)) m hm B hB)
        (fun heq => hclear v N blocked first i a ta Cfg T Tprev c0 n₀ hN hreg heq hn₀) }

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If `AfterPhaseInvariantOverActiveSetsSince` holds at the switch round `rW`, step `n₀`, switch
    step `n₀` and anchor `T₀`, and the step from the base anchor holds at `n₀` and `T₀`, then for
    every `k` it holds at round `rW + k`, with switch step `n₀` and an anchor that is `T₀` or a
    descendant of `T₀`. -/
theorem afterPhaseInvariantOverActiveSetsSince_of_stepFrom (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) {n₀ : Nat} {T₀ : NamedBlock V}
    (hbase : Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x (Restated.switchRound M S tE) n₀ n₀ T₀)
    (hstep : Restated.AfterPhaseStepOverActiveSetsSinceFrom M S Sched x tE n₀ T₀) :
    ∀ k : Nat, ∃ (n : Nat) (T : NamedBlock V),
      Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x (Restated.switchRound M S tE + k) n n₀ T ∧
        Block.Preceq T₀.erase T.erase := by
  intro k
  induction k with
  | zero => exact ⟨n₀, T₀, hbase, preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)⟩
  | succ k ih =>
    obtain ⟨n, T, hinv, hT⟩ := ih
    obtain ⟨n', T', hinv2, hTT'⟩ :=
      hstep (Restated.switchRound M S tE + k) n T (Nat.le_add_right _ _) hT hinv
    exact ⟨n', T', hinv2, preceq_trans_Preceq hT hTT'⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If `AfterPhaseInvariantOverActiveSetsSince` holds at the switch round `rW`, step `n₀`, switch
    step `n₀` and anchor `T₀`, and the step from the base anchor holds at `n₀` and `T₀`, then no two
    blocks finalized in the stores of two validators honest through their own reads conflict. -/
theorem claim13be_conclusion_of_base_and_stepFrom_overActiveSetsSince (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (n₀ : Nat) (T₀ : NamedBlock V)
    (hbase : Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x (Restated.switchRound M S tE) n₀ n₀ T₀)
    (hstep : Restated.AfterPhaseStepOverActiveSetsSinceFrom M S Sched x tE n₀ T₀) :
    ∀ (v₁ v₂ : V) (i j : Nat),
      Restated.HonestThrough M Sched x i v₁ → Restated.HonestThrough M Sched x j v₂ →
      Block.Compatible (x[i][v₁].st).st.core.F (x[j][v₂].st).st.core.F := by
  classical
  intro v₁ v₂ i j hhon₁ hhon₂
  -- one round whose action instant is past both reads, and the invariant there
  obtain ⟨k, hk⟩ :=
    exists_action_gt_kas facts S (Restated.switchRound M S tE) (max (x[i].time : Int) (x[j].time : Int))
  obtain ⟨n, T, hinv, -⟩ :=
    Restated.afterPhaseInvariantOverActiveSetsSince_of_stepFrom facts S Sched x tE hbase hstep k
  obtain ⟨htick1, -⟩ := Restated.tickStepAt_time facts x hinv.tick
  have hi : i ≤ n + 1 := by
    by_contra hcon
    have hle : (x[n + 1].time : Int) ≤ (x[i].time : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_of_lt (Nat.lt_of_not_le hcon))
    have hmx : (x[i].time : Int) ≤ max (x[i].time : Int) (x[j].time : Int) := le_max_left _ _
    rw [htick1] at hle
    linarith
  have hj : j ≤ n + 1 := by
    by_contra hcon
    have hle : (x[n + 1].time : Int) ≤ (x[j].time : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_of_lt (Nat.lt_of_not_le hcon))
    have hmx : (x[j].time : Int) ≤ max (x[i].time : Int) (x[j].time : Int) := le_max_right _ _
    rw [htick1] at hle
    linarith
  -- both finalized blocks are ancestors of that round's one anchor
  exact compatible_iff_Compatible.mpr
    (compatible_of_preceq_common_Preceq (hinv.fin v₁ i hi hhon₁) (hinv.fin v₂ j hj hhon₂))

end

end DecoupledConsensusModel.Sts.Restated
