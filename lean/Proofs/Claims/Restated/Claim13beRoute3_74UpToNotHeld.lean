import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_44UpTo
import Proofs.Claims.Restated.Claim13beRoute3_65
import Proofs.Claims.Restated.Claim13beRoute3_70
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_74
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Restated.Claim13beRoute3_74UpTo
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13beRoute3_74NotHeld

/-!
# The grade-1 clause at a round, for every validator not held at the grade's domain instant, with synchrony up to a cutoff

`grade1_atRound_upTo` and `grade1_at_switchRound_upTo` of `Claim13beRoute3_74UpTo.lean` with the honest active
attesters of the round replaced by every validator the adversary does not hold at the domain
instant of the grade read: the proof never used the reader's awake window.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the bundle along `Restated.runAllPath M S Sched x v N` and the hypotheses of
    `grade1_atRound_upTo_notHeld` on the regime and the named fact, `r` is positive,
    `tGAT + 1 ≤ S.a (r − 1)`, and every round-`(r − 1)` SG emission along that path of a validator
    not held selects only blocks compatible with `T`'s erasure. -/
private theorem grade1_inputs₇₄u (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    {tGAT tE : Int} {N : Nat} (hmono : Sched.MonotoneCorruption)
    (hgst : S.E.t_GST ≤ tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    {r : Round}
    (hrWN : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int)) (hn : (x[N].time : Int) ≤ tE)
    (hf : Restated.AdmissibleFieldsOn M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) }
      (Restated.runAllPath M S Sched x v N) (notHeldAt Sched) Finset.univ (tGAT + 1))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ r)
    (hprev : a.round = r →
      Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      (τ : Int) % S.E.Δ = 0 → u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out)
    -- Every validator whose round-`k` tick is an event of the run, for a round `k` whose grade-2
    -- window starts after `tGAT`, passes the grade-2 awake test on the node state the path holds
    -- before that tick.
    (hrun : ∀ k : Round, tGAT + 1 ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ (u : V) (j : Nat),
      (Restated.runAll M S Sched x v N).events[j]? =
        some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) →
      M.awake_for_grade2 (Setup.alwaysAwake S) u (Restated.runAllPath M S Sched x v N j u) k) :
    1 ≤ r ∧ tGAT + 1 ≤ (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) ∧
      Restated.HonestSGEmissionsCompatibleAtRoundOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) (r - 1) T.erase := by
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hX : ∀ t : Int, 0 ≤ t → notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ _ => Finset.subset_univ _
  have hXXb : (Finset.univ : Finset V) ⊆ Finset.univ := Finset.Subset.refl _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
  obtain ⟨hpredle, hrW1⟩ := pred_le_pred_pos_l74 a.round (r) hapos harW
  obtain ⟨-, -, hloPrev, -⟩ := Restated.loBounds_l70 facts S hapos hlo
  have hpost : tGAT + 1 ≤ (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) :=
    hloPrev.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hpredle)
  refine ⟨hrW1, hpost, ?_⟩
  rcases round_cases_l74 a.round (r) harW with hlt | heq | heq
  · have hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (r - 1)) ≤
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
          Record.Run V).horizon := by
      show (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) ≤ (x[N].time : Int)
      exact (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le _ 1)).trans hrWN
    exact ((hreg.laterHistory_main facts hf hHs hHsXb hX hXXb hcomOn hbelow hlt hlo
      (fun k hk u _ j hj => hrun k hk u j hj)).2 hhor).1
  · have hsrc := hreg.seed.sgEmissionsCompatible_of_source_of_frame_named facts hf hHs
      hHsXb hX hXXb hcomOn hreg.crossing hreg.frame hreg.c0le hreg.ready hreg.postPrev hlo
    rw [heq] at hsrc
    exact hsrc
  · exact hprev heq

/-- With synchrony only up to `x[N].time`: under the theorem's hypotheses, for a regime on
    `runAll M S Sched x v N`, read along `Restated.runAllPath M S Sched x v N` over the validators
    not held, whose source round is at or before `r`, with `n₀` the tick step at `S.a r` and
    `S.a r ≤ x[N].time ≤ tE`: if whatever a validator honest through its own read has finalized, at
    any step up to `n₀ + 1`, is an ancestor of `T`, and, when the source round is `r`,
    `BasePreviousRoundSGCompatibleWithAnchorAtRound` holds along that path, then every block whose
    grade test for round `r` at the store of a validator not held at that grade's domain instant, at
    any phase whose domain instant is at or before the action, can return `true` lies on one chain
    with `T`. -/
theorem grade1_atRound_upTo_notHeld (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {N : Nat} (hsync : Restated.SynchronyFromWakeBefore M S x (x[N].time : Int)) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (htd : Restated.TimeDiverges M x)
    {r : Round}
    (hNlo : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int)) (hNhi : (x[N].time : Int) ≤ tE)
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ r)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r))))
    (hfin : ∀ (v : V) (n' : Nat), n' ≤ n₀ + 1 → Restated.HonestThrough M Sched x n' v →
      Block.Preceq (x[n'][v].st).st.core.F T.erase)
    (hprev : a.round = r →
      Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T) :
    ∀ v : V, ∀ p : Protocol.Phase,
        M.domain S.E S.hc (r) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r)) →
      v ∉ Sched.adv (M.domain S.E S.hc (r) p) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r) p) →
      ∀ B : Block V,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (r)
          (M.early S.E S.hc (r) p)
          (M.late S.E S.hc (r) p) B ⇢ true →
      Block.compatible B T.erase = true := by
  intro w p hdom hw m hm B hB
  have hn : (x[N].time : Int) ≤ tE := hNhi
  have hrWN : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) := hNlo
  obtain ⟨hn₀1, hn₀0⟩ := Restated.tickStepAt_time facts x hn₀
  have hn₀N : n₀ + 1 ≤ N := by
    by_contra hcon
    have hle : ((x[N].time : Nat) : Int) ≤ ((x[n₀].time : Nat) : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (by omega)
    linarith
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  obtain ⟨hrW1, hpost, hsg⟩ := grade1_inputs₇₄u facts S Sched x v hmono hgst hthird hcom hrWN hn hf
    hreg harW hprev (fun k τ u hl _ => facts.ndRun.tick_outcome_sts S Sched x hvalid.idealization.root_injective hvalid.honestRootsNew k τ u hl)
    (Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake hn)
  have hmn₀ : m ≤ n₀ := by
    by_contra hcon
    have hlt := hm.1 n₀ (Nat.lt_of_not_le hcon)
    linarith
  have hmN : m + 1 ≤ N := (Nat.succ_le_succ hmn₀).trans hn₀N
  have hread := Restated.stateBeforeTime_runAll_stepBefore facts S Sched x v hm hmN w
  have hmtime : (x[m].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r)) := by
    have hle : ((x[m].time : Nat) : Int) ≤ ((x[n₀].time : Nat) : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x hmn₀
    linarith
  have hthr : Restated.HonestThrough M Sched x m w := by
    intro t' ht' hmem'
    have hr1 : 1 ≤ r := by
      have := Restated.NamedHeightRegimeRunOn.r0_le_round_l71 facts hf hreg
      omega
    have hm' : Restated.stepBeforeInstant M x m (M.domain S.E S.hc ((r - 1) + 1) p) := by
      rwa [Nat.sub_add_cancel hr1]
    have hmd := Restated.time_lt_domain_of_stepBefore facts S Sched x htd hm'
    rw [Nat.sub_add_cancel hr1] at hmd
    exact hw (hmono t' _ (ht'.trans (le_of_lt hmd)) hmem')
  have hwdom : w ∈ notHeldAt Sched (M.domain S.E S.hc (r) p) :=
    mem_notHeldAt.mpr hw
  have hdomainHor : M.domain S.E S.hc (r) p ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    exact hdom.trans hrWN
  have hFT : Block.Preceq
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.domain S.E S.hc (r) p)) w).st.core.F T.erase := by
    rw [hread]
    exact hfin w m (hmn₀.trans (Nat.le_succ _)) hthr
  have hgrade : M.gradeBool S.E
      (M.gradeView (M.toHealing (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.domain S.E S.hc (r) p)) w).st.core))
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.domain S.E S.hc (r) p)) w).st.core.F
      S.hc.η_SG (r) (M.early S.E S.hc (r) p)
        (M.late S.E S.hc (r) p) B ⇢ true := by
    rw [hread]
    exact hB
  have hkPrev : tGAT + 1 ≤ M.early S.E S.hc (r - 1) .g2 - S.E.Δ := by
    have hr0 := Restated.NamedHeightRegimeRunOn.r0_le_round_l71 facts hf hreg
    have hη := S.hc.η_SG_ge_one
    have h1 : (Restated.roundAt M S tGAT : Nat) + 1 + 2 ≤
        (Restated.roundAt M S tGAT : Nat) + S.hc.η_SG + 2 :=
      Nat.add_le_add_right (Nat.add_le_add_left hη _) 2
    have h2 : (Restated.roundAt M S tGAT : Nat) + 1 + 2 ≤ (r : Nat) :=
      h1.trans (hr0.trans harW)
    have hA1 : tGAT + 1 ≤
        Restated.Vocabulary.Execution.Setup.a M S (Restated.roundAt M S tGAT + 1) :=
      Int.add_one_le_iff.mpr (lt_of_le_of_lt (Restated.Vocabulary.Statements.roundAt_spec facts S tGAT)
        (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S (Nat.lt_succ_self _)))
    exact Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hA1
      (Restated.lt_pred_of_add_two_le_l54 h2)
  exact Restated.phaseGrade_compatible_of_previousSGHistory_namedOn facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs hHsXb hbelow hrW1 hpost hdomainHor hwdom hFT hsg
    hgrade (fun u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake
      hn (r - 1) hkPrev u j hj)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- With synchrony only up to the confirmation instant of the switch round's third slot: under the
    theorem's hypotheses, for a regime on `runAll M S Sched x v N`, read along
    `Restated.runAllPath M S Sched x v N` over the validators not held, whose source round is at or
    before the switch round `rW`, with `n₀` the tick step at `S.a rW`: if whatever a validator
    honest through its own read has finalized, at any step up to `n₀ + 1`, is an ancestor of `T`,
    and, when the source round is `rW`, `BasePreviousRoundSGCompatibleWithAnchor` holds along that
    path, then every block whose grade test for round `rW` at the store of a validator not held at
    that grade's domain instant, at any phase whose domain instant is at or before the action, can
    return `true` lies on one chain with `T`. -/
theorem grade1_at_switchRound_upTo_notHeld (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (hfin : ∀ (v : V) (n' : Nat), n' ≤ n₀ + 1 → Restated.HonestThrough M Sched x n' v →
      Block.Preceq (x[n'][v].st).st.core.F T.erase)
    (hprev : a.round = Restated.switchRound M S tE →
      Restated.BasePreviousRoundSGCompatibleWithAnchor M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) T) :
    ∀ v : V, ∀ p : Protocol.Phase,
        M.domain S.E S.hc (Restated.switchRound M S tE) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) →
      v ∉ Sched.adv (M.domain S.E S.hc (Restated.switchRound M S tE) p) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (Restated.switchRound M S tE) p) →
      ∀ B : Block V,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (Restated.switchRound M S tE)
          (M.early S.E S.hc (Restated.switchRound M S tE) p)
          (M.late S.E S.hc (Restated.switchRound M S tE) p) B ⇢ true →
      Block.compatible B T.erase = true := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  exact Restated.grade1_atRound_upTo_notHeld facts S Sched x v
    (fun k w sm hsend hle haw => hsync k w sm hsend (le_trans hle (le_of_eq hN)) haw)
    hmono hawake hgst hcv hvalid hawm hthird hcom htd
    (by rw [hN]; exact Restated.action_le_confirmation_third facts S _)
    (by rw [hN.trans hN'.symm]; exact hN'E) hreg harW hn₀ hfin hprev

end

end DecoupledConsensusModel.Sts.Restated
