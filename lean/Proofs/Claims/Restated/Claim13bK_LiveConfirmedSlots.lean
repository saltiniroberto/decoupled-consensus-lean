import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActive
import Proofs.Claims.Restated.Claim13bInvariantActiveSince
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bK_ConeAnchor
import Proofs.Claims.Restated.Claim13bK_ConeHeads
import Proofs.Claims.Restated.Claim13bK_ConeSlots
import Proofs.Claims.Restated.Claim13bK_ConfirmedOld
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettle
import Proofs.Claims.Restated.Claim13bK_FgJustified
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeDescendant
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bK_HeadsNewAnchor
import Proofs.Claims.Restated.Claim13bK_HeadsNewAnchorJoint
import Proofs.Claims.Restated.Claim13bK_HolderMargins
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStep
import Proofs.Claims.Restated.Claim13bStepActionF
import Proofs.Claims.Restated.Claim13bStepActiveJoint
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepSGMove
import Proofs.Claims.Restated.Claim13beRoute3_82
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSince
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_ConeAnchor
import Model.Conditions.Claim13bK_ConeSlots
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bK_GradePairwise
import Model.Conditions.Claim13bK_LiveConfirmedSlots
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepFieldsAt
import Model.Conditions.Claim13bStepGrade
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Proofs.Claims.Spec2Claims.Claim13bStepSGMove
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_5
import Model.Conditions.Claim13beRoute3_7
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_LiveConfirmedSlots

/-!
# Live confirmed blocks and honest heads after the switch round

From the joint invariant at a round at or after the switch round: the honest justified blocks are
ancestors of the round's anchor, the anchor is an ancestor of every later honest head, and so is
every block an honest confirmation tick writes as live confirmed. Stated over a model
`M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p74% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_74)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pHJ% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_HeadsNewAnchorJoint)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pCS% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConeSlots)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pCC% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConeChain)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- For every round `r` and step `n'`, some function `att` gives every validator an attestation its
    attestation duty can return at a round-`(r + 1)` action read. -/
private theorem exists_actionAttestationsOf_lcs (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) (n' : Nat) :
    ∃ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att := by
  have hne : ∀ q : V, ∃ a, a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S)
      (x[n'][q].st) q (r + 1) := fun q => by
    obtain ⟨na, hna⟩ := (p74% actionReadFrom_nonempty₇₄) facts (Setup.alwaysAwake S)
      (x[n'][q].st) (r + 1)
    obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract na.cache)
      (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node q) na.st na.record
    exact ⟨D.2.2, na, hna, D.1, D.2.1, hD⟩
  choose att hattq using hne
  exact ⟨att, fun q _ => hattq q⟩

/-- After the tick at slot `s`'s confirmation instant, the block `w` holds as confirmed either
    passes the slot-`s` confirmation eligibility test of `w`'s store before the step, or is that
    store's fork-choice root stamped with the confirmation instant. -/
private theorem live_confirmed_after_confirmation_tick_eligible_lcs (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {n : Nat} {s : Slot} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s)) {w : V}
    (haw : w ∈ Sched.awake (M.confirmation_time S.E s) \ Sched.adv (M.confirmation_time S.E s))
    (hneTickConf : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w) (M.confirmation_time S.E s) ⇢ out)
    -- `w`'s tick at step `n` passes the grade-2 awake test of slot `s + 1`'s round.
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) w
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w) (M.round_of S.hc (s + 1))) :
    (∃ el : Block V → Bool,
        Restated.Vocabulary.Protocol.confEligible M S.E (x[n][w].st).st.core s ⇢ el ∧
        el (x[n + 1][w].st).st.core.live_confirmed = true) ∨
      (x[n + 1][w].st).st.core.live_confirmed
        = Restated.Vocabulary.Protocol.confRoot M (Restated.confStoreAt M S (x[n][w].st) s) := by
  have _hr_0 : M.reachedNode (x[n][w].st) := Record.reachedNode_sts facts S Sched x n w
  have _hr_1 : M.reachedNode (x[n + 1][w].st) := Record.reachedNode_sts facts S Sched x (n + 1) w
  classical
  obtain ⟨t', hlbl, ht'⟩ := id hn
  have hct := facts.sch.confirmation_time_eq_support_cutoff_succ S.E s
  have hdvd : (t' : Int) % S.E.Δ = 0 := by
    rw [ht', hct]
    exact facts.sch.support_cutoff_emod_delta S (s + 1)
  have haw' : w ∈ Sched.awake (t' : Int) \ Sched.adv (t' : Int) := by rw [ht']; exact haw
  rcases Restated.st_succ_of_tick_awake facts S Sched x w hlbl haw' hdvd with
    ⟨out₁, hout, hst⟩ | ⟨hno, -⟩
  · rw [ht', hct] at hout
    obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (M.toHealing (x[n][w].st).st.core)
      (M.support_cutoff S.E (s + 1)) (x[n][w].st).cache
    obtain ⟨D, hD⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
      S.hc (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))) (s + 1 - 1)
    obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core (s + 1 - 1)
    have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (n) w (M.support_cutoff S.E (s + 1))
    have hlc := facts.nd.on_tick_emit_confirmation_of_outcomes (Setup.alwaysAwake S) w _
      (s + 1) (Nat.succ_pos s) out₁ hout c
      (by rw [Record.wakeStage_st facts, Record.wakeStage_cache facts]; exact hc) D
      (by rw [Record.wakeStage_st facts]; exact hD)
      (by rw [Restated.alwaysAwake_alwaysAwake, ← hct]; exact hrun)
    have key : (x[n + 1][w].st).st.core.live_confirmed = X.live_confirmed := by
      rw [hst, hlc, facts.dt.named_update_confirmation_with_core _ _ _ _ _ D hD X hX]
    rw [Nat.add_sub_cancel] at hX
    have hconf : Restated.confStoreAt M S (x[n][w].st) s
        = (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core := by
      rw [Restated.confStoreAt, hct]
    rw [key, hconf]
    by_cases hroot : X.live_confirmed = Restated.Vocabulary.Protocol.confRoot M
        (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core
    · exact Or.inr hroot
    · left
      obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty
        (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core
      obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
        (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core.toHealing
        (M.round_of S.hc (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core.s)
      obtain ⟨score, hscore⟩ : ∃ score : Block V → ℕ, ∀ B, M.goldfish_score S.E
          (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core.T
          ((beforeCutoff tm (M.support_cutoff S.E s)
            ((M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core.pool s)).filter
            (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M S.E
              (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core s) u = true))
          ((beforeCutoff tm (M.support_cutoff S.E s)
            ((M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core.pool s)).filter
            (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M S.E
              (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core s) u = true))
          s B ⇢ score B :=
        ⟨fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose,
          fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose_spec⟩
      obtain ⟨W, hW⟩ := facts.fc.ghost_nonempty R
        (M.get_filtered_block_tree
          (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core.toHealing.toFG)
        score
        (fun B => decide (Restated.Vocabulary.Protocol.confCount M S.E
          (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core s < 2 * score B))
      have hwalk := facts.hd.update_confirmation_with_live_confirmed_walk_or_fgRoot
        (M.gradeContract c) S.E S.hc
        (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core
        s tm htm R hR score hscore W hW X hX
      have hgen := facts.hd.update_confirmation_with_live_confirmed_genuine_or_fgRoot
        (M.gradeContract c) S.E S.hc
        (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core
        s tm htm R hR score hscore W hW X hX
      rcases hwalk with hwalk | hfg
      · rcases hgen with ⟨-, -, hel⟩ | hfg
        · refine ⟨fun B => decide (Restated.Vocabulary.Protocol.confCount M S.E
            (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core s
              < 2 * score B), ?_, ?_⟩
          · rw [← (pHJ% confEligible_setClock_joint) facts S.E (x[n][w].st).st
              (M.support_cutoff S.E (s + 1))]
            refine ((pHJ% returns_bind_iff_joint) _ _ _).2 ⟨_, (pHJ% returns_map_intro_joint) _ _ _
              ((pHJ% returns_map_intro_joint) _ _ _ htm), ?_⟩
            refine ((pHJ% returns_bind_iff_joint) _ _ _).2
              ⟨score, ((pHJ% returns_lift_iff_joint) _ _).2 hscore, ?_⟩
            exact (Record.returns_pure _ _).2 rfl
          · rw [hwalk]
            exact hel
        · exact absurd hfg hroot
      · exact absurd hfg hroot
  · obtain ⟨o, ho⟩ := hneTickConf
    rw [← ht'] at ho
    exact absurd ho (hno o)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If the joint invariant holds at round `r`, at or after the switch round, with anchor `T`, then
    at every step from the switch step up to the step after the round-`(r + 1)` tick, the justified
    block of every honest validator is an ancestor of `T`. -/
theorem justified_preceq_anchor_ofJoint (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) :
    ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T.erase :=
  Restated.justified_preceq_anchor_after_switchW facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
    hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hAW hnW hr
    hJ.toAfterPhaseInvariantOverActiveSetsSince hTW hn'

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If the joint invariant holds at round `r`, at or after the switch round, with anchor `T`, then
    for every slot from round `r`'s third slot to the slot after round `(r + 1)`'s opening slot,
    every honest active member of the slot's committee votes for a descendant of `T`. -/
theorem headsBelow_range_ofJoint (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hw : Restated.WakesAtActionInstants M S Sched)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T) :
    ∀ s : Slot, (M.opening_slot S.hc r) + 2 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) + 1 →
      Restated.HeadsBelow M S Sched x T.erase s := by
  have hinvS := hJ.toAfterPhaseInvariantOverActiveSetsSince
  have hinv := hinvS.toTop
  have hJW : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n'' + 1 → Restated.HonestThrough M Sched x n₁ v →
        Block.Preceq (x[n₁][v].st).st.core.J T.erase :=
    fun n'' h => Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
      hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ h
  have hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T :=
    fun n'' h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hr hnW hinvS (hJW n'' h)
  have hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T :=
    fun n'' h => Restated.stepJustifiedRootUnderAnchor_of_afterSwitch facts S Sched x hr hnW hinvS (hJW n'' h)
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd r
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  obtain ⟨t', ht'E, ht's, ht'len, hcs'⟩ :=
    Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hr
  have hcs2 := Restated.committeeSleepinessW_at_heads_slot facts S Sched tE hmono hcom tGAT gap hgst hlen hphase
    hcs hr
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts S Sched x tE
    hexec hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hcross hn'
  -- the opening slot's support cutoff is before its view freeze, which is before `S.a (r + 1)`
  have hsR : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1))) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1 := by
    have e1 := facts.sch.Sts_support_cutoff_lt_view_freeze S.E ((M.opening_slot S.hc (r + 1)))
    have e2 := facts.sch.view_freeze_lt_confirmation_time S.E ((M.opening_slot S.hc (r + 1)))
    rw [Restated.confirmation_time_opening_slot facts S (r + 1)] at e2
    have e2' := Int.add_one_le_of_lt e2
    linarith
  exact Restated.headsBelow_range_afterPhase facts S Sched x hexec hsync hmult htd hmono hgst hcv
    (fun t h1 h2 => hphase t h1 (le_trans h2 ht'E))
    (fun t h => hthird t (le_trans h ht'E)) hcs' ht'len
    (Restated.deliveredDescendantUnderFinalized_anchor facts S Sched x hn' hfin tGAT)
    (Restated.finalizedPreceqAtSteps_anchor facts S Sched x hn' hfin tGAT)
    (s₀ := (M.opening_slot S.hc r) + 2) (s₁ := (M.opening_slot S.hc (r + 1)))
    (Nat.succ_pos _) ht's hsR
    (fun s h0 h1 => Restated.coneAnchorCompatible_range_at_anchor facts S
      Sched x tE hexec hmono htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr
      hinv hcross hjust hw (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched (show v ∈ Sched.awakeThroughout (M.a S.hc S.E.Δ _ - wAttest S) (M.a S.hc S.E.Δ _) from (Finset.mem_sdiff.1 hv).1) (by linarith [twelve_delta_le_wAttest S, S.E.Δ_pos]) (le_refl _), (Finset.mem_sdiff.1 hv).2⟩)) s h0 h1)
    (fun s h0 h1 => Restated.coneAnchorChainInTree_at_anchor_of_committee facts S Sched x tE
      hexec hmono htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hcs2
      (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) s h0 h1)
    hinv.heads (by intro s _ _ m hm q hq; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hm (facts.sch.vote_time_emod_delta S _) (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h => ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩)) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If the joint invariant holds at round `r`, at or after the switch round, with anchor `T`, then
    for every `k` there are a tick step and an anchor `T_k` such that the joint invariant holds at
    round `r + k` with them, and `T` is an ancestor of `T_k`. -/
theorem exists_anchor_chain (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T) :
    ∀ k : Nat, ∃ (n_k : Nat) (T_k : NamedBlock V),
      Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + k) n_k n_W T_k ∧
        Block.Preceq T.erase T_k.erase ∧ Block.Preceq T_W.erase T_k.erase := by
  intro k
  induction k with
  | zero => exact ⟨n, T, hJ, (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)), hTW⟩
  | succ k ih =>
    obtain ⟨n_k, T_k, hJk, hTk, hWk⟩ := ih
    obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd (r + k)
    obtain ⟨att, hatt⟩ := exists_actionAttestationsOf_lcs facts S Sched x (r + k) n'
    obtain ⟨-, hstep⟩ := Restated.afterPhaseJointRound_of_premises facts S Sched x tE hexec hmono htd hcatch
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB'
      hnW hAW hJswitch (le_trans hr (Nat.le_add_right r k)) hWk hJk hn'
    obtain ⟨hJ', hTT'⟩ := hstep att hatt
    exact ⟨n', _, hJ', preceq_trans_Preceq hTk hTT', preceq_trans_Preceq hWk hTT'⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If the joint invariant holds at round `r`, at or after the switch round, with anchor `T`, then
    every honest active member of the committee of every slot from round `r`'s third slot on votes
    for a descendant of `T`. -/
theorem anchor_ancestorOfHonestHeadsFrom (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x T.erase ((M.opening_slot S.hc r) + 2) := by
  intro s hs0
  obtain ⟨k, hk0, hk1⟩ := facts.gr.exists_round_of_slot S.hc r hs0
  obtain ⟨n_k, T_k, hJk, hTk, hWk⟩ := Restated.exists_anchor_chain facts S Sched x tE hexec hmono htd hcatch
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB'
    hnW hAW hJswitch hr hTW hJ k
  exact Restated.headsBelow_mono facts S Sched x hTk
    (Restated.headsBelow_range_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync hthird hphase
      hrsW hmult hcv hcs hcom hw hrec hprev hclear hB' hnW hAW
      (le_trans hr (Nat.le_add_right r k)) hWk hJk s hk0 hk1)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- A validator in `activeAtW S Sched s'`, with `s + 2 ≤ s' ≤ s + R`, is awake at every instant from
    `slotStart s − Δ` to slot `s`'s confirmation instant. -/
theorem awakeThroughout_confirmation_of_activeAtW (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    {s s' : Slot} {v : V} (hv : v ∈ activeAtW S Sched s') (h2 : s + 2 ≤ s') (hR : s' ≤ s + S.hc.R) :
    v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ) (M.confirmation_time S.E s) := by
  have hd := S.E.Δ_pos
  have hwv : wVote S = (4 * (S.hc.R : Int) + 2) * S.E.Δ := rfl
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right s 2) h2)
  have h2' : (2 : Int) ≤ ((k : Nat) : Int) := by exact_mod_cast Nat.le_of_add_le_add_left h2
  have hR' : ((k : Nat) : Int) ≤ (S.hc.R : Int) := by
    exact_mod_cast Nat.le_of_add_le_add_left hR
  have hss := slotStart_add S.E.Δ s k
  have hct := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s
  refine awakeThroughout_mono Sched hv ?_ ?_
  · rw [hss, hwv]; nlinarith
  · rw [← hct, hss]; nlinarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- For every choice `att` of the round-`(r + 1)` action attestations, every honest active member of
    the committee of the slot after round `(r + 1)`'s opening slot votes there for a descendant of
    the round-`(r + 1)` anchor built from `att`. -/
theorem headsBelow_secondSlot_at_newAnchor (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hw : Restated.WakesAtActionInstants M S Sched)
    {r : Round} {n n' n'' n_W : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n₀ : Nat, Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n₀ T)
    (hjust : ∀ n₀ : Nat, Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n₀ T)
    (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) (hn'' : Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))))
    {att : V → NamedAttestation V} (hatt : Restated.ActionAttestationsOf M S Sched x r n' att)
    (hTT' : Block.Preceq T.erase (Restated.newAnchor M S Sched x r n' att T).erase)
    (hJ' : ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n'' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J (Restated.newAnchor M S Sched x r n' att T).erase)
    (hP : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
      a.round = r → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Restated.HeadsBelow M S Sched x C.erase ((M.opening_slot S.hc (r + 1))))
    (hQ : Restated.ConfirmedCompatibleFreshSGOverHonRound M S Sched x r n n') :
    Restated.HeadsBelow M S Sched x (Restated.newAnchor M S Sched x r n' att T).erase ((M.opening_slot S.hc (r + 1)) + 1) := by
  classical
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hRd : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have hsucc := facts.gr.action_succ_eq_add_rounds S r
  have hsucc1 := facts.gr.action_succ_eq_add_rounds S (r + 1)
  have hn := hinv.tick
  obtain ⟨hn1, -⟩ := Restated.tickStepAt_time facts x hn
  obtain ⟨hn'1, hn'0⟩ := Restated.tickStepAt_time facts x hn'
  have hnn' : n + 1 ≤ n' := Restated.tick_succ_le_tick_succ_round facts S Sched x hn hn'
  have hnWn : n_W ≤ n := Restated.tick_le_of_round_le facts S Sched x hnW hn hr
  have hnWn' : n_W ≤ n' := by omega
  -- a round opens at the proposal instant of its opening slot, at or before the action instant
  have hopen : M.opening S.E S.hc r ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
    show _ ≤ M.a S.hc S.E.Δ r
    rw [facts.gr.opening_eq_proposal_time, facts.sch.a_eq_confirmation_time]
    exact facts.sch.proposal_time_le_confirmation_time _ _
  have htGAT : tGAT ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    le_trans (Restated.tGAT_le_switchOpening facts S tGAT tE gap hgst hlen)
      (le_trans (Restated.switchOpening_le_opening facts S hr) hopen)
  have hso : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 6 * S.E.Δ := by
    rw [← Restated.confirmation_time_opening_slot facts S (r + 1)]
    exact (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E _).symm
  have hlo : tGAT ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) := by linarith
  have hRs : (M.opening_slot S.hc r) + 2 ≤ (M.opening_slot S.hc (r + 1)) := by
    rw [facts.gr.opening_slot_succ]
    exact Nat.add_le_add_left (le_trans (by decide) S.hc.R_ge_three) _
  obtain ⟨t', ht'E, ht's, ht'len, hcs'⟩ :=
    Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hr
  have hcs2 := Restated.committeeSleepinessW_at_heads_slot facts S Sched tE hmono hcom tGAT gap hgst hlen hphase
    hcs hr
  have hsE : t' ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) :=
    le_trans ht's (slotStart_mono S hRs)
  have hfinT := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts S Sched x tE
    hexec hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hcross hn'
  have hjustT := Restated.justified_old_anchor_before_succ_tick_of_hypotheses facts S Sched x tE
    hexec hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hjust hn'
  have hprevT := Restated.headsBelow_secondSlot_at_anchor facts S Sched x tE hexec hmono htd hsync hmult hcom
    tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hjust hw hn'
  obtain ⟨T', hT'⟩ : ∃ T' : NamedBlock V, T' = Restated.newAnchor M S Sched x r n' att T := ⟨_, rfl⟩
  rw [← hT'] at hTT' hJ' ⊢
  have hF' := Restated.fin_preceq_before_succ_succ_tick facts S Sched x hn'' hnWn' hfinT hTT' hJ'
  have hJ'' := Restated.just_preceq_before_succ_succ_tick facts S Sched x hn'' hnWn' hjustT hTT' hJ'
  have hvt1 : M.vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1)
      = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 5 * S.E.Δ + 4 * S.E.Δ * ((1 : Nat) : Int) :=
    Restated.vote_time_opening_slot_add facts S (r + 1) 1
  push_cast at hvt1
  have hFJ0 : Restated.VoteFinJustCompatible M S x T'.erase ((M.opening_slot S.hc (r + 1))) :=
    Restated.voteFinJustCompatible_before_succ_succ_tick facts S Sched x hmono hn hF' hJ''
      (by rw [hvt1]; linarith) (by rw [hvt1]; linarith)
  by_cases hex : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C
  ·
    have hchoice : T' = hex.choose := by
      rw [hT']
      show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C then h.choose else T)
        = hex.choose
      rw [dif_pos hex]
    obtain ⟨q, hqW, hmem, h₀, tmo, hvote⟩ := hex.choose_spec.2.2.2
    rw [← hchoice] at hmem hvote
    have hq : q ∈ Restated.freshAttesters M S Sched x (r + 1) (n' + 1) :=
      Restated.freshAttestersW_subset_freshAttesters facts S Sched x (r + 1) (n' + 1) hqW
    obtain ⟨nr, hnr, ns, rec, hD⟩ := hatt q hqW
    obtain ⟨o, ho⟩ := (pHJ% actionFGSource_nonempty_joint) facts (Setup.alwaysAwake S) nr
    obtain ⟨Cfg, rfl, hpre⟩ :=
      Restated.entry_preceq_source facts S Sched x hexec hn' hq hmem rfl nr hnr
        (ns, rec, att q) hD hvote o ho
    have hCfg := ho
    have hhsq : M.toHealing nr.st.core ∈ Restated.actionHealingStore M S (x[n'][q].st) (r + 1) :=
      ⟨nr, hnr, rfl⟩
    have qH : q ∈ Restated.HonRound M S Sched (r + 1) :=
      Restated.freshAttestersW_subset_honRound facts S Sched x (le_of_eq hn'1.symm) hqW
    have hqn' : Restated.HonestThrough M Sched x n' q := fun t ht =>
      Restated.honestThrough_of_mem_freshAttestersW facts hqW t
        (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_succ n')))
    have hqm : tGAT ≤ (x[n'].time : Int) := by linarith
    have hqlt : (x[n'].time : Int) < (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := by linarith
    have hAB0 : ∀ X : Block V, Block.Preceq T'.erase X →
        (∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
          a.round = r → a.val_index = v_1 →
          (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
          ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
          Block.compatible C.erase X = true) →
        Restated.ConeAnchorCompatible M S x T'.erase ((M.opening_slot S.hc (r + 1))) := fun X hDX hX =>
      Restated.coneAnchorCompatible_of_voteReads facts S x
        (Restated.voteGradeOneCompatible_of_gradedCompatible facts S Sched x hmono hw
          (Restated.graded_compatible_of_sgCompatible facts S Sched x tE hexec hmono htd
            hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hDX hX)
          (j := 1) (by have := S.hc.R_ge_three; omega) rfl)
        hFJ0
    rcases Restated.source_cases facts S (x[n'][q].st) (r + 1) nr hnr Cfg hCfg with hlc | hQ2
    ·
      have hDX : Block.Preceq T'.erase (M.toHealing nr.st.core).live_confirmed :=
        preceq_trans_Preceq hpre hlc
      have hX : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
          a.round = r → a.val_index = v_1 →
          (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
          ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
          Block.compatible C.erase (M.toHealing nr.st.core).live_confirmed = true :=
        fun v_1 hv_1 a har hai has C hC hac => hQ q qH v_1 hv_1 a har hai has C hC hac _ hhsq
      have hFq : Block.Preceq (M.toHealing nr.st.core).F T.erase := by
        rw [Restated.actionHealingStore_F facts S _ _ _ hhsq]; exact hfinT q n' le_rfl hqn'
      have hJq : (M.toHealing nr.st.core).h_max = (M.toHealing nr.st.core).h_j + 1 →
          Block.Preceq (M.toHealing nr.st.core).J T.erase := by
        intro hroot
        rw [Restated.actionHealingStore_h_max facts S _ _ _ hhsq,
          Restated.actionHealingStore_h_j facts S _ _ _ hhsq] at hroot
        rw [Restated.actionHealingStore_J facts S _ _ _ hhsq]
        exact hjustT q n' hnn' le_rfl hqn' hroot
      have hrootq := Restated.confRoot_setClock_preceq_ofAction facts S (x[n'][q].st) r _ hhsq hFq hJq
      have hct : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
        Restated.confirmation_time_opening_slot facts S (r + 1)
      have hn'c : Restated.tickStepAt M x n'
          (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) := by
        rw [hct]; exact hn'
      have hqaw := Restated.honRound_awakeThroughout_confirmation facts S Sched (r + 1) qH
      have hqA : q ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := (Finset.mem_sdiff.1 qH).2
      have hqh : HonestThroughTime Sched
          (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) q :=
        fun t'' ht'' hin => hqA (hmono _ _ (by rw [← hct]; exact ht'') hin)
      have hpath0 : Restated.ConeAnchorChainInTree M S x T'.erase ((M.opening_slot S.hc (r + 1))) := by
        rcases (pHJ% actionHealingStore_live_confirmed_cases_joint) facts S (x[n'][q].st) (r + 1) _ hhsq with
          ⟨el, hel', hel⟩ | hlcR
        · rw [Restated.slotOf_a_sub_one facts S (r + 1)] at hel'
          exact Restated.coneAnchorChainInTree_of_eligibleConfirmation facts S Sched x tE hexec hmono htd hsync
            hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hqaw hqh el hel' hel hDX
            hTT' hlo le_rfl (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
        · have hlc2 : Block.Preceq T'.erase (Restated.Vocabulary.Protocol.confRoot M
              (M.ns_setClock S.E (x[n'][q].st).st
                (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))))).core) := by
            rw [hct, ← hlcR]; exact hDX
          have heq : T'.erase = T.erase := Block.preceq_antisymm (preceq_eq_true_iff_Preceq.mpr (preceq_trans_Preceq hlc2 hrootq))
            (preceq_eq_true_iff_Preceq.mpr hTT')
          rw [heq]
          exact Restated.coneAnchorChainInTree_at_anchor_of_committee facts S Sched x tE
            hexec hmono htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hcs2
            (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) _ hRs le_rfl
      -- the opening slot's view freeze is strictly before `S.a (r + 1)`
      have hvf : M.view_freeze S.E ((M.opening_slot S.hc (r + 1))) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1 := by
        have e1 := facts.sch.view_freeze_lt_confirmation_time S.E ((M.opening_slot S.hc (r + 1)))
        rw [hct] at e1
        have e1' := Int.add_one_le_of_lt e1
        linarith
      have h1 := Restated.headsBelow_secondSlot_of_confirmed_afterPhase facts S Sched x hexec hsync hmult htd
        hmono hgst hcv (fun t h1 h2 => hphase t h1 (le_trans h2 ht'E))
        (fun t h => hthird t (le_trans h ht'E)) hcs' ht'len
        (Restated.deliveredDescendantUnderFinalized_anchor facts S Sched x hn' hfinT tGAT)
        (Restated.finalizedPreceqAtSteps_anchor facts S Sched x hn' hfinT tGAT) hlo hvf hn' qH _ hhsq rfl
        hTT' hDX hrootq hprevT (hAB0 _ hDX hX) hpath0 (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
        (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
      exact h1
    ·
      -- one grade read and one grade-2 outcome at `nr`; the read's Q2 is the grade-2 outcome
      obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract nr.cache) S.E S.hc
        (M.toHealing nr.st.core) (r + 1)
      obtain ⟨o2, ho2⟩ := facts.gr.grade2Block_nonempty (M.toHealing nr.st.core)
        (M.readFrame nr.cache (M.toHealing nr.st.core) (r + 1))
      have hgo2 := facts.nd.ModelProperties_gradeContract_read_Q2 nr.cache S.E S.hc
        (M.toHealing nr.st.core) (r + 1) g hg o2 ho2
      have hgQ := hQ2 g ((facts.nd.gradeContract_read nr.cache S.E S.hc (M.toHealing nr.st.core)
        (r + 1) g).1 hg)
      obtain ⟨root, hroot, hQroot⟩ := facts.gr.grade2Block_preceq_root o2 ho2 (hgo2.symm.trans hgQ)
      obtain ⟨m₂, G, hm₂, hGall, hrootG⟩ := Restated.actionFrame_g2_provenance facts S Sched x hn' q
        root _ ⟨nr, hnr, rfl⟩ hroot
      obtain ⟨bG, hbG⟩ := facts.gr.gradeBool_nonempty S.E
        (M.gradeView (M.toHealing (x[m₂][q].st).st.core)) (x[m₂][q].st).st.core.F S.hc.η_SG (r + 1)
        (M.early S.E S.hc (r + 1) .g2) (M.late S.E S.hc (r + 1) .g2) G
      have hG : M.gradeBool S.E (M.gradeView (M.toHealing (x[m₂][q].st).st.core))
          (x[m₂][q].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g2)
          (M.late S.E S.hc (r + 1) .g2) G ⇢ true := by
        rw [← hGall bG hbG]; exact hbG
      obtain ⟨v_2, hv_2, a₂, har₂, hai₂, has₂, C₂, hC₂, hac₂, hGC₂⟩ :=
        Restated.graded_preceq_freshSG_of_premises facts S Sched x tE hexec hmono htd hsync
          hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross qH
          (facts.gr.domain_le_action S (r + 1) .g2) hm₂ G hG (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
          (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched (show v ∈ Sched.awakeThroughout (M.a S.hc S.E.Δ _ - wAttest S) (M.a S.hc S.E.Δ _) from (Finset.mem_sdiff.1 hv).1) (by linarith [twelve_delta_le_wAttest S, S.E.Δ_pos]) (le_refl _), (Finset.mem_sdiff.1 hv).2⟩))
      have hDX : Block.Preceq T'.erase C₂.erase :=
        preceq_trans_Preceq hpre (preceq_trans_Preceq hQroot (preceq_trans_Preceq hrootG hGC₂))
      have hX : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
          a.round = r → a.val_index = v_1 →
          (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
          ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
          Block.compatible C.erase C₂.erase = true :=
        fun v_1 hv_1 a har hai has C hC hac =>
          hinv.sgPairwise v_1 hv_1 v_2 hv_2 a a₂ har hai has har₂ hai₂ has₂ C C₂ hC hac hC₂ hac₂
      have hv2h : Restated.HonestThrough M Sched x (n + 1) v_2 := fun t ht hin =>
        (Finset.mem_sdiff.1 hv_2).2 (hmono _ _ (by rw [hn1] at ht; exact ht) hin)
      -- `S.a r + Δ` is before the view freeze of round `(r + 1)`'s opening slot
      have hvf : (x[n + 1].time : Int) + S.E.Δ
          < M.view_freeze S.E ((M.opening_slot S.hc (r + 1))) := by
        have hR3 : (M.opening_slot S.hc r) + 1 + 1 + 1 ≤ (M.opening_slot S.hc (r + 1)) := by
          rw [facts.gr.opening_slot_succ]
          exact Nat.add_le_add_left S.hc.R_ge_three _
        have e1 : Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ
            = M.view_freeze S.E ((M.opening_slot S.hc r) + 1) :=
          facts.sch.a_add_delta_eq_view_freeze S r
        have e2 := facts.sch.view_freeze_lt_vote_time_succ S.E ((M.opening_slot S.hc r) + 1)
        have e3 := facts.sch.vote_time_add_delta_le_confirmation_time S ((M.opening_slot S.hc r) + 1 + 1)
        have e4 := facts.sch.confirmation_time_eq_support_cutoff_succ S.E
          ((M.opening_slot S.hc r) + 1 + 1)
        have e5 := facts.sch.support_cutoff_mono S.E hR3
        have e6 := facts.sch.Sts_support_cutoff_lt_view_freeze S.E ((M.opening_slot S.hc (r + 1)))
        rw [hn1]; linarith
      have hpath0 : Restated.ConeAnchorChainInTree M S x T'.erase ((M.opening_slot S.hc (r + 1))) :=
        Restated.coneAnchorChainInTree_of_heldDescendant facts S Sched x tE hexec hmono htd hsync hmult tGAT gap
          hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hC₂ hv2h (by rw [hn1]; exact htGAT)
          hDX hTT' hvf le_rfl (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
      have h0 : Restated.HeadsBelow M S Sched x T'.erase ((M.opening_slot S.hc (r + 1))) :=
        fun w mw hw' hmw G hG => preceq_trans_Preceq hDX (hP v_2 hv_2 a₂ har₂ hai₂ has₂ C₂ hC₂ hac₂ w mw
          hw' hmw G hG)
      have hsR : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1)))
          ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 := by
        -- the opening slot's support cutoff is before its view freeze, which is before
        -- `S.a (r + 1)`
        have e1 := facts.sch.Sts_support_cutoff_lt_view_freeze S.E ((M.opening_slot S.hc (r + 1)))
        have e2 := facts.sch.view_freeze_lt_confirmation_time S.E ((M.opening_slot S.hc (r + 1)))
        rw [Restated.confirmation_time_opening_slot facts S (r + 1)] at e2
        linarith
      have hpos : 0 < (M.opening_slot S.hc (r + 1)) := facts.gr.opening_slot_pos S (Nat.succ_pos r)
      have hrange := Restated.headsBelow_range_afterPhase facts S Sched x hexec hsync hmult htd hmono hgst hcv
        (fun t h1 h2 => hphase t h1 (le_trans h2 ht'E))
        (fun t h => hthird t (le_trans h ht'E)) hcs' ht'len
        (Restated.deliveredDescendant_before_succ_succ_tick facts S Sched x hF' tGAT)
        (Restated.finalizedPreceqAtSteps_before_succ_succ_tick facts S Sched x hF' tGAT)
        (s₀ := (M.opening_slot S.hc (r + 1))) (s₁ := (M.opening_slot S.hc (r + 1)))
        hpos hsE hsR
        (fun s h0' h1' => by
          have hs : s = (M.opening_slot S.hc (r + 1)) := le_antisymm h1' h0'
          rw [hs]; exact hAB0 _ hDX hX)
        (fun s h0' h1' => by
          have hs : s = (M.opening_slot S.hc (r + 1)) := le_antisymm h1' h0'
          rw [hs]; exact hpath0)
        h0 (by intro s _ _ m hm q hq; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hm (facts.sch.vote_time_emod_delta S _) (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h => ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩)) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
      exact hrange _ (Nat.le_succ _) le_rfl
  ·
    have hchoice : T' = T := by
      rw [hT']
      show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C then h.choose else T) = T
      rw [dif_neg hex]
    rw [hchoice]
    exact hprevT

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If the joint invariant holds at round `r`, at or after the switch round, with anchor `T`, then
    for a slot `s` of round `r` and an honest validator `v`, the fork-choice root of `v`'s store at
    slot `s`'s confirmation tick, with its clock set to that instant, is an ancestor of `T`. -/
theorem confRoot_preceq_anchor_atSlot (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T)
    {s : Slot} (hs0 : (M.opening_slot S.hc r) ≤ s) (hs1 : s ≤ (M.opening_slot S.hc (r + 1)))
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s))
    {v : V} (hvm : Restated.HonestThrough M Sched x m v) :
    Block.Preceq (Restated.Vocabulary.Protocol.confRoot M (Restated.confStoreAt M S (x[m][v].st) s)) T.erase := by
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd r
  have hn := hJ.toAfterPhaseInvariantOverActiveSetsSince.tick
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn
  obtain ⟨hn'1, -⟩ := Restated.tickStepAt_time facts x hn'
  obtain ⟨hm1, hm0⟩ := Restated.tickStepAt_time facts x hm
  have hct0 : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ M.confirmation_time S.E s := by
    rw [← Restated.confirmation_time_opening_slot facts S r]
    rw [← facts.sch.slotStart_add_six_delta_eq_confirmation_time, ← facts.sch.slotStart_add_six_delta_eq_confirmation_time]
    linarith [slotStart_mono S hs0]
  have hct1 : M.confirmation_time S.E s ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := by
    rw [← Restated.confirmation_time_opening_slot facts S (r + 1)]
    rw [← facts.sch.slotStart_add_six_delta_eq_confirmation_time, ← facts.sch.slotStart_add_six_delta_eq_confirmation_time]
    linarith [slotStart_mono S hs1]
  have hnm : n ≤ m := by
    by_contra hcon
    have hle : m + 1 ≤ n := by omega
    have h1 := Restated.time_mono_int facts S Sched x hle
    linarith
  have hmn' : m ≤ n' := by
    by_contra hcon
    have hle : n' + 1 ≤ m := by omega
    have h1 := Restated.time_mono_int facts S Sched x hle
    linarith
  have hnWn : n_W ≤ n := Restated.tick_le_of_round_le facts S Sched x hnW hn hr
  have hJT : Block.Preceq (x[m][v].st).st.core.J T.erase :=
    Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync hthird
      hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ hn' v m (by omega)
      (by omega) hvm
  have hFT : Block.Preceq (x[m][v].st).st.core.F T.erase :=
    preceq_trans_Preceq (Restated.finalized_preceq_justified_sts facts S Sched x m v) hJT
  exact facts.fc.fgRoot_preceq_ofJustifiedBranch (stH := (M.toHealing (Restated.confStoreAt M S (x[m][v].st) s)))
    (by
      rw [facts.sto.Sts_toHealing_F]
      show (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core.F
        ⪯ T.erase
      rw [facts.hd.setClock_core_F]
      exact hFT)
    (fun _ => by
      rw [facts.sto.Sts_toHealing_J]
      show (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core.J
        ⪯ T.erase
      rw [facts.hd.setClock_core_J]
      exact hJT)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If every honest active member of slot `s`'s committee votes for a descendant of `B`, and the
    store of an honest validator `v` awake through slot `s`'s confirmation window passes slot `s`'s
    eligibility test for `H`, then `H` and `B` lie on one chain. -/
theorem eligible_compatible_of_cone (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x)
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int} (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE)
    {B : Block V} (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT tR B)
    (hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x tGAT tR B)
    {s : Slot} (hs : 0 < s) (hslo : tGAT ≤ slotStart S.E.Δ s)
    (hanchor : tE ≤ slotStart S.E.Δ (s + 1))
    (hsR : M.support_cutoff S.E s ≤ tR)
    (hprev : Restated.HeadsBelow M S Sched x B s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s))
    {v : V}
    (hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    {H : Block V} {el : Block V → Bool}
    (hel' : Restated.Vocabulary.Protocol.confEligible M S.E (x[m][v].st).st.core s ⇢ el)
    (hel : el H = true) :
    Block.compatible H B = true := by
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  -- the support cutoff of a positive slot is two delays after its start
  have hsc : M.support_cutoff S.E s = slotStart S.E.Δ s + 2 * S.E.Δ := by
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, (Nat.succ_pred_eq_of_pos hs).symm⟩
    rw [← facts.sch.confirmation_time_eq_support_cutoff_succ,
      ← facts.sch.slotStart_add_six_delta_eq_confirmation_time, slotStart_succ]
    ring
  have hct : M.confirmation_time S.E s = slotStart S.E.Δ s + 6 * S.E.Δ :=
    (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s).symm
  obtain ⟨-, hmself⟩ := Restated.tickStepAt_time facts x hm
  have hmrlo : M.support_cutoff S.E s ≤ (x[m].time : Int) := by
    rw [hsc]; rw [hct] at hmself; linarith
  have hmrc : (x[m].time : Int) ≤ M.confirmation_time S.E s := by
    rw [hct]; rw [hct] at hmself; linarith
  have hwaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s) :=
    awakeThroughout_mono Sched hvaw (by linarith) (by rw [hsc, hct]; linarith)
  have hw : v ∉ Sched.adv (x[m].time : Int) := hvh _ hmrc
  have hwh : v ∉ Sched.adv (slotStart S.E.Δ s) := hvh _ (by rw [hct]; linarith)
  obtain ⟨mv, hmv⟩ := Restated.exists_tickStepAt facts x htd (facts.sch.vote_time_pos S hs)
  have hheads := Restated.coneHeads_afterPhase facts S Sched x hexec hsync hmult htd hmono hgst hcv hawake hthird
    hcs hlen hunder hunderS hprev hmv hmrlo hslo hsR hw hwaw (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
  have hcone := Restated.coneSupport_at_confirmation facts S Sched x hexec hsync htd hmono hcs hs hanchor
    (le_trans hgst hslo) hmv hmrlo hmrc hwaw hwh
    (fun q hq => by
      obtain ⟨G, hG⟩ := (pCS% gfHeadFrom_nonempty_cs) facts S (x[mv][q].st) s
      exact ⟨G, hG, hheads q hq G hG⟩)
    (by intro q hq; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hmv (facts.sch.vote_time_emod_delta S _) (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h => ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩))
    (by intro n hn; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hn (slotStart_emod_delta S _) (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hwaw (le_refl _) (by rw [hsc]; linarith), hwh⟩))
  rw [← (pHJ% confEligible_setClock_joint) facts S.E (x[m][v].st).st (M.confirmation_time S.E s)]
    at hel'
  obtain ⟨votes, hvv, hrv⟩ := ((pHJ% returns_bind_iff_joint) _ _ _).1 hel'
  obtain ⟨sc, hsc, hp⟩ := ((pHJ% returns_bind_iff_joint) _ _ _).1 hrv
  have hsc' := ((pHJ% returns_lift_iff_joint) _ _).1 hsc
  rw [Record.returns_pure] at hp
  subst hp
  simp only [Restated.Vocabulary.Protocol.confCount, decide_eq_true_eq] at hel
  -- `B` passes the eligibility test at the same store
  have hc := hcone votes hvv
  obtain ⟨gB, hgB⟩ := facts.fc.goldfish_score_nonempty S.E
    (Restated.confStoreAt M S (x[m][v].st) s).T votes votes s B
  have hB := facts.fc.ConeSupport_eligible S.E (Restated.confStoreAt M S (x[m][v].st) s).T votes votes
    (Restated.Vocabulary.Protocol.confLate M S.E (Restated.confStoreAt M S (x[m][v].st) s) s) s
    (Restated.HonSlot M S Sched s) (fun X => Block.Preceq B X) (C := B)
    hc.majority hc.counted hc.sub hc.no_equiv hc.vote
    (Restated.voteSetValid_conf facts S Sched x m v s)
    (fun X hX => preceq_eq_true_iff_Preceq.mpr hX) gB hgB
  -- two blocks that pass the test at one store lie on one chain
  obtain ⟨ev, hev, rfl⟩ := (pHJ% returns_map_elim_joint) _ _ _ hvv
  obtain ⟨tm, htm, rfl⟩ := (pHJ% returns_map_elim_joint) _ _ _ hev
  have hearly : ∀ u ∈ beforeCutoff tm (M.support_cutoff S.E s)
      (M.store_pool (Restated.confStoreAt M S (x[m][v].st) s) s),
      u ∈ Restated.Vocabulary.Protocol.confLate M S.E (Restated.confStoreAt M S (x[m][v].st) s) s := by
    intro u hu
    have h := (mem_beforeCutoff_iff _ _ _ _).mp hu
    refine (mem_beforeCutoff_iff _ _ _ _).mpr ⟨h.1, ?_⟩
    obtain ⟨σ, hσ, hlt⟩ :=
      exists_stamp_of_stampedBefore (facts.sto.stampedBefore_vote_of_tau _ tm htm h.2)
    exact stampedBefore_of_lt hσ (lt_of_lt_of_le hlt
      (WithBot.coe_le_coe.mpr (facts.sch.Protocol_support_cutoff_le_confirmation_time S.E s)))
  exact facts.fc.eligible_compatible hearly rfl hearly rfl
    (fun u hu => Or.inl (hc.counted hu))
    (fun u hu B₁ C₁ h1 h2 => Option.some.inj (h1.symm.trans h2))
    (fun u hu => Or.inl (hc.counted hu))
    (fun u hu B₁ C₁ h1 h2 => Option.some.inj (h1.symm.trans h2))
    _ (hsc' H) hel _ hgB hB

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If the joint invariant holds at round `r`, at or after the switch round, with anchor `T`, then
    for every `k` there are a tick step and an anchor `T_k` such that the joint invariant holds at
    round `r + k` with them, and, when `k > 0`, every honest active member of the committee of round
    `(r + k)`'s second slot votes for a descendant of `T_k`. -/
theorem exists_anchor_chain_secondSlot (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T) :
    ∀ k : Nat, ∃ (n_k : Nat) (T_k : NamedBlock V),
      Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + k) n_k n_W T_k ∧
        Block.Preceq T_W.erase T_k.erase ∧
        (0 < k → Restated.HeadsBelow M S Sched x T_k.erase ((M.opening_slot S.hc (r + k)) + 1)) := by
  intro k
  induction k with
  | zero => exact ⟨n, T, hJ, hTW, fun h => absurd h (Nat.lt_irrefl 0)⟩
  | succ k ih =>
    obtain ⟨n_k, T_k, hJk, hWk, -⟩ := ih
    have hrk : Restated.switchRound M S tE ≤ r + k := le_trans hr (Nat.le_add_right r k)
    obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd (r + k)
    obtain ⟨n'', hn''⟩ := Restated.tick_field_at_succ facts S Sched x htd (r + k + 1)
    obtain ⟨att, hatt⟩ := exists_actionAttestationsOf_lcs facts S Sched x (r + k) n'
    obtain ⟨-, hstep⟩ := Restated.afterPhaseJointRound_of_premises facts S Sched x tE hexec hmono htd hcatch
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB'
      hnW hAW hJswitch hrk hWk hJk hn'
    obtain ⟨hJ', hTT'⟩ := hstep att hatt
    have hinvS := hJk.toAfterPhaseInvariantOverActiveSetsSince
    have hJW : ∀ n₀ : Nat, Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r + k + 1))) →
        ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n₀ + 1 → Restated.HonestThrough M Sched x n₁ v →
          Block.Preceq (x[n₁][v].st).st.core.J T_k.erase :=
      fun n₀ h => Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
        hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hrk hWk hJk h
    have hcross : ∀ n₀ : Nat, Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r + k + 1))) →
        Restated.StepFinalizedCrossingUnderAnchor M S Sched x (r + k) n₀ T_k :=
      fun n₀ h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hrk hnW hinvS
        (hJW n₀ h)
    have hjust : ∀ n₀ : Nat, Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r + k + 1))) →
        Restated.StepJustifiedRootUnderAnchor M S Sched x (r + k) n_k n₀ T_k :=
      fun n₀ h => Restated.stepJustifiedRootUnderAnchor_of_afterSwitch facts S Sched x hrk hnW hinvS (hJW n₀ h)
    have hTW' := preceq_trans_Preceq hWk hTT'
    have hJ'' := Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
      hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW
      (le_trans hrk (Nat.le_succ _)) hTW' hJ' hn''
    have h2 := Restated.headsBelow_secondSlot_at_newAnchor facts S Sched x tE hexec hmono htd hsync hmult hcom
      tGAT gap hgst hlen hcv hthird hphase hrsW hcs hw hrk hinvS.toTop hcross hjust hnW hn' hn'' hatt
      hTT' hJ'' (hJ'.prevHeads n_k hinvS.tick) (hJ'.prevConfirmed n_k hinvS.tick)
    exact ⟨n', _, hJ', hTW', fun _ => h2⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If the joint invariant holds at round `r₀`, at or after the switch round, then for a slot `s`
    from round `r₀`'s third slot on, the block an honest validator `v` awake through slot `s`'s
    confirmation window writes as its live confirmed block at slot `s`'s confirmation tick is an
    ancestor of every honest head from slot `s + 1` on. -/
theorem live_confirmed_ancestorOfHonestHeadsFrom (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    (hpersist : Restated.EligibleDescendantOfAnchorPersists M S Sched x tE n_W T_W)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {v : V}
    (hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    -- `v`'s tick at step `m` passes the grade-2 awake test of slot `s + 1`'s round.
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.round_of S.hc (s + 1))) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m + 1][v].st).st.core.live_confirmed (s + 1) := by
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  obtain ⟨k, hk0, hk1⟩ := facts.gr.exists_round_of_slot S.hc r₀ (s := s + 1) (Nat.le_succ_of_le hs0)
  have hsk0 : (M.opening_slot S.hc (r₀ + k)) + 1 ≤ s := Nat.le_of_succ_le_succ hk0
  have hsk1 : s ≤ (M.opening_slot S.hc (r₀ + k + 1)) := Nat.le_of_succ_le_succ hk1
  have hrk : Restated.switchRound M S tE ≤ r₀ + k := le_trans hr₀ (Nat.le_add_right r₀ k)
  obtain ⟨n_k, T_k, hJk, hWk, h2k⟩ := Restated.exists_anchor_chain_secondSlot facts S Sched x tE hexec hmono htd
    hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear
    hB' hnW hAW hJswitch hr₀ hTW₀ hJ₀ k
  have hHs : Restated.HeadsBelow M S Sched x T_k.erase s := by
    by_cases hsk : (M.opening_slot S.hc (r₀ + k)) + 2 ≤ s
    · exact Restated.headsBelow_range_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync hthird
        hphase hrsW hmult hcv hcs hcom hw hrec hprev hclear hB' hnW hAW hrk hWk hJk s hsk
        (Nat.le_succ_of_le hsk1)
    · have hseq : s = (M.opening_slot S.hc (r₀ + k)) + 1 :=
        le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_le hsk)) hsk0
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; exact absurd hs0 (by simpa using hsk)
        · exact hk
      rw [hseq]; exact h2k hkpos
  have hAnc : Restated.AncestorOfHonestHeadsFrom M S Sched x T_k.erase (s + 1) :=
    Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x hk0
      (Restated.anchor_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen
        hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW hJswitch
        hrk hWk hJk)
  have hct : M.confirmation_time S.E s = slotStart S.E.Δ s + 6 * S.E.Δ :=
    (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s).symm
  have haw : v ∈ Sched.awake (M.confirmation_time S.E s) \
      Sched.adv (M.confirmation_time S.E s) :=
    Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hvaw (by rw [hct]; linarith) le_rfl,
      hvh _ le_rfl⟩
  rcases live_confirmed_after_confirmation_tick_eligible_lcs facts S Sched x hm haw
      (Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hm
        (by rw [facts.sch.confirmation_time_eq_support_cutoff_succ]
            exact facts.sch.support_cutoff_emod_delta S (s + 1)) haw) hrun
      with ⟨el, hel', hel⟩ | hlc
  · obtain ⟨H, hH⟩ : ∃ H : Block V, H = (x[m + 1][v].st).st.core.live_confirmed := ⟨_, rfl⟩
    rw [← hH] at hel ⊢
    by_cases hHT : Block.Preceq H T_k.erase
    · exact Restated.ancestorOfHonestHeadsFrom_of_preceq facts S Sched x hHT hAnc
    ·
      obtain ⟨t', ht'E, ht's, ht'len, hcs'⟩ :=
        Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hrk
      have hinvS := hJk.toAfterPhaseInvariantOverActiveSetsSince
      obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd (r₀ + k)
      have hcross : ∀ n₀ : Nat, Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r₀ + k + 1))) →
          Restated.StepFinalizedCrossingUnderAnchor M S Sched x (r₀ + k) n₀ T_k :=
        fun n₀ h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hrk hnW hinvS
          (Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
            hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hrk hWk hJk h)
      have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts S Sched x tE
        hexec hmono tGAT gap hgst hlen hthird hphase hrsW hrk hinvS.toTop hcross hn'
      have hso1 : (Restated.Vocabulary.Execution.Setup.a M S (r₀ + k + 1))
          = slotStart S.E.Δ ((M.opening_slot S.hc (r₀ + k + 1))) + 6 * S.E.Δ := by
        rw [← Restated.confirmation_time_opening_slot facts S (r₀ + k + 1)]
        exact (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E _).symm
      -- slot `s`'s support cutoff is before `S.a (r₀ + k + 1)`
      have hsR : M.support_cutoff S.E s ≤ (Restated.Vocabulary.Execution.Setup.a M S (r₀ + k + 1)) - 1 := by
        have e0 := facts.sch.support_cutoff_mono S.E hsk1
        have e1 := facts.sch.Sts_support_cutoff_lt_view_freeze S.E ((M.opening_slot S.hc (r₀ + k + 1)))
        have e2 := facts.sch.view_freeze_lt_confirmation_time S.E ((M.opening_slot S.hc (r₀ + k + 1)))
        rw [Restated.confirmation_time_opening_slot facts S (r₀ + k + 1)] at e2
        have e2' := Int.add_one_le_of_lt e2
        linarith
      have hop : tGAT ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r₀ + k))) := by
        have hopen := Restated.tGAT_add_two_rounds_le_opening facts S tGAT tE gap hgst hlen hrk
        have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
        have hd := S.E.Δ_pos
        rw [facts.gr.opening_eq_proposal_time] at hopen
        have hx1 := facts.sch.proposal_time_le_confirmation_time S.E
          ((M.opening_slot S.hc (r₀ + k)))
        have hx5 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E
          ((M.opening_slot S.hc (r₀ + k)))
        nlinarith
      have hslo : tGAT ≤ slotStart S.E.Δ s :=
        le_trans hop (slotStart_mono S (le_trans (Nat.le_succ _) hsk0))
      have hanchor : t' ≤ slotStart S.E.Δ (s + 1) :=
        le_trans ht's (slotStart_mono S hk0)
      have hcomp := Restated.eligible_compatible_of_cone facts S Sched x hexec hsync hmult htd hmono hgst hcv
        (fun t h1 h2 => hphase t h1 (le_trans h2 ht'E)) (fun t h => hthird t (le_trans h ht'E))
        hcs' ht'len (Restated.deliveredDescendantUnderFinalized_anchor facts S Sched x hn' hfin tGAT)
        (Restated.finalizedPreceqAtSteps_anchor facts S Sched x hn' hfin tGAT)
        (Nat.lt_of_lt_of_le (Nat.succ_pos _) hsk0) hslo hanchor hsR hHs hm hvaw hvh hel' hel
      have hTH : Block.Preceq T_k.erase H := by
        rcases compatible_cases hcomp with h | h
        · exact absurd h hHT
        · exact h
      have hsW : (M.opening_slot S.hc (Restated.switchRound M S tE)) + 2 ≤ s := by
        have : (M.opening_slot S.hc (Restated.switchRound M S tE)) ≤ (M.opening_slot S.hc r₀) := by
          exact facts.gr.opening_slot_le_of_le S.hc hr₀
        exact le_trans (Nat.add_le_add_right this 2) hs0
      exact hpersist (r₀ + k) n_k T_k hrk hWk hJk s hsW hsk0 hsk1 m hm v hvaw hvh H el hel' hel hTH
  · rw [hlc]
    obtain ⟨hm1, -⟩ := Restated.tickStepAt_time facts x hm
    have hvm : Restated.HonestThrough M Sched x m v := fun t ht => hvh t (by
      have := Restated.time_mono_int facts S Sched x (Nat.le_succ m); linarith)
    exact Restated.ancestorOfHonestHeadsFrom_of_preceq facts S Sched x
      (Restated.confRoot_preceq_anchor_atSlot facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync hthird
        hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hrk hWk hJk
        (le_trans (Nat.le_succ _) hsk0) hsk1 hm hvm) hAnc

end

end DecoupledConsensusModel.Sts.Restated
