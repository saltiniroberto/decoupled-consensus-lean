import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bK_ConfirmedNew
import Proofs.Claims.Restated.Claim13bK_ConfirmedSafeAfter
import Proofs.Claims.Restated.Claim13bK_FgJustified
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_FrameNew
import Proofs.Claims.Restated.Claim13bK_GradeDescendant
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bK_HeadsNewAnchorJoint
import Proofs.Claims.Restated.Claim13bK_JointBase
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStep
import Proofs.Claims.Restated.Claim13bStepActiveAssembly
import Proofs.Claims.Restated.Claim13bStepActiveClauses
import Proofs.Claims.Restated.Claim13bStepActiveJoint
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13beKitActiveSince
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_77
import Proofs.Claims.Restated.Claim13beRoute3_82
import Proofs.Claims.Restated.Claim13beRoute3_88
import Proofs.Claims.Restated.Claim13beRoute3_91
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSince
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_GradePairwise
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepActiveAssembly
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepFieldsAt
import Model.Conditions.Claim13bStepGrade
import Model.Conditions.Claim13bStepPairwise
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
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
import Proofs.Claims.Restated.Claim13bStepFinRule
import Proofs.Claims.Restated.Claim13bStepGrade1Recv

/-!
# The joint invariant after the switch round, without the catch-up premise

The joint invariant over the active sets holds at the switch round and carries from each round to
the next, and so no two blocks finalized by honest validators conflict, from the phase's premises
and a justified-height bound before the switch round's tick, without the catch-up premise. The
round-`(r + 1)` anchor is read along every choice `att` of the round-`(r + 1)` action attestations.
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

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open Framework.StsMultisetLog

/-- If the invariant with the target clause since the switch round holds at round `r`, step `n_prev`
    is the tick at the action instant of round `r − 1`, and the facts on round `r − 1`'s heads,
    confirmations and grades hold at `n_prev`, then the joint invariant holds at round `r`. -/
private theorem joint_of_prevTick_l85g (facts : Record.Facts M)
    {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {r : Round} {n n_W n_prev : Nat} {T : NamedBlock V}
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x r n n_W T)
    (hn_prev : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))))
    (hP : ∀ v_1 ∈ Restated.HonRound M S Sched (r - 1), ∀ a : NamedAttestation V,
      a.round = r - 1 → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n_prev + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Restated.HeadsBelow M S Sched x C.erase ((M.opening_slot S.hc r)))
    (hQ : Restated.ConfirmedCompatibleFreshSGOverHonRound M S Sched x (r - 1) n_prev n)
    (hG : ∀ v ∈ Restated.HonRound M S Sched r, ∀ p : Protocol.Phase,
      M.domain S.E S.hc r p ≤ (Restated.Vocabulary.Execution.Setup.a M S r) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc r p) →
      ∀ B : Block V, ∀ b : Bool,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG r (M.early S.E S.hc r p)
          (M.late S.E S.hc r p) B ⇢ b → b = true →
      ∃ v_1 ∈ Restated.HonRound M S Sched (r - 1), ∃ a : NamedAttestation V,
        a.round = r - 1 ∧ a.val_index = v_1 ∧
        (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent ∧
        ∃ C : NamedBlock V, C ∈ (x[n_prev + 1][v_1].st).st.bodies ∧ a.confirmed = some C.root ∧
          Block.Preceq B C.erase)
    (hGP : Restated.GradedUnderPrevSGOverPerformers M S Sched x r n_prev) :
    Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T where
  toAfterPhaseInvariantOverActiveSetsSince := hinv
  prevTick := ⟨n_prev, hn_prev⟩
  prevHeads := fun n₂ hn₂ => by
    obtain rfl := Restated.tickStepAt_unique facts x hn₂ hn_prev
    exact hP
  prevConfirmed := fun n₂ hn₂ => by
    obtain rfl := Restated.tickStepAt_unique facts x hn₂ hn_prev
    exact hQ
  gradedUnderPrevSG := fun n₂ hn₂ => by
    obtain rfl := Restated.tickStepAt_unique facts x hn₂ hn_prev
    exact fun v hv p _ hdom => hG v hv p hdom
  gradedUnderPrevSGPerformers := fun n₂ hn₂ => by
    obtain rfl := Restated.tickStepAt_unique facts x hn₂ hn_prev
    exact hGP

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
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Without the catch-up premise, at every round `r` at or after the switch round whose anchor `T`
    is `T_W` or a descendant of it and at which the joint invariant holds with tick step `n` and
    switch step `n_W`, with `n'` the tick step at `S.a (r + 1)`: the facts `StepFieldsAt` hold at
    `r`, `n`, `n'`, `T`, and for every choice `att` of the round-`(r + 1)` action attestations the
    joint invariant holds at round `r + 1` with tick step `n'`, the same switch step and the anchor
    `newAnchor S Sched x r n' att T`, of which `T` is an ancestor. -/
theorem afterPhaseJointRound_withoutCatchUp_l85f (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hrecvR : Restated.NextRoundReceipts M S Sched x r) :
    Restated.StepFieldsAt M S Sched x tE r n n' T ∧
      ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
        Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n' n_W
          (Restated.newAnchor M S Sched x r n' att T) ∧
        Block.Preceq T.erase (Restated.newAnchor M S Sched x r n' att T).erase := by
  classical
  have hinvS := hJ.toAfterPhaseInvariantOverActiveSetsSince
  have hinv := hinvS.toTop
  have hctx : Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T := ⟨hr, hinv⟩
  have hJW : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n'' + 1 → Restated.HonestThrough M Sched x n₁ v →
        Block.Preceq (x[n₁][v].st).st.core.J T.erase :=
    fun n'' h => Restated.justified_preceq_anchor_after_switchW facts S Sched x tE hexec hmono htd tGAT gap hgst
      hlen hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hAW hnW hr hinvS hTW h
  have hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T :=
    fun n'' h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hr hnW hinvS (hJW n'' h)
  have hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T :=
    fun n'' h => Restated.stepJustifiedRootUnderAnchor_of_afterSwitch facts S Sched x hr hnW hinvS (hJW n'' h)
  have hP : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
      a.round = r → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Restated.HeadsBelow M S Sched x C.erase ((M.opening_slot S.hc (r + 1))) := by
    rcases Nat.lt_or_ge (Restated.switchRound M S tE) r with hlt | hge
    · exact Restated.prevHeads_succ_afterPhase_ofAfterSwitch facts S Sched x tE hexec hmono htd hsync hmult hcom
        tGAT gap hgst hlen hcv hthird hphase hrsW hcs hnW hlt hJ hn' hcross (hJW n' hn')
    · have hrW : r = Restated.switchRound M S tE := le_antisymm hge hr
      refine Restated.prevHeads_succ_afterPhase facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap hgst
        hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross ?_
      intro v n₁ hlo hhi hvh
      by_cases hWn : n_W ≤ n₁
      · exact hJW n' hn' v n₁ hWn hhi hvh
      · rw [hrW] at hlo
        exact preceq_trans_Preceq (hJswitch v n₁ hlo (by omega) hvh) hTW
  have hQ : Restated.ConfirmedCompatibleFreshSGOverHonRound M S Sched x r n n' :=
    Restated.confirmedCompatibleFreshSG_of_openingHeads (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult hcom
      tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hjust hn'
      (fun v_1 hv_1 a ha hav hsent C hC hconf _ _ => hP v_1 hv_1 a ha hav hsent C hC hconf)
      (by intro s _ _ m hm q hq; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hm (facts.sch.vote_time_emod_delta S _) (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h => ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩)) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
      (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨Restated.awake_action_of_mem_honRound facts hv, (Finset.mem_sdiff.1 hv).2⟩))
  have hCN : ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
      ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
        Block.compatible hs.live_confirmed (Restated.newAnchor M S Sched x r n' att T).erase = true :=
    fun att hatt => Restated.confirmedNew_at_of_joint (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult hcom
      tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hjust hn' hatt hQ
      (by intro s _ _ m hm q hq; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hm (facts.sch.vote_time_emod_delta S _) (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h => ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩)) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
      (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨Restated.awake_action_of_mem_honRound facts hv, (Finset.mem_sdiff.1 hv).2⟩))
  have hnWn' : n_W ≤ n' := le_trans (Restated.tick_le_of_round_le facts S Sched x hnW hinv.tick hr)
    (Restated.tick_le_of_round_le facts S Sched x hinv.tick hn' (Nat.le_succ r))
  have hJact : ∀ v ∈ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1), Block.Preceq hs.J T.erase := by
    intro v hv hs hhs
    rw [Restated.actionHealingStore_J facts S _ _ hs hhs]
    have hvT : HonestThroughTime Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) v := mem_honestThroughSet.mp hv
    have htn : (x[n'].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := by
      rw [← (Restated.tickStepAt_time facts x hn').1]
      exact Restated.time_mono_int facts S Sched x (Nat.le_succ n')
    exact hJW n' hn' v n' hnWn' (Nat.le_succ n') (fun t ht => hvT t (le_trans ht htn))
  have hGP := Restated.gradePairwise_at_of_confirmedSafe (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult hcom
    tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hjust hn' hJact hQ
    (by intro s _ _ m hm q hq; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hm (facts.sch.vote_time_emod_delta S _) (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h => ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩)) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
    (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨Restated.awake_action_of_mem_honRound facts hv, (Finset.mem_sdiff.1 hv).2⟩))
  have hGD : ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
      ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ p : Protocol.Phase, M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p) →
      ∀ B : Block V,
        M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
            (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
            (M.late S.E S.hc (r + 1) p) B ⇢ true →
        Block.Preceq T.erase B → B ≠ T.erase →
        Block.compatible B (Restated.newAnchor M S Sched x r n' att T).erase = true :=
    fun att hatt => Restated.gradeDescendant_at_of_confirmedSafe (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult
      tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hn' hatt hQ
      (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨Restated.awake_action_of_mem_honRound facts hv, (Finset.mem_sdiff.1 hv).2⟩))
  have hTT' : ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
      Block.Preceq T.erase (Restated.newAnchor M S Sched x r n' att T).erase :=
    fun att hatt =>
      Restated.anchor_preceq_new_of_hypotheses_overActiveSets (hrecvR := hrecvR) facts (hcross := hcross) (hjust := hjust)
        S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hctx hn' att hatt
  have hceil' := Restated.heightCeiling_field_of_hypotheses_overActiveSets facts S Sched x tE hexec
    hctx hn'
  have hgOld := Restated.gradeOld_of_premises facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
    hthird hphase hrsW hctx.1 hctx.2
    (Restated.freshSGHeadsAtLate_of_premises facts (hcross := hcross) S Sched x tE hexec hmono htd hsync hmult
      tGAT gap hgst hlen hcv hthird hphase hrsW hcs hctx.1 hctx.2
      (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨Restated.awake_action_of_mem_honRound facts hv, (Finset.mem_sdiff.1 hv).2⟩)))
    hrecvR
    (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨Restated.awake_action_of_mem_honRound facts hv, (Finset.mem_sdiff.1 hv).2⟩))
  have hg1' := fun (att : V → NamedAttestation V)
      (hatt : Restated.ActionAttestationsOf M S Sched x r n' att) =>
    Restated.grade1_field_at_new_anchor_overActiveSets facts S Sched x (hTT' att hatt) hgOld (hGD att hatt)
  have htgt' := fun (att : V → NamedAttestation V)
      (hatt : Restated.ActionAttestationsOf M S Sched x r n' att) =>
    Restated.targetsSince_field_at_succ_rule facts S Sched x hexec hinvS.tick hn' hatt
      hinvS.inPlay (hTT' att hatt)
      (fun q hq => hCN att hatt q
        hq)
      (fun q hq => Restated.frameG2Old_of_gradeOld facts S Sched x r n'
        (Restated.newAnchor M S Sched x r n' att T) hn' (hg1' att hatt) q
        hq)
      hinvS.heightCeiling hinvS.targetsSince
  obtain ⟨n'', hn''⟩ := Restated.tick_field_at_succ facts S Sched x htd (r + 1)
  have hheads : ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
      Restated.HeadsBelow M S Sched x (Restated.newAnchor M S Sched x r n' att T).erase
        ((M.opening_slot S.hc (r + 1)) + 2) := by
    intro att hatt
    have hTW' : Block.Preceq T_W.erase (Restated.newAnchor M S Sched x r n' att T).erase :=
      preceq_trans_Preceq hTW (hTT' att hatt)
    have hJ' := Restated.justified_preceq_anchor_after_switchW_ofClauses facts S Sched x tE hexec hmono
      htd tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hAW hnW
      (le_trans hr (Nat.le_succ r)) hn' (hceil' att hatt) (htgt' att hatt) hTW' hn''
    exact Restated.headsAtNewAnchor_of_joint (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap
      hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hjust hnW hn' hn'' hatt (hTT' att hatt)
      (hceil' att hatt) hJ' hP hQ
  have hf : Restated.StepFieldsAt M S Sched x tE r n n' T := ⟨hCN, hGP, hGD, hheads⟩
  refine ⟨hf, fun att hatt => ?_⟩
  have hinv' : Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x (r + 1) n' n_W
      (Restated.newAnchor M S Sched x r n' att T) :=
    { tick := hn'
      inPlay := Restated.inPlay_field_of_hypotheses_overActiveSets facts S Sched x tE hctx att hatt
      anchorEntry := Restated.anchorEntry_field_of_hypotheses_overActiveSets facts S Sched x tE hctx att hatt
      band := Restated.band_field_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono
        tGAT gap hgst hlen hthird hphase hrsW hctx hn' att hatt
      sg := Restated.sg_field_of_hypotheses_overActiveSets_ofFieldsAt (hrecvR := hrecvR) facts (hcross := hcross) (hjust := hjust)
        S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hctx hn' hf att hatt
      sgPairwise := Restated.sgPairwise_field_of_hypotheses_overActiveSets_ofFieldsAt (hrecvR := hrecvR) facts (hcross := hcross)
        (hjust := hjust) S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hctx hn' hf
      heads := Restated.heads_field_of_hypotheses_overActiveSets_ofFieldsAt facts S Sched x tE hf att hatt
      fin := Restated.fin_field_of_hypotheses_overActiveSets_ofFieldsAt (hrecvR := hrecvR) facts (hcross := hcross) (hjust := hjust)
        S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hctx hn' hf att hatt
      grade1 := fun w hw' p _hpg1 hp m hm B b hb hbt =>
        Restated.grade1_field_of_hypotheses_overActiveSets_ofFieldsAt (hrecvR := hrecvR) facts (hcross := hcross)
          (hjust := hjust) S Sched x tE hexec hmono htd
          tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hctx hn' hf att hatt
          w hw' p hp m hm B (hbt ▸ hb)
      grade1Performers := Restated.grade1ClauseOverPerformers_at_succ (hrecvR := hrecvR) facts S Sched x tE
        hexec hmono htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hn'
        hatt (hTT' att hatt)
        (Restated.confirmedCompatibleFreshSG_of_overHonRound facts S Sched x hn' hQ)
        (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
        (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨Restated.awake_action_of_mem_honRound facts hv, (Finset.mem_sdiff.1 hv).2⟩))
      heightCeiling := hceil' att hatt
      targetsTop := Restated.targetsTop_field_of_hypotheses_overActiveSets_ofFieldsAt (hrecvR := hrecvR) facts (hcross := hcross)
        (hjust := hjust) S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hctx hn' hf att hatt
      targetsSince := htgt' att hatt }
  have hG : ∀ v ∈ Restated.HonRound M S Sched (r + 1), ∀ p : Protocol.Phase,
      M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p) →
      ∀ B : Block V, ∀ b : Bool,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
          (M.late S.E S.hc (r + 1) p) B ⇢ b → b = true →
      ∃ v_1 ∈ Restated.HonRound M S Sched r, ∃ a : NamedAttestation V,
        a.round = r ∧ a.val_index = v_1 ∧
        (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent ∧
        ∃ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies ∧ a.confirmed = some C.root ∧
          Block.Preceq B C.erase :=
    fun v hv p hdom m hm B b hB hb => by
      subst hb
      exact Restated.graded_preceq_freshSG_of_premises (hrecvR := hrecvR) facts (hcross := hcross) S Sched x tE hexec hmono
        htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hv hdom hm B hB
        (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨Restated.awake_action_of_mem_honRound facts hv, (Finset.mem_sdiff.1 hv).2⟩))
  exact ⟨joint_of_prevTick_l85g facts hinv' hinv.tick hP hQ hG
    (Restated.gradedUnderPrevSGOverPerformers_at_succ (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd
      hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross), hTT' att hatt⟩

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
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Without the catch-up premise, from every round `r` at or after the switch round whose anchor `T`
    is `T_W` or a descendant of it and at which the joint invariant holds with tick step `n` and
    switch step `n_W`, the joint invariant carries to round `r + 1` with the same switch step and an
    anchor that is `T` or a descendant of `T`. -/
theorem afterPhaseStepOverActiveSetsJoint_withoutCatchUp_l85f (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    (hrecvAll : ∀ r' : Round, Restated.switchRound M S tE ≤ r' → Restated.NextRoundReceipts M S Sched x r') :
    ∀ (r : Round) (n : Nat) (T : NamedBlock V), Restated.switchRound M S tE ≤ r →
      Block.Preceq T_W.erase T.erase →
      Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T →
      ∃ (n' : Nat) (T' : NamedBlock V),
        Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n' n_W T' ∧
          Block.Preceq T.erase T'.erase := by
  intro r n T hr hTW hJ
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd r
  have hne : ∀ q : V, ∃ a, a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S)
      (x[n'][q].st) q (r + 1) := fun q => by
    obtain ⟨na, hna⟩ := (p74% actionReadFrom_nonempty₇₄) facts (Setup.alwaysAwake S)
      (x[n'][q].st) (r + 1)
    obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract na.cache)
      (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node q) na.st na.record
    exact ⟨D.2.2, na, hna, D.1, D.2.1, hD⟩
  choose att hattq using hne
  have hatt : Restated.ActionAttestationsOf M S Sched x r n' att := fun q _ => hattq q
  obtain ⟨-, hstep⟩ := Restated.afterPhaseJointRound_withoutCatchUp_l85f (hrecvR := hrecvAll _ (by first | assumption | exact hctx.1 | exact le_trans hr (Nat.le_add_right _ _) | exact le_trans hr (Nat.le_succ _) | exact le_trans hctx.1 (Nat.le_succ _))) facts S Sched x tE hexec hmono htd
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB'
    hnW hAW hJswitch hr hTW hJ hn'
  obtain ⟨hJ', hTT'⟩ := hstep att hatt
  exact ⟨n', _, hJ', hTT'⟩

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
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Without the catch-up premise, from the phase's premises, if at every step from one instant
    before the vote instant of `o_rW + 1` up to the switch round's tick step every validator honest
    through that step holds a justified height at least that of every anchor at the re-based
    deadline round, then there are a step `n_W` that is the tick at `S.a rW` and a switch-round
    anchor `T_W` such that the joint invariant holds at `rW` with tick step and switch step `n_W`
    and anchor `T_W`, and from every round at or after `rW` whose anchor is `T_W` or a descendant of
    it, the joint invariant with switch step `n_W` carries to the next round with an anchor that is
    the round's anchor or a descendant of it. -/
theorem afterPhaseJoint_base_and_step_withoutCatchUp_l85f (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    (hlow : ∀ n_W : Nat, Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) →
      ∀ T_D' : NamedBlock V,
      Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D' →
      ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      (M.derive_named S.E S.cfg T_D').h ≤ (x[n₁][v].st).st.core.h_j)
    (hrecvAll : ∀ r' : Round, Restated.switchRound M S tE ≤ r' → Restated.NextRoundReceipts M S Sched x r') :
    ∃ (n_W : Nat) (T_W : NamedBlock V), Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) ∧
      Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n_W n_W T_W ∧
      ∀ (r : Round) (n : Nat) (T : NamedBlock V), Restated.switchRound M S tE ≤ r →
        Block.Preceq T_W.erase T.erase →
        Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T →
        ∃ (n' : Nat) (T' : NamedBlock V),
          Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n' n_W T' ∧
            Block.Preceq T.erase T'.erase := by
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hprev := Restated.basePreviousRoundSGCompatibleWithAnchor_atRound facts S Sched x tGAT tE gap hlen hgst
    hmono hexec hsync hmult hcv hcom hthird hawake hrec
  have hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T :=
    fun r hrD' hrW => Restated.baseClearFGSource_atRound_of_premises facts S Sched x tGAT tE gap hgst hmono
      hexec hsync hmult hcv hcom hthird hawake r
      ((Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrD') hrW
  have hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap := by
    intro T_D' hAD' n_W hnW v hv
    have h1 := (Restated.tickStepAt_time facts x hnW).2
    have h2 := Restated.vote_time_succ_le_confirmation_time_l77 facts S ((M.opening_slot S.hc (Restated.switchRound M S tE)))
    rw [Restated.a_eq_confirmation_opening_l58 facts] at h1
    exact hlow n_W hnW T_D' hAD' v n_W (by linarith) le_rfl hv
  obtain ⟨n_W, T_W, hnW, hAW, hbase⟩ := Restated.afterPhaseInvariantOverActiveSetsJoint_at_switchRound facts S
    Sched x tGAT tE gap hgap hlen hgst hmono hexec hsync hmult hcv htd hcom hthird
    hawake hrec hsl hrs hcs hprev hclear hB'
  have hJswitch := Restated.justifiedAncestor_before_switchTick_of_justifiedHigh facts S Sched x tE hexec hmono
    htd tGAT gap hgst hlen' hsync hthird hawake hrs hmult hcv hcom hrec hprev hclear hnW hAW
    (hlow n_W hnW)
  exact ⟨n_W, T_W, hnW, hbase,
    Restated.afterPhaseStepOverActiveSetsJoint_withoutCatchUp_l85f (hrecvAll := hrecvAll) facts S Sched x tE hexec hmono htd tGAT gap
      hgst hlen' hsync hthird hawake hrs hmult hcv hcs hcom hrec hprev hclear hB'
      hnW hAW hJswitch⟩

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
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Without the catch-up premise, from the phase's premises, if at every step from one instant
    before the vote instant of `o_rW + 1` up to the switch round's tick step every validator honest
    through that step holds a justified height at least that of every anchor at the re-based
    deadline round, then no two blocks finalized in the stores of two validators honest through
    their own reads conflict. -/
theorem claim13be_conclusion_of_joint_l85f (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    (hlow : ∀ n_W : Nat, Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) →
      ∀ T_D' : NamedBlock V,
      Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D' →
      ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      (M.derive_named S.E S.cfg T_D').h ≤ (x[n₁][v].st).st.core.h_j)
    (hrecvAll : ∀ r' : Round, Restated.switchRound M S tE ≤ r' → Restated.NextRoundReceipts M S Sched x r') :
    ∀ (v₁ v₂ : V) (i j : Nat),
      Restated.HonestThrough M Sched x i v₁ → Restated.HonestThrough M Sched x j v₂ →
      Block.Compatible (x[i][v₁].st).st.core.F (x[j][v₂].st).st.core.F := by
  obtain ⟨n_W, T_W, -, hbase, hstepJ⟩ := Restated.afterPhaseJoint_base_and_step_withoutCatchUp_l85f (hrecvAll := hrecvAll) facts S Sched x
    tGAT tE gap hgap hlen hgst hmono hexec hsync hmult hcv htd hcom hthird
    hawake hrec hsl hrs hcs hlow
  have hstep : Restated.AfterPhaseStepOverActiveSetsSinceFrom M S Sched x tE n_W T_W := by
    intro r n T hr hTW hinvS
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
    obtain ⟨n₁, T₁, hJ₁, -⟩ :=
      Restated.afterPhaseInvariantOverActiveSetsJoint_of_stepFrom facts S Sched x tE hbase hstepJ k
    obtain rfl : n₁ = n := Restated.tickStepAt_unique facts x
      hJ₁.toAfterPhaseInvariantOverActiveSetsSince.tick hinvS.tick
    have hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE + k) n₁ n_W T :=
      { toAfterPhaseInvariantOverActiveSetsSince := hinvS
        prevTick := hJ₁.prevTick
        prevHeads := hJ₁.prevHeads
        prevConfirmed := hJ₁.prevConfirmed
        gradedUnderPrevSG := hJ₁.gradedUnderPrevSG
        gradedUnderPrevSGPerformers := hJ₁.gradedUnderPrevSGPerformers }
    obtain ⟨n', T', hJ', hTT'⟩ := hstepJ _ n₁ T hr hTW hJ
    exact ⟨n', T', hJ'.toAfterPhaseInvariantOverActiveSetsSince, hTT'⟩
  exact Restated.claim13be_conclusion_of_base_and_stepFrom_overActiveSetsSince facts S Sched x tE n_W T_W
    hbase.toAfterPhaseInvariantOverActiveSetsSince hstep

end

end DecoupledConsensusModel.Sts.Restated
