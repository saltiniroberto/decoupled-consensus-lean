import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_AttestedDescendant
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeLate
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_LiveConfirmedSlots
import Proofs.Claims.Restated.Claim13bPhaseSleepiness
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bStepSG
import Proofs.Claims.Restated.Claim13beRoute3_82
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_74
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
import Proofs.Claims.Restated.Claim13bK_GradeLateRecv

/-!
# Grades from the round's attesters

Theorems showing that a block every member of `freshAttestersW` attests a descendant of is graded at
the next round, stated over a model `M : Record.Model V` with its facts `facts : Record.Facts M`.
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
local macro "pHP% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_HeadsPersist)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pCW% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedWake)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pW% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundWindow)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- From any node state `before`, validator `v`'s round-`r` action can compute some attestation. -/
private theorem actionAttestationFrom_nonempty_gf (facts : Record.Facts M)
    (S : DecoupledConsensusModel.Execution.Setup V)
    (before : M.N) (v : V) (r : Round) :
    ∃ a, a ∈ Restated.actionAttestationFrom M S before v r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract (M.mkNode st before.record c).cache)
    S.E S.hc (S.node v) (M.mkNode st before.record c).st (M.mkNode st before.record c).record
  exact ⟨D.2.2, M.mkNode st before.record c, ⟨c, hc, st, hst, rfl⟩, D.1, D.2.1, hD⟩

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If step `n` is the tick step at `S.a q`, the adversary has held `v_1` at no instant up to step
    `m`, and `tok` is a round-`q` token under `v_1`'s name in an outcome of `v`'s raw view of a
    round-`(q + 1)` grade, then every round-`q` attestation `v_1`'s action can compute from its node
    state at step `n` names the root `tok` names. -/
theorem rawView_key_of_honest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {q : Round} {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S q))) {m : Nat} {v v_1 : V}
    (hv_1 : Restated.HonestThrough M Sched x m v_1) {c : Int} {tok : Protocol.Token (Option BlockId)}
    {X : Finset (Protocol.Token (Option BlockId))}
    (hX : M.rawView (M.gradeView (M.toHealing (x[m][v].st).st.core)) S.hc.η_SG (q + 1) c v_1 ⇢ X)
    (htok : tok ∈ X)
    (hround : tok.round = q) :
    ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 q,
      tok.key = a.confirmed := by
  intro a ha
  obtain ⟨Y, hY⟩ := facts.gr.rawInputs_nonempty
    (M.gradeView (M.toHealing (x[m][v].st).st.core)) S.hc.η_SG (q + 1) c v_1
  obtain ⟨y, hy, hyt⟩ := (facts.gr.mem_rawView_iff _ _ _ _ _ tok X hX Y hY).mp htok
  obtain ⟨⟨k, -, hyk⟩, hyidx, -⟩ := facts.gr.rawInputs_mem_window _ _ _ _ _ Y hY hy
  have hykround : y.round = k := Restated.sgVotesRoundIndexed_sts facts S Sched x m v k y hyk
  have hymem : y ∈ (M.gradeView (M.toHealing (x[m][v].st).st.core)).sg_votes y.round := by
    rw [hykround]; exact hyk
  obtain ⟨n', htick', -, hyeq⟩ :=
    Restated.token_of_honest_sender facts S Sched x hexec hv_1 hymem hyidx
  have hyq : y.round = q := by rw [← facts.gr.token_round y, hyt]; exact hround
  rw [hyq] at htick' hyeq
  have hnn : n' = n := Restated.tickStepAt_unique facts x htick' hn
  rw [hnn] at hyeq
  rw [← hyt, facts.gr.token_key, hyeq a ha, facts.sto.sgVote_confirmed]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If round `q` is at or after the switch round, `n` and `n'` are the tick steps at `S.a q` and
    `S.a (q + 1)`, and `a` is a round-`q` attestation that a member `v_1` of
    `freshAttestersW S Sched x q m` can compute at step `n`, naming the root of a block `C` among
    `v_1`'s bodies, then the finalized block of every validator honest through any step `d ≤ n'` is
    on one chain with `C`. -/
theorem fresh_attested_compatible_finalized (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    {q : Round} (hr : Restated.switchRound M S tE ≤ q)
    {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S q))) {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))))
    {m : Nat} {p : Protocol.Phase}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (q + 1) p))
    {v_1 : V} (hv_1 : v_1 ∈ Restated.freshAttestersW M S Sched x q m)
    {C : NamedBlock V} (hC : C ∈ (x[n + 1][v_1].st).st.bodies)
    (a : NamedAttestation V)
    (ha : a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 q)
    (hconf : a.confirmed = some C.root) :
    ∀ (v : V) (d : Nat), d ≤ n' → Restated.HonestThrough M Sched x d v →
      Block.compatible (x[d][v].st).st.core.F C.erase = true := by
  obtain ⟨nq, T, hJ, -, hTW⟩ := Restated.anchor_at_later_round facts S Sched x tE hexec hmono htd hcatch
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB'
    hnW hAW hJswitch le_rfl hTW₀ hJ₀ hr
  have hinv := (pHP% joint_toTop_hp) hJ
  have hnq : nq = n := Restated.tickStepAt_unique facts x hinv.tick hn
  rw [hnq] at hinv
  have hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x q n'' T :=
    fun n'' h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hr hnW
      hJ.toAfterPhaseInvariantOverActiveSetsSince
      (Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
        hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ h)
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts S Sched x tE
    hexec hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hcross hn'
  have ham : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ (x[m].time : Int) := Restated.action_le_time_of_stepBefore facts S Sched x htd hm
  have hqr : v_1 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S q)) := Restated.honestThrough_of_mem_freshAttestersW facts hv_1 _ ham
  have hv_1f := Restated.freshAttestersW_subset_freshAttesters facts S Sched x q m hv_1
  have hne := Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew
    hmono hn (Restated.action_emod_delta facts S q)
    (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_freshAttesters facts hv_1f, hqr⟩)
  have hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v_1
      (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S q) x[n] v_1) q := by
    obtain ⟨τ, hlbl, hτ⟩ := id hn
    have hwin : v_1 ∈ Sched.awakeThroughout (M.early S.E S.hc q .g2 - S.E.Δ) (M.a S.hc S.E.Δ q) :=
      ((Restated.mem_freshAttestersW facts).mp hv_1).1
    exact Restated.run_fact_g2 facts S Sched x n τ q v_1 hlbl hτ hwin (by
      rw [hτ]
      exact fun t ht => Restated.honestThrough_of_mem_freshAttestersW facts hv_1 t (le_trans ht ham))
  have hsent := Restated.fresh_attests facts S Sched x hn hv_1f hqr hne hrun a ha
  have hCT : Block.compatible C.erase T.erase = true :=
    hinv.sg v_1 (Restated.hfreshH_of_stepBefore facts S Sched x htd hm hv_1) a
      (Restated.actionAttestationFrom_round facts (Setup.alwaysAwake S) _ v_1 q a ha)
      (Restated.actionAttestationFrom_val_index facts (Setup.alwaysAwake S) _ v_1 q a ha) hsent C hC hconf
  intro v d hd hvd
  exact Protocol.compatible_of_preceq_of_compatible (hfin v d hd hvd) (Protocol.compatible_comm hCT)

end

end DecoupledConsensusModel.Sts.Restated
