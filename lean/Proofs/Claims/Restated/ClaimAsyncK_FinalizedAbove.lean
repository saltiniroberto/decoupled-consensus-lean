import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bK_ConeChain
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_78
import Proofs.Claims.Restated.Claim13beRoute3_83
import Proofs.Claims.Restated.Claim13beRoute3_85d
import Proofs.Claims.Restated.Claim13beRoute3_86g
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_RecoveryProposalConfirmationRead
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.ClaimAsyncK_FinalizedAbove

/-!
# Finalized blocks above the earlier heights

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`: honest opening
proposals after a round are at least as high as that round's anchor
(`openingProposal_height_ge_anchorAtRound`), running maximum heights up to `tGAT` are bounded by the
switch round's anchor (`hMax_le_switchAnchor_of_le_tGAT`), and a run proposal is in the sent log as
itself (`runProposal_sent_asItself`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- Refers by name to a private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_86g`. -/
local macro "p86g% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86g)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers by name to a private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_58`. -/
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers by name to a private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_71`. -/
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- Under synchrony from wake, monotone corruption, the awake premise and the third bound up to
    `tL`, `t_GST ≤ tGAT`, the common view at `tGAT`, a valid execution, the awake-at-multiples
    premise, the committee premise and the recurrence of strong openings up to `tL`: if `T` is a
    round-`r` anchor for an end `tA ≤ tL`, `r` is at or after the deadline round, `q` is at least
    `r + 1` and at least the deadline round plus `2`, `S.a q ≤ x[n].time ≤ tL`, the proposer of
    `o_q` is not held at `o_q`'s confirmation instant and `P` is a proposal of that proposer on the
    path `Restated.runAllPath M S Sched x v₀ n`, then `h(T) ≤ h(P)`. -/
theorem openingProposal_height_ge_anchorAtRound (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tA tL : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tL)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tL gap)
    {r : Round} (hrD : Restated.deadlineRoundW M S tGAT gap ≤ r)
    {T : NamedBlock V} (hA : Restated.AnchorAtRound M S Sched x tGAT tA r T) (hAL : tA ≤ tL)
    {q : Round} (hq : r + 1 ≤ q) (hrDq : Restated.deadlineRoundW M S tGAT gap + 2 ≤ q)
    (hqhor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ (x[n].time : Int))
    (hopening : S.E.proposer ((M.opening_slot S.hc q)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc q))))
    {P : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc q)))
      (S.E.proposer (M.opening_slot S.hc q))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc q)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc q))) pn.st ⇢ some P →
    (M.derive_named S.E S.cfg T).h ≤ (M.derive_named S.E S.cfg P).h := by
  intro R W wp cp hcp pn hP
  have hAL' : Restated.AnchorAtRound M S Sched x tGAT tL r T := by
    obtain ⟨v, N, n₁, blocked, first, i, a, ta, Cfg, Tprev, c0, h1, h2, h3, h4, h5, h6⟩ := hA
    exact ⟨v, N, n₁, blocked, first, i, a, ta, Cfg, Tprev, c0, h1, h2, h3.trans hAL, h4, h5, h6⟩
  obtain ⟨-, -, n₀, -, -, -, -, -, -, -, -, hn₀, -⟩ := hA
  have hrq : r ≤ q := (Nat.le_succ _).trans hq
  have hSa : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[n].time : Int) := ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hrq).trans hqhor
  obtain ⟨blocked, first, i, a, ta, Cfg, T', Tprev, c0, hreg, hround, -, htop, -⟩ :=
    Restated.switchRoundRegime_runAll_notHeld_atRound facts S Sched x v₀ hsync hmono hawake hgst
      hcv hvalid hawm hthird hcom hrec hrD hn₀ hSa hn
  have hheight := Restated.anchorAtRound_height facts S Sched x hsync hmono hawake hgst hcv hvalid
    hawm hthird hAL' hn₀
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake
    hgst hcv hvalid hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hX : ∀ t : Int, 0 ≤ t → notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ _ => Finset.subset_univ _
  have hXXb : (Finset.univ : Finset V) ⊆ Finset.univ := Finset.Subset.refl _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hdlo : (M.opening_slot S.hc a.round) + 1 ≤ (M.opening_slot S.hc q) :=
    (facts.gr.opening_slot_succ_le_l78 S a.round).trans
      (facts.gr.opening_slot_mono S ((Nat.succ_le_succ hround).trans hq))
  have hconfA : M.confirmation_time S.E ((M.opening_slot S.hc q)) = (Restated.Vocabulary.Execution.Setup.a M S q) :=
    Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S q
  have hhor : M.vote_time S.E ((M.opening_slot S.hc q)) + S.E.Δ ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[n].time : Int)
    refine (Restated.vote_time_add_delta_le_confirmation_l78 facts S le_rfl).trans ?_
    rw [hconfA]
    exact hqhor
  have hheads := hreg.heads_from_firstInterior facts hf hHs hHsXb hX hXXb hcomOn hbelow hdlo
    hhor hlo (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono
      hawake hn k hk u j hj)
  have hadopt := (Restated.openingAdoption_at_strongWindow_afterDeadline facts S Sched x v₀ n
    hsync hmono hawake hgst hcv hvalid hawm hthird hn hcom hrec hrDq hqhor hopening cp hcp
    hP).1
  have hw : S.E.proposer ((M.opening_slot S.hc q)) ∈
      notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc q))) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hopening
  have hTP : Block.Preceq T'.erase P.erase := by
    obtain ⟨H, cw, hcw, Tr, hTr, L, hL, L', hL', hH⟩ :=
      (p86g% exists_headOutcome₈₆g) facts (Setup.alwaysAwake S)
        (W (strictEventIndex R (M.vote_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q)))
        (M.vote_time S.E (M.opening_slot S.hc q))
    have h := hheads _ hw cw hcw Tr hTr L hL L' hL' H hH
    rwa [hadopt _ hw cw hcw Tr hTr L hL L' hL' H hH] at h
  obtain ⟨hTrun, -⟩ := hreg.checkpoint_runBlock facts hf hHsXb
  obtain ⟨hpos, hgat⟩ := Restated.openingBounds_afterDeadline_l85d facts S hrDq
  have hpropHor : M.proposal_time S.E ((M.opening_slot S.hc q)) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[n].time : Int)
    refine (facts.sch.proposal_time_le_confirmation_time S.E _).trans ?_
    rw [hconfA]
    exact hqhor
  have hPclock : M.proposal_with (M.gradeContract cp)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc q)))
      (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some P := by
    have h := hP
    rw [show pn.st = M.store_with_cache
        (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q))) _ from
      facts.nd.mkNode_st _ _ _, facts.dt.proposal_with_store_with_cache] at h
    exact h
  have hwinQ : tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc q)) .g1 - S.E.Δ := by
    rw [facts.gr.round_of_opening_slot_eq S.hc]
    have hW : Restated.roundAt M S tGAT + S.hc.η_SG < Restated.deadlineRoundW M S tGAT gap := by
      unfold Restated.deadlineRoundW
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ _)
    have h0 := Restated.lo_le_early_g2_sub_delta_of_action_lt facts S
      (Restated.roundAt_lo_le_rGST_l71 facts S tGAT)
      (lt_of_lt_of_le hW ((Nat.le_add_right _ 2).trans hrDq))
    have h1 := facts.gr.early_g2_add_delta_le_early_g1 S q
    have hΔ := S.E.Δ_pos
    linarith
  have hPrun := Restated.proposedBlock_runBlockOn facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf hHs hHsXb hpos hopening hpropHor hgat (fun j hj => hf.tick_outcome j _ _ hj)
    (fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hopening) hwinQ)
    cp hcp hPclock
  have hTPn : NamedBlock.Preceq T' P :=
    Restated.namedPreceq_of_runBlock_erase_preceqOn facts (notHeldAt Sched) Finset.univ hf hTrun hPrun hTP
  rw [hheight]
  exact htop.trans (facts.cs.derive_height_mono S.E S.cfg hTPn)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- Under the phase's length bound, the third bound and the awake premise up to `tE`, the
    round-level sleepiness bound at `tE` and diverging time, if the joint invariant holds at the
    switch round of `tE` with anchor `T`, then every validator's store at every step whose time is
    at or before `tGAT` has `Σ.h_max ≤ h(T) + 1`. -/
theorem hMax_le_switchAnchor_of_le_tGAT (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (gap : Nat)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption)
    (hgst : S.E.t_GST ≤ tGAT) (hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (htd : Restated.TimeDiverges M x)
    {n_W : Nat} {T : NamedBlock V}
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n_W n_W T) :
    ∀ (u : V) (i : Nat), (x[i].time : Int) ≤ tGAT →
      (x[i][u].st).st.core.h_max ≤ (M.derive_named S.E S.cfg T).h + 1 := by
  obtain ⟨n', hn'⟩ := Restated.exists_tickStepAt facts x htd
    (Restated.action_pos facts S (Restated.switchRound M S tE + 1))
  have hband := Restated.hMax_le_anchor_succ_before_succ_tick_of_hypotheses facts S Sched x tE
    hexec hmono tGAT gap hgst hlen' hthird hphase hrsW le_rfl
    hJ.toAfterPhaseInvariantOverActiveSetsSince.toTop hn'
  let rho₀ : Record.Run V := { honest := ∅, horizon := 0, events := [] }
  have hrDW : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans
      (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap rho₀ hgst hlen')
  obtain ⟨hlo, -⟩ := Restated.window_in_phase_atRound facts S tGAT tE gap hgst hlen' hrDW le_rfl
  have hmon : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + 1)) :=
    (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (Nat.le_succ _)
  have hwA : (1 : Int) ≤ wAttest S := by
    have hΔ : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
    have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
    show (1 : Int) ≤ 4 * (S.hc.R : Int) * S.E.Δ
    nlinarith
  intro u i hi
  exact hband u i (Restated.le_tick_of_time_lt_action facts S Sched x hn' (by linarith))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- Under synchrony from wake, monotone corruption, the awake premise and the third bound up to
    `tL`, `t_GST ≤ tGAT`, the common view at `tGAT`, a valid execution and the awake-at-multiples
    premise: let `N` be a step with `x[N].time ≤ tL`, `s > 0` a slot whose proposal instant is in
    `[tGAT + 1, x[N].time]` and whose proposer is not held at `s`'s confirmation instant and passes
    the grade-1 awake test of `s`'s round at its proposal tick on the path
    `Restated.runAllPath M S Sched x v₀ N`, and `P` a proposal of that proposer on that path. Then
    some step `k` stands at `s`'s proposal instant, the message `⟨proposer of s, P⟩` is in the sent
    log `x[k].sent`, and `proposedBlockAtStep S x k s P.erase` holds. -/
theorem runProposal_sent_asItself (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v₀ : V) (N : Nat)
    {tGAT tL : Int}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[N].time : Int) ≤ tL)
    {s : Slot} {P : NamedBlock V} (hs : 0 < s)
    (hlo : tGAT + 1 ≤ M.proposal_time S.E s)
    (hhor : M.proposal_time S.E s ≤ (x[N].time : Int))
    (hprop : S.E.proposer s ∈ notHeldAt Sched (M.confirmation_time S.E s))
    (hrun : ∀ j : Nat,
      ({ Restated.runAll M S Sched x v₀ N with honest := notHeldAt Sched (x[N].time : Int) } :
          Record.Run V).events[j]? =
        some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      M.awake_for_grade1 (Setup.alwaysAwake S) (S.E.proposer s)
        (Restated.runAllPath M S Sched x v₀ N j (S.E.proposer s)) (M.round_of S.hc s)) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ N with honest := notHeldAt Sched (x[N].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ N
    let wp := W (strictEventIndex R (M.proposal_time S.E s))
      (S.E.proposer s)
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E s) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E s))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer s)) pn.st ⇢ some P →
    ∃ k : Nat, (x[k].time : Int) = M.proposal_time S.E s ∧
      (⟨S.E.proposer s, NamedObject.block P⟩ : SignedMsg V (NamedObject V)) ∈ x[k].sent ∧
      Restated.proposedBlockAtStep M S x k s P.erase := by
  intro R W wp cp hcp pn hP
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ N hsync hmono hawake
    hgst hcv hvalid hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hPclock : M.proposal_with (M.gradeContract cp)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer s))
      (M.ns_setClock S.E wp.st (M.proposal_time S.E s)) ⇢ some P := by
    have h := hP
    rw [show pn.st = M.store_with_cache (M.ns_setClock S.E wp.st (M.proposal_time S.E s)) _ from
      facts.nd.mkNode_st _ _ _, facts.dt.proposal_with_store_with_cache] at h
    exact h
  obtain ⟨hslot, hemit⟩ := Restated.proposalTickOn facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf hHs s hs hprop hhor hlo (fun j hj => hf.tick_outcome j _ _ hj) hrun cp hcp hPclock
  obtain ⟨k, -, hktick, hsent⟩ := Restated.mem_sent_of_emits_runAll facts S Sched x v₀ hemit
  have hauth : NamedObject.author (NamedObject.block P) = some (S.E.proposer s) :=
    Restated.author_of_emits facts (Setup.alwaysAwake S) _ W hf.onePath hemit
  exact ⟨k + 1, (Restated.tickStepAt_time facts x hktick).1, hsent, P, hsent, rfl, hslot,
    (author_block P).symm.trans hauth⟩

end

end DecoupledConsensusModel.Sts.Restated
