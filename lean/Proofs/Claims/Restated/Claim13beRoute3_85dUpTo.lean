import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_44UpTo
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_65b
import Proofs.Claims.Restated.Claim13beRoute3_67b
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_72UpTo
import Proofs.Claims.Restated.Claim13beRoute3_78
import Proofs.Claims.Restated.Claim13beRoute3_83UpTo
import Proofs.Claims.Restated.Claim13beRoute3_85b
import Proofs.Claims.Restated.Claim13beRoute3_85bUpTo
import Proofs.Claims.Restated.Claim13beRoute3_85d
import Proofs.Claims.Restated.Claim13beRoute3_86e
import Proofs.Claims.Restated.Claim13beRoute3_86f
import Proofs.Claims.Restated.Claim13beRoute3_86gUpTo
import Proofs.Claims.Restated.Claim13beRoute3_87bUpTo
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ReaderLocalCone
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_RecoveryProposalConfirmationRead
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Grades
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_JustificationBound
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDerived
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# Strong windows after the re-based deadline round, with bounded synchrony

The theorems of `Claim13beRoute3_85d.lean` along the path an execution follows, with synchrony
assumed only up to an instant.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_86g.lean`, by name. -/
local macro "p86g% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86g)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_86f.lean`, by name. -/
local macro "p86f% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86f)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_58.lean`, by name. -/
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_60.lean`, by name. -/
local macro "p60% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_60)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_56.lean`, by name. -/
local macro "p56% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_56)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_55.lean`, by name. -/
local macro "p55% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_55)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_64b.lean`, by name. -/
local macro "p64b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_64b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_71.lean`, by name. -/
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_86c.lean`, by name. -/
local macro "p86c% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86c)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_83UpTo.lean`, by name. -/
local macro "p83u% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83UpTo)
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

/-- `roundAt S tGAT + η_SG < deadlineRoundW S tGAT gap`. -/
private theorem rGST_lt_deadline₈₅du (S : Setup V) (tGAT : Int) (gap : Nat) :
    Restated.roundAt M S tGAT + S.hc.η_SG < Restated.deadlineRoundW M S tGAT gap := by
  unfold Restated.deadlineRoundW
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ _)

/-- If `roundAt S tGAT + η_SG < k`, then `tGAT + 1` is at most one delay before round `k`'s grade-2
    window start and one delay before its grade-1 window start. -/
private theorem lo_le_windows₈₅du (facts : Record.Facts M) (S : Setup V) {tGAT : Int} {k : Round}
    (h : Restated.roundAt M S tGAT + S.hc.η_SG < k) :
    tGAT + 1 ≤ M.early S.E S.hc k .g2 - S.E.Δ ∧ tGAT + 1 ≤ M.early S.E S.hc k .g1 - S.E.Δ := by
  have h0 := Restated.lo_le_early_g2_sub_delta_of_action_lt facts S
    (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) h
  have h1 := facts.gr.early_g2_add_delta_le_early_g1 S k
  have hΔ := S.E.Δ_pos
  exact ⟨h0, by linarith⟩

/-- With synchrony assumed only up to `tE`, in the run of the execution `x` up to step `n`, along
    its path `W`: if `T_D'` is an anchor at the re-based deadline round `rD'`, `rD' + 1 ≤ q`,
    `S.a q ≤ x[n].time ≤ tE`, and the proposer of `o_q` is not held at `o_q`'s confirmation instant
    and `P` is a proposal of its read on `W`, then `h(T_D') ≤ h(P)`. -/
theorem openingProposal_height_ge_rebasedAnchor_l85d_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x tE) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    {T_D' : NamedBlock V}
    (hA' : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D')
    {q : Round} (hq : Restated.rebasedDeadlineRoundW M S tGAT gap + 1 ≤ q)
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
    (M.derive_named S.E S.cfg T_D').h ≤ (M.derive_named S.E S.cfg P).h := by
  intro R W wp cp hcp pn hP
  have hsync' : Restated.SynchronyFromWakeBefore M S x (x[n].time : Int) :=
    (p83u% syncBefore_mono₈₃u) hn hsync
  have hA'c := hA'
  obtain ⟨-, -, n₀, -, -, -, -, -, -, -, -, hn₀, -⟩ := hA'
  have hrD'q : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ q := (Nat.le_succ _).trans hq
  have hrDq : Restated.deadlineRoundW M S tGAT gap + 2 ≤ q := by
    refine le_trans ?_ hq
    show Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.deadlineRoundW M S tGAT gap + gap + 1 + 1
    exact Nat.add_le_add_right (Nat.succ_le_succ (Nat.le_add_right _ _)) 1
  have hSa : (Restated.Vocabulary.Execution.Setup.a M S (Restated.rebasedDeadlineRoundW M S tGAT gap)) ≤ (x[n].time : Int) :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hrD'q).trans hqhor
  obtain ⟨blocked, first, i, a, ta, Cfg, T, Tprev, c0, hreg, hround, -, htop, -⟩ :=
    Restated.switchRoundRegime_runAll_notHeld_atRound_upTo facts S Sched x v₀ hsync' hmono hawake hgst
      hcv hvalid hawm hthird hcom hrec (Restated.deadlineRoundW_le_rebased facts S tGAT gap) hn₀ hSa
      hn
  have hheight := Restated.anchorAtRound_height_upTo facts S Sched x hsync hmono hawake hgst hcv hvalid
    hawm hthird hA'c hn₀
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v₀ n hsync' hmono hawake
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
  have hadopt := (Restated.openingAdoption_at_strongWindow_afterDeadline_upTo facts S Sched x v₀ n
    hsync' hmono hawake hgst hcv hvalid hawm hthird hn hcom hrec hrDq hqhor hopening cp hcp
    hP).1
  have hw : S.E.proposer ((M.opening_slot S.hc q)) ∈
      notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc q))) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hopening
  have hTP : Block.Preceq T.erase P.erase := by
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
    rewrite [show pn.st = M.store_with_cache
        (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q))) cp from
      facts.nd.mkNode_st _ _ _, facts.dt.proposal_with_store_with_cache] at h
    exact h
  have hwinQ : tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc q)) .g1 - S.E.Δ := by
    rw [facts.gr.round_of_opening_slot_eq S.hc]
    exact (lo_le_windows₈₅du facts S (lt_of_lt_of_le (rGST_lt_deadline₈₅du S tGAT gap)
      ((Nat.le_add_right _ 2).trans hrDq))).2
  have hPrun := Restated.proposedBlock_runBlockOn facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf hHs hHsXb hpos hopening hpropHor hgat (fun j hj => hf.tick_outcome j _ _ hj)
    (fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hopening) hwinQ)
    cp hcp hPclock
  have hTPn : NamedBlock.Preceq T P :=
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

/-- With synchrony assumed only up to the tick time `t`, in the run of the execution `x` up to step
    `m + 1`, along its path `W`: if `c` is at least two rounds after the deadline round, step `m` is
    the tick at `t` with `vote_time (o_c + 2) ≤ t ≤ tE`, the proposers of `o_c` and `o_c + 2` are
    not held at their confirmation instants, `P` and `P₂` are proposals of their reads on `W` with
    `P ⪯ P₂`, and `w` is not held at `t`, then `P₂` is among `w`'s bodies after `m` steps and
    `h_j(P₂)` is at most `w`'s justified height there. -/
theorem windowProposal_held_atTick_l85d_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V)
    {tGAT tE : Int} {gap : Nat} {m : Nat} {t : Int}
    (hsync : Restated.SynchronyFromWakeBefore M S x t) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    {c : Round} (hc : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c)
    (hm : Restated.tickStepAt M x m t)
    (hvt : M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤ t) (htE : t ≤ tE)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hprop2 : S.E.proposer ((M.opening_slot S.hc c) + 2) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + 2)))
    {P P₂ : NamedBlock V}
    (hPP₂ : NamedBlock.Preceq P P₂)
    {w : V} (hw : w ∈ notHeldAt Sched t) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ (m + 1) with
          honest := notHeldAt Sched (x[m + 1].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ (m + 1)
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    let wp₂ := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c + 2)))
      (S.E.proposer (M.opening_slot S.hc c + 2))
    ∀ cp₂ : M.Cache,
      M.onPhaseTick S.E S.hc wp₂.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c + 2)) wp₂.cache ⇢ cp₂ →
      let pn₂ := M.mkNode
        (M.ns_setClock S.E wp₂.st (M.proposal_time S.E (M.opening_slot S.hc c + 2))) wp₂.record cp₂
      M.proposal_with (M.gradeContract cp₂) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c + 2))) pn₂.st ⇢ some P₂ →
    P₂ ∈ (x[m][w].st).st.bodies ∧
      (M.derive_named S.E S.cfg P₂).h_j ≤ (x[m][w].st).st.core.h_j := by
  intro R W wp cp hcp pn hP wp₂ cp₂ hcp₂ pn₂ hP₂
  obtain ⟨htime, -⟩ := Restated.tickStepAt_time facts x hm
  have hsync' : Restated.SynchronyFromWakeBefore M S x (x[m + 1].time : Int) :=
    (p83u% syncBefore_mono₈₃u) (le_of_eq htime) hsync
  have hn : (x[m + 1].time : Int) ≤ tE := by rw [htime]; exact htE
  obtain ⟨hAc, hvoteNext, -, -, -, hpv⟩ := Restated.interiorInstants_l85d facts S c
  have hvoteHor : M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤ (x[m + 1].time : Int) := by
    rw [htime]; exact hvt
  have hAcHor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤ (x[m + 1].time : Int) :=
    hAc.trans (hpv.trans hvoteHor)
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v₀ (m + 1) hsync' hmono
    hawake hgst hcv hvalid hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ (m + 1) hthird hn
  have hrecOn := Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ (m + 1) hrec hn
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hheads := (Restated.openingAdoption_at_strongWindow_afterDeadline_upTo facts S Sched x v₀
    (m + 1) hsync' hmono hawake hgst hcv hvalid hawm hthird hn hcom hrec hc hAcHor hopening cp
    hcp hP).1
  have hsource := Restated.fgSource_eq_openingProposal_of_some_runAll_notHeld_upTo facts S Sched x v₀
    (m + 1) hsync' hmono hawake hgst hcv hvalid hawm hthird hn hcom hrec hc hAcHor hopening cp
    hcp hP
  have hrootAt : ∀ u ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc c) + 2)),
      Block.Preceq
        (M.get_fg_root (M.toHealing
          (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc c) + 2))) u).st.core).toFG)
        P.erase :=
    fun u hu => Restated.fgRoot_preceq_openingProposal_at_read_afterDeadlineOn facts
      (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn hbelow hrecOn
      (Setup.timeoutDelayBound _) hpost
      (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]; exact hc) hheads hsource
      (hAc.trans hpv) hvoteNext hvoteHor hu (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) hloOpen ht₀
      (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ (m + 1) hmono
        hawake hn k hk u j hj)
  have hPP₂e : Block.Preceq P.erase P₂.erase :=
    Proofs.NamedWire.erase_preceq hPP₂
  obtain ⟨hpos2, hgat2⟩ : 0 < (M.opening_slot S.hc c) + 2 ∧
      tGAT + 1 ≤ M.proposal_time S.E ((M.opening_slot S.hc c) + 2) := by
    obtain ⟨-, hg⟩ := Restated.openingBounds_afterDeadline_l85d facts S hc
    exact ⟨Nat.succ_pos _, hg.trans (facts.sch.proposal_time_mono S.E (Nat.le_add_right _ 2))⟩
  have hP₂clock : M.proposal_with (M.gradeContract cp₂)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c + 2)))
      (M.ns_setClock S.E wp₂.st (M.proposal_time S.E (M.opening_slot S.hc c + 2))) ⇢ some P₂ := by
    have h := hP₂
    rewrite [show pn₂.st = M.store_with_cache
        (M.ns_setClock S.E wp₂.st (M.proposal_time S.E (M.opening_slot S.hc c + 2))) cp₂
      from facts.nd.mkNode_st _ _ _, facts.dt.proposal_with_store_with_cache] at h
    exact h
  have hrun₂ : ∀ j : Nat, R.events[j]? = some (Record.Event.tick
        (S.E.proposer (M.opening_slot S.hc c + 2)) (M.proposal_time S.E (M.opening_slot S.hc c + 2))) →
      M.awake_for_grade1 (Setup.alwaysAwake S) (S.E.proposer (M.opening_slot S.hc c + 2))
        (W j (S.E.proposer (M.opening_slot S.hc c + 2))) (M.round_of S.hc (M.opening_slot S.hc c + 2)) := by
    intro j hj
    have hwin : tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc c + 2)) .g1 -
        S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_add S.hc c
        (Nat.lt_of_lt_of_le (by decide : 2 < 3) S.hc.R_ge_three)]
      exact (lo_le_windows₈₅du facts S (lt_of_lt_of_le (rGST_lt_deadline₈₅du S tGAT gap)
        ((Nat.le_add_right _ 2).trans hc))).2
    exact hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hprop2) hwin
  have hadmit := Restated.proposedBlock_admittedBefore_vote_after_gstOn facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs hHsXb hpos2 hprop2 hgat2 hvoteHor cp₂ hcp₂ hP₂clock
    (by
      intro u hu i hi
      exact Restated.Vocabulary.Proofs.finalized_preceq_at_prefix_of_storeBeforeRoot_preceq facts
        (Setup.alwaysAwake S) R hf.sorted (w := u) hi (W i) (hf.onePath i).1 _
        ((p55% onePath_slice₅₅b) W hf.onePath hi)
        (preceq_trans_Preceq (hrootAt u hu) hPP₂e))
    hrun₂
  have hwVote : w ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc c) + 2)) :=
    hHs _ _ hvt hw
  have hmem := (Restated.admittedBefore_mem_and_stamp_atOn facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf (hadmit w hwVote) hvt).1
  have hP₂run := Restated.proposedBlock_runBlockOn facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf hHs hHsXb hpos2 hprop2 (hpv.trans hvoteHor) hgat2
    (fun j hj => hf.tick_outcome j _ _ hj) hrun₂ cp₂ hcp₂ hP₂clock
  have hbody := Restated.namedBody_of_mem_storeBeforeTime_l86f facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf (Finset.mem_univ w) hmem hP₂run
  have hstep := Restated.stateBeforeTime_runAll_tick facts S Sched x v₀ hm (le_refl (m + 1)) w
  have hbody' : P₂ ∈ (x[m][w].st).st.bodies := by
    rw [← hstep]; exact hbody
  refine ⟨hbody', ?_⟩
  have hnh := Restated.Vocabulary.Proofs.NamedJustificationBound.noHighJustifications_stateBeforeTime
    facts (Setup.alwaysAwake S) R t w _ ((p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath t)
  exact (hnh P₂ hbody).trans (le_of_eq (congrArg (fun z => z.st.core.h_j) hstep))

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
open DecoupledConsensusModel.Internal.PhaseGrades

/-- With synchrony assumed only up to `x[n].time`, in the run of the execution `x` up to step `n`,
    along its path `W`: if `c` is at least two rounds after the deadline round,
    `vote_time (o_c + 2) ≤ x[n].time ≤ tE`, the proposers of `o_c` and `o_c + 2` are not held at
    their confirmation instants, and `P` and `P₂` are proposals of their reads on `W`, then `P₂` is
    not genesis, `P ⪯ parent(P₂)`, `parent(P₂).slot + 1 ≤ o_c + 2`, and every non-genesis ancestor
    of `P₂` has its parent at a lower slot. -/
theorem windowParent_l85d_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x (x[n].time : Int)) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    {c : Round} (hc : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c)
    (hvoteHor : M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤ (x[n].time : Int))
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hprop2 : S.E.proposer ((M.opening_slot S.hc c) + 2) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + 2)))
    {P P₂ : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    let wp₂ := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c + 2)))
      (S.E.proposer (M.opening_slot S.hc c + 2))
    ∀ cp₂ : M.Cache,
      M.onPhaseTick S.E S.hc wp₂.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c + 2)) wp₂.cache ⇢ cp₂ →
      let pn₂ := M.mkNode
        (M.ns_setClock S.E wp₂.st (M.proposal_time S.E (M.opening_slot S.hc c + 2))) wp₂.record cp₂
      M.proposal_with (M.gradeContract cp₂) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c + 2))) pn₂.st ⇢ some P₂ →
    P₂ ≠ .genesis ∧ NamedBlock.Preceq P P₂.parent ∧
      P₂.parent.slot + 1 ≤ (M.opening_slot S.hc c) + 2 ∧
      ∀ X : NamedBlock V, NamedBlock.Preceq X P₂ → X ≠ .genesis → X.parent.slot < X.slot := by
  intro R W wp cp hcp pn hP wp₂ cp₂ hcp₂ pn₂ hP₂
  classical
  obtain ⟨q, rfl⟩ : ∃ q : Round, c = q + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by
      intro h0; rw [h0] at hc; exact absurd hc (Nat.not_succ_le_zero _ ∘ fun h =>
        (Nat.le_add_left 1 _).trans ((Nat.le_succ _).trans h)))
  set o := (M.opening_slot S.hc (q + 1)) with ho
  obtain ⟨hAc, hvoteNext, hpconf, hsupp, hAcDelta, hpv⟩ :=
    Restated.interiorInstants_l85d facts S (q + 1)
  have hΔ := S.E.Δ_pos
  have hpropHor : M.proposal_time S.E (o + 2) ≤ R.horizon := hpv.trans hvoteHor
  obtain ⟨hv1, hs1, -, -, -, -⟩ := facts.sch.slot_instants_l55 S.E (o + 1)
  have hvs : M.vote_time S.E (o + 1) ≤ M.support_cutoff S.E (o + 1) := by linarith
  have hAcHor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1)) ≤
      (x[n].time : Int) := hAc.trans hpropHor
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v₀ n hsync hmono hawake
    hgst hcv hvalid hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn
  have hrecOn := Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ n hrec hn
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hloPost := Restated.roundAt_lo_le_rGST_l71 facts S tGAT
  have hA : ∀ k : Round, tGAT + 1 ≤ M.early S.E S.hc k .g2 - S.E.Δ →
      ∀ u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat,
        R.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) →
        M.awake_for_grade2 (Setup.alwaysAwake S) u (W j u) k :=
    fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj
  have hDq : Restated.deadlineRoundW M S tGAT gap ≤ q :=
    Nat.le_of_succ_le_succ ((Nat.le_succ _).trans hc)
  have hwinQ1 := lo_le_windows₈₅du facts S
    (lt_of_lt_of_le (rGST_lt_deadline₈₅du S tGAT gap) (hDq.trans (Nat.le_succ q)))
  have hD : Restated.fgSafetyProgressDeadline (Setup.alwaysAwake S) R
      (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds =
      Restated.deadlineRoundW M S tGAT gap :=
    Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts S R tGAT gap
  obtain ⟨hopos, hgatO⟩ := Restated.openingBounds_afterDeadline_l85d facts S hc
  have hconfA : M.confirmation_time S.E o = (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S (q + 1)
  have hp0 : S.E.proposer o ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))) := by
    rw [← hconfA]; exact hopening
  have hpnst : pn.st = M.store_with_cache (M.ns_setClock S.E wp.st (M.proposal_time S.E o)) cp :=
    facts.nd.mkNode_st _ _ _
  have hpncache : pn.cache = cp := facts.nd.mkNode_cache _ _ _
  have hpread : pn ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M
      (Setup.alwaysAwake S) R o :=
    (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp hcp
  have hPn : M.proposal_with (M.gradeContract pn.cache) .poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer o)) pn.st ⇢ some P := by
    rw [hpncache]
    exact hP
  have hPclock : M.proposal_with (M.gradeContract cp)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer o))
      (M.ns_setClock S.E wp.st (M.proposal_time S.E o)) ⇢ some P := by
    have h := hP
    rw [hpnst, facts.dt.proposal_with_store_with_cache] at h
    exact h
  have hpn₂st : pn₂.st = M.store_with_cache (M.ns_setClock S.E wp₂.st (M.proposal_time S.E (o + 2))) cp₂ :=
    facts.nd.mkNode_st _ _ _
  have hpn₂cache : pn₂.cache = cp₂ := facts.nd.mkNode_cache _ _ _
  have hp₂read : pn₂ ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M
      (Setup.alwaysAwake S) R (o + 2) :=
    (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp₂ hcp₂
  have hP₂n : M.proposal_with (M.gradeContract pn₂.cache) .poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer (o + 2))) pn₂.st ⇢ some P₂ := by
    rw [hpn₂cache]
    exact hP₂
  have hP₂clock : M.proposal_with (M.gradeContract cp₂)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer (o + 2)))
      (M.ns_setClock S.E wp₂.st (M.proposal_time S.E (o + 2))) ⇢ some P₂ := by
    have h := hP₂
    rw [hpn₂st, facts.dt.proposal_with_store_with_cache] at h
    exact h
  have hsg := Restated.sgBlock_eq_openingProposal_runAll_notHeld_upTo facts S Sched x v₀ n hsync hmono
    hawake hgst hcv hvalid hawm hthird hn hcom hrec hc hAcHor hopening cp hcp hP
  obtain ⟨nv0, hnv0, g0, hg0, G0, hG0⟩ := (p56% exists_actionSG₅₆) facts (Setup.alwaysAwake S)
    (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1)))
      (S.E.proposer o)) (q + 1)
  have hG0P : G0 = P.erase := hsg _ hp0 nv0 hnv0 g0 hg0 G0 hG0
  have hfirst := fun (w : V) (hw : w ∈ notHeldAt Sched (M.vote_time S.E (o + 1))) =>
    Restated.actionSGBlock_preceq_firstInteriorHead_after_GST_namedOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn hbelow hrecOn
      (Setup.timeoutDelayBound _) hpost (by rw [hD]; exact hDq) hAcHor hp0
      (fun j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
        (q + 1) hwinQ1.1 _ j hj) hw hloPost
      hloOpen ht₀ hA
  have hvote1Hor : M.vote_time S.E (o + 1) ≤ R.horizon :=
    (hvs.trans hsupp).trans hpropHor
  have hlo1 : tGAT + 1 ≤ M.vote_time S.E (o + 1) :=
    hgatO.trans ((facts.sch.proposal_time_mono S.E (Nat.le_succ o)).trans
      (facts.sch.proposal_time_lt_vote_time S.E (o + 1)).le)
  have hcone : Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S) R W (notHeldAt Sched)
      Finset.univ (o + 1) (fun X => Block.Preceq P.erase X) := by
    intro w hw hcomm
    obtain ⟨H, cw, hcw, Tr, hTr, L, hL, L', hL', hH⟩ :=
      (p86g% exists_headOutcome₈₆g) facts (Setup.alwaysAwake S)
        (W (strictEventIndex R (M.vote_time S.E (o + 1))) w) (M.vote_time S.E (o + 1))
    obtain ⟨X, hXerase, hXrun, hXemit⟩ := Restated.named_voter_head_emitsOn facts
      (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hHsXb hw (Nat.succ_pos o) hcomm
      hvote1Hor hlo1 cw hcw
      (fun j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw (by
        show tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc (o + 1)) .g1 - S.E.Δ
        rw [ho, facts.gr.HealingLemmas_round_of_opening_succ S.hc]
        exact hwinQ1.2))
      Tr hTr L hL L' hL' H hH
    have hGH := hfirst w hw cw hcw Tr hTr L hL L' hL' H hH nv0 hnv0 g0 hg0 G0 hG0
    rw [hG0P] at hGH
    exact ⟨X, by rw [hXerase]; exact hGH, hXrun, hXemit⟩
  have huRead : S.E.proposer (o + 2) ∈ notHeldAt Sched (M.proposal_time S.E (o + 2)) :=
    hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hprop2
  have huVote1 : S.E.proposer (o + 2) ∈ notHeldAt Sched (M.vote_time S.E (o + 1)) :=
    hHs _ _ (hvs.trans hsupp) huRead
  have hheads := (Restated.openingAdoption_at_strongWindow_afterDeadline_upTo facts S Sched x v₀ n
    hsync hmono hawake hgst hcv hvalid hawm hthird hn hcom hrec hc hAcHor hopening cp hcp
    hP).1
  have hsource := Restated.fgSource_eq_openingProposal_of_some_runAll_notHeld_upTo facts S Sched x v₀
    n hsync hmono hawake hgst hcv hvalid hawm hthird hn hcom hrec hc hAcHor hopening cp hcp hP
  have hroot : Block.Preceq
      (M.get_fg_root (M.toHealing
        (W (strictEventIndex R (M.proposal_time S.E (o + 2))) (S.E.proposer (o + 2))).st.core).toFG)
      P.erase :=
    Restated.fgRoot_preceq_openingProposal_at_read_afterDeadlineOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn hbelow hrecOn
      (Setup.timeoutDelayBound _) hpost (by rw [hD]; exact hc) hheads hsource
      hAc (hpv.trans hvoteNext) hpropHor huRead hloPost hloOpen ht₀ hA
  have hPrun := Restated.proposedBlock_runBlockOn facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf hHs hHsXb hopos hopening
    ((facts.sch.proposal_time_le_confirmation_time S.E o).trans (by rw [hconfA]; exact hAcHor))
    hgatO (fun j hj => hf.tick_outcome j _ _ hj)
    (fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hopening) (by
        show tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc o) .g1 - S.E.Δ
        rw [ho, facts.gr.round_of_opening_slot_eq S.hc]
        exact hwinQ1.2))
    cp hcp hPclock
  have hactiveStore : P.erase ∈ M.get_filtered_block_tree
      (M.toHealing
        (W (strictEventIndex R (M.proposal_time S.E (o + 2))) (S.E.proposer (o + 2))).st.core).toFG := by
    have hDread : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S))
        (Restated.fgSafetyProgressDeadline (Setup.alwaysAwake S) R
        (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds) ≤
        M.proposal_time S.E (o + 2) := by
      rw [hD]
      exact ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
        (hDq.trans (Nat.le_succ q))).trans hAc
    have hslotD : (M.opening_slot S.hc) (Restated.fgSafetyProgressDeadline
        (Setup.alwaysAwake S) R (Restated.roundAt M S tGAT + S.hc.η_SG) gap
        (Setup.alwaysAwake S).extraRounds) + 1 ≤ o + 1 := by
      rw [hD]
      exact Nat.succ_le_succ (facts.gr.opening_slot_mono S (hDq.trans (Nat.le_succ q)))
    have hshor1 : M.vote_time S.E (o + 1) + S.E.Δ ≤ R.horizon := by
      refine le_trans ?_ hpropHor
      linarith
    obtain ⟨T, hTrun, hTband, hTheads⟩ :=
      (p86f% exists_namedCommonPreviousHeadAncestor_in_frontierBand_after_GSTOn₈₆f) facts
        (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn hbelow hrecOn
        (Setup.timeoutDelayBound _) hpost hDread hpropHor hslotD hpconf hshor1 huRead hloPost
        hloOpen ht₀ hA
    obtain ⟨H, cw, hcw, Tr, hTr, L, hL, L', hL', hH⟩ :=
      (p86g% exists_headOutcome₈₆g) facts (Setup.alwaysAwake S)
        (W (strictEventIndex R (M.vote_time S.E (o + 1))) (S.E.proposer (o + 2)))
        (M.vote_time S.E (o + 1))
    have hTH : Block.Preceq T.erase H :=
      hTheads _ huVote1 cw hcw Tr hTr L hL L' hL' H hH
    have hPH : Block.Preceq P.erase H := by
      have h := hfirst _ huVote1 cw hcw Tr hTr L hL L' hL' H hH nv0 hnv0 g0 hg0 G0 hG0
      rw [hG0P] at h
      exact h
    have hheadVote := Restated.voteDutyHead_mem_voteDutyStoreOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf (S.E.proposer (o + 2)) (o + 1) cw hcw Tr hTr L hL L' hL' H hH
    have hHvoteT : H ∈ (W (strictEventIndex R (M.vote_time S.E (o + 1)))
        (S.E.proposer (o + 2))).st.core.T := by
      have h := hheadVote
      rw [(p60% voteStore_eq₆₀s) facts, facts.hd.Sts_setClock_core_T] at h
      exact h
    have hheadRead : H ∈ (W (strictEventIndex R (M.proposal_time S.E (o + 2)))
        (S.E.proposer (o + 2))).st.core.T :=
      Restated.seedStore_T_subsetOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
        (S.E.proposer (o + 2)) (hvs.trans hsupp) hHvoteT
    have hmemRead := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
      (M.proposal_time S.E (o + 2))
    have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts
      (Setup.alwaysAwake S) R (M.proposal_time S.E (o + 2)) (S.E.proposer (o + 2)) _ hmemRead
    have hFJ := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      facts (Setup.alwaysAwake S) R (M.proposal_time S.E (o + 2)) (S.E.proposer (o + 2)) _ hmemRead
    have hpcT := hpc
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpcT
    rw [facts.sto.toHealing_T] at hpcT
    have hmemOf : ∀ Y : Block V, Block.Preceq Y H →
        Y ∈ (W (strictEventIndex R (M.proposal_time S.E (o + 2)))
          (S.E.proposer (o + 2))).st.core.T :=
      fun Y hY => Proofs.Records.mem_of_preceq hpcT.2 Y H hheadRead
        (preceq_eq_true_iff_Preceq.mpr hY)
    have hbandOf : ∀ Y : NamedBlock V,
        Restated.RunBlockOn M (Setup.alwaysAwake S) R W Finset.univ Y →
        Block.Preceq Y.erase H →
        (M.derive_named S.E S.cfg T).h ≤ (M.derive_named S.E S.cfg Y).h →
        (W (strictEventIndex R (M.proposal_time S.E (o + 2)))
          (S.E.proposer (o + 2))).st.core.h_max - 1 ≤
          ((W (strictEventIndex R (M.proposal_time S.E (o + 2)))
            (S.E.proposer (o + 2))).st.core.σ Y.erase).h := by
      intro Y hYrun hY hTY
      have hYbody := Restated.namedBody_of_mem_storeBeforeTime_l86f facts (Setup.alwaysAwake S)
        (notHeldAt Sched) Finset.univ hf (Finset.mem_univ (S.E.proposer (o + 2)))
        (hmemOf Y.erase hY) hYrun
      have hYview := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts
        (Setup.alwaysAwake S) R (M.proposal_time S.E (o + 2)) (S.E.proposer (o + 2)) _ hmemRead
        Y hYbody
      rw [hYview]
      exact hTband.trans hTY
    rcases preceq_linear_Preceq hTH hPH with hTP | hPT
    · have hTPn := Restated.namedPreceq_of_runBlock_erase_preceqOn facts (notHeldAt Sched)
        Finset.univ hf hTrun hPrun hTP
      exact Restated.Vocabulary.Proofs.HealingSurface.canonicalConeSegment_mem_filtered_of_root_preceq
        facts hpc hFJ hroot (hmemOf P.erase hPH)
        (hbandOf P hPrun hPH (facts.cs.derive_height_mono S.E S.cfg hTPn))
        (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
        (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
    · exact Restated.Vocabulary.Proofs.HealingSurface.canonicalConeSegment_mem_filtered_of_root_preceq
        facts hpc hFJ hroot (hmemOf T.erase hTH) (hbandOf T hTrun hTH le_rfl)
        (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hPT
  have hactive : P.erase ∈ M.get_filtered_block_tree
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M (Setup.alwaysAwake S)
        (W (strictEventIndex R (M.proposal_time S.E (o + 1 + 1)))
          (S.E.proposer (o + 1 + 1))).st.core
        (M.proposal_time S.E (o + 1 + 1)))).toFG := by
    rw [(p86f% tickStore_eq₈₆f) facts, (p60% setClock_filtered₆₀) facts]
    exact hactiveStore
  have hupper := Restated.actionSGBlock_preceq_proposedParent_runAll_notHeld_afterDeadline_upTo facts S
    Sched x v₀ n hsync hmono hawake hgst hcv hvalid hawm hthird hn hcom hrec hc
    ((facts.sch.Protocol_vote_time_le_confirmation_time S.E o).trans (by rw [hconfA]; exact hAcHor))
    hopening cp hcp hP
  simp only [Nat.add_sub_cancel] at hupper
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract cp) S.E S.hc
    ((Setup.alwaysAwake S).node (S.E.proposer o)) (M.toHealing pn.st.core)
  have hI' : Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract pn.cache) S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer o)) (M.toHealing pn.st.core) ⇢ I := by
    rw [hpncache]
    exact hI
  obtain ⟨-, hIP⟩ := (p58% parent_preceq_of_proposal₅₈s) facts (Setup.alwaysAwake S) R o pn hpread
    hPn I hI'
  have hupperP : ∀ v ∈ notHeldAt Sched
        ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)),
      ∀ nq ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)) v) q,
      ∀ g, M.grade2_block_with (M.gradeContract nq.cache) S.E S.hc (M.toHealing nq.st.core)
          (M.round_of S.hc (M.toHealing nq.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract nq.cache) S.E S.hc (M.toHealing nq.st.core)
          (M.round_of S.hc (M.toHealing nq.st.core).s) g ⇢ B →
        Block.Preceq B P.erase := by
    intro v hv nq hnq g hg B hB
    exact preceq_trans_Preceq (hupper v hv nq hnq g hg B hB I hI) hIP
  have hrootProp : Block.Preceq
      (M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex R (M.proposal_time S.E (o + 2))) (S.E.proposer (o + 2))).st
        (M.proposal_time S.E (o + 2)))
        (W (strictEventIndex R (M.proposal_time S.E (o + 2))) (S.E.proposer (o + 2))).record
        cp₂).st.core).toFG) P.erase := by
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [(p60% setClock_fgRoot₆₀) facts]
    exact hroot
  have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1) ≤ R.horizon := by
    have h1 := facts.sch.proposal_time_mono S.E (Nat.le_add_right o 2)
    unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1
    rw [facts.sch.Γ_0_eq_proposal_time S.hc S.E (q + 1)]
    linarith
  have hpostQ : tGAT + 1 ≤ (Restated.Vocabulary.Execution.Setup.a M S q) :=
    hloPost.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (by
      unfold Restated.deadlineRoundW at hDq
      exact (Nat.le_succ _).trans ((Nat.le_add_right _ _).trans hDq)))
  have hgatG1 : tGAT + 1 ≤ M.domain S.E S.hc (q + 1) .g1 := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
    exact hgatO
  have hslo : (M.opening_slot S.hc (q + 1)) + 1 ≤ o + 2 := Nat.succ_le_succ (Nat.le_succ o)
  have hshi : o + 2 < (M.opening_slot S.hc (q + 1 + 1)) := by
    have hR := S.hc.R_ge_three
    rw [ho, facts.gr.opening_slot_succ S.hc (q + 1)]
    exact Nat.add_lt_add_left (lt_of_lt_of_le (by decide) hR) _
  have hanchor := Restated.interiorProposalAnchor_preceq_of_previousCarriersOn_l85d facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hHs hHsXb hbelow hpostQ hcut hslo
    hshi hpropHor hupperP huRead cp₂ hcp₂ hrootProp
    (fun u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn q
      (lo_le_windows₈₅du facts S (lt_of_lt_of_le (rGST_lt_deadline₈₅du S tGAT gap) hDq)).1 u j hj)
    hgatG1
  have hround2 : M.round_of S.hc pn₂.st.core.s = q + 1 := by
    rw [hpn₂st, facts.nd.store_with_cache_core_s, facts.hd.Sts_setClock_core_s,
      facts.sch.slotOf_proposal_time]
    exact facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hslo hshi
  obtain ⟨A0, hA0⟩ := (p58% nodeAnchor_outcome₅₈) facts (Setup.alwaysAwake S) pn₂
    (M.round_of S.hc pn₂.st.core.s)
  have hA0' : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M (Setup.alwaysAwake S) pn₂
      (q + 1) ⇢ A0 := by
    have h := hA0
    rw [hround2] at h
    exact h
  have hcompat : Block.compatible A0 P.erase = true :=
    compatible_of_preceq_common_Preceq (hanchor A0 hA0')
      (Proofs.ModelProperties.Preceq_self P.erase)
  have hconeT := Restated.coneTarget_preceq_nextProposedParent_namedOn facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn (Nat.succ_pos o) hlo1
    (hsupp.trans hpropHor) (hHs _ _ (hsupp.trans (facts.sch.proposal_time_le_confirmation_time
      S.E _)) hprop2) hcone hactive cp₂ hcp₂ A0 hA0 hcompat
  obtain ⟨I₂, hI₂⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract cp₂) S.E S.hc
    ((Setup.alwaysAwake S).node (S.E.proposer (o + 2))) (M.toHealing pn₂.st.core)
  have hI₂' : Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract pn₂.cache) S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer (o + 2))) (M.toHealing pn₂.st.core) ⇢ I₂ := by
    rw [hpn₂cache]
    exact hI₂
  obtain ⟨Q, hQ, hQerase⟩ := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_parent facts
    (Setup.alwaysAwake S) R (o + 2) pn₂ hp₂read hP₂n I₂ hI₂'
  have hP₂ne : P₂ ≠ .genesis := by
    intro h; rw [h] at hQ; cases hQ
  have hP₂par : P₂.parent = Q := by
    cases P₂ with
    | genesis => cases hQ
    | node p sl rt vs sp rows proposer =>
        simp only [NamedBlock.parent?] at hQ
        rw [namedBlock_parent_node]
        exact Option.some.inj hQ
  have hP₂run := Restated.proposedBlock_runBlockOn facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf hHs hHsXb (Nat.succ_pos _) hprop2 hpropHor
    (hgatO.trans (facts.sch.proposal_time_mono S.E (Nat.le_add_right o 2)))
    (fun j hj => hf.tick_outcome j _ _ hj)
    (fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj huRead (by
      show tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc (o + 2)) .g1 - S.E.Δ
      rw [ho, facts.gr.round_of_opening_slot_add S.hc (q + 1)
        (Nat.lt_of_lt_of_le (by decide : 2 < 3) S.hc.R_ge_three)]
      exact hwinQ1.2))
    cp₂ hcp₂ hP₂clock
  have hQrun : Restated.RunBlockOn M (Setup.alwaysAwake S) R W Finset.univ Q :=
    Restated.blockInRun_of_ancestorOn facts (Setup.alwaysAwake S) R W Finset.univ hP₂run
      (by rw [← hP₂par]; exact parent_namedPreceq_l85 P₂)
  have hPQ : NamedBlock.Preceq P Q :=
    Restated.namedPreceq_of_runBlock_erase_preceqOn facts (notHeldAt Sched) Finset.univ hf hPrun hQrun
      (by rw [hQerase]; exact hconeT I₂ hI₂')
  have hQstore : Q.erase ∈ (W (strictEventIndex R (M.proposal_time S.E (o + 2)))
      (S.E.proposer (o + 2))).st.core.T := by
    rw [hQerase]
    have h := Restated.Vocabulary.Proofs.HealingSurface.proposedParent_mem facts (Setup.alwaysAwake S)
      R (o + 2) pn₂ hp₂read I₂ hI₂'
    rw [hpn₂st, facts.nd.store_with_cache_core_T, facts.hd.Sts_setClock_core_T] at h
    exact h
  have hP₂lt : P₂.parent.slot < P₂.slot :=
    named_parent_slot_lt_of_erase_l85d (Restated.proposedBlock_parent_slot_ltOn facts
      (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf (Nat.succ_pos _) cp₂ hcp₂ hP₂clock)
  have hP₂slot : P₂.slot = o + 2 :=
    Restated.Vocabulary.Proofs.Optimistic.proposedBlockAt_slot facts (Setup.alwaysAwake S) R (o + 2)
      (some P₂) ((p56% proposedBlockAt_mem₅₆h) facts (Setup.alwaysAwake S) hf (o + 2) cp₂ hcp₂
        hP₂clock) rfl
  refine ⟨hP₂ne, by rw [hP₂par]; exact hPQ, by rw [← hP₂slot]; exact hP₂lt, ?_⟩
  intro X hX hXne
  rcases hXeq : P₂ with _ | ⟨p, sl, rt, vs, sp, rows, proposer⟩
  · exact absurd hXeq hP₂ne
  · rw [hXeq] at hX
    rcases namedPreceq_node_iff_l85.mp hX with heq | hXp
    · rw [heq, ← hXeq]; exact hP₂lt
    · have hpQ : p = Q := by
        rw [hXeq, namedBlock_parent_node] at hP₂par
        exact hP₂par
      rw [hpQ] at hXp
      have hXmem := Restated.ancestor_mem_storeBeforeTimeOn facts (Setup.alwaysAwake S)
        (notHeldAt Sched) Finset.univ hf hQstore (Proofs.NamedWire.erase_preceq hXp)
      have hXne' : X.erase ≠ Block.genesis := fun h =>
        hXne (eq_named_genesis_of_erase_eq_genesis h)
      exact named_parent_slot_lt_of_erase_l85d (Restated.parent_slot_lt_of_mem_storeBeforeTimeOn
        facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hXmem hXne')

end

end DecoupledConsensusModel.Sts.Restated
