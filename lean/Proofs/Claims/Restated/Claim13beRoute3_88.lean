import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_70
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_79
import Proofs.Claims.Restated.Claim13beRoute3_86e
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RecoveryGenuineClearNextVote
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_79
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_88

/-!
# The previous round's SG blocks under later votes

In the run of the first `N` steps of an execution `x`, over a model `M : Record.Model V`: from two
rounds after the progress deadline on, the previous round's SG blocks are ancestors of the heads
that later honest votes name, and the consequences at the switch round `Restated.switchRound M S tE`
and at the rounds before it.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p63% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_63)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p69b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_69b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p70% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_70)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p72% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_72)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p73% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_73)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p74% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_74)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p78% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_78)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation

/-- In the run of the first `N` steps of the execution `x`, along its path: for a round `r` at least
    two rounds after the progress deadline and a slot `d` after the opening slot of round `r − 1`
    with `vote_time d + Δ ≤ x[N].time`, every block `G` the SG vote selector can return at a
    round-`(r − 1)` action read of a validator not held at `S.a (r − 1)` is an ancestor of a run
    block that every committee member of `d` not held at `vote_time d` votes at `d`. -/
theorem previousRoundSGBelowVotes_runAll_notHeld (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (N : Nat)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hN : (x[N].time : Int) ≤ tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    {r : Round} (hr : Restated.deadlineRoundW M S tGAT gap + 2 ≤ r)
    {d : Slot} (hd : (M.opening_slot S.hc (r - 1)) + 1 ≤ d)
    (hhor : M.vote_time S.E d + S.E.Δ ≤ (x[N].time : Int)) :
    ∀ u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) u)
          (r - 1),
      ∀ A2 : Option (Block V),
        M.grade2_block_with (M.gradeContract nu.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
          (M.toHealing nu.st.core)
          (M.round_of (Setup.alwaysAwake S).hc (M.toHealing nu.st.core).s) ⇢ A2 →
      ∀ G : Block V,
        M.get_sg_vote_with (M.gradeContract nu.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
          (M.toHealing nu.st.core)
          (M.round_of (Setup.alwaysAwake S).hc (M.toHealing nu.st.core).s) A2 ⇢ G →
      Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (notHeldAt Sched) Finset.univ d
        (fun X => Block.Preceq G X) := by
  obtain ⟨c, rfl, hc, hc1, hr1⟩ := nat_round_split_l88 _ _ hr
  rw [hr1] at hd ⊢
  intro u hu nu hnu A2 hA2 G hG
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hN
  have hdPos : 0 < d := lt_of_lt_of_le (Nat.succ_pos _) hd
  have hvoteHor : M.vote_time S.E d ≤ (x[N].time : Int) :=
    le_trans (Int.le_add_of_nonneg_right S.E.Δ_pos.le) hhor
  have hgat : tGAT + 1 ≤ M.vote_time S.E d :=
    Restated.lo_le_vote_after_deadline_l86e facts (delayExtra := (Setup.alwaysAwake S).extraRounds) S
      (rho := ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V))
      (gap := gap) (Restated.roundAt_lo_le_rGST_l71 facts S tGAT)
      (le_trans (Nat.succ_le_succ (facts.gr.opening_slot_mono S hc1)) hd)
  intro w hw hwcomm
  obtain ⟨cc, hcc, Tr, hTr, L, hL, L', hL', H, hH⟩ := (p78% exists_voteHead₇₈) facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (M.vote_time S.E d)) w) d
  have hwinD : tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc d) .g1 - S.E.Δ := by
    have hcd : c + 1 ≤ M.round_of S.hc d := by
      have h := facts.gr.round_of_mono S.hc (le_trans (Nat.le_succ _) hd)
      rwa [facts.gr.round_of_opening_slot_eq S.hc] at h
    have hW : Restated.roundAt M S tGAT + S.hc.η_SG < Restated.deadlineRoundW M S tGAT gap := by
      unfold Restated.deadlineRoundW
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ _)
    have h0 := Restated.lo_le_early_g2_sub_delta_of_action_lt facts S
      (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) (lt_of_lt_of_le hW (hc1.trans hcd))
    have h1 := facts.gr.early_g2_add_delta_le_early_g1 S (M.round_of S.hc d)
    have hΔ := S.E.Δ_pos
    linarith
  obtain ⟨X, hXhead, hXrun, hXemit⟩ :=
    Restated.named_voter_head_emitsOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
      (fun _ => Finset.subset_univ _) hw hdPos hwcomm hvoteHor hgat cc hcc
      (fun j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwinD) Tr hTr L hL L' hL' H hH
  refine ⟨X, ?_, hXrun, hXemit⟩
  rw [hXhead]
  exact Restated.actionSGBlock_preceq_voterHeadAt_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv
    hvalid hawm hthird hN hcom hrec hc hd hhor hu hw cc hcc Tr hTr L hL L' hL' H hH nu hnu A2 hA2 G hG

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation

/-- If `t_GST ≤ tGAT`, `tGAT + healingLengthη S gap ≤ tE` and `strongOpeningsRecurFrom` holds, then
    `Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.rebasedDeadlineRoundW M S tGAT gap`. -/
theorem deadlineRoundW_add_two_le_rebased_l88 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    {tGAT tE : Int} {gap : Nat} (rho : Record.Run V)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) :
    Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.rebasedDeadlineRoundW M S tGAT gap := by
  obtain ⟨c₁, h₁, h₂, -⟩ :=
    Restated.exists_strongWindow_before_rebasedDeadlineRoundW facts S Sched rho hgst hlen hrec
  exact h₁.trans ((Nat.le_succ c₁).trans h₂)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation

/-- For every `v` and every step `N` whose instant is the confirmation instant of the switch round's
    opening slot plus two, and every choice `nprev` of a node state of each validator's
    round-`(rW − 1)` action read along the path of the first `N` steps of `x`,
    `Restated.BasePreviousRoundSGBelowOpeningVotes` holds along that path at that choice, where
    `rW = Restated.switchRound M S tE`. -/
theorem basePreviousRoundSGBelowOpeningVotes_atSwitch (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int)
    (gap : Nat)
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
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) :
    ∀ (v : V) (N : Nat),
      (x[N].time : Int) = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2) →
      ∀ nprev : V → M.N,
      (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
        (Restated.switchRound M S tE - 1)) →
      Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) nprev := by
  intro v N hN nprev hnprev
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    (Restated.runAll M S Sched x v 0) hgst hlen' htd
  have hNE : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hr : Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_add_two_le_rebased_l88 facts S Sched (Restated.runAll M S Sched x v 0) hgst hlen' hrec).trans
      (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v 0) hgst hlen')
  obtain ⟨c, hcW, -, -, hr1⟩ := nat_round_split_l88 _ _ hr
  have hd : (M.opening_slot S.hc (Restated.switchRound M S tE - 1)) + 1 ≤ (M.opening_slot S.hc (Restated.switchRound M S tE)) := by
    rw [hcW, hr1]
    exact facts.gr.opening_slot_succ_lt_l88 S c
  have hhor : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) + S.E.Δ ≤
      (x[N].time : Int) := by
    rw [hN]
    exact (facts.sch.vote_time_add_delta_le_confirmation_time S _).trans
      (facts.sch.confirmation_time_mono_l78 S (Nat.le_add_right _ 2))
  unfold Restated.BasePreviousRoundSGBelowOpeningVotes
  intro u hu D hD _ gc st k A2 hA2 G hG
  exact Restated.previousRoundSGBelowVotes_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hexec
    hmult hthird hNE hcom hrec hr hd hhor u hu (nprev u) (hnprev u) A2 hA2 G hG

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation

/-- At every round `r` from the re-based deadline round to the switch round and every step `N` with
    `S.a r ≤ x[N].time ≤ tE`, for a regime along the path of the first `N` steps of `x` over the
    validators not held, with source round `r`: every block the SG vote selector can return at the
    round-`(r − 1)` action read of a validator not held at `S.a (r − 1)` that emits its
    round-`(r − 1)` attestation is on one chain with the erasure of the regime's checkpoint `T`. -/
theorem basePreviousRoundSGCompatibleWithAnchor_atRound (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int)
    (gap : Nat)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) :
    ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      a.round = r →
      Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T := by
  intro r hrD' hrW v N blocked first i a ta Cfg T Tprev c0 hSaN hn hreg har
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hr : Restated.deadlineRoundW M S tGAT gap + 2 ≤ r :=
    (Restated.deadlineRoundW_add_two_le_rebased_l88 facts S Sched (Restated.runAll M S Sched x v 0) hgst hlen' hrec).trans
      hrD'
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hexec
    hmult hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hX : ∀ t : Int, 0 ≤ t → notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ _ => Finset.subset_univ _
  have hXXb : (Finset.univ : Finset V) ⊆ Finset.univ := Finset.Subset.refl _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
  obtain ⟨-, hloVote, -, -⟩ := Restated.loBounds_l70 facts S hapos hlo
  have hoPos : 0 < (M.opening_slot S.hc r) :=
    facts.gr.opening_slot_pos_of_round_pos S.hc (lt_of_lt_of_le hapos har.le)
  have hSc : (Restated.Vocabulary.Execution.Setup.a M S r) = M.confirmation_time S.E ((M.opening_slot S.hc r)) := by
    rw [Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time]
  have hcut : M.support_cutoff S.E ((M.opening_slot S.hc r)) ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := by
    rw [hSc]
    exact facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _
  have hpostVote : tGAT + 1 ≤ M.vote_time S.E ((M.opening_slot S.hc r)) := by
    rw [← har]
    exact hloVote
  have hconfHor : M.confirmation_time S.E ((M.opening_slot S.hc r)) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [← hSc]
    exact hSaN
  have hTCfg : Block.Preceq T.erase Cfg.erase := by
    rw [hreg.seed.checkpointDerived]
    exact facts.csAdded.derive_named_T_h_preceq S.E S.cfg Cfg
  obtain ⟨c, hcr, hc, -, hr1⟩ := nat_round_split_l88 _ _ hr
  have hd : (M.opening_slot S.hc (c + 1)) + 1 ≤ (M.opening_slot S.hc r) := by
    rw [hcr]
    exact facts.gr.opening_slot_succ_lt_l88 S c
  have hhor : M.vote_time S.E ((M.opening_slot S.hc r)) + S.E.Δ ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon :=
    (facts.sch.vote_time_add_delta_le_confirmation_time S _).trans hconfHor
  rw [hcr]
  unfold Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound
    Restated.HonestSGEmissionsCompatibleAtRoundOn
  rw [hr1]
  intro u hu nu hnu D hD _ gc st k A2 hA2 G hG
  have hSG := fun (y : V) (hy : y ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc r)))) =>
    Restated.actionSGBlock_preceq_voterHeadAt_runAll_notHeld facts S Sched x v N hsync hmono hawake
      hgst hcv hexec hmult hthird hn hcom hrec hc hd hhor hu hy
  have hmemWa := (p69b% mem_stateBeforeTime_along₆₉b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round)
  obtain ⟨na, hna⟩ := (p73% actionReadFrom_nonempty₇₃) facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round)) a.val_index) a.round
  obtain ⟨oQ, hoQ⟩ := (p70% nodeQ2_nonempty₇₀w) facts (Setup.alwaysAwake S) na a.round
  obtain ⟨Q, hQeq⟩ := hreg.seed.exists_nodeQ2_l70 facts na hna oQ hoQ
  rw [hQeq] at hoQ
  obtain ⟨oB, hoB⟩ := (p63% actionFGSource_nonempty₆₃w) facts (Setup.alwaysAwake S) na
  rw [hreg.seed.exactFGSource na hna oB hoB] at hoB
  rcases Restated.Vocabulary.Proofs.HealingSurface.actionFGSource_genuineClear_or_selectedG2_named facts
      (Setup.alwaysAwake S) _ a.val_index a.round _ hmemWa na hna hoQ hoB with
    ⟨Ca, hCa, -, -, -, hCfgCa⟩ | hCfgQ
  ·
    have hsigner : a.val_index ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S r)) := by
      have h := hreg.seed.signerHonest
      rw [hreg.seed.actionTime_eq, har] at h
      exact h
    obtain ⟨ca, hca, sta, -, rfl⟩ := hna
    rw [facts.nd.mkNode_cache] at hCa
    have hca' : M.onPhaseTick S.E S.hc
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index).st.core.toHealing
        (Restated.Vocabulary.Execution.Setup.a M S a.round)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index).cache ⇢ ca := hca
    have hCa' : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract ca) S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M (Setup.alwaysAwake S)
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index).st.core
          (M.confirmation_time S.E (M.opening_slot S.hc a.round)))
        (M.opening_slot S.hc a.round) Ca := hCa
    rw [har, hSc] at hca' hCa'
    have hwinR : tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc r)) .g1 -
        S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_eq S.hc]
      have h0 := Restated.lo_le_early_g2_sub_delta_of_opening facts S hapos hlo har.le
      have h1 := facts.gr.early_g2_add_delta_le_early_g1 S r
      have hΔ := S.E.Δ_pos
      linarith
    obtain ⟨y, hy, -, hCy⟩ :=
      Restated.genuineConfirmation_exists_honestVoteSupporter_ceilingOn facts (Setup.alwaysAwake S)
        (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn (hHs _ _ hcut hsigner) hoPos
        hpostVote hconfHor ca hca' hCa'
        (fun z _ hz j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj
          (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hz) hwinR)
    have hyVote : y ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc r))) :=
      hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hy
    obtain ⟨cc, hcc, Tr, hTr, L, hL, L', hL', H, hH⟩ := (p78% exists_voteHead₇₈) facts (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.vote_time S.E ((M.opening_slot S.hc r)))) y)
      ((M.opening_slot S.hc r))
    exact compatible_of_preceq_common_Preceq
      (hSG y hyVote cc hcc Tr hTr L hL L' hL' H hH nu hnu A2 hA2 G hG)
      (preceq_trans_Preceq (preceq_trans_Preceq hTCfg hCfgCa) (hCy cc hcc Tr hTr L hL L' hL' H hH))
  ·
    rw [← hCfgQ] at hoQ
    have hmaj : (S.E.committee ((M.opening_slot S.hc r))).card <
        2 * ((S.E.committee ((M.opening_slot S.hc r))) ∩
          notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc r)))).card :=
      hcomOn ((M.opening_slot S.hc r))
    have hne : ((S.E.committee ((M.opening_slot S.hc r))) ∩
        notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc r)))).Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨y, hyI⟩ := hne
    obtain ⟨-, hy⟩ := Finset.mem_inter.1 hyI
    have hyVote : y ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc r))) :=
      hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hy
    have hyA : y ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc a.round))) := by
      rw [har]
      exact hyVote
    have hCfgy := hreg.seed.selectedSource_preceq_openingHead_of_namedFrame_history facts hf hHs
      hHsXb hX hXXb hreg.crossing hreg.frame hreg.ready hna hoQ hyA hlo
    rw [har] at hCfgy
    obtain ⟨cc, hcc, Tr, hTr, L, hL, L', hL', H, hH⟩ := (p78% exists_voteHead₇₈) facts (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.vote_time S.E ((M.opening_slot S.hc r)))) y)
      ((M.opening_slot S.hc r))
    exact compatible_of_preceq_common_Preceq
      (hSG y hyVote cc hcc Tr hTr L hL L' hL' H hH nu hnu A2 hA2 G hG)
      (preceq_trans_Preceq hTCfg (hCfgy cc hcc Tr hTr L hL L' hL' H hH))

end

end DecoupledConsensusModel.Sts.Restated
