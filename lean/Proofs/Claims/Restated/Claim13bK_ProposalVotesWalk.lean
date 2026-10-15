import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConfirmedInclusion
import Proofs.Claims.Restated.Claim13bK_ConfirmedOld
import Proofs.Claims.Restated.Claim13bK_HolderMargins
import Proofs.Claims.Restated.Claim13bK_LiveConfirmedSlots
import Proofs.Claims.Restated.Claim13bK_ProposalVotesDelivery
import Proofs.Claims.Restated.Claim13bK_ProposalVotesPivot
import Proofs.Claims.Restated.Claim13bK_ProposalVotesTreeFacts
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepKit
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsFacts
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_W4GSTZeroOpeningLifecycle
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_ProposalVotesDelivery
import Model.Conditions.Claim13bK_ProposalVotesPivot
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
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
import Model.Conditions.Sts_VocabularyAssumptions
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ProposalVotesWalk

/-!
# An honest voter votes the honest proposal

The fields of the stores the proposal and vote duties read, and the theorem that every honest active
voter of a slot after the switch round votes the block that slot's honest proposer sent; stated over
a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "pSC% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bStepCone)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pPVD% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ProposalVotesDelivery)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p83w% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The voter's Goldfish head `GV` is the proposal `B`, when: the proposer's and the voter's stores
    both have store slot `s`; both walks start at ancestors of `Y`, and `Y` is an ancestor of the
    proposer's head `P` and of `GV`; every descendant of `Y` has the same Goldfish score at the two
    stores and the two participant counts are equal; both trees are root-injective below; and the
    voter's tree satisfies the height, path and child conditions, its only block of slot `s` being
    `B`, a child of `P` with no child in that tree. -/
theorem voterHead_eq_proposal_of_scores (facts : Record.Facts M) (contractP contractV : M.Contract)
    (E : Env V) (hc : Protocol.HealConfig) (stp : M.HS)
    (stv : M.S) {votesP supportP : Finset (GoldfishVote V)} {s : Slot}
    {Y P B : Block V}
    (hsp : stp.s = s) (hsv : stv.s = s)
    (Tv : Finset (Block V)) (hTv : Restated.voteTreeOf M E stv ⇢ Tv)
    (Wv : Finset (GoldfishVote V)) (hWv : Restated.voteViewOf M E stv ⇢ Wv)
    (Uv : Finset (GoldfishVote V)) (hUv : Restated.voteSupportViewOf M E stv ⇢ Uv)
    (Ap : Block V) (hAp : M.get_sg_root_with contractP E hc stp (M.round_of hc s) ⇢ Ap)
    (Av : Block V) (hAv : Restated.voteAnchorOf M contractV E hc stv ⇢ Av)
    (hP : M.get_head_with contractP E hc stp votesP supportP (s - 1) ⇢ P)
    (scV : Block V → ℕ) (hscV : ∀ C, M.goldfish_score E stv.T Wv Uv (s - 1) C ⇢ scV C)
    (scP : Block V → ℕ) (hscP : ∀ C, M.goldfish_score E stp.T votesP supportP (s - 1) C ⇢ scP C)
    (hscore : ∀ C, Block.Preceq Y C → scV C = scP C)
    (hcount : M.voters_count E Wv (s - 1) = M.voters_count E votesP (s - 1))
    (hrootP : RootInjectiveBelow (M.get_filtered_block_tree stp.toFG))
    (hrootV : RootInjectiveBelow Tv)
    (hApY : Block.Preceq Ap Y)
    (hAvY : Block.Preceq Av Y)
    (hYP : Block.Preceq Y P)
    (GV : Block V) (hGV : M.get_head_in_tree_with contractV E hc stv Tv Wv Uv (stv.s - 1) ⇢ GV)
    (hpasses : Block.Preceq Y GV)
    (hhP : ∀ X, Block.Preceq Y X → Block.Preceq X P → stp.h_max - 1 ≤ (stp.σ X).h)
    (hhV : ∀ X, Block.Preceq Y X → Block.Preceq X P →
      (M.toHealing stv).h_max - 1 ≤ ((M.toHealing stv).σ X).h)
    (hpathV : ∀ C, Block.Preceq Y C → C ≠ Y → Block.Preceq C P → C ∈ Tv)
    (hchildV : ∀ X C, Block.Preceq Y X → Block.Preceq X P → C ∈ Tv →
      C.parent? = some X → C.slot ≠ s → C ∈ M.get_filtered_block_tree stp.toFG)
    (hBonly : ∀ C ∈ Tv, C.slot = s → C = B)
    (hB : B ∈ Tv) (hBpar : B.parent? = some P) (hBslot : B.slot = s)
    (hfresh : ∀ C ∈ Tv, C.parent? ≠ some B) :
    GV = B := by
  have hAp' : M.get_sg_root_with contractP E hc stp
      (M.round_of hc stp.toFG.toSG.toGoldfishStore.s) ⇢ Ap := by
    have e : stp.toFG.toSG.toGoldfishStore.s = s := hsp
    rw [e]; exact hAp
  have hP' := (facts.gr.get_head_with_eq_fork_choice contractP E hc stp votesP supportP (s - 1)
    Ap hAp' P).1 hP
  have e : stp.toFG.toSG.toGoldfishStore.s = s := hsp
  rw [e] at hP'
  have hGV' := (facts.hd.get_head_in_tree_with_eq_fork_choice contractV E hc stv Tv Wv Uv
    (stv.s - 1) Av hAv GV).1 hGV
  rw [hsv] at hGV'
  exact facts.fc.goldfish_fork_choice_eq_child_of_pivot E hrootP hrootV P hP' rfl hApY hAvY hYP
    GV hGV' hpasses hhP hhV scV hscV scP hscP hscore hcount hpathV hchildV hBonly hB hBpar hBslot
    hfresh

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The store slot `s`'s proposal duty reads holds the node's own tree. -/
theorem proposalStoreAt_toHealing_T_g5 (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) :
    (M.toHealing (Restated.proposalStoreAt M S before s)).T = before.st.core.T := by
  exact facts.hd.setClock_toHealing_T S.E before.st _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The store slot `s`'s proposal duty reads records the node's own `h_max`. -/
theorem proposalStoreAt_h_max_g5 (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) :
    (M.toHealing (Restated.proposalStoreAt M S before s)).h_max = before.st.core.h_max := by
  exact facts.hd.setClock_toHealing_h_max S.E before.st _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The store slot `s`'s proposal duty reads records the node's own chain states. -/
theorem proposalStoreAt_σ_g5 (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) :
    (M.toHealing (Restated.proposalStoreAt M S before s)).σ = before.st.core.σ := by
  exact facts.hd.setClock_toHealing_σ S.E before.st _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The store slot `s`'s proposal duty reads holds the node's own finalized block. -/
theorem proposalStoreAt_F_g5 (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) :
    (M.toHealing (Restated.proposalStoreAt M S before s)).F = before.st.core.F := by
  exact facts.hd.setClock_toHealing_F S.E before.st _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The store slot `s`'s proposal duty reads holds the node's own justified block. -/
theorem proposalStoreAt_J_g5 (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) :
    (M.toHealing (Restated.proposalStoreAt M S before s)).J = before.st.core.J := by
  exact facts.hd.setClock_toHealing_J S.E before.st _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The store slot `s`'s vote duty reads records the node's own `h_max`. -/
theorem voteStoreAt_h_max_g5 (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) :
    (M.toHealing (Restated.voteStoreAt M S before s)).h_max = before.st.core.h_max := by
  exact facts.hd.setClock_toHealing_h_max S.E before.st _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The store slot `s`'s vote duty reads records the node's own chain states. -/
theorem voteStoreAt_σ_g5 (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) :
    (M.toHealing (Restated.voteStoreAt M S before s)).σ = before.st.core.σ := by
  exact facts.hd.setClock_toHealing_σ S.E before.st _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The store slot `s`'s vote duty reads holds the node's own finalized block. -/
theorem voteStoreAt_F_g5 (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) :
    (M.toHealing (Restated.voteStoreAt M S before s)).F = before.st.core.F := by
  exact facts.hd.setClock_toHealing_F S.E before.st _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The store slot `s`'s vote duty reads holds the node's own justified block. -/
theorem voteStoreAt_J_g5 (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) :
    (M.toHealing (Restated.voteStoreAt M S before s)).J = before.st.core.J := by
  exact facts.hd.setClock_toHealing_J S.E before.st _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The fork-choice root of a healing store is an ancestor of every SG root a duty read through the
    grade contract of `c` can start from. -/
theorem fgRoot_preceq_sgRoot_g5 (facts : Record.Facts M) (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig)
    (st : M.HS) (r : Round) :
    ∀ A : Block V, M.get_sg_root_with (M.gradeContract c) E hc st r ⇢ A →
      Block.Preceq (M.get_fg_root st.toFG) A := by
  intro A hA
  exact Restated.Vocabulary.Proofs.w4_fgRoot_preceq_anchor facts E hc st r _ A
    ((facts.nd.gradeContract_sgRoot_eq_frameAnchor c E hc st r A).1 hA)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `exists_anchor_atSlot` with one conjunct more: at every step whose instant is at or before `s`'s
    vote instant, every validator honest through it records, for every block `X` it holds that is a
    descendant of `T`, a chain-state height of `X` at least its `h_max` minus one. -/
theorem exists_anchor_atSlot_heights (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
    {s : Slot} (hslot : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ s) :
    ∃ T : NamedBlock V,
      Restated.HeadsBelow M S Sched x T.erase (s - 1) ∧
      (∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → (x[n₁].time : Int) ≤ M.vote_time S.E s →
        Restated.HonestThrough M Sched x n₁ v →
        Block.Preceq (x[n₁][v].st).st.core.F T.erase ∧
          Block.Preceq (x[n₁][v].st).st.core.J T.erase) ∧
      (∀ (v : V) (n₁ : Nat) (X : Block V), (x[n₁].time : Int) ≤ M.vote_time S.E s →
        Restated.HonestThrough M Sched x n₁ v → X ∈ (x[n₁][v].st).st.core.T → Block.Preceq T.erase X →
        (x[n₁][v].st).st.core.h_max - 1 ≤ ((x[n₁][v].st).st.core.σ X).h) := by
  have hR3 := S.hc.R_ge_three
  -- the height margin at a held descendant of the anchor
  have hmargin : ∀ {ρ : Round} {nρ : Nat} {Tρ : NamedBlock V},
      Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x ρ nρ Tρ →
      (∀ (v : V) (n₁ : Nat), (x[n₁].time : Int) ≤ M.vote_time S.E s →
        (x[n₁][v].st).st.core.h_max ≤ (M.derive_named S.E S.cfg Tρ).h + 1) →
      ∀ (v : V) (n₁ : Nat) (X : Block V), (x[n₁].time : Int) ≤ M.vote_time S.E s →
        Restated.HonestThrough M Sched x n₁ v → X ∈ (x[n₁][v].st).st.core.T → Block.Preceq Tρ.erase X →
        (x[n₁][v].st).st.core.h_max - 1 ≤ ((x[n₁][v].st).st.core.σ X).h := by
    intro ρ nρ Tρ hTop hmax v n₁ X h1 hv hX hTX
    obtain ⟨D, hD, hDe⟩ := Restated.exists_named_of_mem_tree facts S Sched x n₁ v hX
    have hco : Restated.Vocabulary.Proofs.NamedStore.Coherent M (Setup.alwaysAwake S).E (Setup.alwaysAwake S).cfg
        (x[n₁][v].st).st := (Restated.nodeInvariant_sts facts S Sched x n₁ v).1.1.1
    have hσ : (x[n₁][v].st).st.core.σ D.erase = M.derive_named S.E S.cfg D :=
      hco.2.2.2.2 D hD
    have hTD : Block.Preceq Tρ.erase D.erase := by rw [hDe]; exact hTX
    have hh := Restated.derive_height_le_of_anchor_preceq facts S Sched x hexec hTop
      (Restated.blockInLog_of_mem_bodies facts S Sched hv hD) hTD
    have hm := Nat.sub_le_sub_right (hmax v n₁ h1) 1
    rw [Nat.add_sub_cancel] at hm
    rw [← hDe, hσ]
    exact le_trans hm hh
  set r := (M.round_of S.hc s) with hr_def
  have hr : Restated.switchRound M S tE + 1 ≤ r := Restated.succ_le_round_of_g1 facts S hslot
  have hr0 : (M.opening_slot S.hc r) ≤ s := facts.gr.opening_slot_round_of_le_slot S.hc s
  have hr1 : s < (M.opening_slot S.hc (r + 1)) := facts.gr.lt_opening_slot_round_of_succ S.hc s
  have hchain := Restated.exists_anchor_chain_secondSlot_withoutCatchUp_i1 facts S Sched x tE hexec hmono htd
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW
    hAW hJswitch le_rfl hTW₀ hJ₀
  by_cases hA : (M.opening_slot S.hc r) + 2 ≤ s
  · -- `T` is the round-`r` anchor
    have hle : Restated.switchRound M S tE ≤ r := le_trans (Nat.le_succ _) hr
    obtain ⟨n_k, T_k, hJk, hWk, h2k⟩ := hchain (r - Restated.switchRound M S tE)
    rw [Nat.add_sub_cancel' hle] at hJk h2k
    have hheads : Restated.HeadsBelow M S Sched x T_k.erase (s - 1) := by
      rcases nat_pred_cases_g1 hA with h | h
      · exact Restated.headsBelow_range_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
          hthird hphase hrsW hmult hcv hcs hcom hw hrec hprev hclear hB' hnW hAW hle hWk hJk
          (s - 1) h (nat_pred_le_g1 hr1)
      · rw [h]
        rcases nat_sub_pos_or_eq_g1 hle with hpos | heq
        · exact h2k hpos
        · exact absurd (heq ▸ hr) (Nat.not_succ_le_self _)
    obtain ⟨hmax, hFJ⟩ := Restated.anchorBounds_of_joint facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst
      hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
      hJswitch hle hWk hJk (Restated.vote_time_le_action_sub_one_g1 facts S (nat_le_succ_of_lt_g1 hr1))
    exact ⟨T_k, hheads, hFJ, hmargin hJk.toTop hmax⟩
  · -- `s` is `o_r` or `o_r + 1`: `T` is the round-`(r − 1)` anchor
    obtain ⟨ρ, hρ⟩ : ∃ ρ : Round, r = ρ + 1 := ⟨r - 1, (Nat.succ_pred_eq_of_pos
      (lt_of_lt_of_le (Nat.succ_pos _) hr)).symm⟩
    rw [hρ] at hr hr0 hA
    have hle : Restated.switchRound M S tE ≤ ρ := Nat.le_of_succ_le_succ hr
    have hsucc := facts.gr.opening_slot_succ S.hc ρ
    rw [hsucc] at hr0 hA
    obtain ⟨h0, h1, h2⟩ := nat_firstSlots_g1 hR3 hr0 hA
    obtain ⟨n_k, T_k, hJk, hWk, -⟩ := hchain (ρ - Restated.switchRound M S tE)
    rw [Nat.add_sub_cancel' hle] at hJk
    have hheads : Restated.HeadsBelow M S Sched x T_k.erase (s - 1) :=
      Restated.headsBelow_range_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync hthird
        hphase hrsW hmult hcv hcs hcom hw hrec hprev hclear hB' hnW hAW hle hWk hJk (s - 1) h0
        (by rw [hsucc]; exact h1)
    obtain ⟨hmax, hFJ⟩ := Restated.anchorBounds_of_joint facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst
      hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
      hJswitch hle hWk hJk (Restated.vote_time_le_action_sub_one_g1 facts S (s := s) (by rw [hsucc]; exact h2))
    exact ⟨T_k, hheads, hFJ, hmargin hJk.toTop hmax⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The voter's Goldfish head read on a core store with a grade cache written in is the head read on
    the store's own core store. -/
private theorem gfHeadWith_store_with_cache_pvw (facts : Record.Facts M) {contract : M.Contract} {E : Env V}
    {hc : Protocol.HealConfig} {X : M.NS} {c : M.Cache} :
    Restated.gfHeadWith M contract E hc (M.store_with_cache X c).core =
      Restated.gfHeadWith M contract E hc X.core := by
  unfold Restated.gfHeadWith Restated.voteTreeOf Restated.voteViewOf Restated.voteSupportViewOf
  simp only [facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_voter_filtered_block_tree,
    facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view,
    facts.nd.store_with_cache_get_head_in_tree_with]

/-- Under the run's premises and the joint invariant at the switch round, for a slot `s` at or after
    round `rW + 1`'s opening slot whose proposer is honest through `s`'s vote instant and awake at
    its proposal instant, and a block `B'` the proposer can send at that proposal: every head a
    member `v` of `HonSlot S Sched s` can select at its slot-`s` vote is `B'`'s erasure. -/
theorem voterHead_eq_proposal_afterPhase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
    {s : Slot} (hslot : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ s)
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    (hawp : S.E.proposer s ∈ Sched.awake (M.proposal_time S.E s))
    {k : Nat} (hk : Restated.tickStepAt M x k (M.proposal_time S.E s))
    {B' : NamedBlock V}
    (hemit : ∃ out : M.N × List (NamedObject V), M.tick (Setup.alwaysAwake S) (S.E.proposer s)
        (Record.wakeStage M Sched (M.proposal_time S.E s) x[k] (S.E.proposer s))
        (M.proposal_time S.E s) ⇢ out ∧ NamedObject.block B' ∈ out.2)
    {n : M.N} (hn : Restated.proposalReadOf M S (x[k][S.E.proposer s].st) s ⇢ n)
    {D : M.NS × Option (NamedBlock V)}
    (hD : M.duties_propose_block_with (M.gradeContract n.cache)
        S.E S.hc S.cfg ((Setup.alwaysAwake S).node (S.E.proposer s)) (M.ns_setClock S.E (x[k][S.E.proposer s].st).st (M.proposal_time S.E s)) ⇢ D)
    (hduty : D.2 = some B')
    {v : V} (hv : v ∈ Restated.HonSlot M S Sched s) {mr : Nat}
    (hmr : Restated.tickStepAt M x mr (M.vote_time S.E s)) :
    ∀ G : Block V, Restated.gfHeadFrom M S (x[mr][v].st) s ⇢ G → G = B'.erase := by
  have _hr_0 : M.reachedNode (x[k][S.E.proposer s].st) := Record.reachedNode_sts facts S Sched x k (S.E.proposer s)
  have _hr_1 : M.reachedNode (x[mr][v].st) := Record.reachedNode_sts facts S Sched x mr v
  intro G hG
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := by
    simpa only [zero_add] using Int.add_one_le_iff.mpr S.E.Δ_pos
  have hR3 := S.hc.R_ge_three
  have hs2 := Restated.two_le_slot_g2 facts S tE hslot
  have hts := Restated.proposal_time_closed_g1 facts S s
  have hvt := Restated.vote_time_closed_g1 facts S s
  have hpv := Restated.proposal_time_le_vote_time_g1 facts S s
  have hct : ∀ s' : Slot, M.confirmation_time S.E s' = 4 * S.E.Δ * (s' : Int) + 6 * S.E.Δ :=
    fun s' => (pPVD% confirmation_time_closed_pvd) facts S.E s'
  have hs1 : ((s - 1 : Nat) : Int) = (s : Int) - 1 := nat_sub_one_cast_g2 (le_trans (by decide) hs2)
  obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hk
  obtain ⟨hmr1, hmr0⟩ := Restated.tickStepAt_time facts x hmr
  have hpk : Restated.HonestThrough M Sched x k (S.E.proposer s) := fun t ht => hprop t (by linarith)
  have hvmr : Restated.HonestThrough M Sched x mr v :=
    Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hv (by
      rw [hct s]; rw [hvt] at hmr0; linarith)
  -- the fields of the two duty stores
  have ePT : (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)).toFG.toSG.toGoldfishStore.T = (x[k][S.E.proposer s].st).st.core.T :=
    Restated.proposalStoreAt_toHealing_T_g5 facts S _ s
  have ePF : (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)).toFG.F = (x[k][S.E.proposer s].st).st.core.F :=
    Restated.proposalStoreAt_F_g5 facts S _ s
  have ePJ : (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)).toFG.J = (x[k][S.E.proposer s].st).st.core.J :=
    Restated.proposalStoreAt_J_g5 facts S _ s
  have ePh : (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)).toFG.h_max = (x[k][S.E.proposer s].st).st.core.h_max :=
    Restated.proposalStoreAt_h_max_g5 facts S _ s
  have ePσ : (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)).toFG.σ = (x[k][S.E.proposer s].st).st.core.σ :=
    Restated.proposalStoreAt_σ_g5 facts S _ s
  have eVF : (M.toHealing (Restated.voteStoreAt M S (x[mr][v].st) s)).toFG.F = (x[mr][v].st).st.core.F :=
    Restated.voteStoreAt_F_g5 facts S _ s
  have eVJ : (M.toHealing (Restated.voteStoreAt M S (x[mr][v].st) s)).toFG.J = (x[mr][v].st).st.core.J :=
    Restated.voteStoreAt_J_g5 facts S _ s
  have eVh : (M.toHealing (Restated.voteStoreAt M S (x[mr][v].st) s)).toFG.h_max = (x[mr][v].st).st.core.h_max :=
    Restated.voteStoreAt_h_max_g5 facts S _ s
  have eVσ : (M.toHealing (Restated.voteStoreAt M S (x[mr][v].st) s)).toFG.σ = (x[mr][v].st).st.core.σ :=
    Restated.voteStoreAt_σ_g5 facts S _ s
  -- steps after the switch round's tick step
  have hWafter : ∀ n : Nat, M.proposal_time S.E s ≤ (x[n + 1].time : Int) → n_W ≤ n := by
    intro n hn
    have hlt : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) < M.proposal_time S.E s :=
      Restated.action_lt_proposal_time_g1 facts S hslot
    by_contra hcon
    have hle : n + 1 ≤ n_W := Nat.lt_of_not_le hcon
    have h1 := Restated.time_mono_int facts S Sched x hle
    have h2 := (Restated.tickStepAt_time facts x hnW).2
    linarith
  have hWk : n_W ≤ k := hWafter k (by linarith)
  have hWmr : n_W ≤ mr := hWafter mr (by linarith)
  -- the voter's head `G`, taken apart: the vote read `nv`, the tree `Tv`, the views `Wv`, `Uv`
  have hG0 := hG
  unfold Restated.gfHeadFrom at hG
  obtain ⟨nv, hnv, hG⟩ := ((pSC% returns_bind_iff_cone) _ _ _).1 hG
  obtain ⟨cv, -, hnveq⟩ := (pSC% voteReadOf_cases) S (x[mr][v].st) s hnv
  have hnvst : nv.st = M.store_with_cache (M.ns_setClock S.E (x[mr][v].st).st (M.vote_time S.E s)) cv := by rw [hnveq]; exact facts.nd.mkNode_st _ _ _
  rw [hnvst, gfHeadWith_store_with_cache_pvw facts] at hG
  try rw [← (show (M.ns_setClock S.E (x[mr][v].st).st (M.vote_time S.E s)).core = Restated.voteStoreAt M S (x[mr][v].st) s from rfl)] at hG
  obtain ⟨Tv, hTv, Wv, hWv, Uv, hUv, hGV⟩ := (pSC% gfHeadWith_cases) _ _ _ _ hG
  -- one outcome of the proposer's support view, of its head and of the two starts
  obtain ⟨L, hL⟩ := facts.fc.proposer_support_view_nonempty
    (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)).toFG.toSG.toGoldfishStore s
  have hUp : Restated.proposerSupportOf M S (x[k][S.E.proposer s].st) s ⇢ L.toFinset := by
    unfold Restated.proposerSupportOf
    exact (pSC% returns_map_intro_cone) (fun L : List (GoldfishVote V) => L.toFinset) _ L hL
  obtain ⟨P, hP⟩ := facts.fc.get_head_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s))
    (Restated.proposerVotesOf M S (x[k][S.E.proposer s].st) s) L.toFinset (s - 1)
  obtain ⟨Ap, hAp⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)) (M.round_of S.hc s)
  obtain ⟨Av, hAv⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract nv.cache) S.E S.hc
    (M.toHealing (Restated.voteStoreAt M S (x[mr][v].st) s))
    (M.round_of S.hc (Restated.voteStoreAt M S (x[mr][v].st) s).s)
  have hAv' : Restated.voteAnchorOf M (M.gradeContract nv.cache) S.E S.hc
      (Restated.voteStoreAt M S (x[mr][v].st) s) ⇢ Av := hAv
  -- the anchor `T`
  obtain ⟨T, hHT, hFJ, hheight⟩ := Restated.exists_anchor_atSlot_heights facts S Sched x tE hexec hmono htd
    hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear
    hB' hnW hAW hJswitch hTW₀ hJ₀ hslot
  -- the two starts
  have hHAp := Restated.proposalStart_headsBelow facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen
    hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW hJswitch hTW₀
    hJ₀ hslot hprop hawp hk n hn Ap hAp
  have hHAv := Restated.voteStart_headsBelow facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen hsync
    hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW hJswitch hTW₀ hJ₀
    hslot hv hmr nv hnv Av hAv'
  -- the committee majority at slot `s − 1`, and one honest active member there
  have hsucc := facts.gr.opening_slot_succ S.hc (Restated.switchRound M S tE)
  obtain ⟨t', -, ht's, -, hcs'⟩ :=
    Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs
      (r := Restated.switchRound M S tE) le_rfl
  have hss1 : s - 1 + 1 = s := Nat.sub_add_cancel (le_trans (by decide) hs2)
  have hanchor : t' ≤ slotStart S.E.Δ (s - 1 + 1) := by
    rw [hss1]
    refine le_trans ht's (slotStart_mono S ?_)
    exact (nat_opening_le_g5 hR3 (hsucc ▸ hslot)).1
  have hmaj := Restated.majority_of_committeeSleepinessW facts S Sched hcs' hanchor
  obtain ⟨v₁, hv₁⟩ : ∃ v₁, v₁ ∈ Restated.HonSlot M S Sched (s - 1) := by
    have hpos : 0 < ((S.E.committee (s - 1)) ∩ Restated.HonSlot M S Sched (s - 1)).card := by omega
    obtain ⟨v₁, hv₁⟩ := Finset.card_pos.mp hpos
    exact ⟨v₁, (Finset.mem_inter.mp hv₁).2⟩
  have hvt1 : M.vote_time S.E (s - 1) = M.proposal_time S.E s - 3 * S.E.Δ := by
    rw [Restated.vote_time_closed_g1 facts S, hs1, hts]; ring
  obtain ⟨m₁, hm₁⟩ := Restated.exists_tickStepAt facts x htd (t := M.vote_time S.E (s - 1)) (by
    have h0 : (0 : Int) ≤ (s : Int) := by positivity
    rw [Restated.vote_time_closed_g1 facts S]
    nlinarith)
  -- one head of each honest active member of slot `s − 1`, and the vote it makes
  have hheadNE : ∀ q : V, ∃ H : Block V, Restated.gfHeadFrom M S (x[m₁][q].st) (s - 1) ⇢ H := by
    intro q
    obtain ⟨u, hu⟩ := (pSC% gfVoteFrom_nonempty) facts S (x[m₁][q].st) q (s - 1)
    unfold Restated.gfVoteFrom at hu
    obtain ⟨H, hH, -⟩ := (pSC% returns_map_elim_cone) _ _ u hu
    exact ⟨H, hH⟩
  have hvoteOf : ∀ (q : V) (H : Block V), Restated.gfHeadFrom M S (x[m₁][q].st) (s - 1) ⇢ H →
      Restated.gfVoteFrom M S (x[m₁][q].st) q (s - 1) ⇢ (⟨q, s - 1, H.root⟩ : GoldfishVote V) := by
    intro q H hH
    unfold Restated.gfVoteFrom
    exact (pSC% returns_map_intro_cone) (fun H : Block V => (⟨q, s - 1, H.root⟩ : GoldfishVote V)) _ H hH
  obtain ⟨G₁, hG₁⟩ := hheadNE v₁
  -- `Y`, the deepest of `T` and the two starts
  have hHmax : ∀ {X : Block V}, Restated.HeadsBelow M S Sched x X (s - 1) → Block.Preceq X G₁ :=
    fun h => h v₁ m₁ hv₁ hm₁ G₁ hG₁
  obtain ⟨Y, hTY, hApY, hAvY, hYcases⟩ := exists_deepest_of_three (hHmax hHT) (hHmax hHAp)
    (hHmax hHAv)
  have hHY : Restated.HeadsBelow M S Sched x Y (s - 1) := by
    rcases hYcases with rfl | rfl | rfl
    · exact hHT
    · exact hHAp
    · exact hHAv
  have hFY : Restated.FinalizedBelowUpTo M S Sched x n_W (M.vote_time S.E s) Y :=
    Restated.finalizedBelowUpTo_mono facts (fun w n₁ hW h1 hh => (hFJ w n₁ hW h1 hh).1) hTY
  -- the voter's walk passes through `Y`
  have hs0 : (M.opening_slot S.hc (Restated.switchRound M S tE)) + 2 ≤ s - 1 :=
    (nat_opening_le_g5 hR3 (hsucc ▸ hslot)).2
  have hYs : Restated.HeadsBelow M S Sched x Y s :=
    Restated.ancestorOfHonestHeadsFrom_of_headsBelow_i1 facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
      hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW hJswitch
      le_rfl hTW₀ hJ₀ hs0 hHY s (Nat.sub_le s 1)
  have hpasses : Block.Preceq Y G := hYs v mr hv hmr G hG0
  -- the proposal's fields
  obtain ⟨hBslot', -, -, hBpar', hBparMem, -, -⟩ :=
    Restated.proposalDuty_fields facts S (x[k][S.E.proposer s].st) s _ hn hD hduty
  have hBslot : B'.erase.slot = s := hBslot'
  have hBparP : B'.erase.parent = P := hBpar' _ hUp P hP
  have hBne : B'.erase ≠ Block.genesis :=
    ne_genesis_of_slot_pos (by rw [hBslot]; exact lt_of_lt_of_le (by decide) hs2)
  have hBpar : B'.erase.parent? = some P := by
    rw [parent?_eq_some_parent_of_ne_genesis hBne, hBparP]
  have hPT : P ∈ (x[k][S.E.proposer s].st).st.core.T := by
    rw [← hBparP, Proofs.NamedWire.erase_parent, Restated.bodies_image_eq_T facts S Sched x k]
    exact Finset.mem_image_of_mem NamedBlock.erase hBparMem
  -- the proposer's walk passes through `Y`
  have hprev₁ := fun (q : V) (hq : q ∈ Restated.HonSlot M S Sched (s - 1)) (H : Block V)
      (hH : Restated.gfHeadFrom M S (x[m₁][q].st) (s - 1) ⇢ H) =>
    Restated.prevVotes_at_proposalStore facts S Sched x tE hexec hmono htd
      hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev
      hclear hB' hnW hAW hJswitch hTW₀ hJ₀ hslot hawp (fun t ht => hprop t (by linarith)) hk
      hm₁ hq _ (hvoteOf q H hH) H hH
  have hcone : Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E
      (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)).T
      (Restated.proposerVotesOf M S (x[k][S.E.proposer s].st) s)
      L.toFinset
      (Restated.proposerVotesOf M S (x[k][S.E.proposer s].st) s) (s - 1) (Restated.HonSlot M S Sched (s - 1))
      (fun X => Block.Preceq Y X) := by
    refine Restated.Vocabulary.Proofs.Optimistic.coneSupport_of_named_votes facts hmaj (Finset.Subset.refl _) ?_ ?_ ?_
    · intro u hu
      rw [Restated.proposerVotesOf_eq facts]
      exact (Restated.mem_proposerSupportOf facts S _ s hUp hu).1
    · intro q _ hq
      rw [Restated.proposerVotesOf_eq facts]
      exact Restated.no_equiv_of_honest facts S Sched x hexec
        (Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hq (by
          rw [hct (s - 1), hs1]; linarith)) (s - 1)
    · intro q _ hq
      obtain ⟨H, hH⟩ := hheadNE q
      obtain ⟨hpool, hfind, hXs, -⟩ := hprev₁ q hq H hH
      rw [Restated.proposalStoreAt_pool facts] at hpool
      rw [Restated.proposalStoreAt_T facts] at hfind
      refine ⟨H, hHY q m₁ hq hm₁ H hH, hXs, ?_, ?_⟩
      · obtain ⟨b, hb⟩ := facts.sto.resolved_nonempty (x[k][S.E.proposer s].st).st.core.T
          (⟨q, s - 1, H.root⟩ : GoldfishVote V)
        have hbt : b = true :=
          (facts.sto.resolved_eq_true_iff _ _ b hb).2 ⟨_, hfind, hXs⟩
        rw [hbt] at hb
        exact Restated.mem_proposerSupportOf_of facts S _ s hpool hb _ hUp
      · rw [Restated.proposalStoreAt_toHealing_T_g5 facts]
        exact hfind
  have hvalid : Protocol.VoteSetValid S.E (s - 1)
      (Restated.proposerVotesOf M S (x[k][S.E.proposer s].st) s) := by
    intro u hu
    rw [Restated.proposerVotesOf_eq facts] at hu
    have hslotu : u.slot = s - 1 := Restated.slot_of_mem_pool_sts facts S Sched x k _ hu
    have hpool' : u ∈ (M.store_pool (x[k][S.E.proposer s].st).st.core u.slot) := by rw [hslotu]; exact hu
    obtain ⟨j, -, -, h0, h1⟩ := Restated.accepts_of_mem_pool facts S Sched x hpool'
    have hcomm := (Restated.stamp_eq_clock_of_flip_gfVote facts S Sched x h0 h1).2.2
    rw [hslotu] at hcomm
    exact ⟨hslotu, hcomm⟩
  -- the head `G₁` of the member `v₁`, a viability witness in the proposer's tree
  obtain ⟨-, hfind₁, -, -⟩ := hprev₁ v₁ hv₁ G₁ hG₁
  have hX₁T : G₁ ∈ (x[k][S.E.proposer s].st).st.core.T := by
    rw [← Restated.proposalStoreAt_T facts S _ s]; exact Proofs.HealingLemmas.find?_mem hfind₁
  have hFp : Block.Preceq (x[k][S.E.proposer s].st).st.core.F T.erase :=
    (hFJ _ k hWk (by linarith) hpk).1
  have hJp : Block.Preceq (x[k][S.E.proposer s].st).st.core.J T.erase :=
    (hFJ _ k hWk (by linarith) hpk).2
  have hrootp : Block.Preceq
      (M.get_fg_root (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)).toFG)
      T.erase := by
    refine facts.fc.fgRoot_preceq ?_ ?_
    · rw [ePF]; exact hFp
    · rw [ePJ]; exact hJp
  have hrootAp := Restated.fgRoot_preceq_sgRoot_g5 facts n.cache S.E S.hc
    (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)) (M.round_of S.hc s) Ap hAp
  have hFrootp : Block.Preceq (x[k][S.E.proposer s].st).st.core.F
      (M.get_fg_root (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)).toFG) := by
    have h := facts.fc.preceq_get_fg_root_of_F
      (st := (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)).toFG) (by
        refine preceq_eq_true_iff_Preceq.mpr ?_
        show Block.Preceq (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)).F
          (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)).J
        rw [Restated.proposalStoreAt_F_g5 facts, Restated.proposalStoreAt_J_g5 facts]
        exact Restated.F_preceq_J_sts facts S Sched x k _)
    have e : (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)).toFG.F
        = (x[k][S.E.proposer s].st).st.core.F := ePF
    rw [e] at h
    exact preceq_eq_true_iff_Preceq.mp h
  -- membership in the proposer's candidate tree
  have hinP : ∀ C W : Block V, C ∈ (x[k][S.E.proposer s].st).st.core.T →
      Block.Preceq (x[k][S.E.proposer s].st).st.core.F C →
      Block.Preceq (M.get_fg_root
        (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)).toFG) C →
      W ∈ (x[k][S.E.proposer s].st).st.core.T → Block.Preceq C W → Block.Preceq T.erase W →
      C ∈ M.get_filtered_block_tree
        (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)).toFG := by
    intro C W hC hF hroot hW hCW hTW
    refine facts.fc.mem_get_filtered_block_tree_of_parts _ ?_ ?_ ?_ hCW ?_ hroot
    · rw [ePT]; exact hC
    · rw [ePF]; exact hF
    · rw [ePT]; exact hW
    · rw [ePh, ePσ]
      exact hheight _ k W (by linarith) hpk hW hTW
  have hslotp : (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)).s = s := by
    exact (facts.sto.toHealing_slot _).trans (Restated.proposalStoreAt_s facts S _ s)
  have hYP : Block.Preceq Y P := by
    have hAp' : M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s))
        (M.round_of S.hc
          (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)).toFG.toSG.toGoldfishStore.s)
        ⇢ Ap := by
      have e : (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st)
          s)).toFG.toSG.toGoldfishStore.s = s := hslotp
      rw [e]; exact hAp
    have hP' := (facts.gr.get_head_with_eq_fork_choice (M.gradeContract n.cache) S.E S.hc
      (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s))
      (Restated.proposerVotesOf M S (x[k][S.E.proposer s].st) s) L.toFinset (s - 1) Ap hAp' P).1 hP
    refine facts.fc.goldfish_passes_cone S.E _ _ _ _ _ _ _ _ _ hcone.majority hcone.counted
      hcone.sub hcone.no_equiv hcone.vote hvalid hApY ?_ P hP'
    intro C hAC _ hCY
    have hCX₁ : Block.Preceq C G₁ := preceq_trans_Preceq hCY (hHY v₁ m₁ hv₁ hm₁ G₁ hG₁)
    have hrootC := preceq_trans_Preceq hrootAp hAC
    exact hinP C _ (Restated.mem_T_of_preceq_sts facts S Sched x k _ hX₁T hCX₁)
      (preceq_trans_Preceq hFrootp hrootC) hrootC hX₁T hCX₁ (hHT v₁ m₁ hv₁ hm₁ G₁ hG₁)
  have hPB : Block.Preceq P B'.erase :=
    preceq_eq_true_iff_Preceq.mp (Protocol.preceq_of_parent? hBpar)
  have hYB : Block.Preceq Y B'.erase := preceq_trans_Preceq hYP hPB
  -- the voter's side
  obtain ⟨hBv, hUnique⟩ := Restated.proposal_in_voterTree_unique facts S Sched x tE hexec hmono htd hcatch tGAT
    gap hgst hlen hsync hthird hphase hmult hcv hcs hw hnW hslot hprop hawp hk hemit hn hD hduty hv hmr
    hFY hYB
  have hFv : Block.Preceq (x[mr][v].st).st.core.F T.erase :=
    (hFJ v mr hWmr (by linarith) hvmr).1
  have hJv : Block.Preceq (x[mr][v].st).st.core.J T.erase :=
    (hFJ v mr hWmr (by linarith) hvmr).2
  -- one outcome of the voter's processed-block view; it holds every ancestor of the proposal
  obtain ⟨Pr, hPr⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
    (M.toHealing (Restated.voteStoreAt M S (x[mr][v].st) s)).toFG.toSG.toGoldfishStore
    (Restated.voteStoreAt M S (x[mr][v].st) s).s
  have hprocV : ∀ C : Block V, C ∈ (x[mr][v].st).st.core.T → Block.Preceq C B'.erase → C ∈ Pr := by
    intro C hC hCB
    refine facts.fc.mem_voter_processed_block_tree_of_proposal S.E _ _ ?_ ?_ ?_ hCB Pr hPr
    · rw [facts.sto.toHealing_gs_T, Restated.voteStoreAt_T facts]; exact hC
    · rw [facts.sto.toHealing_gs_T, Restated.voteStoreAt_T facts]; exact hBv
    · rw [Restated.voteStoreAt_slot facts]; exact hBslot
  have hBB : Block.Preceq B'.erase B'.erase := preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)
  have hinV : ∀ C, Block.Preceq Y C → Block.Preceq C B'.erase → C ∈ Tv := by
    intro C hYC hCB
    refine facts.hd.mem_voter_filtered_block_tree_of_parts S.E _ _ Pr hPr
      (hprocV C (Restated.mem_T_of_preceq_sts facts S Sched x mr v hBv hCB) hCB) ?_
      (hprocV _ hBv hBB) hCB ?_ ?_ Tv hTv
    · rw [← facts.sto.Sts_toHealing_F, eVF]
      exact preceq_trans_Preceq hFv (preceq_trans_Preceq hTY hYC)
    · rw [← facts.sto.Sts_toHealing_h_max, ← facts.sto.Sts_toHealing_σ,
        eVh, eVσ]
      exact hheight v mr _ (by linarith) hvmr hBv (preceq_trans_Preceq hTY hYB)
    · refine preceq_trans_Preceq (facts.fc.fgRoot_preceq ?_ ?_) (preceq_trans_Preceq hTY hYC)
      · rw [eVF]; exact hFv
      · rw [eVJ]; exact hJv
  -- equal scores and counts, for one outcome of each score
  have hsc := fun (C : Block V) (hYC : Block.Preceq Y C) =>
    Restated.score_eq_at_proposal_and_vote facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen hsync
      hthird hphase hmult hcv hcs hw hnW hslot hprop hawp hk hemit hn hD hduty hv hmr hFY hYB hYC
      Wv hWv Uv hUv L.toFinset hUp
  choose scV hscV using fun C : Block V => facts.fc.goldfish_score_nonempty S.E
    (Restated.voteStoreAt M S (x[mr][v].st) s).T Wv Uv (s - 1) C
  choose scP hscP using fun C : Block V => facts.fc.goldfish_score_nonempty S.E
    (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s).T
    (Restated.proposerVotesOf M S (x[k][S.E.proposer s].st) s) L.toFinset (s - 1) C
  refine Restated.voterHead_eq_proposal_of_scores facts
    (M.gradeContract n.cache) (M.gradeContract nv.cache) S.E S.hc
    (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s))
    (Restated.voteStoreAt M S (x[mr][v].st) s)
    (votesP := Restated.proposerVotesOf M S (x[k][S.E.proposer s].st) s)
    (supportP := L.toFinset) (Y := Y) (P := P)
    hslotp (Restated.voteStoreAt_slot facts S _ s) Tv hTv Wv hWv Uv hUv Ap hAp Av hAv' hP
    scV hscV scP (fun C => by
      have e : (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s)).T = (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s).T := facts.sto.toHealing_gs_T _
      rw [e]; exact hscP C)
    (fun C hYC => (hsc C hYC).1 _ (hscV C) _ (hscP C))
    (hsc Y (preceq_eq_true_iff_Preceq.mp (Block.preceq_self Y))).2
    (Restated.rootInjectiveBelow_proposalTree facts S Sched x hexec hprop hk)
    (Restated.rootInjectiveBelow_voteTree facts S Sched x hexec hmono hv hmr Tv hTv) hApY hAvY hYP
    G hGV hpasses ?_ ?_ ?_ ?_ ?_ ?_ hBpar hBslot
    (Restated.voteTree_no_child_of_slot facts S Sched x hmr v hBslot Tv hTv)
  · -- `hhP`
    intro X hYX hXP
    rw [Restated.proposalStoreAt_h_max_g5 facts, Restated.proposalStoreAt_σ_g5 facts]
    exact hheight _ k X (by linarith) hpk (Restated.mem_T_of_preceq_sts facts S Sched x k _ hPT hXP)
      (preceq_trans_Preceq hTY hYX)
  · -- `hhV`
    intro X hYX hXP
    rw [Restated.voteStoreAt_h_max_g5 facts, Restated.voteStoreAt_σ_g5 facts]
    have hXB := preceq_trans_Preceq hXP hPB
    exact hheight v mr X (by linarith) hvmr (Restated.mem_T_of_preceq_sts facts S Sched x mr v hBv hXB)
      (preceq_trans_Preceq hTY hYX)
  · -- `hpathV`
    intro C hYC _ hCP
    exact hinV C hYC (preceq_trans_Preceq hCP hPB)
  · -- `hchildV`
    intro X C hYX hXP hC hpar hCs
    have hXC : Block.Preceq X C := preceq_eq_true_iff_Preceq.mp (Protocol.preceq_of_parent? hpar)
    have hYC : Block.Preceq Y C := preceq_trans_Preceq hYX hXC
    have hCTp : C ∈ (x[k][S.E.proposer s].st).st.core.T := by
      obtain ⟨hCPr, -⟩ := facts.hd.voter_filtered_block_tree_cases S.E _ _ Tv hTv hC Pr hPr
      obtain ⟨hCT, hcase⟩ := facts.fc.voter_processed_block_tree_cases S.E _ _ Pr hPr hCPr
      rw [facts.sto.toHealing_gs_T, Restated.voteStoreAt_T facts] at hCT
      rcases hcase with hst | ⟨P', hP'T, hP's, hCP'⟩
      · rw [facts.sto.toHealing_gs_timestamp_block, Restated.voteStoreAt_slot facts,
          Restated.voteStoreAt_timestamp_block facts] at hst
        have hfreeze := facts.sch.view_freeze_add_delta_le_proposal_time_succ S.E (s - 1)
        rw [hss1] at hfreeze
        simp only [stampedBefore] at hst
        cases hσ : (x[mr][v].st).st.core.timestamp_block C with
        | none => rw [hσ] at hst; simp at hst
        | some σ =>
          rw [hσ] at hst
          have hlt : σ < ((M.view_freeze S.E (s - 1) : Int) : Stamp) := of_decide_eq_true hst
          have hσc : σ < ((M.proposal_time S.E s - S.E.Δ : Int) : Stamp) :=
            lt_of_lt_of_le hlt (by exact_mod_cast (by linarith : M.view_freeze S.E (s - 1) ≤ M.proposal_time S.E s - S.E.Δ))
          exact Restated.voterBlock_in_proposalTree facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen
            hsync hthird hphase hmult hcv hcs hw hnW hslot hprop hawp hk hv hFY hCT hσ hσc hYC
      · rw [facts.sto.toHealing_gs_T, Restated.voteStoreAt_T facts] at hP'T
        rw [Restated.voteStoreAt_slot facts] at hP's
        have hP'B := hUnique P' hP'T hP's
        rw [hP'B] at hCP'
        have hne : C ≠ B'.erase := fun h => hCs (by rw [h]; exact hBslot)
        have hCP : Block.Preceq C P :=
          preceq_eq_true_iff_Preceq.mp (Proofs.Optimistic.preceq_parent_of_ne hBpar (preceq_eq_true_iff_Preceq.mpr hCP') hne)
        exact Restated.mem_T_of_preceq_sts facts S Sched x k _ hPT hCP
    have hTC : Block.Preceq T.erase C := preceq_trans_Preceq hTY hYC
    exact hinP C C hCTp (preceq_trans_Preceq hFp hTC) (preceq_trans_Preceq hrootp hTC) hCTp
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self C)) hTC
  · -- `hBonly`
    intro C hC hCs
    have hCT := facts.hd.Sts_voter_filtered_block_tree_subset S.E _ _ Tv hTv hC
    rw [facts.hd.Sts_setClock_core_T] at hCT
    exact hUnique C hCT hCs
  · -- `hB`
    exact hinV _ hYB hBB

end

end DecoupledConsensusModel.Sts.Restated
