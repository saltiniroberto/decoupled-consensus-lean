import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSince
import Proofs.Claims.Restated.Claim13bK_ConeAnchor
import Proofs.Claims.Restated.Claim13bK_ConeSlots
import Proofs.Claims.Restated.Claim13bK_FgJustified
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bPhaseSleepiness
import Proofs.Claims.Restated.Claim13bStepActionF
import Proofs.Claims.Restated.Claim13bStepAnchor
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKit
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bStepQuorum
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.Claim13beRoute3_5
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsFacts
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_W4GSTZeroOpeningLifecycle
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_Frame
import Model.Conditions.Claim13bK_GradeOldHeads
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Claim13beRoute3_5
import Model.Conditions.Claim13beRoute3_7
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ConeChain
import Proofs.Claims.Restated.WakeWindow

/-!
# The chain from the SG root to a held block is in the voter tree

Over a model `M : Record.Model V`: bounds on `Σ.h_max` before the next round's tick, the ancestry of
the finalized block and the fork-choice root against the SG root of a vote or confirmation read,
`ConeAnchorChainInTree` at a block an honest validator holds, and the confirmed block of an action
read on one chain with a block.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- From any node state `before`, validator `v`'s round-`r` action read can compute some
    attestation. -/
private theorem actionAttestationFrom_nonempty_cc (facts : Record.Facts M) (S : Setup V)
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

/-- The attestations `v`'s round-`r` action read can compute from the node state `v`'s tick reads at
    instant `t` from configuration `c` are those it can compute from `v`'s node state in `c`. -/
private theorem actionAttestationFrom_wakeStage_cc (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (t : Int) (c : Config V (NamedObject V) M.N) (v : V) (r : Round) :
    Restated.actionAttestationFrom M S (Record.wakeStage M Sched t c v) v r =
      Restated.actionAttestationFrom M S (c[v].st) v r := by
  unfold Restated.actionAttestationFrom Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom
  rw [Record.wakeStage_st facts, Record.wakeStage_cache facts, Record.wakeStage_record facts]

/-- If the invariant holds at round `r` with tick step `n` and anchor `T`, step `n'` is the sts tick
    at `S.a (r + 1)`, and the round-level sleepiness bound holds from an instant `tE` at or before
    round `r + 1`'s opening, then after any number of steps up to `n'` every validator's store,
    honest or not, records a `Σ.h_max` at most one more than `T`'s chain-state height. -/
theorem hMax_le_anchor_succ_before_succ_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (htE : tE ≤ M.opening S.E S.hc (r + 1)) :
    ∀ (v : V) (n₁ : Nat), n₁ ≤ n' →
      (x[n₁][v].st).st.core.h_max ≤ (M.derive_named S.E S.cfg T).h + 1 := by
  classical
  intro v n₁ hn₁
  by_cases hsmall : (x[n₁][v].st).st.core.h_max ≤ 1
  · exact le_trans hsmall (Nat.succ_le_succ (Nat.zero_le _))
  obtain ⟨B, hBmem, hBh⟩ := Restated.hMax_attained_sts facts S Sched x n₁ v
  have hpos : 2 ≤ (M.derive_named S.E S.cfg B).h := by
    rw [hBh]; exact Nat.succ_le_of_lt (not_le.mp hsmall)
  obtain ⟨Q, hQ, hsign⟩ := Restated.carried_vote_of_tree_block facts S Sched x hBmem hpos
  obtain ⟨q, hqQ, hqadv⟩ := Restated.exists_nonAdv_of_quorum facts S Sched hrsW (r₀ := r + 1)
    (Nat.le_add_left 1 r) htE ((isQuorum_iff_q_le S.E Q).mp hQ)
  have htime : (x[n₁].time : Int) ≤ M.opening S.E S.hc (r + 1 + 1) := by
    refine le_trans (Restated.time_mono_int facts S Sched x (Nat.le_succ_of_le hn₁)) ?_
    rw [(Restated.tickStepAt_time facts x hn').1]
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self (r + 1))
    have h2 := facts.gr.early_g2_le_opening S (r + 1 + 1)
    have hd := S.E.Δ_pos
    show M.a S.hc S.E.Δ _ ≤ _
    linarith
  have hqhon : Restated.HonestThrough M Sched x n₁ q := by
    intro t ht hmem
    exact hqadv (hmono t (M.opening S.E S.hc (r + 1 + 1)) (le_trans ht htime) hmem)
  obtain ⟨carrier, a, entry, tmo, hcmem, hrow, hval, hpair⟩ := hsign q hqQ
  have hlog : (⟨a.val_index, NamedObject.attest a⟩ : SignedMsg V (NamedObject V))
      ∈ x[n₁].sent :=
    Restated.carried_vote_in_log facts S Sched x hexec hcmem hrow (by rw [hval]; exact hqhon)
  have hlog' : (⟨q, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₁].sent := by
    rw [← hval]; exact hlog
  have hhonT : HonestThroughTime Sched ((x[n₁].time : Int)) q := fun t ht => hqhon t ht
  obtain ⟨-, k, hkn₁, htick, hawk, out, hout, hemit⟩ :=
    Restated.attest_round_of_sent facts S Sched x (tB := (x[n₁].time : Int)) hhonT
      hexec.toUnforgeability hval (le_refl _) hlog'
  have heq : ∀ a' ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[k][q].st) q a.round,
      a = a' := by
    intro a' ha'
    have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (k) q (Restated.Vocabulary.Execution.Setup.a M S a.round)
    have _hv_s2 := Record.runs_as_wakeStage facts S Sched x (k) q (Restated.Vocabulary.Execution.Setup.a M S a.round)
    exact Restated.attest_of_tick_eq facts S q _ a.round hout hemit a'
      (by rw [actionAttestationFrom_wakeStage_cc facts]; exact ha')
  obtain ⟨a₁, ha₁⟩ := actionAttestationFrom_nonempty_cc facts (Setup.alwaysAwake S)
    (x[k][q].st) q a.round
  have hsent : (⟨q, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent := by
    rw [heq a₁ ha₁]
    -- the tick sent `a`, so the node state it read passed the grade-2 awake test of `a`'s round
    exact Restated.attest_emitted_at_tick_from facts S Sched x htick hawk ⟨out, hout⟩
      (facts.nd.tick_attestation_fields (Setup.alwaysAwake S) q _ _ (Record.runs_as_wakeStage facts S Sched x _ _ _) out hout a hemit).2.1 a₁ ha₁
  have hqk : Restated.HonestThrough M Sched x (k + 1) q := by
    intro t ht hmem
    exact hqhon t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt hkn₁))) hmem
  have hround : a.round ≤ r :=
    Restated.round_le_of_tick_lt facts S Sched x htick hn' (Nat.lt_of_lt_of_le hkn₁ hn₁)
  have hkn : k ≤ n := Restated.tick_le_of_round_le facts S Sched x htick hinv.tick hround
  have hh := hinv.heightCeiling q (k + 1) a _ entry tmo (Nat.succ_le_succ hkn) hqk hval hsent
    hpair
  have hone : 1 ≤ (M.derive_named S.E S.cfg B).h := le_trans (by decide) hpos
  calc (x[n₁][v].st).st.core.h_max
      = (M.derive_named S.E S.cfg B).h := hBh.symm
    _ = ((M.derive_named S.E S.cfg B).h - 1) + 1 := (Nat.sub_add_cancel hone).symm
    _ ≤ (M.derive_named S.E S.cfg T).h + 1 := Nat.succ_le_succ hh

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every outcome `n` of the slot-`s'` vote read of `before`, the fork-choice root of the store
    that read takes is an ancestor of every SG root the vote duty can start from under `n`'s grade
    contract. -/
theorem voteAnchor_fgRoot_preceq (facts : Record.Facts M) (S : Setup V) (before : M.N) (s' : Slot)
    {n : M.N} (hn : Restated.voteReadOf M S before s' ⇢ n) :
    ∀ A, Restated.voteAnchorOf M (M.gradeContract n.cache) S.E S.hc
        (Restated.voteStoreAt M S before s') ⇢ A →
      Block.Preceq (M.get_fg_root (M.toHealing (Restated.voteStoreAt M S before s')).toFG) A :=
  fun A hA => facts.fc.fg_root_Preceq_get_sg_root_with_gradeContract _ S.E S.hc
    (M.toHealing (Restated.voteStoreAt M S before s')) (M.round_of S.hc (Restated.voteStoreAt M S before s').s)
    A hA

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every outcome `n` of `v`'s slot-`s'` vote read after `m` steps, the finalized block of `v`'s
    store is an ancestor of every SG root the vote duty can start from under `n`'s grade contract. -/
theorem voteAnchor_F_preceq (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (m : Nat) (v : V) (s' : Slot)
    {n : M.N} (hn : Restated.voteReadOf M S (x[m][v].st) s' ⇢ n) :
    ∀ A, Restated.voteAnchorOf M (M.gradeContract n.cache) S.E S.hc
        (Restated.voteStoreAt M S (x[m][v].st) s') ⇢ A →
      Block.Preceq (x[m][v].st).st.core.F A := by
  intro A hA
  have hFJ : Block.preceq (M.toHealing (Restated.voteStoreAt M S (x[m][v].st) s')).toFG.F
      (M.toHealing (Restated.voteStoreAt M S (x[m][v].st) s')).toFG.J = true := by
    rw [Restated.voteStoreAt, facts.hd.setClock_toHealing_F, facts.hd.setClock_toHealing_J]
    exact preceq_eq_true_iff_Preceq.mpr (Restated.finalized_preceq_justified_sts facts S Sched x m v)
  have hF : (M.toHealing (Restated.voteStoreAt M S (x[m][v].st) s')).toFG.F = (x[m][v].st).st.core.F := by
    rw [Restated.voteStoreAt, facts.hd.setClock_toHealing_F]
  have hFroot := preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_F hFJ)
  rw [hF] at hFroot
  exact preceq_trans_Preceq hFroot (Restated.voteAnchor_fgRoot_preceq facts S (x[m][v].st) s' hn A hA)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `v_1` holds `B` at step `m`, whose instant is at or after `tGAT`, every finalized block of a
    validator honest through a step at or before `tR` is an ancestor of `B`, `t` is more than a
    delay after step `m`'s instant and at or before both `tR` and step `mr`'s instant, and `v` is
    honest through `mr` and awake at every instant of `[t − 2Δ, t]`, then every ancestor `C` of
    `B`'s erasure is in `v`'s tree after `mr` steps, with a stamp strictly before `t`. The
    hypothesis `hneTick` asks that `v`'s tick have an outcome at every whole multiple of `Δ` from
    the start of `C`'s slot to step `mr`'s instant at which `v` is awake and not held. -/
theorem chain_in_reader_tree_of_holder (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x)
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int}
    (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE)
    {B : NamedBlock V} {v_1 : V} {m : Nat} (hBv_1 : B ∈ (x[m][v_1].st).st.bodies)
    (hv_1 : Restated.HonestThrough M Sched x m v_1) (hm : tGAT ≤ (x[m].time : Int))
    (hFB : ∀ (v : V) (d : Nat), (x[d].time : Int) ≤ tR → Restated.HonestThrough M Sched x d v →
      Block.Preceq (x[d][v].st).st.core.F B.erase)
    {v : V} {mr : Nat} {t : Int} (hdeadline : (x[m].time : Int) + S.E.Δ < t)
    (hΓR : t ≤ tR) (hmr : t ≤ (x[mr].time : Int)) (hvh : Restated.HonestThrough M Sched x mr v)
    (hwaw : v ∈ Sched.awakeThroughout (t - 2 * S.E.Δ) t)
    {C : Block V} (hCB : Block.Preceq C B.erase)
    (hneTick : ∀ (n' : Nat) (t' : Int), Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' →
      slotStart S.E.Δ C.slot ≤ t' → t' ≤ (x[mr].time : Int) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out) :
    C ∈ (x[mr][v].st).st.core.T ∧
      ∃ σ : Stamp, (x[mr][v].st).st.core.timestamp_block C = some σ ∧ σ < (t : Stamp) := by
  have hBT : B.erase ∈ (x[m][v_1].st).st.core.T := by
    rw [Restated.bodies_image_eq_T facts S Sched x m v_1]
    exact Finset.mem_image_of_mem NamedBlock.erase hBv_1
  obtain ⟨D, hD, hDe⟩ := Restated.exists_named_of_mem_tree facts S Sched x m v_1
    (Restated.mem_T_of_preceq_sts facts S Sched x m v_1 hBT hCB)
  have hlogD : Restated.blockInLog M S Sched x D := Restated.blockInLog_of_mem_bodies facts S Sched hv_1 hD
  have hadm : Restated.ReaderAdmitsInPhase M S Sched x tGAT tR v D := by
    intro d v_0 _ hvd _ hhi
    have hc : Block.compatible (x[d][v].st).st.core.F D.erase = true := by
      rw [hDe]; exact compatible_of_preceq_common_Preceq (hFB v d hhi hvd) hCB
    rcases compatible_cases hc with hFD | hDF
    · exact Or.inl (preceq_eq_true_iff_Preceq.mpr hFD)
    · exact Or.inr (Restated.mem_bodies_of_preceq_finalized facts S Sched x hexec hvd hlogD hDF)
  have hadmS : Restated.ReaderAdmitsAtStepsInPhase M S Sched x tGAT tR v D := by
    intro d hvd _ hhi
    have hc : Block.compatible (x[d][v].st).st.core.F D.erase = true := by
      rw [hDe]; exact compatible_of_preceq_common_Preceq (hFB v d hhi hvd) hCB
    rcases compatible_cases hc with hFD | hDF
    · exact Or.inl (preceq_eq_true_iff_Preceq.mpr hFD)
    · exact Or.inr (Restated.mem_bodies_of_preceq_finalized facts S Sched x hexec hvd hlogD hDF)
  obtain ⟨hmem, σ, hσ, hσlt⟩ :=
    Restated.block_in_tree_of_holder_afterPhase_ofAdmits facts S Sched x hexec hsync hmult htd hmono hgst hcv
      hawake hthird hcs hlen hadm hadmS hD hv_1 hm hdeadline hΓR hmr (hvh _ le_rfl) hwaw
      (by rw [hDe]; exact hneTick)
  rw [hDe] at hmem hσ
  exact ⟨hmem, σ, hσ, hσlt⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If a store's slot is `s + 1`, `C` is in the store's tree stamped before slot `s`'s view freeze,
    the store's finalized block is an ancestor of `C`, some block `W` of the store's tree stamped
    before the same freeze is a descendant of `C` with a chain-state height at least the store's
    `h_max` minus one, and the store's fork-choice root is an ancestor of `C`, then `C` is in every
    candidate tree the store's vote duty can descend. -/
theorem mem_voteTreeOf_of_parts (facts : Record.Facts M) (S : Setup V) {st : M.S} {s : Slot}
    (hs : st.s = s + 1) {C W : Block V}
    (hC : C ∈ st.T)
    (hCs : stampedBefore st.timestamp_block (M.view_freeze S.E s) C = true)
    (hF : Block.Preceq st.F C)
    (hW : W ∈ st.T)
    (hWs : stampedBefore st.timestamp_block (M.view_freeze S.E s) W = true)
    (hCW : Block.Preceq C W) (hh : st.h_max - 1 ≤ (st.σ W).h)
    (hroot : Block.Preceq (M.get_fg_root (M.toHealing st).toFG) C) :
    ∀ T, Restated.voteTreeOf M S.E st ⇢ T → C ∈ T := by
  intro T hT
  obtain ⟨P, hP⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
    (M.toHealing st).toFG.toSG.toGoldfishStore st.s
  have hproc : ∀ X : Block V, X ∈ st.T →
      stampedBefore st.timestamp_block (M.view_freeze S.E s) X = true → X ∈ P := by
    intro X hX hXs
    refine facts.fc.mem_voter_processed_block_tree_of_stamped S.E _ st.s ?_ ?_ P hP
    · rw [facts.sto.toHealing_gs_T]; exact hX
    · rw [facts.sto.toHealing_gs_timestamp_block, hs, Nat.add_sub_cancel]; exact hXs
  exact facts.hd.mem_voter_filtered_block_tree_of_parts S.E st st.s P hP (hproc C hC hCs) hF
    (hproc W hW hWs) hCW hh hroot T hT

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `v_1` holds `B` at step `m`, whose instant is at or after `tGAT` and more than a delay before
    slot `s`'s view freeze, every finalized block of a validator honest through a step at or before
    `tR` is an ancestor of `B`, every store's `h_max` at such a step is at most one more than `B`'s
    chain-state height, and slot `s + 1`'s vote instant is at most `tR + 1`, then
    `ConeAnchorChainInTree S x B.erase s`: every block strictly between an honest active voter's SG
    root and `B` is in that voter's slot-`(s + 1)` voter tree. The hypothesis `hneTickW` asks that
    the tick of every validator of `HonSlot S Sched (s + 1)` have an outcome at every whole multiple
    of `Δ` before slot `s + 1`'s vote instant at which it is awake and not held. -/
theorem coneAnchorChainInTree_of_holder_of_bounds (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x)
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int}
    (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE)
    {B : NamedBlock V} {v_1 : V} {m : Nat} (hBv_1 : B ∈ (x[m][v_1].st).st.bodies)
    (hv_1 : Restated.HonestThrough M Sched x m v_1) (hm : tGAT ≤ (x[m].time : Int))
    (hFB : ∀ (v : V) (d : Nat), (x[d].time : Int) ≤ tR → Restated.HonestThrough M Sched x d v →
      Block.Preceq (x[d][v].st).st.core.F B.erase)
    (hhmax : ∀ (v : V) (d : Nat), (x[d].time : Int) ≤ tR →
      (x[d][v].st).st.core.h_max ≤ (M.derive_named S.E S.cfg B).h + 1)
    {s : Slot} (hdeadline : (x[m].time : Int) + S.E.Δ < M.view_freeze S.E s)
    (hvt : M.vote_time S.E (s + 1) ≤ tR + 1)
    (hneTickW : ∀ w ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → w ∈ Sched.awake t' \ Sched.adv t' → t' < M.vote_time S.E (s + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t' x[n'] w) t' ⇢ out) :
    Restated.ConeAnchorChainInTree M S x B.erase s := by
  intro v mr hv hmr nr hnr A hA C hAC _ hCB T hT
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  obtain ⟨-, hself⟩ := Restated.tickStepAt_time facts x hmr
  -- the view freeze is at most two delays before slot `s + 1`'s vote instant, and after the start
  -- of slot `s`
  have hvt1 := facts.sch.slotStart_add_delta_eq_vote_time S.E (s + 1)
  have hss := slotStart_succ S.E.Δ s
  have hvf_le : M.view_freeze S.E s ≤ M.vote_time S.E (s + 1) - 2 * S.E.Δ := by
    have h1 := facts.sch.view_freeze_add_delta_le_proposal_time_succ S.E s
    have hpv := facts.sch.proposal_time_lt_vote_time S.E (s + 1)
    have hps : M.proposal_time S.E (s + 1) ≤ slotStart S.E.Δ (s + 1) := by
      obtain ⟨a, ha⟩ := Int.dvd_of_emod_eq_zero (slotStart_emod_delta S (s + 1))
      obtain ⟨b, hb⟩ :=
        Int.dvd_of_emod_eq_zero (facts.sch.proposal_time_emod_delta_inclX S.E (s + 1))
      rw [← hvt1, ha, hb] at hpv
      rw [ha, hb]
      have hba : b < a + 1 :=
        lt_of_mul_lt_mul_left (by rw [mul_add, mul_one]; exact hpv) (le_of_lt hd)
      have hab : b ≤ a := by omega
      exact mul_le_mul_of_nonneg_left hab (le_of_lt hd)
    linarith
  have hvf_ge : slotStart S.E.Δ s < M.view_freeze S.E s := by
    have hc0 : slotStart S.E.Δ s ≤ M.support_cutoff S.E s :=
      slotStart_le_of_le_slotOf S (le_of_lt (facts.sch.support_cutoff_pos S s))
        (le_of_eq (facts.sch.slotOf_support_cutoff S.E s).symm)
    have hcvf := facts.sch.Sts_support_cutoff_lt_view_freeze S.E s
    linarith
  have hmrR : (x[mr].time : Int) ≤ tR := by linarith
  have hΓR : M.view_freeze S.E s ≤ tR := by linarith
  have hΓmr : M.view_freeze S.E s ≤ (x[mr].time : Int) := by linarith
  have hct : (x[mr].time : Int) ≤ M.confirmation_time S.E (s + 1) := by
    have e : M.confirmation_time S.E (s + 1) = M.vote_time S.E (s + 1) + 5 * S.E.Δ :=
      by
        have h1 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (s + 1)
        have h2 := facts.sch.slotStart_add_delta_eq_vote_time S.E (s + 1)
        linarith
    linarith
  have hvh : Restated.HonestThrough M Sched x mr v := Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hv hct
  have hwin : v ∈ Sched.awakeThroughout (M.vote_time S.E (s + 1) - wVote S)
      (M.vote_time S.E (s + 1)) := by
    rw [← facts.sch.slotStart_add_delta_eq_vote_time S.E (s + 1)]; exact ((Restated.mem_HonSlot facts).mp hv).1
  have hwv : wVote S = 4 * (S.hc.R : Int) * S.E.Δ + 2 * S.E.Δ := by unfold wVote; ring
  have hRd : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have hwaw : v ∈ Sched.awakeThroughout (M.view_freeze S.E s - 2 * S.E.Δ)
      (M.view_freeze S.E s) :=
    awakeThroughout_mono Sched hwin (by rw [hwv]; linarith) (by linarith)
  have hneTick : ∀ (n' : Nat) (t' : Int), Restated.tickStepAt M x n' t' →
      t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ (x[mr].time : Int) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out :=
    fun n' t' hn' hΔ hq ht' => hneTickW v hv n' t' hn' hΔ hq (by linarith)
  have hchain := fun (X : Block V) (hX : Block.Preceq X B.erase) =>
    Restated.chain_in_reader_tree_of_holder facts S Sched x hexec hsync hmult htd hmono hgst hcv hawake hthird
      hcs hlen hBv_1 hv_1 hm hFB hdeadline hΓR hΓmr hvh hwaw hX
      (fun n' t' hn' hΔ hq _ ht' => hneTick n' t' hn' hΔ hq ht')
  obtain ⟨hCT, σC, hσC, hσClt⟩ := hchain C hCB
  obtain ⟨hBT, σB, hσB, hσBlt⟩ := hchain B.erase (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
  have hBbody : B ∈ (x[mr][v].st).st.bodies :=
    Restated.mem_bodies_of_mem_T_honest facts S Sched x hexec hvh (Restated.blockInLog_of_mem_bodies facts S Sched hv_1 hBv_1) hBT
  have hco : Restated.Vocabulary.Proofs.NamedStore.Coherent M (Setup.alwaysAwake S).E (Setup.alwaysAwake S).cfg
      (x[mr][v].st).st := (Restated.nodeInvariant_sts facts S Sched x mr v).1.1.1
  have hσ : (x[mr][v].st).st.core.σ B.erase = M.derive_named S.E S.cfg B :=
    hco.2.2.2.2 B hBbody
  have hF := preceq_trans_Preceq (Restated.voteAnchor_F_preceq facts S Sched x mr v (s + 1) hnr A hA) hAC
  refine Restated.mem_voteTreeOf_of_parts facts S (Restated.voteStoreAt_slot facts S (x[mr][v].st) (s + 1)) (W := B.erase)
    ?_ ?_ ?_ ?_ ?_ hCB ?_
    (preceq_trans_Preceq (Restated.voteAnchor_fgRoot_preceq facts S (x[mr][v].st) (s + 1) hnr A hA) hAC)
    T hT
  all_goals rw [Restated.voteStoreAt]
  · rw [facts.hd.Sts_setClock_core_T]; exact hCT
  · rw [facts.hd.setClock_core_timestamp_block]; exact stampedBefore_of_lt hσC hσClt
  · rw [facts.hd.setClock_core_F]; exact hF
  · rw [facts.hd.Sts_setClock_core_T]; exact hBT
  · rw [facts.hd.setClock_core_timestamp_block]; exact stampedBefore_of_lt hσB hσBlt
  · rw [facts.hd.setClock_core_h_max, facts.hd.Sts_setClock_core_σ, hσ]
    exact Nat.sub_le_iff_le_add.mpr (hhmax v mr hmrR)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If round `r` is at or after the switch round, the invariant holds at round `r` with anchor `T`,
    step `n'` is the sts tick at `S.a (r + 1)`, and the premises on `tGAT`, the one-third bound, the
    phase-awake premise and the round-level sleepiness bound hold, then after any number of steps up
    to `n'` every validator's store records a `Σ.h_max` at most one more than `T`'s chain-state
    height. -/
theorem hMax_le_anchor_succ_before_succ_tick_of_hypotheses (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) :
    ∀ (v : V) (n₁ : Nat), n₁ ≤ n' →
      (x[n₁][v].st).st.core.h_max ≤ (M.derive_named S.E S.cfg T).h + 1 :=
  Restated.hMax_le_anchor_succ_before_succ_tick facts S Sched x hexec hmono (tE := Restated.switchOpening M S tE)
    (Restated.roundSleepinessW_switchOpening_of_phase facts S Sched tGAT tE gap hgst hlen hmono hthird hphase
      hrsW)
    hinv hn' (Restated.switchOpening_le_opening facts S (le_trans hr (Nat.le_succ r)))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `n'` is the sts tick at `S.a (r + 1)` and step `d`'s instant is at most
    `S.a (r + 1) − 1`, then `d ≤ n'`. -/
theorem le_tick_of_time_lt_action (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {n' d : Nat}
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) (hd : (x[d].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1) :
    d ≤ n' := by
  by_contra hcon
  have hle : n' + 1 ≤ d := by omega
  have h1 := Restated.time_mono_int facts S Sched x hle
  rw [(Restated.tickStepAt_time facts x hn').1] at h1
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If round `r` is at or after the switch round, the invariant holds at round `r` with anchor `T`,
    `v_1` holds `B` at step `m`, whose instant is at or after `tGAT` and more than a delay before
    slot `s`'s view freeze, `T` is an ancestor of `B` and `B`'s chain-state height is at least
    `T`'s, and slot `s + 1` is at most one slot after round `r + 1`'s opening slot, then every block
    strictly between an honest active voter's SG root and `B` is in that voter's slot-`(s + 1)`
    voter tree. The hypothesis `hneTickW` is that of `coneAnchorChainInTree_of_holder_of_bounds`. -/
theorem coneAnchorChainInTree_of_holder (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    {B : NamedBlock V} {v_1 : V} {m : Nat} (hBv_1 : B ∈ (x[m][v_1].st).st.bodies)
    (hv_1 : Restated.HonestThrough M Sched x m v_1) (hm : tGAT ≤ (x[m].time : Int))
    (hTB : Block.Preceq T.erase B.erase)
    (hheight : (M.derive_named S.E S.cfg T).h ≤ (M.derive_named S.E S.cfg B).h)
    {s : Slot} (hdeadline : (x[m].time : Int) + S.E.Δ < M.view_freeze S.E s)
    (hj : s + 1 ≤ (M.opening_slot S.hc (r + 1)) + 1)
    (hneTickW : ∀ w ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → w ∈ Sched.awake t' \ Sched.adv t' → t' < M.vote_time S.E (s + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t' x[n'] w) t' ⇢ out) :
    Restated.ConeAnchorChainInTree M S x B.erase s := by
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd r
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE hexec hmono tGAT gap
    hgst hlen hthird hphase hrsW hr hinv hn'
  have hhm := Restated.hMax_le_anchor_succ_before_succ_tick_of_hypotheses facts S Sched x tE hexec hmono tGAT
    gap hgst hlen hthird hphase hrsW hr hinv hn'
  have hd := S.E.Δ_pos
  have hvt : M.vote_time S.E (s + 1) ≤ ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1) + 1 := by
    have e1 := Restated.vote_time_opening_slot_add facts S (r + 1) 1
    have hle : ((s + 1 : Nat) : Int) ≤ (((M.opening_slot S.hc (r + 1)) + 1 : Nat) : Int) := by
      exact_mod_cast hj
    have e2 : M.vote_time S.E (s + 1)
        ≤ M.vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1) :=
      facts.sch.vote_time_mono S.E (by exact_mod_cast hle)
    push_cast at e1
    linarith
  exact Restated.coneAnchorChainInTree_of_holder_of_bounds facts S Sched x hexec hsync hmult htd hmono
    (tR := (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1) hgst hcv hphase hthird hcs (Restated.delta_le_of_healingLengthη facts S hlen)
    hBv_1 hv_1 hm
    (fun v d hd' hvd => preceq_trans_Preceq
      (hfin v d (Restated.le_tick_of_time_lt_action facts S Sched x hn' hd') hvd) hTB)
    (fun v d hd' => le_trans (hhm v d (Restated.le_tick_of_time_lt_action facts S Sched x hn' hd'))
      (Nat.succ_le_succ hheight))
    hdeadline hvt hneTickW

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every outcome `c` of the phase tick the slot-`s` confirmation read prepares, the fork-choice
    root of the store that read takes is an ancestor of every SG root its confirmation walk can
    start from under `c`'s grade contract. -/
theorem confAnchor_fgRoot_preceq (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot)
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing before.st.core)
      (M.confirmation_time S.E s) before.cache ⇢ c) :
    ∀ A, Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
        (Restated.confStoreAt M S before s) ⇢ A →
      Block.Preceq (M.get_fg_root (M.toHealing (Restated.confStoreAt M S before s)).toFG) A := by
  intro A hA
  unfold Restated.Vocabulary.Protocol.confAnchorWith at hA
  exact facts.fc.fg_root_Preceq_get_sg_root_with_gradeContract c S.E S.hc
    (M.toHealing (Restated.confStoreAt M S before s)) (M.round_of S.hc (Restated.confStoreAt M S before s).s)
    A hA

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every outcome `c` of the phase tick `v`'s slot-`s` confirmation read prepares after `n`
    steps, the finalized block of `v`'s store is an ancestor of every SG root that read can start
    from under `c`'s grade contract. -/
theorem confAnchor_F_preceq (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (n : Nat) (v : V) (s : Slot)
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n][v].st).st.core)
      (M.confirmation_time S.E s) (x[n][v].st).cache ⇢ c) :
    ∀ A, Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
        (Restated.confStoreAt M S (x[n][v].st) s) ⇢ A →
      Block.Preceq (x[n][v].st).st.core.F A := by
  intro A hA
  have hFJ : Block.preceq (M.toHealing (Restated.confStoreAt M S (x[n][v].st) s)).toFG.F
      (M.toHealing (Restated.confStoreAt M S (x[n][v].st) s)).toFG.J = true := by
    rw [Restated.confStoreAt, facts.hd.setClock_toHealing_F, facts.hd.setClock_toHealing_J]
    exact preceq_eq_true_iff_Preceq.mpr (Restated.finalized_preceq_justified_sts facts S Sched x n v)
  have hFroot := preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_F hFJ)
  rw [Restated.confStoreAt, facts.hd.setClock_toHealing_F] at hFroot
  exact preceq_trans_Preceq hFroot (Restated.confAnchor_fgRoot_preceq facts S (x[n][v].st) s c hc A hA)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every outcome `c` of the phase tick the slot-`s` confirmation read prepares at `before`,
    every SG root the read can start from under `c`'s grade contract lies on one chain with `B`
    whenever every grade-1 root `c`'s frame holds for the round of the read's store does, and so do
    `before`'s finalized and justified blocks. -/
theorem confAnchor_compatible_of_parts (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot)
    {B : Block V}
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing before.st.core)
      (M.confirmation_time S.E s) before.cache ⇢ c)
    (hg1 : ∀ root : Block V,
      (M.readFrame c
        (M.toHealing (Restated.confStoreAt M S before s)) (M.round_of S.hc (Restated.confStoreAt M S before s).s)).g1
        = some (some root) →
      Block.compatible root B = true)
    (hF : Block.compatible before.st.core.F B = true)
    (hJ : before.st.core.h_max = before.st.core.h_j + 1 →
      Block.compatible before.st.core.J B = true) :
    ∀ A, Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
        (Restated.confStoreAt M S before s) ⇢ A → Block.compatible A B = true := by
  intro A hA
  have hfg : Block.compatible
      (M.get_fg_root (M.toHealing (Restated.confStoreAt M S before s)).toFG) B = true :=
    facts.fc.fgRoot_compatible_of_compatible (stH := (M.toHealing (Restated.confStoreAt M S before s)))
      (by rw [Restated.confStoreAt, facts.hd.setClock_toHealing_F]; exact hF)
      (by
        rw [Restated.confStoreAt, facts.hd.setClock_toHealing_h_max, facts.hd.setClock_toHealing_h_j, facts.hd.setClock_toHealing_J]
        exact hJ)
  unfold Restated.Vocabulary.Protocol.confAnchorWith at hA
  exact facts.gr.anchor_compatible S hg1 hfg A
    ((facts.nd.gradeContract_sgRoot_eq_frameAnchor _ _ _ _ _ _).1 hA)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `n` is the sts tick step at slot `s`'s confirmation instant, `c` is an outcome of the phase
    tick of `v`'s slot-`s` confirmation read and `c`'s frame offers `root` as its grade-1 result for
    the round `ρ` of the read's store, then there are a step `m` before `ρ`'s grade-1 domain instant
    and a block `B` such that every outcome of the grade test of `B` on `v`'s store after `m` steps
    with the grade-1 cutoffs is `true`, and `root ⪯ B`. -/
theorem confFrame_g1_provenance (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {s : Slot} {n : Nat}
    (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s)) (v : V) (root : Block V)
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n][v].st).st.core)
      (M.confirmation_time S.E s) (x[n][v].st).cache ⇢ c)
    (h : (M.readFrame c
        (M.toHealing (Restated.confStoreAt M S (x[n][v].st) s))
        ((M.round_of S.hc (Restated.confStoreAt M S (x[n][v].st) s).s))).g1 = some (some root)) :
    ∃ (m : Nat) (B : Block V),
      Restated.stepBeforeInstant M x m
        (M.domain S.E S.hc ((M.round_of S.hc (Restated.confStoreAt M S (x[n][v].st) s).s)) .g1) ∧
      (∀ b : Bool, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
        (x[m][v].st).st.core.F S.hc.η_SG ((M.round_of S.hc (Restated.confStoreAt M S (x[n][v].st) s).s))
        (M.early S.E S.hc ((M.round_of S.hc (Restated.confStoreAt M S (x[n][v].st) s).s)) .g1)
        (M.late S.E S.hc ((M.round_of S.hc (Restated.confStoreAt M S (x[n][v].st) s).s)) .g1) B ⇢ b →
        b = true) ∧
      Block.Preceq root B := by
  have hprep := Restated.framePhaseProvenance_onPhaseTick facts S hn
    (Restated.framePhaseProvenance_sts facts S Sched x v n) c hc
  obtain ⟨root₀, h₀, hpre⟩ := facts.gr.readFrame_g1_provenance _ _ _ h
  obtain ⟨m, B, hm, hB, hpre'⟩ := hprep _ .g1 root₀ h₀
  exact ⟨m, B, hm, hB, preceq_trans_Preceq hpre hpre'⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The store the confirmation read of round `r`'s opening slot takes is in a slot of round `r`. -/
theorem round_of_confStoreAt_opening_slot (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    M.round_of S.hc (Restated.confStoreAt M S before (M.opening_slot S.hc r)).s = r := by
  rw [Restated.confStoreAt, facts.hd.Sts_setClock_core_s, Restated.confirmation_time_opening_slot facts]
  exact Restated.round_of_slotOf_action facts S r

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If round `r` is at or after the switch round, the invariant holds at round `r` with anchor `T`,
    step `n'` is the sts tick at `S.a (r + 1)`, and `v` is in `HonRound S Sched (r + 1)`, then for
    every outcome `c` of the phase tick of `v`'s confirmation read of round `r + 1`'s opening slot,
    every SG root the read can start from under `c`'s grade contract lies on one chain with `T`. The
    hypotheses `hneTick` and `hneAtt` ask that `v`'s tick have an outcome at every whole multiple of
    `Δ` up to `S.a (r + 1)` at which `v` is awake and not held, and that `M.tick` on every honest
    active attester of round `r` at `S.a r` have an outcome. -/
theorem confAnchor_compatible_at_honRound (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {v : V} (hv : v ∈ Restated.HonRound M S Sched (r + 1))
    (hneTick : ∀ (n'' : Nat) (t' : Int),
      Restated.tickStepAt M x n'' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n''] v) t' ⇢ out)
    (hneAtt : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n'][v].st).st.core)
      (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) (x[n'][v].st).cache ⇢ c) :
    ∀ A, Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
        (Restated.confStoreAt M S (x[n'][v].st) ((M.opening_slot S.hc (r + 1)))) ⇢ A →
      Block.compatible A T.erase = true := by
  have hround := Restated.round_of_confStoreAt_opening_slot facts S (x[n'][v].st) (r + 1)
  have hct := Restated.confirmation_time_opening_slot facts S (r + 1)
  have hn'' : Restated.tickStepAt M x n' (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) := by
    rw [hct]; exact hn'
  have htn : (x[n'].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := by
    rw [← (Restated.tickStepAt_time facts x hn').1]
    exact Restated.time_mono_int facts S Sched x (Nat.le_succ n')
  have hvadv : v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := (Finset.mem_sdiff.1 hv).2
  have hvn : Restated.HonestThrough M Sched x n' v := fun t ht hin =>
    hvadv (hmono t _ (le_trans ht htn) hin)
  refine Restated.confAnchor_compatible_of_parts facts S (x[n'][v].st) _ c hc ?_ ?_ ?_
  · intro root hroot
    obtain ⟨m, B, hm, hB, hpre⟩ :=
      Restated.confFrame_g1_provenance facts S Sched x hn'' v root c hc hroot
    rw [hround] at hm hB
    have hdom := facts.gr.domain_le_action S (r + 1) .g1
    have hawT := Restated.hawT_of_honRound_succ facts S Sched hv hdom
    have hvS : v ∉ Sched.adv (M.domain S.E S.hc (r + 1) .g1) := fun hin =>
      hvadv (hmono _ _ hdom hin)
    obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
      (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g1)
      (M.late S.E S.hc (r + 1) .g1) B
    have hbt := hB b hb
    subst hbt
    exact Protocol.compatible_of_preceq_of_compatible hpre
      (Restated.grade1_compatible_at_awakeReader facts (hcross := hcross) S Sched x tE hexec hmono htd hsync hmult tGAT gap hgst
        hlen hcv hthird hphase hrsW hcs hr hinv hdom hawT hvS hm B hb hneTick hneAtt)
  · exact compatible_of_preceq_common_Preceq
      (Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE hexec hmono tGAT gap hgst hlen
        hthird hphase hrsW hr hinv hn' v n' le_rfl hvn)
        (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
  · exact fun hroot => compatible_of_preceq_common_Preceq
      (Restated.justified_old_anchor_before_succ_tick_of_hypotheses facts (hjust := hjust) S Sched x tE hexec hmono tGAT gap hgst
        hlen hthird hphase hrsW hr hinv hn' v n'
        (Restated.tick_succ_le_tick_succ_round facts S Sched x hinv.tick hn') le_rfl hvn hroot)
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

open scoped DC in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim_cc {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro_cc {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- Every outcome of the slot-`s` confirmation votes of `st` is, for an outcome `tm` of `st`'s
    resolution times, the slot-`s` pool filtered by `tm` against the support cutoff and then by the
    absence of a second vote of the same signer in the late set. -/
private theorem confVotes_cases_cc (E : Env V) (st : M.S) (s : Slot) {e : Finset (GoldfishVote V)}
    (he : Restated.Vocabulary.Protocol.confVotes M E st s ⇢ e) :
    ∃ tm, st.tau ⇢ tm ∧
      e = (beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) u = true) := by
  obtain ⟨e', he', rfl⟩ := returns_map_elim_cc _ _ _ he
  obtain ⟨tm, htm, rfl⟩ := returns_map_elim_cc _ _ _ he'
  exact ⟨tm, htm, rfl⟩

/-- If step `n` is the tick at slot `s`'s confirmation instant, `w` is awake and honest there, `w`'s
    tick at step `n` has an outcome, and the node state that tick reads passes the grade-2 awake
    test of slot `s + 1`'s round (`hrun`), then after the step `w`'s `live_confirmed` is the head
    `W` of the confirmation walk from `A` over its clock-stamped store, or the FG root of that
    store, along one path of outcomes: `c` of the phase tick, `A` of the anchor, `e` of the
    confirmation votes, `sc` of the scores and `W` of the walk. -/
private theorem live_confirmed_after_confirmation_tick_cases (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {n : Nat} {s : Slot} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s)) {w : V}
    (haw : w ∈ Sched.awake (M.confirmation_time S.E s) \ Sched.adv (M.confirmation_time S.E s))
    (hneTickConf : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w) (M.confirmation_time S.E s) ⇢ out)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) w
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w) (M.round_of S.hc (s + 1)))
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n][w].st).st.core)
      (M.confirmation_time S.E s) (x[n][w].st).cache ⇢ c)
    (A : Block V) (hA : Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
      (Restated.confStoreAt M S (x[n][w].st) s) ⇢ A)
    (e : Finset (GoldfishVote V))
    (he : Restated.Vocabulary.Protocol.confVotes M S.E (Restated.confStoreAt M S (x[n][w].st) s) s ⇢ e)
    (sc : Block V → ℕ)
    (hsc : ∀ C, M.goldfish_score S.E (Restated.confStoreAt M S (x[n][w].st) s).T e e s C ⇢ sc C)
    (W : Block V)
    (hW : M.ghost A (Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[n][w].st) s))
      sc (fun C => decide (Restated.Vocabulary.Protocol.confCount M S.E
        (Restated.confStoreAt M S (x[n][w].st) s) s < 2 * sc C)) ⇢ W) :
    (x[n + 1][w].st).st.core.live_confirmed = W ∨
      (x[n + 1][w].st).st.core.live_confirmed
        = Restated.Vocabulary.Protocol.confRoot M (Restated.confStoreAt M S (x[n][w].st) s) := by
  have _hr_0 : M.reachedNode (x[n][w].st) := Record.reachedNode_sts facts S Sched x n w
  obtain ⟨t', hlbl, ht'⟩ := id hn
  have hct := facts.sch.confirmation_time_eq_support_cutoff_succ S.E s
  have hdvd : (t' : Int) % S.E.Δ = 0 := by
    rw [ht', hct]
    exact facts.sch.support_cutoff_emod_delta S (s + 1)
  have haw' : w ∈ Sched.awake (t' : Int) \ Sched.adv (t' : Int) := by rw [ht']; exact haw
  rcases Restated.st_succ_of_tick_awake facts S Sched x w hlbl haw' hdvd with
    ⟨out₁, hout, hst⟩ | ⟨hno, -⟩
  · rw [hst]
    rw [ht', hct] at hout
    rw [hct] at hc
    obtain ⟨D, hD⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
      S.hc (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))) (s + 1 - 1)
    obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core (s + 1 - 1)
    rw [hct] at hrun
    have _hr_s3 := Record.reachedNode_wakeStage facts S Sched x (n) w (M.support_cutoff S.E (s + 1))
    rw [facts.nd.on_tick_emit_confirmation_of_outcomes (Setup.alwaysAwake S) w _
        (s + 1) (Nat.succ_pos s) out₁ hout c
        (by rw [Record.wakeStage_st facts, Record.wakeStage_cache facts]; exact hc) D
        (by rw [Record.wakeStage_st facts]; exact hD) hrun,
      facts.dt.named_update_confirmation_with_core _ _ _ _ _ D hD X hX]
    rw [Nat.add_sub_cancel] at hX
    obtain ⟨tm, htm, rfl⟩ := confVotes_cases_cc S.E _ s he
    have hconf : Restated.confStoreAt M S (x[n][w].st) s
        = (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core := by
      rw [Restated.confStoreAt, hct]
    rw [hconf] at hA htm hsc hW ⊢
    exact facts.hd.update_confirmation_with_live_confirmed_walk_or_fgRoot _ _ _ _ _ tm htm A hA
      sc hsc W hW X hX
  · obtain ⟨o, ho⟩ := hneTickConf
    rw [← ht'] at ho
    exact absurd ho (hno o)

/-- If `n` is the sts tick step at `S.a (r + 1)`, `v` is awake and not held by the adversary there,
    `v`'s tick at step `n` has an outcome (`hneTickConf`) and the node state it reads passes the
    grade-2 awake test (`hrun`), then for every outcome `c` of the phase tick of `v`'s confirmation
    read of round `r + 1`'s opening slot, every SG root `A` that read can start from under `c`'s
    grade contract with `B ⪯ A`, and every store `hs` `v`'s round-`(r + 1)` action read can give
    whose finalized block is an ancestor of `B` and whose justified block lies on one chain with `B`
    (when `hs.h_max = hs.h_j + 1`), the confirmed block `hs` holds lies on one chain with `B`. -/
theorem live_confirmed_compatible_of_anchor_descendant (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {r : Round} {n : Nat} {v : V} {B : Block V}
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (haw : v ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) \ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n][v].st).st.core)
      (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) (x[n][v].st).cache ⇢ c)
    (A : Block V) (hA : Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
      (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1)))) ⇢ A)
    (hBA : Block.Preceq B A)
    (hs : M.HS) (hhs : hs ∈ Restated.actionHealingStore M S (x[n][v].st) (r + 1))
    (hF : Block.Preceq hs.F B)
    (hJ : hs.h_max = hs.h_j + 1 → Block.compatible hs.J B = true)
    (hneTickConf : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) x[n] v) (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ⇢ out)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E (M.opening_slot S.hc (r + 1))) x[n] v)
      (M.round_of S.hc (M.opening_slot S.hc (r + 1) + 1))) :
    Block.compatible hs.live_confirmed B = true := by
  have hct : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    Restated.confirmation_time_opening_slot facts S (r + 1)
  have hn' : Restated.tickStepAt M x n (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) := by
    rw [hct]; exact hn
  have haw' : v ∈ Sched.awake (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) \
      Sched.adv (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) := by
    rw [hct]; exact haw
  have hneConf : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v
        (Record.wakeStage M Sched (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) x[n] v)
        (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) ⇢ out := by
    rw [hct]; exact hneTickConf
  have hbridge : hs.live_confirmed = (x[n + 1][v].st).st.core.live_confirmed :=
    Restated.actionHealingStore_live_confirmed facts S Sched x hct
      (Restated.slotOf_a_sub_one facts S (r + 1)) hn' haw' hneConf hrun hs hhs
  rw [hbridge]
  -- one outcome of the confirmation votes, of the score per block, and of the walk from `A`
  obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty
    (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1))))
  obtain ⟨e, he⟩ : ∃ e, Restated.Vocabulary.Protocol.confVotes M S.E
      (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1))))
      ((M.opening_slot S.hc (r + 1))) ⇢ e :=
    ⟨_, returns_map_intro_cc _ _ _ (returns_map_intro_cc _ _ _ htm)⟩
  obtain ⟨sc, hsc⟩ : ∃ sc : Block V → ℕ, ∀ C,
      M.goldfish_score S.E (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1)))).T
        e e ((M.opening_slot S.hc (r + 1))) C ⇢ sc C :=
    ⟨fun C => Classical.choose (facts.fc.goldfish_score_nonempty S.E _ e e _ C),
      fun C => Classical.choose_spec (facts.fc.goldfish_score_nonempty S.E _ e e _ C)⟩
  obtain ⟨W, hW⟩ := facts.fc.ghost_nonempty A
    (Restated.Vocabulary.Protocol.confTree M
      (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1))))) sc
    (fun C => decide (Restated.Vocabulary.Protocol.confCount M S.E
      (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1))))
      ((M.opening_slot S.hc (r + 1))) < 2 * sc C))
  rcases live_confirmed_after_confirmation_tick_cases facts S Sched x hn' haw' hneConf hrun
      c hc A hA e he sc hsc W hW with hlc | hlc
  · rw [hlc]
    exact compatible_of_preceq_common_Preceq (Proofs.ModelProperties.Preceq_self _)
      (preceq_trans_Preceq hBA (facts.fc.ghost_preceq _ _ _ _ _ hW))
  · rw [hlc]
    unfold Restated.Vocabulary.Protocol.confRoot
    have hF' : Block.Preceq
        (M.toHealing (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1))))).toFG.F B := by
      unfold Restated.confStoreAt
      rw [facts.hd.setClock_toHealing_F]
      rw [Restated.actionHealingStore_F facts S _ _ hs hhs] at hF
      exact hF
    have hJ' : (M.toHealing (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1))))).toFG.h_max
        = (M.toHealing (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1))))).toFG.h_j + 1 →
        Block.compatible
        (M.toHealing (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1))))).toFG.J B = true := by
      unfold Restated.confStoreAt
      rw [facts.hd.setClock_toHealing_h_max, facts.hd.setClock_toHealing_h_j, facts.hd.setClock_toHealing_J]
      rw [Restated.actionHealingStore_h_max facts S _ _ hs hhs, Restated.actionHealingStore_h_j facts S _ _ hs hhs,
        Restated.actionHealingStore_J facts S _ _ hs hhs] at hJ
      exact hJ
    exact facts.fc.fgRoot_compatible_ofJustifiedBranch hF' hJ'

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- When the SG root `A` of `v`'s confirmation read of round `r + 1`'s opening slot lies on one
    chain with `T` (and is not necessarily an ancestor of it), the confirmed block every store `hs`
    of `v`'s round-`(r + 1)` action read holds lies on one chain with `T`. The hypotheses
    `hneTickVote` and `hneTick` ask for tick outcomes: of every honest active member of the opening
    slot's committee at its vote instant, and of `v` at every whole multiple of `Δ` up to the
    opening slot's confirmation instant at which `v` is awake and not held. -/
theorem live_confirmed_compatible_at_action_afterPhase_ofCompatible (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x)
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int} (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE)
    {r : Round} {n : Nat} {v : V} {T : NamedBlock V}
    (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT tR T.erase)
    (hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x tGAT tR T.erase)
    (hsE : tE ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))))
    (hsR : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1))) ≤ tR)
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hv : v ∈ Restated.HonRound M S Sched (r + 1))
    (hprev : Restated.HeadsBelow M S Sched x T.erase ((M.opening_slot S.hc (r + 1))))
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n][v].st).st.core)
      (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) (x[n][v].st).cache ⇢ c)
    (A : Block V) (hA : Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
      (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1)))) ⇢ A)
    (hAB : Block.compatible A T.erase = true)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C T.erase →
      C ∈ Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1)))))
    (hs : M.HS) (hhs : hs ∈ Restated.actionHealingStore M S (x[n][v].st) (r + 1))
    (hF : Block.Preceq hs.F T.erase)
    (hJ : hs.h_max = hs.h_j + 1 → Block.compatible hs.J T.erase = true)
    (hneTickVote : ∀ m : Nat, Restated.tickStepAt M x m (M.vote_time S.E ((M.opening_slot S.hc (r + 1)))) →
      ∀ q ∈ Restated.HonSlot M S Sched ((M.opening_slot S.hc (r + 1))), ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E ((M.opening_slot S.hc (r + 1)))) x[m] q) (M.vote_time S.E ((M.opening_slot S.hc (r + 1)))) ⇢ out)
    (hneTick : ∀ (n' : Nat) (t' : Int), Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' →
      t' ≤ M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out) :
    Block.compatible hs.live_confirmed T.erase = true := by
  rcases compatible_cases hAB with hAT | hTA
  · exact Restated.live_confirmed_compatible_at_action_afterPhase facts S Sched x hexec hsync hmult htd hmono
      hgst hcv hawake hthird hcs hlen hunder hunderS hsE hsR hn hv hprev c hc A hA hAT hpath hs hhs hF hJ
      hneTickVote hneTick
  · have haw : v ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) :=
      mem_awake_of_awakeThroughout Sched (Restated.hawT_of_honRound_succ facts S Sched hv le_rfl)
        (by have := S.E.Δ_pos; have := facts.gr.action_succ_eq_add_rounds S r
            have : (0 : Int) ≤ 4 * (S.hc.R : Int) * S.E.Δ := by positivity
            linarith) le_rfl
    exact Restated.live_confirmed_compatible_of_anchor_descendant facts S Sched x hn
      (Finset.mem_sdiff.2 ⟨haw, (Finset.mem_sdiff.1 hv).2⟩) c hc A hA hTA hs hhs hF hJ
      (hneTick n _ hn (Restated.action_emod_delta facts S (r + 1))
        (Finset.mem_sdiff.2 ⟨haw, (Finset.mem_sdiff.1 hv).2⟩)
        (Restated.confirmation_time_opening_slot facts S (r + 1)).symm.le)
      -- the grade-2 awake test at `v`'s confirmation tick: that instant is round `r + 1`'s action
      -- instant, the slot after the opening slot is in round `r + 1`, and `v` is awake through
      -- `wAttest S ≥ 12Δ` before it, which covers the grade-2 window
      (by
        have hround : M.round_of S.hc (M.opening_slot S.hc (r + 1) + 1) = r + 1 :=
          facts.gr.round_of_opening_slot_add S.hc (r + 1)
            (lt_of_lt_of_le (by norm_num) S.hc.R_ge_three)
        rw [hround, Restated.confirmation_time_opening_slot facts S (r + 1)]
        obtain ⟨τ, hlbl, hτ⟩ := hn
        refine Restated.run_fact_g2 facts S Sched x n τ (r + 1) v hlbl hτ ?_ (by
          -- `v` is awake and not held at `S.a (r + 1)`, so by monotone corruption it is not held
          -- at any instant up to it
          rw [hτ]
          exact Restated.honest_upTo_of_mono hmono (Finset.mem_sdiff.2 ⟨haw, (Finset.mem_sdiff.1 hv).2⟩))
        have hw := (Finset.mem_sdiff.1 hv).1
        have h12 := twelve_delta_le_wAttest S
        simp only [Restated.activeRoundW, Schedule.awakeThroughout, Finset.mem_inf,
          Finset.mem_Icc] at hw ⊢
        rw [facts.gr.early_g2_eq S (r + 1)]
        intro t ht
        exact hw t ⟨by linarith [ht.1], ht.2⟩)

end

end DecoupledConsensusModel.Sts.Restated
