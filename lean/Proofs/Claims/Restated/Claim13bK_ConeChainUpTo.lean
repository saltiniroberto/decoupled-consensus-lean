import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConeAnchor
import Proofs.Claims.Restated.Claim13bK_ConeAnchorUpTo
import Proofs.Claims.Restated.Claim13bK_ConeChain
import Proofs.Claims.Restated.Claim13bK_ConeSlotsUpTo
import Proofs.Claims.Restated.Claim13bK_FgJustified
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bK_GradeOldHeadsUpTo
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.Claim13beRoute3_5
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsFacts
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.Projection
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_GradeOldHeads
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Claim13beRoute3_5
import Model.Conditions.Claim13beRoute3_7
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
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
import Proofs.Claims.Restated.WakeWindow
import Proofs.Claims.Restated.Claim13bK_ConeAnchorUpToRecv

/-!
# The chain from the SG root to a held block is in the voter tree, synchrony up to a bound

Over a model `M : Record.Model V`, with synchrony assumed only up to a bound:
`ConeAnchorChainInTree` at a block an honest validator holds, the SG root of an opening-slot
confirmation read on one chain with the anchor, and the confirmed block of an action read on one
chain with a block.
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

/-- With synchrony only up to `t`: if `v_1` holds `B` at step `m`, whose instant is at or after
    `tGAT`, every finalized block of a validator honest through a step at or before `tR` is an
    ancestor of `B`, `t` is more than a delay after step `m`'s instant and at or before both `tR`
    and step `mr`'s instant, and `v` is honest through `mr` and awake at every instant of
    `[t − 2Δ, t]`, then every ancestor `C` of `B`'s erasure is in `v`'s tree after `mr` steps, with
    a stamp strictly before `t`. The hypothesis `hneTick` asks that `v`'s tick have an outcome at
    every whole multiple of `Δ` from the start of `C`'s slot to step `mr`'s instant at which `v` is
    awake and not held. -/
theorem chain_in_reader_tree_of_holder_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {t : Int} (hsync : Restated.SynchronyFromWakeBefore M S x t)
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
    {v : V} {mr : Nat} (hdeadline : (x[m].time : Int) + S.E.Δ < t)
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
    Restated.block_in_tree_of_holder_afterPhase_ofAdmits_upTo facts S Sched x hexec hsync hmult htd hmono hgst hcv
      hawake hthird hcs hlen hadm hadmS hD hv_1 hm hdeadline hΓR hmr (hvh _ le_rfl) hwaw
      (by rw [hDe]; exact hneTick)
  rw [hDe] at hmem hσ
  exact ⟨hmem, σ, hσ, hσlt⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If synchrony from wake holds for every send whose deadline is at or before `b'`, and `b ≤ b'`,
    then it holds for every send whose deadline is at or before `b`. -/
private theorem synchronyFromWakeBefore_mono {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {b b' : Int} (hb : b ≤ b')
    (hs : Restated.SynchronyFromWakeBefore M S x b') : Restated.SynchronyFromWakeBefore M S x b :=
  fun k w sm hsend hle haw => hs k w sm hsend (le_trans hle hb) haw

/-- Slot `s`'s view freeze is at most two delays before slot `s + 1`'s vote instant. -/
private theorem view_freeze_le_vote_time_succ_sub (facts : Record.Facts M) (S : Setup V)
    (s : Slot) :
    M.view_freeze S.E s ≤ M.vote_time S.E (s + 1) - 2 * S.E.Δ := by
  have hd := S.E.Δ_pos
  have hvt1 := facts.sch.slotStart_add_delta_eq_vote_time S.E (s + 1)
  have hss := slotStart_succ S.E.Δ s
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

/-- With synchrony only up to slot `s`'s view freeze: if `v_1` holds `B` at step `m`, whose instant
    is at or after `tGAT` and more than a delay before slot `s`'s view freeze, every finalized block
    of a validator honest through a step at or before `tR` is an ancestor of `B`, every store's
    `h_max` at such a step is at most one more than `B`'s chain-state height, and slot `s + 1`'s
    vote instant is at most `tR + 1`, then `ConeAnchorChainInTree S x B.erase s`: every block
    strictly between an honest active voter's SG root and `B` is in that voter's slot-`(s + 1)`
    voter tree. The hypothesis `hneTickW` asks that the tick of every validator of
    `HonSlot S Sched (s + 1)` have an outcome at every whole multiple of `Δ` before slot `s + 1`'s
    vote instant at which it is awake and not held. -/
theorem coneAnchorChainInTree_of_holder_of_bounds_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot} (hsync : Restated.SynchronyFromWakeBefore M S x (M.view_freeze S.E s))
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
    (hdeadline : (x[m].time : Int) + S.E.Δ < M.view_freeze S.E s)
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
  have hvf_le := view_freeze_le_vote_time_succ_sub facts S s
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
    Restated.chain_in_reader_tree_of_holder_upTo facts S Sched x hexec hsync hmult htd hmono hgst hcv hawake hthird
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

/-- With synchrony only up to `S.a (r + 1)`: if round `r` is at or after the switch round, the
    invariant holds at round `r` with anchor `T`, `v_1` holds `B` at step `m`, whose instant is at
    or after `tGAT` and more than a delay before slot `s`'s view freeze, `T` is an ancestor of `B`
    and `B`'s chain-state height is at least `T`'s, and slot `s + 1` is at most one slot after round
    `r + 1`'s opening slot, then every block strictly between an honest active voter's SG root and
    `B` is in that voter's slot-`(s + 1)` voter tree. The hypothesis `hneTickW` is that of
    `coneAnchorChainInTree_of_holder_of_bounds_upTo`. -/
theorem coneAnchorChainInTree_of_holder_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {n : Nat} {T : NamedBlock V}
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
  have hvf_le := view_freeze_le_vote_time_succ_sub facts S s
  exact Restated.coneAnchorChainInTree_of_holder_of_bounds_upTo facts S Sched x hexec
    (synchronyFromWakeBefore_mono (by linarith) hsync) hmult htd hmono
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

/-- With synchrony only up to `S.a (r + 1)`: if round `r` is at or after the switch round, the
    invariant holds at round `r` with anchor `T`, step `n'` is the sts tick at `S.a (r + 1)`, and
    `v` is in `HonRound S Sched (r + 1)`, then for every outcome `c` of the phase tick of `v`'s
    confirmation read of round `r + 1`'s opening slot, every SG root the read can start from under
    `c`'s grade contract lies on one chain with `T`. The hypotheses `hneTick` and `hneAtt` ask that
    `v`'s tick have an outcome at every whole multiple of `Δ` up to `S.a (r + 1)` at which `v` is
    awake and not held, and that `M.tick` on every honest active attester of round `r` at `S.a r`
    have an outcome. -/
theorem confAnchor_compatible_at_honRound_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {n : Nat} {T : NamedBlock V}
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
    (hrecvR : Restated.NextRoundReceipts M S Sched x r)
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
    have hawT := Restated.awakeThroughout_late_domain_of_honRound_succ facts S Sched hv hdom
    have hvS : v ∉ Sched.adv (M.domain S.E S.hc (r + 1) .g1) := fun hin =>
      hvadv (hmono _ _ hdom hin)
    obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
      (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g1)
      (M.late S.E S.hc (r + 1) .g1) B
    have hbt := hB b hb
    subst hbt
    exact Protocol.compatible_of_preceq_of_compatible hpre
      (Restated.grade1_compatible_at_awakeReader_upTo_recv facts (hcross := hcross) S Sched x tE hexec hmono htd
        (synchronyFromWakeBefore_mono (le_trans (facts.gr.late_le_domain S (r + 1) .g1) hdom) hsync)
        hmult tGAT gap hgst
        hlen hcv hthird hphase hrsW hcs hr hinv hdom _ le_rfl hawT
        (hrecvR.at facts hv .g1) hvS hm B hb hneTick hneAtt)
  · exact compatible_of_preceq_common_Preceq
      (Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE hexec hmono tGAT gap hgst hlen
        hthird hphase hrsW hr hinv hn' v n' le_rfl hvn) (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
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

/-- With synchrony only up to the support cutoff of round `r + 1`'s opening slot: when the SG root
    `A` of `v`'s confirmation read of round `r + 1`'s opening slot lies on one chain with `T` (and
    is not necessarily an ancestor of it), the confirmed block every store `hs` of `v`'s
    round-`(r + 1)` action read holds lies on one chain with `T`. The hypotheses `hneTickVote` and
    `hneTick` ask for tick outcomes: of every honest active member of the opening slot's committee
    at its vote instant, and of `v` at every whole multiple of `Δ` up to the opening slot's
    confirmation instant at which `v` is awake and not held. -/
theorem live_confirmed_compatible_at_action_afterPhase_ofCompatible_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r : Round}
    (hsync : Restated.SynchronyFromWakeBefore M S x (M.support_cutoff S.E ((M.opening_slot S.hc (r + 1)))))
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int} (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE)
    {n : Nat} {v : V} {T : NamedBlock V}
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
  · exact Restated.live_confirmed_compatible_at_action_afterPhase_upTo facts S Sched x hexec hsync hmult htd hmono
      hgst hcv hawake hthird hcs hlen hunder hunderS hsE hsR hn hv hprev c hc A hA hAT hpath hs hhs hF hJ
      hneTickVote hneTick
  · have haw : v ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) :=
      Restated.awake_action_of_mem_honRound facts hv
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
        obtain ⟨τ, hlbl, hτ⟩ := id hn
        refine Restated.run_fact_g2 facts S Sched x n τ (r + 1) v hlbl hτ ?_ (by
          -- `v` is awake and not held at `S.a (r + 1)`, so by monotone corruption it is not held
          -- at any instant up to it
          rw [hτ]
          exact Restated.honest_upTo_of_mono hmono (Finset.mem_sdiff.2 ⟨haw, (Finset.mem_sdiff.1 hv).2⟩))
        have hw := (Finset.mem_sdiff.1 hv).1
        have h12 := twelve_delta_le_wAttest S
        simp only [Restated.activeRoundW, Restated.attestersAt, Schedule.awakeThroughout, Finset.mem_inf,
          Finset.mem_Icc] at hw ⊢
        try rw [facts.gr.early_g2_eq S (r + 1)] at hw
        rw [facts.gr.early_g2_eq S (r + 1)]
        intro t ht
        exact hw t ⟨by linarith [ht.1], ht.2⟩)

end

end DecoupledConsensusModel.Sts.Restated
