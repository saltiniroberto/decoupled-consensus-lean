import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.ReceiptOutcome
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConeCover
import Proofs.Claims.Restated.Claim13bK_ConeHeads
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Claim13bRelay
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.Claim13beRoute3_5
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsFacts
import Proofs.Claims.Restated.Constants
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.VocabularyAssumptionsLemmas
import Proofs.Claims.Restated.Vocabulary_Internal_Legacy_Instance
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bK_GradeOld
import Model.Conditions.Claim13bK_GradeOldHeads
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13beRoute3_5
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.ProcessedFlip
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Statements_Instantiation_RoundTimes
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.WakeWindow

/-!
# Fresh SG blocks reach the next round's attesters

Theorems carrying a block an honest validator sent or holds into the tree of a validator that admits
it, and from them `FreshSGHeadsAtLate` and the grade-1 condition at round `r + 1`, from the premises
and the round-`r` invariant alone.
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

/-- If `B`, not genesis, is in some validator's tree at a step no later than `d`, and `B` is
    delivered at step `d`, at an instant in `[tGAT, tR]`, to a validator `v` honest through `d` that
    admits `B` in that window, then `B` is among `v`'s bodies after step `d`. -/
theorem block_admitted_of_deliver_ofAdmits (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    {tGAT tR : Int} {d n : Nat} {v v_0 v' : V} {B : NamedBlock V}
    (hadm : Restated.ReaderAdmitsInPhase M S Sched x tGAT tR v B)
    (hlbl : x.lbl d
      = AtomicAction.deliver v (⟨v_0, NamedObject.block B⟩ : SignedMsg V (NamedObject V)))
    (hvh : Restated.HonestThrough M Sched x d v)
    (hmem : B.erase ∈ (x[n][v'].st).st.core.T) (hgen : B ≠ NamedBlock.genesis)
    (hnd : (x[n].time : Int) ≤ (x[d].time : Int))
    (hlo : tGAT ≤ (x[d].time : Int)) (hhi : (x[d].time : Int) ≤ tR)
    (hneTick : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → v ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ B.erase.slot ≤ t → t ≤ (x[d].time : Int) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t x[n'] v) t ⇢ out) :
    B ∈ (x[d + 1][v].st).st.bodies := by
  rcases hadm d v_0 hlbl hvh hlo hhi with hF | hheld
  · exact Restated.block_admitted_of_deliver_of_tree facts S Sched x hexec hlbl hvh hmem hgen
      (Restated.deliver_slot_ok_afterPhase facts S Sched x hmult htd hlbl hmem hnd hvh hneTick) hF
  · exact of_decide_eq_true (Restated.processed_mono facts S Sched x v (NamedObject.block B)
      (Nat.le_succ d) (decide_eq_true hheld))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `B` was honestly sent at step `k`, at or after GST and `tGAT`, and `v` admits `B`, is awake
    throughout `[x[k].time, x[k].time + Δ]` and is not held at step `mr`, with
    `x[k].time + Δ ≤ t ≤ x[mr].time`, then `B` is in `v`'s tree at step `mr` with a stamp strictly
    before `t`. -/
theorem block_in_tree_of_honestSend_window_ofAdmits (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tR : Int}
    {k mr n : Nat} {v_0 v v' : V} {B : NamedBlock V} {t : Int}
    (hadm : Restated.ReaderAdmitsInPhase M S Sched x tGAT tR v B)
    (hsend : Restated.HonestSendAt M S x k (⟨v_0, NamedObject.block B⟩ : SignedMsg V (NamedObject V)))
    (hgst : S.E.t_GST ≤ (x[k].time : Int)) (hklo : tGAT ≤ (x[k].time : Int))
    (hmem : B.erase ∈ (x[n][v'].st).st.core.T) (hgen : B ≠ NamedBlock.genesis)
    (hnk : (x[n].time : Int) ≤ (x[k + 1].time : Int))
    (hdl : (x[k].time : Int) + S.E.Δ ≤ t)
    (hΓR : t ≤ tR) (hmr : t ≤ (x[mr].time : Int))
    (hw : v ∉ Sched.adv (x[mr].time : Int))
    (hwin : v ∈ Sched.awakeThroughout (x[k].time : Int) ((x[k].time : Int) + S.E.Δ))
    (hneTick : ∀ (n' : Nat) (t' : Int), Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' →
      slotStart S.E.Δ B.erase.slot ≤ t' → t' ≤ (x[mr].time : Int) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out) :
    B.erase ∈ (x[mr][v].st).st.core.T ∧
      ∃ σ : Stamp, (x[mr][v].st).st.core.timestamp_block B.erase = some σ ∧
        σ < (t : Stamp) := by
  have hd := S.E.Δ_pos
  have hmax : max (x[k].time : Int) S.E.t_GST = (x[k].time : Int) := max_eq_left hgst
  obtain ⟨d, hkd, hdlt, hdlbl⟩ := Restated.deliver_of_honestSendAt facts S Sched x hsync
    (D := t) hsend (by rw [hmax]; exact hdl) (by rw [hmax]; exact hwin)
  have hkd1 : k + 1 ≤ d := hkd
  have hk1d : (x[k + 1].time : Int) ≤ (x[d].time : Int) := Restated.time_mono_int facts S Sched x hkd1
  have hkd' : (x[k].time : Int) ≤ (x[d].time : Int) :=
    le_trans (Restated.time_mono_int facts S Sched x (Nat.le_succ k)) hk1d
  have hdmr' : (x[d].time : Int) ≤ (x[mr].time : Int) := le_trans (le_of_lt hdlt) hmr
  have hwh : Restated.HonestThrough M Sched x d v := by
    intro t' ht' hin
    exact hw (hmono t' _ (le_trans ht' hdmr') hin)
  have hbody : B ∈ (x[d + 1][v].st).st.bodies :=
    Restated.block_admitted_of_deliver_ofAdmits facts S Sched x hexec hmult htd hadm hdlbl hwh hmem hgen
      (le_trans hnk hk1d) (le_trans hklo hkd') (le_trans (le_of_lt hdlt) hΓR)
      (fun n' t' h1 hΔ hq h2 h3 => hneTick n' t' h1 hΔ hq h2 (le_trans h3 hdmr'))
  have hdtime : (x[d + 1].time : Int) = (x[d].time : Int) := by
    exact_mod_cast congrArg (fun m : Nat => (m : Int)) (Restated.deliver_time facts S Sched x hdlbl)
  have hdmr : d + 1 ≤ mr := by
    by_contra hcon
    have hle : mr ≤ d := by omega
    have hm := Restated.time_mono_int facts S Sched x hle
    linarith
  have hbodymr : B ∈ (x[mr][v].st).st.bodies :=
    of_decide_eq_true (Restated.processed_mono facts S Sched x v (NamedObject.block B) hdmr
      (decide_eq_true hbody))
  refine ⟨?_, ?_⟩
  · rw [Restated.bodies_image_eq_T facts S Sched x mr v]
    exact Finset.mem_image_of_mem NamedBlock.erase hbodymr
  · have hmemTd : B.erase ∈ (x[d + 1][v].st).st.core.T := by
      rw [Restated.bodies_image_eq_T facts S Sched x (d + 1) v]
      exact Finset.mem_image_of_mem NamedBlock.erase hbody
    obtain ⟨σ, hσ, hσlt⟩ :=
      Restated.block_stamp_lt_of_time facts S Sched x (d + 1) v hmemTd (by rw [hdtime]; exact hdlt)
    exact ⟨σ, Restated.block_stamp_carry facts S Sched x hdmr v hσ, hσlt⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After GST, a block an honest validator put on the wire is in the tree of every validator that
    admits it, is awake throughout `[t − 2Δ + 1, t]` and is not held at the reading step, with a
    stamp strictly before `t`. -/
theorem block_in_tree_of_honestSend_afterPhase_ofAdmits (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tR : Int}
    {k mr n : Nat} {v_0 v v' : V} {B : NamedBlock V} {t : Int}
    (hadm : Restated.ReaderAdmitsInPhase M S Sched x tGAT tR v B)
    (hsend : Restated.HonestSendAt M S x k (⟨v_0, NamedObject.block B⟩ : SignedMsg V (NamedObject V)))
    (hgst : S.E.t_GST ≤ (x[k].time : Int)) (hklo : tGAT ≤ (x[k].time : Int))
    (hcover : ∀ t' : Int, (x[k].time : Int) ≤ t' → HonestAwakeCover S Sched t')
    (hmem : B.erase ∈ (x[n][v'].st).st.core.T) (hgen : B ≠ NamedBlock.genesis)
    (hnk : (x[n].time : Int) ≤ (x[k + 1].time : Int))
    (hdl : (x[k].time : Int) + S.E.Δ ≤ t)
    (hΓR : t ≤ tR) (hmr : t ≤ (x[mr].time : Int))
    (hw : v ∉ Sched.adv (x[mr].time : Int))
    (hwaw : v ∈ Sched.awakeThroughout (t - 2 * S.E.Δ + 1) t)
    (hneTick : ∀ (n' : Nat) (t' : Int), Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' →
      slotStart S.E.Δ B.erase.slot ≤ t' → t' ≤ (x[mr].time : Int) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out) :
    B.erase ∈ (x[mr][v].st).st.core.T ∧
      ∃ σ : Stamp, (x[mr][v].st).st.core.timestamp_block B.erase = some σ ∧
        σ < (t : Stamp) := by
  have hd := S.E.Δ_pos
  by_cases hcase : t - 2 * S.E.Δ + 1 ≤ (x[k].time : Int)
  · exact Restated.block_in_tree_of_honestSend_window_ofAdmits facts S Sched x hexec hsync hmult htd hmono
      hadm hsend hgst hklo hmem hgen hnk hdl hΓR hmr hw
      (awakeThroughout_mono Sched hwaw hcase hdl) hneTick
  · have hlt : (x[k].time : Int) < t - 2 * S.E.Δ + 1 := not_le.mp hcase
    obtain ⟨k', v'', hs', h1, h2⟩ :=
      Restated.honestSend_recurs facts S Sched x hsync htd hsend hgst hcover
        (fun _ _ _ hl =>
          Restated.receipt_outcome_of_deliver_mono facts S Sched x hexec.idealization hmono hl)
        (t - 2 * S.E.Δ + 1) (le_of_lt hlt)
    have hkk : k < k' := by
      by_contra hcon
      have hle : k' ≤ k := not_lt.mp hcon
      have := Restated.time_mono_int facts S Sched x hle
      linarith
    have hk1 : (x[k + 1].time : Int) ≤ (x[k' + 1].time : Int) :=
      Restated.time_mono_int facts S Sched x (Nat.succ_le_succ (le_of_lt hkk))
    have hkt : (x[k].time : Int) ≤ (x[k'].time : Int) := Restated.time_mono_int facts S Sched x (le_of_lt hkk)
    exact Restated.block_in_tree_of_honestSend_window_ofAdmits facts S Sched x hexec hsync hmult htd hmono
      hadm hs' (le_trans hgst hkt) (le_trans hklo hkt) hmem hgen (le_trans hnk hk1)
      (by linarith) hΓR hmr hw (awakeThroughout_mono Sched hwaw h1 (by linarith)) hneTick

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A block an honest validator holds at an instant at or after `tGAT` is in the tree of every
    validator that admits it, is awake throughout `[t − 2Δ + 1, t]` and is not held at the reading
    step, with a stamp strictly before `t`, when `t` is more than a delay after the holding. -/
theorem block_in_tree_of_holder_afterPhase_ofAdmits (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
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
    {m mr : Nat} {v' v : V} {B : NamedBlock V} {t : Int}
    (hadm : Restated.ReaderAdmitsInPhase M S Sched x tGAT tR v B)
    (hadmS : Restated.ReaderAdmitsAtStepsInPhase M S Sched x tGAT tR v B)
    (hB : B ∈ (x[m][v'].st).st.bodies)
    (hq : Restated.HonestThrough M Sched x m v')
    (hlo : tGAT ≤ (x[m].time : Int))
    (hdeadline : (x[m].time : Int) + S.E.Δ < t)
    (hΓR : t ≤ tR) (hmr : t ≤ (x[mr].time : Int))
    (hw : v ∉ Sched.adv (x[mr].time : Int))
    (hwaw : v ∈ Sched.awakeThroughout (t - 2 * S.E.Δ) t)
    (hneTick : ∀ (n' : Nat) (t' : Int), Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' →
      slotStart S.E.Δ B.erase.slot ≤ t' → t' ≤ (x[mr].time : Int) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out) :
    B.erase ∈ (x[mr][v].st).st.core.T ∧
      ∃ σ : Stamp, (x[mr][v].st).st.core.timestamp_block B.erase = some σ ∧
        σ < (t : Stamp) := by
  classical
  have hd := S.E.Δ_pos
  have hwaw' : v ∈ Sched.awakeThroughout (t - 2 * S.E.Δ + 1) t :=
    awakeThroughout_mono Sched hwaw (by linarith only) le_rfl
  have hcov : ∀ t' : Int, tGAT ≤ t' → HonestAwakeCover S Sched t' := fun t' ht' =>
    Restated.honestAwakeCover_of_premises facts S Sched hmono hgst hthird hawake hcs ht'
  have hFst : ∀ d : Nat, (x[d].time : Int) = tGAT + S.E.Δ → Restated.HonestThrough M Sched x d v →
      Block.compatible (x[d][v].st).st.core.F B.erase = true ∨ B ∈ (x[d][v].st).st.bodies :=
    fun d hdt' hvd => (hadmS d hvd (by linarith) (by linarith)).imp
      (fun h => compatible_of_cases (Or.inl (preceq_eq_true_iff_Preceq.mp h))) id
  by_cases hgen : B = NamedBlock.genesis
  · subst hgen
    have hgb : (NamedBlock.genesis : NamedBlock V) ∈ (x[mr][v].st).st.bodies :=
      ((Restated.nodeInvariant_sts facts S Sched x mr v).1.1.1.2.2.1).1
    refine ⟨?_, ⊥, ?_, WithBot.bot_lt_coe t⟩
    · rw [Restated.bodies_image_eq_T facts S Sched x mr v]
      exact Finset.mem_image_of_mem NamedBlock.erase hgb
    · refine Restated.block_stamp_carry facts S Sched x (Nat.zero_le mr) v ?_
      have hge : (NamedBlock.genesis : NamedBlock V).erase = Block.genesis := erase_named_genesis
      rw [Record.st_zero M S Sched x v, hge]
      exact facts.nd.initial_timestamp_genesis _ _
  have h0 : Restated.Vocabulary.Execution.Object.processed M (x[0][v'].st).st
      (NamedObject.block B) = false := by
    rw [Record.st_zero M S Sched x v']
    simp only [Restated.Vocabulary.Execution.Object.processed, facts.nd.initial_st,
      facts.hd.initial_bodies, Finset.mem_singleton]
    exact decide_eq_false hgen
  obtain ⟨i, him, hf0, hf1⟩ :=
    Restated.exists_flip_of_processed facts S Sched x v' (NamedObject.block B) h0
      (decide_eq_true hB)
  have hbodyi : B ∈ (x[i + 1][v'].st).st.bodies := of_decide_eq_true hf1
  have hmemi : B.erase ∈ (x[i + 1][v'].st).st.core.T := by
    rw [Restated.bodies_image_eq_T facts S Sched x (i + 1) v']
    exact Finset.mem_image_of_mem NamedBlock.erase hbodyi
  have hqT : HonestThroughTime Sched tGAT v' := fun t' ht => hq t' (le_trans ht hlo)
  have himt : (x[i].time : Int) ≤ (x[m].time : Int) := Restated.time_mono_int facts S Sched x (le_of_lt him)
  have hqi : Restated.HonestThrough M Sched x i v' := fun t' ht => hq t' (le_trans ht himt)
  have hgap : tGAT + S.E.Δ < t := by linarith only [hlo, hdeadline]
  have hiΔ : (x[i].time : Int) + S.E.Δ < t := by linarith only [himt, hdeadline]
  rcases Restated.flip_step_cases facts S Sched x hf0 hf1 with
    ⟨sm, hlbl, -, -, hpay⟩ | ⟨τ, hlbl, haw, hdvd, hem⟩
  ·
    rcases hpay with hmsg | ⟨Bl, -, hcc⟩
    · obtain ⟨u, o⟩ := sm
      have hmsg' : o = NamedObject.block B := hmsg
      subst hmsg'
      have hdt := (Nat.cast_inj (R := Int)).mpr (Restated.deliver_time facts S Sched x hlbl)
      rcases le_or_gt (x[i].time : Int) tGAT with hearly | hlate
      · exact Restated.block_in_tree_of_narrowedCommonView_afterPhase facts S Sched x hexec htd hmono hcv
          hawake hlen hbodyi hqT (by rw [hdt]; exact hearly) hgap hmr hw hFst
      · obtain ⟨k, hkt, hsend⟩ := Restated.block_onWire_of_deliver_phase facts S Sched x hlbl hqi
          (Restated.sent_of_deliver facts S Sched x hlbl).2
          (Restated.receipt_outcome_of_flip facts S Sched x hlbl hf0 hf1)
        have hnk := hdt.trans_le (hkt.symm.trans_le
          (Restated.time_mono_int facts S Sched x (Nat.le_succ k)))
        have hklo := le_of_lt (hlate.trans_eq hkt.symm)
        exact Restated.block_in_tree_of_honestSend_afterPhase_ofAdmits facts S Sched x hexec hsync hmult
          htd hmono hadm hsend (le_trans hgst hklo) hklo (fun t' ht' => hcov t' (le_trans hklo ht'))
          hmemi hgen hnk (by rw [hkt]; exact le_of_lt hiΔ) hΓR hmr hw hwaw' hneTick
    · exact hcc.elim
  ·
    obtain ⟨hτ, hτ'⟩ := Restated.tickAllAwake_time facts S Sched x hlbl
    have hdt := (Nat.cast_inj (R := Int)).mpr (hτ'.trans hτ.symm)
    push_cast at hdt
    obtain ⟨out₁, hout₁, hst₁, hem'⟩ := hem
    rcases hem' with hemit | ⟨Bl, -, hcc⟩
    · rcases lt_or_ge (x[i].time : Int) tGAT with hearly | hlate
      · exact Restated.block_in_tree_of_narrowedCommonView_afterPhase facts S Sched x hexec htd hmono hcv
          hawake hlen hbodyi hqT (by rw [hdt]; exact Int.add_one_le_of_lt hearly) hgap hmr hw hFst
      · have hsend := Restated.block_honestSend_at_tick facts S Sched x hqi hlbl haw hdvd
          ⟨out₁, hout₁, hst₁, hemit⟩
        exact Restated.block_in_tree_of_honestSend_afterPhase_ofAdmits facts S Sched x hexec hsync hmult
          htd hmono hadm hsend (le_trans hgst hlate) hlate (fun t' ht' => hcov t' (le_trans hlate ht'))
          hmemi hgen (le_refl _) (le_of_lt hiΔ) hΓR hmr hw hwaw' hneTick
    · exact hcc.elim

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `m` is the last step strictly before `domain (r + 1) p`, the instant of step `m` is at least
    `domain (r + 1) p − 1`. -/
theorem domain_sub_one_le_time_of_stepBefore (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) {r : Round} {m : Nat}
    {p : Protocol.Phase} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p)) :
    M.domain S.E S.hc (r + 1) p - 1 ≤ (x[m].time : Int) := by
  have hdom := Restated.action_delta_lt_domain_succ facts S r p
  have hpos : 0 < M.domain S.E S.hc (r + 1) p - 1 := by
    have h1 := Restated.action_pos facts S r
    have h2 : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
    linarith
  obtain ⟨k, hk⟩ := Restated.exists_tickStepAt facts x htd hpos
  obtain ⟨hk1, -⟩ := Restated.tickStepAt_time facts x hk
  have hkm : k < m := by
    by_contra hcon
    have h := hm.2 k (Nat.le_of_not_lt hcon)
    rw [hk1] at h
    linarith
  rw [← hk1]
  exact Restated.time_mono_int facts S Sched x hkm

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If GST is at or before `tGAT` and `tGAT + healingLengthη M S gap ≤ tE`, then `tGAT` is at or
    before `Restated.switchOpening M S tE`. -/
theorem tGAT_le_switchOpening (facts : Record.Facts M) (S : Setup V) (tGAT tE : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) :
    tGAT ≤ Restated.switchOpening M S tE := by
  have hbig := Restated.switchRound_ge_of_healingLengthη facts S tGAT tE gap hgst hlen
  have hsw : Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT + 1 ≤ Restated.switchRound M S tE := by
    have h : Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT + 1
        ≤ Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT
          + Statements.Instantiation.finalityStartup S gap S.extraRounds
          + Statements.Instantiation.finalityDeadline S gap S.extraRounds
          + gap + 2 + S.hc.η_SG := by
      show (_ : Nat) ≤ _
      omega
    exact le_trans h hbig
  have hopen : M.opening S.E S.hc (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT + 1)
      ≤ Restated.switchOpening M S tE := facts.gr.Sts_opening_mono S hsw
  have hnext : Restated.Vocabulary.Execution.Setup.a M S (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT)
      ≤ M.opening S.E S.hc (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT + 1) := by
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three
      (Nat.lt_succ_self (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT))
    have h2 := facts.gr.early_g2_le_opening S (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT + 1)
    have hd := S.E.Δ_pos
    show M.a S.hc S.E.Δ _ ≤ _
    linarith only [h1, h2, hd]
  exact le_trans (Restated.Vocabulary.Statements.roundAt_spec facts S tGAT) (le_trans hnext hopen)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `tGAT + healingLengthη M S gap ≤ tE`, then `tGAT + Δ ≤ tE`. -/
theorem delta_le_of_healingLengthη (facts : Record.Facts M) (S : Setup V) {tGAT tE : Int} {gap : Nat}
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) : tGAT + S.E.Δ ≤ tE := by
  have hd := S.E.Δ_pos
  have hper : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
  have heq := Restated.healingLengthη_eq facts S gap
  have hmul : (0 : Int) ≤ (((Statements.Instantiation.finalityStartup S gap S.extraRounds : Nat)
      : Int) + ((Statements.Instantiation.finalityDeadline S gap S.extraRounds : Nat) : Int)
      + (gap : Int) + 3 + (S.hc.η_SG : Int)) * (Restated.constants M S).period :=
    mul_nonneg (by positivity) (le_of_lt hper)
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If every honest finalized block up to the tick step `n'` at `S.a (r + 1)` is an ancestor of `T`,
    then at every delivery of a descendant of `T` to a validator honest through the delivery, at an
    instant between `tGAT` and `S.a (r + 1) − 1`, the receiver's finalized block is an ancestor of
    the delivered block. -/
theorem deliveredDescendantUnderFinalized_anchor (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {n' : Nat} {T : NamedBlock V}
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hfin : ∀ (v : V) (n₁ : Nat), n₁ ≤ n' → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.F T.erase)
    (tGAT : Int) :
    Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1) T.erase := by
  intro d v v' B _ hvh _ hhi hTB
  have hdn : d ≤ n' := by
    by_contra hcon
    have hle : n' + 1 ≤ d := by omega
    have h1 := Restated.time_mono_int facts S Sched x hle
    rw [(Restated.tickStepAt_time facts x hn').1] at h1
    linarith
  exact preceq_eq_true_iff_Preceq.mpr (preceq_trans_Preceq (hfin v d hdn hvh) hTB)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If every honest finalized block up to the tick step `n'` at `S.a (r + 1)` is an ancestor of `T`,
    then at every step whose instant is between `tGAT` and `S.a (r + 1) − 1`, every validator honest
    through that step has a finalized block that is an ancestor of `T`. -/
theorem finalizedPreceqAtSteps_anchor (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {n' : Nat} {T : NamedBlock V}
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hfin : ∀ (v : V) (n₁ : Nat), n₁ ≤ n' → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.F T.erase)
    (tGAT : Int) :
    Restated.FinalizedPreceqAtStepsInPhase M S x tGAT ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1) T.erase := by
  intro d v hvh _ hhi
  have hdn : d ≤ n' := by
    by_contra hcon
    have hle : n' + 1 ≤ d := by omega
    have h1 := Restated.time_mono_int facts S Sched x hle
    rw [(Restated.tickStepAt_time facts x hn').1] at h1
    linarith
  exact hfin v d hdn hvh

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If round `r` is at or after the switch round and the invariant holds at round `r` with tick step
    `n` and anchor `T`, then `FreshSGHeadsAtLate` holds: at the last step `m` before each
    round-`(r + 1)` phase instant at or before `S.a (r + 1)`, the block named by the round-`r`
    attestation of every member of `freshAttestersW S Sched x r m` is in the tree of every member of
    `HonRound S Sched (r + 1)`, stamped before the phase's late cutoff and compatible with its
    finalized block. -/
theorem freshSGHeadsAtLate_of_premises (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    (hneTick : ∀ v ∈ Restated.HonRound M S Sched (r + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out)
    (hneAtt : ∀ v ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    Restated.FreshSGHeadsAtLate M S Sched x r n := by
  classical
  intro v hv p hdom m hm v_1 hv_1 C hCbody a ha hconf
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd r
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE hexec hmono tGAT gap
    hgst hlen hthird hphase hrsW hr hinv hn'
  have hn := hinv.tick
  have hn1 : (x[n + 1].time : Int) = (Restated.Vocabulary.Execution.Setup.a M S r) := (Restated.tickStepAt_time facts x hn).1
  have hn'1 : (x[n' + 1].time : Int) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := (Restated.tickStepAt_time facts x hn').1
  have ham : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[m].time : Int) := Restated.action_le_time_of_stepBefore facts S Sched x htd hm
  have htm : (x[m].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    Restated.time_le_action_succ_of_stepBefore facts S Sched x htd hdom hm
  have hlate : Restated.Vocabulary.Execution.Setup.a M S r + 3 * S.E.Δ ≤ M.late S.E S.hc (r + 1) p :=
    facts.gr.action_add_three_delta_le_late_succ S r p
  have hld := facts.gr.late_le_domain S (r + 1) p
  have hdm := Restated.domain_sub_one_le_time_of_stepBefore facts S Sched x htd hm
  have hopen : M.opening S.E S.hc r ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
    show _ ≤ M.a S.hc S.E.Δ r
    rw [facts.gr.opening_eq_proposal_time, facts.sch.a_eq_confirmation_time]
    exact facts.sch.proposal_time_le_confirmation_time _ _
  have htGAT : tGAT ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    le_trans (Restated.tGAT_le_switchOpening facts S tGAT tE gap hgst hlen)
      (le_trans (Restated.switchOpening_le_opening facts S hr) hopen)
  have hvS : v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := (Finset.mem_sdiff.1 hv).2
  have hvm : Restated.HonestThrough M Sched x m v := fun t ht hin =>
    hvS (hmono t _ (le_trans ht htm) hin)
  have hv1m : Restated.HonestThrough M Sched x m v_1 := Restated.honestThrough_of_mem_freshAttestersW facts hv_1
  have hv1n : Restated.HonestThrough M Sched x (n + 1) v_1 := fun t ht =>
    hv1m t (le_trans ht (by rw [hn1]; exact ham))
  have hqr : v_1 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)) := hv1m _ ham
  have hsent := Restated.fresh_attests facts S Sched x hn
    (Restated.freshAttestersW_subset_freshAttesters facts S Sched x r m hv_1) hqr
    (hneAtt v_1 (Restated.hfreshH_of_stepBefore facts S Sched x htd hm hv_1))
    (by
      have hw := ((Restated.mem_freshAttestersW facts).mp hv_1).1
      obtain ⟨τ, hlbl, hτ⟩ := id hn
      refine Restated.run_fact_g2 facts S Sched x n τ r v_1 hlbl hτ ?_ (by
        rw [hτ]
        exact fun t ht => hv1m t (le_trans ht ham))
      have h12 := twelve_delta_le_wAttest S
      have hΔ := S.E.Δ_pos
      simp only [Restated.activeRoundW, Schedule.awakeThroughout, Finset.mem_inf,
        Finset.mem_Icc] at hw ⊢
      rw [facts.gr.early_g2_eq S r]
      intro t ht
      exact hw t ⟨by linarith [ht.1], ht.2⟩) a ha
  have hCT : Block.compatible C.erase T.erase = true :=
    hinv.sg v_1 (Restated.hfreshH_of_stepBefore facts S Sched x htd hm hv_1) a
      (Restated.actionAttestationFrom_round facts (Setup.alwaysAwake S) _ v_1 r a ha)
      (Restated.actionAttestationFrom_val_index facts (Setup.alwaysAwake S) _ v_1 r a ha) hsent C
      hCbody hconf
  have hFC : ∀ (w : V) (d : Nat), d ≤ n' → Restated.HonestThrough M Sched x d w →
      Block.compatible (x[d][w].st).st.core.F C.erase = true := fun w d hd' hw =>
    Protocol.compatible_of_preceq_of_compatible (hfin w d hd' hw) (Protocol.compatible_comm hCT)
  have hmn' : m ≤ n' := Restated.stepBefore_le_tick facts x hm hn' (le_trans hdom le_rfl)
  have hlog : Restated.blockInLog M S Sched x C := Restated.blockInLog_of_mem_bodies facts S Sched hv1n hCbody
  have hadm : Restated.ReaderAdmitsInPhase M S Sched x tGAT ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1) v C := by
    intro d v_0 _ hvd _ hhi
    have hdn : d ≤ n' := by
      by_contra hcon
      have hle : n' + 1 ≤ d := by omega
      have h1 := Restated.time_mono_int facts S Sched x hle
      rw [hn'1] at h1
      linarith
    have hc := hFC v d hdn hvd
    rcases compatible_cases hc with hFCd | hCFd
    · exact Or.inl (preceq_eq_true_iff_Preceq.mpr hFCd)
    · exact Or.inr (Restated.mem_bodies_of_preceq_finalized facts S Sched x hexec hvd hlog hCFd)
  have hadmS : Restated.ReaderAdmitsAtStepsInPhase M S Sched x tGAT ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1) v C := by
    intro d hvd _ hhi
    have hdn : d ≤ n' := by
      by_contra hcon
      have hle : n' + 1 ≤ d := by omega
      have h1 := Restated.time_mono_int facts S Sched x hle
      rw [hn'1] at h1
      linarith
    have hc := hFC v d hdn hvd
    rcases compatible_cases hc with hFCd | hCFd
    · exact Or.inl (preceq_eq_true_iff_Preceq.mpr hFCd)
    · exact Or.inr (Restated.mem_bodies_of_preceq_finalized facts S Sched x hexec hvd hlog hCFd)
  have hwaw : v ∈ Sched.awakeThroughout
      (M.late S.E S.hc (r + 1) p - 1 - 2 * S.E.Δ) (M.late S.E S.hc (r + 1) p - 1) :=
    awakeThroughout_mono Sched (Restated.hawT_of_honRound_succ facts S Sched hv (le_refl ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))))
      (by linarith) (by linarith)
  obtain ⟨hmemT, σ, hσ, hσlt⟩ :=
    Restated.block_in_tree_of_holder_afterPhase_ofAdmits facts S Sched x hexec hsync hmult htd hmono hgst hcv
      hphase hthird hcs (Restated.delta_le_of_healingLengthη facts S hlen) hadm hadmS hCbody hv1n
      (by rw [hn1]; exact htGAT) (by rw [hn1]; linarith) (by linarith) (by linarith)
      (fun hin => hvS (hmono _ _ htm hin)) hwaw
      (fun n'' t' h1 hΔ hq _ h3 => hneTick v hv n'' t' h1 hΔ hq (le_trans h3 htm))
  refine ⟨?_, ?_, ?_⟩
  · rw [← Proofs.NamedWire.erase_root]
    exact Restated.find_of_mem_tree_honest facts S Sched x hexec hvm hmemT
  · exact stampedBefore_of_lt hσ (lt_of_lt_of_le hσlt (WithBot.coe_le_coe.mpr (by linarith)))
  · exact Protocol.compatible_comm (hFC v m hmn' hvm)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under the hypotheses of `freshSGHeadsAtLate_of_premises`, every block a member of
    `HonRound S Sched (r + 1)` can grade at least 1 for round `r + 1`, at a phase whose domain
    instant is at or before `S.a (r + 1)`, is compatible with `T`. -/
theorem gradeOld_of_premisesOnly (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    (hneTick : ∀ v ∈ Restated.HonRound M S Sched (r + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out)
    (hneAtt : ∀ v ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    ∀ v ∈ Restated.HonRound M S Sched (r + 1),
    ∀ p : Protocol.Phase, M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) →
    ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p) →
    ∀ B : Block V,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
          (M.late S.E S.hc (r + 1) p) B ⇢ true →
      Block.compatible B T.erase = true := by
  have hd := S.E.Δ_pos
  have hstep := facts.gr.action_succ_eq_add_rounds S r
  have hrounds : (0 : Int) ≤ 4 * (S.hc.R : Int) * S.E.Δ :=
    mul_nonneg (mul_nonneg (by norm_num) (Int.natCast_nonneg _)) (le_of_lt hd)
  have hle : Restated.Vocabulary.Execution.Setup.a M S r ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) := by
    linarith only [hstep, hrounds]
  exact Restated.gradeOld_of_premises facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync hthird hphase hrsW
    hr hinv
    (Restated.freshSGHeadsAtLate_of_premises facts (hcross := hcross) S Sched x tE hexec hmono htd hsync hmult tGAT gap hgst hlen
      hcv hthird hphase hrsW hcs hr hinv hneTick hneAtt)
    (fun v hv => hneTick v hv n _ hinv.tick (Restated.action_emod_delta facts S r)
      (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched
          (Restated.hawT_of_honRound_succ facts S Sched hv hle) le_rfl le_rfl,
        Restated.hwh_of_honRound_succ facts S Sched hmono hv⟩) hle) hneAtt

end

end DecoupledConsensusModel.Sts.Restated
