import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.ReceiptOutcome
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConeCover
import Proofs.Claims.Restated.Claim13bK_ConeCoverUpTo
import Proofs.Claims.Restated.Claim13bK_ConeHeads
import Proofs.Claims.Restated.Claim13bRelayUpTo
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.Claim13beRoute3_4
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.VocabularyAssumptionsLemmas
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13beRoute3_5
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.ProcessedFlip
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Honest blocks and heads reach a reader's tree, synchrony up to a bound

Over a model `M : Record.Model V`, with synchrony assumed only up to the instant the reader's tree
is read at: a block an honest validator sends or holds reaches a reader's tree, and the heads of a
slot's honest active committee members resolve in that tree.
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

/-- With synchrony only up to `t`: if an honest validator sends the named block `B` at step `k`, at
    or after GST and `tGAT`, `B`'s erasure is in the tree of the store `v'` holds after `n` steps,
    step `n`'s instant is at or before the instant of the step after the send, `B` is not genesis,
    `C` is an ancestor of `B`, `t` is at least a delay after the send and at or before both `tR` and
    the reading step's instant, and `v` is awake at every instant of `[x[k].time, x[k].time + Δ]`
    and not held by the adversary at the reading step, then `B`'s erasure is in `v`'s tree at the
    reading step, with a stamp strictly before `t`. The hypothesis `hneTick` asks that `v`'s tick
    have an outcome at every whole multiple of `Δ` from the start of `B`'s slot to the reading
    step's instant at which `v` is awake and not held. -/
theorem block_in_tree_of_honestSend_window_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {t : Int}
    (hsync : Restated.SynchronyFromWakeBefore M S x t) (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tR : Int}
    {C : Block V} (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT tR C)
    {k mr n : Nat} {v_0 v v' : V} {B : NamedBlock V}
    (hsend : Restated.HonestSendAt M S x k (⟨v_0, NamedObject.block B⟩ : SignedMsg V (NamedObject V)))
    (hgst : S.E.t_GST ≤ (x[k].time : Int)) (hklo : tGAT ≤ (x[k].time : Int))
    (hmem : B.erase ∈ (x[n][v'].st).st.core.T) (hgen : B ≠ NamedBlock.genesis)
    (hCB : Block.Preceq C B.erase)
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
  -- synchrony up to the send's deadline
  have hsync' : Restated.SynchronyFromWakeBefore M S x
      (max (x[k].time : Int) S.E.t_GST + S.E.Δ) :=
    fun k' w' sm hs hle haw => hsync k' w' sm hs (le_trans hle (by rw [hmax]; exact hdl)) haw
  obtain ⟨d, hkd, hdlt, hdlbl⟩ := Restated.deliver_of_honestSendAt_upTo facts S Sched x hsync'
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
    Restated.block_admitted_of_deliver_afterPhase facts S Sched x hexec hmult htd hunder hdlbl hwh hmem hgen
      hCB (le_trans hnk hk1d) (le_trans hklo hkd') (le_trans (le_of_lt hdlt) hΓR)
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

/-- With synchrony only up to `t`: if an honest validator sent the named block `B` at step `k`, at
    or after GST and `tGAT`, from then on some validator is always awake for a delay, `B`'s erasure
    is in some store's tree at a step whose instant is at or before the instant of the step after
    the send, `B` is not genesis, `C` is an ancestor of `B`, `t` is at least a delay after the send
    and at or before both `tR` and the reading step's instant, and `v` is awake at every instant of
    `[t − 2Δ, t]` and not held by the adversary at the reading step, then `B`'s erasure is in `v`'s
    tree at the reading step, with a stamp strictly before `t`. The hypothesis `hneTick` is that of
    `block_in_tree_of_honestSend_window_upTo`. -/
theorem block_in_tree_of_honestSend_afterPhase_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {t : Int}
    (hsync : Restated.SynchronyFromWakeBefore M S x t) (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tR : Int}
    {C : Block V} (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT tR C)
    {k mr n : Nat} {v_0 v v' : V} {B : NamedBlock V}
    (hsend : Restated.HonestSendAt M S x k (⟨v_0, NamedObject.block B⟩ : SignedMsg V (NamedObject V)))
    (hgst : S.E.t_GST ≤ (x[k].time : Int)) (hklo : tGAT ≤ (x[k].time : Int))
    (hcover : ∀ t' : Int, (x[k].time : Int) ≤ t' → HonestAwakeCover S Sched t')
    (hmem : B.erase ∈ (x[n][v'].st).st.core.T) (hgen : B ≠ NamedBlock.genesis)
    (hCB : Block.Preceq C B.erase)
    (hnk : (x[n].time : Int) ≤ (x[k + 1].time : Int))
    (hdl : (x[k].time : Int) + S.E.Δ ≤ t)
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
  have hd := S.E.Δ_pos
  by_cases hcase : t - 2 * S.E.Δ ≤ (x[k].time : Int)
  · exact Restated.block_in_tree_of_honestSend_window_upTo facts S Sched x hexec hsync hmult htd hmono hunder
      hsend hgst hklo hmem hgen hCB hnk hdl hΓR hmr hw
      (awakeThroughout_mono Sched hwaw hcase hdl) hneTick
  · have hlt : (x[k].time : Int) < t - 2 * S.E.Δ := not_le.mp hcase
    -- synchrony up to `t − Δ`
    have hsync' : Restated.SynchronyFromWakeBefore M S x (t - 2 * S.E.Δ + S.E.Δ) :=
      fun k' w' sm hs hle haw => hsync k' w' sm hs (le_trans hle (by linarith only [hd])) haw
    obtain ⟨k', v'', hs', h1, h2⟩ :=
      Restated.honestSend_recurs_upTo facts S Sched x (tEnd := t - 2 * S.E.Δ) hsync' htd
        hsend hgst hcover (fun _ _ _ hl =>
          Restated.receipt_outcome_of_deliver_mono facts S Sched x hexec.idealization hmono hl)
        (t - 2 * S.E.Δ) (le_of_lt hlt) le_rfl
    have hkk : k < k' := by
      by_contra hcon
      have hle : k' ≤ k := not_lt.mp hcon
      have := Restated.time_mono_int facts S Sched x hle
      linarith
    have hk1 : (x[k + 1].time : Int) ≤ (x[k' + 1].time : Int) :=
      Restated.time_mono_int facts S Sched x (Nat.succ_le_succ (le_of_lt hkk))
    have hkt : (x[k].time : Int) ≤ (x[k'].time : Int) := Restated.time_mono_int facts S Sched x (le_of_lt hkk)
    exact Restated.block_in_tree_of_honestSend_window_upTo facts S Sched x hexec hsync hmult htd hmono hunder
      hs' (le_trans hgst hkt) (le_trans hklo hkt) hmem hgen hCB (le_trans hnk hk1)
      (by linarith) hΓR hmr hw (awakeThroughout_mono Sched hwaw h1 (by linarith)) hneTick

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- With synchrony only up to `t`: if a validator the adversary has held at no instant up to step
    `m`'s instant holds the named block `B` there, `C` is an ancestor of `B`, that instant is at or
    after `tGAT`, `t` is more than a delay after it and at or before both `tR` and the reading
    step's instant, and `v` is awake at every instant of `[t − 2Δ, t]` and not held by the adversary
    at the reading step, then `B`'s erasure is in `v`'s tree at the reading step, with a stamp
    strictly before `t`. The hypothesis `hneTick` is that of
    `block_in_tree_of_honestSend_afterPhase_upTo`. -/
theorem block_in_tree_of_holder_afterPhase_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {t : Int}
    (hsync : Restated.SynchronyFromWakeBefore M S x t)
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int}
    (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE)
    {C : Block V} (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT tR C)
    (hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x tGAT tR C)
    {m mr : Nat} {v' v : V} {B : NamedBlock V}
    (hB : B ∈ (x[m][v'].st).st.bodies)
    (hq : Restated.HonestThrough M Sched x m v')
    (hCB : Block.Preceq C B.erase)
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
  have hd := S.E.Δ_pos
  have hgap : tGAT + S.E.Δ < t := by linarith only [hlo, hdeadline]
  have hlowΔ : tGAT ≤ tGAT + S.E.Δ := by linarith only [hd]
  have hhighΔ : tGAT + S.E.Δ ≤ tR := by linarith only [hgap, hΓR]
  have hFst : ∀ d : Nat, (x[d].time : Int) = tGAT + S.E.Δ → Restated.HonestThrough M Sched x d v →
      Block.compatible (x[d][v].st).st.core.F B.erase = true ∨ B ∈ (x[d][v].st).st.bodies :=
    fun d hdt' hvd => Or.inl (compatible_of_cases (Or.inl
      (preceq_trans_Preceq (hunderS d v hvd (hdt' ▸ hlowΔ) (hdt' ▸ hhighΔ)) hCB)))
  have hcov : ∀ t' : Int, tGAT ≤ t' → HonestAwakeCover S Sched t' := fun t' ht' =>
    Restated.honestAwakeCover_of_premises facts S Sched hmono hgst hthird hawake hcs ht'
  by_cases hgen : B = NamedBlock.genesis
  · subst hgen
    have hgb : (NamedBlock.genesis : NamedBlock V) ∈ (x[mr][v].st).st.bodies :=
      ((Restated.nodeInvariant_sts facts S Sched x mr v).1.1.1.2.2.1).1
    refine ⟨?_, ⊥, ?_, WithBot.bot_lt_coe t⟩
    · rw [Restated.bodies_image_eq_T facts S Sched x mr v]
      exact Finset.mem_image_of_mem NamedBlock.erase hgb
    · refine Restated.block_stamp_carry facts S Sched x (Nat.zero_le mr) v ?_
      rw [Record.st_zero M S Sched x v, erase_named_genesis]
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
  have himt := Restated.time_mono_int facts S Sched x (le_of_lt him)
  have hqi : Restated.HonestThrough M Sched x i v' := fun t' ht => hq t' (le_trans ht himt)
  have hiΔ : (x[i].time : Int) + S.E.Δ < t := by linarith only [himt, hdeadline]
  rcases Restated.flip_step_cases facts S Sched x hf0 hf1 with
    ⟨sm, hlbl, -, -, hpay⟩ | ⟨τ, hlbl, haw, hdvd, hem⟩
  · -- `B` was delivered to the holder at step `i`
    rcases hpay with hmsg | ⟨Bl, -, hcc⟩
    · obtain ⟨u, o⟩ := sm
      have hmsg' : o = NamedObject.block B := hmsg
      subst hmsg'
      have hdt := (Nat.cast_inj (R := Int)).mpr (Restated.deliver_time facts S Sched x hlbl)
      rcases le_or_gt (x[i].time : Int) tGAT with hearly | hlate
      · exact Restated.block_in_tree_of_narrowedCommonView_afterPhase facts S Sched x hexec htd hmono hcv
          hawake hlen
          hbodyi hqT (by rw [hdt]; exact hearly) hgap hmr hw hFst
      · obtain ⟨k, hkt, hsend⟩ := Restated.block_onWire_of_deliver_phase facts S Sched x hlbl hqi
          (Restated.sent_of_deliver facts S Sched x hlbl).2
          (Restated.receipt_outcome_of_flip facts S Sched x hlbl hf0 hf1)
        have hnk := hdt.trans_le (hkt.symm.trans_le
          (Restated.time_mono_int facts S Sched x (Nat.le_succ k)))
        have hklo := le_of_lt (hlate.trans_eq hkt.symm)
        exact Restated.block_in_tree_of_honestSend_afterPhase_upTo facts S Sched x hexec hsync hmult htd
          hmono hunder hsend (le_trans hgst hklo) hklo (fun t' ht' => hcov t' (le_trans hklo ht'))
          hmemi hgen hCB hnk (by rw [hkt]; exact le_of_lt hiΔ) hΓR hmr hw hwaw hneTick
    · exact hcc.elim
  · -- the holder's own tick at step `i` emitted `B`
    obtain ⟨hτ, hτ'⟩ := Restated.tickAllAwake_time facts S Sched x hlbl
    have hdt := (Nat.cast_inj (R := Int)).mpr (hτ'.trans hτ.symm)
    push_cast at hdt
    obtain ⟨out₁, hout₁, hst₁, hem'⟩ := hem
    rcases hem' with hemit | ⟨Bl, -, hcc⟩
    · rcases lt_or_ge (x[i].time : Int) tGAT with hearly | hlate
      · exact Restated.block_in_tree_of_narrowedCommonView_afterPhase facts S Sched x hexec htd hmono hcv
          hawake hlen
          hbodyi hqT (by rw [hdt]; exact Int.add_one_le_of_lt hearly) hgap hmr hw hFst
      · have hsend := Restated.block_honestSend_at_tick facts S Sched x hqi hlbl haw hdvd
          ⟨out₁, hout₁, hst₁, hemit⟩
        exact Restated.block_in_tree_of_honestSend_afterPhase_upTo facts S Sched x hexec hsync hmult htd
          hmono hunder hsend (le_trans hgst hlate) hlate (fun t' ht' => hcov t' (le_trans hlate ht'))
          hmemi hgen hCB (le_refl _) (le_of_lt hiΔ) hΓR hmr hw hwaw hneTick
    · exact hcc.elim

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every slot `s`, `slotStart s + 2Δ ≤ support_cutoff s`. -/
private theorem slotStart_add_two_delta_le_support_cutoff (facts : Record.Facts M)
    (S : Setup V) (s : Slot) :
    slotStart S.E.Δ s + 2 * S.E.Δ ≤ M.support_cutoff S.E s := by
  have hd := S.E.Δ_pos
  have hvt := facts.sch.slotStart_add_delta_eq_vote_time S.E s
  have hp0 : slotStart S.E.Δ s ≤ M.proposal_time S.E s :=
    slotStart_le_of_le_slotOf S (facts.sch.Sts_proposal_time_nonneg S s)
      (le_of_eq (facts.sch.slotOf_proposal_time S.E s).symm)
  have hpv := facts.sch.proposal_time_lt_vote_time S.E s
  have hc0 : slotStart S.E.Δ s ≤ M.support_cutoff S.E s :=
    slotStart_le_of_le_slotOf S (le_of_lt (facts.sch.support_cutoff_pos S s))
      (le_of_eq (facts.sch.slotOf_support_cutoff S.E s).symm)
  have hcp := facts.sch.support_cutoff_ne_proposal_time S.E s
  have hcv := facts.sch.support_cutoff_ne_vote_time S.E s
  obtain ⟨a, ha⟩ := Int.dvd_of_emod_eq_zero (slotStart_emod_delta S s)
  obtain ⟨b, hb⟩ := Int.dvd_of_emod_eq_zero (facts.sch.proposal_time_emod_delta_inclX S.E s)
  obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero (facts.sch.support_cutoff_emod_delta S s)
  rw [ha, hb] at hp0
  rw [← hvt, ha, hb] at hpv
  rw [ha, hc] at hc0
  rw [hc, hb] at hcp
  rw [← hvt, hc, ha] at hcv
  rw [ha, hc]
  have hab : a ≤ b := le_of_mul_le_mul_left hp0 hd
  have hba : b < a + 1 :=
    lt_of_mul_lt_mul_left (by rw [mul_add, mul_one]; exact hpv) (le_of_lt hd)
  have hbeq : b = a := by omega
  subst hbeq
  have hac : b ≤ c := le_of_mul_le_mul_left hc0 hd
  have hc1 : c ≠ b := fun h => hcp (by rw [h])
  have hc2 : c ≠ b + 1 := fun h => hcv (by rw [h, mul_add, mul_one])
  have hc3 : b + 2 ≤ c := by omega
  nlinarith

/-- With synchrony only up to slot `s`'s support cutoff: if the tick of slot `s`'s vote instant is
    step `m`, the reading step `mr` is at or after slot `s`'s support cutoff, the slot's start is at
    or after `tGAT`, the support cutoff is at or before `tR`, `v` is awake at every instant from the
    slot's start to its support cutoff and not held by the adversary at step `mr`, `v'` is an honest
    active member of slot `s`'s committee, and every such member votes there for a descendant of
    `C`, then every block `G` that `v'`'s slot-`s` fork choice can return is in `v`'s tree at step
    `mr`, `Block.find?` answers with `G` for its root, `G` is of a slot at or before `s`, and it
    carries a stamp strictly before slot `s`'s support cutoff. The hypothesis `hneTick` asks that
    `v`'s tick have an outcome at every whole multiple of `Δ` up to step `mr`'s instant at which `v`
    is awake and not held. -/
theorem head_in_reader_tree_afterPhase_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot}
    (hsync : Restated.SynchronyFromWakeBefore M S x (M.support_cutoff S.E s))
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int} (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE)
    {C : Block V} (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT tR C)
    (hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x tGAT tR C)
    {m mr : Nat} {v v' : V}
    (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    (hmrlo : M.support_cutoff S.E s ≤ (x[mr].time : Int))
    (hslo : tGAT ≤ slotStart S.E.Δ s) (hsR : M.support_cutoff S.E s ≤ tR)
    (hw : v ∉ Sched.adv (x[mr].time : Int))
    (hwaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s))
    (hq : v' ∈ Restated.HonSlot M S Sched s)
    (hbelow : Restated.HeadsBelow M S Sched x C s)
    (hneTick : ∀ (n' : Nat) (t' : Int), Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' →
      t' ≤ (x[mr].time : Int) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out) :
    ∀ G : Block V, Restated.gfHeadFrom M S (x[m][v'].st) s ⇢ G →
    Block.find? (x[mr][v].st).st.core.T G.root = some G ∧
      G.slot ≤ s ∧
      ∃ σ : Stamp,
        (x[mr][v].st).st.core.timestamp_block G = some σ ∧
          σ < ((M.support_cutoff S.E s : Int) : Stamp) := by
  intro G hG
  have hd := S.E.Δ_pos
  have hvt : M.vote_time S.E s = slotStart S.E.Δ s + S.E.Δ :=
      (facts.sch.slotStart_add_delta_eq_vote_time S.E s).symm
  have hsc : slotStart S.E.Δ s + 2 * S.E.Δ ≤ M.support_cutoff S.E s :=
    slotStart_add_two_delta_le_support_cutoff facts S s
  have hct : M.confirmation_time S.E s = slotStart S.E.Δ s + 6 * S.E.Δ :=
      (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s).symm
  obtain ⟨-, hmself⟩ := Restated.tickStepAt_time facts x hm
  rw [hvt] at hmself
  have hwh : Restated.HonestThrough M Sched x mr v := by
    intro t ht hin
    exact hw (hmono _ _ ht hin)
  have hmc : (x[m].time : Int) ≤ M.confirmation_time S.E s := by
    rw [hct]; linarith
  have hqh : Restated.HonestThrough M Sched x m v' :=
    Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hq hmc
  obtain ⟨D, hD, hDe⟩ :=
    Restated.exists_named_of_mem_tree facts S Sched x m v'
      (Restated.gfHeadFrom_mem_tree facts S Sched x m v' s G hG)
  have hCD : Block.Preceq C D.erase := by
    rw [hDe]; exact hbelow v' m hq hm G hG
  have hwaw' : v ∈ Sched.awakeThroughout (M.support_cutoff S.E s - 2 * S.E.Δ)
      (M.support_cutoff S.E s) :=
    awakeThroughout_mono Sched hwaw (by linarith) (le_refl _)
  obtain ⟨hmemT, σ, hσ, hσlt⟩ :=
    Restated.block_in_tree_of_holder_afterPhase_upTo facts S Sched x hexec hsync hmult htd hmono hgst hcv
      hawake hthird hcs hlen hunder hunderS (v := v) (t := M.support_cutoff S.E s) hD hqh hCD
      (by linarith) (by linarith) hsR hmrlo hw hwaw'
      (fun n' t' h1 hΔ hq _ h3 => hneTick n' t' h1 hΔ hq h3)
  rw [hDe] at hmemT hσ
  exact ⟨Restated.find_of_mem_tree_honest facts S Sched x hexec hwh hmemT,
    Restated.headSlot_le_of_tickStepAt facts S Sched x hm v' G hG, σ, hσ, hσlt⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- With synchrony only up to slot `s`'s support cutoff and under the premises of
    `head_in_reader_tree_afterPhase_upTo`, `HeadsResolve S Sched x v m mr s` holds: for every honest
    active member of slot `s`'s committee, the root of each of its slot-`s` heads is answered by
    `Block.find?` on `v`'s tree at step `mr` with a block of a slot at or before `s`, stamped there
    strictly before slot `s`'s support cutoff. -/
theorem headsResolve_afterPhase_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot}
    (hsync : Restated.SynchronyFromWakeBefore M S x (M.support_cutoff S.E s))
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int} (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE)
    {C : Block V} (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT tR C)
    (hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x tGAT tR C)
    {m mr : Nat} {v : V}
    (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    (hmrlo : M.support_cutoff S.E s ≤ (x[mr].time : Int))
    (hslo : tGAT ≤ slotStart S.E.Δ s) (hsR : M.support_cutoff S.E s ≤ tR)
    (hw : v ∉ Sched.adv (x[mr].time : Int))
    (hwaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s))
    (hbelow : Restated.HeadsBelow M S Sched x C s)
    (hneTick : ∀ (n' : Nat) (t' : Int), Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' →
      t' ≤ (x[mr].time : Int) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out) :
    Restated.HeadsResolve M S Sched x v m mr s := by
  intro v' hq G hG
  obtain ⟨hfind, hslot, σ, hσ, hσlt⟩ :=
    Restated.head_in_reader_tree_afterPhase_upTo facts S Sched x hexec hsync hmult htd hmono hgst hcv
      hawake hthird hcs hlen hunder hunderS hm hmrlo hslo hsR hw hwaw hq hbelow hneTick G hG
  exact ⟨G, rfl, hslot, hfind, σ, hσ, hσlt⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- With synchrony only up to slot `s`'s support cutoff and under the premises of
    `head_in_reader_tree_afterPhase_upTo` with `C := B`: for each honest active member `v'` of slot
    `s`'s committee and every block `G` its slot-`s` fork choice can return, there is a block with
    `G`'s root which is a descendant of `B`, is of a slot at or before `s`, is what `Block.find?`
    answers on `v`'s tree at step `mr` for that root, and carries a stamp strictly before slot `s`'s
    support cutoff. -/
theorem coneHeads_afterPhase_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot}
    (hsync : Restated.SynchronyFromWakeBefore M S x (M.support_cutoff S.E s))
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int} (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE)
    {B : Block V} (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT tR B)
    (hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x tGAT tR B)
    {m mr : Nat} {v : V}
    (hprev : Restated.HeadsBelow M S Sched x B s)
    (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    (hmrlo : M.support_cutoff S.E s ≤ (x[mr].time : Int))
    (hslo : tGAT ≤ slotStart S.E.Δ s) (hsR : M.support_cutoff S.E s ≤ tR)
    (hw : v ∉ Sched.adv (x[mr].time : Int))
    (hwaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s))
    (hneTick : ∀ (n' : Nat) (t' : Int), Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' →
      t' ≤ (x[mr].time : Int) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out) :
    ∀ v' ∈ Restated.HonSlot M S Sched s, ∀ G : Block V,
      Restated.gfHeadFrom M S (x[m][v'].st) s ⇢ G → ∃ X : Block V,
      X.root = G.root ∧ Block.Preceq B X ∧ X.slot ≤ s ∧
        Block.find? (x[mr][v].st).st.core.T X.root = some X ∧
        ∃ σ : Stamp, (x[mr][v].st).st.core.timestamp_block X = some σ ∧
          σ < ((M.support_cutoff S.E s : Int) : Stamp) := by
  intro v' hq G hG
  obtain ⟨hfind, hslot, σ, hσ, hσlt⟩ :=
    Restated.head_in_reader_tree_afterPhase_upTo facts S Sched x hexec hsync hmult htd hmono hgst hcv
      hawake hthird hcs hlen hunder hunderS hm hmrlo hslo hsR hw hwaw hq hprev hneTick G hG
  exact ⟨G, rfl, hprev v' m hq hm G hG, hslot, hfind, σ, hσ, hσlt⟩

end

end DecoupledConsensusModel.Sts.Restated
