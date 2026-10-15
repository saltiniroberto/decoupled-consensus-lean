import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.ReceiptOutcome
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConeCover
import Proofs.Claims.Restated.Claim13bK_ConeHeads
import Proofs.Claims.Restated.Claim13bK_ConfirmedInclusion
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettle
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeFor
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bK_ProposalVotesAfterPhase
import Proofs.Claims.Restated.Claim13bK_StableReaders
import Proofs.Claims.Restated.Claim13bK_StableRecord
import Proofs.Claims.Restated.Claim13bK_StableRootFor
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsFacts
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.VocabularyAssumptionsLemmas
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedInclusion
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bK_ConfirmedWake
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bK_GradeOldHeads
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.ProcessedFlip
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedAfterHealing
import Model.Conditions.Sts_Spec2Claims_ClaimStableLiveAfterHealing
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Grades at the next round for every round length

The grade theorems at round `q + 1` for a validator awake since `S.a q` or waking there, for every
round length, and the inclusion of an honest proposal in the stable output from the third slot after
the switch round on, stated over a model `M : Record.Model V`.
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

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under `AwakeAtMultiples`, a validator `w` awake at `S.a r − 1` is awake at every instant of
    `[S.a r − Δ, S.a r − 1]`. -/
theorem awake_before_action_of_awake (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (hmult : AwakeAtMultiples S Sched) {w : V} {r : Round}
    (haw : w ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S r) - 1)) :
    w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r) - S.E.Δ) ((Restated.Vocabulary.Execution.Setup.a M S r) - 1) := by
  have hΔ : 0 < S.E.Δ := S.E.Δ_pos
  have hmod := Restated.action_emod_delta facts S r
  have hstep : ∀ d : Nat, (Restated.Vocabulary.Execution.Setup.a M S r) - S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S r) - 1 - (d : Int) →
      w ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S r) - 1 - (d : Int)) := by
    intro d
    induction d with
    | zero => intro _; simpa using haw
    | succ d ih =>
      intro hd
      push_cast at hd
      have hprev := ih (by linarith)
      by_contra hnot
      have hnot' : w ∉ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S r) - 1 - (d : Int) - 1) := by
        have he : (Restated.Vocabulary.Execution.Setup.a M S r) - 1 - (d : Int) - 1 = (Restated.Vocabulary.Execution.Setup.a M S r) - 1 - ((d + 1 : Nat) : Int) := by
          push_cast; ring
        rw [he]; exact hnot
      have hm := hmult ((Restated.Vocabulary.Execution.Setup.a M S r) - 1 - (d : Int)) w hprev hnot'
      have h1 : S.E.Δ ∣ (Restated.Vocabulary.Execution.Setup.a M S r) := Int.dvd_of_emod_eq_zero hmod
      have h2 : S.E.Δ ∣ (Restated.Vocabulary.Execution.Setup.a M S r) - 1 - (d : Int) := Int.dvd_of_emod_eq_zero hm
      have h3 : S.E.Δ ∣ 1 + (d : Int) := by
        have h := dvd_sub h1 h2
        have he : (Restated.Vocabulary.Execution.Setup.a M S r) - ((Restated.Vocabulary.Execution.Setup.a M S r) - 1 - (d : Int)) = 1 + (d : Int) := by ring
        rwa [he] at h
      have h4 := Int.le_of_dvd (by positivity) h3
      linarith
  refine mem_awakeThroughout_of_forall Sched (fun t h0 h1 => ?_)
  have h := hstep ((Restated.Vocabulary.Execution.Setup.a M S r) - 1 - t).toNat (by rw [Int.toNat_of_nonneg (by linarith)]; linarith)
  rwa [Int.toNat_of_nonneg (by linarith), sub_sub_cancel] at h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If the adversary has held `v'` at no instant up to step `m` and a block `B`, not genesis, is
    among `v'`'s bodies at step `m`, then `B` entered `v'`'s bodies and tree at some step `i < m`,
    and some validator not held by the adversary put `B` on the wire at a step `k` with the same
    instant as step `i`. -/
theorem honestSend_of_holder (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {m : Nat} {v' : V} {B : NamedBlock V}
    (hB : B ∈ (x[m][v'].st).st.bodies) (hq : Restated.HonestThrough M Sched x m v')
    (hgen : B ≠ NamedBlock.genesis) :
    ∃ i k : Nat, ∃ v_0 : V, i < m ∧ B.erase ∈ (x[i + 1][v'].st).st.core.T ∧
      B ∈ (x[i + 1][v'].st).st.bodies ∧
      (x[k].time : Int) = (x[i].time : Int) ∧
      (x[i + 1].time : Int) ≤ (x[k + 1].time : Int) ∧
      (x[i + 1].time : Int) ≤ (x[k].time : Int) + 1 ∧
      Restated.HonestSendAt M S x k (⟨v_0, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) := by
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
  have himt : (x[i].time : Int) ≤ (x[m].time : Int) := Restated.time_mono_int facts S Sched x (le_of_lt him)
  have hqi : Restated.HonestThrough M Sched x i v' := fun t' ht => hq t' (le_trans ht himt)
  rcases Restated.flip_step_cases facts S Sched x hf0 hf1 with
    ⟨sm, hlbl, -, -, hpay⟩ | ⟨τ, hlbl, haw, hdvd, hem⟩
  · rcases hpay with hmsg | ⟨Bl, -, hcc⟩
    · obtain ⟨u, o⟩ := sm
      have hmsg' : o = NamedObject.block B := hmsg
      subst hmsg'
      have hdt : (x[i + 1].time : Int) = (x[i].time : Int) := by
        exact_mod_cast congrArg (fun j : Nat => (j : Int)) (Restated.deliver_time facts S Sched x hlbl)
      obtain ⟨k, hkt, hsend⟩ := Restated.block_onWire_of_deliver_phase facts S Sched x hlbl hqi
        (Restated.sent_of_deliver facts S Sched x hlbl).2
        (Restated.receipt_outcome_of_flip facts S Sched x hlbl hf0 hf1)
      refine ⟨i, k, v', him, hmemi, hbodyi, hkt, ?_, ?_, hsend⟩
      · rw [hdt, ← hkt]
        exact Restated.time_mono_int facts S Sched x (Nat.le_succ k)
      · rw [hdt, hkt]; linarith
    · exact hcc.elim
  · obtain ⟨out₁, hout₁, hst₁, hem'⟩ := hem
    rcases hem' with hemit | ⟨Bl, -, hcc⟩
    · obtain ⟨hτ, hτ'⟩ := Restated.tickAllAwake_time facts S Sched x hlbl
      have hdt : (x[i + 1].time : Int) = (x[i].time : Int) + 1 := by
        have h1 : (x[i].time : Int) + 1 = (τ : Int) := by exact_mod_cast hτ
        have h2 : (x[i + 1].time : Int) = (τ : Int) := by exact_mod_cast hτ'
        linarith
      exact ⟨i, i, v', him, hmemi, hbodyi, rfl, le_rfl, by rw [hdt],
        Restated.block_honestSend_at_tick facts S Sched x hqi hlbl haw hdvd
          ⟨out₁, hout₁, hst₁, hemit⟩⟩
    · exact hcc.elim

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A block `B` an honest validator holds, entered into its store strictly before `t_0`, is in the
    tree of a validator `v` that admits it, at any step `mr` with `t ≤ x[mr].time`, stamped strictly
    before `t`, when `tGAT < t_0`, `t_0 + Δ ≤ t`, and `v` is awake throughout `[t − 2Δ + 1, t]` or
    is asleep at `t_0 − 1` and awake throughout `[t_0, t_0 + Δ]`. -/
theorem block_in_tree_of_holder_beforeAction_ofAdmits (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hcatch : Restated.CatchUpOnWake M S x)
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int}
    (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE)
    {m mr : Nat} {v' v : V} {B : NamedBlock V} {t_0 t : Int}
    (hadm : Restated.ReaderAdmitsInPhase M S Sched x tGAT tR v B)
    (hadmS : Restated.ReaderAdmitsAtStepsInPhase M S Sched x tGAT tR v B)
    (hB : B ∈ (x[m][v'].st).st.bodies)
    (hq : Restated.HonestThrough M Sched x m v')
    (hmlo : tGAT ≤ (x[m].time : Int))
    (hpre : ∀ i : Nat, i < m → (x[i].time : Int) < t_0)
    (hlo : tGAT < t_0) (hdl : t_0 + S.E.Δ ≤ t)
    (hΓR : t ≤ tR) (hmr : t ≤ (x[mr].time : Int))
    (hw : v ∉ Sched.adv (x[mr].time : Int))
    (hrd : v ∈ Sched.awakeThroughout (t - 2 * S.E.Δ + 1) t ∨
      (v ∉ Sched.awake (t_0 - 1) ∧ v ∈ Sched.awakeThroughout t_0 (t_0 + S.E.Δ)))
    (hneTick : ∀ (n' : Nat) (t' : Int), Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' →
      slotStart S.E.Δ B.erase.slot ≤ t' → t' ≤ (x[mr].time : Int) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out) :
    B.erase ∈ (x[mr][v].st).st.core.T ∧
      ∃ σ : Stamp, (x[mr][v].st).st.core.timestamp_block B.erase = some σ ∧
        σ < (t : Stamp) := by
  classical
  have hd := S.E.Δ_pos
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
  obtain ⟨i, k, v_0, him, hmemi, hbodyi, hkt, hnk, hnk1, hsend⟩ :=
    Restated.honestSend_of_holder facts S Sched x hB hq hgen
  have hki : (x[k].time : Int) < t_0 := by rw [hkt]; exact hpre i him
  rcases hrd with hwaw | ⟨hns, hwin⟩
  · by_cases hearly : (x[k].time : Int) < tGAT
    · have hqT : HonestThroughTime Sched tGAT v' := fun t' ht => hq t' (le_trans ht hmlo)
      exact Restated.block_in_tree_of_narrowedCommonView_afterPhase facts S Sched x hexec htd hmono hcv
          hawake hlen
        hbodyi hqT (by linarith) (by linarith) hmr hw hFst
    · have hklo : tGAT ≤ (x[k].time : Int) := not_lt.mp hearly
      have hcov : ∀ t' : Int, (x[k].time : Int) ≤ t' → HonestAwakeCover S Sched t' :=
        fun t' ht' => Restated.honestAwakeCover_of_premises facts S Sched hmono hgst hthird hawake hcs
          (le_trans hklo ht')
      exact Restated.block_in_tree_of_honestSend_afterPhase_ofAdmits facts S Sched x hexec hsync hmult htd
        hmono hadm hsend (le_trans hgst hklo) hklo hcov hmemi hgen hnk (by linarith) hΓR hmr hw
        hwaw hneTick
  · have hmax : max t_0 S.E.t_GST = t_0 := max_eq_left (by linarith)
    have hwa : v ∈ Sched.awake t_0 :=
      mem_awake_of_awakeThroughout Sched hwin le_rfl (by linarith)
    obtain ⟨d, hkd, hdlbl, hdlo, hdhi⟩ :=
      hcatch k v _ t_0 hsend hki hwa hns (by rw [hmax]; exact hwin)
    rw [hmax] at hdhi
    have hk1d : (x[k + 1].time : Int) ≤ (x[d].time : Int) := Restated.time_mono_int facts S Sched x hkd
    have hdmr' : (x[d].time : Int) ≤ (x[mr].time : Int) := by linarith
    have hwh : Restated.HonestThrough M Sched x d v := by
      intro t' ht' hin
      exact hw (hmono t' _ (le_trans ht' hdmr') hin)
    have hbody : B ∈ (x[d + 1][v].st).st.bodies :=
      Restated.block_admitted_of_deliver_ofAdmits facts S Sched x hexec hmult htd hadm hdlbl hwh hmemi hgen
        (le_trans hnk hk1d) (by linarith) (by linarith)
        (fun n' t' hn' hΔ hq hlo' hhi' => hneTick n' t' hn' hΔ hq hlo' (le_trans hhi' hdmr'))
    have hdtime : (x[d + 1].time : Int) = (x[d].time : Int) := by
      exact_mod_cast congrArg (fun j : Nat => (j : Int)) (Restated.deliver_time facts S Sched x hdlbl)
    have hdmr : d + 1 ≤ mr := by
      by_contra hcon
      have hle : mr ≤ d := by omega
      have h := Restated.time_mono_int facts S Sched x hle
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
        Restated.block_stamp_lt_of_time facts S Sched x (d + 1) v (Γ := t) hmemTd (by rw [hdtime]; linarith)
      exact ⟨σ, Restated.block_stamp_carry facts S Sched x hdmr v hσ, hσlt⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `q` is at or after the switch round, `n` is the tick step at `S.a q`, `m` is the last step
    before round `q + 1`'s phase-`p` instant, and `v` is awake throughout
    `[S.a q, domain (q + 1) p]` and not held by the adversary at `domain (q + 1) p`, then every
    block named by a round-`q` attestation that a member of `freshAttestersW S Sched x q m` can
    compute resolves in `v`'s tree after `m` steps, stamped strictly before round `q + 1`'s early
    cutoff of phase `p`. -/
theorem hstamp_of_premises (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    {q : Round} (hr : Restated.switchRound M S tE ≤ q)
    {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S q)))
    {p : Protocol.Phase} {m : Nat}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (q + 1) p))
    {v : V} (hvaw : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S q)) (M.domain S.E S.hc (q + 1) p))
    (hvS : v ∉ Sched.adv (M.domain S.E S.hc (q + 1) p)) :
    ∀ v_1 ∈ Restated.freshAttestersW M S Sched x q m, ∀ C : NamedBlock V,
      C ∈ (x[n + 1][v_1].st).st.bodies →
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 q,
      a.confirmed = some C.root →
      Block.find? (x[m][v].st).st.core.T C.root = some C.erase ∧
      stampedBefore (x[m][v].st).st.core.timestamp_block
        (M.early S.E S.hc (q + 1) p) C.erase = true := by
  intro v_1 hv_1 C hC a ha hconf
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hdom : M.domain S.E S.hc (q + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) := facts.gr.domain_le_action S (q + 1) p
  have hmd : (x[m].time : Int) < M.domain S.E S.hc (q + 1) p :=
    Restated.time_lt_domain_of_stepBefore facts S Sched x htd hm
  have hdm := Restated.domain_sub_one_le_time_of_stepBefore facts S Sched x htd hm
  have ham : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ (x[m].time : Int) := Restated.action_le_time_of_stepBefore facts S Sched x htd hm
  have hearly : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤ M.early S.E S.hc (q + 1) p :=
    le_trans (Restated.action_delta_le_early_succ facts S q) (Restated.early_g2_le_early facts S (q + 1) p)
  have hed := facts.gr.early_add_two_delta_le_domain S (q + 1) p
  have hopq : (Restated.Vocabulary.Execution.Setup.a M S q) = M.opening S.E S.hc q + 6 * S.E.Δ :=
      (pHP% action_eq_opening_add_hp) facts S q
  have htGATo : tGAT ≤ M.opening S.E S.hc q :=
    le_trans (Restated.tGAT_le_switchOpening facts S tGAT tE gap hgst hlen) (Restated.switchOpening_le_opening facts S hr)
  have htGAT : tGAT < (Restated.Vocabulary.Execution.Setup.a M S q) := by linarith
  have hvm : Restated.HonestThrough M Sched x m v := fun t ht hin =>
    hvS (hmono t _ (le_trans ht (le_of_lt hmd)) hin)
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd q
  have hn'1 : (x[n' + 1].time : Int) = (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) := (Restated.tickStepAt_time facts x hn').1
  have hn1 : (x[n + 1].time : Int) = (Restated.Vocabulary.Execution.Setup.a M S q) := (Restated.tickStepAt_time facts x hn).1
  have hn0 : (x[n].time : Int) + 1 = (Restated.Vocabulary.Execution.Setup.a M S q) := (Restated.tickStepAt_time facts x hn).2
  have hv1m : Restated.HonestThrough M Sched x m v_1 := Restated.honestThrough_of_mem_freshAttestersW facts hv_1
  have hv1n : Restated.HonestThrough M Sched x (n + 1) v_1 := fun t ht =>
    hv1m t (le_trans ht (by rw [hn1]; exact ham))
  have hFC := Restated.fresh_attested_compatible_finalized facts S Sched x tE hexec hmono htd hcatch tGAT gap
    hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
    hJswitch hTW₀ hJ₀ hr hn hn' hm hv_1 hC a ha hconf
  have hlog : Restated.blockInLog M S Sched x C := Restated.blockInLog_of_mem_bodies facts S Sched hv1n hC
  have hadm : Restated.ReaderAdmitsInPhase M S Sched x tGAT ((Restated.Vocabulary.Execution.Setup.a M S (q + 1)) - 1) v C := by
    intro d v_0 _ hvd _ hhi
    have hdn : d ≤ n' := by
      by_contra hcon
      have hle : n' + 1 ≤ d := by omega
      have h1 := Restated.time_mono_int facts S Sched x hle
      rw [hn'1] at h1
      linarith
    rcases compatible_cases (hFC v d hdn hvd) with hFCd | hCFd
    · exact Or.inl (preceq_eq_true_iff_Preceq.mpr hFCd)
    · exact Or.inr (Restated.mem_bodies_of_preceq_finalized facts S Sched x hexec hvd hlog hCFd)
  have hadmS : Restated.ReaderAdmitsAtStepsInPhase M S Sched x tGAT ((Restated.Vocabulary.Execution.Setup.a M S (q + 1)) - 1) v C := by
    intro d hvd _ hhi
    have hdn : d ≤ n' := by
      by_contra hcon
      have hle : n' + 1 ≤ d := by omega
      have h1 := Restated.time_mono_int facts S Sched x hle
      rw [hn'1] at h1
      linarith
    rcases compatible_cases (hFC v d hdn hvd) with hFCd | hCFd
    · exact Or.inl (preceq_eq_true_iff_Preceq.mpr hFCd)
    · exact Or.inr (Restated.mem_bodies_of_preceq_finalized facts S Sched x hexec hvd hlog hCFd)
  have hpre : ∀ i : Nat, i < n + 1 → (x[i].time : Int) < (Restated.Vocabulary.Execution.Setup.a M S q) := by
    intro i hi
    have h := Restated.time_mono_int facts S Sched x (show i ≤ n by omega)
    linarith
  have hrd : v ∈ Sched.awakeThroughout (M.early S.E S.hc (q + 1) p - 2 * S.E.Δ + 1)
        (M.early S.E S.hc (q + 1) p) ∨
      (v ∉ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S q) - 1) ∧ v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S q)) ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ)) := by
    by_cases hprev1 : v ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S q) - 1)
    · left
      have hbefore := Restated.awake_before_action_of_awake facts S Sched hmult hprev1
      refine mem_awakeThroughout_of_forall Sched (fun t h0 h1 => ?_)
      by_cases htq : t ≤ (Restated.Vocabulary.Execution.Setup.a M S q) - 1
      · exact mem_awake_of_awakeThroughout Sched hbefore (by linarith) htq
      · exact mem_awake_of_awakeThroughout Sched hvaw (by linarith) (by linarith)
    · exact Or.inr ⟨hprev1, awakeThroughout_mono Sched hvaw le_rfl (by linarith)⟩
  obtain ⟨hmemT, σ, hσ, hσlt⟩ :=
    Restated.block_in_tree_of_holder_beforeAction_ofAdmits facts S Sched x hexec hsync hcatch hmult htd hmono
      hgst hcv hphase hthird hcs (Restated.delta_le_of_healingLengthη facts S hlen) hadm hadmS hC hv1n
      (by rw [hn1]; exact le_of_lt htGAT) hpre htGAT hearly (by linarith) (by linarith)
      (fun hin => hvm _ le_rfl hin) hrd (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
  refine ⟨?_, stampedBefore_of_lt hσ hσlt⟩
  rw [← Proofs.NamedWire.erase_root]
  exact Restated.find_of_mem_tree_honest facts S Sched x hexec hvm hmemT

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `q` is at least two rounds after the switch round, every honest active member of the
    committee of round `q`'s opening slot votes there for a descendant of `X`, `n` is the tick step
    at `S.a q`, `m` is the last step before round `q + 1`'s phase-`p` instant, and `v` is awake
    throughout `[S.a q, domain (q + 1) p]` and not held by the adversary at `domain (q + 1) p`, then
    every outcome of `v`'s grade test for `X` at round `q + 1` and phase `p` after `m` steps is
    `true`. -/
theorem gradeBool_of_headsBelow_of_three_le_R (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    {q : Round} (hq : Restated.switchRound M S tE + 2 ≤ q)
    {X : Block V} (hX : Restated.HeadsBelow M S Sched x X ((M.opening_slot S.hc q)))
    {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S q)))
    {p : Protocol.Phase} {m : Nat}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (q + 1) p))
    {v : V} (hvaw : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S q)) (M.domain S.E S.hc (q + 1) p))
    (hvS : v ∉ Sched.adv (M.domain S.E S.hc (q + 1) p)) :
    ∀ g : Bool, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core)) (x[m][v].st).st.core.F
      S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p) (M.late S.E S.hc (q + 1) p)
      X ⇢ g → g = true :=
  Restated.gradeBool_of_headsBelow_of_stamp facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen
    hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW hJswitch
    hTW₀ hJ₀ hq hX hn hm hvaw hvS
    (Restated.hstamp_of_premises facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen hsync hthird
      hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW hJswitch hTW₀ hJ₀
      (le_trans (Nat.le_add_right _ 2) hq) hn hm hvaw hvS)

end

private theorem le_succ_of_not_add_two_le_cu (a b : Nat) (h : ¬ b + 2 ≤ a) : a ≤ b + 1 := by
  omega

private theorem false_of_slot_chain_cu (o o' s : Nat) (h1 : s ≤ o) (h2 : o ≤ o')
    (h3 : o' + 2 ≤ s) : False := by
  omega

private theorem three_le_add_cu (o R : Nat) (h : 3 ≤ R) : 3 ≤ o + R := by
  omega

private theorem succ_le_succ_of_add_two_cu (a b : Nat) (h : b + 2 ≤ a) : b + 1 ≤ a + 1 := by
  omega

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If slot `s` is at or after the third slot of the round after the switch round, its proposer is
    honest up to `s`'s vote instant, and it proposed `B` at a step `k` at or before that vote
    instant, then at every step `j` at or after `s`'s proposal instant plus
    `Restated.stableInclusionDelay M S`, `B` is an ancestor of the stable output of every validator
    honest through `j` and in `activeAtW` at `j`'s slot. -/
theorem stableIncluded_afterPhase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    (hsettle : Restated.RecordsSettledAtSettleTick M S Sched x tE)
    {s : Slot} (hsl : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) + 2 ≤ s)
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    {k : Nat} {B : Block V} (hB : Restated.proposedBlockAtStep M S x k s B)
    (hk : (x[k].time : Int) ≤ M.vote_time S.E s) :
    ∀ (v : V) (j : Nat), Restated.HonestThrough M Sched x j v →
      M.proposal_time S.E s + Restated.stableInclusionDelay M S ≤ (x[j].time : Int) →
      v ∈ activeAtW S Sched (S.E.slotOf (x[j].time : Int)) →
      Block.Preceq B (M.get_stable (x[j][v].st).st.core) := by
  intro v j hvj htj hva
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hR3 := S.hc.R_ge_three
  have hj0 : (0 : Int) ≤ (x[j].time : Int) := Int.natCast_nonneg _
  have hpt : slotStart S.E.Δ s ≤ M.proposal_time S.E s :=
    slotStart_le_of_le_slotOf S (facts.sch.Sts_proposal_time_nonneg S s)
      (le_of_eq (facts.sch.slotOf_proposal_time S.E s).symm)
  have hdelay : Restated.stableInclusionDelay M S = 2 * (4 * S.E.Δ * (S.hc.R : Int)) + 4 * S.E.Δ := by
    show 2 * (Restated.constants M S).period + 4 * S.E.Δ = _
    rw [Restated.period_eq facts S]
  have hstart : slotStart S.E.Δ (s + 2 * S.hc.R + 1) ≤ (x[j].time : Int) := by
    have hs0' := slotStart_closed S.E.Δ s
    rw [slotStart_closed]; push_cast
    rw [hdelay] at htj; linarith
  have hss : s + 2 * S.hc.R + 1 ≤ S.E.slotOf (x[j].time : Int) := by
    have h := slotOf_mono_sts S hstart
    rwa [slotOf_slotStart] at h
  have hst' : slotStart S.E.Δ (S.E.slotOf (x[j].time : Int)) ≤ (x[j].time : Int) :=
    slotStart_le_of_le_slotOf S hj0 le_rfl
  obtain ⟨q, hso, hq1t, hawq⟩ := Restated.exists_readerRound_of_activeAtW facts S Sched hw hss hva
  have hq1j : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ (x[j].time : Int) := by linarith
  have hq : Restated.switchRound M S tE + 2 ≤ q := by
    by_contra hcon
    have hle : (M.opening_slot S.hc q) ≤ (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) :=
      facts.gr.opening_slot_mono S (le_succ_of_not_add_two_le_cu _ _ hcon)
    exact false_of_slot_chain_cu _ _ _ hso hle hsl
  have hw1 : v ∈ Restated.HonRound M S Sched (q + 1) := by
    refine Finset.mem_sdiff.2 ⟨?_, hvj _ hq1j⟩
    show v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S (q + 1)) - wAttest S) ((Restated.Vocabulary.Execution.Setup.a M S (q + 1)))
    rw [Restated.wAttest_eq_action_succ_sub facts S q]; exact hawq
  have hop : (M.opening_slot S.hc (Restated.switchRound M S tE)) ≤ (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) :=
    facts.gr.opening_slot_mono S (Nat.le_succ _)
  have hs0 : (M.opening_slot S.hc (Restated.switchRound M S tE)) + 2 ≤ s :=
    le_trans (Nat.add_le_add_right hop 2) hsl
  have hadopt := Restated.honestProposalHeadsAtOwnSlot_afterPhase facts S Sched x tE hexec hmono htd hcatch tGAT
    gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
    hJswitch hTW₀ hJ₀ (M.confirmation_time S.E s)
  have hBh : Restated.AncestorOfHonestHeadsFrom M S Sched x B s :=
    Restated.honestProposal_ancestorOfHonestHeadsFrom_i1 facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
      hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW hJswitch
      (r₀ := Restated.switchRound M S tE) le_rfl hTW₀ hJ₀ hadopt hs0
      (le_trans (Nat.le_add_right _ 2) hsl) le_rfl hprop hB hk
  have hX : Restated.HeadsBelow M S Sched x B ((M.opening_slot S.hc q)) := hBh _ hso
  obtain ⟨nq, hnq⟩ := Restated.exists_tickStepAt facts x htd (Restated.action_pos facts S q)
  have hdomE : M.domain S.E S.hc (q + 1) .g2
      = 4 * S.E.Δ * (((M.opening_slot S.hc (q + 1)) : Nat) : Int) - S.E.Δ := by
    rw [← facts.gr.gammaNeg1_eq_domain_g2_succ S q, slotStart_closed]
  have ho1 : (3 : Int) ≤ (((M.opening_slot S.hc (q + 1)) : Nat) : Int) := by
    have : 3 ≤ (M.opening_slot S.hc (q + 1)) := by
      rw [facts.gr.opening_slot_succ S.hc q]; exact three_le_add_cu _ _ hR3
    exact_mod_cast this
  have hdpos : 0 < M.domain S.E S.hc (q + 1) .g2 := by rw [hdomE]; nlinarith
  obtain ⟨md, hmd⟩ := Restated.exists_tickStepAt facts x htd hdpos
  have hm := Restated.stepBeforeInstant_of_tickStepAt facts x hmd
  have hdom := facts.gr.domain_le_action S (q + 1) .g2
  have hvaw : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S q)) (M.domain S.E S.hc (q + 1) .g2) :=
    awakeThroughout_mono Sched hawq le_rfl hdom
  have hvS : v ∉ Sched.adv (M.domain S.E S.hc (q + 1) .g2) := hvj _ (by linarith)
  have hgrall := Restated.gradeBool_of_headsBelow_of_three_le_R facts S Sched x tE hexec hmono htd hcatch tGAT gap
    hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
    hJswitch hTW₀ hJ₀ hq hX hnq hm hvaw hvS
  have hgr : M.gradeBool S.E (M.gradeView (M.toHealing (x[md][v].st).st.core))
      (x[md][v].st).st.core.F S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g2)
      (M.late S.E S.hc (q + 1) .g2) B ⇢ true := by
    obtain ⟨g, hg⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[md][v].st).st.core))
      (x[md][v].st).st.core.F S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g2)
      (M.late S.E S.hc (q + 1) .g2) B
    have hgt := hgrall g hg
    rw [hgt] at hg
    exact hg
  have hctpos : 0 < M.confirmation_time S.E ((M.opening_slot S.hc (q + 1))) := by
    rw [Restated.confirmation_time_opening_slot facts]; exact Restated.action_pos facts S (q + 1)
  obtain ⟨n, hn⟩ := Restated.exists_tickStepAt facts x htd hctpos
  have hn1 : (x[n + 1].time : Int) = (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) := by
    rw [(Restated.tickStepAt_time facts x hn).1, Restated.confirmation_time_opening_slot facts]
  have hct : M.confirmation_time S.E ((M.opening_slot S.hc (q + 1))) = (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    Restated.confirmation_time_opening_slot facts S (q + 1)
  have haw : v ∈ Sched.awake (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)))) \
      Sched.adv (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)))) := by
    rw [hct]
    exact Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hawq
      (Restated.action_mono facts S (Nat.le_succ q)) le_rfl, hvj _ hq1j⟩
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (M.toHealing (x[n][v].st).st.core)
    (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)))) (x[n][v].st).cache
  obtain ⟨o, ho'⟩ := facts.gr.frameStableRoot_nonempty c S.E S.hc
    (M.toHealing (M.ns_setClock S.E (x[n][v].st).st
      (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1))))).core)
    ((M.round_of S.hc) (M.ns_setClock S.E (x[n][v].st).st
      (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1))))).core.s)
  have ho := (facts.nd.gradeContract_stableRoot _ _ _ _ _ o).2 ho'
  have hneTick := Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew
    hmono hn (by rw [hct]; exact Restated.action_emod_delta facts S (q + 1)) haw
  have hround : M.round_of S.hc (M.opening_slot S.hc (q + 1) + 1) = q + 1 :=
    facts.gr.round_of_opening_slot_add S.hc (q + 1) (by omega)
  have hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E (M.opening_slot S.hc (q + 1))) x[n] v)
      (M.round_of S.hc (M.opening_slot S.hc (q + 1) + 1)) := by
    obtain ⟨τ, hlbl, hτ⟩ := hn
    rw [hround, hct]
    exact Restated.run_fact_g2 facts S Sched x n τ (q + 1) v hlbl (hτ.trans hct)
      (awakeThroughout_mono Sched hawq
        (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S le_rfl (Nat.lt_succ_self q)) le_rfl)
      (fun t' ht' => hvj t' (by rw [hτ, hct] at ht'; linarith))
  obtain ⟨G, rfl, -, -⟩ := Restated.records_after_confirmation_tick facts S Sched x hn haw
    hneTick hrun c hc _ ho
  have hBG := Restated.stableRoot_descendant_of_graded_at_action facts S Sched x tE hexec hmono htd hcatch tGAT
    gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
    hJswitch hTW₀ hJ₀ hq hw1 hm hgr hn hc ho
  have hsettleq : Restated.confirmedSettleTime M S tE ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) := by
    show (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1))
    exact Restated.action_mono facts S (succ_le_succ_of_add_two_cu _ _ hq)
  have hvh : Restated.HonestThrough M Sched x (n + 1) v := fun t ht => hvj t (by rw [hn1] at ht; linarith)
  have hwrite := (Restated.stable_records_preceq_after_confirmation_tick facts S Sched x tE hexec hmono htd hcatch
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW
    hAW hJswitch hTW₀ hJ₀ hsettle hn (by rw [hct]; exact hsettleq) haw hvh hc ho hBG hrun).2
  have hnj : n + 1 ≤ j := by
    by_contra hcon
    have h := Restated.time_mono_int facts S Sched x (show j ≤ n by omega)
    have h0 := (Restated.tickStepAt_time facts x hn).2
    rw [hct] at h0
    linarith
  have hext := Restated.stableOnlyExtendsAfterHealing_of_settle facts S Sched x tE hexec hmono htd hcatch tGAT
    gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
    hJswitch hTW₀ hJ₀ hsettle
  exact preceq_trans_Preceq hwrite (hext v (n + 1) j hnj hvj (by rw [hn1]; exact hsettleq))

end

end DecoupledConsensusModel.Sts.Restated
