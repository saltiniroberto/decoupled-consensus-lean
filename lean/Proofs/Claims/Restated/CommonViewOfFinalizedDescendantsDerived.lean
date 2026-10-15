import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_GradeForCatchUp
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13beRoute3_5
import Proofs.Claims.Restated.Claim13beRoute3_6
import Proofs.Claims.Restated.ClaimAsyncK_GstShift
import Proofs.Claims.Restated.Constants
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.TickOutcomeHonest
import Model.Conditions.Claim13bKit
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Conditions.Sts_Spec2Claims_ClaimStableThroughAsyncPeriod
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Deriving the common view among finalized descendants

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M` deriving
`CommonViewOfFinalizedDescendantsAt` from the delivery premises: with any deadline, at the start of
the phase after GST, and before or after an asynchronous period; and two bounds on the healing
length.
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

/-- If every honest send is delivered before the deadline `dl t` of its time `t` to the validators
    awake from the send through that deadline, a validator that wakes at `t_w` is delivered before
    `dl t_w` what honest validators sent before its wake, every deadline of a time at or before `t₀`
    is at most `t₀ + Δ`, and every validator the adversary does not hold is awake at every time from
    `t₀` to `tE ≥ t₀ + Δ`, then `CommonViewOfFinalizedDescendantsAt` holds at `t₀`. -/
theorem commonViewOfFinalizedDescendantsAt_of_deliveryBy (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) {dl : Int → Int}
    (hsync : Restated.SynchronyFromWakeBy M S x dl) (hcatch : Restated.CatchUpOnWakeBy M S x dl)
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    {t₀ tE : Int} (hdl : ∀ t : Int, t ≤ t₀ → dl t ≤ t₀ + S.E.Δ) (hlen : t₀ + S.E.Δ ≤ tE)
    (hawake : ∀ t : Int, t₀ ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) :
    Restated.CommonViewOfFinalizedDescendantsAt M S Sched x t₀ := by
  classical
  intro i j v w B hi hv hB hj hwj _ hF
  have hd := S.E.Δ_pos
  by_cases hgen : B = NamedBlock.genesis
  · subst hgen
    exact ((Restated.nodeInvariant_sts facts S Sched x j w).1.1.1.2.2.1).1
  have hq : Restated.HonestThrough M Sched x i v := fun t' ht => hv t' (le_trans ht hi)
  obtain ⟨i₀, k, v₀, hi₀, hmemT, -, hkt, hnk, -, hsend⟩ :=
    Restated.honestSend_of_holder facts S Sched x hB hq hgen
  have hkG : (x[k].time : Int) ≤ t₀ := by
    rw [hkt]; exact le_trans (Restated.time_mono_int facts S Sched x (le_of_lt hi₀)) hi
  have hwaw : ∀ t : Int, t₀ ≤ t → t ≤ t₀ + S.E.Δ → w ∈ Sched.awake t := fun t h0 h1 =>
    hawake t h0 (le_trans h1 hlen) w (hwj t (le_trans h1 hj))
  have hdel : ∃ d : Nat, k < d ∧
      x.lbl d = AtomicAction.deliver w
        (⟨v₀, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∧
      (x[d].time : Int) < t₀ + S.E.Δ := by
    by_cases hall : ∀ τ : Int, (x[k + 1].time : Int) ≤ τ → τ < t₀ → w ∈ Sched.awake τ
    · have hmax : dl (x[k].time : Int) ≤ t₀ + S.E.Δ := hdl _ hkG
      have hwin : w ∈ Sched.awakeThroughout (x[k + 1].time : Int)
          (dl (x[k].time : Int)) := by
        refine mem_awakeThroughout_of_forall Sched (fun τ h0 h1 => ?_)
        by_cases hτ : τ < t₀
        · exact hall τ h0 hτ
        · exact hwaw τ (not_lt.mp hτ) (le_trans h1 hmax)
      obtain ⟨d, hkd, hlbl, -, hlt⟩ := hsync k w _ hsend hwin
      exact ⟨d, hkd, hlbl, lt_of_lt_of_le hlt hmax⟩
    · push Not at hall
      obtain ⟨τ₀, hτ₀lo, hτ₀hi, hτ₀as⟩ := hall
      let A : Finset Int :=
        (Finset.Icc (x[k + 1].time : Int) (t₀ - 1)).filter (fun τ => w ∉ Sched.awake τ)
      have hA : A.Nonempty :=
        ⟨τ₀, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hτ₀lo, by linarith⟩, hτ₀as⟩⟩
      obtain ⟨hτmI, hτmas⟩ := Finset.mem_filter.1 (A.max'_mem hA)
      obtain ⟨hτmlo, hτmhi⟩ := Finset.mem_Icc.1 hτmI
      have hafter : ∀ τ : Int, A.max' hA < τ → τ ≤ t₀ + S.E.Δ → w ∈ Sched.awake τ := by
        intro τ h0 h1
        by_cases hτ : τ < t₀
        · by_contra hne
          have hmem : τ ∈ A :=
            Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by linarith, by linarith⟩, hne⟩
          exact absurd (A.le_max' τ hmem) (not_le.mpr h0)
        · exact hwaw τ (not_lt.mp hτ) h1
      have hmaxle : dl (A.max' hA + 1) ≤ t₀ + S.E.Δ := hdl _ (by linarith)
      have hkτ : (x[k].time : Int) < A.max' hA + 1 := by
        have := Restated.time_mono_int facts S Sched x (Nat.le_succ k)
        linarith
      obtain ⟨d, hkd, hlbl, -, hlt⟩ := hcatch k w _ (A.max' hA + 1) hsend hkτ
        (hafter _ (by linarith) (by linarith))
        (by rw [add_sub_cancel_right]; exact hτmas)
        (mem_awakeThroughout_of_forall Sched
          (fun τ h0 h1 => hafter τ (by linarith) (le_trans h1 hmaxle)))
      exact ⟨d, hkd, hlbl, lt_of_lt_of_le hlt hmaxle⟩
  obtain ⟨d, hkd, hlbl, hdlt⟩ := hdel
  have hdj : d + 1 ≤ j := by
    by_contra hcon
    have hle : j ≤ d := by omega
    have := Restated.time_mono_int facts S Sched x hle
    linarith
  have hdjt : (x[d].time : Int) ≤ (x[j].time : Int) := Restated.time_mono_int facts S Sched x (by omega)
  have hwd : Restated.HonestThrough M Sched x d w := fun t' ht => hwj t' (le_trans ht hdjt)
  have hslot : B.erase.slot ≤ (x[d][w].st).st.core.s := by
    refine Restated.slot_ge_of_awake_of_slotStart facts S Sched x hmult htd ?_
      (Restated.sent_of_deliver facts S Sched x hlbl).2 hwd
      (fun n' t' hn' hΔ hq _ hhi' => Restated.tick_outcome_of_tickStepAt_honest facts S Sched x
        hexec.idealization.root_injective hexec.honestRootsNew hn' hΔ hq (fun t'' ht'' => hwd t'' (le_trans ht'' hhi')))
    have h1 := Restated.slotStart_le_time_of_mem_tree facts S Sched x (i₀ + 1) v hmemT
    have h2 := Restated.time_mono_int facts S Sched x (show k + 1 ≤ d by omega)
    linarith
  have hfin : Block.preceq (x[d][w].st).st.core.F B.erase = true :=
    preceq_eq_true_iff_Preceq.mpr
      (preceq_trans_Preceq (Restated.F_mono facts S Sched x w (show d ≤ j by omega)) hF)
  have hbd : B ∈ (x[d + 1][w].st).st.bodies :=
    Restated.block_admitted_of_deliver_of_tree facts S Sched x hexec hlbl hwd hmemT hgen hslot hfin
  simp only [Restated.Read.blocks]
  exact of_decide_eq_true (Restated.processed_mono facts S Sched x w (NamedObject.block B) hdj
    (decide_eq_true hbd))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If every honest send is delivered before `max t g + Δ` to the validators awake from the send
    through that deadline, a validator that wakes at `t_w` is delivered before `max t_w g + Δ` what
    honest validators sent before its wake, `g ≤ t₀`, and every validator the adversary does not
    hold is awake at every time from `t₀` to `tE ≥ t₀ + Δ`, then
    `CommonViewOfFinalizedDescendantsAt` holds at `t₀`. -/
theorem commonViewOfFinalizedDescendantsAt_of_delivery (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) {g : Int}
    (hsync : Restated.SynchronyFromWakeBy M S x (fun t => max t g + S.E.Δ))
    (hcatch : Restated.CatchUpOnWakeBy M S x (fun t => max t g + S.E.Δ))
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    {t₀ tE : Int} (hg : g ≤ t₀) (hlen : t₀ + S.E.Δ ≤ tE)
    (hawake : ∀ t : Int, t₀ ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) :
    Restated.CommonViewOfFinalizedDescendantsAt M S Sched x t₀ :=
  Restated.commonViewOfFinalizedDescendantsAt_of_deliveryBy facts S Sched x hexec hsync hcatch hmult htd
    (fun t ht => by have := max_le ht hg; linarith) hlen hawake

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- On an execution with `SynchronyFromWake` and `CatchUpOnWake`, if `t_GST ≤ tGAT` and every
    validator the adversary does not hold is awake at every time from `tGAT` to `tE ≥ tGAT + Δ`,
    then `CommonViewOfFinalizedDescendantsAt` holds at `tGAT`. -/
theorem commonViewOfFinalizedDescendantsAt_of_catchUp (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hcatch : Restated.CatchUpOnWake M S x)
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    {tGAT tE : Int} (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + S.E.Δ ≤ tE)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) :
    Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT :=
  Restated.commonViewOfFinalizedDescendantsAt_of_delivery facts S Sched x hexec hsync hcatch hmult htd hgst hlen
    hawake

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- On an execution with synchrony and catch-up on wake outside the period `[b₀, b₁)`, with
    `b₀ ≤ b₁`, `t_GST ≤ b₁`, `b₁ + Δ ≤ tAgain` and `tAgain + Δ ≤ tSafe`, if every validator the
    adversary does not hold is awake at every time from `tAgain` to `tSafe`, then
    `CommonViewOfFinalizedDescendantsAt` holds at `tAgain`. -/
theorem commonViewOfFinalizedDescendantsAt_afterPeriod (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) {b₀ b₁ tAgain tSafe : Int}
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁) (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁)
    (hb : b₀ ≤ b₁) (hg : S.E.t_GST ≤ b₁) (hAgain : b₁ + S.E.Δ ≤ tAgain)
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hSafe : tAgain + S.E.Δ ≤ tSafe)
    (hawake : ∀ t : Int, tAgain ≤ t → t ≤ tSafe →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) :
    Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tAgain :=
  Restated.commonViewOfFinalizedDescendantsAt_of_delivery facts S Sched x hexec
    (Restated.synchronyBy_of_outside facts S x hb hg hsync) (Restated.catchUpBy_of_outside facts S x hb hg hcatch) hmult htd
    (by have := S.E.Δ_pos; linarith) hSafe hawake

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- On an execution with synchrony and catch-up on wake outside the period `[b₀, b₁)`, with
    `t_GST ≤ tGAT` and `tGAT + Δ ≤ b₀`, if every validator the adversary does not hold is awake at
    every time from `tGAT` to `tE ≥ tGAT + Δ`, then `CommonViewOfFinalizedDescendantsAt` holds at
    `tGAT`. -/
theorem commonViewOfFinalizedDescendantsAt_beforePeriod (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) {b₀ b₁ tGAT tE : Int}
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁) (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁)
    (hgst : S.E.t_GST ≤ tGAT) (hb₀ : tGAT + S.E.Δ ≤ b₀)
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hlen : tGAT + S.E.Δ ≤ tE)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) :
    Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT := by
  refine Restated.commonViewOfFinalizedDescendantsAt_of_deliveryBy facts S Sched x hexec hsync hcatch hmult htd
    (fun t ht => ?_) hlen hawake
  have hm : max t S.E.t_GST ≤ tGAT := max_le ht hgst
  unfold deadlineOutside
  rw [if_pos (by linarith)]
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `Δ ≤ healingLengthη S gap + period`. -/
theorem delta_le_healingLengthη_add_period (facts : Record.Facts M) (S : Setup V) (gap : Nat) :
    S.E.Δ ≤ Restated.healingLengthη M S gap + (Restated.constants M S).period := by
  have hd : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hη := Restated.healingLengthη_nonneg facts S gap
  rw [Restated.period_eq facts S]
  nlinarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `Δ ≤ healingLengthη S gap + (gap + 2) · period`. -/
theorem delta_le_healingLengthη_add_gap_period (facts : Record.Facts M) (S : Setup V) (gap : Nat) :
    S.E.Δ ≤ Restated.healingLengthη M S gap + ((gap : Int) + 2) * (Restated.constants M S).period := by
  have h1 := Restated.delta_le_healingLengthη_add_period facts S gap
  have hper : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
  have hg : (0 : Int) ≤ (gap : Int) := Int.natCast_nonneg gap
  nlinarith

end

end DecoupledConsensusModel.Sts.Restated
