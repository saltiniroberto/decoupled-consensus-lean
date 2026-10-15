import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bRelay
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ConeCover

/-!
# Honest awake cover and recurring honest sends

Over a model `M : Record.Model V`: from the start of the phase on, at every instant some honest
validator is awake for the next delay, and then an honest send's payload is honestly re-sent in
every later window of one delay.
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

/-- Under monotone corruption and `committeeSleepinessW S Sched tE`, if `0 ≤ t` and `tE ≤ t + Δ`,
    some honest committee member is awake throughout `[t, t + Δ]` and not held by the adversary at
    `t + Δ`. -/
theorem honestAwakeCover_of_committee (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (hmono : Sched.MonotoneCorruption) {tE t : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE) (ht0 : 0 ≤ t) (htE : tE ≤ t + S.E.Δ) :
    HonestAwakeCover S Sched t := by
  have hd := S.E.Δ_pos
  obtain ⟨hlo, hhi⟩ := slotStart_succ_slotOf_bounds S ht0
  have hsucc : slotStart S.E.Δ (S.E.slotOf t + 1 + 1)
      = slotStart S.E.Δ (S.E.slotOf t + 1) + 4 * S.E.Δ :=
    slotStart_succ S.E.Δ (S.E.slotOf t + 1)
  have hanchor : tE ≤ slotStart S.E.Δ (S.E.slotOf t + 1 + 1) := by
    rw [hsucc]; linarith
  have hlt := hcs (S.E.slotOf t + 1 + 1) (Nat.le_add_left 1 _) hanchor
  rw [Nat.add_sub_cancel] at hlt
  have hne : 0 < ((activeAtW S Sched (S.E.slotOf t + 1) ∩ S.E.committee (S.E.slotOf t + 1)) \
      Sched.adv (M.confirmation_time S.E (S.E.slotOf t + 1))).card :=
    lt_of_le_of_lt (Nat.zero_le _) hlt
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hne
  have hvH : v ∈ Restated.HonSlot M S Sched (S.E.slotOf t + 1) := hv
  obtain ⟨hact, -, hnadv⟩ := (Restated.mem_HonSlot facts).mp hvH
  have hw5 := five_delta_le_wVote S
  have hct : M.confirmation_time S.E (S.E.slotOf t + 1)
      = slotStart S.E.Δ (S.E.slotOf t + 1) + 6 * S.E.Δ :=
    (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (S.E.slotOf t + 1)).symm
  refine ⟨v, awakeThroughout_mono Sched hact (by linarith) (by linarith), ?_⟩
  intro hm
  exact hnadv (hmono (t + S.E.Δ) _ (by rw [hct]; linarith) hm)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- From the start of the phase on, at every instant some validator is awake for the next delay and
    not held by the adversary at its end: inside the phase because every honest validator is awake
    and the adversary holds less than a third of the weight, after it by committee sleepiness. -/
theorem honestAwakeCover_of_premises (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (hmono : Sched.MonotoneCorruption) {tGAT tE : Int} (hgst : S.E.t_GST ≤ tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hcs : Restated.committeeSleepinessW M S Sched tE) {t : Int} (ht : tGAT ≤ t) :
    HonestAwakeCover S Sched t := by
  by_cases h : t + S.E.Δ ≤ tE
  · exact honestAwakeCover_of_phase S Sched hmono (hthird _ h) hawake ht h
  · have h0 : 0 ≤ t := le_trans S.E.t_GST_nonneg (le_trans hgst ht)
    exact Restated.honestAwakeCover_of_committee facts S Sched hmono hcs h0 (by linarith)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If an honest validator sent `o` at step `k`, at or after GST, and some validator is awake for
    the delay from that step's instant, then at a later step, before that delay is over, some
    validator honestly sends `o` again. The hypothesis `hne` asks that every delivery of `⟨v_0, o⟩`
    to a validator `w` have an outcome of `w`'s receipt of `o`. -/
theorem honestSend_step (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hsync : Restated.SynchronyFromWake M S x) {k : Nat} {v_0 : V} {o : NamedObject V}
    (hsend : Restated.HonestSendAt M S x k (⟨v_0, o⟩ : SignedMsg V (NamedObject V)))
    (hgst : S.E.t_GST ≤ (x[k].time : Int))
    (hcov : HonestAwakeCover S Sched (x[k].time : Int))
    -- every delivery of `⟨v_0, o⟩` has an outcome from the node state the receiver holds before it
    (hne : ∀ (d : Nat) (w : V), x.lbl d = AtomicAction.deliver w ⟨v_0, o⟩ →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[d][w].st) o ⇢ n') :
    ∃ k' : Nat, ∃ v' : V, k < k' ∧
      Restated.HonestSendAt M S x k' (⟨v', o⟩ : SignedMsg V (NamedObject V)) ∧
      (x[k'].time : Int) < (x[k].time : Int) + S.E.Δ := by
  obtain ⟨v, hv, -⟩ := hcov
  have hmax : max (x[k].time : Int) S.E.t_GST = (x[k].time : Int) := max_eq_left hgst
  obtain ⟨d, hkd, hlt, hl⟩ := Restated.deliver_of_honestSendAt facts S Sched x hsync
    (D := (x[k].time : Int) + S.E.Δ) hsend (by rw [hmax]) (by rw [hmax]; exact hv)
  have ho : o ∈ relayedObjects
      (⟨v_0, o⟩ : SignedMsg V (NamedObject V)).msg :=
    (mem_relayedObjects_iff _ _).mpr (Or.inl rfl)
  exact ⟨d, v, hkd, Restated.honestSendAt_of_deliver_relay facts S Sched x hl ho
    (hne d v hl), hlt⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If an honest validator sent `o` at or after GST, and from then on some validator is always awake
    for a delay, then every later window `[t, t + Δ)` contains a step at which some validator
    honestly sends `o`. The hypothesis `hne` asks that every delivery of `o`, under any signer, have
    an outcome of the receiver's receipt. -/
theorem honestSend_recurs (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hsync : Restated.SynchronyFromWake M S x) (htd : Restated.TimeDiverges M x)
    {k : Nat} {v_0 : V} {o : NamedObject V}
    (hsend : Restated.HonestSendAt M S x k (⟨v_0, o⟩ : SignedMsg V (NamedObject V)))
    (hgst : S.E.t_GST ≤ (x[k].time : Int))
    (hcover : ∀ t : Int, (x[k].time : Int) ≤ t → HonestAwakeCover S Sched t)
    -- every delivery of `o`, under any signer, has an outcome from the node state the receiver
    -- holds before it
    (hne : ∀ (d : Nat) (w v' : V), x.lbl d = AtomicAction.deliver w ⟨v', o⟩ →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[d][w].st) o ⇢ n') :
    ∀ t : Int, (x[k].time : Int) ≤ t →
      ∃ k' : Nat, ∃ v' : V, Restated.HonestSendAt M S x k' (⟨v', o⟩ : SignedMsg V (NamedObject V)) ∧
        t ≤ (x[k'].time : Int) ∧ (x[k'].time : Int) < t + S.E.Δ := by
  classical
  intro t ht
  -- `Q j`: step `j` is an honest send of `o`, at or after `k`.
  let Q : Nat → Prop := fun j =>
    (∃ v' : V, Restated.HonestSendAt M S x j (⟨v', o⟩ : SignedMsg V (NamedObject V))) ∧ k ≤ j
  have hstep : ∀ j, Q j → ∃ j', j < j' ∧ Q j' ∧
      (x[j'].time : Int) < (x[j].time : Int) + S.E.Δ := by
    intro j ⟨⟨v', hv'⟩, hkj⟩
    have hmono := Restated.time_mono_int facts S Sched x hkj
    obtain ⟨j', v'', hjj, hs, hlt⟩ :=
      Restated.honestSend_step facts S Sched x hsync hv' (le_trans hgst hmono) (hcover _ hmono)
        (fun d w hl => hne d w v' hl)
    exact ⟨j', hjj, ⟨⟨v'', hs⟩, le_trans hkj (le_of_lt hjj)⟩, hlt⟩
  let nxt : Nat → Nat := fun j => if h : Q j then Classical.choose (hstep j h) else j
  have hnxt : ∀ j, Q j → j < nxt j ∧ Q (nxt j) ∧
      (x[nxt j].time : Int) < (x[j].time : Int) + S.E.Δ := by
    intro j hj
    have := Classical.choose_spec (hstep j hj)
    simp only [nxt, dif_pos hj]
    exact this
  let seq : Nat → Nat := fun n => nxt^[n] k
  have hseq_succ : ∀ n, seq (n + 1) = nxt (seq n) := fun n =>
    Function.iterate_succ_apply' nxt n k
  have hQ : ∀ n, Q (seq n) := by
    intro n
    induction n with
    | zero => exact ⟨⟨v_0, hsend⟩, le_refl k⟩
    | succ n ih => rw [hseq_succ]; exact (hnxt _ ih).2.1
  have hge : ∀ n, n ≤ seq n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => rw [hseq_succ]; exact lt_of_le_of_lt ih (hnxt _ (hQ n)).1
  have hex : ∃ n, t ≤ (x[seq n].time : Int) := by
    obtain ⟨i, hi⟩ := htd t.toNat
    refine ⟨i, ?_⟩
    have h1 : t ≤ ((t.toNat : Nat) : Int) := Int.self_le_toNat t
    have h2 : ((t.toNat : Nat) : Int) ≤ (x[i].time : Int) := by exact_mod_cast hi
    exact le_trans h1 (le_trans h2 (Restated.time_mono_int facts S Sched x (hge i)))
  let n₀ := Nat.find hex
  have hn₀ : t ≤ (x[seq n₀].time : Int) := Nat.find_spec hex
  obtain ⟨⟨v', hv'⟩, -⟩ := hQ n₀
  refine ⟨seq n₀, v', hv', hn₀, ?_⟩
  cases hcase : n₀ with
  | zero =>
      have hk : (x[seq 0].time : Int) = (x[k].time : Int) := rfl
      have hd := S.E.Δ_pos
      have : (x[seq 0].time : Int) ≤ t := by rw [hk]; exact ht
      linarith
  | succ n =>
      have hmin : ¬ t ≤ (x[seq n].time : Int) :=
        Nat.find_min hex (show n < n₀ by omega)
      have hlt := (hnxt _ (hQ n)).2.2
      rw [← hseq_succ] at hlt
      linarith

end

end DecoupledConsensusModel.Sts.Restated
