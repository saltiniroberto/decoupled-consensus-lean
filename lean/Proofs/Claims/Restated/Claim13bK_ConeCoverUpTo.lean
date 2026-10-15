import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bRelayUpTo
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Record.Wiring

/-!
# Recurring honest sends, synchrony up to a bound

Over a model `M : Record.Model V`, with synchrony assumed only up to a bound: an honest send's
payload is honestly re-sent within one delay, and in every later window of one delay up to the
bound.
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

/-- With synchrony only up to `x[k].time + Δ`: if an honest validator sent `o` at step `k`, at or
    after GST, and some validator is awake for the delay from that step's instant, then at a later
    step, before that delay is over, some validator honestly sends `o` again. The hypothesis `hne`
    asks that every delivery of `⟨v_0, o⟩` to a validator `w` have an outcome of `w`'s receipt of
    `o`. -/
theorem honestSend_step_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {k : Nat} (hsync : Restated.SynchronyFromWakeBefore M S x ((x[k].time : Int) + S.E.Δ)) {v_0 : V} {o : NamedObject V}
    (hsend : Restated.HonestSendAt M S x k (⟨v_0, o⟩ : SignedMsg V (NamedObject V)))
    (hgst : S.E.t_GST ≤ (x[k].time : Int))
    (hcov : HonestAwakeCover S Sched (x[k].time : Int))
    (hne : ∀ (d : Nat) (w : V), x.lbl d = AtomicAction.deliver w ⟨v_0, o⟩ →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[d][w].st) o ⇢ n') :
    ∃ k' : Nat, ∃ v' : V, k < k' ∧
      Restated.HonestSendAt M S x k' (⟨v', o⟩ : SignedMsg V (NamedObject V)) ∧
      (x[k'].time : Int) < (x[k].time : Int) + S.E.Δ := by
  obtain ⟨v, hv, -⟩ := hcov
  have hmax : max (x[k].time : Int) S.E.t_GST = (x[k].time : Int) := max_eq_left hgst
  have hsync' : Restated.SynchronyFromWakeBefore M S x
      (max (x[k].time : Int) S.E.t_GST + S.E.Δ) :=
    fun k' w sm hs' hle haw => hsync k' w sm hs' (le_trans hle (by rw [hmax])) haw
  obtain ⟨d, hkd, hlt, hl⟩ := Restated.deliver_of_honestSendAt_upTo facts S Sched x
    hsync' (D := (x[k].time : Int) + S.E.Δ) hsend (by rw [hmax]) (by rw [hmax]; exact hv)
  have ho : o ∈ relayedObjects
      (⟨v_0, o⟩ : SignedMsg V (NamedObject V)).msg :=
    (mem_relayedObjects_iff _ _).mpr (Or.inl rfl)
  exact ⟨d, v, hkd, Restated.honestSendAt_of_deliver_relay facts S Sched x hl ho (hne d v hl), hlt⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- With synchrony only up to `tEnd + Δ`: if an honest validator sent `o` at or after GST, and from
    then on some validator is always awake for a delay, then every later window `[t, t + Δ)` with
    `t ≤ tEnd` contains a step at which some validator honestly sends `o`. The hypothesis `hne` asks
    that every delivery of `o`, under any signer, have an outcome of the receiver's receipt. -/
theorem honestSend_recurs_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {k : Nat} {tEnd : Int}
    (hsync : Restated.SynchronyFromWakeBefore M S x (tEnd + S.E.Δ)) (htd : Restated.TimeDiverges M x)
    {v_0 : V} {o : NamedObject V}
    (hsend : Restated.HonestSendAt M S x k (⟨v_0, o⟩ : SignedMsg V (NamedObject V)))
    (hgst : S.E.t_GST ≤ (x[k].time : Int))
    (hcover : ∀ t : Int, (x[k].time : Int) ≤ t → HonestAwakeCover S Sched t)
    (hne : ∀ (d : Nat) (w v' : V), x.lbl d = AtomicAction.deliver w ⟨v', o⟩ →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[d][w].st) o ⇢ n') :
    ∀ t : Int, (x[k].time : Int) ≤ t → t ≤ tEnd →
      ∃ k' : Nat, ∃ v' : V, Restated.HonestSendAt M S x k' (⟨v', o⟩ : SignedMsg V (NamedObject V)) ∧
        t ≤ (x[k'].time : Int) ∧ (x[k'].time : Int) < t + S.E.Δ := by
  classical
  intro t ht htEnd
  -- `Q j`: step `j` is an honest send of `o`, at or after `k`.
  let Q : Nat → Prop := fun j =>
    (∃ v' : V, Restated.HonestSendAt M S x j (⟨v', o⟩ : SignedMsg V (NamedObject V))) ∧ k ≤ j
  have hstep : ∀ j, Q j → (x[j].time : Int) < t → ∃ j', j < j' ∧ Q j' ∧
      (x[j'].time : Int) < (x[j].time : Int) + S.E.Δ := by
    intro j ⟨⟨v', hv'⟩, hkj⟩ hjt
    have hmono := Restated.time_mono_int facts S Sched x hkj
    obtain ⟨j', v'', hjj, hs, hlt⟩ :=
      Restated.honestSend_step_upTo facts S Sched x
        (fun k' w sm hs' hle haw => hsync k' w sm hs' (le_trans hle (by linarith)) haw) hv'
        (le_trans hgst hmono)
        (hcover _ hmono) (fun d w hl => hne d w v' hl)
    exact ⟨j', hjj, ⟨⟨v'', hs⟩, le_trans hkj (le_of_lt hjj)⟩, hlt⟩
  let nxt : Nat → Nat := fun j =>
    if h : Q j ∧ (x[j].time : Int) < t then Classical.choose (hstep j h.1 h.2) else j
  have hnxt : ∀ j, Q j → (x[j].time : Int) < t → j < nxt j ∧ Q (nxt j) ∧
      (x[nxt j].time : Int) < (x[j].time : Int) + S.E.Δ := by
    intro j hj hjt
    have := Classical.choose_spec (hstep j hj hjt)
    simp only [nxt, dif_pos (And.intro hj hjt)]
    exact this
  have hnxt_stop : ∀ j, ¬ (x[j].time : Int) < t → nxt j = j := by
    intro j hjt
    simp only [nxt, dif_neg (fun h : Q j ∧ (x[j].time : Int) < t => hjt h.2)]
  let seq : Nat → Nat := fun n => nxt^[n] k
  have hseq_succ : ∀ n, seq (n + 1) = nxt (seq n) := fun n =>
    Function.iterate_succ_apply' nxt n k
  have hQ : ∀ n, Q (seq n) := by
    intro n
    induction n with
    | zero => exact ⟨⟨v_0, hsend⟩, le_refl k⟩
    | succ n ih =>
        rw [hseq_succ]
        by_cases hjt : (x[seq n].time : Int) < t
        · exact (hnxt _ ih hjt).2.1
        · rw [hnxt_stop _ hjt]; exact ih
  have hex : ∃ n, t ≤ (x[seq n].time : Int) := by
    by_contra hne
    push_neg at hne
    have hge : ∀ n, n ≤ seq n := by
      intro n
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih => rw [hseq_succ]; exact lt_of_le_of_lt ih (hnxt _ (hQ n) (hne n)).1
    obtain ⟨i, hi⟩ := htd t.toNat
    have h1 : t ≤ ((t.toNat : Nat) : Int) := Int.self_le_toNat t
    have h2 : ((t.toNat : Nat) : Int) ≤ (x[i].time : Int) := by exact_mod_cast hi
    have h3 := Restated.time_mono_int facts S Sched x (hge i)
    have h4 := hne i
    linarith
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
      have hlt := (hnxt _ (hQ n) (not_le.mp hmin)).2.2
      rw [← hseq_succ] at hlt
      linarith

end

end DecoupledConsensusModel.Sts.Restated
