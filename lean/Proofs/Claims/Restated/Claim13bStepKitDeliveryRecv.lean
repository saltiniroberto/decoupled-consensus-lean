import Proofs.Claims.Restated.Claim13bW_ReceiptRule
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepGrade

/-!
# Recorded attestations from a receipt, with a tick at every clock reading

The delivery kit's window test and recorded attestations without an awake window for the
receiver: since a validator awake and not held at a time ticks at that time before any delivery
there, its store clock at a delivery is the delivery's time. Stated over a model
`M : Record.Model V` and its facts `facts : Record.Facts M`.
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

/-- If step `k` delivers a message to `w` at a positive time, `w` is honest through that time, and
    every tick of a validator awake and not held up to it has an outcome, then `w`'s store clock at
    step `k` is the time of step `k`. -/
theorem clock_eq_time_of_deliver (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k : Nat} {w : V}
    {sm : SignedMsg V (NamedObject V)} (hl : x.lbl k = AtomicAction.deliver w sm)
    (hpos : 0 < (x[k].time : Int))
    (hw : HonestThroughTime Sched (x[k].time : Int) w)
    -- Every tick of a validator awake and not held by the adversary up to it has an outcome.
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out) :
    (x[k][w].st).st.core.t = (x[k].time : Int) := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  have hwk : w ∈ Sched.awake (x[k].time : Int) \ Sched.adv (x[k].time : Int) :=
    Finset.mem_sdiff.2 ⟨hs.1.2.1, hw _ le_rfl⟩
  obtain ⟨j, hjk, hlj, -, -⟩ := tickAllAwake_of_time x k (rfl : x[k].time = x[k].time) (by omega)
  have hne := hnr j (x[k].time) w hlj hwk hw
  have hge := Restated.clock_ge_of_tickStepAt_awake_sts facts S Sched x (t := (x[k].time : Int))
    ⟨x[k].time, hlj, rfl⟩ hwk hne (Nat.succ_le_of_lt hjk)
  exact le_antisymm (Restated.clock_le_time_sts facts S Sched x k w) hge

/-- With every tick of a validator awake and not held up to it having an outcome: if `a` names
    `v`, `v` and `w` are honest through the time of step `j`, and the round of that time's slot is
    at most `a.round + η_SG`, then no delivery of `⟨v, .attest a⟩` to `w` before step `j` finds `a`
    stale or of a future round. -/
theorem window_of_deliver_recv (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {j : Nat} {v w : V} {a : NamedAttestation V}
    (hv : HonestThroughTime Sched (x[j].time : Int) v)
    (hw : HonestThroughTime Sched (x[j].time : Int) w)
    (hunf : Restated.Unforgeability M S x) (hidx : a.val_index = v)
    (hexp : (M.round_of S.hc (S.E.slotOf (x[j].time : Int))) ≤ a.round + S.hc.η_SG)
    -- Every tick of a validator awake and not held by the adversary up to it has an outcome.
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out) :
    ∀ k : Nat, k < j →
      x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ →
      ¬ (a.round < (M.round_of S.hc (x[k][w].st).st.core.s) - S.hc.η_SG ∨
         (M.round_of S.hc (x[k][w].st).st.core.s) < a.round) := by
  intro k hkj hlbl
  have hkt : (x[k].time : Int) ≤ (x[j].time : Int) := Restated.time_mono_int facts S Sched x (le_of_lt hkj)
  have hvk : HonestThroughTime Sched (x[k].time : Int) v :=
    fun t ht => hv t (le_trans ht hkt)
  obtain ⟨-, -, -, -, -, hact⟩ := Restated.deliver_attest_after_action facts S Sched x hvk hunf hidx hlbl
  have hpos : 0 < (x[k].time : Int) := lt_of_lt_of_le (Restated.action_pos facts S a.round) hact
  have hclock : (x[k][w].st).st.core.t = (x[k].time : Int) :=
    clock_eq_time_of_deliver facts S Sched x hlbl hpos (fun t ht => hw t (le_trans ht hkt)) hnr
  have hge : a.round ≤ (M.round_of S.hc (x[k][w].st).st.core.s) :=
    Restated.receiver_round_ge_of_clock_ge facts S Sched x k w a.round (by rw [hclock]; exact hact)
  have hle : (M.round_of S.hc (x[k][w].st).st.core.s) ≤ a.round + S.hc.η_SG :=
    le_trans (Restated.receiver_round_le_of_time_le facts S Sched x k w hkt) hexp
  have hsub : (M.round_of S.hc (x[k][w].st).st.core.s) - S.hc.η_SG ≤ a.round :=
    Nat.sub_le_iff_le_add.mpr hle
  rintro (h | h)
  · exact absurd h (Nat.not_lt.mpr hsub)
  · exact absurd h (Nat.not_lt.mpr hge)

/-- `attest_recorded_of_mem_view` with the window test discharged by `window_of_deliver_recv`. -/
theorem attest_recorded_of_mem_view_recv (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {j : Nat} {v w : V} {a : NamedAttestation V}
    (hview : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[j][w].view)
    (haw : AtomicAwake x j w)
    (hv : HonestThroughTime Sched (x[j].time : Int) v)
    (hw : HonestThroughTime Sched (x[j].time : Int) w)
    (hunf : Restated.Unforgeability M S x) (hidx : a.val_index = v)
    (hexp : (M.round_of S.hc (S.E.slotOf (x[j].time : Int))) ≤ a.round + S.hc.η_SG)
    (hroom : ∀ k : Nat, k < j →
      x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ →
      (M.round_votes (x[k][w].st).st.core a.erase).card ≠ 2)
    -- Every tick of a validator awake and not held by the adversary up to it has an outcome.
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out)
    (hne : ∀ k : Nat, k < j →
      x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[k][w].st) (NamedObject.attest a) ⇢ n') :
    ∃ k : Nat, k < j ∧ x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ ∧
      (a.erase.confirmed ∈ M.round_votes (x[k][w].st).st.core a.erase ∨
        (a ∈ (x[k + 1][w].st).st.sg_rows a.round ∧
          a ∈ (x[j][w].st).st.sg_rows a.round ∧
          (x[k + 1][w].st).st.core.timestamp_sg_vote (M.sgVote a.erase)
            = some (((x[k][w].st).st.core.t : Stamp)))) :=
  Restated.attest_recorded_of_mem_view facts S Sched x hview haw
    (window_of_deliver_recv facts S Sched x hv hw hunf hidx hexp hnr) hroom hne

/-- From a receipt of round `a.round`'s attestations before `bound`: if step `n` is the tick at
    `S.a a.round` and `⟨v, .attest a⟩` was sent honestly there, `a` names `v`, `v` and `w` are honest
    through step `m` with `bound ≤ x[m].time`, the round of `x[m].time`'s slot is at most
    `a.round + η_SG`, and no delivery to `w` before step `m` finds two heads, then some delivery `k`
    of it to `w`, with `k + 1 ≤ m`, happened strictly before `bound`, and there `w` already held the
    sender's head for the round, or the row was written with the stamp of `w`'s clock. -/
theorem attest_recorded_of_receipt_recv (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hunf : Restated.Unforgeability M S x)
    {n m : Nat} {v w : V} {a : NamedAttestation V} {bound : Int}
    (hn : Restated.tickStepAt M x n (Restated.Vocabulary.Execution.Setup.a M S a.round))
    (hsend : Restated.HonestSendAt M S x n (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)))
    (hidx : a.val_index = v)
    (hrecv : ReceivesRoundAttestationsBefore M S Sched x a.round w bound)
    (hbm : bound ≤ (x[m].time : Int))
    (hv : HonestThroughTime Sched (x[m].time : Int) v)
    (hw : HonestThroughTime Sched (x[m].time : Int) w)
    (hexp : (M.round_of S.hc (S.E.slotOf (x[m].time : Int))) ≤ a.round + S.hc.η_SG)
    (hroom : ∀ k : Nat, k < m →
      x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ →
      (M.round_votes (x[k][w].st).st.core a.erase).card ≠ 2)
    -- Every tick of a validator awake and not held by the adversary up to it has an outcome.
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out) :
    ∃ k : Nat, k + 1 ≤ m ∧ x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ ∧
      (x[k].time : Int) < bound ∧
      (a.erase.confirmed ∈ M.round_votes (x[k][w].st).st.core a.erase ∨
        (a ∈ (x[k + 1][w].st).st.sg_rows a.round ∧
          (x[k + 1][w].st).st.core.timestamp_sg_vote (M.sgVote a.erase)
            = some (((x[k][w].st).st.core.t : Stamp)))) := by
  obtain ⟨d, -, hld, hdb⟩ := hrecv n v a hn hsend rfl hidx
  have hdm : d < m := by
    by_contra hcon
    have h := Restated.time_mono_int facts S Sched x (Nat.le_of_not_lt hcon)
    linarith
  have hd1m : d + 1 ≤ m := Nat.succ_le_of_lt hdm
  have hd1le : (x[d + 1].time : Int) ≤ (x[m].time : Int) := Restated.time_mono_int facts S Sched x hd1m
  have hview : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[d + 1][w].view :=
    Restated.mem_view_succ_of_deliver facts S Sched x hld
  have hdtime : x[d + 1].time = x[d].time := Restated.deliver_time facts S Sched x hld
  have haw : AtomicAwake x (d + 1) w := by
    have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl d) x[d] x[d + 1] := x.step d
    rw [hld] at hs
    show w ∈ Sched.awake (x[d + 1].time : Int)
    rw [hdtime]; exact hs.1.2.1
  have hexp' : (M.round_of S.hc (S.E.slotOf (x[d + 1].time : Int))) ≤ a.round + S.hc.η_SG :=
    le_trans (facts.gr.round_of_mono_sts S.hc (slotOf_mono_sts S hd1le)) hexp
  obtain ⟨k, hkj, hlbl, hcase⟩ :=
    attest_recorded_of_mem_view_recv facts S Sched x hview haw
      (fun t ht => hv t (le_trans ht hd1le)) (fun t ht => hw t (le_trans ht hd1le)) hunf hidx hexp'
      (fun k hk hl => hroom k (lt_of_lt_of_le hk hd1m) hl) hnr
      (fun k _ _ => facts.nd.process_nonempty _ _ _ (fun _ h => by cases h))
  have hkd : (x[k].time : Int) ≤ (x[d].time : Int) :=
    Restated.time_mono_int facts S Sched x (Nat.le_of_lt_succ hkj)
  exact ⟨k, le_trans (Nat.succ_le_of_lt hkj) hd1m, hlbl, lt_of_le_of_lt hkd hdb,
    hcase.imp id (fun h => ⟨h.1, h.2.2⟩)⟩

end

end DecoupledConsensusModel.Sts.Restated
