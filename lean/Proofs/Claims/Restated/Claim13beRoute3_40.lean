import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_19
import Proofs.Claims.Restated.Claim13beRoute3_22
import Proofs.Claims.Restated.Claim13beRoute3_24
import Proofs.Claims.Restated.Claim13beRoute3_25
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.RunAll
import Model.Conditions.Vocabulary_Protocol_Schedule_Alignment
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_40

/-!
# The receiver's slot at block deliveries

Every delivery of a block at or after its proposal time finds the receiver's slot at least the
block's slot. Stated over a model `M : Record.Model V`.
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

/-- Under monotone corruption and wakes at multiples of `Δ`, if every tick the execution performs
    for a validator honest up to its time has an outcome, then in the run of the first `n` steps
    with any honest set, every delivery of a block `B` to a validator `w` at a time at or after
    `B`'s proposal time finds `w`'s slot at least `B`'s, in the world the path `x` follows holds
    before that delivery. -/
theorem receiver_slot_at_deliveries_runAll (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (H : Finset V) (n : Nat)
    (hmono : Sched.MonotoneCorruption) (hawm : AwakeAtMultiples S Sched)
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out)
    {w : V} {B : NamedBlock V} :
    ∀ (j : Nat) (td : Int),
      ({ Restated.runAll M S Sched x v n with honest := H } : Record.Run V).events[j]? =
        some (.deliver w (.block B) td) →
      M.proposal_time S.E B.erase.slot ≤ td →
      B.erase.slot ≤ (Restated.runAllPath M S Sched x v n j w).st.core.s := by
  intro j td hdeliver hlo
  have hP := Restated.OnePath_runAllPath facts S Sched x v n
  have hto := Restated.tick_outcome_runAllPath facts S Sched x v n hmono hnr
  by_cases h0 : B.erase.slot = 0
  · rw [h0]; exact Nat.zero_le _
  have hΔ : 0 < S.E.Δ := S.E.Δ_pos
  have hpos : 0 < M.proposal_time S.E B.erase.slot :=
    facts.sch.proposal_time_pos_of_slot_pos S.E (Nat.pos_of_ne_zero h0)
  have hsorted := Restated.sorted_runAll_withHonest_events facts S Sched x v H n
  have hin := Restated.in_horizon_runAll_withHonest facts S Sched x v H n
  obtain ⟨htd0, htdhor⟩ := hin _ (List.mem_of_getElem? hdeliver)
  replace htd0 : 0 ≤ td := htd0
  replace htdhor : td ≤ (x[n].time : Int) := htdhor
  -- the delivery step, and the receiver awake and not held there
  have hdeliver' : (Restated.runEvents M S Sched x n)[j]? =
      some (.deliver w (.block B) td) := hdeliver
  obtain ⟨k, -, hmem⟩ := Restated.exists_step_of_mem_runEvents facts S Sched x n
    (List.mem_of_getElem? hdeliver')
  obtain ⟨sm, hl, -, ht⟩ := Restated.deliver_of_mem_actionEventsOf hmem
  have hs := x.step k
  rw [hl] at hs
  have haw : w ∈ Sched.awake td := by rw [ht]; exact hs.1.2.1
  have hnadv : w ∉ Sched.adv td := by rw [ht]; exact hs.1.2.2
  -- the latest multiple of `Δ` at or before the delivery
  set q := td / S.E.Δ * S.E.Δ with hq
  have hqle : q ≤ td := Int.ediv_mul_le td (ne_of_gt hΔ)
  have hqaw : w ∈ Sched.awake q := awake_at_floor_of_awakeAtMultiples S Sched hawm haw
  have hqadv : w ∉ Sched.adv q := fun h => hnadv (hmono _ _ hqle h)
  have hPq : M.proposal_time S.E B.erase.slot ≤ q := by
    obtain ⟨kk, hkk⟩ := Restated.Vocabulary.Proofs.Optimistic.publicTime_proposal_time facts S B.erase.slot
    rw [hkk] at hlo ⊢
    have hdiv : (kk : Int) ≤ td / S.E.Δ := Int.le_ediv_of_mul_le hΔ hlo
    rw [hq]
    exact Int.mul_le_mul_of_nonneg_right hdiv (le_of_lt hΔ)
  have hpub : Execution.PublicTime (Setup.alwaysAwake S) q := by
    refine ⟨(td / S.E.Δ).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (Int.ediv_nonneg htd0 (le_of_lt hΔ))]
    rfl
  have htickEv := Restated.tickAtAwake_runAll_withHonest facts S Sched x v H n w q hpub
    (lt_of_lt_of_le hpos hPq) (le_trans hqle htdhor) hqaw hqadv
  have hclock := Restated.Vocabulary.Proofs.NamedRawRelay.tick_le_clock_before_delivery_of_fields facts
    (Setup.alwaysAwake S) _ hsorted hin (Restated.runAllPath M S Sched x v n) hP hto hdeliver
    htickEv hqle
  have hslot := Restated.Vocabulary.Proofs.NamedStoreBridge.slotOfClock_stateBefore facts (Setup.alwaysAwake S)
    { Restated.runAll M S Sched x v n with honest := H } j w _ (hP j).1
  unfold Restated.Vocabulary.Proofs.Optimistic.SlotOfClock at hslot
  rw [hslot]
  exact facts.sch.slot_le_slotOf_of_proposal_time_le S.E (le_trans hPq hclock)

end

end DecoupledConsensusModel.Sts.Restated
