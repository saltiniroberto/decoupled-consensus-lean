import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRecord
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13beRoute3_4
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_6

/-!
# Store clocks and slots of awake validators

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, on an execution
`x`: the store clock of a validator awake at a step is at or after every multiple of the delay that
has passed, its store's slot is at or after every slot that has started, and every block in a
store's tree is of a slot that has started.
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

/-- If `t` is a multiple of the delay, at or before step `m`'s instant and strictly within one delay
    of it, `v` is awake at step `m`'s instant, and `v`'s tick at `t` has an outcome, then `v`'s
    store clock at step `m` is at or after `t`. -/
theorem clock_ge_of_awake_of_multiple_near (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x) {m : Nat} {v : V} {t : Int}
    (hdvd : t % S.E.Δ = 0) (hle : t ≤ (x[m].time : Int))
    (hnear : (x[m].time : Int) < t + S.E.Δ)
    (haw : v ∈ Sched.awake (x[m].time : Int)) (hvh : Restated.HonestThrough M Sched x m v)
    (hneTick : ∀ n' : Nat, Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → v ∈ Sched.awake t \ Sched.adv t →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t x[n'] v) t ⇢ out) :
    t ≤ (x[m][v].st).st.core.t := by
  have hd : (0 : Int) < S.E.Δ := S.E.Δ_pos
  by_cases hpos : 0 < t
  case neg => exact le_trans (not_lt.mp hpos) (Restated.clock_nonneg_sts facts S Sched x m v)
  have hq : S.E.Δ * (t / S.E.Δ) = t := Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hdvd)
  have hnn : (0 : Int) ≤ (x[m].time : Int) - t := by linarith
  have hkeq : t + ((((x[m].time : Int) - t).toNat : Nat) : Int) = (x[m].time : Int) := by
    rw [Int.toNat_of_nonneg hnn]; ring
  have hklt : ((((x[m].time : Int) - t).toNat : Nat) : Int) < S.E.Δ := by
    rw [Int.toNat_of_nonneg hnn]; linarith
  have hawt : v ∈ Sched.awake t := by
    refine awake_of_awake_later S Sched hmult t ((x[m].time : Int) - t).toNat ?_ ?_
    · intro j hj1 hj2
      have hj0 : (0 : Int) < (j : Int) := by exact_mod_cast hj1
      have hjle : ((j : Nat) : Int) ≤ ((((x[m].time : Int) - t).toNat : Nat) : Int) := by
        exact_mod_cast hj2
      have hjlt : (j : Int) < S.E.Δ := lt_of_le_of_lt hjle hklt
      have hsum : t + (j : Int) = (j : Int) + S.E.Δ * (t / S.E.Δ) := by rw [hq]; ring
      rw [hsum, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (le_of_lt hj0) hjlt]
      omega
    · rw [hkeq]; exact haw
  obtain ⟨n, hn⟩ := Restated.exists_tickStepAt facts x htd hpos
  obtain ⟨-, hnb⟩ := Restated.tickStepAt_time facts x hn
  have hnm : n + 1 ≤ m := by
    by_contra hcon
    have hmn : m ≤ n := by omega
    have hmono := Restated.time_mono_int facts S Sched x hmn
    linarith
  exact Restated.clock_ge_of_tickStepAt_awake_sts facts S Sched x hn (Finset.mem_sdiff.2 ⟨hawt, hvh _ hle⟩)
    hdvd (hneTick n hn hdvd (Finset.mem_sdiff.2 ⟨hawt, hvh _ hle⟩)) hnm

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `t` is a multiple of the delay at or before step `m`'s instant, `v` is awake at that instant,
    and `v`'s ticks at the multiples of the delay from `t` to that instant have an outcome, then
    `v`'s store clock at step `m` is at or after `t`. -/
theorem clock_ge_of_awake_of_multiple (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    {m : Nat} {v : V} {t : Int} (hdvd : t % S.E.Δ = 0) (hle : t ≤ (x[m].time : Int))
    (haw : v ∈ Sched.awake (x[m].time : Int)) (hvh : Restated.HonestThrough M Sched x m v)
    (hneTick : ∀ (n' : Nat) (t' : Int), Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' →
      t ≤ t' → t' ≤ (x[m].time : Int) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out) :
    t ≤ (x[m][v].st).st.core.t := by
  have hd : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hdm := Int.mul_ediv_add_emod (x[m].time : Int) S.E.Δ
  have hmod0 : 0 ≤ (x[m].time : Int) % S.E.Δ := Int.emod_nonneg _ (ne_of_gt hd)
  have hmod1 : (x[m].time : Int) % S.E.Δ < S.E.Δ := Int.emod_lt_of_pos _ hd
  have hq : S.E.Δ * (t / S.E.Δ) = t := Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hdvd)
  have hmul : S.E.Δ * (t / S.E.Δ) ≤ S.E.Δ * ((x[m].time : Int) / S.E.Δ) :=
    Int.mul_le_mul_of_nonneg_left (Int.ediv_le_ediv hd hle) (le_of_lt hd)
  have hfl : S.E.Δ * ((x[m].time : Int) / S.E.Δ) ≤ (x[m][v].st).st.core.t :=
    Restated.clock_ge_of_awake_of_multiple_near facts S Sched x hmult htd (Int.mul_emod_right _ _)
      (by linarith) (by linarith) haw hvh
      (fun n' hn' hΔ hq => hneTick n' _ hn' hΔ hq (by linarith) (by linarith))
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If slot `s` starts at or before step `m`'s instant, `v` is awake there, and `v`'s ticks from the
    start of `s` to that instant have an outcome, then the slot of `v`'s store after `m` steps is at
    or after `s`. -/
theorem slot_ge_of_awake_of_slotStart (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    {m : Nat} {v : V} {s : Slot} (hstart : slotStart S.E.Δ s ≤ (x[m].time : Int))
    (haw : v ∈ Sched.awake (x[m].time : Int)) (hvh : Restated.HonestThrough M Sched x m v)
    (hneTick : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → v ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ (x[m].time : Int) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t x[n'] v) t ⇢ out) :
    s ≤ (x[m][v].st).st.core.s := by
  have hdvd : slotStart S.E.Δ s % S.E.Δ = 0 := slotStart_emod_delta S s
  have hclock : slotStart S.E.Δ s ≤ (x[m][v].st).st.core.t :=
    Restated.clock_ge_of_awake_of_multiple facts S Sched x hmult htd hdvd hstart haw hvh hneTick
  have hss : S.E.slotOf (slotStart S.E.Δ s) = s := _root_.DecoupledConsensusModel.Sts.slotOf_slotStart S s
  rw [Restated.slotOfClock_sts facts S Sched x m v, ← hss]
  exact slotOf_mono_sts S hclock

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If a block is in the tree of the store `q` holds after `n` steps, then that block's slot starts
    at or before step `n`'s instant. -/
theorem slotStart_le_time_of_mem_tree (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (n : Nat) (q : V) {X : Block V}
    (hX : X ∈ (x[n][q].st).st.core.T) : slotStart S.E.Δ X.slot ≤ (x[n].time : Int) := by
  have hb : X.slot ≤ (x[n][q].st).st.core.s := Restated.treeSlotBounded_sts facts S Sched x n q X hX
  rw [Restated.slotOfClock_sts facts S Sched x n q] at hb
  refine slotStart_le_of_le_slotOf S (Int.natCast_nonneg _) (le_trans hb ?_)
  exact slotOf_mono_sts S (Restated.clock_le_time_sts facts S Sched x n q)

end

end DecoupledConsensusModel.Sts.Restated
