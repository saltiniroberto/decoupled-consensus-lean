import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRecord
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Redelivery
import Proofs.Claims.Restated.RunAll
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13beRoute3_4
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_4

/-!
# Stores hold no block of a later slot

No store holds a block of a slot after its own, so the slot-`s` fork-choice head at a store whose
clock has not passed slot `s`'s vote time is of a slot at most `s`. Stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Sts.TreeSlotStep
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Leaving the store alone is a `TreeSlotStep`. -/
theorem TreeSlotStep.refl' (facts : Record.Facts M) (st : M.S) : Restated.TreeSlotStep M st st := fun h => h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After a tick step at `τ`, either `v`'s store is unchanged, or `v`'s next node state is that of
    an outcome of `v`'s tick at `τ` from a node state whose store is `v`'s store before the step. -/
private theorem st_succ_of_tick₃₄ (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k τ : Nat} (v : V)
    (hl : x.lbl k = AtomicAction.tickAllAwake τ) :
    (x[k + 1][v].st).st = (x[k][v].st).st ∨
      ∃ (n : M.N) (out : M.N × List (NamedObject V)), n.st = (x[k][v].st).st ∧
        M.tick (Setup.alwaysAwake S) v n (τ : Int) ⇢ out ∧ x[k + 1][v].st = out.1 := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, w', tk, hwake, htick, hc⟩ := hs
  by_cases hv : v ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int)
  · have hwst : ((w' v).state).st = (x[k][v].st).st := by
      have hww := hwake v
      unfold TickAllAwakeWake at hww
      by_cases he : v ∈ entrants Sched τ
      · rw [if_pos he] at hww
        rw [Record.protocolOf_step_wake M S hww]
        exact (facts.nd.wake_st_record _).1
      · rw [if_neg he] at hww
        rw [hww]
    have hx1 : x[k + 1][v].st = (tk v).state := by
      have h2 : x[k + 1][v] = (tickAllAwakeUpdate Sched τ x[k] w' tk)[v] := by rw [hc]
      rw [h2, tickAllAwakeUpdate_getElem_react hv]
    have htk := htick v hv
    by_cases hp : (τ : Int) % S.E.Δ = 0
    · rcases htk with htk | ⟨-, htk⟩
      · rw [Restated.reaction_tick_of_emod facts S v ((w' v).state) hp] at htk
        obtain ⟨out₁, hout, hres⟩ := htk
        exact Or.inr ⟨(w' v).state, out₁, hwst, hout, by rw [hx1, hres]⟩
      · refine Or.inl ?_
        rw [hx1, htk]
        exact hwst
    · refine Or.inl ?_
      rcases htk with htk | ⟨-, htk⟩
      · rw [Restated.reaction_tick_of_not_emod facts S v ((w' v).state) hp] at htk
        rw [hx1, Set.mem_singleton_iff.mp htk]
        exact hwst
      · rw [hx1, htk]
        exact hwst
  · refine Or.inl ?_
    have h2 : x[k + 1][v] = (tickAllAwakeUpdate Sched τ x[k] w' tk)[v] := by rw [hc]
    rw [h2, tickAllAwakeUpdate_getElem_st_of_not_react hv]

/-- Every step makes a `TreeSlotStep` at every validator's core store: if the store before it holds
    no block of a slot after its own, neither does the store after it. -/
theorem treeSlotStep_sts_succ (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (w : V) :
    Restated.TreeSlotStep M (x[i][w].st).st.core (x[i + 1][w].st).st.core := by
  cases hl : x.lbl i with
  | tickAllAwake τ =>
      rcases st_succ_of_tick₃₄ facts S Sched x w hl with hst | ⟨n, out₁, hn, hout, hst⟩
      · intro h
        rw [hst]
        exact h
      · obtain ⟨hten, -⟩ := Restated.tickAllAwake_time facts S Sched x hl
        have hle : (x[i][w].st).st.core.t ≤ (τ : Int) := by
          have h1 := Restated.clock_le_time_sts facts S Sched x i w
          have h2 : (x[i].time : Int) + 1 = (τ : Int) := by exact_mod_cast hten
          linarith
        have hs : n.st.core.s ≤ S.E.slotOf (τ : Int) := by
          rw [hn, Restated.slotOfClock_sts facts S Sched x i w]
          exact slotOf_mono_sts S hle
        have h := facts.ndRun.treeSlotStep_tick (Setup.alwaysAwake S) w n (τ : Int) out₁ hout hs
        rw [hn, ← hst] at h
        exact h
  | deliver p sm =>
      by_cases hp : p = w
      · subst hp
        rcases Restated.st_succ_of_deliver facts S Sched x hl with hproc | ⟨-, hst⟩
        · exact facts.ndRun.treeSlotStep_process (Setup.alwaysAwake S) (x[i][p].st) sm.msg _ hproc
        · rw [hst]; exact Restated.TreeSlotStep.refl' facts _
      · rw [Restated.getElem_succ_of_deliver_ne facts S Sched x hl hp]
        exact Restated.TreeSlotStep.refl' facts _
  | custom p ev => exact ev.elim
  | adversarial p mm =>
      rw [Restated.getElem_succ_of_adversarial facts S Sched x hl]
      exact Restated.TreeSlotStep.refl' facts _
  | forward p mm =>
      rw [Restated.getElem_succ_of_forward facts S Sched x hl]
      exact Restated.TreeSlotStep.refl' facts _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After any number of steps, every block in any validator's tree is of a slot at or before the
    slot of that validator's store. -/
theorem treeSlotBounded_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (m : Nat) (w : V) : Restated.TreeSlotBounded M (x[m][w].st).st.core := by
  induction m with
  | zero =>
      rw [Record.st_zero M S Sched x w, facts.nd.initial_st_inclG2]
      exact facts.hd.treeSlotBounded_init
  | succ i ih => exact Restated.treeSlotStep_sts_succ facts S Sched x i w ih

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every block the slot-`s` fork choice of the store a validator holds after `m` steps can return
    is of a slot at or before that store's slot. -/
theorem headSlot_le_store_slot (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (m : Nat) (q : V) (s : Slot) :
    ∀ H, Restated.gfHeadFrom M S (x[m][q].st) s ⇢ H → H.slot ≤ (x[m][q].st).st.core.s :=
  fun H hH =>
    Restated.treeSlotBounded_sts facts S Sched x m q _ (Restated.gfHeadFrom_mem_tree facts S Sched x m q s H hH)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A store whose clock is at or before slot `s`'s vote time has slot at most `s`. -/
theorem store_slot_le_of_clock_le (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (m : Nat) (q : V) {s : Slot}
    (hclock : (x[m][q].st).st.core.t ≤ M.vote_time S.E s) :
    (x[m][q].st).st.core.s ≤ s := by
  rw [Restated.slotOfClock_sts facts S Sched x m q, ← facts.sch.slotOf_vote_time S.E s]
  exact slotOf_mono_sts S hclock

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- No block the slot-`s` fork choice can return at a store whose clock is at or before slot `s`'s
    vote time is of a slot after `s`. -/
theorem headSlot_le_of_clock_le (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (m : Nat) (q : V) {s : Slot}
    (hclock : (x[m][q].st).st.core.t ≤ M.vote_time S.E s) :
    ∀ H, Restated.gfHeadFrom M S (x[m][q].st) s ⇢ H → H.slot ≤ s :=
  fun H hH => le_trans (Restated.headSlot_le_store_slot facts S Sched x m q s H hH)
    (Restated.store_slot_le_of_clock_le facts S Sched x m q hclock)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `m` is the tick at slot `s`'s vote time, then no block any validator's slot-`s` fork
    choice can return from the store it holds at step `m` is of a slot after `s`. -/
theorem headSlot_le_of_tickStepAt (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {m : Nat} {s : Slot}
    (hm : Restated.tickStepAt M x m (M.vote_time S.E s)) (q : V) :
    ∀ H, Restated.gfHeadFrom M S (x[m][q].st) s ⇢ H → H.slot ≤ s := by
  obtain ⟨-, hmself⟩ := Restated.tickStepAt_time facts x hm
  refine Restated.headSlot_le_of_clock_le facts S Sched x m q ?_
  have h1 := Restated.clock_le_time_sts facts S Sched x m q
  linarith

end

end DecoupledConsensusModel.Sts.Restated
