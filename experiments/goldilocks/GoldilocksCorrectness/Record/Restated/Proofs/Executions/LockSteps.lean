module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Steps
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Locks
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickDefs
public import GoldilocksCorrectness.Proofs.Executions.LockSteps

@[expose] public section

/-!
# LockSteps, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/LockSteps.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: what a step does to a validator's saved
confirmations and lock entries (the fields `tick_voteTime_locks`, `tick_supportCutoff_confirmation`
and `tick_dutyTime_not_awake` of `F.tk2`, `tick_lock_entries`, `tick_keeps_confirmation_off_cutoff`
of `F.tk`), and a step that changes the saved confirmation of slot `j` is the tick at the support
cutoff of slot `j + 1`. The page's routine-level theorems are the facts' fields or have their twins
in phase A.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (supportCutoff_cast)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.ite DREBPost.liftM
  DREBPost.pure DREPost DREPost.bind_any DREPost.dite DREPost.ite DREPost.pure)

open GoldilocksCorrectness.Proofs.Routines (revoke_locks_saved)

open GoldilocksCorrectness.Proofs.Routines (tick_cases)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor LocksRevoked ConfirmationUpdated)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (tick_ac_on_tick voteTime_ne_cutoff
  goldfish_vote_keepsConfirmation receive_keeps_confirmation)

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The routines -/

section Routines

end Routines

/-! ## The tick -/

section Tick

variable [RootOrder]

end Tick

/-! ## The steps -/

section Steps

variable [RootOrder] {S : Setup V} {A : Activity V}

/-- What a step does to a validator's saved confirmations and lock entries, in three cases: it
keeps the saved confirmations and keeps a subset of the lock entries; or it is the validator's tick
to a reading `t`, by a validator active at that step, `t` is the vote time of its slot, the tick starts from a node state awake since that slot's duty window started
(`AwakeFor`), the step leaves the lock entries of the revocation of that slot (`LocksRevoked`, from
the node state the tick starts from) and keeps the saved confirmations; or it is that tick at the
support cutoff of its slot, from a node state awake for that slot, and the step leaves what the
confirmation update of that slot leaves (`ConfirmationUpdated`).

The landed statement names the answers of the routines `revoke_locks` and `update_confirmation`;
the twin reads the tick's effect through the record's predicates. A tick at a duty time
from a node not awake for the slot deletes the expired lock entries and keeps the saved
confirmations (`F.tk2.tick_dutyTime_not_awake`): the first case. No recovery line: the record has
no theorem from the predicates to the routines' answers.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `v`: the validator.

Read aloud: only the validator's own revocation and confirmation update, at their times and when
it has been awake for the slot, write its lock entries beyond deleting some, and only the update
writes its saved confirmations. -/
theorem step_cases_lock_saved (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    (M.savedConfirmation (x.st (i + 1) v) = M.savedConfirmation (x.st i v) ∧
      (x.st (i + 1) v).lockEntries ⊆ (x.st i v).lockEntries) ∨
    (∃ t : ℕ, x.lbl i = Event.tick v t ∧
      v ∈ A.active i ∧
      (t : Int) = S.C.t_ (S.C.slot t) + S.C.Δ ∧
      AwakeFor M S.C (x.tickInput v t) (S.C.slot t) ∧
      LocksRevoked M S.P (x.tickInput v t) t (S.C.slot t) (x.st (i + 1) v) ∧
      M.savedConfirmation (x.st (i + 1) v) = M.savedConfirmation (x.st i v)) ∨
    (∃ t : ℕ, x.lbl i = Event.tick v t ∧
      v ∈ A.active i ∧
      (t : Int) = S.C.t_ (S.C.slot t) + 2 * S.C.Δ ∧
      AwakeFor M S.C (x.tickInput v t) (S.C.slot t) ∧
      ConfirmationUpdated M S.C S.P (x.tickInput v t) t (S.C.slot t) (x.st (i + 1) v)) := by
  rcases (step_cases_per_step M F) x R E i v with h | ⟨t, n', sent, hl, hmem, hok, h, -⟩ | ⟨sm, -, -, h⟩ |
      ⟨⟨tRw, keepw, hlw⟩, -, h⟩
  · rw [h]
    exact Or.inl ⟨rfl, subset_refl _⟩
  · -- the tick starts from `v`'s state at the step `i`
    have hti : x.tickInput v t = x.st i v := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl]
    have hSC : M.savedConfirmation (x.tickInput v t) = M.savedConfirmation (x.st i v) := by
      rw [hti]
    have hLE : (x.tickInput v t).lockEntries = (x.st i v).lockEntries := by rw [hti]
    have hInv : M.nodeInv S.C S.P S.X (x.tickInput v t) := by
      rw [hti]
      exact (lem11_node_invariant M F S A x R E i v (E.not_mem_corrupted_of_tick hl)).1
    rw [h]
    by_cases hv : (t : Int) = S.C.t_ (S.C.slot t) + S.C.Δ
    · have hc : (t : Int) ≠ S.C.t_ (S.C.slot t) + 2 * S.C.Δ :=
        GoldilocksCorrectness.Proofs.Routines.voteTime_ne_cutoff hv
      by_cases hA : AwakeFor M S.C (x.tickInput v t) (S.C.slot t)
      · refine Or.inr (Or.inl ⟨t, hl, hmem, hv, hA,
          F.tk2.tick_voteTime_locks S.C S.P S.X _ _ n' sent hok hInv hv hA, ?_⟩)
        exact (F.tk.tick_keeps_confirmation_off_cutoff S.C S.P S.X _ _ n' sent hok hc).1.trans hSC
      · obtain ⟨h1, h2, -, -⟩ :=
          F.tk2.tick_dutyTime_not_awake S.C S.P S.X _ _ n' sent hok (Or.inl hv) hA
        refine Or.inl ⟨h2.trans hSC, ?_⟩
        rw [h1, ← hLE]
        exact Finset.filter_subset _ _
    · by_cases hc : (t : Int) = S.C.t_ (S.C.slot t) + 2 * S.C.Δ
      · by_cases hA : AwakeFor M S.C (x.tickInput v t) (S.C.slot t)
        · exact Or.inr (Or.inr ⟨t, hl, hmem, hc, hA,
            F.tk2.tick_supportCutoff_confirmation S.C S.P S.X _ _ n' sent hok hInv hc hA⟩)
        · obtain ⟨h1, h2, -, -⟩ :=
            F.tk2.tick_dutyTime_not_awake S.C S.P S.X _ _ n' sent hok (Or.inr hc) hA
          refine Or.inl ⟨h2.trans hSC, ?_⟩
          rw [h1, ← hLE]
          exact Finset.filter_subset _ _
      · refine Or.inl
          ⟨(F.tk.tick_keeps_confirmation_off_cutoff S.C S.P S.X _ _ n' sent hok hc).1.trans hSC, ?_⟩
        rcases F.tk.tick_lock_entries S.C S.P S.X _ _ n' sent hok with h1 | h1 | h1
        · rw [h1, ← hLE]
          exact Finset.filter_subset _ _
        · exact absurd h1 hv
        · exact absurd h1 hc
  · rw [h]
    obtain ⟨h1, -, h2, -⟩ := F.rcv.receive_keeps_confirmation S.C S.P S.X (x.st i v) sm.msg
    exact Or.inl ⟨h1, h2.le⟩
  · rw [h tRw keepw hlw]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hSC, hLE, -⟩ := F.wk.wake_readers (x.st i v) (tRw : Int)
    exact Or.inl ⟨hSC, hLE.le⟩

/-- A step that changes a validator's saved confirmation of slot `j` is the validator's tick at the
support cutoff of slot `j + 1`, by a validator active at that step; that tick starts from a node state awake since the duty window of slot `j + 1` started (`AwakeFor`), and
the step leaves what the confirmation update of slot `j + 1` leaves from that node state
(`ConfirmationUpdated`).

The landed statement names the answer of `update_confirmation`; the twin reads the update through
the record's predicate. No recovery line: the record has no theorem from the predicate
to the routine's answer.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `U`: its slot layout is uniform;
- `x`: the execution; `i`: the step; `v`: the validator; `j`: the slot of the confirmation.

Read aloud: only the validator's update of slot `j + 1`, at its time, writes its saved
confirmation of slot `j`. -/
theorem step_saved_changed (U : UniformSchedule M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) (j : ℕ)
    -- the step changes the saved confirmation of slot `j`
    (hne : (x.st (i + 1) v).savedConfirmation j ≠ (x.st i v).savedConfirmation j) :
    x.lbl i = Event.tick v (M.supportCutoff S.C (j + 1)) ∧
      v ∈ A.active i ∧
      AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (j + 1))) (j + 1) ∧
      ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (j + 1)))
        ((M.supportCutoff S.C (j + 1) : ℕ) : Int) (j + 1) (x.st (i + 1) v) := by
  rcases (step_cases_lock_saved M F) x R E i v with ⟨h, -⟩ | ⟨t, -, -, -, -, -, h⟩ |
      ⟨t, hl, hmem, ht, hA, hcu⟩
  · exact absurd (congrFun h j) hne
  · exact absurd (congrFun h j) hne
  have hSC : M.savedConfirmation (x.tickInput v t) = M.savedConfirmation (x.st i v) := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  -- the update of the slot of `t` changed slot `j`'s field, so that slot is `j + 1`
  have hframe := GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_saved_ne hcu
  have hs0 : S.C.slot (t : Int) ≠ 0 := by
    intro h0
    rw [h0] at hcu
    exact hne (congrFun
      ((GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_zero hcu).1.trans hSC) j)
  have hj : j = S.C.slot (t : Int) - 1 := by
    by_contra hj
    exact hne ((hframe j hj).trans (congrFun hSC j))
  have hslot : S.C.slot (t : Int) = j + 1 := by
    -- `omega` reads facts stated at `Slot`, an `abbrev` of `ℕ`, only once restated at `ℕ`
    have h0 : @Ne ℕ (S.C.slot (t : Int)) 0 := hs0
    have h1 : @Eq ℕ j (S.C.slot (t : Int) - 1) := hj
    show @Eq ℕ (S.C.slot (t : Int)) (j + 1)
    omega
  have htc : t = M.supportCutoff S.C (j + 1) := by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout
      F.sched U) S (j + 1)
    rw [hslot] at ht
    have : (t : Int) = ((M.supportCutoff S.C (j + 1) : ℕ) : Int) := by rw [h1]; exact ht
    exact_mod_cast this
  subst htc
  rw [hslot] at hcu hA
  exact ⟨hl, hmem, hA, hcu⟩

end Steps

end GoldilocksCorrectness.Record.Proofs.Executions

