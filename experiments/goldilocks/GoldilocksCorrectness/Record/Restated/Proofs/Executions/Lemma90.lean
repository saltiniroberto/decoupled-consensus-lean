module
public import GoldilocksCorrectness.Record.Restated.Proofs.View.Bridges
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ConfirmedTipDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.SleepyStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainAfterHealingStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedCachesStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ConfirmationSteps
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.LockSteps
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Monotone
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Clock
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Wake
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Locks
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Node
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ConfirmationACStore
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma40
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Sleepy
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickUpdateState
public import GoldilocksCorrectness.Proofs.View.Bridges
public import GoldilocksCorrectness.Statements.Executions.ConfirmedTipDefs
public import GoldilocksCorrectness.Proofs.Routines.ConfirmedTip
public import GoldilocksCorrectness.Statements.Executions.SleepyStatements
public import GoldilocksCorrectness.Statements.Executions.HonestChainAfterHealingStatements
public import GoldilocksCorrectness.Statements.Executions.HealedCachesStatements
public import GoldilocksCorrectness.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Proofs.Executions.ConfirmationSteps
public import GoldilocksCorrectness.Proofs.Executions.LockSteps
public import GoldilocksCorrectness.Proofs.Executions.Monotone
public import GoldilocksCorrectness.Proofs.Executions.Clock
public import GoldilocksCorrectness.Proofs.Executions.Wake
public import GoldilocksCorrectness.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.Locks
public import GoldilocksCorrectness.Proofs.Routines.ACInterfaceTick
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.NodeTick
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption

@[expose] public section

/-!
# Lemma90, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma90.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: the record of the confirmed tip at a step, after
the healed slot's update and on the honest chain, and Lemma 90 (a), agreement and growth of the
confirmed tips after the healed slot. The page's routine-level theorems are the facts' fields or
have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ
  slotStart_eq slot_eq_of_mem supportCutoff_cast supportCutoff_eq supportCutoff_lt_of_lt
  supportCutoff_slot_eq voteTime_cast voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.ite DREBPost.liftM
  DREBPost.pure DREPost DREPost.bind_any DREPost.dite DREPost.ite DREPost.pure)

open GoldilocksCorrectness.Proofs.Routines (revoke_locks_latest)

open GoldilocksCorrectness.Proofs.Routines (confirmedOf_ancestorEq_of
  slot_lt_of_ancestorEq_of_treeClosed tick_latest_cases)
open GoldilocksCorrectness.Statements.Routines (confirmedOf)

open GoldilocksCorrectness.Proofs.Routines (acState_initial_eq initial_eq)

open GoldilocksCorrectness.Proofs.Routines (fgState_initial_eq)

open GoldilocksCorrectness.Proofs.Routines (duty_window_start_le_dutyWindowStart)

namespace GoldilocksCorrectness.Record.Proofs.Executions



open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (tick_ac_on_tick voteTime_ne_cutoff
  goldfish_vote_keepsConfirmation receive_keeps_confirmation ac_confirmed_cases)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## What a tick and a step do to the record -/

section Steps

variable {S : Setup V} {A : Activity V}

/-- What a step does to a validator's record of the confirmed tip: it keeps it; or it is the
validator's tick to a value `t`, the validator active at the tick's step,
`t` is the support cutoff of its slot, the tick starts from a node state awake since that slot's duty window
started (`AwakeFor`), and the step leaves what the confirmation update of that slot leaves from that
node state (`ConfirmationUpdated`).

The landed statement names the answer of the routine `update_confirmation`; the twin reads the
tick's effect through the record's predicate, as `step_cases_lock_saved` of
`Record/Restated/Proofs/Executions/LockSteps.lean` does. A tick away from the support cutoff, or
from a node not awake for the slot, keeps the record (`F.tk.tick_confirmation_awake`): the first
case. No recovery line: the record has no theorem from the predicate to the routine's answer.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `v`: the validator.

Read aloud: only the validator's own confirmation update, at its time, writes its record of the
confirmed tip. -/
theorem step_cases_latest (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    (x.st (i + 1) v).latestConfirmed = (x.st i v).latestConfirmed ∨
    (∃ t : ℕ, x.lbl i = Event.tick v t ∧
      v ∈ A.active i ∧
      (t : Int) = S.C.t_ (S.C.slot t) + 2 * S.C.Δ ∧
      AwakeFor M S.C (x.tickInput v t) (S.C.slot t) ∧
      ConfirmationUpdated M S.C S.P (x.tickInput v t) t (S.C.slot t)
        (x.st (i + 1) v)) := by
  rcases (step_cases M F) x R E i v with h | ⟨t, n', sent, hl, hmem, hok, h, -⟩ | ⟨sm, -, -, h⟩ |
      ⟨⟨tRw, keepw, hlw⟩, -, h⟩
  · rw [h]
    exact Or.inl rfl
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hLC, -⟩ :
        (x.tickInput v t).v = (x.st i v).v ∧
          (x.tickInput v t).t = (x.st i v).t ∧
          (x.tickInput v t).tree = (x.st i v).tree ∧
          (x.tickInput v t).finalized = (x.st i v).finalized ∧
          (x.tickInput v t).justified = (x.st i v).justified ∧
          (x.tickInput v t).justifiedHeight = (x.st i v).justifiedHeight ∧
          (x.tickInput v t).attestationsHeld = (x.st i v).attestationsHeld ∧
          M.votesHeld (x.tickInput v t) = M.votesHeld (x.st i v) ∧
          M.voteStamp (x.tickInput v t) = M.voteStamp (x.st i v) ∧
          M.blockStamp (x.tickInput v t) = M.blockStamp (x.st i v) ∧
          M.savedConfirmation (x.tickInput v t) = M.savedConfirmation (x.st i v) ∧
          (x.tickInput v t).lockEntries = (x.st i v).lockEntries ∧
          (x.tickInput v t).fastBlocks = (x.st i v).fastBlocks ∧
          (x.tickInput v t).latestConfirmed = (x.st i v).latestConfirmed ∧
          M.sentTarget (x.tickInput v t) = M.sentTarget (x.st i v) ∧
          M.sentTimeout (x.tickInput v t) = M.sentTimeout (x.st i v) ∧
          M.sentLock (x.tickInput v t) = M.sentLock (x.st i v) ∧
          (x.tickInput v t).sentAttestations = (x.st i v).sentAttestations := by
      rw [show x.tickInput v t = x.st i v by
        unfold Trace.tickInput
        rw [(tickStep_eq_of_lbl M) x E (i := i) (v := v) (by assumption)]]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hInv : M.nodeInv S.C S.P S.X (x.tickInput v t) := by
      rw [show x.tickInput v t = x.st i v by
        unfold Trace.tickInput
        rw [(tickStep_eq_of_lbl M) x E (i := i) (v := v) (by assumption)]]
      exact (lem11_node_invariant M F S A x R E i v (E.not_mem_corrupted_of_tick (by assumption))).1
    rw [h]
    -- the tick keeps the record, unless it is at the support cutoff of its slot from a node state
    -- awake for that slot (the field `tick_confirmation_awake` of `F.tk`); then it runs the
    -- confirmation update (the field `tick_supportCutoff_confirmation` of `F.tk2`)
    rcases F.tk.tick_confirmation_awake S.C S.P S.X _ _ n' sent hok with ⟨-, h1⟩ | ⟨hc, hA⟩
    · exact Or.inl (h1.trans hLC)
    · exact Or.inr ⟨t, hl, hmem, hc, hA,
        F.tk2.tick_supportCutoff_confirmation S.C S.P S.X _ _ n' sent hok hInv hc hA⟩
  · rw [h]
    exact Or.inl (F.rcv.receive_keeps_confirmation S.C S.P S.X (x.st i v) sm.msg).2.2.2.1
  · -- a wake keeps the record of the confirmed tip
    rw [h tRw keepw hlw]
    exact Or.inl (F.wk.wake_readers _ _).2.2.2.2.2.2.2.2.2.2.2.2.2.1

end Steps

/-! ## The record over an execution -/

section Record

variable {S : Setup V} {A : Activity V}

/-- **Kit fact, the record of the confirmed tip is held.** At every step of every execution, a
validator's record of the confirmed tip is a block of its FG state's tree.

Why: the record is the genesis block initially; a step that changes it is the validator's
confirmation update, which writes the confirmation it saves
(`update_confirmation_latest_confirmed`), held by the kit fact
`saved_confirmation_mem_T_of_exec`; and the tree only grows.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `i`: the step; `v`: the validator.

Read aloud: a validator holds the block it records as confirmed. -/
theorem latest_confirmed_mem_T_of_exec (U : UniformSchedule M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    (x.st i v).latestConfirmed ∈ (x.st i v).tree := by
  induction i with
  | zero =>
      rw [(getElem_zero_st M F) x R v, F.init.initial_latestConfirmed, F.init.initial_tree]
      exact Finset.mem_singleton_self _
  | succ i ih =>
      have hTs := (mem_T_mono M F) x R E v (Nat.le_succ i)
      rcases (step_cases_latest M F) x R E i v with h | ⟨t, hl, -, -, -, hcu⟩
      · rw [h]
        exact hTs ih
      · -- the update keeps the record of the state the tick starts from, or writes the confirmation
        -- it saves
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hLC, -⟩ :
            (x.tickInput v t).v = (x.st i v).v ∧
              (x.tickInput v t).t = (x.st i v).t ∧
              (x.tickInput v t).tree = (x.st i v).tree ∧
              (x.tickInput v t).finalized = (x.st i v).finalized ∧
              (x.tickInput v t).justified = (x.st i v).justified ∧
              (x.tickInput v t).justifiedHeight = (x.st i v).justifiedHeight ∧
              (x.tickInput v t).attestationsHeld = (x.st i v).attestationsHeld ∧
              M.votesHeld (x.tickInput v t) = M.votesHeld (x.st i v) ∧
              M.voteStamp (x.tickInput v t) = M.voteStamp (x.st i v) ∧
              M.blockStamp (x.tickInput v t) = M.blockStamp (x.st i v) ∧
              M.savedConfirmation (x.tickInput v t) = M.savedConfirmation (x.st i v) ∧
              (x.tickInput v t).lockEntries = (x.st i v).lockEntries ∧
              (x.tickInput v t).fastBlocks = (x.st i v).fastBlocks ∧
              (x.tickInput v t).latestConfirmed = (x.st i v).latestConfirmed ∧
              M.sentTarget (x.tickInput v t) = M.sentTarget (x.st i v) ∧
              M.sentTimeout (x.tickInput v t) = M.sentTimeout (x.st i v) ∧
              M.sentLock (x.tickInput v t) = M.sentLock (x.st i v) ∧
              (x.tickInput v t).sentAttestations = (x.st i v).sentAttestations := by
          rw [show x.tickInput v t = x.st i v by
            unfold Trace.tickInput
            rw [(tickStep_eq_of_lbl M) x E (i := i) (v := v) (by assumption)]]
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        by_cases hs0 : S.C.slot (t : Int) = 0
        · rw [hs0] at hcu
          rw [(GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_zero hcu).2.2.1, hLC]
          exact hTs ih
        · rcases (GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_latest_confirmed F) hs0 hcu with h | ⟨h, -⟩
          · rw [h, hLC]
            exact hTs ih
          · exact (saved_confirmation_mem_T_of_exec M F U) S A x R E (i + 1) v _ _ h

/-- **Kit fact, the slot of the record before an update.** In an execution where every time is
reached and corruption is permanent: at every step `i` before which every tick of `v` is to a clock
value less than the support cutoff of slot `s + 1`, `v`'s record of the confirmed tip has a slot at
most `s`.

Why: the record is the genesis block, of slot `0`, initially; a step that changes it is `v`'s
confirmation update at its tick to the support cutoff `t` of the slot `r` of `t`, with `t` less than
the support cutoff of slot `s + 1`, so `r ≤ s`; it writes the confirmation it saves, a block of the
tree the tick reads, whose slot is at most the slot of `v`'s clock value then
(`slot_le_clockValue_of_mem_tree`, `v` honest at its tick), at most `t` (`clockValue_le_of_set`).

Stated at steps, with the ticks before the step bounded, in place of a bound on the step's time
: under the two clock bounds a tick to the support cutoff of slot `s + 1` can come at a
time before it.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `v`: the validator; `s`: the slot; `i`: the step.

Read aloud: before `v`'s update of slot `s + 1`, `v`'s record is of slot `s` or earlier. -/
theorem latest_confirmed_slot_le (U : UniformSchedule M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (v : V) (s : ℕ) :
    ∀ i : ℕ, (∀ k < i, ∀ t : ℕ, x.lbl k = Event.tick v t → t < M.supportCutoff S.C (s + 1)) →
      (x.st i v).latestConfirmed.slot ≤ s := by
  intro i
  induction i with
  | zero =>
      intro _
      rw [(getElem_zero_st M F) x R v, F.init.initial_latestConfirmed]
      exact Nat.zero_le _
  | succ i ih =>
      intro hi
      have hi' : ∀ k < i, ∀ t : ℕ, x.lbl k = Event.tick v t → t < M.supportCutoff S.C (s + 1) :=
        fun k hk => hi k (Nat.lt_succ_of_lt hk)
      rcases (step_cases_latest M F) x R E i v with h | ⟨t, hl, -, ht, -, hcu⟩
      · rw [h]
        exact ih hi'
      · have hTI : x.tickInput v t = x.st i v := by
          unfold Trace.tickInput
          rw [(tickStep_eq_of_lbl M) x E hl]
        rw [hTI] at hcu
        have hsl : S.C.slot (t : Int) = M.slot S.C t := by
          rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
            ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
        have hv : v ∉ A.corrupted i := E.not_mem_corrupted_of_tick hl
        -- the slot of the tick's value is at most `s`: its support cutoff is `t`, less than that of
        -- slot `s + 1`
        have hle : M.slot S.C t ≤ s := by
          have ht' := ht
          rw [hsl] at ht'
          have hcut := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot_eq M.toSlotLayout F.sched U) S ht'
          have hlt := hi i (Nat.lt_succ_self i) t hl
          by_contra hgt
          have h1 : M.supportCutoff S.C (s + 1) ≤ M.supportCutoff S.C (M.slot S.C t) := by
            rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt (Nat.lt_of_not_le hgt)) with h2 | h2
            · exact le_of_lt ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt_of_lt M.toSlotLayout F.sched) S h2)
            · rw [← h2]
          omega
        by_cases hs0 : S.C.slot (t : Int) = 0
        · rw [hs0] at hcu
          rw [(GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_zero hcu).2.2.1]
          exact ih hi'
        · rcases (GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_latest_confirmed F) hs0 hcu with h | ⟨h, -⟩
          · rw [h]
            exact ih hi'
          · -- the saved confirmation is a block of the tree the tick reads
            have hmem := GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_saved_mem
              (Nat.one_le_iff_ne_zero.mpr hs0) hcu _ h
            have hT : (x.st (i + 1) v).latestConfirmed ∈ (x.st i v).tree := by
              rcases hmem with h' | h'
              · rw [h', (GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]
                exact F.nd.nodeInv_finalized_mem_tree (lem11_node_invariant M F S A x R E i v hv).1
              · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 h').1
            have hsl' := (slot_le_clockValue_of_mem_tree M F) R E hv hT
            have hcv : x.clockValue i v ≤ t := E.clockValue_le_of_set hv (Or.inl hl)
            have hmono := GoldilocksCorrectness.Proofs.Routines.slot_mono_int S
              (show ((x.clockValue i v : ℕ) : Int) ≤ ((t : ℕ) : Int) by exact_mod_cast hcv)
            rw [hsl] at hmono
            exact le_trans hsl' (le_trans hmono hle)

end Record

/-! ## The record right after the update of the healed slot -/

section Base

open Classical in
/-- **`live_locks_compatible_of_revocation` with the revocation's clause asked of `activeAt`.** For an updater
`v` of slot `s₀`: every lock entry of `v`'s tick input to the support cutoff `c` of slot `s₀ + 1`, live at `c`, is
on a block compatible with `B₀`, when, if `v` is in `activeAt M S A x s₀`, every entry its revocation of slot
`s₀ + 1` leaves live is. No honesty at the real time of `c` is read: the entry's provenance puts `v` in
`activeAt M S A x s₀`, and the clause is asked there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `s₀`: the slot; `B₀`: the block; `v`: the updater.

Read aloud: an updater's live locks at its tick to the support cutoff are compatible with `B₀` when the live
locks its revocation of the next slot leaves are, if it was active through the slot's duties. -/
theorem live_locks_compatible_of_revocation_of_active (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ : ℕ) (B₀ : Block V) (v : V)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the two clock bounds together are less than one delay
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- corruption is permanent
    -- `v` is an updater of slot `s₀`
    (hv : v ∈ updaterAt M S A x s₀)
    -- when `v` is in `activeAt M S A x s₀`, the live entries its revocation of slot `s₀ + 1` leaves at its
    -- tick to the vote time of slot `s₀ + 1` are compatible with `B₀`
    (hRev : v ∈ activeAt M S A x s₀ → ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (s₀ + 1)))
        ((M.voteTime S.C (s₀ + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.voteTime S.C (s₀ + 1))) (s₀ + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput v (M.voteTime S.C (s₀ + 1)))
          ((M.voteTime S.C (s₀ + 1) : ℕ) : Int) e = true → e.B.compatible B₀ = true) :
    ∀ e ∈ (x.tickInput v (M.supportCutoff S.C (s₀ + 1))).lockEntries,
      M.is_live (x.tickInput v (M.supportCutoff S.C (s₀ + 1)))
        ((M.supportCutoff S.C (s₀ + 1) : ℕ) : Int) e = true → e.B.compatible B₀ = true := by
  intro e he hlive
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hv' : ∀ s : ℕ, M.voteTime S.C s = M.slotStart S.C s + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
  have hc' : ∀ s : ℕ, M.supportCutoff S.C s = M.voteTime S.C s + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
  have hss : ∀ s : ℕ, M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := fun s => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add,
      Nat.mul_one]
  -- `v`'s tick `k'` to the support cutoff `c₀` of slot `s₀ + 1`, and its activity up to it
  have hvw : v ∈ A.activeThroughoutToTick x (Goldilocks.duty_window_start S.C (s₀ + 1))
      (M.supportCutoff S.C (s₀ + 1)) := hv
  obtain ⟨k', hk', hact⟩ := Activity.mem_activeThroughoutToTick.1 hvw
  have hts : x.tickStep v (M.supportCutoff S.C (s₀ + 1)) = k' := (tickStep_eq_of_lbl M) x E hk'
  have he' : e ∈ (x.st k' v).lockEntries := by
    rw [← hts]
    exact he
  have hlive' := hlive
  simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hlive'
  -- where `e` comes from (Lemma 39 at `k'`): `v`'s update of a slot `σ + 1` at its tick to the
  -- support cutoff `c₁`, at an earlier step, from a state awake since `τ`
  obtain ⟨σ, hd, hk₁, hl₁, ⟨τ, hτ, hτle⟩, h39⟩ :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem39_lock_entry_provenance M F U) S A x R k' v e
      E he'
  obtain ⟨n₁, sent₁, hrun₁, hAw₁, -⟩ := (update_state_of_tick M F U) S A x R σ v E hl₁ ⟨τ, hτ, hτle⟩
  obtain ⟨e₀, -, -, -, -, -, -, -, htr⟩ := h39 n₁ sent₁ hrun₁ hAw₁
  -- `c₁ < c₀` (`clock_mono`, `tick_unique`), so `σ + 1 ≤ s₀`
  have hle₁ := E.clock_mono _ _ v _ _ hk₁ (E.not_mem_corrupted_of_tick hk') (Or.inl hl₁) (Or.inl hk')
  have hne₁ : M.supportCutoff S.C (σ + 1) ≠ M.supportCutoff S.C (s₀ + 1) := fun h => by
    have hl' : x.lbl (x.tickStep v (M.supportCutoff S.C (σ + 1))) =
        Event.tick v (M.supportCutoff S.C (s₀ + 1)) := by
      rw [hl₁, h]
    have := E.tick_unique _ _ v _ hl' hk'
    omega
  have hσ : σ + 1 ≤ s₀ := by
    by_contra h
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show s₀ + 1 ≤ σ + 1 by omega)
    have h1 := hc' (σ + 1)
    have h2 := hv' (σ + 1)
    have h3 := hc' (s₀ + 1)
    have h4 := hv' (s₀ + 1)
    omega
  -- live at `c₀`, the lock is of a slot `σ` with `s₀ + 1 ≤ σ + k` (Lemma 41)
  have hσk : s₀ + 1 ≤ σ + S.C.k := by
    by_cases hkle : S.C.k ≤ s₀ + 1
    · have h41 := (GoldilocksCorrectness.Record.Statements.Executions.lem41_slot_of_live_entry M F U) S
        (s₀ + 1 - S.C.k) σ (M.supportCutoff S.C (s₀ + 1)) e hd hlive'.1 (by
          rw [show s₀ + 1 - S.C.k + S.C.k = s₀ + 1 by omega]
          have := hc' (s₀ + 1)
          omega)
      omega
    · omega
  -- the reader's start tick comes at or before the tick to `c₁`: `v` is active from the tick to `c₁`
  -- up to its tick to `c₀`
  have hdw : Goldilocks.duty_window_start S.C (s₀ + 1) ≤ ((M.supportCutoff S.C (σ + 1) : ℕ) : ℤ) := by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart
      M.toSlotLayout F.sched U) S (s₀ + 1)
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_le_supportCutoff M.toSlotLayout
      F.sched U) S (show s₀ + 1 ≤ σ + 1 + S.C.k by omega)
    have h2' : ((M.dutyWindowStart S.C (s₀ + 1) : ℕ) : ℤ) ≤ ((M.supportCutoff S.C (σ + 1) : ℕ) : ℤ) := by
      exact_mod_cast h2
    exact h1.trans h2'
  have hact₁ : ∀ i : ℕ, x.tickStep v (M.supportCutoff S.C (σ + 1)) ≤ i → i ≤ k' → v ∈ A.active i := by
    rcases hact with hall | ⟨k, -, c, hca, hlk, hkw⟩
    · exact fun i _ h => hall i h
    · have hkk₁ : k ≤ x.tickStep v (M.supportCutoff S.C (σ + 1)) := by
        by_contra hlt'
        have hlt'' := Nat.lt_of_not_le hlt'
        have hcc := E.clock_mono _ _ v _ _ hlt'' (E.not_mem_corrupted_of_tick hlk) (Or.inl hl₁) (Or.inl hlk)
        have hca' : (c : ℤ) ≤ ((M.supportCutoff S.C (σ + 1) : ℕ) : ℤ) := hca.trans hdw
        have hceq : c = M.supportCutoff S.C (σ + 1) := by omega
        rw [hceq] at hlk
        have := E.tick_unique _ _ v _ hl₁ hlk
        omega
      exact fun i h1 h2 => hkw i (hkk₁.trans h1) h2
  -- so `v` is in `activeAt M S A x s₀`: awake from the tick that wrote `τ`, at most the duty window's
  -- start of slot `σ + 1`, or from the start, up to its tick to `c₀`
  have hAct₀ : v ∈ A.awakeThroughoutToTick x (Goldilocks.duty_window_start S.C s₀)
      (M.supportCutoff S.C (s₀ + 1)) := by
    have hτ' : (x.tickInput v (M.supportCutoff S.C (σ + 1))).awakeSince = some τ := hτ
    refine Activity.mem_awakeThroughoutToTick.2 ⟨k', hk', ?_⟩
    rcases (awake_of_tickInput_awakeSince_of_tick M F) x R E ⟨_, hl₁⟩ hτ' with
        ⟨-, hall⟩ | ⟨k₀, τ', hk₀, hl₀, hτ'eq, haw₀⟩
    · left
      intro i hi
      rcases le_or_gt i (x.tickStep v (M.supportCutoff S.C (σ + 1))) with h | h
      · exact hall i h
      · exact Activity.mem_awake_of_mem_active (hact₁ i h.le hi)
    · right
      refine ⟨k₀, by omega, τ', ?_, hl₀, fun i h1 h2 => ?_⟩
      · rw [hτ'eq]
        exact hτle.trans (GoldilocksCorrectness.Proofs.Routines.duty_window_start_mono S (by omega))
      · rcases le_or_gt i (x.tickStep v (M.supportCutoff S.C (σ + 1))) with h | h
        · exact haw₀ i h1 h
        · exact Activity.mem_awake_of_mem_active (hact₁ i h.le h2)
  have hHon : v ∈ activeAt M S A x s₀ := hAct₀
  -- `v`'s tick to the vote time of slot `s₀ + 1`, inside its window (`hSkew`), from a state awake for
  -- slot `s₀ + 1`
  have hdR := duty_window_start_real S (s₀ + 1)
  have hvR : ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * ((s₀ + 1 : ℕ) : ℝ) + (Δ S : ℝ) := by
    rw [hv' (s₀ + 1), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
    push_cast
    ring
  have hcR : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) = ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) + (Δ S : ℝ) := by
    rw [hc' (s₀ + 1)]
    push_cast
    ring
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hkR : (2 : ℝ) ≤ (S.C.k : ℝ) := by exact_mod_cast hk
  have hΔk : (Δ S : ℝ) ≤ 4 * (Δ S : ℝ) * (S.C.k : ℝ) := by nlinarith
  have hw₃ := (mem_activeThroughoutToTick_of_inside M F) R E (c := M.voteTime S.C (s₀ + 1)) hvw
    (by have := hv' (s₀ + 1); omega) (by rw [hdR, hvR]; linarith) (by rw [hcR]; linarith)
  obtain ⟨τ₃, hτ₃, hτ₃le⟩ := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hw₃ (by
    have h : ((Goldilocks.duty_window_start S.C (s₀ + 1) : ℤ) : ℝ) <
        (((M.voteTime S.C (s₀ + 1) : ℕ) : ℤ) : ℝ) := by
      push_cast
      rw [hdR, hvR]
      linarith
    exact_mod_cast h)
  obtain ⟨k₃, hl₃, -⟩ := Activity.mem_activeThroughoutToTick.1 hw₃
  have hts₃ : x.tickStep v (M.voteTime S.C (s₀ + 1)) = k₃ := (tickStep_eq_of_lbl M) x E hl₃
  obtain ⟨n₃, sent₃, hok₃, hst₃, -⟩ := R.tick k₃ v _ hl₃
  have hrun₃ : .ok (n₃, sent₃) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (s₀ + 1)))
      ((M.voteTime S.C (s₀ + 1) : ℕ) : Int) := by
    unfold Trace.tickInput
    rw [hts₃]
    exact hok₃
  have hAwake : AwakeFor M S.C (x.tickInput v (M.voteTime S.C (s₀ + 1))) (s₀ + 1) := ⟨τ₃, hτ₃, hτ₃le⟩
  -- the order of the three ticks: to `c₁`, to the vote time, to `c₀`
  have hc₁vt : M.supportCutoff S.C (σ + 1) < M.voteTime S.C (s₀ + 1) := by
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show σ + 1 ≤ s₀ by omega)
    have h1 := hc' (σ + 1)
    have h2 := hv' (σ + 1)
    have h3 := hv' (s₀ + 1)
    have h4 := hss s₀
    omega
  have hvtc₀ : M.voteTime S.C (s₀ + 1) < M.supportCutoff S.C (s₀ + 1) := by
    have := hc' (s₀ + 1)
    omega
  have h13 : x.tickStep v (M.supportCutoff S.C (σ + 1)) < k₃ := by
    rcases lt_trichotomy (x.tickStep v (M.supportCutoff S.C (σ + 1))) k₃ with h | h | h
    · exact h
    · rw [h, hl₃] at hl₁
      have := (Event.tick.inj hl₁).2
      omega
    · have := E.clock_mono _ _ v _ _ h (E.not_mem_corrupted_of_tick hl₁) (Or.inl hl₃) (Or.inl hl₁)
      omega
  have h3' : k₃ < k' := by
    rcases lt_trichotomy k₃ k' with h | h | h
    · exact h
    · rw [h, hk'] at hl₃
      have := (Event.tick.inj hl₃).2
      omega
    · have := E.clock_mono _ _ v _ _ h (E.not_mem_corrupted_of_tick hl₃) (Or.inl hk') (Or.inl hl₃)
      omega
  -- that tick ran the revocation of slot `s₀ + 1`; the entry traced from `e`'s update right after it
  -- is an entry of its outcome, live at the vote time, so compatible with `B₀` (`hRev`)
  have hRevoke := (locksRevoked_of_voteTime_outcome M F U) S A x R E (s₀ + 1) v n₃ sent₃ hrun₃ hAwake
  obtain ⟨e', he'', hd', heB', -⟩ := htr (k₃ + 1) (by omega) (by omega)
  have he'A : e' ∈ M.lockEntries n₃ := by
    rw [← hst₃]
    exact he''
  have hlive₃ : M.is_live (x.tickInput v (M.voteTime S.C (s₀ + 1)))
      ((M.voteTime S.C (s₀ + 1) : ℕ) : Int) e' = true := by
    simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)]
    refine ⟨?_, GoldilocksCorrectness.Record.Proofs.Routines.revoke_locks_entry_mem_tree
      (Nat.le_add_left 1 s₀) hRevoke e' he'A⟩
    rw [hd']
    exact lt_trans (Int.ofNat_lt.2 hvtc₀) hlive'.1
  exact GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible heB'
    (hRev hHon n₃ sent₃ hrun₃ hAwake e' he'A hlive₃)


open Classical in
/-- **The live locks an updater holds at its tick to the support cutoff are compatible with `B₀` when
those its revocation leaves are.** For an updater `v` of slot `s₀`, honest after every step whose time is at
most the support cutoff `c` of slot `s₀ + 1` and at every step at which an honest validator ticks to `c`:
every lock entry of `v`'s tick input to `c`, live at `c`, is on a block compatible with `B₀`, when, if `v` is
an honest active validator of slot `s₀`, every entry its revocation of slot `s₀ + 1` (at its tick to the vote
time of slot `s₀ + 1`) leaves live is.

Why: the entry was written by `v`'s update of a slot `σ + 1 ≤ s₀` at its tick to that slot's support cutoff
(Lemma 39), so `v` is an honest active validator of slot `s₀`; its tick to the vote time of slot `s₀ + 1`
comes between that tick and its tick to `c`, from a state awake for slot `s₀ + 1`, and ran the revocation; the
entry traced from that update right after it is an entry of the revocation's outcome, live at the vote time.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `s₀`: the slot; `B₀`: the block; `v`: the updater.

Read aloud: an updater's live locks at its tick to the support cutoff are compatible with `B₀` when the live
locks its revocation of the next slot leaves are. -/
theorem live_locks_compatible_of_revocation (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ : ℕ) (B₀ : Block V) (v : V)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the two clock bounds together are less than one delay
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- corruption is permanent
    -- `v` is an updater of slot `s₀`
    (hv : v ∈ updaterAt M S A x s₀)
    -- `v` is outside the adversary set after every step whose time is at most the support cutoff
    -- of slot `s₀ + 1`, and at every step at which a validator outside it ticks to that cutoff
    (hvc : v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) ∪
      Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
        x.lbl k = Event.tick w (M.supportCutoff S.C (s₀ + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- when `v` is an honest active validator of slot `s₀`, the live entries its revocation of slot
    -- `s₀ + 1` leaves at its tick to the vote time of slot `s₀ + 1` are compatible with `B₀`
    (hRev : v ∈ honestActiveAt M S A x s₀ → ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (s₀ + 1)))
        ((M.voteTime S.C (s₀ + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.voteTime S.C (s₀ + 1))) (s₀ + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput v (M.voteTime S.C (s₀ + 1)))
          ((M.voteTime S.C (s₀ + 1) : ℕ) : Int) e = true → e.B.compatible B₀ = true) :
    ∀ e ∈ (x.tickInput v (M.supportCutoff S.C (s₀ + 1))).lockEntries,
      M.is_live (x.tickInput v (M.supportCutoff S.C (s₀ + 1)))
        ((M.supportCutoff S.C (s₀ + 1) : ℕ) : Int) e = true → e.B.compatible B₀ = true := by
  exact (live_locks_compatible_of_revocation_of_active M F U) S A x R s₀ B₀ v E hSkew hv
    (fun h => hRev (Finset.mem_sdiff.2 ⟨h, hvc⟩))

open Classical in
/-- **No live lock vetoes `B₀` at the update of the healed slot.** In an execution where every
time is reached and corruption is permanent: when `HonestChainExtends`
holds for `B₀` at slot `s₀` at the honest active validators of slot `s₀`, every lock entry of an
updater `v` of slot `s₀`, held before the support cutoff `c` of slot `s₀ + 1` and live at `c`, is
on a block compatible with `B₀`.

Why: `v`'s tick at the vote time of slot `s₀ + 1` ran the revocation of that slot (Lemma 13: `v`
is awake since the duty window's start of slot `s₀ + 1`), and from that tick to `c` the lock
entries only shrink (`lockEntries_tickInput_subset_tickOutput`). When `v` is an honest active validator of
slot `s₀`, the second clause of `HonestChainExtends` makes every entry the revocation left, live at
the vote time, compatible with `B₀`. Otherwise `v` was asleep at some time from the duty window's
start of slot `s₀` to before that of slot `s₀ + 1`, so it held no entry live at the vote time
(`lock_free_after_wake`) and the revocation left none.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `B₀`: the block; `v`: the updater.

Read aloud: at the update of the healed slot, no live lock of an updater conflicts with `B₀`. -/
theorem live_locks_compatible_at_healed_update (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ : ℕ) (B₀ : Block V) (v : V)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the two clock bounds together are less than one delay
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- corruption is permanent
    -- the slot invariant restricted to `B₀` at slot `s₀`
    (hBase : HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀)
    -- `v` is an updater of slot `s₀`
    (hv : v ∈ updaterAt M S A x s₀)
    -- `v` is outside the adversary set after every step whose time is at most the support cutoff
    -- of slot `s₀ + 1`, and at every step at which a validator outside it ticks to that cutoff
    (hvc : v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) ∪
      Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
        x.lbl k = Event.tick w (M.supportCutoff S.C (s₀ + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k)) :
    ∀ e ∈ (x.tickInput v (M.supportCutoff S.C (s₀ + 1))).lockEntries,
      M.is_live (x.tickInput v (M.supportCutoff S.C (s₀ + 1)))
        ((M.supportCutoff S.C (s₀ + 1) : ℕ) : Int) e = true → e.B.compatible B₀ = true := by
  exact live_locks_compatible_of_revocation M F U S A x R s₀ B₀ v E hSkew hv hvc (fun hH => hBase.2.1 v hH)

open Classical in
/-- **The record right after an update that saves `B₀` with no conflicting live lock.** As
`latest_confirmed_after_healed_update`, with its two uses of the slot invariant and of `v`'s honesty at the real
time of the cutoff taken as inputs: `v`'s update of slot `s₀ + 1` saved `B₀`, and every lock entry of its input
live at the cutoff is on a block compatible with `B₀`. Then `v` holds `B₀` as its record of the confirmed tip
right after that update.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `s₀`: the slot; `B₀`: the saved block; `v`: the updater.

Read aloud: an updater whose update saves `B₀`, with no live lock conflicting with `B₀`, records `B₀` as its
confirmed tip right after the update. -/
theorem latest_confirmed_after_update_of_compatible (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ : ℕ) (B₀ : Block V) (v : V)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the two clock bounds together are less than one delay
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- corruption is permanent
    -- `B₀`'s slot is at least `s₀`
    (hB₀slot : s₀ ≤ B₀.slot)
    -- `v` is an updater of slot `s₀`
    (hv : v ∈ updaterAt M S A x s₀)
    -- `v`'s update saved `B₀`
    (hSaved : (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀)
    -- every lock entry of `v`'s tick input to the support cutoff of slot `s₀ + 1`, live there, is on a block
    -- compatible with `B₀`
    (hComp : ∀ e ∈ (x.tickInput v (M.supportCutoff S.C (s₀ + 1))).lockEntries,
      M.is_live (x.tickInput v (M.supportCutoff S.C (s₀ + 1)))
        ((M.supportCutoff S.C (s₀ + 1) : ℕ) : Int) e = true → e.B.compatible B₀ = true) :
    (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).latestConfirmed = B₀ := by
  have hΔ := one_le_Δ S
  -- `v`'s tick `K` to the support cutoff `c₀` of slot `s₀ + 1`, honest there
  have hvw : v ∈ A.activeThroughoutToTick x (Goldilocks.duty_window_start S.C (s₀ + 1))
      (M.supportCutoff S.C (s₀ + 1)) := hv
  obtain ⟨K, hlK, -⟩ := Activity.mem_activeThroughoutToTick.1 hvw
  have huK : v ∉ A.corrupted K := E.not_mem_corrupted_of_tick hlK
  have hTI : x.tickInput v (M.supportCutoff S.C (s₀ + 1)) = x.st K v := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hlK]
  -- the update of slot `s₀ + 1` ran at that tick and saved `B₀`
  obtain ⟨τ, hτ, hτle⟩ := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hvw
    (by
      have hdwz : (Goldilocks.duty_window_start S.C (s₀ + 1) : ℤ) ≤
          ((M.dutyWindowStart S.C (s₀ + 1) : ℕ) : ℤ) := by
        rw [(GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_eq_toNat M.toSlotLayout F.sched U)]
        exact Int.self_le_toNat _
      have h := (dutyWindowStart_succ_lt_supportCutoff M F U) S s₀
      have h' : ((M.dutyWindowStart S.C (s₀ + 1) : ℕ) : ℤ) < ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℤ) := by
        exact_mod_cast h
      exact lt_of_le_of_lt hdwz h')
  obtain ⟨n'', sent, hrun, hAwF, hSv, -, -, hLc⟩ :=
    (update_state_of_tick M F U) S A x R s₀ v E hlK ⟨τ, hτ, hτle⟩
  have hUpd := (confirmationUpdated_of_cutoff_tickInput M F U) x R s₀ v n'' sent hrun hAwF
  have hInv : M.nodeInv S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s₀ + 1))) := by
    rw [hTI]; exact (lem11_node_invariant M F S A x R E K v huK).1
  have hB : n''.savedConfirmation s₀ = some B₀ := by
    have h := hSaved
    rw [hSv] at h
    exact h
  -- no live lock of the update's input vetoes `B₀`
  have hNoVeto : M.live_lock_vetoes (x.tickInput v (M.supportCutoff S.C (s₀ + 1)))
      ((M.supportCutoff S.C (s₀ + 1) : ℕ) : Int) B₀ = false :=
    (GoldilocksCorrectness.Record.Proofs.Routines.live_lock_vetoes_eq_false M F)
      hComp
  rw [hLc]
  rcases GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_latest_cases (Nat.add_one_ne_zero s₀) hUpd with
    ⟨hn, -⟩ | ⟨C', hC', ⟨hv', -⟩ | ⟨-, hadv⟩⟩
  · rw [Nat.add_sub_cancel, hB] at hn
    cases hn
  · rw [Nat.add_sub_cancel, hB] at hC'
    cases hC'
    rw [hNoVeto] at hv'
    cases hv'
  · rw [Nat.add_sub_cancel, hB] at hC'
    cases hC'
    refine hadv.trans ?_
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.advance_some F)
        (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s₀ + 1))))
        (x.tickInput v (M.supportCutoff S.C (s₀ + 1))).latestConfirmed B₀ with
      ⟨hin, hanc, ha⟩ | ⟨-, ha⟩
    · rw [ha]
      -- the old record is `B₀`: its slot is at most `s₀` (every tick of `v` before `K` is to a value less than `c₀`)
      have hoT := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hin).1
      have hsl' : (x.tickInput v (M.supportCutoff S.C (s₀ + 1))).latestConfirmed.slot ≤ s₀ := by
        rw [hTI]
        refine (latest_confirmed_slot_le M F U) x R E v s₀ K (fun k hk t hlk => ?_)
        have h1 := E.clock_mono k K v t _ hk huK (Or.inl hlk) (Or.inl hlK)
        rcases Nat.lt_or_eq_of_le h1 with h2 | h2
        · exact h2
        · subst h2
          exact absurd (E.tick_unique _ _ v _ hlk hlK) (Nat.ne_of_lt hk)
      by_contra hne
      -- an ancestor of a block of `v`'s closed tree, other than that block, has a smaller slot
      have hTC := F.nd.nodeInv_treeClosed hInv
      have hslt : ∀ D ∈ (x.tickInput v (M.supportCutoff S.C (s₀ + 1))).tree, B₀.AncestorEq D →
          B₀ ≠ D → B₀.slot < D.slot := by
        intro D
        induction D with
        | genesis =>
          exact fun _ hBD hne' => absurd ((GoldilocksCorrectness.Proofs.Routines.ancestorEq_genesis_iff B₀).1 hBD) hne'
        | node q sq r votes support ats u ih =>
          intro hD hBD hne'
          rcases (GoldilocksCorrectness.Proofs.Routines.ancestorEq_node_iff B₀ q sq r votes support ats u).1 hBD
            with h | h
          · exact absurd h hne'
          · obtain ⟨hqT, -, -, hqs⟩ := hTC.2 _ hD (fun h' => by cases h')
            have hqs' : q.slot < sq := hqs
            by_cases hBq : B₀ = q
            · rw [hBq]
              exact hqs'
            · exact lt_trans (ih hqT h hBq) hqs'
      have hlt := hslt _ hoT hanc (Ne.symm hne)
      exact absurd (lt_of_lt_of_le hlt hsl') (Nat.not_lt.2 hB₀slot)
    · exact ha

open Classical in
/-- **The record right after the update of the healed slot.** In an execution where every time
is reached and corruption is permanent: when `B₀`'s slot is at least
`s₀`, `HonestChainExtends` holds for `B₀` at slot `s₀` at the honest active validators of slot
`s₀`, and every updater of slot `s₀` saves `B₀` as its confirmation of slot `s₀`, then every
updater `v` of slot `s₀` holds `B₀` as its record of the confirmed tip right after the support
cutoff of slot `s₀ + 1`.

Why: `v`'s update of slot `s₀ + 1` ran (`update_state_of_duty`) and saved `B₀`; no live lock of
its input vetoes `B₀` (`live_locks_compatible_at_healed_update`), so it wrote
`advance Φ old (some B₀)`. That is `B₀` unless `old` is in `Φ.tree` and `B₀` is an ancestor of
`old` or `old` itself; but `old`, held before the support cutoff of slot `s₀ + 1`, has a slot at
most `s₀` (`latest_confirmed_slot_le`), which is at most `B₀`'s, and a strict ancestor of a tree
block has a smaller slot; so then `old = B₀`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `B₀`: the block every updater of slot `s₀` saved; `v`: the updater.

Read aloud: right after the update of the healed slot, every updater of that slot records `B₀` as
its confirmed tip. -/
theorem latest_confirmed_after_healed_update (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ : ℕ) (B₀ : Block V) (v : V)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the two clock bounds together are less than one delay
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- corruption is permanent
    -- `B₀`'s slot is at least `s₀`
    (hB₀slot : s₀ ≤ B₀.slot)
    -- the slot invariant restricted to `B₀` at slot `s₀`
    (hBase : HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀)
    -- every updater of slot `s₀` saved `B₀`
    (hBaseSaved : ∀ u ∈ updaterAt M S A x s₀,
      (x.tickOutput u (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀)
    -- `v` is an updater of slot `s₀`
    (hv : v ∈ updaterAt M S A x s₀)
    -- `v` is outside the adversary set after every step whose time is at most the support cutoff
    -- of slot `s₀ + 1`, and at every step at which a validator outside it ticks to that cutoff
    (hvc : v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) ∪
      Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
        x.lbl k = Event.tick w (M.supportCutoff S.C (s₀ + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k)) :
    (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).latestConfirmed = B₀ := by
  exact (latest_confirmed_after_update_of_compatible M F U) S A x R s₀ B₀ v E hSkew hB₀slot hv (hBaseSaved v hv)
    ((live_locks_compatible_at_healed_update M F U) S A x R s₀ B₀ v E hSkew hBase hv hvc)

open Classical in
/-- **`lem90a_latest_confirmed_honest_at`, the record after the healed round is an honest
confirmation, of a slot whose update ran by then.** The proof; the audited statement is in
`Statements/Executions/ConfirmedTipStatements.lean`.

Why: by induction on the steps from the tick at the time after the support cutoff `c` of slot
`s₀ + 1`. There, a validator honest at `c` is an updater of slot `s₀` (`hAwake`) and holds `B₀`
(`latest_confirmed_after_healed_update`), its saved confirmation of slot `s₀`. A later step keeps
the record (`step_cases_latest`), or is the validator's update of a slot `s + 1` after `c`, which
keeps it or writes the confirmation of slot `s ≥ s₀` it saves; the validator passed the duty test
of slot `s + 1`, so it is awake from that slot's duty window's start up to its tick
; a tick is by a validator active at
its step, so it is honest up to that tick and an updater of slot `s`
. The record is held
at every step (`latest_confirmed_mem_T_of_exec`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `B₀`: the block every updater of slot `s₀` saved.

Keeping the slot: the slot `s` of the confirmation the record is, with its update at the support
cutoff of slot `s + 1` at most the time of the step read, the time of the update that wrote it.

Read aloud: after the healed round's action time, the record of the confirmed tip of every validator
honest at the step is an honest confirmation of a slot whose update ran by then, and the validator
holds it. -/
theorem lem90a_latest_confirmed_honest_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ : ℕ) (B₀ : Block V)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the two clock bounds together are less than one delay
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- corruption is permanent
    -- `B₀`'s slot is at least `s₀`
    (hB₀slot : s₀ ≤ B₀.slot)
    -- the slot invariant restricted to `B₀` at slot `s₀`
    (hBase : HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀)
    -- every updater of slot `s₀` saved `B₀`
    (hBaseSaved : ∀ v ∈ updaterAt M S A x s₀,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀)
    -- every validator honest at the support cutoff of slot `s₀ + 1` is an updater of slot `s₀`
    (hAwake : ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) →
      v ∈ updaterAt M S A x s₀) :
    ∀ (i : ℕ) (v : V), v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) ∪
      Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
        x.lbl k = Event.tick w (M.supportCutoff S.C (s₀ + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k) →
      x.tickStep v (M.supportCutoff S.C (s₀ + 1)) < i → v ∉ A.corrupted i →
      (∃ s : ℕ, s₀ ≤ s ∧ x.lbl (x.tickStep v (M.supportCutoff S.C (s + 1))) = Event.tick v (M.supportCutoff S.C (s + 1)) ∧
        x.tickStep v (M.supportCutoff S.C (s + 1)) < i ∧ ∃ u ∈ updaterAt M S A x s,
        (x.tickOutput u (M.supportCutoff S.C (s + 1))).savedConfirmation s =
          some (x.st i v).latestConfirmed) ∧
        (x.st i v).latestConfirmed ∈ (x.st i v).tree := by
  intro i v hv₀ hi hvi
  have hU₀ := hAwake v (fun h => hv₀ (Finset.mem_union_left _ h))
  have hvw : v ∈ A.activeThroughoutToTick x (Goldilocks.duty_window_start S.C (s₀ + 1))
      (M.supportCutoff S.C (s₀ + 1)) := hU₀
  obtain ⟨K, hlK, -⟩ := Activity.mem_activeThroughoutToTick.1 hvw
  have hKs : x.tickStep v (M.supportCutoff S.C (s₀ + 1)) = K := (tickStep_eq_of_lbl M) x E hlK
  rw [hKs] at hi
  have hvi' : v ∉ A.corrupted i := hvi
  -- by induction on the steps from `K + 1` to `i`
  have key : ∀ j : ℕ, K + 1 ≤ j → j ≤ i →
      ∃ s : ℕ, s₀ ≤ s ∧ x.lbl (x.tickStep v (M.supportCutoff S.C (s + 1))) = Event.tick v (M.supportCutoff S.C (s + 1)) ∧
        x.tickStep v (M.supportCutoff S.C (s + 1)) < j ∧ ∃ u ∈ updaterAt M S A x s,
        (x.tickOutput u (M.supportCutoff S.C (s + 1))).savedConfirmation s =
          some (x.st j v).latestConfirmed := by
    intro j hKj hji
    induction j, hKj using Nat.le_induction with
    | base =>
        refine ⟨s₀, le_rfl, by rw [hKs]; exact hlK, by rw [hKs]; omega, v, hU₀, ?_⟩
        have hTO : x.st (K + 1) v = x.tickOutput v (M.supportCutoff S.C (s₀ + 1)) := by
          unfold Trace.tickOutput; rw [hKs]
        rw [hTO, (latest_confirmed_after_healed_update M F U) S A x R s₀ B₀ v E hSkew hB₀slot hBase
          hBaseSaved hU₀ hv₀]
        exact hBaseSaved v hU₀
    | succ j hKj ih =>
        obtain ⟨s', hs', hl', hlt', u', hu', hsv'⟩ := ih (by omega)
        have hvj : v ∉ A.corrupted j := fun h => hvi' (E.corrupted_mono _ _ (by omega) h)
        rcases (step_cases_latest M F) x R E j v with h | ⟨t, hl, -, ht, hAwT, hcu⟩
        · rw [h]
          exact ⟨s', hs', hl', by omega, u', hu', hsv'⟩
        · have hTIj : x.tickInput v t = x.st j v := by
            unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hl]
          -- the spec's slot of `t` is the layout's
          have hsl : S.C.slot (t : Int) = M.slot S.C t := by
            rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
              ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
          rw [hsl] at ht hcu hAwT
          by_cases hs0 : M.slot S.C t = 0
          · rw [hs0] at hcu
            rw [(GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_zero hcu).2.2.1, hTIj]
            exact ⟨s', hs', hl', by omega, u', hu', hsv'⟩
          rcases (GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_latest_confirmed F) hs0 hcu with h | ⟨h, -⟩
          · rw [h, hTIj]
            exact ⟨s', hs', hl', by omega, u', hu', hsv'⟩
          obtain ⟨s, hs⟩ : ∃ s : ℕ, M.slot S.C t = s + 1 :=
            ⟨_, (Nat.succ_pred_eq_of_ne_zero hs0).symm⟩
          have hcut := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot_eq M.toSlotLayout F.sched U) S ht
          rw [hs] at hcut
          -- the tick is to a value after `c₀`: `v` ticked to `c₀` at `K < j`
          have hc₀t : M.supportCutoff S.C (s₀ + 1) < t := by
            have h1 := E.clock_mono K j v _ t (by omega) hvj (Or.inl hlK) (Or.inl hl)
            rcases Nat.lt_or_eq_of_le h1 with h2 | h2
            · exact h2
            · subst h2
              exact absurd (E.tick_unique _ _ v _ hlK hl) (by omega)
          have hss₀ : s₀ ≤ s := ((GoldilocksCorrectness.Record.Proofs.Routines.slot_le_of_supportCutoff_lt
            M.toSlotLayout F.sched) S s₀ s).2.2 (by omega)
          rw [hs] at hAwT
          rw [← hcut] at hl hAwT
          have hjs : x.tickStep v (M.supportCutoff S.C (s + 1)) = j := (tickStep_eq_of_lbl M) x E hl
          refine ⟨s, hss₀, by rw [hjs]; exact hl, by rw [hjs]; omega, v, ?_, ?_⟩
          · -- `v` passed the duty test of slot `s + 1` at its tick: the reader of `updaterAt M S A x s`
            -- (`awake_of_tickInput_awakeSince_of_tick`, the reader's two cases)
            obtain ⟨τ, hτ, hτle⟩ := hAwT
            have hcases := (awake_of_tickInput_awakeSince_of_tick M F) x R E ⟨j, hl⟩ hτ
            rw [hjs] at hcases
            refine E.mem_activeThroughoutToTick_of_awakeThroughoutToTick ?_
            rcases hcases with ⟨-, hall⟩ | ⟨k₁, τ', hk₁, hl₁, hτ', hawk⟩
            · exact Activity.mem_awakeThroughoutToTick_of_forall hl hall
            · exact Activity.mem_awakeThroughoutToTick_of_tick (hτ' ▸ hτle) hk₁.le hl hl₁ hawk
          · -- its saved confirmation of slot `s`, left by the tick
            have hTO : x.tickOutput v (M.supportCutoff S.C (s + 1)) = x.st (j + 1) v := by
              unfold Trace.tickOutput; rw [hjs]
            rw [hTO]
            rw [hs, Nat.add_sub_cancel] at h
            exact h
  exact ⟨key i (by omega) le_rfl, (latest_confirmed_mem_T_of_exec M F U) x R E i v⟩

end Base

/-! ## Lemma 90, agreement and growth -/

section Lemma90

open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff)

variable {S : Setup V} {A : Activity V}

/-- An honest confirmation is on the honest chain: it is the confirmation of its own slot.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `s₀`: the first slot of the chain; `L`: the block.

Read aloud: an honest confirmation is on the honest chain. -/
theorem onHonestChain_of_isHonestConfirmation {x : Trace V (NamedObject V) M.N} {s₀ : ℕ}
    {L : Block V}
    -- `L` is an honest confirmation from slot `s₀`
    (h : IsHonestConfirmation M S A x s₀ L) : OnHonestChain M S A x s₀ L := by
  obtain ⟨s, hs, v, hv, hL⟩ := h
  exact ⟨s, hs, v, hv, L, hL, ancestorEq_refl L⟩

/-- **One step of Lemma 90's growth, from three compatibilities.** When, at steps `j` and `j + 1`,
`v`'s record is held in its tree, the record at step `j + 1` is compatible with the finalized block
at step `j + 1`, and the record at step `j` is compatible with the record at step `j + 1` and with
the finalized block at step `j`, then `v`'s confirmed tip at step `j` is an ancestor of, or equal
to, the one at step `j + 1`.

Why: `confirmedOf_step`'s proof, which reads the honest chain only for these three compatibilities.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `j`: the step; `v`: the validator.

Read aloud: when the records and the finalized blocks of two consecutive steps are compatible, the
confirmed tip of the later step extends the earlier one. -/
theorem confirmedOf_step_of_compatible {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (j : ℕ) (v : V)
    -- at step `j`, the record is held in the tree
    (hLT : (x.st j v).latestConfirmed ∈ (x.st j v).tree)
    -- at step `j + 1`, the record is held in the tree
    (hL'T : (x.st (j + 1) v).latestConfirmed ∈ (x.st (j + 1) v).tree)
    -- the three compatibilities
    (hL'F' : (x.st (j + 1) v).latestConfirmed.compatible (x.st (j + 1) v).finalized = true)
    (hLL' : (x.st j v).latestConfirmed.compatible (x.st (j + 1) v).latestConfirmed = true)
    (hLF : (x.st j v).latestConfirmed.compatible (x.st j v).finalized = true) :
    (M.ac_confirmed (x.st j v)).AncestorEq (M.ac_confirmed (x.st (j + 1) v)) := by
  have hFF := (F_ancestorEq_of_le M F) x R E v (Nat.le_succ j)
  -- the record at step `j` is an ancestor of, or equal to, the finalized block or the record at
  -- step `j + 1`
  have hkey : (x.st j v).latestConfirmed.AncestorEq (x.st (j + 1) v).finalized ∨
      (x.st j v).latestConfirmed.AncestorEq (x.st (j + 1) v).latestConfirmed := by
    rcases (step_cases_latest M F) x R E j v with h | ⟨t, hl, -, -, -, hcu⟩
    · right
      rw [h]
      exact ancestorEq_refl _
    obtain ⟨-, -, hTT, hFin, -, -, -, -, -, -, -, -, -, hLC, -⟩ :
        (x.tickInput v t).v = (x.st j v).v ∧
          (x.tickInput v t).t = (x.st j v).t ∧
          (x.tickInput v t).tree = (x.st j v).tree ∧
          (x.tickInput v t).finalized = (x.st j v).finalized ∧
          (x.tickInput v t).justified = (x.st j v).justified ∧
          (x.tickInput v t).justifiedHeight = (x.st j v).justifiedHeight ∧
          (x.tickInput v t).attestationsHeld = (x.st j v).attestationsHeld ∧
          M.votesHeld (x.tickInput v t) = M.votesHeld (x.st j v) ∧
          M.voteStamp (x.tickInput v t) = M.voteStamp (x.st j v) ∧
          M.blockStamp (x.tickInput v t) = M.blockStamp (x.st j v) ∧
          M.savedConfirmation (x.tickInput v t) = M.savedConfirmation (x.st j v) ∧
          (x.tickInput v t).lockEntries = (x.st j v).lockEntries ∧
          (x.tickInput v t).fastBlocks = (x.st j v).fastBlocks ∧
          (x.tickInput v t).latestConfirmed = (x.st j v).latestConfirmed ∧
          M.sentTarget (x.tickInput v t) = M.sentTarget (x.st j v) ∧
          M.sentTimeout (x.tickInput v t) = M.sentTimeout (x.st j v) ∧
          M.sentLock (x.tickInput v t) = M.sentLock (x.st j v) ∧
          (x.tickInput v t).sentAttestations = (x.st j v).sentAttestations := by
      rw [show x.tickInput v t = x.st j v by
        unfold Trace.tickInput
        rw [(tickStep_eq_of_lbl M) x E (i := j) (v := v) (by assumption)]]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    by_cases hs0 : S.C.slot (t : Int) = 0
    · rw [hs0] at hcu
      right
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_zero hcu).2.2.1, hLC]
      exact ancestorEq_refl _
    rcases GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_latest_cases hs0 hcu with
      ⟨-, h⟩ | ⟨C', -, ⟨-, h⟩ | ⟨-, h⟩⟩
    · right
      rw [h, hLC]
      exact ancestorEq_refl _
    · right
      rw [h, hLC]
      exact ancestorEq_refl _
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.advance_some F) (M.fg_to_ac (x.tickInput v t))
        (x.tickInput v t).latestConfirmed C' with
      ⟨-, -, ha⟩ | ⟨hnot, ha⟩
    · right
      rw [h, ha, hLC]
      exact ancestorEq_refl _
    have hL'eq : (x.st (j + 1) v).latestConfirmed = C' := by rw [h, ha]
    rw [hL'eq] at hLL'
    rcases (compatible_iff _ _).1 hLL' with h1 | h1
    · right
      rw [hL'eq]
      exact h1
    · -- `C'` is an ancestor of the old record, which is then not in the frame's tree
      left
      have hnin : ¬ (x.st j v).finalized.AncestorEq (x.st j v).latestConfirmed := fun hFL =>
        hnot ⟨((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2
          ⟨by rw [hLC, hTT]; exact hLT, by rw [hLC, hFin]; exact hFL⟩, by rw [hLC]; exact h1⟩
      rcases (compatible_iff _ _).1 hLF with h2 | h2
      · exact ancestorEq_trans h2 hFF
      · exact absurd h2 hnin
  -- the confirmed tip at step `j + 1` is a descendant of, or equal to, both its finalized block and
  -- its record: it is the record when the record is in the frame's tree (the reader fact
  -- `ac_confirmed_eq`), and the finalized block otherwise, of which the record, compatible with it,
  -- is then an ancestor
  have hc' : (x.st (j + 1) v).finalized.AncestorEq (M.ac_confirmed (x.st (j + 1) v)) ∧
      (x.st (j + 1) v).latestConfirmed.AncestorEq (M.ac_confirmed (x.st (j + 1) v)) := by
    rw [F.rd.ac_confirmed_eq]
    split
    · rename_i hin
      exact ⟨(((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hin).2, ancestorEq_refl _⟩
    · rename_i hout
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]
      refine ⟨ancestorEq_refl _, ?_⟩
      rcases (compatible_iff _ _).1 hL'F' with h1 | h1
      · exact h1
      · exact absurd (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hL'T, h1⟩) hout
  -- the confirmed tip at step `j` is the record or the finalized block
  rw [F.rd.ac_confirmed_eq (x.st j v)]
  split
  · rcases hkey with h1 | h1
    · exact ancestorEq_trans h1 hc'.1
    · exact ancestorEq_trans h1 hc'.2
  · rw [(GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]
    exact ancestorEq_trans hFF hc'.1

/-- **One step of Lemma 90's growth.** When, at steps `j` and `j + 1`, `v`'s record is an honest
confirmation held in its tree and its finalized block is on the honest chain, and the honest
confirmations form a chain, `v`'s confirmed tip at step `j` is an ancestor of, or equal to, the
one at step `j + 1`.

Why: `confirmedOf_ancestorEq_of`, with the finalized block only moving to a descendant
(`F_ancestorEq_of_le`) and the record at step `j` an ancestor of, or equal to, the finalized block
or the record at step `j + 1`: the step keeps the record (`step_cases_latest`), or is `v`'s
update, which keeps it or writes the confirmation `C'` it saves when `advance` does not keep it.
The record at step `j` and `C'`, both on the honest chain, are compatible; when `C'` is an
ancestor of the old record, `advance` not keeping the old record means it is not in the frame's
tree, so (held, and compatible with the finalized block) it is an ancestor of the finalized block.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `s₀`: the healed slot; `j`: the step; `v`: the validator.

It is `confirmedOf_step_of_compatible`, the three compatibilities read on the honest chain.

Read aloud: when the records are honest confirmations and the finalized blocks are on the honest
chain, the confirmed tip of the later of two consecutive steps extends the earlier one. -/
theorem confirmedOf_step {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {s₀ : ℕ} (j : ℕ) (v : V)
    -- the honest confirmations form a chain from slot `s₀`
    (hChain : ConfirmationsChain M S A x s₀)
    -- at step `j`, the record is an honest confirmation held in the tree
    (hL : IsHonestConfirmation M S A x s₀ (x.st j v).latestConfirmed)
    (hLT : (x.st j v).latestConfirmed ∈ (x.st j v).tree)
    -- at step `j`, the finalized block is on the honest chain
    (hF : OnHonestChain M S A x s₀ (x.st j v).finalized)
    -- at step `j + 1`, the record is an honest confirmation held in the tree
    (hL' : IsHonestConfirmation M S A x s₀ (x.st (j + 1) v).latestConfirmed)
    (hL'T : (x.st (j + 1) v).latestConfirmed ∈ (x.st (j + 1) v).tree)
    -- at step `j + 1`, the finalized block is on the honest chain
    (hF' : OnHonestChain M S A x s₀ (x.st (j + 1) v).finalized) :
    (M.ac_confirmed (x.st j v)).AncestorEq (M.ac_confirmed (x.st (j + 1) v)) :=
  have hcomp : ∀ B B' : Block V, OnHonestChain M S A x s₀ B → OnHonestChain M S A x s₀ B' →
      B.compatible B' = true := fun B B' hB hB' =>
    (onHonestChain_compatible M F) S A x s₀ B B' hChain hB hB'
  (confirmedOf_step_of_compatible M F R E) j v hLT hL'T
    (hcomp _ _ ((onHonestChain_of_isHonestConfirmation M F) hL') hF')
    (hcomp _ _ ((onHonestChain_of_isHonestConfirmation M F) hL)
      ((onHonestChain_of_isHonestConfirmation M F) hL'))
    (hcomp _ _ ((onHonestChain_of_isHonestConfirmation M F) hL) hF)

/-- **Lemma 90, growth, read up to a time `t`.** The proof; the audited statement is in
`Statements/Executions/ConfirmedTipStatements.lean`.

Why: by induction on the later step, with `confirmedOf_step` at each step: `v` is honest at every
step up to the later one, so the records and the caches at those steps are on the honest chain by
the two hypotheses.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `H`: the threshold of the caches; `i₁`: the step from which the facts hold; `t`: the time up to
  which the later confirmed tip is read.

Caches up to `t`: the proof reads the caches in the states the steps up to the later one leave,
at times at most `t`; the record and the caches are read in the state a step leaves, as the
conclusion is.

Read aloud: from the phase's end to `t`, the confirmed tip of a validator honest through the later
of two steps only extends. -/
theorem lem90_confirmed_monotone_until (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s₀ H i₁ t : ℕ)
    -- the honest confirmations form a chain from slot `s₀`
    (hChain : ConfirmationsChain M S A x s₀)
    -- from the time of step `i₁` on, in the state a step leaves, an honest validator's record is an
    -- honest confirmation it holds
    (hLatest : ∀ (i : ℕ) (v : V), x.time i₁ ≤ x.time i → v ∉ A.corrupted i →
      IsHonestConfirmation M S A x s₀ (x.st (i + 1) v).latestConfirmed ∧
        (x.st (i + 1) v).latestConfirmed ∈ (x.st (i + 1) v).tree)
    -- from the time of step `i₁` to `t`, in the state a step leaves, an honest validator's caches
    -- are on the honest chain
    (hCaches : ∀ (i : ℕ) (v : V), x.time i₁ ≤ x.time i → x.time i ≤ t →
      v ∉ A.corrupted i → CachesOnChain M S A x s₀ H (x.st (i + 1) v)) :
    ConfirmedMonotoneBetween M S A x (x.time i₁) t := by
  intro v i j hij hj hi hjt
  revert hjt
  induction j, hij using Nat.le_induction with
  | base => exact fun _ => ancestorEq_refl _
  | succ j hij ih =>
      intro hjt
      have hjj : A.HonestThroughTime x (x.time j) v := fun i' hi' =>
        hj i' (show x.time i' ≤ x.time (j + 1) from le_trans hi' ((time_le_succ M) x R j))
      have htj : x.time i₁ ≤ x.time j := le_trans hi ((time_mono M) x R hij)
      have htj1 : x.time i₁ ≤ x.time (j + 1) := le_trans htj ((time_le_succ M) x R j)
      have hvj : v ∉ A.corrupted j := hjj _ le_rfl
      have hvj1 : v ∉ A.corrupted (j + 1) := hj _ le_rfl
      obtain ⟨hL, hLT⟩ := hLatest j v htj hvj
      obtain ⟨hL', hL'T⟩ := hLatest (j + 1) v htj1 hvj1
      have hjt' : x.time j ≤ t := le_trans ((time_le_succ M) x R j) hjt
      have hC := hCaches j v htj hjt' hvj
      have hC' := hCaches (j + 1) v htj1 hjt hvj1
      exact ancestorEq_trans (ih hjj hjt') ((confirmedOf_step M F R E) (j + 1) v hChain hL hLT
        ((onHonestChain_of_ancestorEq M F) hC.2.1 hC.2.2.2.2) hL' hL'T
        ((onHonestChain_of_ancestorEq M F) hC'.2.1 hC'.2.2.2.2))

/-- **Kit fact, a tick before a step is at a time at most that step's.** When some validator ticks to
the clock value `c` at a step before `i`, and the time of step `i` is at most `t`, that tick is at a
step whose time is at most `t`.

Why: the time of a step only grows with the step (`time_mono`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `c`: the clock value; `i`: the step; `t`: the bound.

Read aloud: a tick before a step at a time at most `t` is at a time at most `t`. -/
theorem tick_time_le_of_lt {S : Setup V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {c i : ℕ} {t : ℝ}
    -- some validator ticks to `c` at a step before `i`
    (h : ∃ (k : ℕ) (u : V), k < i ∧ x.lbl k = Event.tick u c)
    -- step `i` is at a time at most `t`
    (hi : x.time i ≤ t) :
    ∃ (k : ℕ) (u : V), x.lbl k = Event.tick u c ∧ x.time k ≤ t := by
  obtain ⟨k, u, hk, hl⟩ := h
  exact ⟨k, u, hl, le_trans ((time_mono M) x R hk.le) hi⟩

/-- **Kit fact, two blocks on the honest chain at slots whose update is at most `t` are
compatible**, when the updaters' confirmations of the slots whose update is at most `t` form one
chain from slot `s₀`.

Why: both blocks are on the chain before the slot after the later of the two slots, whose update
some validator ran at a step by the time `t`; two blocks on the chain before a slot are compatible
(`onHonestChainBefore_compatible`).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t`: the
  bound; `σ`, `σ'`: the two slots; `B`, `B'`: the two blocks.

Read aloud: two blocks on the honest chain at slots updated by `t` are compatible, when the
confirmations of those slots form one chain. -/
theorem compatible_of_onHonestChainAt (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (s₀ t σ σ' : ℕ) (B B' : Block V)
    -- the updaters' confirmations of the slots whose update some validator ran at a step by `t` form one chain
    (hChain : ∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
        x.time k ≤ t → ConfirmationsChainBefore M S A x s₀ (σ + 1))
    (hB : OnHonestChainAt M S A x s₀ σ B)
    (hσ : ∃ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) ∧ x.time k ≤ t)
    (hB' : OnHonestChainAt M S A x s₀ σ' B')
    (hσ' : ∃ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ' + 1)) ∧ x.time k ≤ t) :
    B.compatible B' = true := by
  rcases le_total σ σ' with h | h
  · obtain ⟨k, u, hk, hkt⟩ := hσ'
    exact (onHonestChainBefore_compatible M F) S A x s₀ (σ' + 1) B B' (hChain σ' k u hk hkt)
      ⟨σ, Nat.lt_succ_of_le h, hB⟩ ⟨σ', Nat.lt_succ_self σ', hB'⟩
  · obtain ⟨k, u, hk, hkt⟩ := hσ
    exact (onHonestChainBefore_compatible M F) S A x s₀ (σ + 1) B B' (hChain σ k u hk hkt)
      ⟨σ, Nat.lt_succ_self σ, hB⟩ ⟨σ', Nat.lt_succ_of_le h, hB'⟩

/-- **Kit fact, the finalized block of an honest state is on the chain at a slot whose update ran
by then.** Under the hypotheses of `justified_onHonestChainAt_of_caches` at the healed slot (the
honest attestations from the support cutoff of slot `s₀ + 1` on the chain, Lemma 82), when `v`'s
caches after `i` steps are on the honest chain: `v`'s finalized block is on the honest chain at a
slot whose update some validator ran at a step before `i`.

Why: the finalized block is the justified block or an ancestor of it (`CachesOnChain`), and the
justified block, above the threshold, is on the chain at such a slot
(`justified_onHonestChainAt_of_caches`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the
  threshold; `i`: the step; `v`: the validator.

Read aloud: when an honest validator's caches are on the honest chain, its finalized block is on the
honest chain at a slot already updated. -/
theorem finalized_onHonestChainAt_of_caches (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H i : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x (x.time i))
    -- fewer than a quorum of validators have been in the adversary set up to the later of `x.time i` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time i) (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hv : v ∉ A.corrupted i)
    (hC : CachesOnChain M S A x s₀ H (x.st i v)) :
    ∃ σ : ℕ, (∃ (k : ℕ) (u : V), k < i ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1))) ∧
      OnHonestChainAt M S A x s₀ σ (x.st i v).finalized := by
  obtain ⟨σ, hσ, hJ⟩ := (justified_onHonestChainAt_of_caches M F U Fx) S A x R s₀ (M.supportCutoff S.C (s₀ + 1))
    H i v E hRoots hAdvQ ((lem82_honest_attestations_on_chain M F U) S A x R s₀ E) hOld hv
    hC.1
  exact ⟨σ, hσ, (onHonestChainAt_of_ancestorEq M F) hJ hC.2.2.2.2⟩

/-- **Kit fact, the confirmed tip of an honest state is on the chain at a slot whose update ran by
then.** When `v`'s record after `i` steps is on the honest chain at a slot whose update some
validator ran at a step before `i`, and
its caches are on the honest chain, under the
hypotheses of `finalized_onHonestChainAt_of_caches`: so is `v`'s confirmed tip.

Why: the confirmed tip is the record or the finalized block (`ac_confirmed_cases`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the
  threshold; `i`: the step; `v`: the validator.

Read aloud: when an honest validator's record and caches are on the honest chain at slots already
updated, so is its confirmed tip. -/
theorem confirmedOf_onHonestChainAt (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H i : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x (x.time i))
    -- fewer than a quorum of validators have been in the adversary set up to the later of `x.time i` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time i) (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hv : v ∉ A.corrupted i)
    (hL : ∃ σ : ℕ, (∃ (k : ℕ) (u : V), k < i ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1))) ∧
      OnHonestChainAt M S A x s₀ σ (x.st i v).latestConfirmed)
    (hC : CachesOnChain M S A x s₀ H (x.st i v)) :
    ∃ σ : ℕ, (∃ (k : ℕ) (u : V), k < i ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1))) ∧
      OnHonestChainAt M S A x s₀ σ (M.ac_confirmed (x.st i v)) := by
  -- the confirmed tip is the record when the record is in the frame's tree, the frame's finalized
  -- block otherwise (the reader fact `ac_confirmed_eq`)
  rw [F.rd.ac_confirmed_eq]
  split
  · exact hL
  · rw [(GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]
    exact (finalized_onHonestChainAt_of_caches M F U Fx) S A x R s₀ H i v E hRoots hAdvQ hOld hv
      hC

/-- **Kit fact, a tick before the step after `i` is at a time at most that of step `i`'s bound.**
When some validator ticks to `c` at a step before `i + 1` and step `i` is at a time at most `t`, the
tick is at a time at most `t`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `c`: the clock value; `i`: the step; `t`: the bound.

Read aloud: a tick at or before step `i` is at a time at most any bound on step `i`'s time. -/
theorem tick_time_le_of_lt_succ {S : Setup V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {c i : ℕ} {t : ℝ}
    -- some validator ticks to `c` at a step before `i + 1`
    (h : ∃ (k : ℕ) (u : V), k < i + 1 ∧ x.lbl k = Event.tick u c)
    -- step `i` is at a time at most `t`
    (hi : x.time i ≤ t) :
    ∃ (k : ℕ) (u : V), x.lbl k = Event.tick u c ∧ x.time k ≤ t := by
  obtain ⟨k, u, hk, hl⟩ := h
  exact ⟨k, u, hl, le_trans ((time_mono M) x R (Nat.lt_succ_iff.1 hk)) hi⟩

/-- **Kit fact, the finalized block of an honest state is on the chain at a slot whose update ran by
then, read in the state a step leaves.** `finalized_onHonestChainAt_of_caches` for the state step `i`
leaves, with the roots, the adversary count and the honesty read at step `i`.

Why: step `i` is of the kind `other` and leaves `v`'s state as it was, so the fact at step `i`
applies; or it keeps the time and the adversary set, so the fact at step `i + 1` applies
(`step_succ_cases`). In the first case the tick before `i` is before `i + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `s₀`: the healed slot; `H`: the
  threshold; `i`: the step; `v`: the validator.

Read aloud: when an honest validator's caches right after a step are on the honest chain, its
finalized block there is on the honest chain at a slot already updated. -/
theorem finalized_onHonestChainAt_of_caches_succ (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H i : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x (x.time i))
    -- fewer than a quorum of validators have been in the adversary set up to the later of `x.time i` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time i) (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hv : v ∉ A.corrupted i)
    (hC : CachesOnChain M S A x s₀ H (x.st (i + 1) v)) :
    ∃ σ : ℕ, (∃ (k : ℕ) (u : V), k < i + 1 ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1))) ∧
      OnHonestChainAt M S A x s₀ σ (x.st (i + 1) v).finalized := by
  rcases (step_succ_cases M F) x R E i with ⟨-, h⟩ | ⟨ht, hc⟩
  · rw [h v] at hC ⊢
    obtain ⟨σ, ⟨k, u, hk, hl⟩, hB⟩ :=
      (finalized_onHonestChainAt_of_caches M F U Fx) S A x R s₀ H i v E hRoots hAdvQ hOld hv hC
    exact ⟨σ, ⟨k, u, Nat.lt_succ_of_lt hk, hl⟩, hB⟩
  · exact (finalized_onHonestChainAt_of_caches M F U Fx) S A x R s₀ H (i + 1) v E
      (by rw [ht]; exact hRoots) (by rw [ht]; exact hAdvQ) hOld (by rw [hc]; exact hv) hC

/-- **Kit fact, the confirmed tip of an honest state is on the chain at a slot whose update ran by
then, read in the state a step leaves.** `confirmedOf_onHonestChainAt` for the state step `i` leaves,
with the roots, the adversary count and the honesty read at step `i`.

Why: as `finalized_onHonestChainAt_of_caches_succ`; when step `i` is of the kind `other`, the tick
before `i + 1` that the record names is not step `i`, which is no tick, so it is before `i`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `s₀`: the healed slot; `H`: the
  threshold; `i`: the step; `v`: the validator.

Read aloud: when an honest validator's record and caches right after a step are on the honest chain
at slots already updated, so is its confirmed tip there. -/
theorem confirmedOf_onHonestChainAt_succ (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H i : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x (x.time i))
    -- fewer than a quorum of validators have been in the adversary set up to the later of `x.time i` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time i) (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hv : v ∉ A.corrupted i)
    (hL : ∃ σ : ℕ, (∃ (k : ℕ) (u : V), k < i + 1 ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1))) ∧
      OnHonestChainAt M S A x s₀ σ (x.st (i + 1) v).latestConfirmed)
    (hC : CachesOnChain M S A x s₀ H (x.st (i + 1) v)) :
    ∃ σ : ℕ, (∃ (k : ℕ) (u : V), k < i + 1 ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1))) ∧
      OnHonestChainAt M S A x s₀ σ (M.ac_confirmed (x.st (i + 1) v)) := by
  rcases (step_succ_cases M F) x R E i with ⟨hl, h⟩ | ⟨ht, hc⟩
  · rw [h v] at hC hL ⊢
    obtain ⟨σL, ⟨kL, uL, hkL, hlL⟩, hBL⟩ := hL
    have hkL' : kL < i := by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hkL with h' | h'
      · exact h'
      · subst h'; rw [hl] at hlL; cases hlL
    obtain ⟨σ, ⟨k, u, hk, hl'⟩, hB⟩ :=
      (confirmedOf_onHonestChainAt M F U Fx) S A x R s₀ H i v E hRoots hAdvQ hOld hv
        ⟨σL, ⟨kL, uL, hkL', hlL⟩, hBL⟩ hC
    exact ⟨σ, ⟨k, u, Nat.lt_succ_of_lt hk, hl'⟩, hB⟩
  · exact (confirmedOf_onHonestChainAt M F U Fx) S A x R s₀ H (i + 1) v E
      (by rw [ht]; exact hRoots) (by rw [ht]; exact hAdvQ) hOld (by rw [hc]; exact hv) hL hC

/-- **Lemma 90, agreement, on the chain before a slot.** The proof; the audited statement is in
`Statements/Executions/ConfirmedTipStatements.lean`. From the time of step `i₁` to `t`: when the
updaters' confirmations of the slots whose update is at most `t` form one chain from slot `s₀`,
an honest validator's record is on the honest chain at a slot whose update ran by then, its caches
are on the honest chain, roots name blocks among what honest validators hold by `t`, and the
attestations behind the caches are as at the healed slot: the confirmed tips of two validators
honest through their steps are compatible.

Why: each confirmed tip is on the honest chain at a slot whose update ran by its step
(`confirmedOf_onHonestChainAt`), so at most `t`, and two such blocks are compatible
(`compatible_of_onHonestChainAt`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `H`: the threshold of the caches; `i₁`: the step from which the facts hold; `t`: the time up to
  which the confirmed tips are read.

On the chain before a slot: the two confirmed tips compared are on the chain at slots whose update
is at most `t`, which `ConfirmationsChainBefore` covers; the landed form reads `ConfirmationsChain`
at every slot.

Read aloud: when the confirmations of the slots some validator updated by `t` form one chain, from the phase's end
to `t` the confirmed tips of two validators honest at their steps are compatible. -/
theorem lem90_confirmed_agree_before (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H i₁ t : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x t)
    -- fewer than a quorum of validators have been in the adversary set up to the later of `t` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max t (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the updaters' confirmations of the slots whose update some validator ran at a step by `t` form one chain
    (hChain : ∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
        x.time k ≤ t → ConfirmationsChainBefore M S A x s₀ (σ + 1))
    -- in the state each step at a time from that of step `i₁` to `t` leaves, an honest validator's record is on the honest chain at a
    -- slot whose update ran by then
    (hLatest : ∀ (i : ℕ) (v : V), x.time i₁ ≤ x.time i → x.time i ≤ t →
      v ∉ A.corrupted i → ∃ σ : ℕ, x.lbl (x.tickStep v (M.supportCutoff S.C (σ + 1))) = Event.tick v (M.supportCutoff S.C (σ + 1)) ∧ x.tickStep v (M.supportCutoff S.C (σ + 1)) < i + 1 ∧
        OnHonestChainAt M S A x s₀ σ (x.st (i + 1) v).latestConfirmed)
    -- in the state each step at a time from that of step `i₁` to `t` leaves, an honest validator's caches are on the honest chain
    (hCaches : ∀ (i : ℕ) (v : V), x.time i₁ ≤ x.time i → x.time i ≤ t →
      v ∉ A.corrupted i → CachesOnChain M S A x s₀ H (x.st (i + 1) v)) :
    ConfirmedAgreeBetween M S A x (x.time i₁) t := by
  rw [(GoldilocksCorrectness.Record.Proofs.View.confirmedAgreeBetween_unfold M x)]
  intro v₁ v₂ i j h₁ h₂ hi hj hit hjt
  have hh₁ : v₁ ∉ A.corrupted i := h₁ _ le_rfl
  have hh₂ : v₂ ∉ A.corrupted j := h₂ _ le_rfl
  obtain ⟨σ₁, hl₁, hk₁, hB₁⟩ := hLatest i v₁ hi hit hh₁
  obtain ⟨σ₂, hl₂, hk₂, hB₂⟩ := hLatest j v₂ hj hjt hh₂
  obtain ⟨σ, hσ, hB⟩ := (confirmedOf_onHonestChainAt_succ M F U Fx) S A x R s₀ H i v₁ E
    ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hit hRoots) (hAdvQ.mono ((max_le_max_right _ hit))) hOld hh₁
    ⟨σ₁, ⟨_, v₁, hk₁, hl₁⟩, hB₁⟩ (hCaches i v₁ hi hit hh₁)
  obtain ⟨σ', hσ', hB'⟩ := (confirmedOf_onHonestChainAt_succ M F U Fx) S A x R s₀ H j v₂ E
    ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hjt hRoots) (hAdvQ.mono ((max_le_max_right _ hjt))) hOld hh₂
    ⟨σ₂, ⟨_, v₂, hk₂, hl₂⟩, hB₂⟩ (hCaches j v₂ hj hjt hh₂)
  exact (compatible_of_onHonestChainAt M F) S A x s₀ t σ σ' _ _ hChain hB
    ((tick_time_le_of_lt_succ M F) R hσ hit) hB' ((tick_time_le_of_lt_succ M F) R hσ' hjt)

/-- **Lemma 90, growth, on the chain before a slot.** The proof; the audited statement is in
`Statements/Executions/ConfirmedTipStatements.lean`. Under the hypotheses of
`lem90_confirmed_agree_before`, the record also held in the tree: the confirmed tip of a validator
honest through the later of two steps, the later at a time at most `t`, only extends.

Why: by induction on the later step, with `confirmedOf_step_of_compatible` at each step: the
records and finalized blocks at the two steps of each step are on the honest chain at slots whose
update ran by then (the hypothesis on the record, `finalized_onHonestChainAt_of_caches`), so at
most `t`, and compatible (`compatible_of_onHonestChainAt`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `H`: the threshold of the caches; `i₁`: the step from which the facts hold; `t`: the time up to
  which the later confirmed tip is read.

On the chain before a slot: as `lem90_confirmed_agree_before`.

Read aloud: when the confirmations of the slots some validator updated by `t` form one chain, from the phase's end
to `t` the confirmed tip of a validator honest through the later of two steps only extends. -/
theorem lem90_confirmed_monotone_before (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H i₁ t : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x t)
    -- fewer than a quorum of validators have been in the adversary set up to the later of `t` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max t (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the updaters' confirmations of the slots whose update some validator ran at a step by `t` form one chain
    (hChain : ∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
        x.time k ≤ t → ConfirmationsChainBefore M S A x s₀ (σ + 1))
    -- in the state each step at a time from that of step `i₁` to `t` leaves, an honest validator's record is on the honest chain at a
    -- slot whose update ran by then, and it holds it
    (hLatest : ∀ (i : ℕ) (v : V), x.time i₁ ≤ x.time i → x.time i ≤ t →
      v ∉ A.corrupted i → (∃ σ : ℕ, x.lbl (x.tickStep v (M.supportCutoff S.C (σ + 1))) = Event.tick v (M.supportCutoff S.C (σ + 1)) ∧ x.tickStep v (M.supportCutoff S.C (σ + 1)) < i + 1 ∧
        OnHonestChainAt M S A x s₀ σ (x.st (i + 1) v).latestConfirmed) ∧
        (x.st (i + 1) v).latestConfirmed ∈ (x.st (i + 1) v).tree)
    -- in the state each step at a time from that of step `i₁` to `t` leaves, an honest validator's caches are on the honest chain
    (hCaches : ∀ (i : ℕ) (v : V), x.time i₁ ≤ x.time i → x.time i ≤ t →
      v ∉ A.corrupted i → CachesOnChain M S A x s₀ H (x.st (i + 1) v)) :
    ConfirmedMonotoneBetween M S A x (x.time i₁) t := by
  intro v i j hij hj hi hjt
  revert hjt
  induction j, hij using Nat.le_induction with
  | base => exact fun _ => ancestorEq_refl _
  | succ j hij ih =>
      intro hjt
      have hjj : A.HonestThroughTime x (x.time j) v := fun i' hi' =>
        hj i' (show x.time i' ≤ x.time (j + 1) from le_trans hi' ((time_le_succ M) x R j))
      have hjt' : x.time j ≤ t := le_trans ((time_le_succ M) x R j) hjt
      have htj : x.time i₁ ≤ x.time j := le_trans hi ((time_mono M) x R hij)
      have htj1 : x.time i₁ ≤ x.time (j + 1) := le_trans htj ((time_le_succ M) x R j)
      have hvj : v ∉ A.corrupted j := hjj _ le_rfl
      have hvj1 : v ∉ A.corrupted (j + 1) := hj _ le_rfl
      obtain ⟨⟨σL, hlL, hkL, hL⟩, hLT⟩ := hLatest j v htj hjt' hvj
      obtain ⟨⟨σL', hlL', hkL', hL'⟩, hL'T⟩ := hLatest (j + 1) v htj1 hjt hvj1
      obtain ⟨σF, hσF, hF⟩ := (finalized_onHonestChainAt_of_caches_succ M F U Fx) S A x R s₀ H j v E
        ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hjt' hRoots) (hAdvQ.mono ((max_le_max_right _ hjt'))) hOld hvj (hCaches j v htj hjt' hvj)
      obtain ⟨σF', hσF', hF'⟩ := (finalized_onHonestChainAt_of_caches_succ M F U Fx) S A x R s₀ H (j + 1) v E
        ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hjt hRoots) (hAdvQ.mono ((max_le_max_right _ hjt))) hOld hvj1 (hCaches (j + 1) v htj1 hjt hvj1)
      have hσL := (tick_time_le_of_lt_succ M F) R ⟨_, v, hkL, hlL⟩ hjt'
      have hσL' := (tick_time_le_of_lt_succ M F) R ⟨_, v, hkL', hlL'⟩ hjt
      have hc := fun σ σ' (B B' : Block V) => (compatible_of_onHonestChainAt M F) S A x s₀ t σ σ' B B'
        hChain
      exact ancestorEq_trans (ih hjj hjt') ((confirmedOf_step_of_compatible M F R E) (j + 1) v hLT hL'T
        (hc _ _ _ _ hL' hσL' hF' ((tick_time_le_of_lt_succ M F) R hσF' hjt))
        (hc _ _ _ _ hL hσL hL' hσL')
        (hc _ _ _ _ hL hσL hF ((tick_time_le_of_lt_succ M F) R hσF hjt')))

/-- **Kit fact, the first step at a time.** In an execution where every time is reached, the step
right after the tick at `t ≥ 1` is the first step at the time `t`: a step at that time or later
comes no earlier.

Why: every step up to the tick at `t` is at a time before `t` (`time_lt_iff_le_stepBefore`), and
the step after it is at `t` (`stepBefore_spec`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `t`: the time; `i`: the step.

Read aloud: a step at a time at least `t` comes at or after the first step at `t`. -/
theorem stepBefore_succ_le_of_time_le {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {t i : ℕ}
    -- `t` is at least `1`
    (ht : 1 ≤ t)
    -- step `i` is at a time at least that of the step after the tick at `t`
    (hi : x.time (x.stepBefore t + 1) ≤ x.time i) :
    x.stepBefore t + 1 ≤ i := by
  obtain ⟨h1, h2⟩ := (stepBefore_time M) x R E ht
  by_contra hlt
  have hle : i ≤ x.stepBefore t := by omega
  have := (time_mono M) x R hle
  linarith

end Lemma90

end GoldilocksCorrectness.Record.Proofs.Executions

