module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncResilienceDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Relay
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.SleepyStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma39
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma90
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Locks
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Node
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.LockSteps
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Clock
public import GoldilocksCorrectness.Proofs.Executions.PeriodHolders
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# PeriodHolders, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/PeriodHolders.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: the bundle `AsyncHyps` of the asynchronous
period's hypotheses, and what a step does to a validator's lock entries, record and fast blocks
inside the period. The page's routine-level theorems are the facts' fields or have their twins in
phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem
  supportCutoff_cast supportCutoff_eq voteTime_cast voteTime_eq)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.Executions (acObject fgObject)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

open GoldilocksCorrectness.Statements.AbstractTrace (SyncedWithinOutside)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

section Period

variable (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)

/-- unforgeability; fewer than a quorum ever corrupted (Lemma
87's conclusion); committee sleepiness from `anchor`, at or before the start of slot `s + 1`;
`GST` at or before `b₀`; the period's bounds; the lock holders' majority;
`t₀` at or before the hand-over cutoff; and the hand-over facts, whose last clause reads the
confirmed tips from `tAwakeEnd` on.

The variables:
- `M`: the model.

Read aloud: the hypotheses of the asynchronous period's step lemmas, bundled. -/
structure AsyncHyps (GST s : ℕ) (B : Block V) (H t₀ anchor tAwakeEnd b₀ b₁ : ℕ) (Δs Δs_F : ℕ) (release : NamedObject V → Option ℕ) (ΔRedeliver : ℕ) (ΔClockAhead ΔClockBehind : ℝ) (tW : ℝ) : Prop where
  hSync : x.SynchronyFromWakeOutside A (Δ S) ΔRedeliver GST release acObject b₀ b₁
  /-- What an honest active validator would serve at a time `t` reaches every validator active
  from `t` within `Δs` of the later of `t` and `GST` when that is at or before `b₀`, and within `Δs`
  of the latest of `t`, `b₁` and `GST` otherwise (blocks and Goldfish votes). -/
  Sy : SyncedWithinOutside A x (servesMin M S.C) acObject release ΔRedeliver Δs GST b₀ b₁
  hSyncF : x.SynchronyFromWakeOutside A (Δ_F S) ΔRedeliver GST release fgObject b₀ b₁
  /-- The same for attestations, within `Δs_F`. -/
  Sy_F : SyncedWithinOutside A x (servesMin M S.C) fgObject release ΔRedeliver Δs_F GST b₀ b₁
  hParent : ParentHeldAtDelivery M x
  hAdvQ : ∀ t : ℕ, A.AdversaryFewerThanQuorumUntil x (quorum V) t
  hSleepK : CommitteeSleepiness M S A x anchor
  hAnchor : anchor ≤ M.slotStart S.C (s + 1)
  hGST : GST ≤ b₀
  hb₀ : M.supportCutoff S.C (s + 1) ≤ b₀
  hb : b₀ ≤ b₁
  /-- The period plus its recovery `max (Δ S) Δs` ends before the vote time of slot `s + k`. -/
  hb₁ : b₁ + max (Δ S) Δs ≤ M.voteTime S.C (s + S.C.k)
  hHold : HoldersOutweighWhereOwed M S A x s Δs b₀ b₁
  ht₀ : t₀ ≤ M.supportCutoff S.C (s + 1)
  hHand : HandoverFacts M S A x tW s B H t₀ tAwakeEnd

/-- `AsyncHypsUntil M S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T`: `AsyncHyps` with its
two premises bounded: fewer than a quorum corrupted up to `T`
(`hAdvQ`), and committee sleepiness from `anchor` for every slot whose support cutoff is at most
`T` (`hSleepK`). Every other field is `AsyncHyps`'s, with the same name, but the hand-over facts `hHand`, which
no reader of this bundle reads.

`AsyncHyps.toUntil` gives it at every `T`; the step lemmas of the period's induction take it, with
a hypothesis bounding the time they read by `T`.

The variables:
- `M`: the model; `T`: the time up to which the premises are read.

Read aloud: the hypotheses of the asynchronous period's step lemmas, bundled, with fewer than a
quorum corrupted up to `T` and committee sleepiness for the committees counted up to `T`. -/
structure AsyncHypsUntil (GST s : ℕ) (B : Block V) (H t₀ anchor tAwakeEnd b₀ b₁ : ℕ) (Δs Δs_F T : ℕ) (release : NamedObject V → Option ℕ) (ΔRedeliver : ℕ) (ΔClockAhead ΔClockBehind : ℝ) :
    Prop where
  hSync : x.SynchronyFromWakeOutside A (Δ S) ΔRedeliver GST release acObject b₀ b₁
  /-- What an honest active validator would serve at a time `t` reaches every validator active
  from `t` within `Δs` of the later of `t` and `GST` when that is at or before `b₀`, and within `Δs`
  of the latest of `t`, `b₁` and `GST` otherwise (blocks and Goldfish votes). -/
  Sy : SyncedWithinOutside A x (servesMin M S.C) acObject release ΔRedeliver Δs GST b₀ b₁
  hSyncF : x.SynchronyFromWakeOutside A (Δ_F S) ΔRedeliver GST release fgObject b₀ b₁
  /-- The same for attestations, within `Δs_F`. -/
  Sy_F : SyncedWithinOutside A x (servesMin M S.C) fgObject release ΔRedeliver Δs_F GST b₀ b₁
  hParent : ParentHeldAtDelivery M x
  /-- Fewer than a quorum have been corrupted up to `T`. -/
  hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) T
  /-- From `anchor` on, for every slot whose support cutoff is at most `T`, the honest active
  members of the previous slot's committee outnumber the rest. -/
  hSleepK : CommitteeSleepinessUntil M S A x anchor T
  hAnchor : anchor ≤ M.slotStart S.C (s + 1)
  hGST : GST ≤ b₀
  hb₀ : M.supportCutoff S.C (s + 1) ≤ b₀
  hb : b₀ ≤ b₁
  /-- The period plus its recovery `max (Δ S) Δs` ends before the vote time of slot `s + k`. -/
  hb₁ : b₁ + max (Δ S) Δs ≤ M.voteTime S.C (s + S.C.k)
  hHold : HoldersOutweighWhereOwed M S A x s Δs b₀ b₁
  ht₀ : t₀ ≤ M.supportCutoff S.C (s + 1)

end Period

end GoldilocksCorrectness.Record.Statements.Executions

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Record.Proofs.Routines
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem
  supportCutoff_cast supportCutoff_eq voteTime_cast voteTime_eq)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated LocksRevoked)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once. No statement and no proof term changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## The bounded bundle -/

/-- The bundle with its two premises for all time gives the bounded bundle at every `T`: fewer than
a quorum corrupted up to any time gives it up to `T`, and committee sleepiness gives its bounded
form (`committeeSleepinessUntil_of_committeeSleepiness`). Every other field is kept.

The variables:
- `M`: the model; `F`: its facts;
- `P`: the hypotheses; `T`: the time up to which the bounded premises are read.

Read aloud: the hypotheses of the period with the premises for all time give the hypotheses with
the premises bounded at any time `T`. -/
theorem AsyncHyps.toUntil {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F : ℕ}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} (P : AsyncHyps M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F release ΔRedeliver ΔClockAhead ΔClockBehind tW) (T : ℕ) :
    AsyncHypsUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T release ΔRedeliver ΔClockAhead ΔClockBehind := by
  exact
    ⟨P.hSync, P.Sy, P.hSyncF, P.Sy_F, P.hParent, P.hAdvQ T,
      committeeSleepinessUntil_of_committeeSleepiness M S A x _ T P.hSleepK, P.hAnchor, P.hGST, P.hb₀,
      P.hb, P.hb₁, P.hHold, P.ht₀⟩

/-! ## The step of the lock holder's invariant -/

/-- **Kit fact: every lock entry is on a held block.** At every step of every execution, the block
of every lock entry a validator holds is a block of its FG state's tree.

Why: the entry is traced (`lockTracedAfterTick_of_mem`): its block is an ancestor of a block of the frame's
tree at an earlier step, or that block; the tree only grows (`mem_T_mono`) and holds every
ancestor of its blocks (`ancestors_mem_T_of_exec`).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `v`: the validator; `i`: the step.

Read aloud: a validator holds every block it has locked. -/
theorem lock_entry_mem_T_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (v : V) (i : ℕ) :
    ∀ e ∈ (x.st i v).lockEntries, e.B ∈ (x.st i v).tree := by
  -- by induction on the step through `step_cases_lock_saved`: a kept entry is on a block of the
  -- earlier tree, which only grows; an entry the revocation or the update leaves is `v`'s, or on a
  -- block of the tree of `M.fg_to_ac` of the state the tick starts from, which has `v`'s tree
  induction i with
  | zero =>
      intro e he
      rw [(getElem_zero_st M F) x R, F.init.initial_lockEntries] at he
      exact absurd he (Finset.notMem_empty e)
  | succ i ih =>
      intro e he
      have hTs := (mem_T_mono M F) x R E v (Nat.le_succ i)
      rcases (step_cases_lock_saved M F) x R E i v with ⟨-, hsub⟩ | ⟨t, hl, -, -, -, hLR, -⟩ |
          ⟨t, hl, -, -, -, hCU⟩
      · exact hTs (ih e (hsub he))
      · obtain ⟨-, -, hT, -, -, -, -, -, -, -, -, hLE, -⟩ :
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
        · rw [hs0] at hLR
          have he₁ := ((GoldilocksCorrectness.Record.Proofs.Routines.revoke_locks_zero hLR) e).1 he
          exact hTs (ih e (hLE ▸ he₁.1))
        · have h := GoldilocksCorrectness.Record.Proofs.Routines.revoke_locks_entry_mem_tree
            (Nat.one_le_iff_ne_zero.mpr hs0) hLR e he
          rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F), hT] at h
          exact hTs h.1
      · obtain ⟨-, -, hT, -, -, -, -, -, -, -, -, hLE, -⟩ :
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
        rcases ((GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_in_frame F)
            hCU).2.2.1 e he with h | ⟨h, -⟩
        · exact hTs (ih e (hLE ▸ h))
        · rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F), hT] at h
          exact hTs h.1

section Steps

variable {S : Setup V} {A : Activity V}

/-- What a step does to a validator's lock entries, record of the confirmed tip and fast blocks:
it keeps all three; or it is the tick of every awake validator at a time `t` at which the
validator is awake and honest, and either the step leaves the validator's lock entries whose
deadline is after `t` and keeps the other two fields, or `t` is the vote time of its slot, the tick
starts from a node state awake since that slot's duty window started (`AwakeFor`), and the step
leaves the lock entries of the revocation of that slot (`LocksRevoked`, from the node state the
tick starts from) and keeps the other two fields, or `t` is the support cutoff of its slot, the
tick starts from a node state awake for that slot, and the step leaves what the confirmation
update of that slot leaves (`ConfirmationUpdated`).

The landed statement names the answers of the routines `revoke_locks` and `update_confirmation`;
the twin reads the tick's effect through the record's predicates, as
`step_cases_lock_saved` of `Record/Restated/Proofs/Executions/LockSteps.lean` does. A tick at a
duty time from a node not awake for the slot deletes the expired lock entries and keeps the other
fields (`F.tk2.tick_dutyTime_not_awake`): the first case of the tick. No recovery line: the record
has no theorem from the predicates to the routines' answers.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `v`: the validator.

Read aloud: only the validator's own tick changes its locks, record and fast blocks, and only
through the expiry, the revocation and the confirmation update. -/
theorem step_cases_period (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    ((x.st (i + 1) v).lockEntries = (x.st i v).lockEntries ∧
      (x.st (i + 1) v).latestConfirmed = (x.st i v).latestConfirmed ∧
      (x.st (i + 1) v).fastBlocks = (x.st i v).fastBlocks) ∨
    (∃ t : ℕ, x.lbl i = Event.tick v t ∧
      v ∈ A.active i ∧
      (((x.st (i + 1) v).lockEntries = {e ∈ (x.st i v).lockEntries | (t : Int) < e.d} ∧
          (x.st (i + 1) v).latestConfirmed = (x.st i v).latestConfirmed ∧
          (x.st (i + 1) v).fastBlocks = (x.st i v).fastBlocks) ∨
        ((t : Int) = S.C.t_ (S.C.slot t) + S.C.Δ ∧
          AwakeFor M S.C (x.tickInput v t) (S.C.slot t) ∧
          LocksRevoked M S.P (x.tickInput v t) t (S.C.slot t) (x.st (i + 1) v) ∧
          (x.st (i + 1) v).latestConfirmed = (x.st i v).latestConfirmed ∧
          (x.st (i + 1) v).fastBlocks = (x.st i v).fastBlocks) ∨
        ((t : Int) = S.C.t_ (S.C.slot t) + 2 * S.C.Δ ∧
          AwakeFor M S.C (x.tickInput v t) (S.C.slot t) ∧
          ConfirmationUpdated M S.C S.P (x.tickInput v t) t (S.C.slot t)
            (x.st (i + 1) v)))) := by
  rcases (step_cases M F) x R E i v with h | ⟨t, n', sent, hl, hmem, hok, h, -⟩ | ⟨sm, -, -, h⟩ |
      ⟨⟨tRw, keepw, hlw⟩, -, h⟩
  · rw [h]
    exact Or.inl ⟨rfl, rfl, rfl⟩
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hLE, hFB, hLC, -⟩ :
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
    refine Or.inr ⟨t, hl, hmem, ?_⟩
    -- at a duty time from a node state awake for the slot, the revocation or the update; at a duty
    -- time from one not awake for it (`F.tk2.tick_dutyTime_not_awake`), and away from the duty
    -- times (`F.tk.tick_lock_entries`), the expired entries deleted and the rest kept
    by_cases hv : (t : Int) = S.C.t_ (S.C.slot t) + S.C.Δ
    · have hc : (t : Int) ≠ S.C.t_ (S.C.slot t) + 2 * S.C.Δ :=
        GoldilocksCorrectness.Proofs.Routines.voteTime_ne_cutoff hv
      obtain ⟨-, hfb, hlc⟩ := F.tk.tick_keeps_confirmation_off_cutoff S.C S.P S.X _ _ n' sent hok hc
      by_cases hA : AwakeFor M S.C (x.tickInput v t) (S.C.slot t)
      · exact Or.inr (Or.inl ⟨hv, hA, F.tk2.tick_voteTime_locks S.C S.P S.X _ _ n' sent hok hInv hv hA,
          hlc.trans hLC, hfb.trans hFB⟩)
      · obtain ⟨h1, -, h3, h4⟩ :=
          F.tk2.tick_dutyTime_not_awake S.C S.P S.X _ _ n' sent hok (Or.inl hv) hA
        exact Or.inl ⟨by rw [h1, hLE], h4.trans hLC, h3.trans hFB⟩
    · by_cases hc : (t : Int) = S.C.t_ (S.C.slot t) + 2 * S.C.Δ
      · by_cases hA : AwakeFor M S.C (x.tickInput v t) (S.C.slot t)
        · exact Or.inr (Or.inr ⟨hc, hA,
            F.tk2.tick_supportCutoff_confirmation S.C S.P S.X _ _ n' sent hok hInv hc hA⟩)
        · obtain ⟨h1, -, h3, h4⟩ :=
            F.tk2.tick_dutyTime_not_awake S.C S.P S.X _ _ n' sent hok (Or.inr hc) hA
          exact Or.inl ⟨by rw [h1, hLE], h4.trans hLC, h3.trans hFB⟩
      · obtain ⟨-, hfb, hlc⟩ := F.tk.tick_keeps_confirmation_off_cutoff S.C S.P S.X _ _ n' sent hok hc
        rcases F.tk.tick_lock_entries S.C S.P S.X _ _ n' sent hok with h1 | h1 | h1
        · exact Or.inl ⟨by rw [h1, hLE], hlc.trans hLC, hfb.trans hFB⟩
        · exact absurd h1 hv
        · exact absurd h1 hc
  · rw [h]
    obtain ⟨-, h2, h3, h4, -⟩ := F.rcv.receive_keeps_confirmation S.C S.P S.X (x.st i v) sm.msg
    exact Or.inl ⟨h3, h4, h2⟩
  · -- a wake keeps the locks, the record of the confirmed tip and the fast blocks
    rw [h tRw keepw hlw]
    exact Or.inl ⟨(F.wk.wake_readers _ _).2.2.2.2.2.2.2.2.2.2.2.1,
      (F.wk.wake_readers _ _).2.2.2.2.2.2.2.2.2.2.2.2.2.1, (F.wk.wake_readers _ _).2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- **Kit fact: no lock entry is on the genesis block.** At every step of every execution, no lock
entry a validator holds is on the genesis block.

Why: by induction on the step, through `step_cases_lock_saved`: the initial AC state holds no
entry; a step keeps a subset of the entries, or revokes (`revoke_locks_entry_ne_genesis`), or runs
the confirmation update, which adds only an entry on a block of its path
(`update_confirmation_in_frame`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `v`: the validator; `i`: the step.

Read aloud: nobody locks the genesis block. -/
theorem lock_entry_ne_genesis_of_exec (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (v : V) (i : ℕ) :
    ∀ e ∈ (x.st i v).lockEntries, e.B ≠ Block.genesis := by
  induction i with
  | zero =>
      intro e he
      rw [(getElem_zero_st M F) x R, F.init.initial_lockEntries] at he
      exact absurd he (Finset.notMem_empty e)
  | succ i ih =>
      intro e he
      rcases (step_cases_lock_saved M F) x R E i v with ⟨-, hsub⟩ | ⟨t, hl, -, -, -, hLR, -⟩ |
          ⟨t, hl, -, -, -, hCU⟩
      · exact ih e (hsub he)
      · -- the revocation, from the node state the tick starts from, whose lock entries are `v`'s
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hLE, -⟩ :
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
        · rw [hs0] at hLR
          have he₁ := ((GoldilocksCorrectness.Record.Proofs.Routines.revoke_locks_zero hLR) e).1 he
          exact ih e (hLE ▸ he₁.1)
        · exact GoldilocksCorrectness.Record.Proofs.Routines.revoke_locks_entry_ne_genesis
            (Nat.one_le_iff_ne_zero.mpr hs0) hLR e he
      · -- the update keeps `v`'s entries or adds one on a non-genesis block
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hLE, -⟩ :
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
        rcases ((GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_in_frame F)
            hCU).2.2.1 e he with h | ⟨-, h⟩
        · exact ih e (hLE ▸ h)
        · exact h

end Steps

end GoldilocksCorrectness.Record.Proofs.Executions

