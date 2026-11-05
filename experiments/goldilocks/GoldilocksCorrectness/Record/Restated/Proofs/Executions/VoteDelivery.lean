module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACStore
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# VoteDelivery, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/VoteDelivery.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: a vote of an honest validator held by any
validator was put on the wire by its own tick, and one vote per slot of an honest validator. The
delivery of a Goldfish vote into a receiver's pool is read at the receiver's tick
(`pool_vote_at_tick_of_send`, `ReadingPoints.lean`). The page's routine-level
theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slot_mono slot_natCast)

open GoldilocksCorrectness.Proofs.Routines (fun_getElem)

open GoldilocksCorrectness.Proofs.Routines (receive_gfVote_cases)

open GoldilocksCorrectness.Proofs.Routines (on_ac_message_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open Goldilocks
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The admission of a Goldfish vote -/

section Admission

end Admission

/-! ## Along an execution -/

section Delivery

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks.Sts (Setup)

variable [RootOrder] {S : Setup V} {A : Activity V}

/-- A vote of a validator `u` that a validator's pool holds before `t`, with `u` honest at `t`,
was put on the wire by `u`'s own tick at some step.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `t`: the time; `w`: the validator whose pool it is; `u`: the voter;
  `s`: the slot; `vote`: the vote.

Read aloud: a vote of an honest validator held by any validator was put on the wire by its voter's
tick. -/
theorem pool_vote_tick_send {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- corruption is permanent
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner M A x)
    {t : ℕ} {w u : V} {s : Slot} {vote : GoldfishVote V}
    -- `u` is honest at `t`
    (hu : u ∉ A.corruptedAtTime x t)
    -- `w`'s pool of slot `s` before `t` holds `vote`, a vote of `u`
    (hv : vote ∈ M.votesHeldSet (x.stateBefore t w) s) (hi : vote.val_index = u) :
    ∃ k t' : ℕ, x.lbl k = Event.tick u t' ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (k + 1) - x.sent k := by
  subst hi
  obtain ⟨i, hi', sm, hsm, hcarry⟩ := (pool_vote_sent_before M F R) E hv
  have hit : x.time i ≤ t :=
    le_of_lt (lt_of_le_of_lt ((time_le_succ M) x R i) (((lt_stepBefore_iff M) x R E).1 hi'))
  have hhon : vote.val_index ∉ A.corrupted i := (not_mem_corrupted_of_le_time M) x R E hu hit
  obtain ⟨k, t', -, hlk, hsk⟩ := hOwner i sm vote hsm hcarry hhon
  exact ⟨k, t', hlk, hsk⟩

/-- One vote per slot of an honest validator: two votes of the validator `u`, honest at `t`, that
a validator's pool of slot `s` holds before `t` are the same vote.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `t`: the time; `w`: the validator whose pool it is; `u`: the voter;
  `s`: the slot; `v₁`, `v₂`: the two votes.

Read aloud: a validator holds at most one vote per slot of each honest validator. -/
theorem unique_vote_of_owner {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- corruption is permanent
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner M A x)
    {t : ℕ} {w u : V} {s : Slot} {v₁ v₂ : GoldfishVote V}
    -- `u` is honest at `t`
    (hu : u ∉ A.corruptedAtTime x t)
    -- `w`'s pool of slot `s` before `t` holds `v₁` and `v₂`, both votes of `u`
    (h₁ : v₁ ∈ M.votesHeldSet (x.stateBefore t w) s) (h₂ : v₂ ∈ M.votesHeldSet (x.stateBefore t w) s)
    (hi₁ : v₁.val_index = u) (hi₂ : v₂.val_index = u) :
    v₁ = v₂ := by
  obtain ⟨k₁, t₁, hl₁, hs₁⟩ := (pool_vote_tick_send M F R) E hOwner hu h₁ hi₁
  obtain ⟨k₂, t₂, hl₂, hs₂⟩ := (pool_vote_tick_send M F R) E hOwner hu h₂ hi₂
  refine (honest_vote_sent_once M F R E) hl₁ hl₂ hs₁ hs₂ ?_
  rw [(GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_stateBefore M F) S A x R E t w s v₁ h₁, (GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_stateBefore M F) S A x R E t w s v₂ h₂]

end Delivery

end GoldilocksCorrectness.Record.Proofs.Executions

