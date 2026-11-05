module
public import GoldilocksCorrectness.Record.Restated.Proofs.View.Bridges
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedTopStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.FinalityLivenessStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.View.Bridges
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HealedFinalityLiveness, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/HealedFinalityLiveness.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 98 (finality liveness
after healing) and the two facts its composition reads (the proposer of an honest round opening slot
is an honest active validator of the slot before it, and proposes). The page's routine-level
theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart proposalWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono dutyWindowStart_succ_le_slotStart
  one_le_Δ proposalWindowStart_eq slotStart_eq slotStart_mono slot_after_healed_round
  slot_lt_of_lt_slotStart slot_mono slot_mono_int supportCutoff_eq supportCutoff_mono voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (slot_lt_of_ancestorEq_of_treeClosed)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Proofs.Executions (mem_awakeThroughout_of_forall)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (OpeningsOutsideWaitsAndWindows Vocab.goldilocks
  acObject fgObject healFrontSlots)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_compatible ancestorEq_antisymm)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-- **Kit fact, the proposer of an honest round opening slot is an honest active validator of the
slot before it.** Its proposal window starts at the duty window of the slot before
(`proposal_window_start_eq`), and the reader of `HonestOpenerAt` holds up to its tick to the support cutoff of
slot `q + 2`, strictly inside the reader's window with the two clock bounds' margins
(`mem_activeThroughoutToTick_of_inside`); its honesty reaches the update of its own slot.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `A`: the activity; `x`: the execution; `R`: the run's facts; `E`: the environment's facts;
  `hSkew`: the two clock bounds together are less than one delay; `q`: the slot is `q + 2`.

Read aloud: the proposer of an honest round opening slot is an honest active validator of the slot
before it. -/
theorem opener_mem_honestActiveAt_prev (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : ΔClockAhead + ΔClockBehind < Δ S)
    (q : ℕ) (hOpener : HonestOpenerAt M S A x (q + 2)) :
    S.P.proposer (q + 2) ∈ honestActiveAt M S A x (q + 1) := by
  obtain ⟨hr, hh⟩ := hOpener
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  rw [GoldilocksCorrectness.Proofs.Routines.proposal_window_start_eq S q] at hr
  have hd : ((duty_window_start S.C (q + 1) : ℤ) : ℝ) =
      4 * ((Δ S : ℝ) * (q : ℝ)) + 5 * (Δ S : ℝ) - 4 * ((Δ S : ℝ) * (S.C.k : ℝ)) := by
    rw [duty_window_start_real S (q + 1)]; push_cast; ring
  have h10 : ((M.supportCutoff S.C (q + 1 + 1) : ℕ) : ℝ) = 4 * ((Δ S : ℝ) * (q : ℝ)) + 10 * (Δ S : ℝ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (q + 1 + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 1 + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (q + 1 + 1)]
    push_cast; ring
  have h14 : ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℝ) = 4 * ((Δ S : ℝ) * (q : ℝ)) + 14 * (Δ S : ℝ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (q + 2 + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 2 + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (q + 2 + 1)]
    push_cast; ring
  have hk0 : (0 : ℝ) ≤ (Δ S : ℝ) * (S.C.k : ℝ) := by positivity
  have hc1 : 1 ≤ M.supportCutoff S.C (q + 1 + 1) :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S (q + 1)).2
  have hm := (mem_activeThroughoutToTick_of_inside M F) R E hr hc1 (by linarith) (by linarith)
  -- honest through the support cutoff of slot `q + 3`, `4 Δ S` after that of slot `q + 2`, so at every
  -- honest tick to the latter (`ΔClockBehind < Δ S`)
  exact Finset.mem_sdiff.2 ⟨Activity.mem_awakeThroughoutToTick_of_mem_activeThroughoutToTick hm,
    not_mem_corruptedAtTime_union_ticks_of_le E (by rw [h10, h14]; linarith)
      (fun h => hh (Finset.mem_union_left _ (Finset.mem_union_left _ h)))⟩

/-- **Kit fact, the proposer of an honest round opening slot proposes.** For a slot `s ≥ 2` with
`HonestOpenerAt M S A x s`, the proposer's tick at the start of `s` puts some block on the wire: the reader of
`HonestOpenerAt` holds up to its tick to the slot's start, strictly inside its window with the two clock bounds'
margins (`mem_activeThroughoutToTick_of_inside`), and `honest_proposer_proposesJ` reads it there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `A`: the activity; `x`: the execution; `R`: the run's facts; `s`: the slot; `E`: the
  environment's facts; `hSkew`: the two clock bounds together are less than one delay.

Read aloud: the proposer of an honest round opening slot proposes a block at the start of its slot.
-/
theorem proposal_of_opener (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : ΔClockAhead + ΔClockBehind < Δ S)
    (hs : 2 ≤ s) (hOpener : HonestOpenerAt M S A x s) : ∃ B : Block V,
      ProposalAt M S x s B := by
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  obtain ⟨hr, -⟩ := hOpener
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hd : ((proposal_window_start S.C (q + 2) : ℤ) : ℝ) =
      4 * ((Δ S : ℝ) * (q : ℝ)) + 5 * (Δ S : ℝ) - 4 * ((Δ S : ℝ) * (S.C.k : ℝ)) := by
    rw [GoldilocksCorrectness.Proofs.Routines.proposal_window_start_eq S q, duty_window_start_real S (q + 1)]
    push_cast; ring
  have hss : ((M.slotStart S.C (q + 2) : ℕ) : ℝ) = 4 * ((Δ S : ℝ) * (q : ℝ)) + 8 * (Δ S : ℝ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (q + 2)]
    push_cast; ring
  have hsc : ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℝ) = 4 * ((Δ S : ℝ) * (q : ℝ)) + 14 * (Δ S : ℝ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (q + 2 + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 2 + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (q + 2 + 1)]
    push_cast; ring
  have hk0 : (0 : ℝ) ≤ (Δ S : ℝ) * (S.C.k : ℝ) := by positivity
  have hq0 : (0 : ℝ) ≤ (Δ S : ℝ) * (q : ℝ) := by positivity
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hc1 : 1 ≤ M.slotStart S.C (q + 2) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (q + 2)]
    have := Nat.mul_le_mul (show 4 ≤ 4 * Δ S by omega) (show 1 ≤ q + 2 by omega)
    omega
  have hm := (mem_activeThroughoutToTick_of_inside M F) R E hr hc1 (by rw [hd, hss]; linarith)
    (by rw [hss, hsc]; linarith)
  obtain ⟨i, B, hl, hsent⟩ := (honest_proposer_proposesJ M F U) S A x R q E hm
  exact ⟨B, i, hl, hsent⟩

/-- **Kit fact, the per-tick rows at an honest round opening slot Lemma 98 reads.** For
an honest round opening slot `s` at or after `tAwakeEnd` whose next support cutoff is at most `t`, every
updater of `s` ticks to that cutoff at a real time at most `t` (`hLastTick`, the updater's own tick to
the cutoff is one such tick); so roots naming blocks up to `t` and fewer than a quorum in the adversary set
up to `t` hold up to each updater's tick, the rows `hRootsU` and `hAdvQU` the Lemma 94, 97 and 107 group
takes (T-RC86-1).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `A`: the activity; `x`: the execution; `tAwakeEnd`: the end of the healing phase; `t`: the
  time up to which the execution is read; `s`: the honest round opening slot.

Read aloud: at an honest round opening slot after the phase whose next support cutoff is at most `t`,
every updater's tick to that cutoff is at a real time at most `t`, and roots and the quorum bound hold up
to it. -/
theorem opening_tick_rows_of_lastTick (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (tAwakeEnd t : ℕ)
    (hLastTick : ∀ (s k : ℕ) (u : V) (c : ℕ), tAwakeEnd ≤ M.slotStart S.C s → HonestOpenerAt M S A x s →
      M.supportCutoff S.C (s + 1) ≤ t → x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s + 1) →
      (x.time k : ℝ) ≤ t)
    (hRootsT : RootsNameBlocksUntil M A x t) (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) t)
    (s : ℕ) (hs : tAwakeEnd ≤ M.slotStart S.C s) (hO : HonestOpenerAt M S A x s)
    (hc : M.supportCutoff S.C (s + 1) ≤ t) :
    (∀ v ∈ updaterAt M S A x s, (x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) : ℝ) ≤ t) ∧
    (∀ v ∈ updaterAt M S A x s,
      RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1))))) ∧
    (∀ v ∈ updaterAt M S A x s,
      A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1))))) := by
  have hle : ∀ v ∈ updaterAt M S A x s, (x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) : ℝ) ≤ t := by
    intro v hv
    obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hv
    exact hLastTick s _ v _ hs hO hc (x.lbl_tickStep ⟨k', hk'⟩) le_rfl
  exact ⟨hle, fun v hv => (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (hle v hv) hRootsT,
    fun v hv => hAdvQ.mono (hle v hv)⟩

/-- **Kit fact, a finalized block held before the start of a slot has a slot at most that slot.** For every
validator `u`, one in the adversary set included, and every step `i'` at a real time before the start of slot `s`,
the finalized block of `u`'s node state at `i'` has a slot at most `s`. Used by Lemma 98's last clause.

Why: the clock-free part of Lemma 11 makes the finalized block the
justified block or an ancestor of it, the justified block a block of the tree, and the tree closed under parents with
slots decreasing; a block of the tree other than genesis was put on the wire by `u` at an earlier step `i''`
(`tree_block_relayed`), with a slot at most the slot of `u`'s clock after `i''`; that clock is at most the real time
plus `ΔClockAhead` (`clock_le_time_add_ahead`), less than the start of slot `s + 1` since `ΔClockAhead < Δ S`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, its run facts; `E`: the environment's facts; `hSkew`: the
  two clock bounds together are less than one delay; `s`: the slot; `i'`: the step; `u`: the validator.

Read aloud: no validator holds, before a slot starts, a finalized block of a later slot. -/
theorem finalized_slot_le_of_time_lt_slotStart (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : ΔClockAhead + ΔClockBehind < Δ S) (s i' : ℕ) (u : V)
    (hi' : x.time i' < M.slotStart S.C s) :
    (x.st i' u).finalized.slot ≤ s := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hTimes : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s, Nat.mul_add, Nat.mul_one]
  have hCore := ((lem11_node_invariantCore_of_run M F) S x R i' u).1
  have hTCu := F.nd.nodeInvCore_treeClosed hCore
  have hFJ : (x.st i' u).finalized.AncestorEq (x.st i' u).justified := F.nd.nodeInvCore_finalizedAncestorJustified hCore
  have hJT : (x.st i' u).justified ∈ (x.st i' u).tree := F.nd.nodeInvCore_justifiedInTree hCore
  have hFJs : (x.st i' u).finalized.slot ≤ (x.st i' u).justified.slot := by
    by_cases he : (x.st i' u).finalized = (x.st i' u).justified
    · rw [he]
    · exact ((slot_lt_of_ancestorEq_of_treeClosed_node M F) hTCu hJT hFJ he).le
  have hJs : (x.st i' u).justified.slot ≤ s := by
    by_cases hg : (x.st i' u).justified = Block.genesis
    · rw [hg]; simp only [Block.slot]; omega_nat
    obtain ⟨i'', hi'', -, -, hsl⟩ := (tree_block_relayed M F) x R E hJT hg
    have hc := (clock_le_time_add_ahead M F) x R E (i'' + 1) u
    have ht1 := (time_mono M) x R (Nat.succ_le_of_lt hi'')
    have hS := hTimes
    have h1 : 1 ≤ M.slotStart S.C (s + 1) := by omega
    have hst : ((M.slotStart S.C (s + 1) : ℕ) : ℝ) = (M.slotStart S.C s : ℝ) + 4 * (Δ S : ℝ) := by
      rw [hS]; push_cast; ring
    have hlt1 : (((x.st (i'' + 1) u).t : ℤ) : ℝ) < (((M.slotStart S.C (s + 1) : ℕ) : ℤ) : ℝ) := by
      rw [Int.cast_natCast]
      refine lt_of_le_of_lt hc (max_lt (by positivity) ?_)
      linarith
    have hlt2 := Int.cast_lt.1 hlt1
    have hcle : (x.st (i'' + 1) u).t ≤ ((M.slotStart S.C (s + 1) - 1 : ℕ) : ℤ) := by
      have h4 : ((M.slotStart S.C (s + 1) - 1 : ℕ) : ℤ) = ((M.slotStart S.C (s + 1) : ℕ) : ℤ) - 1 := by omega
      rw [h4]
      exact Int.le_sub_one_of_lt hlt2
    have h2 := slot_mono_int S hcle
    have h3 := slot_lt_of_lt_slotStart S (s := s + 1) (t := M.slotStart S.C (s + 1) - 1) (by
      have h5 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1)
      have h6 := slotStart_eq S (s + 1)
      omega)
    exact Nat.lt_succ_iff.1 (lt_of_le_of_lt (le_trans hsl h2) h3)
  exact le_trans hFJs hJs

/-- **Kit fact, Lemma 98's window part.** Lemma 98's hypotheses, with roots naming blocks up
to `t`, fewer than a quorum in the adversary set up to `t`, the facts after the hand-over up to `t`
(`healed_handover_facts_until`'s third disjunct, its rows named) and Lemma 90's inclusion up to `t`: every honest
proposal followed by four honest round opening slots with quorums at the first three, and the window's update by
`t`, is finalized up to `t` by everyone awake for a delay after the fourth. The part of Lemma 98's proof after its
calls of the facts after the hand-over and of Lemma 90, stated on its own so that each declaration stays within the
heartbeat budget.

Why: as `lem98_healed_finality_liveness`'s docstring, with the rows Lemma 97 reads after the window from the hand-over
facts' chain clause and `hTicksBy` (`confirmationsChainBefore_of_handover_le`, Lemma 81 at each slot), the caches at
each step from the hand-over's real time from its row on `x.st j u`, and the tick clause of `hAfter`
from its third conjunct.

The variables: as Lemma 98's; `s₀`, `i₂`, `B₀`: the healed slot, the hand-over step and the healed block.

Read aloud: once the hand-over facts and Lemma 90's inclusion hold up to `t`, every honest proposal followed by the
window is finalized up to `t`. -/
theorem lem98_window_of_handover (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (rs : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    (hParent : ParentHeldAtDelivery M x)
    -- the time up to which the execution is read, after the phase
    (t : ℕ)
    -- `t` is not inside any slot's update: at every slot whose update is at most `t`, or to whose update some
    -- validator ticked at a real time at most `t`, every tick to a clock value at most that update is at a real
    -- time at most `t` (; the sentence of's `hLastTick` at every slot, which it replaces)
    (hTicksBy : TicksToUpdatesBy M S x t)
    -- committee sleepiness from `anchorCW S tGAT`, for the slots whose update is at most `t`
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) t)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S rs m)
    (hParam : (Δ_F S : ℝ) + Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * (S.C.k + 1))
    (hDelF : ∀ r' : ℕ, tAwakeEnd ≤ M.slotStart S.C (r' * S.C.R) → HonestOpenerAt M S A x ((r' + 1) * S.C.R) →
      ∀ u ∈ honestActiveAt M S A x (r' * S.C.R), ∀ (j t' : ℕ) (a : Attestation V), x.lbl j = Event.tick u t' →
      t' ≤ M.supportCutoff S.C (r' * S.C.R + 1) →
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j →
      M.justifiedHeight (x.stateBefore (M.proposalWindowStart S.C ((r' + 1) * S.C.R)) u) ≤ a.h →
      (∃ d : ℕ, x.lbl d = Event.deliver (S.P.proposer ((r' + 1) * S.C.R)) ⟨u, NamedObject.attest a⟩ ∧
      d < x.tickStep (S.P.proposer ((r' + 1) * S.C.R)) (M.slotStart S.C ((r' + 1) * S.C.R))) ∨
      a ∈ (x.stateBefore (M.proposalWindowStart S.C ((r' + 1) * S.C.R)) (S.P.proposer ((r' + 1) * S.C.R))).attestationsHeld)
    -- at every honest round opening slot after the phase, no block an honest active member of the round holds when it
    -- ticks to the round's action time includes an attestation put on the wire at a tick to that action time
    --
    (hTickInputs : ∀ r' : ℕ, tAwakeEnd ≤ M.slotStart S.C (r' * S.C.R) → HonestOpenerAt M S A x (r' * S.C.R) →
      ∀ v ∈ honestActiveAt M S A x (r' * S.C.R), ∀ Z ∈ (x.tickInput v (M.supportCutoff S.C (r' * S.C.R + 1))).tree,
      ∀ a ∈ Z.attestations, ∀ (j : ℕ) (w : V), x.lbl j = Event.tick w (M.supportCutoff S.C (r' * S.C.R + 1)) →
      (⟨w, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x.sent (j + 1) - x.sent j)
    (hHold : ∀ s' : ℕ, tAwakeEnd ≤ M.slotStart S.C (s' + 1) → M.supportCutoff S.C (s' + 1) ≤ t →
      ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- every honest committee member of every slot starting at or after `tAwakeEnd` whose update is at most `t` is active
    -- from its duty window's start through the sync delay after that update; at every slot at or after `tAwakeEnd` with an
    -- honest opener whose update is at most `t`, its proposer through the sync delay after the slot's update
    --
    (hHoldC : ∀ σ' : ℕ, tAwakeEnd ≤ M.slotStart S.C σ' → M.supportCutoff S.C (σ' + 1) ≤ t →
      ∀ u ∈ honestActiveAt M S A x σ', u ∈ S.P.committee σ' →
      u ∈ A.activeThroughout x ((M.dutyWindowStart S.C σ' : ℕ) : ℝ) (((M.supportCutoff S.C (σ' + 1) : ℕ) : ℝ) + Δs))
    (hHoldP : ∀ s : ℕ, tAwakeEnd ≤ M.slotStart S.C s → M.supportCutoff S.C (s + 1) ≤ t → HonestOpenerAt M S A x s →
      S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + Δs))
    -- the facts the main body obtains: roots up to `t`, the quorum bound, the hand-over facts and Lemma 90's inclusion
    (hRootsT : RootsNameBlocksUntil M A x t)
    (hAdvQ' : A.AdversaryFewerThanQuorumUntil x (quorum V) t)
    (s₀ i₂ : ℕ) (B₀ : Block V)
    (hsc : M.supportCutoff S.C (s₀ + 1) < x.time i₂)
    (hafter : ∀ s : ℕ, tAwakeEnd ≤ M.slotStart S.C s → x.time i₂ < M.slotStart S.C s ∧
      ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.slotStart S.C s) → x.time i₂ < x.time k)
    (hAnc : anchorCW S tGAT ≤ M.slotStart S.C (s₀ + 1)) (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt M S A x s₀,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1))
      (M.chainStateOf S.C B₀).h)
    (hCachesAt : ∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ t → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.st j u))
    (hVF : ∀ s : ℕ, s₀ < s → M.supportCutoff S.C (s + 1) ≤ t →
      ∀ w ∈ honestActiveAt M S A x s, VoterFrameOnChainAt M S A x s₀ s w)
    (hUF : ∀ s : ℕ, s₀ < s → ∀ v ∈ updaterAt M S A x s,
      x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) ≤ t → UpdaterFinalizedOnChainAt M S A x s₀ s v)
    (hChain : ∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
      x.time k ≤ t → ConfirmationsChainBefore M S A x s₀ σ ∧
      ∀ v ∈ updaterAt M S A x σ, x.time (x.tickStep v (M.supportCutoff S.C (σ + 1))) ≤ t →
      ∀ C' : Block V, (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' →
      (∀ C : Block V, OnHonestChainBefore M S A x s₀ σ C → C.AncestorEq C') ∧
      (s₀ ≤ σ → ∀ v' ∈ updaterAt M S A x σ, x.time (x.tickStep v' (M.supportCutoff S.C (σ + 1))) ≤ t →
      ∀ C'' : Block V, (x.tickOutput v' (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C'' →
      C'.compatible C'' = true))
    (hIncl : ConfirmedIncludedBetween M S A x tAwakeEnd t) :
    FinalityIncludedBetween M S A x Δs tAwakeEnd t := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hR := S.C.R_ge_two
  have hcm : ∀ a b : ℕ, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun a b h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  have hsle : ∀ n n' : ℕ, n ≤ n' → M.slotStart S.C n ≤ M.slotStart S.C n' := fun n n' h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h
  have hTimes : ∀ n : ℕ, M.voteTime S.C n = M.slotStart S.C n + Δ S ∧
      M.supportCutoff S.C n = M.slotStart S.C n + 2 * Δ S ∧
      M.slotStart S.C (n + 1) = M.slotStart S.C n + 4 * Δ S := fun n => by
    have h1 : M.voteTime S.C n = M.slotStart S.C n + Δ S :=
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S n
    have h2 : M.supportCutoff S.C n = M.voteTime S.C n + Δ S :=
      (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S n
    have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S n
    have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (n + 1)
    refine ⟨h1, by omega, ?_⟩
    rw [h4, h3, Nat.mul_add, Nat.mul_one]
  have hOwner : VotesCastByOwner M A x := (votesCastByOwner_of_unforgeability M F) S A x R E
  have hGSTs : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀ :=
    gst_sync_of_anchor M F U S hGST hΔs hAnc (by linarith)
  --'s sentence at the honest round opening slots, from `hTicksBy`
  have hLastTick : ∀ (s k : ℕ) (u : V) (c : ℕ), tAwakeEnd ≤ M.slotStart S.C s → HonestOpenerAt M S A x s →
      M.supportCutoff S.C (s + 1) ≤ t → x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s + 1) →
      (x.time k : ℝ) ≤ t := fun s k u c _ _ hc hk hcc => hTicksBy s k u c (Or.inl hc) hk hcc
  rw [(GoldilocksCorrectness.Record.Proofs.View.confirmedIncludedBetween_unfold M x)] at hIncl
  rw [(GoldilocksCorrectness.Record.Proofs.View.finalityIncludedBetween_unfold M x)]
  set H := (M.chainStateOf S.C B₀).h with hHdef
  have hParamN : Δ_F S + Δ S ≤ 4 * Δ S * (S.C.k + 1) := by
    have : ((Δ_F S + Δ S : ℕ) : ℝ) ≤ ((4 * Δ S * (S.C.k + 1) : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hAnc₂ : anchorCW S tGAT ≤ x.time i₂ := by
    have h1 : M.slotStart S.C (s₀ + 1) ≤ M.supportCutoff S.C (s₀ + 1) := by
      have := hTimes (s₀ + 1); omega
    have : ((anchorCW S tGAT : ℕ) : ℝ) ≤ (M.supportCutoff S.C (s₀ + 1) : ℝ) := by exact_mod_cast le_trans hAnc h1
    linarith
  have h8m := (GoldilocksCorrectness.Record.Statements.Executions.eight_le_m_of_openings M F) S rs m hOpenings
  have hδt : 2 * S.C.R ≤ S.C.δt + 1 :=
    (GoldilocksCorrectness.Record.Statements.Executions.two_R_le_δt_succ_of_seq M F) S A x rs m _ _ hSeq (by omega)
  intro s r hs hop hsr hwin hcut
  have hx2s : x.time i₂ < M.slotStart S.C s := (hafter s hs).1
  -- the window's openers and quorums
  obtain ⟨hOp, hQ⟩ := hwin
  have hO0 : HonestOpenerAt M S A x (r * S.C.R) := by simpa using hOp 0 (by omega)
  have hO1 : HonestOpenerAt M S A x ((r + 1) * S.C.R) := hOp 1 (by omega)
  have hO2 : HonestOpenerAt M S A x ((r + 2) * S.C.R) := hOp 2 (by omega)
  have hO3 : HonestOpenerAt M S A x ((r + 3) * S.C.R) := hOp 3 (by omega)
  have hQ0 : QuorumActiveAt M S A x (r * S.C.R) := by simpa using hQ 0 (by omega)
  have hQ1 : QuorumActiveAt M S A x ((r + 1) * S.C.R) := hQ 1 (by omega)
  have hQ2 : QuorumActiveAt M S A x ((r + 2) * S.C.R) := hQ 2 (by omega)
  have hm : ∀ i : ℕ, (r + i) * S.C.R = r * S.C.R + i * S.C.R := fun i => Nat.add_mul r i S.C.R
  have hm1 := hm 1
  have hm2 := hm 2
  have hm3 := hm 3
  have hs2 : 2 ≤ s := by
    obtain ⟨hs2, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.slot_after_healed_round M.toSlotLayout F.sched) S s₀ s
      (by have : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) < M.slotStart S.C s := lt_trans hsc hx2s
          exact_mod_cast this)
    omega
  have hrR : 2 ≤ r * S.C.R := by omega
  -- the window's condition and the times inside it
  have hcutle : ∀ n : ℕ, n ≤ (r + 3) * S.C.R + 1 → M.supportCutoff S.C n ≤ t := fun n hn =>
    le_trans (hcm _ _ hn) hcut
  have hvle : ∀ n : ℕ, n ≤ (r + 3) * S.C.R + 1 → M.voteTime S.C n ≤ M.supportCutoff S.C n := fun n _ => by
    have := hTimes n; omega
  have hEnd : ∀ r' : ℕ, r ≤ r' → tAwakeEnd ≤ M.slotStart S.C (r' * S.C.R) := fun r' hr' =>
    le_trans hs (hsle _ _ (le_trans hsr (Nat.mul_le_mul_right _ hr')))
  have hEnd3 := hEnd (r + 3) (by omega)
  -- every tick to a clock value at most the update of slot `(r + 3) * R` is at a real time at most `t`
  have hTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C ((r + 3) * S.C.R + 1) →
      (x.time k : ℝ) ≤ t := fun k u c hk hc => hLastTick _ k u c hEnd3 hO3 hcut hk hc
  have hRootsTickW : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c →
      c ≤ M.supportCutoff S.C ((r + 3) * S.C.R + 1) → RootsNameBlocksUntil M A x (x.time k) := fun k u c hk hc =>
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (hTick k u c hk hc) hRootsT
  have hRootsAt : ∀ n : ℕ, n ≤ t → RootsNameBlocksUntil M A x n := fun n hn =>
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by exact_mod_cast hn) hRootsT
  -- an updater's tick to the support cutoff of the next slot, inside the window, is at a real time at most `t`
  have hUpdTick : ∀ σ : ℕ, σ ≤ (r + 3) * S.C.R → ∀ v ∈ updaterAt M S A x σ,
      x.time (x.tickStep v (M.supportCutoff S.C (σ + 1))) ≤ t := fun σ hσ v hv => by
    obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hv
    exact hTick _ v _ (x.lbl_tickStep ⟨k', hk'⟩) (hcm _ _ (by omega))
  -- the confirmations chain before the slot after every slot whose update is at most `t`
  have hG2c : ∀ σ : ℕ, M.supportCutoff S.C (σ + 1) ≤ t → ConfirmationsChainBefore M S A x s₀ (σ + 1) :=
    (confirmationsChainBefore_of_handover_le M F) S x E s₀ t hChain hTicksBy
  -- the chain invariant and the lock invariant at every slot after `s₀` whose update is at most `t`
  -- (`lem81_inv_before`, the updaters' ticks by `t` from `hTicksBy`)
  have hInvT : ∀ s' : ℕ, s₀ < s' → M.supportCutoff S.C (s' + 1) ≤ t →
      ChainInvFor M S A x (honestActiveAt M S A x s') (OnHonestChainBefore M S A x s₀ s') s' ∧
      ∀ u ∈ honestActiveAt M S A x s', LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' u := by
    intro s' h₁ hst
    exact (lem81_inv_before M F U) S A x R GST s₀ (anchorCW S tGAT) (s' + 1) B₀ E hNet hSkew hRedeliver Sy hΔs
      (hRootsAt _ (by rw [Nat.add_sub_cancel]; exact le_trans (hcm _ _ (Nat.le_succ s')) hst))
      (fun k u c hk hc => (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
        (hTicksBy s' k u c (Or.inl hst) hk (le_trans (by rwa [Nat.add_sub_cancel] at hc) (hcm _ _ (Nat.le_succ s'))))
        hRootsT)
      hParent hOwner hGSTs (hCommittees.mono M hst) hAnc hB₀slot hBase hBaseSaved
      (fun s'' h₃ h₄ => hVF s'' h₃ (le_trans (hcm _ _ (by omega)) hst))
      (fun s'' h₃ h₄ v hv => hUF s'' h₃ v hv (by
        obtain ⟨K, hK, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
        exact hTicksBy s' _ v _ (Or.inl hst) (x.lbl_tickStep ⟨K, hK⟩) (hcm _ _ (by omega))))
      s' h₁ (Nat.lt_succ_self s')
  -- the caches on the state at each step from the hand-over's real time
  have hCachesLe : ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j → (x.time j : ℝ) ≤ t → w ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j w) := hCachesAt
  have hCachesTo : ∀ c : ℕ, c ≤ t → ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j → x.time j ≤ c →
      w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w) := fun c hc j w h₁ h₂ h₃ =>
    hCachesLe j w h₁ (le_trans h₂ (by exact_mod_cast hc)) h₃
  have hCachesKW : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c →
      c ≤ M.supportCutoff S.C ((r + 3) * S.C.R + 1) → ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j →
      x.time j ≤ x.time k → w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w) :=
    fun k u c hk hc j w h₁ h₂ h₃ => hCachesLe j w h₁ (le_trans h₂ (hTick k u c hk hc)) h₃
  -- the confirmations chain up to the window's last opener, and every prefix of it
  have hChainW : ∀ n : ℕ, n ≤ (r + 3) * S.C.R → ConfirmationsChainBefore M S A x s₀ n := by
    have hp3 : S.P.proposer ((r + 3) * S.C.R) ∈ updaterAt M S A x ((r + 3) * S.C.R) ∨ True := Or.inr trivial
    obtain ⟨k₃, hk₃, -⟩ := Activity.mem_activeThroughoutToTick.1 hO3.1
    have hC := (hChain ((r + 3) * S.C.R) k₃ _ hk₃ (hTick _ _ _ hk₃ le_rfl)).1
    intro n hn s₁ s₂ v v' C C' h₁ h₂ h₃ hv hv' hC₁ hC₂
    exact hC s₁ s₂ v v' C C' h₁ h₂ (by omega) hv hv' hC₁ hC₂
  -- the chain invariant and the lock invariant at the slots of the window
  have hInvW : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 3) * S.C.R →
      ChainInvFor M S A x (honestActiveAt M S A x s') (OnHonestChainBefore M S A x s₀ s') s' ∧
      ∀ u ∈ honestActiveAt M S A x s', LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' u := by
    intro s' h₁ h₂
    have hc' : M.supportCutoff S.C s' ≤ M.supportCutoff S.C ((r + 3) * S.C.R + 1) := hcm _ _ (by omega)
    exact (lem81_inv_before M F U) S A x R GST s₀ (anchorCW S tGAT) (s' + 1) B₀ E hNet hSkew hRedeliver Sy hΔs
      (hRootsAt _ (by rw [Nat.add_sub_cancel]; exact le_trans hc' hcut))
      (fun k u c hk hc => hRootsTickW k u c hk (le_trans (by rwa [Nat.add_sub_cancel] at hc) hc'))
      hParent hOwner hGSTs (hCommittees.mono M (hcutle _ (by omega))) hAnc hB₀slot hBase hBaseSaved
      (fun s'' h₃ h₄ => hVF s'' h₃ (hcutle _ (by omega)))
      (fun s'' h₃ h₄ v hv => hUF s'' h₃ v hv (hUpdTick s'' (by omega) v hv)) s' h₁ (Nat.lt_succ_self s')
  have hLocks₀ : ∀ u ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ u :=
    fun u hu => (base_locks_on_chain M F U) S A x R s₀ (anchorCW S tGAT) B₀ u E
      (hCommittees.mono M (le_trans (hcm _ _ (by
        have : s₀ < s := by
          by_contra hcon
          have h1 := hsle s s₀ (by omega)
          have h2 := hTimes (s₀ + 1)
          have h3 := hTimes s₀
          have : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) < M.slotStart S.C s := lt_trans hsc hx2s
          have : M.supportCutoff S.C (s₀ + 1) < M.slotStart S.C s := by exact_mod_cast this
          omega
        omega)) (hcutle s (by omega)))) hAnc hB₀slot hBase hBaseSaved hu
  -- the tick clause of `hAfter` at a first slot of a round after the proposal's
  have hAfterOf : ∀ σ : ℕ, s ≤ σ → (x.time i₂ < M.slotStart S.C σ ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer σ) (M.slotStart S.C σ) → x.time i₂ < x.time k) := by
    intro σ hσ
    have h := hafter σ (le_trans hs (by exact_mod_cast hsle _ _ hσ))
    exact ⟨h.1, fun k hk => h.2 k _ hk⟩
  -- the activity rows of the callees, from Lemma 98's
  have hHoldW : ∀ σ : ℕ, r * S.C.R - 1 ≤ σ → σ ≤ (r + 3) * S.C.R → ∀ u ∈ honestActiveAt M S A x σ,
      u ∈ S.P.committee σ → u ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) := fun σ h₁ h₂ =>
    hHold σ (le_trans (hEnd r le_rfl) (hsle _ _ (by omega))) (hcutle _ (by omega))
  have hHoldPW : ∀ ρ : ℕ, r ≤ ρ → ρ ≤ r + 3 → HonestOpenerAt M S A x (ρ * S.C.R) →
      S.P.proposer (ρ * S.C.R) ∈ A.activeThroughout x ((M.slotStart S.C (ρ * S.C.R) - max (Δ S) Δs : ℕ) : ℝ)
        (((M.slotStart S.C (ρ * S.C.R) - max (Δ S) Δs : ℕ) : ℝ) + Δs) := fun ρ h₁ h₂ hO => by
    have hρ : ρ * S.C.R ≤ (r + 3) * S.C.R := Nat.mul_le_mul_right _ h₂
    refine Activity.mem_activeThroughout_of_le le_rfl ?_ (hHoldP _ (hEnd ρ h₁) (hcutle _ (by omega)) hO)
    have : (M.slotStart S.C (ρ * S.C.R) - max (Δ S) Δs : ℕ) ≤ M.supportCutoff S.C (ρ * S.C.R + 1) := by
      have := hTimes (ρ * S.C.R); have := hTimes (ρ * S.C.R + 1); omega
    have : ((M.slotStart S.C (ρ * S.C.R) - max (Δ S) Δs : ℕ) : ℝ) ≤ (M.supportCutoff S.C (ρ * S.C.R + 1) : ℝ) := by
      exact_mod_cast this
    linarith
  have hAdvQW : ∀ n : ℕ, n ≤ (r + 3) * S.C.R + 1 → A.AdversaryFewerThanQuorumUntil x (quorum V) (M.supportCutoff S.C n) :=
    fun n hn => hAdvQ'.mono (by exact_mod_cast hcutle n hn)
  -- the window's proposals
  obtain ⟨B2, hB2⟩ := (proposal_of_opener M F U) S A x R _ E hSkew (by omega) hO1
  obtain ⟨B3, hB3⟩ := (proposal_of_opener M F U) S A x R _ E hSkew (by omega) hO2
  obtain ⟨B4, hB4⟩ := (proposal_of_opener M F U) S A x R _ E hSkew (by omega) hO3
  -- the existence of the proposal
  have hIs := hIncl s hs (hcutle _ (by omega)) hop
  refine ⟨hIs.1, fun i B hl hsent => ?_⟩
  by_cases hc1 : RootCollisionAtProposal M S A x s B
  · exact Or.inl hc1
  by_cases hc2 : RootCollisionAtOpening M S A x (fun i => r + i) 3
  · exact Or.inr (Or.inl hc2)
  right; right
  have hNC : ∀ i' : ℕ, i' ≤ 3 → ∀ B' : Block V, ProposalAt M S x ((r + i') * S.C.R) B' →
      ¬ RootCollisionAtProposal M S A x ((r + i') * S.C.R) B' :=
    fun i' hi' B' hB' hcol => hc2 (((GoldilocksCorrectness.Record.Proofs.View.rootCollisionAtOpening_unfold M) x _ 3).2
      ⟨i', hi', B', hB', hcol⟩)
  have hNC2 := hNC 1 (by omega) B2 hB2
  have hNC3 := hNC 2 (by omega) B3 hB3
  have hNC4 := hNC 3 (by omega) B4 hB4
  -- the window's first proposal `B₁`, with `B` its ancestor or itself
  obtain ⟨B1, hB1, hNC1, hBB1⟩ : ∃ B1 : Block V, ProposalAt M S x (r * S.C.R) B1 ∧
      ¬ RootCollisionAtProposal M S A x (r * S.C.R) B1 ∧ B.AncestorEq B1 := by
    rcases Nat.lt_or_ge s (r * S.C.R) with hlt | hge
    · obtain ⟨B1, hB1⟩ := (proposal_of_opener M F U) S A x R _ E hSkew hrR hO0
      have hNC1 : ¬ RootCollisionAtProposal M S A x (r * S.C.R) B1 := by
        have := hNC 0 (by omega) B1 (by simpa using hB1)
        simpa using this
      refine ⟨B1, hB1, hNC1, ?_⟩
      obtain ⟨q₁, hq₁⟩ : ∃ q₁, r * S.C.R = q₁ + 2 := ⟨r * S.C.R - 2, by omega⟩
      have hp₁ : S.P.proposer (r * S.C.R) ∈ honestActiveAt M S A x (r * S.C.R) := by
        rw [hq₁]; rw [hq₁] at hO0; exact (opener_mem_honestActiveAt M F U) S A R E q₁ hO0
      obtain ⟨i1, hl1, hsent1⟩ := hB1
      obtain ⟨k₁, hk₁, -⟩ := Activity.mem_activeThroughoutToTick.1 hO0.1
      have hj₁ := x.lbl_tickStep ⟨k₁, hk₁⟩
      have htj₁ := hTick _ _ _ hj₁ (hcm _ _ (by omega))
      rcases (hIncl (r * S.C.R) (hEnd r le_rfl) (hcutle _ (by omega)) hO0).2 i1 B1 hl1 hsent1 with hcol | ⟨hfirst, -⟩
      · exact absurd hcol hNC1
      have hconf := hfirst _ hp₁ htj₁
      rcases hIs.2 i B hl hsent with hcol | ⟨-, hlater⟩
      · exact absurd hcol hc1
      have hHon : A.HonestThroughTime x (x.time (x.tickStep (S.P.proposer (r * S.C.R))
          (M.supportCutoff S.C (r * S.C.R + 1)))) (S.P.proposer (r * S.C.R)) :=
        Activity.not_mem_corruptedAtTime.1 (fun h => hO0.2 (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
      have hB := hlater _ _ (r * S.C.R) hHon hlt.le hp₁ le_rfl (hcutle _ (by omega)) htj₁
      rw [show x.st (x.tickStep (S.P.proposer (r * S.C.R)) (M.supportCutoff S.C (r * S.C.R + 1)) + 1)
          (S.P.proposer (r * S.C.R)) = x.tickOutput (S.P.proposer (r * S.C.R)) (M.supportCutoff S.C (r * S.C.R + 1))
          from rfl, hconf] at hB
      exact hB
    · have hseq : s = r * S.C.R := le_antisymm hsr hge
      subst hseq
      exact ⟨B, ⟨i, hl, hsent⟩, hc1, ancestorEq_refl B⟩
  have hm10 : (r + 1 - 1) * S.C.R = r * S.C.R := by rw [Nat.add_sub_cancel]
  have hm11 : (r + 1 + 1) * S.C.R = r * S.C.R + 2 * S.C.R := by rw [Nat.add_mul, Nat.add_mul]; omega
  have hm21 : (r + 2 + 1) * S.C.R = r * S.C.R + 3 * S.C.R := by rw [Nat.add_mul, Nat.add_mul]; omega
  have hvW : ∀ n : ℕ, n ≤ (r + 3) * S.C.R + 1 → M.voteTime S.C n ≤ M.supportCutoff S.C ((r + 3) * S.C.R + 1) :=
    fun n hn => le_trans (hvle n hn) (hcm _ _ hn)
  have hvt : ∀ n : ℕ, n ≤ (r + 3) * S.C.R + 1 → M.voteTime S.C n ≤ t := fun n hn => le_trans (hvW n hn) hcut
  -- Lemma 95 at `r` and `r + 1`: the height rises twice
  obtain ⟨hB12, hh12⟩ := (consecutive_openings_height_step M F U Fx) S A x R GST s₀ (anchorCW S tGAT) i₂ H r B1 B2
    (E := E) (hNet := hNet) (hSkew := hSkew) (hRedeliver := hRedeliver) (E_F := E_F) (hNet_F := hNet_F) (hSkew_F := hSkew_F)
    (Sy := Sy) (hΔs := hΔs) (Sy_F := Sy_F) (hΔs_F := hΔs_F)
    (hRoots := hRootsAt _ (hvt _ (by omega)))
    (hRootsK := fun k u c hk hc => hRootsTickW k u c hk (le_trans hc (hvW _ (by omega))))
    (hParent := hParent) (hAdvQ := hAdvQW _ (by omega)) (hSleepK := hCommittees.mono M (hcutle _ (by omega)))
    (hAnchor := hAnc₂) (hGST := hGSTs) (ht₀ := hsc.le) (hChain := hChainW _ (by omega))
    (hInv := fun s' h₁ h₂ => (hInvW s' h₁ (by omega)).1) (hLocks := fun s' h₁ h₂ => (hInvW s' h₁ (by omega)).2)
    (hLocks₀ := hLocks₀) (hOld := hOld) (hCaches := hCachesTo _ (hvt _ (by omega)))
    (hCachesK := fun k u c hk hc => hCachesKW k u c hk (le_trans hc (hvW _ (by omega))))
    (hParam := hParamN) (hAfter := hAfterOf _ hsr) (hOpener := hO0) (hOpener' := hO1) (hQuorum := hQ0)
    (hDel := hDelF r (hEnd r le_rfl) hO1) (hPropose := hB1) (hPropose' := hB2) (hNoCol := hNC1) (hNoCol' := hNC2)
    (hHold := fun σ h₁ h₂ => hHoldW σ (by omega) (by omega)) (hHold' := hHoldW _ (by omega) (by omega))
    (hHoldP := hHoldPW r le_rfl (by omega) hO0) (hHoldP' := hHoldPW (r + 1) (by omega) (by omega) hO1)
  obtain ⟨hB23, hh23⟩ := (consecutive_openings_height_step M F U Fx) S A x R GST s₀ (anchorCW S tGAT) i₂ H (r + 1) B2 B3
    (E := E) (hNet := hNet) (hSkew := hSkew) (hRedeliver := hRedeliver) (E_F := E_F) (hNet_F := hNet_F) (hSkew_F := hSkew_F)
    (Sy := Sy) (hΔs := hΔs) (Sy_F := Sy_F) (hΔs_F := hΔs_F)
    (hRoots := hRootsAt _ (hvt _ (by omega)))
    (hRootsK := fun k u c hk hc => hRootsTickW k u c hk (le_trans hc (hvW _ (by omega))))
    (hParent := hParent) (hAdvQ := hAdvQW _ (by omega)) (hSleepK := hCommittees.mono M (hcutle _ (by omega)))
    (hAnchor := hAnc₂) (hGST := hGSTs) (ht₀ := hsc.le) (hChain := hChainW _ (by omega))
    (hInv := fun s' h₁ h₂ => (hInvW s' h₁ (by omega)).1) (hLocks := fun s' h₁ h₂ => (hInvW s' h₁ (by omega)).2)
    (hLocks₀ := hLocks₀) (hOld := hOld) (hCaches := hCachesTo _ (hvt _ (by omega)))
    (hCachesK := fun k u c hk hc => hCachesKW k u c hk (le_trans hc (hvW _ (by omega))))
    (hParam := hParamN) (hAfter := hAfterOf _ (by omega)) (hOpener := hO1) (hOpener' := hO2) (hQuorum := hQ1)
    (hDel := hDelF (r + 1) (hEnd _ (by omega)) hO2) (hPropose := hB2) (hPropose' := hB3) (hNoCol := hNC2) (hNoCol' := hNC3)
    (hHold := fun σ h₁ h₂ => hHoldW σ (by omega) (by omega)) (hHold' := hHoldW _ (by omega) (by omega))
    (hHoldP := hHoldPW (r + 1) (by omega) (by omega) hO1) (hHoldP' := hHoldPW (r + 2) (by omega) (by omega) hO2)
  -- Lemma 96 at `r + 1`: the second proposal's height is justified by the third
  have h96 : (M.chainStateOf S.C B2).h ≤ (M.chainStateOf S.C B3).h_j :=
    (lem96_consecutive_openings_justified M F U Fx) S A x R GST s₀ (anchorCW S tGAT) i₂ H (r + 1) B1 B2 B3
      (E := E) (hNet := hNet) (hSkew := hSkew) (hRedeliver := hRedeliver) (E_F := E_F) (hNet_F := hNet_F)
      (hSkew_F := hSkew_F) (Sy := Sy) (hΔs := hΔs) (Sy_F := Sy_F) (hΔs_F := hΔs_F)
      (hRoots := hRootsAt _ (hvt _ (by omega)))
      (hRootsK := fun k u c hk hc => hRootsTickW k u c hk (le_trans hc (hvW _ (by omega))))
      (hParent := hParent) (hAdvQ := hAdvQW _ (by omega)) (hSleepK := hCommittees.mono M (hcutle _ (by omega)))
      (hAnchor := hAnc₂) (hGST := hGSTs) (ht₀ := hsc.le) (hChain := hChainW _ (by omega))
      (hInv := fun s' h₁ h₂ => (hInvW s' h₁ (by omega)).1) (hLocks := fun s' h₁ h₂ => (hInvW s' h₁ (by omega)).2)
      (hLocks₀ := hLocks₀) (hOld := hOld) (hCaches := hCachesTo _ (hvt _ (by omega)))
      (hCachesK := fun k u c hk hc => hCachesKW k u c hk (le_trans hc (hvW _ (by omega))))
      (hParam := hParamN) (hδt := hδt) (hr := by omega) (hAfter := by rw [hm10]; exact hAfterOf _ hsr)
      (hOpenerPrev := by rw [hm10]; exact hO0) (hOpener := hO1) (hOpener' := hO2)
      (hQuorumPrev := by rw [hm10]; exact hQ0)
      (hDelPrev := by rw [hm10]; exact hDelF r (hEnd r le_rfl) hO1) (hQuorum := hQ1)
      (hDel := hDelF (r + 1) (hEnd _ (by omega)) hO2)
      (hProposePrev := by rw [hm10]; exact hB1) (hPropose := hB2) (hPropose' := hB3)
      (hNoColPrev := by rw [hm10]; exact hNC1) (hNoCol := hNC2) (hNoCol' := hNC3)
      (hHoldPrev := fun σ h₁ h₂ => hHoldW σ (by omega) (by omega))
      (hHold := fun σ h₁ h₂ => hHoldW σ (by omega) (by omega)) (hHold' := hHoldW _ (by omega) (by omega))
      (hHoldPPrev := by rw [hm10]; exact hHoldPW r le_rfl (by omega) hO0)
      (hHoldP := hHoldPW (r + 1) (by omega) (by omega) hO1) (hHoldP' := hHoldPW (r + 2) (by omega) (by omega) hO2)
  -- the per-tick rows at the openers `(r + 1) * R` and `(r + 3) * R`
  obtain ⟨hU1t, hU1r, hU1q⟩ := opening_tick_rows_of_lastTick M F S A x tAwakeEnd t hLastTick hRootsT hAdvQ' _
    (hEnd _ (by omega)) hO1 (hcutle _ (by omega))
  obtain ⟨hU3t, hU3r, hU3q⟩ := opening_tick_rows_of_lastTick M F S A x tAwakeEnd t hLastTick hRootsT hAdvQ' _
    hEnd3 hO3 hcut
  -- the frame at `(r + 1) * R`: `H < h(B₂)`
  obtain ⟨q₂, hq₂⟩ : ∃ q₂, (r + 1) * S.C.R = q₂ + 2 := ⟨(r + 1) * S.C.R - 2, by omega⟩
  have hp₂ : S.P.proposer ((r + 1) * S.C.R) ∈ honestActiveAt M S A x ((r + 1) * S.C.R) := by
    rw [hq₂]; rw [hq₂] at hO1; exact (opener_mem_honestActiveAt M F U) S A R E q₂ hO1
  obtain ⟨-, -, -, hHB2, -⟩ := (round_member_frame_after_healing M F U Fx) S A x R GST s₀ (anchorCW S tGAT) i₂ H
    ((r + 1) * S.C.R) B2 _ (E := E) (hNet := hNet) (hSkew := hSkew) (hRedeliver := hRedeliver) (Sy := Sy) (hΔs := hΔs)
    (hRootsU := hU1r) (hParent := hParent) (hAdvQU := hU1q) (hSleepK := hCommittees.mono M (hcutle _ (by omega)))
    (hAnchor := hAnc₂) (hGST := hGSTs) (ht₀ := hsc.le) (hChain := hChainW _ (by omega))
    (hInv := fun s' h₁ h₂ => (hInvW s' h₁ (by omega)).1) (hLocks := fun s' h₁ h₂ => (hInvW s' h₁ (by omega)).2)
    (hLocks₀ := hLocks₀) (hOld := hOld)
    (hCachesU := fun v hv j w h₁ h₂ h₃ => hCachesLe j w h₁ (le_trans h₂ (hU1t v hv)) h₃)
    (hAfter := hAfterOf _ (by omega)) (hOpener := hO1) (hPropose := hB2) (hNoCollision := hNC2)
    (hHold := fun σ h₁ h₂ => hHoldW σ (by omega) (by omega)) (hHoldP := hHoldPW (r + 1) (by omega) (by omega) hO1)
    (hu := hp₂)
  -- Lemma 107 at `r + 1`, raised to `h_j(B₃)`: the old honest attestations of round `r + 2`
  have h107 := (lem107_honest_attestations_at_most_opening_height M F U Fx) S A x R GST s₀ (anchorCW S tGAT) i₂ H
    (r + 1) ((r + 1) * S.C.R) B2 (E := E) (hNet := hNet) (hSkew := hSkew) (hRedeliver := hRedeliver) (Sy := Sy)
    (hΔs := hΔs) (hRootsU := hU1r) (hParent := hParent) (hAdvQU := hU1q)
    (hSleepK := hCommittees.mono M (hcutle _ (by omega)))
    (hAnchor := hAnc₂) (hGST := hGSTs) (ht₀ := hsc.le) (hChain := hChainW _ (by omega))
    (hInv := fun s' h₁ h₂ => (hInvW s' h₁ (by omega)).1) (hLocks := fun s' h₁ h₂ => (hInvW s' h₁ (by omega)).2)
    (hLocks₀ := hLocks₀) (hOld := hOld)
    (hCachesU := fun v hv j w h₁ h₂ h₃ => hCachesLe j w h₁ (le_trans h₂ (hU1t v hv)) h₃) (hs := rfl)
    (hAfter := hAfterOf _ (by omega)) (hOpener := hO1) (hPropose := hB2) (hNoCollision := hNC2)
    (hHold := fun σ h₁ h₂ => hHoldW σ (by omega) (by omega)) (hHoldP := hHoldPW (r + 1) (by omega) (by omega) hO1)
  have hOldJ : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C ((r + 2) * S.C.R + 1))
      (M.supportCutoff S.C ((r + 2) * S.C.R + 1)) (M.chainStateOf S.C B3).h_j :=
    (GoldilocksCorrectness.Record.Statements.Executions.oldAttestationsAtMost_mono M F) S A x _ _ _ h107 h96
  -- Lemma 95 at `r + 2`: the fourth proposal finalizes the third's justification
  obtain ⟨hB34, hh34, hjF⟩ := (lem95_consecutive_openings_step M F U Fx) S A x R GST s₀ (anchorCW S tGAT) i₂ H (r + 2) B3 B4
    (E := E) (hNet := hNet) (hSkew := hSkew) (hRedeliver := hRedeliver) (E_F := E_F) (hNet_F := hNet_F) (hSkew_F := hSkew_F)
    (Sy := Sy) (hΔs := hΔs) (Sy_F := Sy_F) (hΔs_F := hΔs_F)
    (hRoots := hRootsAt _ (hvt _ (by omega)))
    (hRootsK := fun k u c hk hc => hRootsTickW k u c hk (le_trans hc (hvW _ (by omega))))
    (hParent := hParent) (hAdvQ := hAdvQW _ (by omega)) (hSleepK := hCommittees.mono M (hcutle _ (by omega)))
    (hAnchor := hAnc₂) (hGST := hGSTs) (ht₀ := hsc.le) (hChain := hChainW _ (by omega))
    (hInv := fun s' h₁ h₂ => (hInvW s' h₁ (by omega)).1) (hLocks := fun s' h₁ h₂ => (hInvW s' h₁ (by omega)).2)
    (hLocks₀ := hLocks₀) (hOld := hOld) (hCaches := hCachesTo _ (hvt _ (by omega)))
    (hCachesK := fun k u c hk hc => hCachesKW k u c hk (le_trans hc (hvW _ (by omega))))
    (hParam := hParamN) (hAfter := hAfterOf _ (by omega)) (hOpener := hO2) (hOpener' := hO3) (hQuorum := hQ2)
    (hDel := hDelF (r + 2) (hEnd _ (by omega)) hO3) (hPropose := hB3) (hPropose' := hB4) (hNoCol := hNC3) (hNoCol' := hNC4)
    (hHold := fun σ h₁ h₂ => hHoldW σ (by omega) (by omega)) (hHold' := hHoldW _ (by omega) (by omega))
    (hHoldP := hHoldPW (r + 2) (by omega) (by omega) hO2) (hHoldP' := hHoldPW (r + 3) (by omega) (by omega) hO3)
    (hOldJ := hOldJ) (hTickInputs := hTickInputs (r + 2) (hEnd _ (by omega)) hO2) (hHJ := lt_of_lt_of_le hHB2 h96)
  -- `B` is a strict ancestor of `F(B₄)`
  have hBB4 : B.AncestorEq B4 := ancestorEq_trans hBB1 (ancestorEq_trans hB12 (ancestorEq_trans hB23 hB34))
  have hhB := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B1).2.2.2.1 hBB1
  have hF1 : 1 ≤ (M.chainStateOf S.C B4).h_F := by
    have := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B).1.1
    omega_nat
  obtain ⟨-, -, hFB4, hFh⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C B4).2.2 hF1
  have hBF : B.AncestorEq (M.chainStateOf S.C B4).F := by
    rcases ancestorEq_compatible hBB4 hFB4 with h | h
    · exact h
    · exfalso
      have := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C _ _).2.2.2.1 h
      rw [hFh] at this
      omega_nat
  have hBneF : B ≠ (M.chainStateOf S.C B4).F := by
    intro h
    have : (M.chainStateOf S.C B).h = (M.chainStateOf S.C (M.chainStateOf S.C B4).F).h := by rw [h]
    rw [hFh] at this
    omega_nat
  intro v j hv hjt hAw
  -- Lemma 97 at `B₄`: the reader's finalized block is `F(B₄)` or a descendant of it
  have h97 := (lem97_reader_finalized M F U Fx) S A x R GST s₀ (anchorCW S tGAT) i₂ H t (r + 3) ((r + 3) * S.C.R) j B4 v
    (E := E) (hNet := hNet) (hSkew := hSkew) (hRedeliver := hRedeliver) (Sy := Sy) (hΔs := hΔs)
    (hRoots := hRootsT) (hRootsU := hU3r) (hParent := hParent) (hAdvQ := hAdvQ') (hAdvQU := hU3q)
    (hSleepK := hCommittees) (hAnchor := hAnc₂) (hGST := hGSTs) (ht₀ := hsc.le)
    (hChain := fun σ hσ => by
      by_cases h : σ + 1 ≤ (r + 3) * S.C.R
      · exact hChainW _ h
      · exact hG2c σ hσ)
    (hInv := fun s' h₁ h₂ => by
      by_cases h : s' ≤ (r + 3) * S.C.R
      · exact (hInvW s' h₁ h).1
      · exact (hInvT s' h₁ h₂).1)
    (hLocks := fun s' h₁ h₂ => by
      by_cases h : s' ≤ (r + 3) * S.C.R
      · exact (hInvW s' h₁ h).2
      · exact (hInvT s' h₁ h₂).2)
    (hLocks₀ := hLocks₀) (hOld := hOld)
    (hCaches := fun j' w h₁ h₂ h₃ => hCachesLe j' w h₁ h₂ h₃)
    (hCachesU := fun v' hv' j' w h₁ h₂ h₃ => hCachesLe j' w h₁ (le_trans h₂ (hU3t v' hv')) h₃)
    (hsD := rfl) (hT := hcutle _ (by omega)) (hAfter := hAfterOf _ (by omega)) (hOpener := hO3) (hPropose := hB4)
    (hNoCol := hNC4) (hHold := fun σ h₁ h₂ => hHoldW σ (by omega) (by omega))
    (hHoldC := fun σ' h₁ h₂ => hHoldC σ' (le_trans hEnd3 (hsle _ _ (by omega))) h₂)
    (hHoldP := hHoldP _ hEnd3 (hcutle _ (by omega)) hO3) (hHD := by omega_nat) (hv := hv) (hjT := hjt) (hAwake := hAw)
  have hBFj : B.AncestorEq (x.st j v).finalized := ancestorEq_trans hBF h97
  refine ⟨hBFj, fun u i' hi' hEq => ?_⟩
  -- the slot of the reader's finalized block is greater than `s`
  have hvj : v ∉ A.corrupted j := hv j le_rfl
  have hInvj := (lem11_node_invariant M F S A x R E j v hvj).1
  have hFT : (x.st j v).finalized ∈ (x.st j v).tree := F.nd.nodeInv_finalized_mem_tree hInvj
  have hBne : B ≠ (x.st j v).finalized := by
    intro h
    rw [← h] at h97
    exact hBneF (ancestorEq_antisymm hBF h97)
  have hBslot : B.slot = s := by
    obtain ⟨s₁, rfl⟩ : ∃ s₁, s = s₁ + 1 := ⟨s - 1, by omega⟩
    exact ((proposal_parent_walk_end M F U) S A x R E s₁ i B (S.P.proposer (s₁ + 1)) hl hsent).1
  have hlt := (slot_lt_of_ancestorEq_of_treeClosed_node M F) (F.nd.nodeInv_treeClosed hInvj) hFT hBFj hBne
  rw [hBslot, ← hEq] at hlt
  -- `u`'s finalized block before the start of `s` has a slot at most `s`
  have hu := (finalized_slot_le_of_time_lt_slotStart M F U) S A x R E hSkew s i' u hi'
  omega_nat

/-- **Lemma 98, finality liveness after healing.** The proof; the audited statement is in
`Statements/Executions/HealedFinalityLivenessStatements.lean`.

Why: for `t ≥ tAwakeEnd`, either a root collision has hit two blocks honest validators hold by
`t`, or roots name blocks up to `t`; then the facts after the hand-over up to `t`
(`healed_handover_facts_until`) and the inclusion up to `t` (`lem90_healed_confirmed_until`). For
a proposal `B` of slot `s` followed by the window at `r`, with no root collision at the five
proposals `B`, `B₁` to `B₄`: `B` is `B₁` or an ancestor of the confirmed tip `B₁` of the proposer
of `r * R` (the inclusion of `B`, read at that proposer, honest active at `r * R − 1`); Lemma 95
at `r` and `r + 1` raises the height twice; Lemma 96 at `r + 1` puts `h(B₂) ≤ h_j(B₃)`; the frame
at `(r + 1) * R` gives `H < h(B₂)`, Lemma 107 at `r + 1` bounds the honest attestations before the
action time of round `r + 2` by `h(B₂)`, so Lemma 95 at `r + 2` applies and `h_j(B₃) ≤ h_F(B₄)`.
So `h(B) < h(F(B₄))` with `F(B₄)` and `B` ancestors of `B₄`: `B` is a strict ancestor of `F(B₄)`,
and Lemma 97 makes `F(B₄)` an ancestor of the reader's finalized block. That finalized block has a
slot greater than `B`'s, `s`, while every finalized block held before the start of `s` has a slot
less than `s`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `m`, `rs`: the index of the last honest round opening slot and the rounds of the honest round opening slots.

The second conclusion, `FinalizedExtendedByHonestProposalsBetween`, from the first and Lemma 86 read
up to `t` (`lem86_healed_finality_safety_until`, `finalizedExtendedBetween_of_compatible_included`).

Read aloud: for every time `t` after the phase, unless a collision has hit by `t`, whenever four
consecutive honest round opening slots with quorums at the first three follow an honest proposal,
everyone awake for a delay after the fourth has, up to `t`, finalized that proposal or a descendant
of it, a block no validator had finalized before the proposal, and that finalized block strictly
extends every finalized block honest validators had before the proposal. -/
theorem lem98_healed_finality_liveness (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (rs : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (rs i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    -- the time up to which the execution is read, after the phase
    (t : ℕ) (ht : tAwakeEnd ≤ t)
    -- `t` is not inside any slot's update: at every slot whose update is at most `t`, or to whose update some
    -- validator ticked at a real time at most `t`, every tick to a clock value at most that update is at a real
    -- time at most `t` (; the sentence of's `hLastTick` at every slot, which it replaces)
    (hTicksBy : TicksToUpdatesBy M S x t)
    -- committee sleepiness from `anchorCW S tGAT`, for the slots whose update is at most `t`
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) t)
    -- every tick at a real time at most `t`, to a clock value `c`: committee sleepiness from `anchorCW S tGAT` read up
    -- to `c`
    (hCommitteesTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → (x.time k : ℝ) ≤ t →
      CommitteeSleepinessUntil M S A x (anchorCW S tGAT) c)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    -- every updater of a slot from the first honest round opening slot `rs 0 * S.C.R` on, whose update is at
    -- most `t`, is active for the sync delay after the real time of its own tick to the support cutoff of the
    -- next slot
    (hStay : ∀ σ : ℕ, rs 0 * S.C.R ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hOpenings : OpeningsOutsideWaitsAndWindows S rs m)
    -- fewer than two thirds of the validators corrupted up to `t`
    (hAdvQ : A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) t)
    (hParam : (Δ_F S : ℝ) + Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * (S.C.k + 1))
    (hDelF : ∀ r' : ℕ, tAwakeEnd ≤ M.slotStart S.C (r' * S.C.R) → HonestOpenerAt M S A x ((r' + 1) * S.C.R) →
      ∀ u ∈ honestActiveAt M S A x (r' * S.C.R), ∀ (j t' : ℕ) (a : Attestation V), x.lbl j = Event.tick u t' →
      t' ≤ M.supportCutoff S.C (r' * S.C.R + 1) →
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j →
      M.justifiedHeight (x.stateBefore (M.proposalWindowStart S.C ((r' + 1) * S.C.R)) u) ≤ a.h →
      (∃ d : ℕ, x.lbl d = Event.deliver (S.P.proposer ((r' + 1) * S.C.R)) ⟨u, NamedObject.attest a⟩ ∧
      d < x.tickStep (S.P.proposer ((r' + 1) * S.C.R)) (M.slotStart S.C ((r' + 1) * S.C.R))) ∨
      a ∈ (x.stateBefore (M.proposalWindowStart S.C ((r' + 1) * S.C.R)) (S.P.proposer ((r' + 1) * S.C.R))).attestationsHeld)
    -- at every honest round opening slot after the phase, no block an honest active member of the round holds when it
    -- ticks to the round's action time includes an attestation put on the wire at a tick to that action time
    --
    (hTickInputs : ∀ r' : ℕ, tAwakeEnd ≤ M.slotStart S.C (r' * S.C.R) → HonestOpenerAt M S A x (r' * S.C.R) →
      ∀ v ∈ honestActiveAt M S A x (r' * S.C.R), ∀ Z ∈ (x.tickInput v (M.supportCutoff S.C (r' * S.C.R + 1))).tree,
      ∀ a ∈ Z.attestations, ∀ (j : ℕ) (w : V), x.lbl j = Event.tick w (M.supportCutoff S.C (r' * S.C.R + 1)) →
      (⟨w, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x.sent (j + 1) - x.sent j)
    (hHold : ∀ s' : ℕ, tAwakeEnd ≤ M.slotStart S.C (s' + 1) → M.supportCutoff S.C (s' + 1) ≤ t →
      ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- every honest committee member of every slot starting at or after `tAwakeEnd` whose update is at most `t` is active
    -- from its duty window's start through the sync delay after that update; at every slot at or after `tAwakeEnd` with an
    -- honest opener whose update is at most `t`, its proposer through the sync delay after the slot's update
    --
    (hHoldC : ∀ σ' : ℕ, tAwakeEnd ≤ M.slotStart S.C σ' → M.supportCutoff S.C (σ' + 1) ≤ t →
      ∀ u ∈ honestActiveAt M S A x σ', u ∈ S.P.committee σ' →
      u ∈ A.activeThroughout x ((M.dutyWindowStart S.C σ' : ℕ) : ℝ) (((M.supportCutoff S.C (σ' + 1) : ℕ) : ℝ) + Δs))
    (hHoldP : ∀ s : ℕ, tAwakeEnd ≤ M.slotStart S.C s → M.supportCutoff S.C (s + 1) ≤ t → HonestOpenerAt M S A x s →
      S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + Δs)) :
    RootCollisionAtOpening M S A x rs m ∨ RootCollisionHeldBy M S A x t ∨
      (FinalityIncludedBetween M S A x Δs tAwakeEnd t ∧
        FinalizedExtendedByHonestProposalsBetween M S A x Δs tAwakeEnd t) := by
  have hAdvQ' := (adversaryFewerThanQuorumUntil_of_adversaryFewerThanTwoThirdsUntil M F) A x t hAdvQ
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hR := S.C.R_ge_two
  have hcm : ∀ a b : ℕ, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun a b h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  have hsle : ∀ n n' : ℕ, n ≤ n' → M.slotStart S.C n ≤ M.slotStart S.C n' := fun n n' h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h
  have hTimes : ∀ n : ℕ, M.voteTime S.C n = M.slotStart S.C n + Δ S ∧
      M.supportCutoff S.C n = M.slotStart S.C n + 2 * Δ S ∧
      M.slotStart S.C (n + 1) = M.slotStart S.C n + 4 * Δ S := fun n => by
    have h1 : M.voteTime S.C n = M.slotStart S.C n + Δ S :=
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S n
    have h2 : M.supportCutoff S.C n = M.voteTime S.C n + Δ S :=
      (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S n
    have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S n
    have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (n + 1)
    refine ⟨h1, by omega, ?_⟩
    rw [h4, h3, Nat.mul_add, Nat.mul_one]
  -- the second conclusion from the first and Lemma 86 read up to `t`
  rcases (lem86_healed_finality_safety_until M F U Fx) S A x R GST tGAT tAwakeEnd m rs hGST E hNet hSkew hRedeliver
      E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hParent hThird hAwake hActive t ht hCommittees hCommitteesTick hStay
      hSeq hOpenings hAdvQ with hCol | hCol | hCompat
  · exact Or.inl hCol
  · exact Or.inr (Or.inl hCol)
  suffices h : RootCollisionAtOpening M S A x rs m ∨ RootCollisionHeldBy M S A x t ∨
      FinalityIncludedBetween M S A x Δs tAwakeEnd t by
    rcases h with hCol | hCol | hIncl
    · exact Or.inl hCol
    · exact Or.inr (Or.inl hCol)
    exact Or.inr (Or.inr ⟨hIncl, (finalizedExtendedBetween_of_compatible_included M F U) S A x R E hSkew
      Δs tAwakeEnd t hCompat hIncl⟩)
  -- roots name blocks up to `t`, or a collision has hit by `t`
  rcases (rootsNameBlocksUntil_or_collision M) x t with hRootsT | hCol
  swap
  · exact Or.inr (Or.inl hCol)
  rcases (healed_handover_facts_until M F U Fx) S A x R GST tGAT tAwakeEnd m rs hGST E hNet hSkew hRedeliver
      E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hParent hThird hAwake hActive t ht hCommittees hCommitteesTick hStay
      hSeq hOpenings hAdvQ' with
    hCol | hCol | ⟨s₀, i₂, B₀, ⟨hsc, -⟩, hx2le, hafter, -, -, hAnc, hB₀slot, hBase, hBaseSaved, -, hOld,
      hCachesAt, -, hVF, hUF, hChain⟩
  · exact Or.inl hCol
  · exact Or.inr (Or.inl hCol)
  rcases (lem90_healed_confirmed_until M F U Fx) S A x R GST tGAT tAwakeEnd m rs hGST E hNet hSkew hRedeliver
      E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hParent hThird hAwake hActive t ht hTicksBy hCommittees hCommitteesTick
      hStay hSeq hOpenings hAdvQ hHold
      (fun s hs hc hO => Activity.mem_activeThroughout_of_le le_rfl
        (by have : (M.slotStart S.C s - max (Δ S) Δs : ℕ) ≤ M.supportCutoff S.C (s + 1) := by
              have := hTimes s; have := hTimes (s + 1); omega
            have : ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) ≤ (M.supportCutoff S.C (s + 1) : ℝ) := by
              exact_mod_cast this
            linarith)
        (hHoldP s hs hc hO))
      with hCol | hCol | ⟨-, -, hIncl, -⟩
  · exact Or.inl hCol
  · exact Or.inr (Or.inl hCol)
  right; right
  exact (lem98_window_of_handover M F) U Fx S A x R GST tGAT tAwakeEnd m rs hGST E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hParent t hTicksBy hCommittees hSeq hOpenings hParam hDelF hTickInputs hHold hHoldC hHoldP
    hRootsT hAdvQ' s₀ i₂ B₀ hsc hafter hAnc hB₀slot hBase hBaseSaved hOld hCachesAt hVF hUF hChain hIncl

/-! ## Lemma 98 with the sync fact -/

/-- **Lemma 98 with the sync fact.** The proof; the audited statement is in
`Statements/Executions/HealedFinalityLivenessStatements.lean`. `lem98_healed_finality_liveness` with
`hAttW` in place of `hDelF`, and `hHoldQ`: at every round after the phase whose next round's first slot is an honest round
opening slot, the next opener is active at every step at a real time from its proposal window's start to its
slot's start.

Why: `hDelF` from the sync fact: for a round `r'` starting at or after `tAwakeEnd`, `GST` is at
least `4Δ(k + 1)` before one delay after the start of slot `(r' + 1) * R` (the honest round opening
slots lie between `tGAT + 4Δ(3k + 1)` and `tAwakeEnd`, and `GST ≤ tGAT`), so
`attestations_reach_opener_of_sync` delivers each attestation to the next opener or finds it held by
the opener before its proposal window starts, its sender active at the proposal
window's start by `hAttW`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- as `lem98_healed_finality_liveness`.

Read aloud: Lemma 98 holds when, after the phase, every honest active member of a round is still
active when the next round's proposal window opens, and each next opener is active from its proposal window's
start to its slot's start. -/
theorem lem98_healed_finality_liveness_ofSync (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (rs : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (rs i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    -- the time up to which the execution is read, after the phase
    (t : ℕ) (ht : tAwakeEnd ≤ t)
    -- `t` is not inside any slot's update: at every slot whose update is at most `t`, or to whose update some
    -- validator ticked at a real time at most `t`, every tick to a clock value at most that update is at a real
    -- time at most `t` (; the sentence of's `hLastTick` at every slot, which it replaces)
    (hTicksBy : TicksToUpdatesBy M S x t)
    -- committee sleepiness from `anchorCW S tGAT`, for the slots whose update is at most `t`
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) t)
    -- every tick at a real time at most `t`, to a clock value `c`: committee sleepiness from `anchorCW S tGAT` read up
    -- to `c`
    (hCommitteesTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → (x.time k : ℝ) ≤ t →
      CommitteeSleepinessUntil M S A x (anchorCW S tGAT) c)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    -- every updater of a slot from the first honest round opening slot `rs 0 * S.C.R` on, whose update is at
    -- most `t`, is active for the sync delay after the real time of its own tick to the support cutoff of the
    -- next slot
    (hStay : ∀ σ : ℕ, rs 0 * S.C.R ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hOpenings : OpeningsOutsideWaitsAndWindows S rs m)
    -- fewer than two thirds of the validators corrupted up to `t`
    (hAdvQ : A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) t)
    (hParam : (Δ_F S : ℝ) + Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * (S.C.k + 1))
    (hAttW : ∀ r' : ℕ, tAwakeEnd ≤ M.slotStart S.C (r' * S.C.R) → ∀ u ∈ honestActiveAt M S A x (r' * S.C.R),
      u ∈ A.activeThroughout x (M.proposalWindowStart S.C ((r' + 1) * S.C.R))
        ((M.proposalWindowStart S.C ((r' + 1) * S.C.R) : ℕ) + Δs_F))
    -- at every round after the phase whose next round's first slot is an honest round opening slot, the next opener is
    -- active at every step at a real time from its proposal window's start to its slot's start
    (hHoldQ : ∀ r' : ℕ, tAwakeEnd ≤ M.slotStart S.C (r' * S.C.R) → HonestOpenerAt M S A x ((r' + 1) * S.C.R) →
      S.P.proposer ((r' + 1) * S.C.R) ∈ A.activeThroughout x ((M.proposalWindowStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ)
        ((M.slotStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ))
    -- at every honest round opening slot after the phase, no block an honest active member of the round holds when it
    -- ticks to the round's action time includes an attestation put on the wire at a tick to that action time
    --
    (hTickInputs : ∀ r' : ℕ, tAwakeEnd ≤ M.slotStart S.C (r' * S.C.R) → HonestOpenerAt M S A x (r' * S.C.R) →
      ∀ v ∈ honestActiveAt M S A x (r' * S.C.R), ∀ Z ∈ (x.tickInput v (M.supportCutoff S.C (r' * S.C.R + 1))).tree,
      ∀ a ∈ Z.attestations, ∀ (j : ℕ) (w : V), x.lbl j = Event.tick w (M.supportCutoff S.C (r' * S.C.R + 1)) →
      (⟨w, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x.sent (j + 1) - x.sent j)
    (hHold : ∀ s' : ℕ, tAwakeEnd ≤ M.slotStart S.C (s' + 1) → M.supportCutoff S.C (s' + 1) ≤ t →
      ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- every honest committee member of every slot starting at or after `tAwakeEnd` whose update is at most `t` is active
    -- from its duty window's start through the sync delay after that update; at every slot at or after `tAwakeEnd` with an
    -- honest opener whose update is at most `t`, its proposer through the sync delay after the slot's update
    --
    (hHoldC : ∀ σ' : ℕ, tAwakeEnd ≤ M.slotStart S.C σ' → M.supportCutoff S.C (σ' + 1) ≤ t →
      ∀ u ∈ honestActiveAt M S A x σ', u ∈ S.P.committee σ' →
      u ∈ A.activeThroughout x ((M.dutyWindowStart S.C σ' : ℕ) : ℝ) (((M.supportCutoff S.C (σ' + 1) : ℕ) : ℝ) + Δs))
    (hHoldP : ∀ s : ℕ, tAwakeEnd ≤ M.slotStart S.C s → M.supportCutoff S.C (s + 1) ≤ t → HonestOpenerAt M S A x s →
      S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + Δs)) :
    RootCollisionAtOpening M S A x rs m ∨ RootCollisionHeldBy M S A x t ∨
      (FinalityIncludedBetween M S A x Δs tAwakeEnd t ∧
        FinalizedExtendedByHonestProposalsBetween M S A x Δs tAwakeEnd t) := by
  have hΔ := one_le_Δ S
  -- `GST` is at least `4Δ(k + 1)` before `tAwakeEnd`: the honest round opening slots lie between
  -- `tGAT + 4Δ(3k + 1)` and `tAwakeEnd`
  have hmono : ∀ i : ℕ, i ≤ m → rs 0 ≤ rs i := by
    intro i
    induction i with
    | zero => intro _; exact le_rfl
    | succ i ih => intro hi; exact le_trans (ih (by omega)) (hSeq.mono i (by omega)).le
  have hfirst := hSeq.first
  have hlast := hSeq.last
  unfold healFrontSlots at hfirst
  have h0m : M.slotStart S.C (rs 0 * S.C.R) ≤ M.slotStart S.C (rs m * S.C.R) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (Nat.mul_le_mul_right _ (hmono m le_rfl))
  have hcm := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (rs m * S.C.R)
  have hvm := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (rs m * S.C.R)
  have hk : 4 * Δ S * (S.C.k + 1) ≤ 4 * Δ S * (3 * S.C.k + 1) := Nat.mul_le_mul_left _ (by omega)
  have hEnd : GST + 4 * Δ S * (S.C.k + 1) ≤ tAwakeEnd := by omega
  refine (lem98_healed_finality_liveness M F U Fx) S A x R GST tGAT tAwakeEnd m rs hGST E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F
    hΔs_F hHoldF hParent hThird hAwake hActive t ht hTicksBy hCommittees hCommitteesTick hSeq hStay hOpenings hAdvQ hParam ?_ hTickInputs hHold hHoldC hHoldP
  intro r' hr' hO u hu j t' a hl ht' hsent hjust
  have hsle := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
    (show r' * S.C.R ≤ (r' + 1) * S.C.R from Nat.mul_le_mul_right _ (Nat.le_succ r'))
  exact (attestations_reach_opener_of_sync M F U) S A x R GST r' E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy_F hΔs_F hParam (by omega) hO
    (hHoldQ r' hr' hO) u (hAttW r' hr' u hu) j t' a hl ht' hsent hjust

/-- **Lemma 98 with the sync fact, for rounds of at most `k + 2` slots.** The proof; the audited
statement is in `Statements/Executions/HealedFinalityLivenessStatements.lean`.
`lem98_healed_finality_liveness_ofSync` with `hRk` in place of `hAttW`.

Why: `hAttW` from membership: with `R ≤ k + 2` the proposal window of slot `(r' + 1) * R` opens at
most `5Δ` after the start of slot `r' * R`, before the support cutoff of slot `r' * R + 1`, and not
before the duty window's start of slot `r' * R`; a member of `honestActiveAt M S A x (r' * R)` is
active throughout that window (`honestActiveAt_window`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- as `lem98_healed_finality_liveness`.

Read aloud: Lemma 98 holds with the sync fact alone when a round has at most `k + 2` slots, and each next
opener is active from its proposal window's start to its slot's start. -/
theorem lem98_healed_finality_liveness_ofSync_of_R_le (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (rs : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (rs i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    -- the time up to which the execution is read, after the phase
    (t : ℕ) (ht : tAwakeEnd ≤ t)
    -- `t` is not inside any slot's update: at every slot whose update is at most `t`, or to whose update some
    -- validator ticked at a real time at most `t`, every tick to a clock value at most that update is at a real
    -- time at most `t` (; the sentence of's `hLastTick` at every slot, which it replaces)
    (hTicksBy : TicksToUpdatesBy M S x t)
    -- committee sleepiness from `anchorCW S tGAT`, for the slots whose update is at most `t`
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) t)
    -- every tick at a real time at most `t`, to a clock value `c`: committee sleepiness from `anchorCW S tGAT` read up
    -- to `c`
    (hCommitteesTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → (x.time k : ℝ) ≤ t →
      CommitteeSleepinessUntil M S A x (anchorCW S tGAT) c)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    -- every updater of a slot from the first honest round opening slot `rs 0 * S.C.R` on, whose update is at
    -- most `t`, is active for the sync delay after the real time of its own tick to the support cutoff of the
    -- next slot
    (hStay : ∀ σ : ℕ, rs 0 * S.C.R ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hOpenings : OpeningsOutsideWaitsAndWindows S rs m)
    -- fewer than two thirds of the validators corrupted up to `t`
    (hAdvQ : A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) t)
    (hParam : (Δ_F S : ℝ) + Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * (S.C.k + 1))
    (hRk : (4 * Δ S * S.C.R : ℝ) + Δs_F + ΔClockAhead < 4 * Δ S * (S.C.k + 2) + Δ S)
    -- at every round after the phase whose next round's first slot is an honest round opening slot, the next opener is
    -- active at every step at a real time from its proposal window's start to its slot's start
    (hHoldQ : ∀ r' : ℕ, tAwakeEnd ≤ M.slotStart S.C (r' * S.C.R) → HonestOpenerAt M S A x ((r' + 1) * S.C.R) →
      S.P.proposer ((r' + 1) * S.C.R) ∈ A.activeThroughout x ((M.proposalWindowStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ)
        ((M.slotStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ))
    -- at every honest round opening slot after the phase, no block an honest active member of the round holds when it
    -- ticks to the round's action time includes an attestation put on the wire at a tick to that action time
    --
    (hTickInputs : ∀ r' : ℕ, tAwakeEnd ≤ M.slotStart S.C (r' * S.C.R) → HonestOpenerAt M S A x (r' * S.C.R) →
      ∀ v ∈ honestActiveAt M S A x (r' * S.C.R), ∀ Z ∈ (x.tickInput v (M.supportCutoff S.C (r' * S.C.R + 1))).tree,
      ∀ a ∈ Z.attestations, ∀ (j : ℕ) (w : V), x.lbl j = Event.tick w (M.supportCutoff S.C (r' * S.C.R + 1)) →
      (⟨w, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x.sent (j + 1) - x.sent j)
    (hHold : ∀ s' : ℕ, tAwakeEnd ≤ M.slotStart S.C (s' + 1) → M.supportCutoff S.C (s' + 1) ≤ t →
      ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- every honest committee member of every slot starting at or after `tAwakeEnd` whose update is at most `t` is active
    -- from its duty window's start through the sync delay after that update; at every slot at or after `tAwakeEnd` with an
    -- honest opener whose update is at most `t`, its proposer through the sync delay after the slot's update
    --
    (hHoldC : ∀ σ' : ℕ, tAwakeEnd ≤ M.slotStart S.C σ' → M.supportCutoff S.C (σ' + 1) ≤ t →
      ∀ u ∈ honestActiveAt M S A x σ', u ∈ S.P.committee σ' →
      u ∈ A.activeThroughout x ((M.dutyWindowStart S.C σ' : ℕ) : ℝ) (((M.supportCutoff S.C (σ' + 1) : ℕ) : ℝ) + Δs))
    (hHoldP : ∀ s : ℕ, tAwakeEnd ≤ M.slotStart S.C s → M.supportCutoff S.C (s + 1) ≤ t → HonestOpenerAt M S A x s →
      S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + Δs)) :
    RootCollisionAtOpening M S A x rs m ∨ RootCollisionHeldBy M S A x t ∨
      (FinalityIncludedBetween M S A x Δs tAwakeEnd t ∧
        FinalizedExtendedByHonestProposalsBetween M S A x Δs tAwakeEnd t) := by
  -- `4Δ(k + 1)` is at most `tAwakeEnd`: the honest round opening slots lie between `tGAT + 4Δ(3k + 1)` and
  -- `tAwakeEnd` (as in `lem98_healed_finality_liveness_ofSync`), so no proposal window start of a round after
  -- `tAwakeEnd` is cut at `0`
  have hEnd : 4 * Δ S * (S.C.k + 1) ≤ tAwakeEnd := by
    have hmono : ∀ i : ℕ, i ≤ m → rs 0 ≤ rs i := by
      intro i
      induction i with
      | zero => intro _; exact le_rfl
      | succ i ih => intro hi; exact le_trans (ih (by omega)) (hSeq.mono i (by omega)).le
    have hfirst := hSeq.first
    have hlast := hSeq.last
    unfold healFrontSlots at hfirst
    have h0m : M.slotStart S.C (rs 0 * S.C.R) ≤ M.slotStart S.C (rs m * S.C.R) :=
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
        (Nat.mul_le_mul_right _ (hmono m le_rfl))
    have hcm := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (rs m * S.C.R)
    have hvm := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (rs m * S.C.R)
    have hk : 4 * Δ S * (S.C.k + 1) ≤ 4 * Δ S * (3 * S.C.k + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  refine (lem98_healed_finality_liveness_ofSync M F U Fx) S A x R GST tGAT tAwakeEnd m rs hGST E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs
    Sy_F hΔs_F hHoldF hParent hThird hAwake hActive t ht hTicksBy hCommittees hCommitteesTick hSeq hStay hOpenings hAdvQ hParam ?_ hHoldQ hTickInputs hHold hHoldC hHoldP
  intro r' hr' u hu
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  have hpw := U.proposalWindowStart_eq S ((r' + 1) * S.C.R)
  have hss : M.slotStart S.C ((r' + 1) * S.C.R) = 4 * Δ S * (r' * S.C.R) + 4 * Δ S * S.C.R := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.add_mul,
      Nat.one_mul, Nat.mul_add]
  have hss1 : M.slotStart S.C (r' * S.C.R + 1) = 4 * Δ S * (r' * S.C.R) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add,
      Nat.mul_one]
  have hc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (r' * S.C.R + 1)
  have hv := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (r' * S.C.R + 1)
  have hk1 : 4 * Δ S * (S.C.k + 1) = 4 * Δ S * S.C.k + 4 * Δ S := by rw [Nat.mul_add, Nat.mul_one]
  have hk2 : 4 * Δ S * (S.C.k + 2) = 4 * Δ S * S.C.k + 8 * Δ S := by rw [Nat.mul_add]; omega
  have hR2 : 4 * Δ S * 2 ≤ 4 * Δ S * S.C.R := Nat.mul_le_mul_left _ hR
  -- the margins: the window opens at least `Δ S` after the duty window's start (or that start is `0`)
  -- and at least `Δ S` before the support cutoff of the next slot; both clock bounds are less than `Δ S`
  have hA := E.ahead_nonneg
  have hB := E.behind_nonneg
  -- the proposal window start of slot `(r' + 1) R` is not cut at `0`: slot `r' R` starts at or after `tAwakeEnd`
  have hs0 : M.slotStart S.C (r' * S.C.R) = 4 * Δ S * (r' * S.C.R) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
  have hpwN : M.proposalWindowStart S.C ((r' + 1) * S.C.R) + 4 * Δ S * (S.C.k + 1) =
      4 * Δ S * (r' * S.C.R) + 4 * Δ S * S.C.R + Δ S := by
    omega
  have hcN : M.supportCutoff S.C (r' * S.C.R + 1) = 4 * Δ S * (r' * S.C.R) + 6 * Δ S := by omega
  suffices hmem : u ∈ A.activeThroughout x (M.proposalWindowStart S.C ((r' + 1) * S.C.R))
      ((M.proposalWindowStart S.C ((r' + 1) * S.C.R) + Δs_F : ℕ) : ℝ) by
    rw [Nat.cast_add] at hmem; exact hmem
  refine (mem_activeThroughout_of_honestActiveAt M F) R E hu ?_ ?_
  · -- the protocol's duty window start of slot `r' R` is `4 Δ R − 4 Δ` before the proposal window start
    -- of slot `(r' + 1) R` (the latter cut to `0` when negative, so at least its formula), and
    -- `ΔClockBehind < Δ S ≤ 4 Δ R − 4 Δ`
    have hdr := duty_window_start_real S (r' * S.C.R)
    have hpwR : ((M.slotStart S.C ((r' + 1) * S.C.R) + Δ S : ℕ) : ℝ) - ((4 * Δ S * (S.C.k + 1) : ℕ) : ℝ) ≤
        ((M.proposalWindowStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ) := by
      rw [hpw]
      have h := (le_tsub_add : M.slotStart S.C ((r' + 1) * S.C.R) + Δ S ≤
        M.slotStart S.C ((r' + 1) * S.C.R) + Δ S - 4 * Δ S * (S.C.k + 1) + 4 * Δ S * (S.C.k + 1))
      have h' : ((M.slotStart S.C ((r' + 1) * S.C.R) + Δ S : ℕ) : ℝ) ≤
          ((M.slotStart S.C ((r' + 1) * S.C.R) + Δ S - 4 * Δ S * (S.C.k + 1) : ℕ) : ℝ) +
            ((4 * Δ S * (S.C.k + 1) : ℕ) : ℝ) := by exact_mod_cast h
      linarith
    rw [hss] at hpwR
    have hR2R : (2 : ℝ) ≤ S.C.R := by exact_mod_cast hR
    have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
    have h4R : (4 * Δ S * 2 : ℝ) ≤ 4 * Δ S * S.C.R := by
      apply mul_le_mul_of_nonneg_left hR2R; positivity
    push_cast at hpwR
    rw [hdr]
    push_cast
    linarith
  · -- one attestation sync delay after the window's start is more than `ΔClockAhead` before the support cutoff of
    -- slot `r' R + 1`: `hRk`
    have h1 : ((M.proposalWindowStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ) + 4 * Δ S * (S.C.k + 1) =
        4 * Δ S * (r' * S.C.R) + 4 * Δ S * S.C.R + Δ S := by exact_mod_cast hpwN
    have h2 : ((M.supportCutoff S.C (r' * S.C.R + 1) : ℕ) : ℝ) = 4 * Δ S * (r' * S.C.R) + 6 * Δ S := by
      exact_mod_cast hcN
    push_cast
    rw [h2]
    linarith

end GoldilocksCorrectness.Record.Proofs.Executions

