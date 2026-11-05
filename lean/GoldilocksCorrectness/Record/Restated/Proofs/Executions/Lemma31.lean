module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.DeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ReadingPointStatements
public import GoldilocksCorrectness.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Statements.Executions.ReadingPointStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma31, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma31.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: the votes of a validator's pool at its tick to the
support cutoff of slot `s + 1` are stamped before the late cutoff, and Lemma 31, two honest
confirmation updates of a slot save compatible blocks. The page's routine-level theorems are the facts' fields or have their twins in
phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq supportCutoff_cast
  supportCutoff_eq viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (expireLocks_keepsVotes tau_of_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (t_eq_mul)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- Every vote of a validator's slot-`s` pool at its tick to the support cutoff of slot `s + 1` is
stamped strictly before `S.C.t_ s + 6 · S.C.Δ`, when the validator is active from that cutoff less
`ΔClockAhead` up to that tick: its clock value before the tick is less than the cutoff
(`clockValue_lt_of_tick_of_active`), and a vote is stamped with the clock value after the step it
entered the pool (`voteStamp_entry_clock`), no larger (T-RC8-2).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, the run's facts, the environment's
  facts; `s`: the slot; `v`: the validator; `k`: the step of its tick to the support cutoff of slot
  `s + 1`.

Read aloud: every vote of `v`'s slot-`s` pool at its tick to the support cutoff of slot `s + 1` is
stamped strictly before `S.C.t_ s + 6 · S.C.Δ`. -/
theorem pool_vote_late_of_tick (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (s : ℕ) (v : V) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (k : ℕ) (hk : x.lbl k = Event.tick v (M.supportCutoff S.C (s + 1)))
    (hwin : ∀ j : ℕ, (M.supportCutoff S.C (s + 1) : ℝ) - ΔClockAhead ≤ x.time j → j ≤ k → v ∈ A.active j) :
    ∀ vote ∈ M.votesHeldSet (x.st k v) s, ∃ τ : Stamp,
      (x.st k v).voteStamp vote = some τ ∧
      τ < ((S.C.t_ s + 6 * S.C.Δ : Time) : Stamp) := by
  intro vote hvote
  have hΔ := one_le_Δ S
  have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hcv := clockValue_lt_of_tick_of_active M F E hk (by omega) hwin
  obtain ⟨e, he, -, -, hτ⟩ := (voteStamp_entry_clock M F) R E hvote
  refine ⟨_, hτ, ?_⟩
  have hle := E.clockValue_mono (show e + 1 ≤ k by omega) (E.not_mem_corrupted_of_tick hk)
  rw [(clock_eq_clockValue M F) x R (e + 1) v]
  have hcast : ((M.supportCutoff S.C (s + 1) : ℕ) : Int) = S.C.t_ s + 6 * S.C.Δ := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.t_eq_mul, GoldilocksCorrectness.Proofs.Routines.t_eq_mul]
    push_cast
    ring
  have hlt : ((x.clockValue (e + 1) v : ℕ) : Int) < S.C.t_ s + 6 * S.C.Δ := by
    rw [← hcast]
    exact_mod_cast lt_of_le_of_lt hle hcv
  exact_mod_cast hlt

/-- A vote of a validator's slot-`s` votes at its tick `k` to the clock value `t > 0` is stamped strictly
before `t`, when the validator is active after every step from the first one whose time is `t − ΔClockAhead`
up to `k`: the vote entered at an earlier step, stamped with the clock value after that step
(`voteStamp_entry_clock`), at most the clock value at `k` (`clockValue_mono`), which is less than `t`
(`clockValue_lt_of_tick_of_active`). The lines of Lemma 63's proof, as a kit theorem (T-RC10-1).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `k`: the step of the tick;
  `t`: its clock value; `v`: the validator; `s`: the slot; `vote`: the vote.

Read aloud: a vote held at a tick to `t`, by a validator active since `ΔClockAhead` before `t`, carries
a stamp less than `t`. -/
theorem voteStamp_lt_of_tick_of_active {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k t : ℕ} {v : V} {s : ℕ} {vote : GoldfishVote V}
    (hk : x.lbl k = Event.tick v t) (ht : 0 < t)
    (hwin : ∀ j : ℕ, (t : ℝ) - ΔClockAhead ≤ x.time j → j ≤ k → v ∈ A.active j)
    (hvote : vote ∈ M.votesHeldSet (x.st k v) s) :
    ∃ τ : Stamp, (x.st k v).voteStamp vote = some τ ∧ τ < (((t : ℕ) : Int) : Stamp) := by
  have hcv := clockValue_lt_of_tick_of_active M F E hk ht hwin
  obtain ⟨e, he, -, -, hτ⟩ := (voteStamp_entry_clock M F) R E hvote
  refine ⟨_, hτ, ?_⟩
  have hle := E.clockValue_mono (show e + 1 ≤ k by omega) (E.not_mem_corrupted_of_tick hk)
  rw [(clock_eq_clockValue M F) x R (e + 1) v]
  exact_mod_cast lt_of_le_of_lt hle hcv

/-- A vote of a validator's slot-`s` votes at its tick `k` to `t > 0` is among its late votes of slot `s`
(`LateVotes`, stamped strictly before `S.C.t_ s + 6 · S.C.Δ`) at its later tick `k'` to `t' ≥ t`, when it
is active after every step from the first one whose time is `t − ΔClockAhead` up to `k` and `t` is at
most `S.C.t_ s + 6 · S.C.Δ`: the vote is stamped strictly before `t` (`voteStamp_lt_of_tick_of_active`), and
votes and stamps are kept to every later step (`pool_mono`, `voteStamp_kept`), whatever the validator does
between the two ticks (T-RC10-1).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `k`, `k'`: the steps of the two
  ticks; `t`, `t'`: their clock values; `v`: the validator; `s`: the slot; `vote`: the vote.

Read aloud: a vote held at a tick to `t`, by a validator active since `ΔClockAhead` before `t`, is a late
vote at every later tick when `t` is at most the slot's late cutoff. -/
theorem mem_lateVotes_of_held_at_tick {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k k' t t' : ℕ} {v : V} {s : ℕ} {vote : GoldfishVote V}
    (hk : x.lbl k = Event.tick v t) (hk' : x.lbl k' = Event.tick v t') (htt : t ≤ t') (ht : 0 < t)
    (hwin : ∀ j : ℕ, (t : ℝ) - ΔClockAhead ≤ x.time j → j ≤ k → v ∈ A.active j)
    (hcut : ((t : ℕ) : Int) ≤ S.C.t_ s + 6 * S.C.Δ)
    (hvote : vote ∈ M.votesHeldSet (x.st k v) s) :
    vote ∈ GoldilocksCorrectness.Record.Statements.Routines.LateVotes M S.C (x.st k' v) s := by
  obtain ⟨τ, hτ, hlt⟩ := (voteStamp_lt_of_tick_of_active M F) R E hk ht hwin hvote
  have hkk : k ≤ k' := tick_step_le_of_le M F E hk hk' htt
  refine GoldilocksCorrectness.Record.Proofs.Routines.mem_lateVotes.2
    ⟨(pool_mono M F) x R E v hkk s hvote, τ, ?_, ?_⟩
  · rw [(voteStamp_kept M F) x R E v hkk hvote]
    exact hτ
  · have hc : (((t : ℕ) : Int) : Stamp) ≤ ((S.C.t_ s + 6 * S.C.Δ : Time) : Stamp) := by
      exact_mod_cast hcut
    exact lt_of_lt_of_le hlt hc

/-- **Lemma 31's core, from the reach to the earlier ticks.** Two confirmation updates of slot `s + 1`,
at `v₁`'s and `v₂`'s ticks `k₁`, `k₂` to the support cutoff of slot `s + 1`, save compatible blocks, when
each validator ticks to the view freeze of slot `s` (`kF₁`, `kF₂`) active from `ΔClockAhead` before it,
every vote resolving early (before the support cutoff of slot `s`) at one validator's update is among the
other's votes at its tick to the view freeze, or two votes of its validator are, and roots name blocks
until the later real time of the two ticks to the cutoff.

Why: the reached votes are stamped before the view freeze, so they are late votes at the tick to the
cutoff (`mem_lateVotes_of_held_at_tick`), and Lemma 30's helper form concludes; the two frame trees are
read at steps of honest validators at real times at most `supportCutoff (s + 1) + ΔClockBehind`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, the run's facts, the environment's
  facts; `s`: the slot confirmed; `v₁`, `v₂`: the two validators; `n₁'`, `n₂'`: the node states the two
  updates leave; `C₁`, `C₂`: the blocks saved; `kF₁`, `kF₂`, `k₁`, `k₂`: the ticks.

Read aloud: two updates at the cutoff whose early votes reached each other by the view freeze save
blocks of one chain. -/
theorem lem31_compatible_of_reach_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (v₁ v₂ : V) (n₁' n₂' : M.N)
    (C₁ C₂ : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (kF₁ : ℕ) (hkF₁ : x.lbl kF₁ = Event.tick v₁ (M.viewFreeze S.C s))
    (hwin₁ : ∀ j : ℕ, (M.viewFreeze S.C s : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kF₁ → v₁ ∈ A.active j)
    (kF₂ : ℕ) (hkF₂ : x.lbl kF₂ = Event.tick v₂ (M.viewFreeze S.C s))
    (hwin₂ : ∀ j : ℕ, (M.viewFreeze S.C s : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kF₂ → v₂ ∈ A.active j)
    (k₁ : ℕ) (hk₁ : x.lbl k₁ = Event.tick v₁ (M.supportCutoff S.C (s + 1)))
    (k₂ : ℕ) (hk₂ : x.lbl k₂ = Event.tick v₂ (M.supportCutoff S.C (s + 1)))
    (hRoots : RootsNameBlocksUntil M A x (max (x.time k₁) (x.time k₂)))
    (h12 : ∀ vote ∈ M.votesHeldSet (x.tickInput v₁ (M.supportCutoff S.C (s + 1))) s,
      (∃ y : Stamp, GoldilocksCorrectness.Record.Statements.Routines.ResolvesAt M (x.tickInput v₁ (M.supportCutoff S.C (s + 1))) vote y ∧
        occurrenceBefore (some y) ((M.supportCutoff S.C s : ℕ) : Int) = true) →
      vote ∈ M.votesHeldSet (x.tickInput v₂ (M.viewFreeze S.C s)) s ∨
        ∃ u₁ ∈ M.votesHeldSet (x.tickInput v₂ (M.viewFreeze S.C s)) s,
          ∃ u₂ ∈ M.votesHeldSet (x.tickInput v₂ (M.viewFreeze S.C s)) s,
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index)
    (h21 : ∀ vote ∈ M.votesHeldSet (x.tickInput v₂ (M.supportCutoff S.C (s + 1))) s,
      (∃ y : Stamp, GoldilocksCorrectness.Record.Statements.Routines.ResolvesAt M (x.tickInput v₂ (M.supportCutoff S.C (s + 1))) vote y ∧
        occurrenceBefore (some y) ((M.supportCutoff S.C s : ℕ) : Int) = true) →
      vote ∈ M.votesHeldSet (x.tickInput v₁ (M.viewFreeze S.C s)) s ∨
        ∃ u₁ ∈ M.votesHeldSet (x.tickInput v₁ (M.viewFreeze S.C s)) s,
          ∃ u₂ ∈ M.votesHeldSet (x.tickInput v₁ (M.viewFreeze S.C s)) s,
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index)
    (hUpdate₁ : ConfirmationUpdated M S.C S.P (x.tickInput v₁ (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n₁')
    (hSaved₁ : n₁'.savedConfirmation s = some C₁)
    (hUpdate₂ : ConfirmationUpdated M S.C S.P (x.tickInput v₂ (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n₂')
    (hSaved₂ : n₂'.savedConfirmation s = some C₂) :
    C₁.compatible C₂ = true := by
  have hΔ := one_le_Δ S
  have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hfr := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hfc : M.viewFreeze S.C s ≤ M.supportCutoff S.C (s + 1) := by omega
  have hfpos : 0 < M.viewFreeze S.C s := by omega
  have hcast : ((M.supportCutoff S.C (s + 1) : ℕ) : Int) = S.C.t_ s + 6 * S.C.Δ := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.t_eq_mul, GoldilocksCorrectness.Proofs.Routines.t_eq_mul]
    push_cast
    ring
  have hcut : ((M.viewFreeze S.C s : ℕ) : Int) ≤ S.C.t_ s + 6 * S.C.Δ := by
    rw [← hcast]; exact_mod_cast hfc
  have hti₁ : x.tickInput v₁ (M.supportCutoff S.C (s + 1)) = x.st k₁ v₁ := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk₁]
  have hti₂ : x.tickInput v₂ (M.supportCutoff S.C (s + 1)) = x.st k₂ v₂ := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk₂]
  have htiF₁ : x.tickInput v₁ (M.viewFreeze S.C s) = x.st kF₁ v₁ := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkF₁]
  have htiF₂ : x.tickInput v₂ (M.viewFreeze S.C s) = x.st kF₂ v₂ := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkF₂]
  -- the votes each validator holds at its tick to the view freeze are late votes at its tick to the cutoff
  have late₁ : ∀ u ∈ M.votesHeldSet (x.tickInput v₁ (M.viewFreeze S.C s)) s,
      u ∈ GoldilocksCorrectness.Record.Statements.Routines.LateVotes M S.C
        (x.tickInput v₁ (M.supportCutoff S.C (s + 1))) s := by
    intro u hu
    rw [htiF₁] at hu
    rw [hti₁]
    exact (mem_lateVotes_of_held_at_tick M F) R E hkF₁ hk₁ hfc hfpos hwin₁ hcut hu
  have late₂ : ∀ u ∈ M.votesHeldSet (x.tickInput v₂ (M.viewFreeze S.C s)) s,
      u ∈ GoldilocksCorrectness.Record.Statements.Routines.LateVotes M S.C
        (x.tickInput v₂ (M.supportCutoff S.C (s + 1))) s := by
    intro u hu
    rw [htiF₂] at hu
    rw [hti₂]
    exact (mem_lateVotes_of_held_at_tick M F) R E hkF₂ hk₂ hfc hfpos hwin₂ hcut hu
  -- the roots name blocks across the two frame trees, held by honest validators at their ticks to the cutoff
  have hRoots₁₂ : RootsNameBlocksIn
      ((M.fg_to_ac (x.tickInput v₁ (M.supportCutoff S.C (s + 1)))).tree ∪
        (M.fg_to_ac (x.tickInput v₂ (M.supportCutoff S.C (s + 1)))).tree) := by
    have hin : ∀ B ∈ (M.fg_to_ac (x.tickInput v₁ (M.supportCutoff S.C (s + 1)))).tree ∪
        (M.fg_to_ac (x.tickInput v₂ (M.supportCutoff S.C (s + 1)))).tree,
        inHonestTreeBy M A x (max (x.time k₁) (x.time k₂)) B := by
      intro B hB
      rcases Finset.mem_union.1 hB with hB | hB
      · refine ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := k₁) (v := v₁) (E.not_mem_corrupted_of_tick hk₁) (le_max_left _ _) (?_))
        rw [← hti₁]
        exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hB).1
      · refine ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := k₂) (v := v₂) (E.not_mem_corrupted_of_tick hk₂) (le_max_right _ _) (?_))
        rw [← hti₂]
        exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hB).1
    exact fun B hB B' hB' hroot => hRoots B B' (hin B hB) (hin B' hB') hroot
  rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U)] at h12 h21
  -- Lemma 30's helper form
  exact (GoldilocksCorrectness.Record.Statements.Routines.lem30_saved_confirmations_compatible_of_lateReach F)
    C₁ C₂ (Nat.le_add_left 1 s) hRoots₁₂
    (by
      rw [Nat.add_sub_cancel]
      intro vote hvote hres
      rcases h12 vote hvote hres with h | ⟨u₁, h₁, u₂, h₂, hne, hi₁, hi₂⟩
      · exact Or.inl (late₂ _ h)
      · exact Or.inr ⟨u₁, late₂ _ h₁, u₂, late₂ _ h₂, hne, hi₁, hi₂⟩)
    (by
      rw [Nat.add_sub_cancel]
      intro vote hvote hres
      rcases h21 vote hvote hres with h | ⟨u₁, h₁, u₂, h₂, hne, hi₁, hi₂⟩
      · exact Or.inl (late₁ _ h)
      · exact Or.inr ⟨u₁, late₁ _ h₁, u₂, late₁ _ h₂, hne, hi₁, hi₂⟩)
    hUpdate₁ (by rw [Nat.add_sub_cancel]; exact hSaved₁) hUpdate₂
    (by rw [Nat.add_sub_cancel]; exact hSaved₂)

/-- **Lemma 31, two honest confirmation updates of a slot save compatible blocks.** In an
execution synchronous from the support cutoff of slot `s`, the confirmation updates of slot
`s + 1`, for the slot `s`, from the node states of `v₁` and `v₂` at their ticks to the support cutoff of
slot `s + 1`, that save `C₁` and `C₂` as the confirmation of slot `s`, save compatible blocks, when
each validator is awake and honest from the support cutoff of slot `s` to its view freeze and honest
at the support cutoff of slot `s + 1`.

Why: Lemma 30. A vote resolving early at one validator was held there before the support cutoff
of slot `s`, was re-sent then, and reaches the other within one delay, while it is awake; every
pool vote before the update is stamped before it; the two frame trees hold only blocks of honest
validators, where a root names one block.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot confirmed;
- `v₁`, `v₂`: the two validators; `n₁'`, `n₂'`: the node states the two updates leave;
- `C₁`, `C₂`: the blocks saved.

Read aloud: in a synchronous execution from the support cutoff of slot `s`, if two validators,
each awake and honest from that cutoff for one delay and ticking to the cutoff where the update for slot `s` runs,
have that update save `C₁` and `C₂`, then `C₁` and `C₂` are on one chain.

Roots name blocks until the later real time of the two ticks to the support cutoff of slot `s + 1`: the
proof compares the blocks of the two
frame trees on `v₁`'s and `v₂`'s states before the support cutoff of slot `s + 1`. -/
theorem lem31_saved_confirmations_compatible (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (v₁ v₂ : V) (n₁' n₂' : M.N)
    (C₁ C₂ : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    -- the network is synchronous from the support cutoff of slot `s` on
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s)
    -- `v₁` ticks to the view freeze of slot `s` at `kF₁`, and is active at every step up to that tick
    -- whose real time is at least `ΔClockAhead` before `M.viewFreeze S.C s − max (3 * Δ S) Δs`, and at every
    -- step whose real time is in the sync delay after the earliest re-send
    (kF₁ : ℕ) (hkF₁ : x.lbl kF₁ = Event.tick v₁ (M.viewFreeze S.C s))
    (hwin₁ : ∀ i : ℕ, (M.viewFreeze S.C s : ℝ) - max (3 * Δ S) Δs - ΔClockAhead ≤ x.time i → i ≤ kF₁ →
      v₁ ∈ A.active i)
    (hv₁₀ : v₁ ∈ A.activeThroughout x ((M.viewFreeze S.C s) - (max (Δ S) Δs)) (((M.viewFreeze S.C s) - (max (Δ S) Δs)) + Δs))
    -- `v₂` ticks to the view freeze of slot `s` at `kF₂`, and is active at every step up to that tick
    -- whose real time is at least `ΔClockAhead` before `M.viewFreeze S.C s − max (3 * Δ S) Δs`, and at every
    -- step whose real time is in the sync delay after the earliest re-send
    (kF₂ : ℕ) (hkF₂ : x.lbl kF₂ = Event.tick v₂ (M.viewFreeze S.C s))
    (hwin₂ : ∀ i : ℕ, (M.viewFreeze S.C s : ℝ) - max (3 * Δ S) Δs - ΔClockAhead ≤ x.time i → i ≤ kF₂ →
      v₂ ∈ A.active i)
    (hv₂₀ : v₂ ∈ A.activeThroughout x ((M.viewFreeze S.C s) - (max (Δ S) Δs)) (((M.viewFreeze S.C s) - (max (Δ S) Δs)) + Δs))
    -- `v₁` and `v₂` tick to the support cutoff of slot `s + 1` at `k₁`, `k₂`, where their updates run
    -- (the read point, T-RC10-1,)
    (k₁ : ℕ) (hk₁ : x.lbl k₁ = Event.tick v₁ (M.supportCutoff S.C (s + 1)))
    (k₂ : ℕ) (hk₂ : x.lbl k₂ = Event.tick v₂ (M.supportCutoff S.C (s + 1)))
    -- a root names one block among what honest validators hold, until the later real time of the two
    -- ticks to the support cutoff of slot `s + 1`
    (hRoots : RootsNameBlocksUntil M A x (max (x.time k₁) (x.time k₂)))
    -- the confirmation update of slot `s + 1` at `v₁`'s tick to the support cutoff of slot `s + 1` leaves `n₁'`,
    -- which saves `C₁` as the confirmation of slot `s`
    (hUpdate₁ : ConfirmationUpdated M S.C S.P (x.tickInput v₁ (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n₁')
    (hSaved₁ : n₁'.savedConfirmation s = some C₁)
    -- likewise at `v₂`
    (hUpdate₂ : ConfirmationUpdated M S.C S.P (x.tickInput v₂ (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n₂')
    (hSaved₂ : n₂'.savedConfirmation s = some C₂) :
    -- then `C₁` and `C₂` are compatible
    C₁.compatible C₂ = true := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hss2 : M.slotStart S.C (s + 2) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1), Nat.mul_add, Nat.mul_add]
    omega
  have hv₁t : M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hc : M.supportCutoff S.C s = M.voteTime S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have hv₂t : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have ht₂ : M.supportCutoff S.C (s + 1) = M.voteTime S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have hfr : M.viewFreeze S.C s = M.slotStart S.C s + 3 * Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hfr' : M.supportCutoff S.C s + Δ S = M.viewFreeze S.C s := by omega
  have hfrR : ((M.viewFreeze S.C s : ℕ) : ℝ) = (M.supportCutoff S.C s : ℝ) + Δ S := by
    rw [← hfr']; push_cast; ring
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hscs : (M.slotStart S.C s : ℝ) < (M.supportCutoff S.C s : ℝ) := by
    exact_mod_cast (show M.slotStart S.C s < M.supportCutoff S.C s by omega)
  have h3a := le_max_left (3 * Δ S) Δs
  have h3b := le_max_right (3 * Δ S) Δs
  have h1a := le_max_left (Δ S) Δs
  have h1b := le_max_right (Δ S) Δs
  have hm1le : max (Δ S) Δs ≤ M.viewFreeze S.C s := by omega
  -- each validator's window, from one clock-ahead bound before `M.viewFreeze S.C s − max (3 * Δ S) Δs`, contains
  -- the window from one clock-ahead bound before the support cutoff of slot `s`, and Lemma 62's
  have hmR : (M.viewFreeze S.C s : ℝ) - max (3 * Δ S) Δs - ΔClockAhead ≤ (M.supportCutoff S.C s : ℝ) - ΔClockAhead := by
    have : (3 * Δ S : ℝ) ≤ ((max (3 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast le_max_left (3 * Δ S) Δs
    linarith
  have hlow : (M.viewFreeze S.C s : ℝ) - max (3 * Δ S) Δs ≤
      min (((M.supportCutoff S.C s : ℕ) : ℝ) + Δ S - max (Δ S) Δs) (M.slotStart S.C s) := by
    have h3 : ((max (Δ S) Δs : ℕ) : ℝ) ≤ ((max (3 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast max_le_max (by omega) le_rfl
    have h4 : (3 * Δ S : ℝ) ≤ ((max (3 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast le_max_left (3 * Δ S) Δs
    have hfR : ((M.viewFreeze S.C s : ℕ) : ℝ) = (M.slotStart S.C s : ℝ) + 3 * Δ S := by
      rw [hfr]; push_cast; ring
    exact le_min (by linarith) (by linarith)
  have hw₁ : ∀ j : ℕ, (M.supportCutoff S.C s : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kF₁ → v₁ ∈ A.active j :=
    fun j hj hjk => hwin₁ j (le_trans hmR hj) hjk
  have hw₂ : ∀ j : ℕ, (M.supportCutoff S.C s : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kF₂ → v₂ ∈ A.active j :=
    fun j hj hjk => hwin₂ j (le_trans hmR hj) hjk
  have hkF₁T := (E.tick_active kF₁ v₁ _ hkF₁).2.1
  have hkF₂T := (E.tick_active kF₂ v₂ _ hkF₂).2.1
  obtain ⟨kₑ₁, hkₑ₁, -, -⟩ := E.tick_of_active (M.supportCutoff S.C s) (by omega) v₁ fun j hj1 hj2 =>
    hw₁ j hj1 ((lt_of_time_lt M) x R (by linarith)).le
  obtain ⟨kₑ₂, hkₑ₂, -, -⟩ := E.tick_of_active (M.supportCutoff S.C s) (by omega) v₂ fun j hj1 hj2 =>
    hw₂ j hj1 ((lt_of_time_lt M) x R (by linarith)).le
  -- the early votes of each validator reach the other by its tick to the view freeze (Lemma 62, each way)
  have h12 := (lem62_early_vote_reaches_at M F U) S A x R GST s (M.supportCutoff S.C s)
    (M.supportCutoff S.C (s + 1)) (M.viewFreeze S.C s) (M.viewFreeze S.C s) v₁ v₂ (E.upTo _) hNet hSkew hRedeliver (Sy.upTo _)
    (by omega) (by omega) kF₂ (by rw [hfr']; exact hkF₂)
    (fun i hi hik => hwin₂ i (by linarith [hlow]) hik) (by omega) kF₂ hkF₂
    (by rw [hfr', Nat.cast_sub hm1le]; exact hv₁₀) kₑ₁ hkₑ₁ k₁ hk₁ (by omega)
  have h21 := (lem62_early_vote_reaches_at M F U) S A x R GST s (M.supportCutoff S.C s)
    (M.supportCutoff S.C (s + 1)) (M.viewFreeze S.C s) (M.viewFreeze S.C s) v₂ v₁ (E.upTo _) hNet hSkew hRedeliver (Sy.upTo _)
    (by omega) (by omega) kF₁ (by rw [hfr']; exact hkF₁)
    (fun i hi hik => hwin₁ i (by linarith [hlow]) hik) (by omega) kF₁ hkF₁
    (by rw [hfr', Nat.cast_sub hm1le]; exact hv₂₀) kₑ₂ hkₑ₂ k₂ hk₂ (by omega)
  exact (lem31_compatible_of_reach_at M F U) S A x R s v₁ v₂ n₁' n₂' C₁ C₂ E
    kF₁ hkF₁ (fun j hj hjk => hw₁ j (by linarith) hjk) kF₂ hkF₂ (fun j hj hjk => hw₂ j (by linarith) hjk)
    k₁ hk₁ k₂ hk₂ hRoots h12 h21 hUpdate₁ hSaved₁ hUpdate₂ hSaved₂

/-- Lemma 31 for a slot that starts after `GST`: two honest confirmation updates of slot `s + 1`
save compatible confirmations of slot `s`, when the network is synchronous from the start of slot
`s`, each validator is active from that start to the view freeze of slot `s` and honest at the
support cutoff of slot `s + 1`. No sync fact and no sync delay.

Why: `Lemma31.lean`'s proof, with Lemma 62 read through
`lem62_early_vote_reaches_of_slotStart_at` in each direction.

Read aloud: when slot `s` starts after `GST`, two validators active since it started, ticking to the cutoff where
the update for slot `s` runs, have that update save blocks of one chain.
 -/
theorem lem31_saved_confirmations_compatible_of_slotStart (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (v₁ v₂ : V) (n₁' n₂' : M.N)
    (C₁ C₂ : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)

    -- the network is synchronous from the start of slot `s`
    (hGST : GST ≤ M.slotStart S.C s)
    -- `v₁` is active from `tStart₁`, more than both clock bounds before the start of slot `s`, up to
    -- its own tick to the view freeze of slot `s` (, Lemma 62's slot-start form), and from
    -- the start of slot `s` to its view freeze (the holder's window) (T-RC5-3)
    (tStart₁ : ℤ) (htStart₁ : (tStart₁ : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    (hv₁ : v₁ ∈ A.activeThroughoutToTick x tStart₁ (M.viewFreeze S.C s))
    (hv₁₀ : v₁ ∈ A.activeThroughout x (M.slotStart S.C s) (M.viewFreeze S.C s))
    -- `v₂` is active from `tStart₂`, more than both clock bounds before the start of slot `s`, up to
    -- its own tick to the view freeze of slot `s` (, Lemma 62's slot-start form), and from
    -- the start of slot `s` to its view freeze (the holder's window) (T-RC5-3)
    (tStart₂ : ℤ) (htStart₂ : (tStart₂ : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    (hv₂ : v₂ ∈ A.activeThroughoutToTick x tStart₂ (M.viewFreeze S.C s))
    (hv₂₀ : v₂ ∈ A.activeThroughout x (M.slotStart S.C s) (M.viewFreeze S.C s))
    -- `v₁` and `v₂` tick to the support cutoff of slot `s + 1` at `k₁`, `k₂`, where their updates run
    -- (the read point, T-RC10-1,)
    (k₁ : ℕ) (hk₁ : x.lbl k₁ = Event.tick v₁ (M.supportCutoff S.C (s + 1)))
    (k₂ : ℕ) (hk₂ : x.lbl k₂ = Event.tick v₂ (M.supportCutoff S.C (s + 1)))
    -- a root names one block among what honest validators hold, until the later real time of the two
    -- ticks to the support cutoff of slot `s + 1`
    (hRoots : RootsNameBlocksUntil M A x (max (x.time k₁) (x.time k₂)))
    (hUpdate₁ : ConfirmationUpdated M S.C S.P (x.tickInput v₁ (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n₁')
    (hSaved₁ : n₁'.savedConfirmation s = some C₁)
    (hUpdate₂ : ConfirmationUpdated M S.C S.P (x.tickInput v₂ (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n₂')
    (hSaved₂ : n₂'.savedConfirmation s = some C₂) :
    C₁.compatible C₂ = true := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hss2 : M.slotStart S.C (s + 2) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1), Nat.mul_add, Nat.mul_add]
    omega
  have hv₁t : M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hc : M.supportCutoff S.C s = M.voteTime S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have hv₂t : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have ht₂ : M.supportCutoff S.C (s + 1) = M.voteTime S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have hfr : M.viewFreeze S.C s = M.slotStart S.C s + 3 * Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hfr' : M.supportCutoff S.C s + Δ S = M.viewFreeze S.C s := by omega
  have hfrR : ((M.viewFreeze S.C s : ℕ) : ℝ) = (M.supportCutoff S.C s : ℝ) + Δ S := by
    rw [← hfr']; push_cast; ring
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hscs : (M.slotStart S.C s : ℝ) < (M.supportCutoff S.C s : ℝ) := by
    exact_mod_cast (show M.slotStart S.C s < M.supportCutoff S.C s by omega)
  -- each validator's ticks to the view freeze of slot `s` and to the support cutoff of slot `s`
  obtain ⟨kF₁, hkF₁, hw₁⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv₁
    (t₀ := (M.supportCutoff S.C s : ℝ) - ΔClockAhead) (by linarith)
  obtain ⟨kF₂, hkF₂, hw₂⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv₂
    (t₀ := (M.supportCutoff S.C s : ℝ) - ΔClockAhead) (by linarith)
  have hkF₁T := (E.tick_active kF₁ v₁ _ hkF₁).2.1
  have hkF₂T := (E.tick_active kF₂ v₂ _ hkF₂).2.1
  obtain ⟨kₑ₁, hkₑ₁, -, -⟩ := E.tick_of_active (M.supportCutoff S.C s) (by omega) v₁ fun j hj1 hj2 =>
    hw₁ j hj1 ((lt_of_time_lt M) x R (by linarith)).le
  obtain ⟨kₑ₂, hkₑ₂, -, -⟩ := E.tick_of_active (M.supportCutoff S.C s) (by omega) v₂ fun j hj1 hj2 =>
    hw₂ j hj1 ((lt_of_time_lt M) x R (by linarith)).le
  -- the early votes of each validator reach the other by its tick to the view freeze (Lemma 62's slot-start
  -- form, each way)
  have h12 := (lem62_early_vote_reaches_of_slotStart_at M F U) S A x R GST s (M.supportCutoff S.C s)
    (M.supportCutoff S.C (s + 1)) (M.viewFreeze S.C s) (M.viewFreeze S.C s) v₁ v₂ (E.upTo _) hNet hSkew hRedeliver
    hGST (by omega) tStart₂ htStart₂ (by rw [hfr']; exact hv₂) (by omega) kF₂ hkF₂ kₑ₁ hkₑ₁ k₁ hk₁ (by omega)
  have h21 := (lem62_early_vote_reaches_of_slotStart_at M F U) S A x R GST s (M.supportCutoff S.C s)
    (M.supportCutoff S.C (s + 1)) (M.viewFreeze S.C s) (M.viewFreeze S.C s) v₂ v₁ (E.upTo _) hNet hSkew hRedeliver
    hGST (by omega) tStart₁ htStart₁ (by rw [hfr']; exact hv₁) (by omega) kF₁ hkF₁ kₑ₂ hkₑ₂ k₂ hk₂ (by omega)
  exact (lem31_compatible_of_reach_at M F U) S A x R s v₁ v₂ n₁' n₂' C₁ C₂ E
    kF₁ hkF₁ (fun j hj hjk => hw₁ j (by linarith) hjk) kF₂ hkF₂ (fun j hj hjk => hw₂ j (by linarith) hjk)
    k₁ hk₁ k₂ hk₂ hRoots h12 h21 hUpdate₁ hSaved₁ hUpdate₂ hSaved₂

end GoldilocksCorrectness.Record.Proofs.Executions

