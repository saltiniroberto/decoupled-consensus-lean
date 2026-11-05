module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89FastBase
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89f
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Unforgeability
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodFastSupport
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma80
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma32
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ChainState
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma79
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma42
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma31
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealingStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedAttestationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.PhaseKitStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.SleepyStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Executions.Lemma89FastFamily
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89FastFamily, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89FastFamily.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: part A of Lemma 89 on the
fast-confirmation route, namely the bundle `PartAHyps` of its hypotheses, the line sources made from
the first honest fast block, the induction of the slot invariant relative to every line source, and
one line from the first honest fast block. The page's routine-level theorems are the facts' fields
or have their twins in phase A. For `PartAHyps` and `LineInv` the recovery section states maps from
the landed definitions to the record's (`goldilocks_PartAHyps_of_landed`,
`goldilocks_LineInv_of_landed`) in place of equations: the record's bundle takes a node state where
the landed one takes the landed update's answer, and the record's slot invariant reads the outcomes
of a tick from an awake state where the landed one reads the answers of the revocation.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff
  dutyWindowStart_le_voteTime dutyWindowStart_mono dutyWindowStart_of_anchor
  dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq slotStart_mono slot_eq_of_mem
  supportCutoff_cast supportCutoff_eq supportCutoff_lt supportCutoff_mono supportCutoff_succ_times
  tGAT_le_slotStart t_lt_of_lt times_eq viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both compatible_symm')

open GoldilocksCorrectness.Proofs.Routines (duty_window_start_lt_supportCutoff)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Proofs.Executions (mem_awakeThroughout_of_forall)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated LocksRevoked)

open GoldilocksCorrectness.Record.Statements.Routines (FrameShape ProgressCertOn)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)
open GoldilocksCorrectness.Statements.Routines (expireLocks RootsNameBlocksIn)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  ancestorEq_antisymm compatible_iff compatible_of_ancestorEq_compatible)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## The kit: the tick that saved a confirmation or added a lock entry -/

/-- **The tick that added a lock entry.** A lock entry `e` of `v`'s node state before `t`, whose
deadline names slot `s`, was added at `v`'s tick to the support cutoff of slot `s + 1`: the step
`x.tickStep v (M.supportCutoff S.C (s + 1))` is that tick.

Why: Lemma 39's trace of the entry (`lockTracedAfterTick_of_mem`) names that tick; the deadline fixes
its slot (`active_of_lock_entry`'s argument).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `E`: the
  environment's facts; `t`: the time; `v`: the validator; `e`: the
  entry; `s`: the slot its deadline names.

Read aloud: a held lock entry was added at the validator's tick to the support cutoff of the slot
after the one its deadline names. -/
theorem tick_of_lock_entry (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (t : ℕ) (v : V) (e : M.LE)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)

    (he : e ∈ (x.stateBefore t v).lockEntries) (s : ℕ)
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ) :
    x.lbl (x.tickStep v (M.supportCutoff S.C (s + 1))) = Event.tick v (M.supportCutoff S.C (s + 1)) := by
  obtain ⟨s₀, hd₀, -, hlab, -⟩ :=
    (lockTracedAfterTick_of_mem M F U) S A x R E v (x.stepBefore t) e he
  have h1 : S.C.t_ (s + S.C.k) = S.C.t_ (s₀ + S.C.k) := add_right_cancel (hd.symm.trans hd₀)
  have hs : s = s₀ := by
    rcases lt_trichotomy s s₀ with h | h | h
    · have := GoldilocksCorrectness.Proofs.Routines.t_lt_of_lt S (show s + S.C.k < s₀ + S.C.k by omega)
      rw [h1] at this
      exact absurd this (lt_irrefl _)
    · exact h
    · have := GoldilocksCorrectness.Proofs.Routines.t_lt_of_lt S (show s₀ + S.C.k < s + S.C.k by omega)
      rw [h1] at this
      exact absurd this (lt_irrefl _)
  subst hs
  exact hlab

/-- **The tick that saved a confirmation.** A confirmation of slot `s'` saved in `v`'s node state
before `t` was saved at `v`'s tick to the support cutoff of slot `s' + 1`: the step
`x.tickStep v (M.supportCutoff S.C (s' + 1))` is that tick.

Why: Lemma 40's trace of the saved confirmation (`savedTracedAfterTick`) names that tick.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `E`: the
  environment's facts; `t`: the time; `v`: the validator; `s'`: the
  slot of the confirmation; `C'`: the block.

Read aloud: a saved confirmation was saved at the validator's tick to the next slot's support
cutoff. -/
theorem tick_of_saved_confirmation (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (t : ℕ) (v : V) (s' : ℕ) (C' : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)

    (hSaved : (x.stateBefore t v).savedConfirmation s' = some C') :
    x.lbl (x.tickStep v (M.supportCutoff S.C (s' + 1))) =
      Event.tick v (M.supportCutoff S.C (s' + 1)) := by
  obtain ⟨-, hlab, -⟩ :=
    (savedTracedAfterTick M F U) S A x R E v s' C' (x.stepBefore t) hSaved
  exact hlab

/-- **An outcome of a tick to a support cutoff, read off the tick.** When `v` ticks to the support
cutoff of slot `s + 1` from a node state awake since a time at most the duty window's start of that
slot, the tick has an outcome from `v`'s node state before the cutoff, and that node state is awake
for slot `s + 1`.

Why: `update_state_of_tick`'s first two conclusions.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `hWS`: the trace is
  wake-shaped; `s`: the slot; `v`: the validator; `τ`: its wake time; `i`: the tick's step.

Read aloud: a validator's tick to a support cutoff, past the wake test, has an outcome. -/
theorem cutoff_tick_outcome_of_tick (U : UniformSchedule M.toSlotLayout) {S : Setup V}
    {A : Activity V} (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
 (s : ℕ) (v : V) (τ : Time) {i : ℕ}
    (hl : x.lbl i = Event.tick v (M.supportCutoff S.C (s + 1)))
    (hτ : (x.tickInput v (M.supportCutoff S.C (s + 1))).awakeSince = some τ)
    (hτle : τ ≤ duty_window_start S.C (s + 1)) :
    ∃ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) ∧
      GoldilocksCorrectness.Record.Statements.Routines.AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1) := by
  obtain ⟨n'', sent, hrun, hAw, -⟩ :=
    (update_state_of_tick M F U) S A x R s v E hl ⟨τ, hτ, hτle⟩
  exact ⟨n'', sent, hrun, hAw⟩

/-- A step whose real time is less than `c` comes before the first step whose real time reaches `c`.

The variables:
- `M`: the model; `F`: its facts; `R`, `E`: the run's and the environment's facts (every time is reached); `c`: the time;
  `k`: the step.

Read aloud: a step before the time `c` is before the first step at `c`. -/
theorem lt_firstAt_of_time_lt {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {c k : ℕ} (hk : x.time k < (c : ℝ)) : k < x.firstAt c := by
  classical
  have hex : ∃ i : ℕ, (c : ℝ) ≤ x.time i := E.time_div c
  have hfa : x.firstAt c = Nat.find hex := by
    unfold Trace.firstAt
    rw [dif_pos hex]
  by_contra hge
  have h1 : x.firstAt c ≤ k := Nat.le_of_not_lt hge
  have h2 := Nat.find_spec hex
  rw [← hfa] at h2
  have h3 := (time_mono M) x R h1
  linarith

/-- A step before the first step whose real time reaches `c` is at a real time less than `c`.

The variables:
- `M`: the model; `F`: its facts; `E`: the environment's facts (every time is reached); `c`: the time; `k`: the step.

Read aloud: every step before the first step at `c` is before `c`. -/
theorem time_lt_of_lt_firstAt {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {c k : ℕ} (hk : k < x.firstAt c) : x.time k < (c : ℝ) := by
  classical
  have hex : ∃ i : ℕ, (c : ℝ) ≤ x.time i := E.time_div c
  have hfa : x.firstAt c = Nat.find hex := by
    unfold Trace.firstAt
    rw [dif_pos hex]
  rw [hfa] at hk
  exact not_le.1 (Nat.find_min hex hk)

/-- The first step whose real time reaches `c` is at or before every step whose real time is at least `c`.

The variables:
- `M`: the model; `F`: its facts; `R`, `E`: the run's and the environment's facts; `c`: the time; `k`: the step.

Read aloud: the first step at `c` is no later than any step at or after `c`. -/
theorem firstAt_le_of_time_ge {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {c k : ℕ} (hk : (c : ℝ) ≤ x.time k) : x.firstAt c ≤ k := by
  classical
  have hex : ∃ i : ℕ, (c : ℝ) ≤ x.time i := ⟨k, hk⟩
  have hfa : x.firstAt c = Nat.find hex := by
    unfold Trace.firstAt
    rw [dif_pos hex]
  rw [hfa]
  exact Nat.find_min' hex hk

/-- **The step form of `hOld` before a step `i`, when every step before `i` is at a real time whose sum with
`ΔClockAhead` is less than `aR M S r`.** Every attestation put on the wire by a tick at a step before `i`, by a
validator outside the adversary set at `tAwakeEnd`, has height at most `H₂`.

Why: a tick at a step before `i` is to a clock value at most that time plus
`ΔClockAhead` (`tick_active`), less than `aR M S r`; a validator outside the adversary set at `tAwakeEnd` is outside it
at `aR M S r`; `hOld` bounds the attestation.

The variables:
- `M`: the model; `F`: its facts; `R`, `E`: the run's and the environment's facts; `r`: the round; `H₂`: the bound;
  `tAwakeEnd`: the phase's end; `i`: the step.

Read aloud: before a step earlier than any tick to `aR M S r` can be, every honest attestation has height at most
`H₂`. -/
theorem oldStep_of_clock {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {r H₂ tAwakeEnd : ℕ} (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hEnd : aR M S r ≤ tAwakeEnd) {i : ℕ}
    (hi : ∀ k : ℕ, k < i → x.time k + ΔClockAhead < ((aR M S r : ℕ) : ℝ)) :
    ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < i → x.lbl k = Event.tick u t →
      u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂ := by
  intro k t u a' hk hl hu hs
  have h1 := (E.tick_active k u t hl).2.1
  have h2 := hi k hk
  refine hOld k t u a' hl ?_ ((not_mem_corruptedAtTime_of_le M) x R E hEnd hu) hs
  linarith

/-- **A tick to the support cutoff of slot `μ + 1` is at a real time at most `t`, when the support cutoff of slot
`μ + 2` is at most `t`.**

Why: the tick is at a real time at most its clock value plus `ΔClockBehind` (`tick_active`), less than that cutoff plus
one delay `Δ S` (`hSkew`), which is at most the support cutoff of slot `μ + 2` (`supportCutoff_succ_eq`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `E`: the environment's facts; `μ`: the slot; `t`: the
  bound; `u`, `k`: the validator and the step of the tick.

Read aloud: a tick to a slot's support cutoff happens no later than any time at or after the next slot's support
cutoff. -/
theorem time_le_of_tick_supportCutoff (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {μ t : ℕ} (hEnd : M.supportCutoff S.C (μ + 2) ≤ t)
    {u : V} {k : ℕ} (hk : x.lbl k = Event.tick u (M.supportCutoff S.C (μ + 1))) : x.time k ≤ t := by
  have hkt := (E.tick_active _ _ _ hk).2.2
  have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (μ + 1)
  rw [show μ + 1 + 1 = μ + 2 from rfl] at h1
  have hc : ((M.supportCutoff S.C (μ + 1) : ℕ) : ℝ) + Δ S ≤ (t : ℕ) := by
    exact_mod_cast (show M.supportCutoff S.C (μ + 1) + Δ S ≤ t by omega)
  have hA0 := E.ahead_nonneg
  linarith

/-- **A3 read at the read step.** `finalized_ancestor_of_fast_block` with its bound on the old attestations asked only
before the read step `i`, not up to `v`'s tick `k₀`: the proof reads that bound only through A2 at `i`.

The variables: as `finalized_ancestor_of_fast_block`'s.

Read aloud: when no honest attestation of height more than `H₂` was sent before the read step, the finalized block
read there is the fast block or an ancestor of it. -/
theorem finalized_ancestor_of_fast_block_le (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (tAwakeEnd r H₂ k₀ i : ℕ) (v w : V) (L : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
      {tR : ℕ} (hRoots : RootsNameBlocksUntil M A x tR) (htR : x.time k₀ ≤ tR)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hk₀ : x.lbl k₀ = Event.tick v (aR M S r))
    (hOld : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < i → x.lbl k = Event.tick u t →
      u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂)
    (hEnd : x.time k₀ ≤ tAwakeEnd)
    (hLv : L ∈ (x.tickInput v (aR M S r)).tree)
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (hi : i ≤ k₀) (hw : w ∉ A.corrupted i) :
    (x.st i w).finalized.AncestorEq L := by
  obtain ⟨B, hB, hF⟩ := (finalizedFromChain_of_exec M F) S A x R E i w
  have hik := (time_mono M) x R hi
  have hBh := (held_height_le_before_action M F Fx) S A x R E tAwakeEnd H₂ i i w B hThird
    hOld (hik.trans hEnd) le_rfl hB
  obtain ⟨-, hj, hFj⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B).1
  have hlt : (M.chainStateOf S.C B).h_F < (M.chainStateOf S.C L).h := by
    rw [hL]
    exact lt_of_le_of_lt hFj (lt_of_lt_of_le hj hBh)
  have hT : A.AdversaryFewerThanThirdUntil x (validator_count V) (max (x.time i) (x.time k₀)) :=
    hThird.mono (max_le (hik.trans hEnd) hEnd)
  have hv' : v ∉ A.corrupted k₀ := E.not_mem_corrupted_of_tick hk₀
  have hLv' : L ∈ (x.st k₀ v).tree := by
    have h : x.tickInput v (aR M S r) = x.st k₀ v := by
      unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk₀]
    rw [← h]; exact hLv
  have hFL := (lem68_honest_past_finalized M F Fx) S A x R E hRoots i k₀ w v B L hT hw hv' hB hLv' hlt
    (max_le (hik.trans htR) htR)
  rw [hF]
  exact hFL

/-! ## The hypotheses of part A, bundled -/

/-- `PartAHyps M S Sched x GST tGAT tAwakeEnd r H₂ v L n'`: the hypotheses of A5 `fast_block_base`
but its bound on the phase's end, with the update of `v` at the action time `aR M S r` read as a
node state `n'` the record's update leaves from `v`'s node state before that time
(`ConfirmationUpdated`, the shape of Lemma 31's twin), with `L` among its fast blocks; the landed
bundle reads the answer `A'` of the landed update in its place, and `fast_block_base`'s twin an
outcome of `v`'s tick there, which gives `n'` (`confirmationUpdated_of_phase_tick`).

Roots name blocks until `tAwakeEnd`: the phase's end; each kit theorem reads blocks held up to the
end time its own hypothesis `hEnd` bounds by `tAwakeEnd`.

The variables:
- `M`: the model.

Read aloud: the hypotheses of the base at the slot after the fast block's round, but its bound on
the phase's end, bundled. -/
structure PartAHyps (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V) (n' : M.N) (Δs : ℕ) (release : (NamedObject V) → Option ℕ) (ΔRedeliver : ℕ) (ΔClockAhead ΔClockBehind : ℝ) (ΔNet : ℕ) : Prop where
  /-- The run's facts on the trace. -/
  R : RunFacts M S x
  /-- The environment's facts on the trace, for the delay `(Δ S)` from `GST`. -/
  E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST release acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks
  /-- The network delay and the two clock bounds fit in the delay `Δ S`. -/
  hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S
  /-- The two clock bounds together are less than one delay `Δ S`. -/
  hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S
  /-- A re-delivery after the receiver's clock reaches an object's release clock value, plus both clock bounds, fits in one delay `Δ S`. -/
  hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S
  /-- What an honest validator active at a time `t` would serve at `t` reaches every validator active
  from `t` within `Δs` of the later of `t` and `GST`. -/
  Sy : SyncedWithin A x (servesMin M S.C) acObject release ΔRedeliver Δs GST
  /-- The sync delay is at most the protocol's slow window less three delays. -/
  hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k
  hRoots : RootsNameBlocksUntil M A x tAwakeEnd
  hParent : ParentHeldAtDelivery M x
  hGST : GST ≤ tGAT
  hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd
  hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
    v ∉ A.corrupted i → v ∈ A.awake i
  /-- At every slot of the phase, every validator honest at the slot's update is an honest active validator and an
  updater of the slot. -/
  hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
    ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
      v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s
  hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd
  hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1)
  hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂
  hv : v ∉ A.corruptedAtTime x (aR M S r)
  hUpdate : ConfirmationUpdated M S.C S.P (x.tickInput v (aR M S r)) ((aR M S r : ℕ) : Int)
    (r * S.C.R + 1) n'
  hFast : L ∈ M.fastBlocks n'
  hL : (M.chainStateOf S.C L).h = H₂ + 1
  /-- The action time of round `r` is in the phase: `cert_source` reads the quorum
  member outside the adversary set up to it. -/
  hEnd : aR M S r ≤ tAwakeEnd
  /-- `v` ticks to the action time of round `r`, at the step `x.tickStep v (aR M S r)`. -/
  hk₀ : x.lbl (x.tickStep v (aR M S r)) = Event.tick v (aR M S r)
  /-- Every attestation put on the wire by a tick at a step before the first step whose real time reaches the support
  cutoff of slot `r * R`, by a validator outside the adversary set at `tAwakeEnd`, has height at most `H₂`. -/
  hOldStep : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < x.firstAt (M.supportCutoff S.C (r * S.C.R)) → x.lbl k = Event.tick u t →
    u ∉ A.corruptedAtTime x tAwakeEnd →
    (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂
  /-- `v`'s tick to `aR M S r` is in the phase. -/
  hEndStep : x.time (x.tickStep v (aR M S r)) ≤ tAwakeEnd

/-! ## The line sources -/

/-- `LineSource M S Sched x r H₂ μ X`: `X` is an ancestor of, or equal to, a block `X₀` on the
confirmation `C₀` of slot `μ` saved by the update of a member `u` of `updaterAt M S A x μ`, with: `μ`
the first slot of round `r`, `X₀` fast in that update and of chain-state height `H₂ + 1`; or
`μ ≥ r * R + 1` and `X₀` fast or passing the slow test in that update; or `μ ≥ r * R + k`. The
member's update is read as a node state `n₀` the record's update of slot `μ + 1` leaves from `u`'s
tick input at its support cutoff (`ConfirmationUpdated`); at the spec's model it is the landed
answer (`goldilocks_LineSource`).

The variables:
- `M`: the model.

Read aloud: `X` is on the chain of a block that a member's update of slot `μ` saved as its
confirmation and made fast or passed by the slow test, of the kind the slot allows. -/
def LineSource (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (r H₂ μ : ℕ) (X : Block V) : Prop :=
  ∃ u ∈ updaterAt M S A x μ, ∃ (n₀ : M.N) (C₀ X₀ : Block V),
    ConfirmationUpdated M S.C S.P (x.tickInput u (M.supportCutoff S.C (μ + 1)))
      ((M.supportCutoff S.C (μ + 1) : ℕ) : Int) (μ + 1) n₀ ∧
    M.savedConfirmation n₀ μ = some C₀ ∧
    M.savedConfirmation (x.tickOutput u (M.supportCutoff S.C (μ + 1))) μ = some C₀ ∧
    X.AncestorEq X₀ ∧ X₀.AncestorEq C₀ ∧
    ((μ = r * S.C.R ∧ X₀ ∈ M.fastBlocks n₀ ∧ (M.chainStateOf S.C X₀).h = H₂ + 1) ∨
      (r * S.C.R + 1 ≤ μ ∧ (X₀ ∈ M.fastBlocks n₀ ∨
        M.slow_test S.C (x.tickInput u (M.supportCutoff S.C (μ + 1))) μ X₀ = true)) ∨
      r * S.C.R + S.C.k ≤ μ)

/-- `LineInv M S Sched x r H₂ σ`: at slot `σ`, the slot invariant relative to every line source
of a slot before `σ`.

The variables:
- `M`: the model.

The second conjunct reads the confirmation of slot `σ` that every updater of slot `σ` saved at its own
tick to the support cutoff of slot `σ + 1` (`updaterAt`: active up to that tick, nothing asked after it).

Read aloud: at slot `σ`, the slot invariant holds relative to every line source of a slot before
`σ`, and the confirmation every updater of slot `σ` saved at its tick extends the source. -/
def LineInv (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (r H₂ σ : ℕ) : Prop :=
  ∀ μ X, LineSource M S A x r H₂ μ X → μ + 1 ≤ σ →
    HonestChainExtends M S A x (Hon M S A x σ) X σ ∧
    ∀ u ∈ updaterAt M S A x σ, ∀ C' : Block V,
      (x.tickOutput u (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' → X.AncestorEq C'

theorem LineSource.slot_ge {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N}
    {r H₂ μ : ℕ} {X : Block V} (h : LineSource M S A x r H₂ μ X) : r * S.C.R ≤ μ := by
  obtain ⟨_u, _hu, _A₀, _C₀, _X₀, -, -, -, -, -, hk⟩ := h
  rcases hk with ⟨h1, -⟩ | ⟨h1, -⟩ | h1 <;> omega

theorem LineSource.anc {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    {r H₂ μ : ℕ} {X Y : Block V} (h : LineSource M S A x r H₂ μ X) (hYX : Y.AncestorEq X) :
    LineSource M S A x r H₂ μ Y := by
  obtain ⟨u, hu, A₀, C₀, X₀, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨u, hu, A₀, C₀, X₀, h1, h2, h3, ancestorEq_trans hYX h4, h5, h6⟩

/-! ## The kit: a saved confirmation read off the update -/

/-- At the support cutoff of slot `s + 1`, an outcome of `v`'s tick from its node state before the
cutoff, awake for slot `s + 1`, is a node state the confirmation update of slot `s + 1` leaves
(the field `tick_supportCutoff_confirmation` of `F.tk2`, from the node invariant, Lemma 11).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `s`: the slot; `v`: the validator; `n₀`, `sent`: the outcome;
- `hrun`: `(n₀, sent)` is an outcome of `v`'s tick at the cutoff from its node state before it;
  `hAw`: that node state has been awake since the duty window's start of slot `s + 1`.

Read aloud: the tick at the support cutoff runs the confirmation update, from an awake state. -/
theorem confirmationUpdated_of_cutoff_tick (U : UniformSchedule M.toSlotLayout) {S : Setup V}
    {A : Activity V} (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (v : V) (n₀ : M.N)
    (sent : List (NamedObject V))
    (hrun : .ok (n₀, sent) ∈ M.tick S.C S.P S.X (x.stateBefore (M.supportCutoff S.C (s + 1)) v)
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
    (hAw : AwakeFor M S.C (x.stateBefore (M.supportCutoff S.C (s + 1)) v) (s + 1)) :
    ConfirmationUpdated M S.C S.P (x.stateBefore (M.supportCutoff S.C (s + 1)) v)
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n₀ := by
  have hInv : M.nodeInvCore S.C S.P S.X (x.stateBefore (M.supportCutoff S.C (s + 1)) v) :=
    (lem11_node_invariantCore_of_run M F S x R (x.stepBefore (M.supportCutoff S.C (s + 1))) v).1
  have hsl : S.C.slot ((M.supportCutoff S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S s).1
  have h := F.tk2.tick_supportCutoff_confirmation_of_core S.C S.P S.X _ _ n₀ sent hrun hInv
    (by rw [hsl]; exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout
      F.sched U) S (s + 1))
    (by rw [hsl]; exact hAw)
  rw [hsl] at h
  exact h

/-- Two node states the confirmation update of slot `s ≥ 1` leaves from one node state have the same
fast blocks: they save the same confirmation (`confirmationUpdated_saved_eq`), and the fast blocks
are read off the saved confirmation when no live lock entry vetoes it, none otherwise.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`: the parameters; `n`: the node state before the update; `n₁`, `n₂`: two node states
  after it; `t`: the time; `s`: the slot; `B`: the block;
- `hs`: the slot is not the first; `h₁`, `h₂`: `n₁` and `n₂` are what the update leaves from `n`;
  `hB`: `B` is a fast block of `n₁`.

Read aloud: every outcome of the update marks the same fast blocks. -/
theorem fast_of_confirmationUpdated {C : Config} {P : Provisional V} {n n₁ n₂ : M.N} {t : Time}
    {s : Slot} {B : Block V} (hs : 1 ≤ s) (h₁ : ConfirmationUpdated M C P n t s n₁)
    (h₂ : ConfirmationUpdated M C P n t s n₂) (hB : B ∈ M.fastBlocks n₁) :
    B ∈ M.fastBlocks n₂ := by
  obtain ⟨H', hH', hveto, hBT, hBg, hBH, hft⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.confirmationUpdated_fast_cases hs h₁ hB
  have hH₂ := (confirmationUpdated_saved_eq M F) hs h₁ h₂ hH'
  obtain ⟨-, -, -, hv0⟩ := GoldilocksCorrectness.Record.Proofs.Routines.confirmationUpdated_saved_some hs h₂ hH₂
  exact ((hv0 hveto).2.1 B).2 ⟨hBT, hBg, hBH, hft⟩

/-- At the vote time of slot `s`, an outcome of `w`'s tick from its node state before the vote time,
awake for slot `s`, is a node state the revocation of slot `s` leaves (the field
`tick_voteTime_locks` of `F.tk2`, from the node invariant, Lemma 11).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `s`: the slot; `w`: the validator; `n''`, `sent`: the outcome;
- `hrun`: `(n'', sent)` is an outcome of `w`'s tick at the vote time from its node state before it;
  `hAw`: that node state has been awake since the duty window's start of slot `s`.

Read aloud: the tick at the vote time runs the revocation, from an awake state. -/
theorem locksRevoked_of_vote_tick (U : UniformSchedule M.toSlotLayout) {S : Setup V}
    {A : Activity V} (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (w : V) (n'' : M.N)
    (sent : List (NamedObject V))
    (hrun : .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.stateBefore (M.voteTime S.C s) w)
      ((M.voteTime S.C s : ℕ) : Int))
    (hAw : AwakeFor M S.C (x.stateBefore (M.voteTime S.C s) w) s) :
    LocksRevoked M S.P (x.stateBefore (M.voteTime S.C s) w) ((M.voteTime S.C s : ℕ) : Int) s
      n'' := by
  have hΔ := one_le_Δ S
  have hInv : M.nodeInvCore S.C S.P S.X (x.stateBefore (M.voteTime S.C s) w) :=
    (lem11_node_invariantCore_of_run M F S x R (x.stepBefore (M.voteTime S.C s)) w).1
  have hsl : S.C.slot ((M.voteTime S.C s : ℕ) : Int) = s := by
    have hvs := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
    have hsss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
        (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add,
        Nat.mul_one]
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (by omega)
      (by omega)
  have h := F.tk2.tick_voteTime_locks_of_core S.C S.P S.X _ _ n'' sent hrun hInv
    (by rw [hsl]; exact (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched
      U S s))
    (by rw [hsl]; exact hAw)
  rw [hsl] at h
  exact h

/-- At the vote time of slot `s`, an outcome of `w`'s tick from its tick input to that vote time, awake for slot `s`, is
a node state the revocation of slot `s` leaves (the field `tick_voteTime_locks_of_core` of `F.tk2`, from the node
invariant's core). `locksRevoked_of_vote_tick` read at the tick input.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `s`: the slot; `w`: the validator; `n''`, `sent`: the outcome;
- `hrun`: `(n'', sent)` is an outcome of `w`'s tick to the vote time from its tick input;
  `hAw`: that node state has been awake since the duty window's start of slot `s`.

Read aloud: the tick to the vote time runs the revocation, from an awake state. -/
theorem locksRevoked_of_vote_tickInput (U : UniformSchedule M.toSlotLayout) {S : Setup V}
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (w : V) (n'' : M.N)
    (sent : List (NamedObject V))
    (hrun : .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
      ((M.voteTime S.C s : ℕ) : Int))
    (hAw : AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s) :
    LocksRevoked M S.P (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) s
      n'' := by
  have hΔ := one_le_Δ S
  have hInv : M.nodeInvCore S.C S.P S.X (x.tickInput w (M.voteTime S.C s)) :=
    (lem11_node_invariantCore_of_run M F S x R (x.tickStep w (M.voteTime S.C s)) w).1
  have hsl : S.C.slot ((M.voteTime S.C s : ℕ) : Int) = s := by
    have hvs := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
    have hsss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
        (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add,
        Nat.mul_one]
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (by omega)
      (by omega)
  have h := F.tk2.tick_voteTime_locks_of_core S.C S.P S.X _ _ n'' sent hrun hInv
    (by rw [hsl]; exact (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched
      U S s))
    (by rw [hsl]; exact hAw)
  rw [hsl] at h
  exact h

/-- In the phase of part A, an outcome of `v`'s tick at the action time of round `r` from its tick input is a node
state the confirmation update of slot `r * R + 1` leaves, when `v` is an updater of slot `r * R` (`updaterAt`: it
ticks to `aR M S r`, and is awake and outside the adversary set from the duty window's start of slot `r * R + 1` up to
that tick).

Why: the tick input is awake for slot `r * R + 1` (`tickInput_awakeSince_of_mem_activeThroughoutToTick`), and the
tick at the support cutoff runs the update from it (`confirmationUpdated_of_cutoff_tickInput`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `r`: the round; `v`: the validator; `n'`, `sent`: the outcome;
- `hupd`: `v` is an updater of slot `r * R`; `hUpdate`: `(n', sent)` is an outcome of `v`'s tick at the action time.

Read aloud: an updater's tick at a round's action time runs the update. -/
theorem confirmationUpdated_of_phase_tick (U : UniformSchedule M.toSlotLayout) {S : Setup V}
    {A : Activity V} (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (r : ℕ) (v : V)
    (n' : M.N) (sent : List (NamedObject V))
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hupd : v ∈ updaterAt M S A x (r * S.C.R))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
      ((aR M S r : ℕ) : Int)) :
    ConfirmationUpdated M S.C S.P (x.tickInput v (aR M S r)) ((aR M S r : ℕ) : Int)
      (r * S.C.R + 1) n' := by
  have hAw := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hupd
    ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout
      F.sched U) S (r * S.C.R + 1))
  exact (confirmationUpdated_of_cutoff_tickInput M F U) x R (r * S.C.R) v n' sent hUpdate hAw

/-- The state right after the support cutoff of slot `s + 1` saves, for slot `s`, what the
confirmation update of slot `s + 1` saved (in a node state `n₀` the record's update leaves from the
validator's tick input at the cutoff, `ConfirmationUpdated`), when the validator is in
`updaterAt M S A x s` (awake and honest from the duty window's start of slot `s + 1` to its tick to
that cutoff).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: after the support cutoff, the node state saves what the update at that cutoff saved. -/
theorem state_saved_of_update (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (v : V) (n₀ : M.N)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hw : v ∈ updaterAt M S A x s)
    (hUpd : ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n₀) :
    M.savedConfirmation (x.tickOutput v (M.supportCutoff S.C (s + 1))) s =
      M.savedConfirmation n₀ s := by
  -- the tick to the cutoff the step took runs the update from its tick input (`update_state_of_tick`), whose
  -- saved confirmations the tick output keeps; two outcomes of the update from one node state save the same
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hw
  obtain ⟨n'', sent, hrun, hAw, hsave, -, -, -⟩ := (update_state_of_tick M F U) S A x R s v E hk'
    ((tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hw
      ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout
        F.sched U) S (s + 1)))
  have hCU := (confirmationUpdated_of_cutoff_tickInput M F U) x R s v n'' sent hrun hAw
  have hs1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  show (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = M.savedConfirmation n₀ s
  rw [hsave]
  cases h₀ : M.savedConfirmation n₀ s with
  | some H =>
    have := (confirmationUpdated_saved_eq M F) hs1 hUpd hCU (by rw [Nat.add_sub_cancel]; exact h₀)
    rw [Nat.add_sub_cancel] at this
    exact this
  | none =>
    cases h₂ : M.savedConfirmation n'' s with
    | none => rfl
    | some H =>
      have := (confirmationUpdated_saved_eq M F) hs1 hCU hUpd (by rw [Nat.add_sub_cancel]; exact h₂)
      rw [Nat.add_sub_cancel] at this
      exact absurd (h₀.symm.trans this) (by simp)

/-- **The bundle of part A from the assemblies' hypotheses.** The hypotheses the A7 and A8 assemblies take (the
execution's facts, the phase's premises, `hOld`, `v` honest at `aR M S r`, an outcome `(n', sent)` of `v`'s tick at
`aR M S r` from its tick input with `L` among the fast blocks of `n'`, `h(L) = H₂ + 1`), with the support cutoff of
slot `r * R + 2` in the phase, give `PartAHyps`.

Why: `hActive` at slot `r * R` (its duty window starts one delay after `tGAT`, `hAnchor`) makes `v` an updater of slot
`r * R`, so `v` ticks to `aR M S r` (`hk₀`), at a real time at most `aR M S r + ΔClockBehind`, less than the support
cutoff of slot `r * R + 2` (`hEndStep`); the tick runs the update (`confirmationUpdated_of_phase_tick`); every step
before the first step reaching the support cutoff of slot `r * R` is at a real time less than that cutoff, four delays
before `aR M S r`, so `hOld` bounds its honest attestations (`oldStep_of_clock`, `hOldStep`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; the rest as `PartAHyps`' fields;
- `hE2`: the support cutoff of slot `r * R + 2` is at most `tAwakeEnd`.

Read aloud: the assemblies' hypotheses give the bundle of part A once the phase reaches the slot after the fast
block's update. -/
theorem PartAHyps.of_tick (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V}
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    {n' : M.N} {sent : List (NamedObject V)}
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (hE2 : M.supportCutoff S.C (r * S.C.R + 2) ≤ tAwakeEnd) :
    PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind
      ΔNet := by
  classical
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have h12 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S
    (r * S.C.R + 1)
  rw [show r * S.C.R + 1 + 1 = r * S.C.R + 2 from rfl] at h12
  have h01 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S
    (r * S.C.R)
  have haR : aR M S r = M.supportCutoff S.C (r * S.C.R + 1) := rfl
  have hEnd : aR M S r ≤ tAwakeEnd := by omega
  have hdws := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S
    tGAT (r * S.C.R) hAnchor
  have hupd : v ∈ updaterAt M S A x (r * S.C.R) := (hActive (r * S.C.R) (by omega) hEnd v hv).2
  obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hupd
  have hkS : x.tickStep v (aR M S r) = k := (tickStep_eq_of_lbl M) x E hk
  have hk₀ : x.lbl (x.tickStep v (aR M S r)) = Event.tick v (aR M S r) := by
    rw [hkS]
    exact hk
  have hkt := (E.tick_active _ v _ hk₀).2.2
  refine
    { R := R, E := E, hNet := hNet, hSkew := hSkew, hRedeliver := hRedeliver, Sy := Sy, hΔs := hΔs,
      hRoots := hRoots, hParent := hParent, hGST := hGST, hThird := hThird, hAwake := hAwake,
      hActive := hActive, hCommittees := hCommittees, hAnchor := hAnchor, hOld := hOld, hv := hv,
      hUpdate := (confirmationUpdated_of_phase_tick M F U) x R r v n' sent E hupd hUpdate,
      hFast := hFast, hL := hL, hEnd := hEnd, hk₀ := hk₀,
      hOldStep := (oldStep_of_clock M F) R E hOld hEnd (fun k' hk' => ?_),
      hEndStep := ?_ }
  · have h1 := (time_lt_of_lt_firstAt M F (S := S)) E hk'
    have h4 : ((M.supportCutoff S.C (r * S.C.R) : ℕ) : ℝ) + 4 * Δ S ≤ ((aR M S r : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (r * S.C.R) + 4 * Δ S ≤ aR M S r by omega)
    linarith
  · have h4 : ((aR M S r : ℕ) : ℝ) + Δ S ≤ ((tAwakeEnd : ℕ) : ℝ) := by
      exact_mod_cast (show aR M S r + Δ S ≤ tAwakeEnd by omega)
    linarith

namespace PartAHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}

/-- A validator honest at `t₀ ≤ tAwakeEnd` is awake and honest at every `t` from `tGAT` to `t₀`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: a validator honest at a time of the phase is awake and honest from `tGAT` to it. -/
theorem window {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {u : V} {t₀ : ℕ}
    (hu : u ∉ A.corruptedAtTime x t₀) (h₀ : t₀ ≤ tAwakeEnd) :
    u ∈ A.activeThroughout x tGAT t₀ :=
  (mem_activeThroughout_of_hAwake_honest_at M F) P.R P.E P.hAwake le_rfl h₀ hu

/-- The duty window of every slot from `r * R` on starts after `tGAT`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: the duty window of every slot from round `r` on starts after `tGAT` and one delay. -/
theorem dws (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {s : ℕ}
    (hs : r * S.C.R ≤ s) : tGAT + Δ S ≤ M.dutyWindowStart S.C s :=
  le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT (r * S.C.R) P.hAnchor) ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S hs)

/-- A member of `Hon M S Sched s`, `s ≥ r * R`, with the support cutoff of slot `s + 1` in the
phase, is awake and honest from `tGAT` to that cutoff.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: a member of a slot from round `r` on is awake and honest from `tGAT` to the support
cutoff of the next slot. -/
theorem member {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {s : ℕ} {u : V}
    (hu : u ∈ Hon M S A x s) (hEnd : M.supportCutoff S.C (s + 1) ≤ tAwakeEnd) :
    u ∈ A.activeThroughout x tGAT (M.supportCutoff S.C (s + 1)) := by
  unfold Hon roundMembers at hu
  exact P.window M F (Finset.mem_sdiff.1 hu).2 hEnd

/-- A member of `Hon M S Sched s`, `s ≥ r * R`, is awake and honest from the duty window's start of
slot `s + 1` to the support cutoff of slot `s + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: a member of a slot from round `r` on is awake and honest through the duty window of the
next slot up to its support cutoff. -/
theorem member1 (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {s : ℕ} {u : V}
    (hs : r * S.C.R ≤ s) (hu : u ∈ Hon M S A x s)
    (hEnd : M.supportCutoff S.C (s + 1) ≤ tAwakeEnd) :
    u ∈ A.activeThroughout x (M.dutyWindowStart S.C (s + 1)) (M.supportCutoff S.C (s + 1)) := by
  exact Activity.mem_activeThroughout_of_le (by have := P.dws M F U (show r * S.C.R ≤ s + 1 by omega); norm_cast; omega) le_rfl (P.member M F hu hEnd)

/-- A member of `Hon M S Sched s`, `s ≥ r * R`, is awake and honest from the duty window's start of
slot `s` to the support cutoff of slot `s + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: a member of a slot from round `r` on is awake and honest from the duty window's start of
the slot to the support cutoff of the next slot. -/
theorem member0 (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {s : ℕ} {u : V}
    (hs : r * S.C.R ≤ s) (hu : u ∈ Hon M S A x s)
    (hEnd : M.supportCutoff S.C (s + 1) ≤ tAwakeEnd) :
    u ∈ A.activeThroughout x (M.dutyWindowStart S.C s) (M.supportCutoff S.C (s + 1)) := by
  exact Activity.mem_activeThroughout_of_le (by have := P.dws M F U (show r * S.C.R ≤ s by omega); norm_cast; omega) le_rfl (P.member M F hu hEnd)

/-- A member of `Hon M S Sched s`, `s ≥ r * R`, with the support cutoff of slot `s + 1` in the
phase, is an updater of slot `s` (the bundle's `hActive`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: a member of a slot from round `r` on ran that slot's update awake and honest up to its own
tick. -/
theorem memberU (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {s : ℕ} {u : V}
    (hs : r * S.C.R ≤ s) (hu : u ∈ Hon M S A x s)
    (hEnd : M.supportCutoff S.C (s + 1) ≤ tAwakeEnd) :
    u ∈ updaterAt M S A x s := by
  have hdw := P.dws M F U hs
  unfold Hon roundMembers at hu
  exact (P.hActive s (by omega) hEnd u (Finset.mem_sdiff.1 hu).2).2

/-- `GST` is at most the duty window's start, the vote time and the support cutoff of every slot
from `r * R` on.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: `GST` comes no later than the duty window's start, the vote time and the support cutoff
of every slot from round `r` on. -/
theorem gst (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {s : ℕ}
    (hs : r * S.C.R ≤ s) : GST ≤ M.dutyWindowStart S.C s ∧ GST ≤ M.voteTime S.C s ∧
      GST ≤ M.supportCutoff S.C s := by
  have h1 := P.dws M F U hs
  have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_le_voteTime M.toSlotLayout F.sched) S s
  have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have h4 := P.hGST
  omega

/-- `GST` is at least one delay or one sync delay before the view freeze and the support cutoff of
every slot from `r * R` on; `tGAT` is that much and three delays more before the vote time.

Why: `tGAT + Δ` is at most the duty window's start (`dws`), which is `4 Δ k` before the vote time,
and `Δs + 3 Δ ≤ 4 Δ k`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: the network is synchronous one sync delay before the view freeze of every slot from
round `r` on. -/
theorem gstSync (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {s : ℕ}
    (hs : r * S.C.R ≤ s) : tGAT + max (Δ S) Δs + 3 * Δ S ≤ M.voteTime S.C s ∧
      GST + max (Δ S) Δs ≤ M.viewFreeze S.C s ∧ GST + max (Δ S) Δs ≤ M.supportCutoff S.C s := by
  have h1 := P.dws M F U hs
  have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S s
  have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have h5 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have h6 := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have h7 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  -- the bundle's sync bound without the two (nonnegative) clock bounds, over the natural numbers
  have h8 : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have hd := P.hΔs
    have hA := P.E.ahead_nonneg
    have hB := P.E.behind_nonneg
    have hR : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hR
  have h9 := Nat.mul_le_mul_left (4 * Δ S) S.C.k_ge_two
  have h4 := P.hGST
  have h10 := one_le_Δ S
  rcases max_cases (Δ S) Δs with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] at h8 ⊢ <;> omega

/-- The holder lines of Lemma 42 at a slot `μ` of the round: a member `u` of slot `μ`
is active from the recovery delay before the view freeze of `μ` through the support cutoff of `μ`,
and a validator `w` awake and honest from `tGAT` through the support cutoff of slot `μ + 2` is active
from the recovery delay before the support cutoff of slot `μ + 1` through the vote time of slot
`μ + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the bundle; `μ`: the slot; `u`, `w`: the two validators.

Read aloud: a member of a slot of the round, and a validator awake through the phase, are active
through the two windows Lemma 42 reads. -/
theorem lem42_windows (U : UniformSchedule M.toSlotLayout) {Δs : ℕ}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {μ : ℕ} {u w : V}
    (hμ : r * S.C.R ≤ μ) (hu : u ∈ Hon M S A x μ) (hEnd1 : M.supportCutoff S.C (μ + 1) ≤ tAwakeEnd)
    (hwin : w ∈ A.activeThroughout x tGAT (M.supportCutoff S.C (μ + 2))) :
    u ∈ A.activeThroughout x ((M.viewFreeze S.C μ) - (max (Δ S) Δs))
        (M.supportCutoff S.C μ) ∧
      w ∈ A.activeThroughout x ((M.supportCutoff S.C (μ + 1)) - (max (Δ S) Δs))
        (M.voteTime S.C (μ + 1)) := by
  have hG := (P.gstSync M F U hμ).1
  obtain ⟨hv0, hc0, hf0, hs0, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ
  obtain ⟨hv1, hc1, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 1)
  have hc2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (μ + 2)
  have hv2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (μ + 2)
  have hsm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show μ + 1 ≤ μ + 2 by omega)
  have hmx1 := le_max_left (Δ S) Δs
  exact ⟨Activity.mem_activeThroughout_of_le (by rw [le_sub_iff_add_le]; norm_cast; omega) (by norm_cast; omega) (P.member M F hu hEnd1),
    Activity.mem_activeThroughout_of_le (by rw [le_sub_iff_add_le]; norm_cast; omega) (by norm_cast; omega) hwin⟩

/-- The fast block `L` is a line source of slot `r * R`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: the fast block `L` is a line source of the round's first slot. -/
theorem source_L (R : RunFacts M S x) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (hEnd : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd) :
    LineSource M S A x r H₂ (r * S.C.R) L := by
  have hvH : v ∈ Hon M S A x (r * S.C.R) := by
    unfold Hon roundMembers
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, P.hv⟩
  have hU : ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (r * S.C.R + 1)))
      ((M.supportCutoff S.C (r * S.C.R + 1) : ℕ) : Int) (r * S.C.R + 1) n' := P.hUpdate
  have hvU : v ∈ updaterAt M S A x (r * S.C.R) := P.memberU M F U le_rfl hvH hEnd
  obtain ⟨C', hC', hLC'⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_fast_block_saved
      (Nat.le_add_left 1 _) hU P.hFast
  rw [Nat.add_sub_cancel] at hC'
  have hst := (state_saved_of_update M F U) S A x R (r * S.C.R) v n' P.E
    hvU hU
  exact ⟨v, hvU, n', C', L, hU, hC', hst.trans hC', ancestorEq_refl L, hLC',
    Or.inl ⟨rfl, P.hFast, P.hL⟩⟩

/-- A block on a member's confirmation of a slot `σ ≥ r * R + k` is a line source of slot `σ`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: a block on a member's confirmation of a slot `k` or more past the round's first is a
line source of that slot. -/
theorem source_conf (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ} {u : V}
    {C X : Block V} (hσ : r * S.C.R + S.C.k ≤ σ) (hu : u ∈ Hon M S A x σ)
    (hEnd : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd)
    (hC : (x.tickOutput u (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C)
    (hXC : X.AncestorEq C) : LineSource M S A x r H₂ σ X := by
  have huU : u ∈ updaterAt M S A x σ := P.memberU M F U (by omega) hu hEnd
  obtain ⟨n₀, sent, hrun, hAw, hS⟩ := (update_of_saved_confirmation_of_updater M F U) S A x R σ u C P.E
    huU hC
  exact ⟨u, huU, n₀, C, C, (confirmationUpdated_of_cutoff_tickInput M F U) x R σ u n₀ sent hrun hAw, hS, hC,
    hXC, ancestorEq_refl C, Or.inr (Or.inr hσ)⟩

/-- A lock entry `u` holds in its tick input to the clock value `t`, honest up to the real time `t`, is of a slot `μ` whose update ran before `t`,
on `u`'s confirmation of slot `μ`; and its block is a line source of slot `μ` when
`μ ≥ r * R + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: a lock entry an honest validator holds is on its confirmation of the lock's slot, and
its block is a line source when that slot is after the round's first. -/
theorem source_lock (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {t : ℕ} {u : V}
    {e : M.LE} (hu : u ∉ A.corruptedAtTime x t) (hEnd : t ≤ tAwakeEnd)
    (he : e ∈ (x.tickInput u t).lockEntries) :
    ∃ μ : ℕ, e.d = S.C.t_ (μ + S.C.k) + 5 * S.C.Δ ∧ M.supportCutoff S.C (μ + 1) < t ∧
      (∃ C' : Block V,
        (x.tickOutput u (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C' ∧
        e.B.AncestorEq C') ∧
      (r * S.C.R + 1 ≤ μ → LineSource M S A x r H₂ μ e.B) := by
  obtain ⟨μ, hd, hcut, hC⟩ := (lock_entry_confirmation M F U) S A x R t u e E he
  refine ⟨μ, hd, hcut, hC, fun hμ => ?_⟩
  have he' : e ∈ (x.st (x.tickStep u t) u).lockEntries := he
  obtain ⟨μ', hd', -, hl, ⟨τ, hτ, hτle⟩, hprov⟩ :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem39_lock_entry_provenance M F U) S A x R
      (x.tickStep u t) u e E he'
  have hμμ : μ' = μ := by
    have h1 : S.C.t_ (μ' + S.C.k) = S.C.t_ (μ + S.C.k) := add_right_cancel (hd'.symm.trans hd)
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := GoldilocksCorrectness.Proofs.Routines.t_lt_of_lt S (show μ' + S.C.k < μ + S.C.k by omega)
      rw [h1] at this
      exact lt_irrefl _ this
    · have := GoldilocksCorrectness.Proofs.Routines.t_lt_of_lt S (show μ + S.C.k < μ' + S.C.k by omega)
      rw [h1] at this
      exact lt_irrefl _ this
  subst hμμ
  obtain ⟨n₀, sent, hrun, hA, -⟩ := (update_state_of_tick M F U) S A x R μ' u E hl ⟨τ, hτ, hτle⟩
  obtain ⟨e₀, -, -, -, -, ⟨C₀, hC₀, he₀C₀⟩, hkind, heB₀, -⟩ := hprov n₀ sent hrun hA
  have hA₀ := (confirmationUpdated_of_cutoff_tickInput M F U) x R μ' u n₀ sent hrun hA
  have huH : u ∈ Hon M S A x μ' := by
    unfold Hon roundMembers
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _,
      (not_mem_corruptedAtTime_of_le M) x R E hcut.le hu⟩
  have huU : u ∈ updaterAt M S A x μ' := P.memberU M F U (by omega) huH (le_trans hcut.le hEnd)
  have hst := (state_saved_of_update M F U) S A x R μ' u n₀ E huU hA₀
  exact ⟨u, huU, n₀, C₀, e₀.B, hA₀, hC₀, hst.trans hC₀, heB₀, he₀C₀, Or.inr (Or.inl ⟨hμ, hkind⟩)⟩

end PartAHyps

/-! ## Two line sources are compatible -/

namespace PartAHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}

/-- **Two line sources of slots in strict order.** A line source `X` of slot `μ` and a line source
`X'` of a slot `μ' > μ` at most `σ` are compatible when the invariant holds at every slot up to `σ`:
`X'`'s saver is an updater of slot `μ'`, and the invariant at `μ'` (its second conjunct) says the
confirmation it saved at its tick extends `X`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: a line source of an earlier slot is compatible with a line source of a later slot at
most `σ`, when the invariant holds up to `σ`. -/
theorem sources_compatible_lt {σ : ℕ}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') {μ μ' : ℕ} {X X' : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hX' : LineSource M S A x r H₂ μ' X')
    (hμμ : μ < μ') (hμ' : μ' ≤ σ) : X.compatible X' = true := by
  obtain ⟨u', hu', A₀', C₀', X₀', -, -, hC₀', hXX₀', hX₀C₀', -⟩ := hX'
  have hXC := (hG μ' hμ' μ X hX (by omega)).2 u' hu' C₀' hC₀'
  exact compatible_of_ancestorEq_both hXC (ancestorEq_trans hXX₀' hX₀C₀')
    ((compatible_iff _ _).2 (Or.inl (ancestorEq_refl _)))

/-- **Two line sources of one slot.** Two line sources of a slot `μ` from round `r` on are
compatible when every tick to the support cutoff of slot `μ + 1` is in the phase (`hEndμ`): Lemma 32
compares the confirmations the two savers saved at their own ticks.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: two line sources of one slot are compatible, when the ticks to that slot's update are in
the phase. -/
theorem sources_compatible_eq (R : RunFacts M S x) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {μ : ℕ} (hEndμ : ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (μ + 1)) →
      x.time k ≤ tAwakeEnd) {X X' : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hX' : LineSource M S A x r H₂ μ X') : X.compatible X' = true := by
  have hs := hX.slot_ge M F
  obtain ⟨u', hu', A₀', C₀', X₀', -, -, hC₀', hXX₀', hX₀C₀', -⟩ := hX'
  have hX'C : X'.AncestorEq C₀' := ancestorEq_trans hXX₀' hX₀C₀'
  obtain ⟨u, hu, A₀, C₀, X₀, -, -, hC₀, hXX₀, hX₀C₀, -⟩ := hX
  -- the two savers' ticks to the support cutoff of slot `μ + 1` are in the phase (`hEndμ`)
  obtain ⟨k₁, hk₁, -⟩ := Activity.mem_activeThroughoutToTick.1 hu
  obtain ⟨k₂, hk₂, -⟩ := Activity.mem_activeThroughoutToTick.1 hu'
  have hRoots' : RootsNameBlocksUntil M A x (max (x.time (x.tickStep u (M.supportCutoff S.C (μ + 1))))
      (x.time (x.tickStep u' (M.supportCutoff S.C (μ + 1))))) := by
    rw [(tickStep_eq_of_lbl M) x P.E hk₁, (tickStep_eq_of_lbl M) x P.E hk₂]
    exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
      (max_le (hEndμ u k₁ hk₁) (hEndμ u' k₂ hk₂)) P.hRoots
  exact compatible_of_ancestorEq_both (ancestorEq_trans hXX₀ hX₀C₀) hX'C
    ((GoldilocksCorrectness.Record.Proofs.Executions.lem32_saved_confirmations_compatible_state M F U) S A x R GST μ u u' C₀ C₀'
      P.E P.hNet P.hSkew P.hRedeliver P.Sy P.hΔs hRoots' (P.gstSync M F U hs).2.1 hu hu' hC₀ hC₀')

/-- Two line sources of slots `μ ≤ μ' ≤ σ` are compatible, when the invariant holds at every slot
up to `σ`: of one slot, by Lemma 32; of two slots, the later source's confirmation extends the
earlier source.


The support cutoff of slot `σ + 2` is in the phase (`hEnd`): Lemma 32 compares the frame trees of two savers of one
slot `μ ≤ σ` at their own ticks to the support cutoff of slot `μ + 1`, each at a real time less than the support cutoff
of slot `μ + 2` (`time_le_of_tick_supportCutoff`).
The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: two line sources of slots in order, both at most `σ`, are compatible when the invariant
holds up to `σ`. -/
theorem sources_compatible_le (R : RunFacts M S x) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ')
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) {μ μ' : ℕ} {X X' : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hX' : LineSource M S A x r H₂ μ' X')
    (hμμ : μ ≤ μ') (hμ' : μ' ≤ σ) : X.compatible X' = true := by
  rcases Nat.lt_or_eq_of_le hμμ with hlt | heq
  · exact sources_compatible_lt M F hG hX hX' hlt hμ'
  · subst heq
    exact P.sources_compatible_eq M F R U
      (fun u k hk => (time_le_of_tick_supportCutoff M F U) P.E P.hSkew
        (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
          (show μ + 2 ≤ σ + 2 by omega)) hEnd) hk) hX hX'

/-- Two line sources of slots at most `σ` are compatible, when the invariant holds at every slot
up to `σ`.


The support cutoff of slot `σ + 2` is in the phase (`hEnd`): Lemma 32 compares the frame trees of two savers of one
slot `μ ≤ σ` at their own ticks to the support cutoff of slot `μ + 1`, each at a real time less than the support cutoff
of slot `μ + 2` (`time_le_of_tick_supportCutoff`).
The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: two line sources of slots at most `σ` are compatible when the invariant holds up to `σ`.
-/
theorem sources_compatible (R : RunFacts M S x) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ')
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) {μ μ' : ℕ} {X X' : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hX' : LineSource M S A x r H₂ μ' X')
    (hμ : μ ≤ σ) (hμ' : μ' ≤ σ) : X.compatible X' = true := by
  rcases le_total μ μ' with h | h
  · exact P.sources_compatible_le M F R U hG hEnd hX hX' h hμ'
  · exact compatible_symm' (P.sources_compatible_le M F R U hG hEnd hX' hX h hμ)

end PartAHyps

/-! ## A certificate at a height greater than `H₂` names an entry of a line source -/

open GoldilocksCorrectness.Proofs.Routines (tick_attest_awake awakeSince_of_record_awake
  create_attestation_cases)

/-- An honest attestation is put on the wire only at a round's action time.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: an honest attestation is put on the wire only at a round's action time. -/
theorem attest_time_round (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {i t : ℕ} {u : V} {a : Attestation V} (hl : x.lbl i = Event.tick u t)
    (hSent : (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i) :
    ∃ r' : ℕ, t = aR M S r' := by
  obtain ⟨-, n', sent, hrun, ha⟩ := (tick_send_of_honestSendAt M F R E) hl hSent
  -- the tick's input state satisfies the node invariant (a wake keeps it)
  have hTI_i : x.tickInput u t = x.st i u := by
    show x.st (x.tickStep u t) u = x.st i u
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput u t) := by
    rw [hTI_i]
    exact (lem11_node_invariant M F S A x R E i u (E.not_mem_corrupted_of_tick hl)).1
  -- Lemma 49 over the record (T8): the tick attests only at the action time of its round
  obtain ⟨hAct, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n' _ sent a
      hrun hInvT ha
  -- the spec's slot of `t` is the model's (`U`)
  have hsl : S.C.slot (t : Int) = M.slot S.C t := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
  rw [hsl] at hAct
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = S.C.round (M.slot S.C t) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = r * S.C.R := ⟨_, rfl⟩
  obtain ⟨hslot, hround, hact', -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_times M.toSlotLayout F.sched U) S r
      s hs
  have htInt : (t : Int) = ((M.supportCutoff S.C (s + 1) : ℕ) : Int) := by
    rw [hact', hslot, hround, hr]
    exact hAct
  refine ⟨r, ?_⟩
  have ht : t = M.supportCutoff S.C (s + 1) := by exact_mod_cast htInt
  rw [ht, hs]
  rfl

/-- A1 with the attestation's root: an honest attestation at the action time of round `r` is
built from a fast block `X` of a node state `n₀` its sender's update leaves (`ConfirmationUpdated`,
the shape of `fast_block_of_honest_attestation`), held then, with `a`'s height as its height and the
root of its entry block `T_h(X)` as `a`'s root.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: an honest attestation at a round's action time is built from a fast block of its
sender's update, held then. -/
theorem fast_source_of_attestation (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (r : ℕ) (v : V) (a : Attestation V)
    (hSend : HonestAttestationAt M S A x (aR M S r) v a) :
    ∃ (n₀ : M.N) (X : Block V),
      ConfirmationUpdated M S.C S.P (x.tickInput v (aR M S r)) ((aR M S r : ℕ) : Int)
        (r * S.C.R + 1) n₀ ∧
      X ∈ M.fastBlocks n₀ ∧ X ∈ (x.tickInput v (aR M S r)).tree ∧
      (M.chainStateOf S.C X).h = a.h ∧ (M.chainStateOf S.C X).T_h.root = a.T := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = r * S.C.R := ⟨_, rfl⟩
  have haR : aR M S r = M.supportCutoff S.C (s + 1) := by rw [hs]; rfl
  rw [haR] at hSend ⊢
  rw [← hs]
  obtain ⟨i, hl, hSent⟩ := hSend
  -- the tick, and the attestation it built
  obtain ⟨-, n', sent, hrun, ha⟩ := (tick_send_of_honestSendAt M F R E) hl hSent
  have hTI_i : x.tickInput v (M.supportCutoff S.C (s + 1)) = x.st i v := by
    show x.st (x.tickStep v (M.supportCutoff S.C (s + 1))) v = x.st i v
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1))) := by
    rw [hTI_i]
    exact (lem11_node_invariant M F S A x R E i v (E.not_mem_corrupted_of_tick hl)).1
  -- Lemma 49 over the record: the tick ran from a state awake for the slot of the cutoff, and built
  -- `a` from the height and the root of `T_h` of the source's chain state, the source being the
  -- deepest fast block of the outcome in the viable tree
  obtain ⟨-, hAw, source, head, hsrc, -, ⟨τ', -, -, rfl⟩, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n' _ sent a
      hrun hInvT ha
  -- the spec's slot of the cutoff is `s + 1` (`U`)
  have hsl1 : S.C.slot ((M.supportCutoff S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S s).1
  -- the confirmation update of slot `s + 1` ran in the tick, from the state awake for the slot
  have hCU := F.tk2.tick_supportCutoff_confirmation S.C S.P S.X _ _ n' sent hrun hInvT
    (by rw [hsl1]; exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U) S (s + 1))
    hAw
  rw [hsl1] at hCU
  -- the source is a fast block of the outcome, and a block of the viable tree of the input's tree,
  -- so a block of the input's tree (the readers `viable_tree` and `fg_to_ac` by their definitions)
  obtain ⟨hfast, hvt⟩ := Finset.mem_inter.1 (GoldilocksCorrectness.Proofs.Routines.deepest?_mem hsrc)
  have hsT : source ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).tree := by
    rw [F.rd.viable_tree_eq] at hvt
    have h1 := (Finset.mem_filter.1 hvt).1
    rw [F.rd.fg_to_ac_eq] at h1
    exact (Finset.mem_filter.1 h1).1
  exact ⟨n', source, hCU, hfast, hsT, rfl, rfl⟩

/-- **`cert_source_core` with the source's fast block.** The certificate's entry block `E` is the entry
`T_h(X₀)` of a block `X₀` that the update of the honest attester `u` at its tick to `aR M S r'` made fast
(the proof of `cert_source_core`, which builds the line source from that fast block, A1).

The variables: as `cert_source_core`'s.

Read aloud: a certificate above `H₂` names the entry of a fast block of an honest attester's update, at a
tick before the reading. -/
theorem cert_source_core_fast {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {tGAT tAwakeEnd r H₂ : ℕ} {v : V}
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hk₀ : x.lbl (x.tickStep v (aR M S r)) = Event.tick v (aR M S r))
    (hOldStep : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < x.firstAt (M.supportCutoff S.C (r * S.C.R)) →
      x.lbl k = Event.tick u t → u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂)
    (hEndStep : x.time (x.tickStep v (aR M S r)) ≤ tAwakeEnd)
    {j : ℕ} {w : V} {Y T : Block V} {h : Height} (hj : x.time j ≤ tAwakeEnd)
    (hY : Y ∈ (x.st j w).tree) (hJ : ProgressCertOn M Y h T) (hH : H₂ < h) :
    ∃ (r' : ℕ) (E : Block V) (u : V) (k : ℕ), r ≤ r' ∧ x.lbl k = Event.tick u (aR M S r') ∧ k < j ∧
      u ∈ A.active k ∧ LineSource M S A x r H₂ (r' * S.C.R) E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = h ∧ T.root = E.root ∧
      u ∈ updaterAt M S A x (r' * S.C.R) ∧ ∃ (n₀ : M.N) (X₀ : Block V),
        ConfirmationUpdated M S.C S.P (x.tickInput u (aR M S r')) ((aR M S r' : ℕ) : Int) (r' * S.C.R + 1) n₀ ∧
        X₀ ∈ M.fastBlocks n₀ ∧ E.AncestorEq X₀ := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  -- the adversary bound up to the later of `x.time j` and the action time of round `r`
  have hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time j) (aR M S r)) :=
    fun X hX => by
      have h1 := (hThird.mono (max_le hj (by exact_mod_cast hEnd))) X hX
      have h2 := (GoldilocksCorrectness.Statements.Routines.lem65b_quorum_threshold (V := V)).2
      omega
  obtain ⟨X₁, hX₁Y, Q, hqA, hQ⟩ := hJ
  rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X₁] at hqA
  obtain ⟨u, hu, hhonM⟩ : ∃ u ∈ Q, A.HonestThroughTime x (max (x.time j) (aR M S r)) u := by
    by_contra hno
    have hall : ∀ v ∈ Q, ∃ i : ℕ, x.time i ≤ max (x.time j) (aR M S r) ∧ v ∈ A.corrupted i := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun i hi ha => hn ⟨i, hi, ha⟩⟩
    have h3 := hAdvQ Q hall
    omega
  have hhonT : ∀ t'' : ℕ, t'' ≤ max (x.time j) (aR M S r) → u ∉ A.corruptedAtTime x t'' :=
    fun t'' ht'' => Activity.not_mem_corruptedAtTime.2 fun i hi => hhonM i (le_trans hi ht'')
  have hhon : x.HonestThrough A j u :=
    fun i'' hi'' => hhonM i'' (le_trans ((time_mono M) x R hi'') (le_max_left _ _))
  have huR : u ∉ A.corruptedAtTime x (aR M S r) := hhonT _ (le_max_right _ _)
  obtain ⟨a, hau, hah, haT, hon⟩ := hQ u hu
  have hrec := (GoldilocksCorrectness.Record.Proofs.Executions.lem74_honest_attestations_recorded M F) S A x R E j w Y a hY
    ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_mono M F) a hX₁Y hon)
    (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, hact', hsent, -, hcont, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Executions.record_content_sent_step M F) S A x R E u j _ hrec
  have hh' : a'.h = h := by
    rw [← hah]
    exact congrArg AttestationContent.h hcont
  have hT' : a'.T = T.root := by
    rw [← haT]
    exact congrArg AttestationContent.T hcont
  have hge : aR M S r ≤ t' := by
    by_contra hlt
    have hle := hOld j' t' u a' hl (by exact_mod_cast Nat.lt_of_not_le hlt) huR hsent
    rw [hh'] at hle
    exact absurd hle (Nat.not_le.mpr hH)
  obtain ⟨r', rfl⟩ := (attest_time_round M F U) S A x R E hl hsent
  have hrr : r ≤ r' := by
    by_contra hlt
    have : r' * S.C.R + 1 < r * S.C.R + 1 := by
      have := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_le hlt)
        (show 0 < S.C.R by have := S.C.R_ge_two; omega)
      omega
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt M.toSlotLayout F.sched) S this
    exact absurd hge (Nat.not_le.mpr this)
  obtain ⟨n₀, X, hU, hXf, hXT, hXh, hXT'⟩ :=
    (fast_source_of_attestation M F U) S A x R E r' u a' ⟨j', hl, hsent⟩
  obtain ⟨hE1, hE2, hE3⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.isEntry_T_h M F) S.C X
  -- `u` is an updater of slot `r' * R`: honest up to its tick `j'`, awake from its tick to the duty
  -- window's start of slot `r' * R + 1`
  have hj'j : x.time j' ≤ x.time j := htime hj'.le
  have hhon' : ∀ i : ℕ, i ≤ j' → u ∉ A.corrupted i := fun i hi => hhon i (by omega)
  have hkt := (E.tick_active j' u _ hl).2
  have hdws : tGAT + Δ S ≤ M.dutyWindowStart S.C (r' * S.C.R + 1) :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S
      tGAT (r * S.C.R) hAnchor)
      ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S
        (show r * S.C.R ≤ r' * S.C.R + 1 by have := Nat.mul_le_mul_right S.C.R hrr; omega))
  have hdw := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S
    (r' * S.C.R)
  have hT0 := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (r' * S.C.R)
  have hT1 := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (r' * S.C.R + 1)
  have hcR : ((M.dutyWindowStart S.C (r' * S.C.R + 1) : ℕ) : ℝ) + 4 * Δ S ≤ (aR M S r' : ℝ) := by
    have : M.dutyWindowStart S.C (r' * S.C.R + 1) + 4 * Δ S ≤ aR M S r' := by
      show _ ≤ M.supportCutoff S.C (r' * S.C.R + 1)
      omega
    exact_mod_cast this
  have hdwsR : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.dutyWindowStart S.C (r' * S.C.R + 1) : ℕ) : ℝ) := by
    exact_mod_cast hdws
  obtain ⟨kc, hkc, hkc1, hkc2⟩ := E.tick_of_active (M.dutyWindowStart S.C (r' * S.C.R + 1)) (by omega) u
    (fun i h1 h2 => by
      have hij : i < j' := (lt_of_time_lt M) x R (by linarith)
      have hui := hhon' i hij.le
      exact Activity.mem_active.2 ⟨hAwake i u (by linarith [htime hij.le]) (by linarith [htime (Nat.le_succ i)]) hui, hui⟩)
  have hkcj : kc ≤ j' := tick_step_le_of_le M F E hkc hl (by
    show M.dutyWindowStart S.C (r' * S.C.R + 1) ≤ M.supportCutoff S.C (r' * S.C.R + 1)
    omega)
  have hupd : u ∈ updaterAt M S A x (r' * S.C.R) := by
    show u ∈ A.activeThroughoutToTick x (Goldilocks.duty_window_start S.C (r' * S.C.R + 1))
      (M.supportCutoff S.C (r' * S.C.R + 1))
    refine Activity.mem_activeThroughoutToTick.2 ⟨j', hl, Or.inr ⟨kc, hkcj, M.dutyWindowStart S.C (r' * S.C.R + 1),
      (dutyWindowStart_le_duty_window_start M F U) S (by omega), hkc, fun i h1 h2 => ?_⟩⟩
    have hui := hhon' i h2
    exact Activity.mem_active.2 ⟨hAwake i u (by linarith [htime h2]) (by linarith [htime h1, htime (Nat.le_succ i)]) hui, hui⟩
  have hst := (GoldilocksCorrectness.Record.Proofs.Executions.state_saved_of_update M F U) S A x R (r' * S.C.R) u n₀ E
    hupd hU
  obtain ⟨C₀, hC₀, hXC₀⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_fast_block_saved
      (Nat.le_add_left 1 _) hU hXf
  rw [Nat.add_sub_cancel] at hC₀
  have hkind : (r' * S.C.R = r * S.C.R ∧ X ∈ M.fastBlocks n₀ ∧ (M.chainStateOf S.C X).h = H₂ + 1) ∨
      (r * S.C.R + 1 ≤ r' * S.C.R ∧ (X ∈ M.fastBlocks n₀ ∨
        M.slow_test S.C (x.tickInput u (M.supportCutoff S.C (r' * S.C.R + 1))) (r' * S.C.R) X =
          true)) ∨
      r * S.C.R + S.C.k ≤ r' * S.C.R := by
    rcases Nat.lt_or_eq_of_le hrr with hlt | heq
    · refine Or.inr (Or.inl ⟨?_, Or.inl hXf⟩)
      have h1 := Nat.mul_le_mul_right S.C.R (show r + 1 ≤ r' by omega)
      have h2 := S.C.R_ge_two
      rw [Nat.succ_mul] at h1
      omega
    · subst heq
      refine Or.inl ⟨rfl, hXf, ?_⟩
      -- `X` is `H_v` or an ancestor of it, a block an honest committee member held at its tick to the
      -- vote time of slot `r * R`, a step before `v`'s tick to `aR M S r` (A2 there)
      have hRoots' : RootsNameBlocksUntil M A x ((M.supportCutoff S.C (r * S.C.R + 1) : ℕ) : ℝ) :=
        hRoots.mono M (by exact_mod_cast hEnd)
      obtain ⟨v', -, H_v, hHv, hXH⟩ :=
        (fast_block_has_honest_supporter_of_update M F U) S A x R (anchorCW S tGAT) (r * S.C.R) u E hSkew
          ((votesCastByOwner_of_unforgeability M F) S A x R E) hRoots'
          (hCommittees.mono M hEnd) hAnchor hupd n₀ hU X hXf
      have hk0t := (E.tick_active _ v _ hk₀).2.1
      have hT0' := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (r * S.C.R)
      have hT1' := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (r * S.C.R + 1)
      -- `v'`'s tick to the vote time of slot `r * R` comes before the first step reaching that slot's support cutoff
      have hvk : x.tickStep v' (M.voteTime S.C (r * S.C.R)) ≤ x.firstAt (M.supportCutoff S.C (r * S.C.R)) := by
        by_cases hex : ∃ i : ℕ, x.lbl i = Event.tick v' (M.voteTime S.C (r * S.C.R))
        · obtain ⟨i, hi⟩ := hex
          rw [(tickStep_eq_of_lbl M) x E hi]
          have hit := (E.tick_active i v' _ hi).2.2
          have hvt : ((M.voteTime S.C (r * S.C.R) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (r * S.C.R) : ℕ) : ℝ) := by
            exact_mod_cast hT0'.2.1
          exact ((lt_firstAt_of_time_lt M F) R E (by linarith)).le
        · simp only [Trace.tickStep, hex, dif_neg, not_false_eq_true]
          exact Nat.zero_le _
      -- that first step is at or before `v`'s tick to `aR M S r`, so in the phase
      have hk0E : x.time (x.firstAt (M.supportCutoff S.C (r * S.C.R))) ≤ tAwakeEnd := by
        have hc : ((M.supportCutoff S.C (r * S.C.R) : ℕ) : ℝ) ≤ x.time (x.tickStep v (aR M S r)) := by
          have : M.supportCutoff S.C (r * S.C.R) + 4 * Δ S ≤ aR M S r := by
            show _ ≤ M.supportCutoff S.C (r * S.C.R + 1)
            omega
          have h4 : ((M.supportCutoff S.C (r * S.C.R) : ℕ) : ℝ) + 4 * Δ S ≤ (aR M S r : ℝ) := by exact_mod_cast this
          linarith
        exact le_trans ((time_mono M) x R ((firstAt_le_of_time_ge M F) R E hc)) hEndStep
      have hle := (held_height_le_before_action M F Fx) S A x R E tAwakeEnd H₂ (x.firstAt (M.supportCutoff S.C (r * S.C.R)))
        (x.tickStep v' (M.voteTime S.C (r * S.C.R))) v' H_v hThird hOldStep hk0E hvk hHv
      have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C hXH
      rw [hXh, hh'] at hmono ⊢
      unfold Height at *
      omega
  refine ⟨r', (M.chainStateOf S.C X).T_h, u, j', hrr, hl, hj', hact', ⟨u, hupd, n₀, C₀, X, hU, hC₀,
    hst.trans hC₀, hE3, hXC₀, hkind⟩, hE1, by rw [hE2, hXh, hh'], ?_, hupd, n₀, X, hU, hXf, hE3⟩
  rw [← hT', ← hXT']

/-- **A certificate above `H₂` names the entry of a line source, at an honest tick before the reading.** A
progress certificate at a height `h > H₂` on the chain of a block `w` holds after `j` steps, within the phase, names
the root of an entry block `E` at the height `h` that is a line source of the first slot of a round `r' ≥ r`, made a
line source by the update an honest validator `u` ran at its tick `k` to `aR M S r'`, a step before `j` at which `u` is
active.

Why: an honest member `u` of the certificate's quorum (fewer than a third in the adversary set) recorded its attestation,
which its tick `k` at a clock value `t'` put on the wire (`record_content_sent_step`); `t'` is the action time of a round
`r' ≥ r` (`attest_time_round`, and `hOld` below `aR M S r`). The attestation is built from a fast block `X` of `u`'s
update (A1, `fast_source_of_attestation`), saved on the confirmation of slot `r' * R`, and `u` is an updater of that slot
(awake from its tick to the duty window's start, `tick_of_active`, honest up to `k`). When `r' = r`, `X` is `H_v` or an
ancestor of `H_v`, a block an honest committee member held at its tick to the vote time of slot `r * R`
(`fast_block_has_honest_supporter_of_update`), a step before `v`'s tick to `aR M S r`, so its height is at most
`H₂ + 1` (A2, `held_height_le_before_action`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, the run's facts, the environment's facts;
  `tGAT`, `tAwakeEnd`: the phase; `r`: the round; `H₂`: the threshold; `v`: the first attester above it;
- `j`: the reading step; `w`: the holder; `Y`: the block; `h`, `T`: the certificate's height and block.

Read aloud: a certificate above `H₂` names the entry of a line source of a round's first slot, whose update an honest
validator ran at a tick before the reading. -/
theorem cert_source_core {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {tGAT tAwakeEnd r H₂ : ℕ} {v : V}
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hk₀ : x.lbl (x.tickStep v (aR M S r)) = Event.tick v (aR M S r))
    (hOldStep : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < x.firstAt (M.supportCutoff S.C (r * S.C.R)) →
      x.lbl k = Event.tick u t → u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂)
    (hEndStep : x.time (x.tickStep v (aR M S r)) ≤ tAwakeEnd)
    {j : ℕ} {w : V} {Y T : Block V} {h : Height} (hj : x.time j ≤ tAwakeEnd)
    (hY : Y ∈ (x.st j w).tree) (hJ : ProgressCertOn M Y h T) (hH : H₂ < h) :
    ∃ (r' : ℕ) (E : Block V) (u : V) (k : ℕ), r ≤ r' ∧ x.lbl k = Event.tick u (aR M S r') ∧ k < j ∧
      u ∈ A.active k ∧ LineSource M S A x r H₂ (r' * S.C.R) E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = h ∧ T.root = E.root := by
  obtain ⟨r', E', u, k, hrr, hk, hkj, hku, hE, hE1, hE2, hE3, -⟩ := (cert_source_core_fast M F) R E U Fx hSkew hRoots
    hThird hAwake hCommittees hAnchor hOld hEnd hk₀ hOldStep hEndStep hj hY hJ hH
  exact ⟨r', E', u, k, hrr, hk, hkj, hku, hE, hE1, hE2, hE3⟩

/-- **A fast block of an update is compatible with `X` when the slot's votes extend `X`.** For an
updater `u` of slot `σ'` (`updaterAt M S A x σ'`) and a node state `n₀` its update of slot `σ'` leaves from
its tick input at the support cutoff of slot `σ' + 1`: when every vote of slot `σ'` that a member of
`Hon M S A x σ'` put on the wire at its tick to the vote time of slot `σ'` is for a block of its tick input
that is `X` or a descendant of `X`, every fast block of `n₀` is compatible with `X`.

Why: a fast block `D` of the update has a supporter `v`, an honest active committee member of slot `σ'`,
whose tick to the vote time of slot `σ'` sent its vote for a block `H_v` it held, with `D ⪯ H_v`
(`fast_block_has_honest_supporter_vote_of_update`); `v` is a member of `Hon M S A x σ'` (honest at the
support cutoff of slot `σ' + 1`), so its vote is for a block `H_w` of the same tree with `X ⪯ H_w`; the two
blocks have one root and are held by `v` at its tick, before that cutoff (`hRoots`), so they are one block,
and `D` and `X` are both `H_v` or ancestors of it.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, the run's facts, the environment's facts;
  `anchor`: the time from which committee sleepiness holds; `σ'`: the slot; `u`: the updater; `n₀`: the node
  state its update leaves; `X`: the block the votes extend; `D`: the fast block.

Read aloud: when every honest vote of slot `σ'` extends `X`, every block an honest update of slot `σ'` makes
fast is compatible with `X`. -/
theorem fast_block_compatible_of_votes_core {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (U : UniformSchedule M.toSlotLayout) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    {anchor σ' : ℕ} {u : V} {X : Block V}
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (σ' + 1)))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (σ' + 1)))
    (hAnchor : anchor ≤ M.slotStart S.C (σ' + 1))
    (hu : u ∈ updaterAt M S A x σ') {n₀ : M.N}
    (hCU : ConfirmationUpdated M S.C S.P (x.tickInput u (M.supportCutoff S.C (σ' + 1)))
      ((M.supportCutoff S.C (σ' + 1) : ℕ) : Int) (σ' + 1) n₀)
    (hV : ∀ w ∈ Hon M S A x σ', ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C σ') ∧
        (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_w ∈ (x.tickInput w (M.voteTime S.C σ')).tree,
        vote = GoldfishVote.mk w σ' H_w.root ∧ X.AncestorEq H_w)
    {D : Block V} (hD : D ∈ M.fastBlocks n₀) : D.compatible X = true := by
  obtain ⟨v, hv, H_v, hHv, hDH, k, hk, hsk⟩ :=
    (fast_block_has_honest_supporter_vote_of_update M F U) S A x R anchor σ' u E hSkew
      ((votesCastByOwner_of_unforgeability M F) S A x R E) hRoots hSleepK hAnchor hu n₀ hCU D hD
  have hvc : v ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ' + 1)) :=
    fun h => (Finset.mem_sdiff.1 (Finset.mem_inter.1 hv).1).2 (Finset.mem_union_left _ h)
  have hvH : v ∈ Hon M S A x σ' := by
    unfold Hon roundMembers
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hvc⟩
  obtain ⟨H_w, hHw, hveq, hXH⟩ := hV v hvH _ ⟨k, hk, hsk⟩
  have hroot : H_v.root = H_w.root := (GoldfishVote.mk.inj hveq).2.2
  -- `v`'s tick `k` to the vote time of slot `σ'` is before the support cutoff of slot `σ' + 1`
  have hkc : x.time k ≤ (M.supportCutoff S.C (σ' + 1) : ℝ) := by
    have h1 := (E.tick_active k v _ hk).2.2
    obtain ⟨hv1, -, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ'
    obtain ⟨-, hc2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ' + 1)
    have hB0 := E.behind_nonneg
    have hA0 := E.ahead_nonneg
    have h3 : (M.voteTime S.C σ' : ℝ) + Δ S ≤ M.supportCutoff S.C (σ' + 1) := by
      exact_mod_cast (show M.voteTime S.C σ' + Δ S ≤ M.supportCutoff S.C (σ' + 1) by omega)
    linarith
  have hTI : x.tickInput v (M.voteTime S.C σ') = x.st k v := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk]
  have hvk : v ∉ A.corrupted k := E.not_mem_corrupted_of_tick hk
  have hHH : H_v = H_w := hRoots H_v H_w ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := k) (v := v) hvk hkc (hTI ▸ hHv)) ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := k) (v := v) hvk hkc (hTI ▸ hHw)) hroot
  rw [← hHH] at hXH
  exact (compatible_iff _ _).2 (ancestorEq_compatible hDH hXH)

namespace PartAHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}

/-- **A certificate at a height greater than `H₂` names an entry of a line source.** A progress
certificate at a height `h > H₂` on the chain of a block `w` holds after `j` steps, within the
phase, names the root of an entry block `E` at the height `h` that is a line source of a slot `μ`
whose update an honest validator `u` ran at its tick `k` to the support cutoff of slot
`μ + 1`, a step before `j` at which `u` is active (`cert_source_core`): `E` is the entry of the fast block an honest attester's update made fast
at the action time of a round `r' ≥ r` (A1), of kind (a) when `r' = r` (its height is then `H₂ + 1`,
A2).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: a certificate at a height greater than `H₂` names the entry of a line source. -/
theorem cert_source (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {j : ℕ} {w : V}
    {Y T : Block V} {h : Height} (hj : x.time j ≤ tAwakeEnd)
    (hY : Y ∈ (x.st j w).tree) (hJ : ProgressCertOn M Y h T) (hH : H₂ < h) :
    ∃ (μ : ℕ) (E : Block V) (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (μ + 1)) ∧
      k < j ∧ u ∈ A.active k ∧
      LineSource M S A x r H₂ μ E ∧ IsEntry M S.C E ∧ (M.chainStateOf S.C E).h = h ∧
      T.root = E.root := by
  obtain ⟨r', E', u, k, -, hk, hkj, hku, hE, hE1, hE2, hE3⟩ := (cert_source_core M F) R E U Fx P.hSkew P.hRoots P.hThird P.hAwake P.hCommittees P.hAnchor P.hOld
    P.hEnd P.hk₀ P.hOldStep P.hEndStep hj hY hJ hH
  exact ⟨r' * S.C.R, E', u, k, hk, hkj, hku, hE, hE1, hE2, hE3⟩

/-- `cert_source_fast` with the source's slot written as the first slot `r' * R` of a round `r'`
(`cert_source_core_fast` names the round).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: a certificate above `H₂` names the entry of a fast block of an honest update run, at a
round's action time, at a tick before the reading. -/
theorem cert_source_fast_round (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {j : ℕ} {w : V}
    {Y T : Block V} {h : Height} (hj : x.time j ≤ tAwakeEnd)
    (hY : Y ∈ (x.st j w).tree) (hJ : ProgressCertOn M Y h T) (hH : H₂ < h) :
    ∃ (r' : ℕ) (E : Block V) (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (r' * S.C.R + 1)) ∧
      k < j ∧ u ∈ A.active k ∧
      LineSource M S A x r H₂ (r' * S.C.R) E ∧ IsEntry M S.C E ∧ (M.chainStateOf S.C E).h = h ∧
      T.root = E.root ∧
      u ∈ updaterAt M S A x (r' * S.C.R) ∧ ∃ (n₀ : M.N) (X₀ : Block V),
        ConfirmationUpdated M S.C S.P (x.tickInput u (M.supportCutoff S.C (r' * S.C.R + 1)))
          ((M.supportCutoff S.C (r' * S.C.R + 1) : ℕ) : Int) (r' * S.C.R + 1) n₀ ∧
        X₀ ∈ M.fastBlocks n₀ ∧ E.AncestorEq X₀ := by
  obtain ⟨r', E', u, k, -, hk, hkj, hku, hE, hE1, hE2, hE3, hF⟩ := (cert_source_core_fast M F) R E U Fx P.hSkew P.hRoots P.hThird P.hAwake P.hCommittees P.hAnchor P.hOld
    P.hEnd P.hk₀ P.hOldStep P.hEndStep hj hY hJ hH
  exact ⟨r', E', u, k, hk, hkj, hku, hE, hE1, hE2, hE3, hF⟩

/-- `cert_source` with the source's fast block: the entry `E` is `X₀`'s entry or an ancestor of `X₀`,
a block the honest validator `u`'s update at its tick `k` made fast (`cert_source_core_fast`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: a certificate above `H₂` names the entry of a fast block of an honest update run at a tick
before the reading. -/
theorem cert_source_fast (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {j : ℕ} {w : V}
    {Y T : Block V} {h : Height} (hj : x.time j ≤ tAwakeEnd)
    (hY : Y ∈ (x.st j w).tree) (hJ : ProgressCertOn M Y h T) (hH : H₂ < h) :
    ∃ (μ : ℕ) (E : Block V) (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (μ + 1)) ∧
      k < j ∧ u ∈ A.active k ∧
      LineSource M S A x r H₂ μ E ∧ IsEntry M S.C E ∧ (M.chainStateOf S.C E).h = h ∧
      T.root = E.root ∧
      u ∈ updaterAt M S A x μ ∧ ∃ (n₀ : M.N) (X₀ : Block V),
        ConfirmationUpdated M S.C S.P (x.tickInput u (M.supportCutoff S.C (μ + 1)))
          ((M.supportCutoff S.C (μ + 1) : ℕ) : Int) (μ + 1) n₀ ∧
        X₀ ∈ M.fastBlocks n₀ ∧ E.AncestorEq X₀ := by
  obtain ⟨r', E', u, k, -, hk, hkj, hku, hE, hE1, hE2, hE3, hF⟩ := (cert_source_core_fast M F) R E U Fx P.hSkew P.hRoots P.hThird P.hAwake P.hCommittees P.hAnchor P.hOld
    P.hEnd P.hk₀ P.hOldStep P.hEndStep hj hY hJ hH
  exact ⟨r' * S.C.R, E', u, k, hk, hkj, hku, hE, hE1, hE2, hE3, hF⟩

end PartAHyps

/-! ## The frames relative to a line source -/

namespace PartAHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}

/-- A line source of slot `μ` is a block of an honest validator's tree at a step at a time at most
the support cutoff of slot `μ + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: a line source of slot `μ` is in an honest validator's tree by the support cutoff of slot
`μ + 1`. -/
theorem source_inHonestTreeBy (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {μ : ℕ}
    {X : Block V} (hX : LineSource M S A x r H₂ μ X) :
    inHonestTreeBy M A x (M.supportCutoff S.C (μ + 1)) X := by
  -- the saver `u` held its saved confirmation `C₀`, an extension of `X`, when it ticked to the support cutoff of slot `μ`
  obtain ⟨u, hu, n₀, C₀, X₀, -, -, hsv, hXX₀, hX₀C₀, -⟩ := hX
  obtain ⟨hl₀, hCT, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.saved_confirmation_held_compatible_supportCutoff M F U)
    S A x R μ u C₀ E P.hSkew hu hsv
  have hb := (E.tick_active _ u _ hl₀).2.2
  have hsk := P.hSkew
  have hA0 := E.ahead_nonneg
  have hcc : M.supportCutoff S.C μ + Δ S ≤ M.supportCutoff S.C (μ + 1) := by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S μ
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (μ + 1)
    have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S μ
    have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (μ + 1)
    have h5 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S μ
    have h6 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (μ + 1)
    rw [Nat.mul_add, Nat.mul_one] at h6
    omega
  have hccR : ((M.supportCutoff S.C μ : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (μ + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcc
  refine ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := x.tickStep u (M.supportCutoff S.C μ)) (v := u) (E.not_mem_corrupted_of_tick hl₀) (by linarith) (?_))
  exact (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ u C₀ X hCT
    (ancestorEq_trans hXX₀ hX₀C₀)

/-- A line source of slot `μ` is a block of an honest validator's tree at a step no later than any
tick to the support cutoff of slot `μ + 1`: its saver held it at its tick to the support cutoff of slot
`μ`, at a real time at most that cutoff plus `ΔClockBehind`, and a tick to the support cutoff of slot
`μ + 1` is at a real time at least that cutoff minus `ΔClockAhead`, one delay later (`hSkew`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `k`: a step that is some
  validator `u'`'s tick to the support cutoff of slot `μ + 1`.

Read aloud: a line source of slot `μ` is in an honest validator's tree by the real time of any tick
to the support cutoff of slot `μ + 1`. -/
theorem source_inHonestTreeBy_tick (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {μ : ℕ}
    {X : Block V} (hX : LineSource M S A x r H₂ μ X) {u' : V} {k : ℕ}
    (hk : x.lbl k = Event.tick u' (M.supportCutoff S.C (μ + 1))) :
    inHonestTreeBy M A x (x.time k) X := by
  -- the saver `u` held its saved confirmation `C₀`, an extension of `X`, when it ticked to the support cutoff of slot `μ`
  obtain ⟨u, hu, n₀, C₀, X₀, -, -, hsv, hXX₀, hX₀C₀, -⟩ := hX
  obtain ⟨hl₀, hCT, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.saved_confirmation_held_compatible_supportCutoff M F U)
    S A x R μ u C₀ E P.hSkew hu hsv
  have hb := (E.tick_active _ u _ hl₀).2.2
  have hsk := P.hSkew
  have hA0 := E.ahead_nonneg
  have hcc : M.supportCutoff S.C μ + Δ S ≤ M.supportCutoff S.C (μ + 1) := by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S μ
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (μ + 1)
    have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S μ
    have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (μ + 1)
    have h5 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S μ
    have h6 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (μ + 1)
    rw [Nat.mul_add, Nat.mul_one] at h6
    omega
  have hccR : ((M.supportCutoff S.C μ : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (μ + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcc
  have hkt := (E.tick_active _ _ _ hk).2.1
  have hB0 := E.behind_nonneg
  refine ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := x.tickStep u (M.supportCutoff S.C μ)) (v := u) (E.not_mem_corrupted_of_tick hl₀) (by linarith) (?_))
  exact (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ u C₀ X hCT
    (ancestorEq_trans hXX₀ hX₀C₀)

/-- A line source is a block of an honest validator's tree.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: a line source is in an honest validator's tree. -/
theorem source_inHonestTree (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {μ : ℕ}
    {X : Block V} (hX : LineSource M S A x r H₂ μ X) : inHonestTree M A x X := by
  exact (GoldilocksCorrectness.Record.Proofs.Executions.inHonestTree_of_inHonestTreeBy M F) x R E
    (P.source_inHonestTreeBy M F R E U hX)

/-- A line source of slot `μ` is in the tree of every validator at its tick `k` to the view freeze of
slot `μ`, when its finalized block there is compatible with it: the saver holds the
source at its tick to the support cutoff of slot `μ` (`saved_confirmation_held_compatible_supportCutoff`),
and `block_at_tick_of_held_tick` carries it to the receiver, from the window start one delay or one sync
delay before that cutoff.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: a line source of slot `μ` is in every validator's tree when its clock reaches the view
freeze of slot `μ`, when its finalized block then is compatible with the source. -/
theorem source_held (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {μ : ℕ}
    {X : Block V} {w : V} (hX : LineSource M S A x r H₂ μ X)
    (hEnd : M.supportCutoff S.C (μ + 1) ≤ tAwakeEnd)
    {k : ℕ} (hk : x.lbl k = Event.tick w (M.viewFreeze S.C μ))
    (hF : (x.tickInput w (M.viewFreeze S.C μ)).finalized.compatible X = true) :
    X ∈ (x.tickInput w (M.viewFreeze S.C μ)).tree := by
  have hs := hX.slot_ge M F
  obtain ⟨u, hu, n₀, C₀, X₀, -, -, hC₀, hXX₀, hX₀C₀, -⟩ := hX
  have hXC : X.AncestorEq C₀ := ancestorEq_trans hXX₀ hX₀C₀
  -- the saver `u` holds `C₀` at its tick `kU` to the support cutoff of slot `μ`, its finalized block there
  -- compatible with `C₀`
  obtain ⟨hkU, hCT, hFC⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Executions.saved_confirmation_held_compatible_supportCutoff M F U)
      S A x R μ u C₀ P.E P.hSkew hu hC₀
  have hXT : X ∈ (x.st (x.tickStep u (M.supportCutoff S.C μ)) u).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R P.E _ u C₀ X hCT hXC
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hsk := P.hSkew
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  obtain ⟨hv0, hc0, hf0, hs0, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ
  obtain ⟨hv1, hc1, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 1)
  obtain ⟨hG1, -, hG3⟩ := P.gstSync M F U hs
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  obtain ⟨a, ha_def⟩ : ∃ a : ℕ, a = M.supportCutoff S.C μ - max (Δ S) Δs := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := by omega
  -- the window starts one sync delay or one delay before the support cutoff of slot `μ`
  have hEndR : ((M.supportCutoff S.C (μ + 1) : ℕ) : ℝ) ≤ (tAwakeEnd : ℕ) := by exact_mod_cast hEnd
  have hfc : ((M.viewFreeze S.C μ : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (μ + 1) : ℕ) : ℝ) := by
    exact_mod_cast (show M.viewFreeze S.C μ + Δ S ≤ M.supportCutoff S.C (μ + 1) by omega)
  have hcf : ((M.supportCutoff S.C μ : ℕ) : ℝ) + Δ S = ((M.viewFreeze S.C μ : ℕ) : ℝ) := by
    exact_mod_cast (show M.supportCutoff S.C μ + Δ S = M.viewFreeze S.C μ by omega)
  have ha : ((a : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C μ : ℕ) : ℝ) := by
    exact_mod_cast (show a + Δ S ≤ M.supportCutoff S.C μ by omega)
  have htGa : (tGAT : ℝ) ≤ ((a : ℕ) : ℝ) := by
    exact_mod_cast (show tGAT ≤ a by omega)
  -- `w`, honest at its tick `k` to the view freeze of slot `μ`, is active at every step from `tGAT` up to `k`
  have hkt := P.E.tick_active k w _ hk
  have hwk : w ∉ A.corrupted k := P.E.not_mem_corrupted_of_tick hk
  have hwact : ∀ i : ℕ, (tGAT : ℝ) ≤ x.time (i + 1) → i ≤ k → w ∈ A.active i := by
    intro i h1 h2
    have hci : w ∉ A.corrupted i := P.E.not_mem_corrupted_of_le h2 hwk
    exact Activity.mem_active.2 ⟨P.hAwake i w (by linarith [htime h2]) h1 hci, hci⟩
  -- `w` ticks to the support cutoff of slot `μ` at a step `k₂`
  obtain ⟨k₂, hk₂, hk₂a, hk₂b⟩ := P.E.tick_of_active (M.supportCutoff S.C μ) (by omega) w fun i h1 h2 => by
    refine hwact i (le_trans (by linarith) (htime (Nat.le_succ i))) ?_
    by_contra hc
    have := htime (show k ≤ i by omega)
    linarith
  -- `u`, honest at its tick to the support cutoff of slot `μ + 1`, is active through the window
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hu
  have hk't := P.E.tick_active k' u _ hk'
  have huk' : u ∉ A.corrupted k' := P.E.not_mem_corrupted_of_tick hk'
  have hcμ : ((M.supportCutoff S.C μ : ℕ) : ℝ) + 4 * Δ S = ((M.supportCutoff S.C (μ + 1) : ℕ) : ℝ) := by
    exact_mod_cast (show M.supportCutoff S.C μ + 4 * Δ S = M.supportCutoff S.C (μ + 1) by omega)
  have hcorr : u ∉ A.corruptedAtTime x ((a + Δs : ℕ) : ℝ) := Activity.not_mem_corruptedAtTime.2 fun i hi => by
    refine P.E.not_mem_corrupted_of_le ((lt_of_time_lt M) x R ?_).le huk'
    have h1 : ((a + Δs : ℕ) : ℝ) ≤ ((M.supportCutoff S.C μ : ℕ) : ℝ) := by
      exact_mod_cast (show a + Δs ≤ M.supportCutoff S.C μ by omega)
    linarith
  have hu₀ : u ∈ A.activeThroughout x a (a + Δs) := by
    have h := (mem_activeThroughout_of_hAwake_honest_at M F) R P.E P.hAwake (a := a) (b := a + Δs)
      (by omega) (by omega) hcorr
    push_cast at h
    exact h
  -- `u`'s finalized block at its last step before the window's start is an ancestor of the one at `kU`
  have hkUt := P.E.tick_active _ u _ hkU
  have hsa : x.stepBefore a ≤ x.tickStep u (M.supportCutoff S.C μ) := by
    have h1 := ((stepBefore_time M) x R P.E ha1).1
    exact ((lt_of_time_lt M) x R (by linarith)).le
  have hFa : (x.st (x.stepBefore a) u).finalized.compatible X = true :=
    compatible_of_ancestorEq_both ((F_ancestorEq_of_le M F) x R P.E u hsa) hXC hFC
  -- `X`'s slot is at most `μ`
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hslotc : S.C.slot ((M.supportCutoff S.C μ : ℕ) : Int) = μ :=
    hsl _ ▸ (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
      (by omega) (by omega)
  have huU : u ∉ A.corrupted (x.tickStep u (M.supportCutoff S.C μ)) := P.E.not_mem_corrupted_of_tick hkU
  have hXs : X.slot ≤ μ := by
    have h := (slot_le_clockValue_of_mem_tree M F) R P.E huU hXT
    rw [← hslotc]
    exact h.trans (GoldilocksCorrectness.Proofs.Routines.slot_mono_int S
      (by exact_mod_cast P.E.clockValue_le_of_set huU (Or.inl hkU)))
  have hXc₂ : M.slotStart S.C X.slot ≤ M.supportCutoff S.C μ :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hXs)
      (by omega)
  have hkR : x.tickStep w (M.viewFreeze S.C μ) = k := (tickStep_eq_of_lbl M) x P.E hk
  show X ∈ (x.st (x.tickStep w (M.viewFreeze S.C μ)) w).tree
  rw [hkR]
  by_cases hg : X = Block.genesis
  · rw [hg]
    exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R P.E _ w
  refine (block_at_tick_of_held_tick M F U) S A x R GST (M.viewFreeze S.C μ) (M.supportCutoff S.C μ)
    (x.tickStep u (M.supportCutoff S.C μ)) a (M.viewFreeze S.C μ)
    (M.supportCutoff S.C μ) k k₂ u w X (P.E.upTo _) P.hNet P.hSkew P.hRedeliver (P.Sy.upTo _)
    ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (show x.time k ≤ ((tAwakeEnd : ℕ) : ℝ) by linarith) P.hRoots) P.hParent (by omega) (by omega) (by omega) le_rfl hu₀ hkU hXT hFa hg
    hk (fun i hi hik => hwact i (le_trans htGa (le_trans hi (htime (Nat.le_succ i)))) hik) hk₂ (by omega) hXc₂ ?_
  have := hF
  rw [show x.tickInput w (M.viewFreeze S.C μ) = x.st k w by
    show x.st (x.tickStep w (M.viewFreeze S.C μ)) w = x.st k w; rw [hkR]] at this
  exact this

end PartAHyps

namespace PartAHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}

/-- **A tick of an honest validator one delay before a reading.** A validator outside the adversary set
at `t`, in the phase, ticks to every clock value `c` at least one delay after `tGAT` and at least one delay
before `t`, at a step at or before the step before `t`.

Why: every step whose real time is in `[c − ΔClockAhead, c + ΔClockBehind]` is in the phase and before
`t` (`hSkew`), so the validator is active there (`hAwake`), and `tick_of_active` gives the tick.

The variables:
- `M`: the model; `F`: its facts; `R`: the run's facts; `P`: the bundle; `w`: the validator; `c`: the
  clock value; `t`: the reading.

Read aloud: an honest validator in the phase ticks to every clock value one delay before the reading,
before the reading. -/
theorem tick_before {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {w : V} {c t : ℕ} (hc : tGAT + Δ S ≤ c) (hct : c + Δ S ≤ t) (htE : t ≤ tAwakeEnd)
    (hw : w ∉ A.corruptedAtTime x t) :
    ∃ k : ℕ, x.lbl k = Event.tick w c ∧ k ≤ x.stepBefore t := by
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hsk := P.hSkew
  have hΔ := one_le_Δ S
  have ht1 : 1 ≤ t := by omega
  have htR : (c : ℝ) + Δ S ≤ (t : ℝ) := by exact_mod_cast hct
  have hER : (t : ℝ) ≤ ((tAwakeEnd : ℕ) : ℝ) := by exact_mod_cast htE
  have hGR : (tGAT : ℝ) + Δ S ≤ (c : ℝ) := by exact_mod_cast hc
  have hwj : w ∉ A.corrupted (x.stepBefore t) :=
    Activity.not_mem_corruptedAtTime.1 hw _ ((time_stepBefore_le M) x P.R P.E t)
  have hbefore : ∀ i : ℕ, x.time i ≤ (c : ℝ) + ΔClockBehind → i ≤ x.stepBefore t :=
    fun i hi => ((time_lt_iff_le_stepBefore M) x P.R P.E ht1).1 (by linarith)
  obtain ⟨k, hk, -, hkb⟩ := P.E.tick_of_active c (by omega) w fun i h1 h2 => by
    have hci : w ∉ A.corrupted i := P.E.not_mem_corrupted_of_le (hbefore i h2) hwj
    exact Activity.mem_active.2 ⟨P.hAwake i w (by linarith)
      (le_trans (by linarith) ((time_mono M) x P.R (Nat.le_succ i))) hci, hci⟩
  exact ⟨k, hk, hbefore k hkb⟩

/-- **A tick of an honest validator one delay before a step.** `tick_before` read at a step: a validator outside the
adversary set at step `j`, in the phase, ticks to every clock value `c` at least one delay after `tGAT` and at least one
delay before the real time of `j`, at a step less than `j`.

Why: every step whose real time is in `[c − ΔClockAhead, c + ΔClockBehind]` has a real time less than that of `j`
(`hSkew`), so it is before `j`, and the validator is outside the adversary set there and active (`hAwake`);
`tick_of_active` gives the tick.

The variables:
- `M`: the model; `F`: its facts; `P`: the bundle; `w`: the validator; `c`: the clock value; `j`: the step.

Read aloud: an honest validator in the phase ticks to every clock value one delay before a step's real time, before
that step. -/
theorem tick_before_st {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {w : V} {c j : ℕ} (hc : tGAT + Δ S ≤ c) (hcj : (c : ℝ) + Δ S ≤ x.time j) (hjE : x.time j ≤ tAwakeEnd)
    (hw : w ∉ A.corrupted j) :
    ∃ k : ℕ, x.lbl k = Event.tick w c ∧ k < j := by
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hsk := P.hSkew
  have hΔ := one_le_Δ S
  have hGR : (tGAT : ℝ) + Δ S ≤ (c : ℝ) := by exact_mod_cast hc
  have hbefore : ∀ i : ℕ, x.time i ≤ (c : ℝ) + ΔClockBehind → i < j :=
    fun i hi => (lt_of_time_lt M) x P.R (by linarith)
  obtain ⟨k, hk, -, hkb⟩ := P.E.tick_of_active c (by omega) w fun i h1 h2 => by
    have hci : w ∉ A.corrupted i := P.E.not_mem_corrupted_of_le (hbefore i h2).le hw
    exact Activity.mem_active.2 ⟨P.hAwake i w (by linarith)
      (le_trans (by linarith) ((time_mono M) x P.R (Nat.le_succ i))) hci, hci⟩
  exact ⟨k, hk, hbefore k hkb⟩

/-- `v` holds `L` in its tick input to the support cutoff of slot `r * R`, and so in its tick input to
`a_r`, a later step (the first tick is at most `ΔClockBehind` after that cutoff, more than one delay
before `a_r`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: `v` holds `L` when its clock reaches the support cutoff of the round's first slot. -/
theorem L_held_v (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (hEnd : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd) :
    L ∈ (x.tickInput v (M.supportCutoff S.C (r * S.C.R))).tree ∧
      L ∈ (x.tickInput v (aR M S r)).tree := by
  have hvH : v ∈ Hon M S A x (r * S.C.R) := by
    unfold Hon roundMembers
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, P.hv⟩
  have hU : ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (r * S.C.R + 1)))
      ((M.supportCutoff S.C (r * S.C.R + 1) : ℕ) : Int) (r * S.C.R + 1) n' := P.hUpdate
  have hvU : v ∈ updaterAt M S A x (r * S.C.R) := P.memberU M F U le_rfl hvH hEnd
  obtain ⟨C', hC', hLC'⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_fast_block_saved
      (Nat.le_add_left 1 _) hU P.hFast
  rw [Nat.add_sub_cancel] at hC'
  have hst := (GoldilocksCorrectness.Record.Proofs.Executions.state_saved_of_update M F U) S A x R (r * S.C.R) v n' P.E
    hvU hU
  obtain ⟨hl₀, hCT, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.saved_confirmation_held_compatible_supportCutoff M F U) S A x R
    (r * S.C.R) v C' P.E P.hSkew hvU (hst.trans hC')
  have h1 := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ v C' L hCT hLC'
  have hgap : ∀ j : ℕ, x.time j + Δ S ≤ (aR M S r : ℝ) → j ≤ x.tickStep v (aR M S r) := by
    intro j hj
    by_contra hge
    have hm := (time_mono M) x R (Nat.lt_of_not_le hge).le
    have hk := (E.tick_active _ v _ P.hk₀).2.1
    have hsk := P.hSkew
    have hb0 := E.behind_nonneg
    linarith
  have haR : M.slotStart S.C (r * S.C.R) + 6 * Δ S = aR M S r := by
    unfold aR
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (r * S.C.R)]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hsc : M.supportCutoff S.C (r * S.C.R) = M.slotStart S.C (r * S.C.R) + 2 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (r * S.C.R),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (r * S.C.R)]
    omega
  have hle : x.tickStep v (M.supportCutoff S.C (r * S.C.R)) ≤ x.tickStep v (aR M S r) := by
    refine hgap _ ?_
    have ht := (E.tick_active _ v _ hl₀).2.2
    have hsk := P.hSkew
    have hA0 := E.ahead_nonneg
    have h6 : ((M.supportCutoff S.C (r * S.C.R) + 2 * Δ S : ℕ) : ℝ) ≤ (aR M S r : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (r * S.C.R) + 2 * Δ S ≤ aR M S r by omega)
    push_cast at h6
    linarith
  exact ⟨h1, (mem_T_mono M F) x R E v hle h1⟩

/-- Every validator holds `L` in its tick input to the view freeze of slot `r * R`:
its finalized block there is an ancestor of `L` (`finalized_ancestor_of_fast_block`), and
`source_held` at the line source `L`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: every validator holds `L` when its clock reaches the view freeze of the round's first slot. -/
theorem L_held (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (hEnd : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd) {w : V}
    {k : ℕ} (hk : x.lbl k = Event.tick w (M.viewFreeze S.C (r * S.C.R))) :
    L ∈ (x.tickInput w (M.viewFreeze S.C (r * S.C.R))).tree := by
  have haR : M.slotStart S.C (r * S.C.R) + 6 * Δ S = aR M S r := by
    unfold aR
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (r * S.C.R)]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hvf' : M.viewFreeze S.C (r * S.C.R) = M.slotStart S.C (r * S.C.R) + 3 * Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S (r * S.C.R)
  -- `w`'s tick `k` to the view freeze of slot `r * R` comes before `v`'s tick to `a_r`
  have hle : k ≤ x.tickStep v (aR M S r) := by
    by_contra hge
    have hm := (time_mono M) x R (Nat.lt_of_not_le hge).le
    have hk0 := (P.E.tick_active _ v _ P.hk₀).2.1
    have hk1 := (P.E.tick_active _ w _ hk).2.2
    have hsk := P.hSkew
    have hA0 := P.E.ahead_nonneg
    have hB0 := P.E.behind_nonneg
    have h6 : ((M.viewFreeze S.C (r * S.C.R) + Δ S : ℕ) : ℝ) ≤ (aR M S r : ℝ) := by
      exact_mod_cast (show M.viewFreeze S.C (r * S.C.R) + Δ S ≤ aR M S r by omega)
    push_cast at h6
    linarith
  have hwk : w ∉ A.corrupted k := P.E.not_mem_corrupted_of_tick hk
  have hkR : x.tickStep w (M.viewFreeze S.C (r * S.C.R)) = k := (tickStep_eq_of_lbl M) x P.E hk
  have hFk : (x.st k w).finalized.AncestorEq L :=
    (finalized_ancestor_of_fast_block_le M F Fx) S A x R tAwakeEnd r H₂
      (x.tickStep v (aR M S r)) _ v w L P.E (tR := tAwakeEnd) P.hRoots P.hEndStep P.hThird P.hk₀
      ((oldStep_of_clock M F) R P.E P.hOld P.hEnd (fun k' hk' => by
        have hkk := (time_mono M) x R hk'.le
        have hk1 := (P.E.tick_active _ w _ hk).2.2
        have hsk := P.hSkew
        have hA0 := P.E.ahead_nonneg
        have h6 : ((M.viewFreeze S.C (r * S.C.R) + Δ S : ℕ) : ℝ) ≤ (aR M S r : ℝ) := by
          exact_mod_cast (show M.viewFreeze S.C (r * S.C.R) + Δ S ≤ aR M S r by omega)
        push_cast at h6
        linarith)) P.hEndStep
      (P.L_held_v M F R P.E U hEnd).2 P.hL hle hwk
  refine P.source_held M F R E hNet hSkew hRedeliver Sy hΔs U (P.source_L M F R U hEnd) hEnd hk ?_
  show (x.st (x.tickStep w (M.viewFreeze S.C (r * S.C.R))) w).finalized.compatible L = true
  rw [hkR]
  exact (compatible_iff _ _).2 (Or.inl hFk)

/-- `F_compat` at a step: under `F_compat`'s hypotheses, at a step `j` in the phase at which `w` is outside the
adversary set and whose real time is less than the earliest real time of a tick to the support cutoff of slot
`σ + 3` (that cutoff less `ΔClockAhead`), `w`'s finalized block is compatible with the line source `X`.

Why: `F_compat`'s argument, read at `j`: an update whose certificate `w`'s finalized block carries ran at a tick
before `j`, so of a slot at most `σ + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.

Read aloud: at a step before any tick to the support cutoff of slot `σ + 3`, an honest validator's finalized block
is compatible with every line source of a slot at most `σ`. -/
theorem F_compat_st (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ j : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) (hjE : x.time j ≤ tAwakeEnd)
    (hw' : w ∉ A.corrupted j)
    (hjc : x.time j < ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) - ΔClockAhead) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hV : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead ≤ x.time j →
      ∀ u ∈ Hon M S A x (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (σ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (σ + 1))).tree,
        vote = GoldfishVote.mk u (σ + 1) H_u.root ∧ X.AncestorEq H_u) :
    (x.st j w).finalized.compatible X = true := by
  have hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
  -- every tick to the support cutoff of a slot up to `σ + 1` is at a real time at most that cutoff plus
  -- `ΔClockBehind`, less than the support cutoff of slot `σ + 2` (`hSkew`)
  have hEndT : ∀ μ'' : ℕ, μ'' ≤ σ → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (μ'' + 1)) →
      x.time k ≤ tAwakeEnd := by
    intro μ'' hμ'' u k hk
    have hkt := (E.tick_active _ _ _ hk).2.2
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show μ'' + 1 ≤ σ + 1 by omega)
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (σ + 1)
    rw [show σ + 1 + 1 = σ + 2 from rfl] at h1
    have hc : ((M.supportCutoff S.C (μ'' + 1) : ℕ) : ℝ) + Δ S ≤ (tAwakeEnd : ℕ) := by
      exact_mod_cast (show M.supportCutoff S.C (μ'' + 1) + Δ S ≤ tAwakeEnd by omega)
    have hsk := hSkew
    have hA0 := E.ahead_nonneg
    linarith
  obtain ⟨D, hD, hFD⟩ :=
    (GoldilocksCorrectness.Record.Statements.Executions.finalizedFromChain_of_exec M F) S A x R E
      j w
  rw [hFD]
  by_cases hle : (M.chainStateOf S.C D).h_F ≤ H₂
  · -- `v` held `L` at its tick to the action time of round `r` (`L_held_v`), honest there, in the phase
    have hv' : v ∉ A.corrupted (x.tickStep v (aR M S r)) := E.not_mem_corrupted_of_tick P.hk₀
    have hT : A.AdversaryFewerThanThirdUntil x (validator_count V)
        (max (x.time j) (x.time (x.tickStep v (aR M S r)))) :=
      P.hThird.mono (max_le hjE P.hEndStep)
    have hLv : L ∈ (x.st (x.tickStep v (aR M S r)) v).tree := (P.L_held_v M F R E U hEndR).2
    have hFL := (GoldilocksCorrectness.Record.Proofs.Executions.lem68_honest_past_finalized M F Fx) S A x R E P.hRoots j
      (x.tickStep v (aR M S r)) w v D L hT hw' hv' hD hLv
      (by rw [P.hL]; exact Nat.lt_succ_of_le hle) (max_le hjE P.hEndStep)
    exact compatible_of_ancestorEq_compatible hFL
      (P.sources_compatible M F R U hG hEnd (P.source_L M F R U hEndR) hX hσ hμ)
  · have hlt : H₂ < (M.chainStateOf S.C D).h_F := Nat.lt_of_not_le hle
    obtain ⟨hJC, -, hFanc, -⟩ :=
      ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2
        (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
    have hFT : (M.chainStateOf S.C D).F ∈ (x.st j w).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w D _ hD hFanc
    obtain ⟨μ', Eb, u, kc, hkc, hkcj, -, hE, -, -, hEr, hupd, n₀, X₀, hCU, hX₀f, hEX₀⟩ :=
      P.cert_source_fast M F R E U Fx hjE hD
        ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hJC) hlt
    have hFE : (M.chainStateOf S.C D).F = Eb :=
      P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hw' hjE hFT)
        ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x
          (le_trans ((time_mono M) x R hkcj.le) hjE) (P.source_inHonestTreeBy_tick M F R E U hE hkc)) hEr
    rw [hFE]
    -- the update of slot `μ'` ran at a tick before the reading, so `μ' ≤ σ + 1` (`hSkew`)
    have hμ'1 : μ' ≤ σ + 1 := by
      by_contra h
      have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show σ + 3 ≤ μ' + 1 by omega)
      have h4 : ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (μ' + 1) : ℕ) : ℝ) := by
        exact_mod_cast hmono
      have hkt := (E.tick_active _ _ _ hkc).2.1
      have hkk := (time_mono M) x R hkcj.le
      linarith
    rcases Nat.lt_or_eq_of_le hμ'1 with hlt' | heq
    · exact P.sources_compatible M F R U hG hEnd hE hX (by omega) hμ
    · -- the slot under proof: `Eb` is `X₀` or an ancestor of it, a block `u`'s update of slot `σ + 1`
      -- made fast, which the votes of slot `σ + 1` (`hV`) make compatible with `X`
      subst heq
      have hAnc : anchorCW S tGAT ≤ M.slotStart S.C (σ + 1 + 1) :=
        le_trans P.hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
      exact compatible_of_ancestorEq_compatible hEX₀
        ((fast_block_compatible_of_votes_core M F) R E U P.hSkew (P.hRoots.mono M (by exact_mod_cast hEnd))
          (P.hCommittees.mono M hEnd) hAnc hupd hCU (hV (by
            have hkt := (E.tick_active _ _ _ hkc).2.1
            rw [show σ + 1 + 1 = σ + 2 from rfl] at hkt
            exact le_trans hkt ((time_mono M) x R hkcj.le))) hX₀f)

/-- `F_compat` at `w`'s tick input to the support cutoff of slot `σ + 2`: under `F_compat`'s hypotheses, with the
support cutoff of slot `σ + 3` in the phase, the finalized block of the state `w`'s tick to the support cutoff of
slot `σ + 2` starts from is compatible with the line source `X`, when `w` is outside the adversary set at that
cutoff.

Why: when `w` ticks to that cutoff, it is honest there, and the tick's real time is at most the cutoff plus
`ΔClockBehind`, less than the support cutoff of slot `σ + 3` less `ΔClockAhead` (`hSkew`), so `F_compat_st`
applies; otherwise the tick input is the initial state, whose finalized block is the genesis block.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: the finalized block an honest validator's tick to the support cutoff of slot `σ + 2` reads is
compatible with every line source of a slot at most `σ`. -/
theorem F_compat_tick (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd3 : M.supportCutoff S.C (σ + 3) ≤ tAwakeEnd) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hV : ∀ u ∈ Hon M S A x (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (σ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (σ + 1))).tree,
        vote = GoldfishVote.mk u (σ + 1) H_u.root ∧ X.AncestorEq H_u) :
    (x.tickInput w (M.supportCutoff S.C (σ + 2))).finalized.compatible X = true := by
  obtain ⟨-, hc2, -, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  obtain ⟨-, hc3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 3)
  have h23 : M.supportCutoff S.C (σ + 2) + 4 * Δ S ≤ M.supportCutoff S.C (σ + 3) := by
    rw [show σ + 2 + 1 = σ + 3 from rfl] at hs2
    omega
  by_cases hex : ∃ k : ℕ, x.lbl k = Event.tick w (M.supportCutoff S.C (σ + 2))
  · obtain ⟨k, hk⟩ := hex
    have hks : x.tickStep w (M.supportCutoff S.C (σ + 2)) = k := (tickStep_eq_of_lbl M) x E hk
    rw [show x.tickInput w (M.supportCutoff S.C (σ + 2)) = x.st k w by
      show x.st (x.tickStep w (M.supportCutoff S.C (σ + 2))) w = x.st k w; rw [hks]]
    have hkt := (E.tick_active _ _ _ hk).2.2
    have h4 : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) + 4 * Δ S ≤ ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) := by
      exact_mod_cast h23
    have hE3 : ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) ≤ ((tAwakeEnd : ℕ) : ℝ) := by exact_mod_cast hEnd3
    have hA0 := E.ahead_nonneg
    have hB0 := E.behind_nonneg
    have hsk := hSkew
    have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast one_le_Δ S
    exact P.F_compat_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ (by omega) (by linarith)
      (E.not_mem_corrupted_of_tick hk) (by linarith) hX hμ (fun _ => hV)
  · have h0 : x.tickStep w (M.supportCutoff S.C (σ + 2)) = 0 := by
      unfold Trace.tickStep
      rw [dif_neg hex]
    rw [show x.tickInput w (M.supportCutoff S.C (σ + 2)) = x.st 0 w by
      show x.st (x.tickStep w (M.supportCutoff S.C (σ + 2))) w = x.st 0 w; rw [h0],
      (getElem_zero_st M F) x R, F.init.initial_finalized S.C w]
    exact (compatible_iff _ _).2 (Or.inl (GoldilocksCorrectness.Proofs.Routines.genesis_ancestorEq X))

/-- **The finalized block is compatible with every line source.** At a time `t ≥ 1` up to the
support cutoff of slot `σ + 2`, in the phase, when the invariant holds at every slot up to `σ`,
an honest validator's finalized block is compatible with every line source of a slot at most `σ`:
at a finalization height at most `H₂` it is an ancestor of `L` (Lemma 89a), at a greater height it
is a line source itself (`cert_source`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.
- `hV`: every vote of slot `σ + 1` that a member of `Hon M S A x (σ + 1)` put on the wire at its tick to the
  vote time of slot `σ + 1` is for a block of its tick input that is `X` or a descendant of `X`; asked only when `t` is after the support cutoff of slot `σ + 2` less `ΔClockAhead`, the earliest real time of a tick that runs the update of slot `σ + 1`.

Read aloud: an honest validator's finalized block is compatible with every line source, within the
phase. -/
theorem F_compat (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ t : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) (ht1 : 1 ≤ t)
    (ht : t ≤ M.supportCutoff S.C (σ + 2)) (hw : w ∉ A.corruptedAtTime x t) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hV : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead < (t : ℝ) →
      ∀ u ∈ Hon M S A x (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (σ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (σ + 1))).tree,
        vote = GoldfishVote.mk u (σ + 1) H_u.root ∧ X.AncestorEq H_u) :
    (x.stateBefore t w).finalized.compatible X = true := by
  obtain ⟨-, hc2, -, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  obtain ⟨-, hc3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 3)
  have h4 : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) + 4 * Δ S ≤ ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) := by
    exact_mod_cast (show M.supportCutoff S.C (σ + 2) + 4 * Δ S ≤ M.supportCutoff S.C (σ + 3) by
      rw [show σ + 2 + 1 = σ + 3 from rfl] at hs2
      omega)
  -- the step before `t` is at a time less than `t` (`stepBefore_time`'s strict bound)
  have htj : x.time (x.stepBefore t) < t := ((stepBefore_time M) x R E ht1).1
  have htE : ((t : ℕ) : ℝ) ≤ (tAwakeEnd : ℕ) := by exact_mod_cast ht.trans hEnd
  have htR : ((t : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) := by exact_mod_cast ht
  have hA0 := E.ahead_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hsk := hSkew
  have hB0 := E.behind_nonneg
  exact P.F_compat_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd (by linarith)
    ((not_mem_corrupted_of_le_time M) x R P.E hw htj.le) (by linarith) hX hμ (fun h => hV (lt_of_le_of_lt h htj))

end PartAHyps

namespace PartAHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}

/-- From the start of slot `r * R + 1` on, an honest validator holds `L` (its tick to the view freeze of
slot `r * R` is before then, `tick_before`, and `L_held` there), with its own chain
state (over the record an equation of `M.chainStateOf S.C L` with itself: the record has no
chain-state cache), at a height at most its greatest chain-state height `hMax M S.C n`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: from the start of the slot after the round's first slot on, an honest validator holds `L`, at a
chain-state height at most its greatest one. -/
theorem L_tall (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (hEnd : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd) {t : ℕ} {w : V}
    (ht0 : M.slotStart S.C (r * S.C.R + 1) ≤ t) (hw : w ∉ A.corruptedAtTime x t) :
    L ∈ (x.stateBefore t w).tree ∧ M.chainStateOf S.C L = M.chainStateOf S.C L ∧
      H₂ + 1 ≤ hMax M S.C (x.stateBefore t w) := by
  obtain ⟨hv0, -, hf0, hs0, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r * S.C.R)
  obtain ⟨-, hc1, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1)
  obtain ⟨hG1, -, -⟩ := P.gstSync M F U (le_refl (r * S.C.R))
  -- `w`, honest at the start of slot `r * R + 1`, ticks to the view freeze of slot `r * R` before it
  have hw' : w ∉ A.corruptedAtTime x (M.slotStart S.C (r * S.C.R + 1)) :=
    (not_mem_corruptedAtTime_of_le M) x R P.E ht0 hw
  obtain ⟨k, hk, hkt⟩ := P.tick_before M F (c := M.viewFreeze S.C (r * S.C.R)) (by omega) (by omega)
    (by omega) hw'
  have hLk := P.L_held M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEnd hk
  have hkR : x.tickStep w (M.viewFreeze S.C (r * S.C.R)) = k := (tickStep_eq_of_lbl M) x P.E hk
  rw [show x.tickInput w (M.viewFreeze S.C (r * S.C.R)) = x.st k w by
    show x.st (x.tickStep w (M.viewFreeze S.C (r * S.C.R))) w = x.st k w; rw [hkR]] at hLk
  have hLT : L ∈ (x.stateBefore t w).tree :=
    (mem_T_mono M F) x R P.E w (le_trans hkt ((stepBefore_mono M) x R P.E ht0)) hLk
  have hge : (M.chainStateOf S.C L).h ≤ hMax M S.C (x.stateBefore t w) := le_hMax M hLT
  rw [P.hL] at hge
  exact ⟨hLT, rfl, hge⟩

/-- `L_tall` at a step: from the start of slot `r * R + 1` on, a validator outside the adversary set at step `j` holds
`L` at `j` (its tick to the view freeze of slot `r * R` is before `j`, `tick_before_st`, and `L_held` there), at a
greatest chain-state height at least `H₂ + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.

Read aloud: at a step after the start of the slot after the round's first slot, an honest validator holds `L`, at a
greatest chain-state height at least `H₂ + 1`. -/
theorem L_tall_st (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (hEnd : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd) {j : ℕ} {w : V}
    (hj0 : ((M.slotStart S.C (r * S.C.R + 1) : ℕ) : ℝ) ≤ x.time j) (hjE : x.time j ≤ tAwakeEnd)
    (hw : w ∉ A.corrupted j) :
    L ∈ (x.st j w).tree ∧ H₂ + 1 ≤ hMax M S.C (x.st j w) := by
  obtain ⟨hv0, -, hf0, hs0, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r * S.C.R)
  obtain ⟨hG1, -, -⟩ := P.gstSync M F U (le_refl (r * S.C.R))
  have hcj : ((M.viewFreeze S.C (r * S.C.R) : ℕ) : ℝ) + Δ S ≤ x.time j := by
    have : ((M.viewFreeze S.C (r * S.C.R) + Δ S : ℕ) : ℝ) ≤ ((M.slotStart S.C (r * S.C.R + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.viewFreeze S.C (r * S.C.R) + Δ S ≤ M.slotStart S.C (r * S.C.R + 1) by omega)
    push_cast at this
    linarith
  obtain ⟨k, hk, hkj⟩ := P.tick_before_st M F (c := M.viewFreeze S.C (r * S.C.R)) (by omega) hcj hjE hw
  have hLk := P.L_held M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEnd hk
  have hkR : x.tickStep w (M.viewFreeze S.C (r * S.C.R)) = k := (tickStep_eq_of_lbl M) x P.E hk
  rw [show x.tickInput w (M.viewFreeze S.C (r * S.C.R)) = x.st k w by
    show x.st (x.tickStep w (M.viewFreeze S.C (r * S.C.R))) w = x.st k w; rw [hkR]] at hLk
  have hLT : L ∈ (x.st j w).tree := (mem_T_mono M F) x R P.E w hkj.le hLk
  have hge : (M.chainStateOf S.C L).h ≤ hMax M S.C (x.st j w) := le_hMax M hLT
  rw [P.hL] at hge
  exact ⟨hLT, hge⟩

/-- `root_compat_of_L` at a step: under its hypotheses, at a step `j` in the phase at which `w` is outside the adversary
set and whose real time is less than the earliest real time of a tick to the support cutoff of slot `σ + 3` (that cutoff
less `ΔClockAhead`), when `w` holds `L` at `j` at a greatest chain-state height at least `H₂ + 1`, the root of `w`'s fork
choice at `j` is compatible with the line source `X`.

Why: `root_compat_of_L`'s argument, read at `j` (`F_compat_st` for the finalized block): an update whose certificate a
block of `w`'s tree at `j` carries ran at a tick before `j`, so of a slot at most `σ + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.
- `hV`: the votes clause of slot `σ + 1`, asked only when `j` is at or after the support cutoff of slot `σ + 2` less
  `ΔClockAhead`, the earliest real time of a tick that runs the update of slot `σ + 1`.

Read aloud: at a step before any tick to the support cutoff of slot `σ + 3`, when an honest validator holds `L` at a
greatest chain-state height at least `H₂ + 1`, the root of its fork choice is compatible with every line source of a slot
at most `σ`. -/
theorem root_compat_of_L_st (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ j : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) (hjE : x.time j ≤ tAwakeEnd)
    (hw' : w ∉ A.corrupted j)
    (hjc : x.time j < ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) - ΔClockAhead) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hV : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead ≤ x.time j →
      ∀ u ∈ Hon M S A x (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (σ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (σ + 1))).tree,
        vote = GoldfishVote.mk u (σ + 1) H_u.root ∧ X.AncestorEq H_u)
    (hLT : L ∈ (x.st j w).tree) (hM : H₂ + 1 ≤ hMax M S.C (x.st j w)) :
    (M.get_fc_root (x.st j w)).compatible X = true := by
  have hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
  -- every tick to the support cutoff of a slot up to `σ + 1` is in the phase (`hSkew`), as in `F_compat`
  have hEndT : ∀ μ'' : ℕ, μ'' ≤ σ → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (μ'' + 1)) →
      x.time k ≤ tAwakeEnd := by
    intro μ'' hμ'' u k hk
    have hkt := (E.tick_active _ _ _ hk).2.2
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show μ'' + 1 ≤ σ + 1 by omega)
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (σ + 1)
    rw [show σ + 1 + 1 = σ + 2 from rfl] at h1
    have hc : ((M.supportCutoff S.C (μ'' + 1) : ℕ) : ℝ) + Δ S ≤ (tAwakeEnd : ℕ) := by
      exact_mod_cast (show M.supportCutoff S.C (μ'' + 1) + Δ S ≤ tAwakeEnd by omega)
    have hsk := hSkew
    have hA0 := E.ahead_nonneg
    linarith
  have hwj : w ∉ A.corrupted j := hw'
  have hInv : M.nodeInv S.C S.P S.X (x.st j w) :=
    ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariant M F S A x R E
      j w) hwj).1
  by_cases hR : M.get_fc_root (x.st j w) = (x.st j w).finalized
  · rw [hR]
    exact P.F_compat_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hjE hw' hjc hX hμ hV
  have key : hMax M S.C (x.st j w) = (x.st j w).justifiedHeight + 1 ∧
      M.get_fc_root (x.st j w) = (x.st j w).justified := by
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.st j w) hInv
      with ⟨hJ, hm, -⟩ | ⟨hF, -⟩
    · exact ⟨hm, hJ⟩
    · exact absurd hF hR
  obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j w
  rw [key.2]
  by_cases hlt : H₂ < (x.st j w).justifiedHeight
  · rw [hhjD] at hlt
    obtain ⟨hJC, hJanc, -⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F)
      S.C D).1 (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
    have hD' : D ∈ (x.st j w).tree := hD
    have hJT : (M.chainStateOf S.C D).J ∈ (x.st j w).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w D _ hD' hJanc
    obtain ⟨μ', Eb, u, kc, hkc, hkcj, -, hE, -, -, hEr, hupd, n₀, X₀, hCU, hX₀f, hEX₀⟩ :=
      P.cert_source_fast M F R E U Fx hjE hD'
        ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hJC) hlt
    have hJE : (M.chainStateOf S.C D).J = Eb :=
      P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hwj hjE hJT)
        ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x
          (le_trans ((time_mono M) x R hkcj.le) hjE) (P.source_inHonestTreeBy_tick M F R E U hE hkc)) hEr
    rw [hJD, hJE]
    -- the update of slot `μ'` ran at a tick before the reading, so `μ' ≤ σ + 1` (`hSkew`), as in `F_compat`
    have hμ'1 : μ' ≤ σ + 1 := by
      by_contra h
      have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show σ + 3 ≤ μ' + 1 by omega)
      obtain ⟨-, hc2, -, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
      obtain ⟨-, hc3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 3)
      have h4 : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) + 4 * Δ S ≤ ((M.supportCutoff S.C (μ' + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show M.supportCutoff S.C (σ + 2) + 4 * Δ S ≤ M.supportCutoff S.C (μ' + 1) by
          rw [show σ + 2 + 1 = σ + 3 from rfl] at hs2
          omega)
      have hkt := (E.tick_active _ _ _ hkc).2.1
      have hkk := (time_mono M) x R hkcj.le
      have h3 : ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (μ' + 1) : ℕ) : ℝ) := by exact_mod_cast hmono
      have hsk := P.hSkew
      have hB0 := E.behind_nonneg
      linarith
    rcases Nat.lt_or_eq_of_le hμ'1 with hlt' | heq
    · exact P.sources_compatible M F R U hG hEnd hE hX (by omega) hμ
    · -- the slot `σ + 1`: `Eb` is `X₀` or an ancestor of it, a block `u`'s update of slot `σ + 1` made
      -- fast, which the votes of slot `σ + 1` (`hV`) make compatible with `X`
      subst heq
      have hAnc : anchorCW S tGAT ≤ M.slotStart S.C (σ + 1 + 1) :=
        le_trans P.hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
      exact compatible_of_ancestorEq_compatible hEX₀
        ((fast_block_compatible_of_votes_core M F) R E U P.hSkew (P.hRoots.mono M (by exact_mod_cast hEnd))
          (P.hCommittees.mono M hEnd) hAnc hupd hCU (hV (by
            have hkt := (E.tick_active _ _ _ hkc).2.1
            rw [show σ + 1 + 1 = σ + 2 from rfl] at hkt
            have hkk := (time_mono M) x R hkcj.le
            linarith)) hX₀f)
  · have hhj : (x.st j w).justifiedHeight = H₂ := by
      have := key.1
      have h1 : (x.st j w).justifiedHeight ≤ H₂ := Nat.le_of_not_lt hlt
      unfold Height at *
      omega
    have hLX := P.sources_compatible M F R U hG hEnd (P.source_L M F R U hEndR) hX hσ hμ
    by_cases h0 : (M.chainStateOf S.C D).h_j = 0
    · have hg := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).2.1 h0
      rw [hJD, hg]
      exact (compatible_iff _ _).2 (Or.inl (GoldilocksCorrectness.Proofs.Routines.genesis_ancestorEq X))
    · have hJh := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).2.2 (Nat.one_le_iff_ne_zero.2 h0)
      have hFJ : (x.st j w).finalized.AncestorEq (x.st j w).justified := by
        have := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E j w
        rw [key.2] at this
        exact this
      -- the finalized block is an ancestor of `L`: at a finalization height at most `H₂` by Lemma 89a; at a
      -- greater one it is a line source taller than the justified block, its descendant, which cannot be
      have hFL : (x.st j w).finalized.AncestorEq L := by
        obtain ⟨DF, hDF, hFDF⟩ :=
          (GoldilocksCorrectness.Record.Statements.Executions.finalizedFromChain_of_exec M F) S A x R E
            j w
        have hFDF' : (x.st j w).finalized = (M.chainStateOf S.C DF).F := hFDF
        rw [hFDF']
        by_cases hle : (M.chainStateOf S.C DF).h_F ≤ H₂
        · have hv' : v ∉ A.corrupted (x.tickStep v (aR M S r)) := E.not_mem_corrupted_of_tick P.hk₀
          have hT : A.AdversaryFewerThanThirdUntil x (validator_count V)
              (max (x.time j) (x.time (x.tickStep v (aR M S r)))) :=
            P.hThird.mono (max_le hjE P.hEndStep)
          have hLv : L ∈ (x.st (x.tickStep v (aR M S r)) v).tree := (P.L_held_v M F R E U hEndR).2
          exact (GoldilocksCorrectness.Record.Proofs.Executions.lem68_honest_past_finalized M F Fx) S A x R E P.hRoots
            j (x.tickStep v (aR M S r)) w v DF L hT hwj hv' hDF hLv
            (by rw [P.hL]; exact Nat.lt_succ_of_le hle) (max_le hjE P.hEndStep)
        · exfalso
          have hlt2 : H₂ < (M.chainStateOf S.C DF).h_F := Nat.lt_of_not_le hle
          obtain ⟨hFC, -, hFanc, -⟩ :=
            ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C DF).2.2
              (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt2))
          have hFT : (M.chainStateOf S.C DF).F ∈ (x.st j w).tree :=
            (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w DF _ hDF hFanc
          obtain ⟨μ₂, Eb₂, u₂, kc₂, hkc₂, hkcj₂, -, hE₂, -, hEh₂, hEr₂⟩ :=
            P.cert_source M F R E U Fx hjE hDF
              ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hFC) hlt2
          have hFE : (M.chainStateOf S.C DF).F = Eb₂ :=
            P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hwj hjE hFT)
              ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x
                (le_trans ((time_mono M) x R hkcj₂.le) hjE) (P.source_inHonestTreeBy_tick M F R E U hE₂ hkc₂)) hEr₂
          rw [hFDF', hFE, hJD] at hFJ
          have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C hFJ
          rw [hEh₂, hJh, ← hhjD, hhj] at h1
          unfold Height at *
          omega
      have hRL := (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_of_tall M F) S.C S.P S.X
        (x.st j w) hInv L hLT hFL (by rw [P.hL, key.1, hhj])
      rw [key.2] at hRL
      exact compatible_of_ancestorEq_compatible hRL hLX

/-- **The root is compatible with every line source, given `L` at the reading.** `root_compat`'s
argument with the one fact it reads from `L_tall` taken as hypotheses: `w` holds `L` before `t`
(`hLT`), and its greatest chain-state height before `t` is at least `H₂ + 1` (`hM`). The root is
the finalized block (`F_compat`), or the justified block: a line source of a slot at most `σ + 1`
when its height is greater than `H₂` (`cert_source_fast`; the slot `σ + 1` by the votes of slot
`σ + 1`, `hV`, as in `F_compat`), and `L` or an ancestor of `L` otherwise (the contest rule, with
the finalized block an ancestor of `L` by Lemma 89a, or a line source taller than the justified
block, which cannot be).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.
- `hV`: every vote of slot `σ + 1` that a member of `Hon M S A x (σ + 1)` put on the wire at its tick to the
  vote time of slot `σ + 1` is for a block of its tick input that is `X` or a descendant of `X`; asked only when `t` is after the support cutoff of slot `σ + 2` less `ΔClockAhead`, the earliest real time of a tick that runs the update of slot `σ + 1`.
- `hLT`, `hM`: `w` holds `L` before `t`, at a greatest chain-state height at least `H₂ + 1`.

Read aloud: when an honest validator holds `L` before `t`, at a greatest chain-state height at least
`H₂ + 1`, its fork-choice root before `t` is compatible with every line source of a slot at most `σ`,
within the phase. -/
theorem root_compat_of_L (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ t : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) (ht0 : M.viewFreeze S.C (r * S.C.R) ≤ t)
    (ht : t ≤ M.supportCutoff S.C (σ + 2)) (hw : w ∉ A.corruptedAtTime x t) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hV : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead < (t : ℝ) →
      ∀ u ∈ Hon M S A x (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (σ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (σ + 1))).tree,
        vote = GoldfishVote.mk u (σ + 1) H_u.root ∧ X.AncestorEq H_u)
    (hLT : L ∈ (x.stateBefore t w).tree) (hM : H₂ + 1 ≤ hMax M S.C (x.stateBefore t w)) :
    (M.get_fc_root (x.stateBefore t w)).compatible X = true := by
  have ht1 : 1 ≤ t := by
    obtain ⟨-, -, hf0, -, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r * S.C.R)
    omega
  obtain ⟨-, hc2, -, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  obtain ⟨-, hc3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 3)
  have h4 : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) + 4 * Δ S ≤ ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) := by
    exact_mod_cast (show M.supportCutoff S.C (σ + 2) + 4 * Δ S ≤ M.supportCutoff S.C (σ + 3) by
      rw [show σ + 2 + 1 = σ + 3 from rfl] at hs2
      omega)
  -- the step before `t` is at a time less than `t` (`stepBefore_time`'s strict bound)
  have htj : x.time (x.stepBefore t) < t := ((stepBefore_time M) x R E ht1).1
  have htE : ((t : ℕ) : ℝ) ≤ (tAwakeEnd : ℕ) := by exact_mod_cast ht.trans hEnd
  have htR : ((t : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) := by exact_mod_cast ht
  have hA0 := E.ahead_nonneg
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast one_le_Δ S
  have hsk := hSkew
  have hB0 := E.behind_nonneg
  exact P.root_compat_of_L_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd (by linarith)
    (Activity.not_mem_corruptedAtTime.1 hw _ ((time_stepBefore_le M) x R E t)) (by linarith) hX hμ
    (fun h => hV (lt_of_le_of_lt h htj)) hLT hM

/-- **The root is compatible with every line source.** From the start of slot `r * R + 1` to
the support cutoff of slot `σ + 2`, in the phase, when the invariant holds at every slot up to
`σ`, an honest validator's fork-choice root is compatible with every line source of a slot at
most `σ`: the finalized block (`F_compat`); or the justified block, a line source when its height
is greater than `H₂` (`cert_source`), and `L` or an ancestor of `L` otherwise (the contest rule).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: an honest validator's fork-choice root is compatible with every line source, within the
phase.

`hV`: every vote of slot `σ + 1` that a member of `Hon M S A x (σ + 1)` put on the wire at its tick to the
vote time of slot `σ + 1` is for a block of its tick input that is `X` or a descendant of `X`; asked only when `t` is after the support cutoff of slot `σ + 2` less `ΔClockAhead`, the earliest real time of a tick that runs the update of slot `σ + 1`. -/
theorem root_compat (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ t : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) (ht0 : M.slotStart S.C (r * S.C.R + 1) ≤ t)
    (ht : t ≤ M.supportCutoff S.C (σ + 2)) (hw : w ∉ A.corruptedAtTime x t) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hV : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead < (t : ℝ) →
      ∀ u ∈ Hon M S A x (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (σ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (σ + 1))).tree,
        vote = GoldfishVote.mk u (σ + 1) H_u.root ∧ X.AncestorEq H_u) :
    (M.get_fc_root (x.stateBefore t w)).compatible X = true := by
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd
  have hfR : M.viewFreeze S.C (r * S.C.R) ≤ t := by
    obtain ⟨-, -, hf0, hs0, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r * S.C.R)
    omega
  obtain ⟨hLT, -, hM⟩ := P.L_tall M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEndR ht0 hw
  exact P.root_compat_of_L M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hfR ht hw hX hμ hV hLT hM

/-- **The root is compatible with every line source, at a step**. `root_compat` read at a step `j`: from
the start of slot `r * R + 1` on, at a step in the phase at which `w` is outside the adversary set and whose real time is
less than the earliest real time of a tick to the support cutoff of slot `σ + 3`, when the invariant holds at every slot
up to `σ`, the root of `w`'s fork choice at `j` is compatible with every line source of a slot at most `σ`.

Why: `L_tall_st` gives `L` at `j` at a greatest chain-state height at least `H₂ + 1`, and `root_compat_of_L_st` the rest.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.
- `hV`: the votes clause of slot `σ + 1`, asked only when `j` is at or after the support cutoff of slot `σ + 2` less
  `ΔClockAhead`.

Read aloud: at a step of the phase before any tick to the support cutoff of slot `σ + 3`, an honest validator's
fork-choice root is compatible with every line source of a slot at most `σ`. -/
theorem root_compat_st (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ j : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd)
    (hj0 : ((M.slotStart S.C (r * S.C.R + 1) : ℕ) : ℝ) ≤ x.time j) (hjE : x.time j ≤ tAwakeEnd)
    (hw' : w ∉ A.corrupted j)
    (hjc : x.time j < ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) - ΔClockAhead) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hV : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead ≤ x.time j →
      ∀ u ∈ Hon M S A x (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (σ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (σ + 1))).tree,
        vote = GoldfishVote.mk u (σ + 1) H_u.root ∧ X.AncestorEq H_u) :
    (M.get_fc_root (x.st j w)).compatible X = true := by
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd
  obtain ⟨hLT, hM⟩ := P.L_tall_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEndR hj0 hjE hw'
  exact P.root_compat_of_L_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hjE hw' hjc hX hμ hV hLT hM


end PartAHyps

namespace PartAHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}

/-- `tall_entry` at a step: a block whose chain state has a height `h ≥ H₂ + 2`, held at step `j` by a validator outside
the adversary set there, in the phase, has an ancestor entry at the height `h − 1` that is a line source of a slot whose
update ran at a step less than `j`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.

Read aloud: a block held at a step, two or more heights past `H₂`, has its entry one height lower on a line source of an
update before that step. -/
theorem tall_entry_st (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {j : ℕ} {w : V}
    (hjE : x.time j ≤ tAwakeEnd) (hw' : w ∉ A.corrupted j) {Y : Block V}
    (hY : Y ∈ (x.st j w).tree) (hYh : H₂ + 2 ≤ (M.chainStateOf S.C Y).h) :
    ∃ (μ' : ℕ) (E : Block V), (∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (μ' + 1)) ∧
        k < j ∧ u ∈ A.active k) ∧
      LineSource M S A x r H₂ μ' E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = (M.chainStateOf S.C Y).h - 1 ∧ E.AncestorEq Y := by
  have hY' : Y ∈ (x.st j w).tree := hY
  obtain ⟨Y', hY'Y, -, -, -, hT', hcert⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem67_first_advance M F) S.C Y
      ((M.chainStateOf S.C Y).h - 1) (by unfold Height at *; omega) (by unfold Height at *; omega)
  have hY'T := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w Y Y' hY' hY'Y
  have hT'T := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w Y' _ hY'T hT'
  obtain ⟨μ', Eb, u, kc, hkc, hkcj, hku, hE, hEe, hEh, hEr⟩ := P.cert_source M F R E U Fx hjE hY'T hcert
    (by unfold Height at *; omega)
  have hTE := P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hw' hjE hT'T)
    ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x (le_trans ((time_mono M) x R hkcj.le) hjE) (P.source_inHonestTreeBy_tick M F R E U hE hkc)) hEr
  refine ⟨μ', Eb, ⟨u, kc, hkc, hkcj, hku⟩, hE, hEe, hEh, ?_⟩
  rw [← hTE]
  exact ancestorEq_trans hT' hY'Y

/-- A block whose chain state has a height `h ≥ H₂ + 2`, held by an honest validator in the phase,
has an ancestor entry at the height `h − 1` that is a line source of a slot whose update ran
before then.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: a held block two or more heights past `H₂` has its entry one height lower on a line
source. -/
theorem tall_entry (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {t : ℕ} {w : V}
    (ht1 : 1 ≤ t) (htE : t ≤ tAwakeEnd) (hw : w ∉ A.corruptedAtTime x t) {Y : Block V}
    (hY : Y ∈ (x.stateBefore t w).tree) (hYh : H₂ + 2 ≤ (M.chainStateOf S.C Y).h) :
    ∃ (μ' : ℕ) (E : Block V), (∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (μ' + 1)) ∧
        k < x.stepBefore t ∧ u ∈ A.active k) ∧
      LineSource M S A x r H₂ μ' E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = (M.chainStateOf S.C Y).h - 1 ∧ E.AncestorEq Y := by
  have htj : x.time (x.stepBefore t) < t := ((stepBefore_time M) x R E ht1).1
  have htE' : ((t : ℕ) : ℝ) ≤ (tAwakeEnd : ℕ) := by exact_mod_cast htE
  exact P.tall_entry_st M F R E U Fx (by linarith) ((not_mem_corrupted_of_le_time M) x R P.E hw htj.le) hY hYh

/-- `viable_candidate_of_held` at a step: at a step `j` in the phase at which `w` is outside the adversary set and whose
real time is less than the earliest real time of a tick to the support cutoff of slot `σ + 2` (that cutoff less
`ΔClockAhead`), when the line sources on `X`'s chain and `L` are in a node state `nH`'s tree, some block `W` of `nH`'s
tree, `X` or a descendant of `X`, has a chain-state height at least `w`'s `head_height_floor` at `j`. Every line source
read here comes from a tick before `j`, so of a slot at most `σ`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.
- `nH`: the node state in which the sources are held; `hheld`, `hLH`: the held sources and `L`.

Read aloud: at a step before any tick to the support cutoff of slot `σ + 2`, when the line sources on a line source's
chain and `L` are in a node state's tree, some block of that tree, that source or a descendant of it, is viable for the
validator at that step. -/
theorem viable_candidate_of_held_st (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    {Δs : ℕ} (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ j : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) (hjE : x.time j ≤ tAwakeEnd)
    (hw' : w ∉ A.corrupted j) (hjc : x.time j < ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    {nH : M.N}
    (hheld : ∀ {μ₁ : ℕ} {X₁ : Block V}, LineSource M S A x r H₂ μ₁ X₁ → μ₁ ≤ σ →
      X.AncestorEq X₁ → X₁ ∈ nH.tree)
    (hLH : L ∈ nH.tree) :
    ∃ W : Block V, X.AncestorEq W ∧ W ∈ nH.tree ∧
      M.head_height_floor (x.st j w) ≤ (M.chainStateOf S.C W).h := by
  have hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
  obtain ⟨hv2, hc2, -, -, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  obtain ⟨hv1, -, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  -- every tick to the support cutoff of a slot up to `σ + 1` is in the phase (`hSkew`), as in `F_compat`
  have hEndT : ∀ μ'' : ℕ, μ'' ≤ σ → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (μ'' + 1)) →
      x.time k ≤ tAwakeEnd := by
    intro μ'' hμ'' u k hk
    have hkt := (E.tick_active _ _ _ hk).2.2
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show μ'' + 1 ≤ σ + 1 by omega)
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (σ + 1)
    rw [show σ + 1 + 1 = σ + 2 from rfl] at h1
    have hc : ((M.supportCutoff S.C (μ'' + 1) : ℕ) : ℝ) + Δ S ≤ (tAwakeEnd : ℕ) := by
      exact_mod_cast (show M.supportCutoff S.C (μ'' + 1) + Δ S ≤ tAwakeEnd by omega)
    have hsk := hSkew
    have hA0 := E.ahead_nonneg
    linarith
  have hwj : w ∉ A.corrupted j := hw'
  have hInv : M.nodeInv S.C S.P S.X (x.st j w) :=
    ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariant M F S A x R E
      j w) hwj).1
  -- a slot whose update ran at a tick before the reading is at most `σ`: a tick to the support cutoff
  -- of slot `σ + 2` or later is at a real time later than the vote time of slot `σ + 2`
  have hslot : ∀ (μ' : ℕ) (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (μ' + 1)) →
      k < j → μ' ≤ σ := by
    intro μ' u k hk hkj
    by_contra h
    have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show σ + 2 ≤ μ' + 1 by omega)
    have hkt := (E.tick_active _ _ _ hk).2.1
    have hkk := (time_mono M) x R hkj.le
    have h4 : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (μ' + 1) : ℕ) : ℝ) := by
      exact_mod_cast hmono
    have hsk := hSkew
    have hB0 := E.behind_nonneg
    linarith
  have hXh := hheld hX hμ (ancestorEq_refl X)
  by_cases hMle : hMax M S.C (x.st j w) ≤ H₂ + 1
  · have hfl := (GoldilocksCorrectness.Record.Proofs.Routines.floor_le_h_max M F) S.C S.P S.X (x.st j w) hInv
    rcases (compatible_iff _ _).1 (P.sources_compatible M F R U hG hEnd (P.source_L M F R U hEndR) hX hσ hμ)
      with h | h
    · refine ⟨X, ancestorEq_refl X, hXh, ?_⟩
      have := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C h
      rw [P.hL] at this
      unfold Height at *
      omega
    · refine ⟨L, h, hLH, ?_⟩
      rw [P.hL]
      unfold Height at *
      omega
  · have hM2 : H₂ + 2 ≤ hMax M S.C (x.st j w) := by unfold Height at *; omega
    obtain ⟨-, ⟨Y, hY, hYh⟩, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j w
    obtain ⟨μ', Eb, ⟨u', k', hk', hkj', -⟩, hE, hEe, hEh, hEY⟩ :=
      P.tall_entry_st M F R E U Fx hjE hw' hY (by rw [hYh]; exact hM2)
    have hμ' : μ' ≤ σ := hslot μ' u' k' hk' hkj'
    rw [hYh] at hEh
    -- the state is not contested
    have hnc : M.fg_contest (x.st j w) = false := by
      cases hcs : M.fg_contest (x.st j w)
      · rfl
      exfalso
      obtain ⟨hbox, B, hBT, -, hBh, hJB⟩ :=
        (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_spec M F) S.C S.P S.X (x.st j w) hInv hcs
      obtain ⟨μB, EB, ⟨uB, kB, hkB, hkjB, -⟩, hEB, hEBe, hEBh, hEBB⟩ :=
        P.tall_entry_st M F R E U Fx hjE hw' hBT (by rw [hBh]; exact hM2)
      have hμB : μB ≤ σ := hslot μB uB kB hkB hkjB
      obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j w
      have hlt : H₂ < (M.chainStateOf S.C D).h_j := by
        rw [← hhjD]
        unfold Height at *
        omega
      obtain ⟨hJC, hJanc, hJh⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F)
        S.C D).1 (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
      have hD' : D ∈ (x.st j w).tree := hD
      have hJT : (M.chainStateOf S.C D).J ∈ (x.st j w).tree :=
        (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w D _ hD' hJanc
      obtain ⟨μJ, EJ, uJ, kJ, hkJ, hkjJ, -, hEJ, hEJe, hEJh, hEJr⟩ := P.cert_source M F R E U Fx hjE hD'
        ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hJC) hlt
      have hμJ : μJ ≤ σ := hslot μJ uJ kJ hkJ hkjJ
      have hJE : (M.chainStateOf S.C D).J = EJ :=
        P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hwj hjE hJT)
          ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x
            (le_trans ((time_mono M) x R hkjJ.le) hjE) (P.source_inHonestTreeBy_tick M F R E U hEJ hkJ)) hEJr
      have hEE : EJ = EB := (GoldilocksCorrectness.Record.Proofs.Routines.entry_eq_of_compatible M F) S.C hEJe hEBe (by
          rw [hEJh, hEBh, ← hhjD, hBh, hbox]
          unfold Height at *
          omega)
        (P.sources_compatible M F R U hG hEnd hEJ hEB hμJ hμB)
      apply hJB
      rw [hJD, hJE, hEE]
      exact hEBB
    have hfloor : M.head_height_floor (x.st j w) = hMax M S.C (x.st j w) - 1 :=
      (GoldilocksCorrectness.Record.Proofs.Routines.head_height_floor_of_not_contested M F) S.C S.P S.X
        (x.st j w) hInv hnc
    rcases (compatible_iff _ _).1 (P.sources_compatible M F R U hG hEnd hX hE hμ hμ') with h | h
    · exact ⟨Eb, h, hheld hE hμ' h, by rw [hfloor, hEh]⟩
    · refine ⟨X, ancestorEq_refl X, hXh, ?_⟩
      have := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C h
      rw [hfloor, ← hEh]
      exact this

/-- **A viable block on a line source's chain, given the held sources.** `viable_candidate`'s
argument with the facts it reads from `source_held` and `L_held` taken as hypotheses, in a node state
`nH`: every line source of a slot at most `σ` that is `X` or a descendant of `X` is in `nH`'s tree
(`hheld`), and so is `L` (`hLH`). From the vote time of slot `σ + 1` to the vote time of
slot `σ + 2`: some block `W`, `X` or a descendant of
`X`, in `nH`'s tree, has a chain-state height at least `w`'s `head_height_floor`. `W` is `L` or `X`
when the greatest chain-state height is at most `H₂ + 1`; otherwise the state is not contested (the
entries one height lower are one block, a line source, `tall_entry` and `cert_source`) and `W` is that
entry or `X`. Every line source read here comes from a tick before the reading, so of a slot at most
`σ`: a tick to the support cutoff of slot `σ + 2` is at a real time later than the vote time of slot
`σ + 2` (`hSkew`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.
- `nH`: the node state in which the sources are held; `hheld`, `hLH`: the held sources and `L`.

Read aloud: when the line sources on a line source's chain and `L` are in a node state's tree, some block of that tree, that source or a descendant of it, is
viable for the validator. -/
theorem viable_candidate_of_held (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    {Δs : ℕ} (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ t : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) (ht0 : M.voteTime S.C (σ + 1) ≤ t)
    (ht : t ≤ M.voteTime S.C (σ + 2)) (hw : w ∉ A.corruptedAtTime x t) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    {nH : M.N}
    (hheld : ∀ {μ₁ : ℕ} {X₁ : Block V}, LineSource M S A x r H₂ μ₁ X₁ → μ₁ ≤ σ →
      X.AncestorEq X₁ → X₁ ∈ nH.tree)
    (hLH : L ∈ nH.tree) :
    ∃ W : Block V, X.AncestorEq W ∧ W ∈ nH.tree ∧
      M.head_height_floor (x.stateBefore t w) ≤ (M.chainStateOf S.C W).h := by
  obtain ⟨hv2, hc2, -, -, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  have ht1 : 1 ≤ t := by
    obtain ⟨hv1, -, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
    omega
  have htj : x.time (x.stepBefore t) < t := ((stepBefore_time M) x R E ht1).1
  have htE : ((t : ℕ) : ℝ) ≤ (tAwakeEnd : ℕ) := by
    exact_mod_cast (show t ≤ tAwakeEnd by omega)
  have h4 : ((t : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) := by
    exact_mod_cast (show t + Δ S ≤ M.supportCutoff S.C (σ + 2) by omega)
  have hsk := hSkew
  have hB0 := E.behind_nonneg
  exact P.viable_candidate_of_held_st M F R E hSkew U Fx hG hσ hEnd (by linarith)
    (Activity.not_mem_corruptedAtTime.1 hw _ ((time_stepBefore_le M) x R E t)) (by linarith) hX hμ hheld hLH

/-- **A viable block on a line source's chain, up to the vote time of slot `σ + 2`.** From the vote time of slot
`σ + 1` to the vote time of slot `σ + 2`: in the phase, when the invariant holds
at every slot up to `σ` and an honest validator's root is a line source `X` of a slot at most `σ` or an ancestor
of it, some block `W`, `X` or a descendant of `X`, held by the validator at its tick to the view freeze of slot
`σ`, has a chain-state height at least its `head_height_floor` (`viable_candidate_of_held`, the line sources and
`L` held at that tick by `source_held` and `L_held`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: up to the vote time of the next slot, when an honest validator's root is on a line source's chain,
some viable block of its tree is that source or a descendant of it. -/
theorem viable_candidate (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ t : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) (ht0 : M.voteTime S.C (σ + 1) ≤ t)
    (ht : t ≤ M.voteTime S.C (σ + 2))
    (hw : w ∉ A.corruptedAtTime x t) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hRX : (M.get_fc_root (x.stateBefore t w)).AncestorEq X) :
    ∃ W : Block V, X.AncestorEq W ∧ W ∈ (x.tickInput w (M.viewFreeze S.C σ)).tree ∧
      M.head_height_floor (x.stateBefore t w) ≤ (M.chainStateOf S.C W).h := by
  obtain ⟨hvσ, hcσ, hfσ, hsσ, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  obtain ⟨hvσ1, hcσ1, -, hsσ1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  obtain ⟨-, hcσ2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  have htc : t ≤ M.supportCutoff S.C (σ + 2) := by
    obtain ⟨hv2, hc2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
    omega
  have hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
  have hEndE : t ≤ tAwakeEnd := le_trans htc hEnd
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hsk := P.hSkew
  -- `w` ticks to the view freeze of every slot `μ₁` from `r * R` to `σ` before `t`
  have htick : ∀ μ₁ : ℕ, r * S.C.R ≤ μ₁ → μ₁ ≤ σ →
      ∃ k : ℕ, x.lbl k = Event.tick w (M.viewFreeze S.C μ₁) ∧ k ≤ x.stepBefore t := by
    intro μ₁ h1 h2
    obtain ⟨hv₁, -, hf₁, hs₁, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ₁
    obtain ⟨hG1, -, -⟩ := P.gstSync M F U h1
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h2
    exact P.tick_before M F (by omega) (by omega) hEndE hw
  obtain ⟨kσ, hkσ, hkσt⟩ := htick σ hσ le_rfl
  have hkσR : x.tickStep w (M.viewFreeze S.C σ) = kσ := (tickStep_eq_of_lbl M) x P.E hkσ
  have hTIσ : x.tickInput w (M.viewFreeze S.C σ) = x.st kσ w := by
    show x.st (x.tickStep w (M.viewFreeze S.C σ)) w = x.st kσ w; rw [hkσR]
  -- a tree read at `w`'s tick to the view freeze of a slot `μ₁ ≤ σ` grows to its tick to the one of `σ`
  have hgrow : ∀ μ₁ : ℕ, μ₁ ≤ σ → ∀ k₁ : ℕ, x.lbl k₁ = Event.tick w (M.viewFreeze S.C μ₁) →
      ∀ B : Block V, B ∈ (x.st k₁ w).tree → B ∈ (x.st kσ w).tree := by
    intro μ₁ h2 k₁ hk₁ B hB
    refine (mem_T_mono M F) x R P.E w ?_ hB
    rcases Nat.lt_or_eq_of_le h2 with hlt | heq
    · obtain ⟨-, -, hf₁, hs₁, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ₁
      have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
        (show μ₁ + 1 ≤ σ by omega)
      have h1 := (P.E.tick_active _ w _ hk₁).2.2
      have h2' := (P.E.tick_active _ w _ hkσ).2.1
      have h4 : ((M.viewFreeze S.C μ₁ : ℕ) : ℝ) + Δ S ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) := by
        exact_mod_cast (show M.viewFreeze S.C μ₁ + Δ S ≤ M.viewFreeze S.C σ by omega)
      exact ((lt_of_time_lt M) x R (by linarith)).le
    · subst heq
      exact (P.E.tick_unique _ _ w _ hk₁ hkσ).le
  -- `w`'s finalized block at a tick before `t` is an ancestor of `X`
  have hFX : ∀ k₁ : ℕ, k₁ ≤ x.stepBefore t → (x.st k₁ w).finalized.AncestorEq X := fun k₁ hk₁ =>
    ancestorEq_trans ((F_ancestorEq_of_le M F) x R P.E w hk₁)
      (ancestorEq_trans ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_stateBefore M F) S A x R P.E t w) hRX)
  -- a line source of a slot at most `σ` on `X`'s chain is held at `w`'s tick to the view freeze of `σ`
  have hheld : ∀ {μ₁ : ℕ} {X₁ : Block V}, LineSource M S A x r H₂ μ₁ X₁ → μ₁ ≤ σ →
      X.AncestorEq X₁ → X₁ ∈ (x.tickInput w (M.viewFreeze S.C σ)).tree := by
    intro μ₁ X₁ hX₁ hμ₁ hXX₁
    obtain ⟨k₁, hk₁, hk₁t⟩ := htick μ₁ (hX₁.slot_ge M F) hμ₁
    have hk₁R : x.tickStep w (M.viewFreeze S.C μ₁) = k₁ := (tickStep_eq_of_lbl M) x P.E hk₁
    have hTI₁ : x.tickInput w (M.viewFreeze S.C μ₁) = x.st k₁ w := by
      show x.st (x.tickStep w (M.viewFreeze S.C μ₁)) w = x.st k₁ w; rw [hk₁R]
    have hE₁ : M.supportCutoff S.C (μ₁ + 1) ≤ tAwakeEnd :=
      le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
    have h := P.source_held M F R E hNet hSkew hRedeliver Sy hΔs U hX₁ hE₁ hk₁ (by
      rw [hTI₁]
      exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans (hFX k₁ hk₁t) hXX₁)))
    rw [hTI₁] at h
    rw [hTIσ]
    exact hgrow μ₁ hμ₁ k₁ hk₁ X₁ h
  have hLH : L ∈ (x.tickInput w (M.viewFreeze S.C σ)).tree := by
    obtain ⟨kL, hkL, -⟩ := htick (r * S.C.R) le_rfl hσ
    have hkLR : x.tickStep w (M.viewFreeze S.C (r * S.C.R)) = kL := (tickStep_eq_of_lbl M) x P.E hkL
    have h := P.L_held M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEndR hkL
    rw [show x.tickInput w (M.viewFreeze S.C (r * S.C.R)) = x.st kL w by
      show x.st (x.tickStep w (M.viewFreeze S.C (r * S.C.R))) w = x.st kL w; rw [hkLR]] at h
    rw [hTIσ]
    exact hgrow (r * S.C.R) hσ kL hkL L h
  exact P.viable_candidate_of_held M F R E hSkew U Fx hG hσ hEnd ht0 ht hw hX hμ hheld hLH

/-- **A viable block on a line source's chain, at a step**. `viable_candidate` read at a step `j`: at a
step in the phase at which `w` is outside the adversary set, at least one delay after the view freeze of slot `σ` and
before the earliest real time of a tick to the support cutoff of slot `σ + 2`, when the invariant holds at every slot up
to `σ` and the root of `w`'s fork choice at `j` is a line source `X` of a slot at most `σ` or an ancestor of it, some
block `W`, `X` or a descendant of `X`, held by `w` at its tick to the view freeze of slot `σ`, has a chain-state height
at least `w`'s `head_height_floor` at `j`.

Why: `viable_candidate`'s argument, read at `j`: `w` ticks to the view freeze of every slot from `r * R` to `σ` before
`j` (`tick_before_st`), holds there the line sources on `X`'s chain (`source_held`) and `L` (`L_held`), and
`viable_candidate_of_held_st` concludes.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.

Read aloud: at such a step, when an honest validator's root is on a line source's chain, some viable block of its tree
at its tick to the view freeze of slot `σ` is that source or a descendant of it. -/
theorem viable_candidate_st (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ j : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) (hjE : x.time j ≤ tAwakeEnd) (hw' : w ∉ A.corrupted j)
    (hjv : ((M.viewFreeze S.C σ : ℕ) : ℝ) + Δ S ≤ x.time j)
    (hjc : x.time j < ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hRX : (M.get_fc_root (x.st j w)).AncestorEq X) :
    ∃ W : Block V, X.AncestorEq W ∧ W ∈ (x.tickInput w (M.viewFreeze S.C σ)).tree ∧
      M.head_height_floor (x.st j w) ≤ (M.chainStateOf S.C W).h := by
  have hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hsk := P.hSkew
  -- `w` ticks to the view freeze of every slot `μ₁` from `r * R` to `σ` before `j`
  have htick : ∀ μ₁ : ℕ, r * S.C.R ≤ μ₁ → μ₁ ≤ σ →
      ∃ k : ℕ, x.lbl k = Event.tick w (M.viewFreeze S.C μ₁) ∧ k ≤ j := by
    intro μ₁ h1 h2
    obtain ⟨hv₁, -, hf₁, hs₁, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ₁
    obtain ⟨-, -, hfσ, hsσ, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
    obtain ⟨hG1, -, -⟩ := P.gstSync M F U h1
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h2
    have hvv : ((M.viewFreeze S.C μ₁ : ℕ) : ℝ) ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) := by
      exact_mod_cast (show M.viewFreeze S.C μ₁ ≤ M.viewFreeze S.C σ by omega)
    obtain ⟨k, hk, hkj⟩ := P.tick_before_st M F (c := M.viewFreeze S.C μ₁) (by omega) (by linarith) hjE hw'
    exact ⟨k, hk, hkj.le⟩
  obtain ⟨kσ, hkσ, hkσt⟩ := htick σ hσ le_rfl
  have hkσR : x.tickStep w (M.viewFreeze S.C σ) = kσ := (tickStep_eq_of_lbl M) x P.E hkσ
  have hTIσ : x.tickInput w (M.viewFreeze S.C σ) = x.st kσ w := by
    show x.st (x.tickStep w (M.viewFreeze S.C σ)) w = x.st kσ w; rw [hkσR]
  -- a tree read at `w`'s tick to the view freeze of a slot `μ₁ ≤ σ` grows to its tick to the one of `σ`
  have hgrow : ∀ μ₁ : ℕ, μ₁ ≤ σ → ∀ k₁ : ℕ, x.lbl k₁ = Event.tick w (M.viewFreeze S.C μ₁) →
      ∀ B : Block V, B ∈ (x.st k₁ w).tree → B ∈ (x.st kσ w).tree := by
    intro μ₁ h2 k₁ hk₁ B hB
    refine (mem_T_mono M F) x R P.E w ?_ hB
    rcases Nat.lt_or_eq_of_le h2 with hlt | heq
    · obtain ⟨-, -, hf₁, hs₁, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ₁
      have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
        (show μ₁ + 1 ≤ σ by omega)
      obtain ⟨-, -, hfσ, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
      have h1 := (P.E.tick_active _ w _ hk₁).2.2
      have h2' := (P.E.tick_active _ w _ hkσ).2.1
      have h4 : ((M.viewFreeze S.C μ₁ : ℕ) : ℝ) + Δ S ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) := by
        exact_mod_cast (show M.viewFreeze S.C μ₁ + Δ S ≤ M.viewFreeze S.C σ by omega)
      exact ((lt_of_time_lt M) x R (by linarith)).le
    · subst heq
      exact (P.E.tick_unique _ _ w _ hk₁ hkσ).le
  -- `w`'s finalized block at a step up to `j` is an ancestor of `X`
  have hFX : ∀ k₁ : ℕ, k₁ ≤ j → (x.st k₁ w).finalized.AncestorEq X := fun k₁ hk₁ =>
    ancestorEq_trans ((F_ancestorEq_of_le M F) x R P.E w hk₁)
      (ancestorEq_trans ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R P.E j w) hRX)
  -- a line source of a slot at most `σ` on `X`'s chain is held at `w`'s tick to the view freeze of `σ`
  have hheld : ∀ {μ₁ : ℕ} {X₁ : Block V}, LineSource M S A x r H₂ μ₁ X₁ → μ₁ ≤ σ →
      X.AncestorEq X₁ → X₁ ∈ (x.tickInput w (M.viewFreeze S.C σ)).tree := by
    intro μ₁ X₁ hX₁ hμ₁ hXX₁
    obtain ⟨k₁, hk₁, hk₁t⟩ := htick μ₁ (hX₁.slot_ge M F) hμ₁
    have hk₁R : x.tickStep w (M.viewFreeze S.C μ₁) = k₁ := (tickStep_eq_of_lbl M) x P.E hk₁
    have hTI₁ : x.tickInput w (M.viewFreeze S.C μ₁) = x.st k₁ w := by
      show x.st (x.tickStep w (M.viewFreeze S.C μ₁)) w = x.st k₁ w; rw [hk₁R]
    have hE₁ : M.supportCutoff S.C (μ₁ + 1) ≤ tAwakeEnd :=
      le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
    have h := P.source_held M F R E hNet hSkew hRedeliver Sy hΔs U hX₁ hE₁ hk₁ (by
      rw [hTI₁]
      exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans (hFX k₁ hk₁t) hXX₁)))
    rw [hTI₁] at h
    rw [hTIσ]
    exact hgrow μ₁ hμ₁ k₁ hk₁ X₁ h
  have hLH : L ∈ (x.tickInput w (M.viewFreeze S.C σ)).tree := by
    obtain ⟨kL, hkL, -⟩ := htick (r * S.C.R) le_rfl hσ
    have hkLR : x.tickStep w (M.viewFreeze S.C (r * S.C.R)) = kL := (tickStep_eq_of_lbl M) x P.E hkL
    have h := P.L_held M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEndR hkL
    rw [show x.tickInput w (M.viewFreeze S.C (r * S.C.R)) = x.st kL w by
      show x.st (x.tickStep w (M.viewFreeze S.C (r * S.C.R))) w = x.st kL w; rw [hkLR]] at h
    rw [hTIσ]
    exact hgrow (r * S.C.R) hσ kL hkL L h
  exact P.viable_candidate_of_held_st M F R E hSkew U Fx hG hσ hEnd hjE hw' hjc hX hμ hheld hLH

end PartAHyps

namespace PartAHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}

/-- **The vote's frame conditions relative to a line source.** In the phase up to the support cutoff of slot `σ + 2`,
when the invariant holds at every slot up to `σ`, a validator `w` whose tick `k` to the vote time of slot `σ + 1` exists
satisfies the first two conjuncts of `StepFrameAt` relative to every line source `X` of a slot at most `σ`: on the state
`w`'s tick to the vote time of slot `σ + 1` starts from, the root of its fork choice is compatible with `X`, and when that
root is `X` or an ancestor of `X`, some block of `w`'s voter tree for slot `σ + 1` that is `X` or a descendant of `X` is a
viable head.

Why: `w` is outside the adversary set at its tick `k`, whose real time is within `ΔClockAhead` before and `ΔClockBehind`
after the vote time. The root by `root_compat_st` at `k`, which asks the votes clause of slot `σ + 1` only when `k` is at or
after the earliest real time of a tick to the support cutoff of slot `σ + 2`, that cutoff less `ΔClockAhead`; the vote
time is `5Δ` before that cutoff and `ΔClockAhead + ΔClockBehind < Δ` (`hSkew`), so it is not asked. The viable head by
`viable_candidate_st` at `k` and `proposal_viable_head_at_tick_st` at `k`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `k`: `w`'s tick to the
  vote time of slot `σ + 1`.

Read aloud: the frame conditions of `w`'s vote of slot `σ + 1` hold relative to every line source, within the phase,
without the votes of slot `σ + 1`. -/
theorem stepFrame_vote_source (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd)
    {k : ℕ} (hk : x.lbl k = Event.tick w (M.voteTime S.C (σ + 1))) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ) :
    (M.fg_to_ac (x.tickInput w (M.voteTime S.C (σ + 1)))).fc_root.compatible X = true ∧
    ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (σ + 1)))).fc_root.AncestorEq X →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (σ + 1)))
        (S.C.t_ ((σ + 1) - 1) + 3 * S.C.Δ) (σ + 1) W ∧
          W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (σ + 1)))).viable_heads ∧
        X.AncestorEq W) := by
  obtain ⟨hvσ, -, hfσ, hsσ, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  obtain ⟨hvσ1, hcσ1, -, hsσ1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  obtain ⟨hv2, hcσ2, -, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  have hv1c5 : M.voteTime S.C (σ + 1) + 5 * Δ S = M.supportCutoff S.C (σ + 2) := by
    rw [show σ + 2 = σ + 1 + 1 by omega] at hcσ2 hs2 hv2 ⊢
    omega
  have hc23 : M.supportCutoff S.C (σ + 2) + 4 * Δ S ≤ M.supportCutoff S.C (σ + 3) := by
    obtain ⟨-, hc3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 3)
    rw [show σ + 2 + 1 = σ + 3 from rfl] at hs2
    omega
  have hks : x.tickStep w (M.voteTime S.C (σ + 1)) = k := (tickStep_eq_of_lbl M) x P.E hk
  have hTI : x.tickInput w (M.voteTime S.C (σ + 1)) = x.st k w := by
    show x.st (x.tickStep w (M.voteTime S.C (σ + 1))) w = x.st k w; rw [hks]
  rw [hTI]
  -- `w` is honest at its tick `k`, whose real time is within the clock bounds of the vote time
  have hwk : w ∉ A.corrupted k := P.E.not_mem_corrupted_of_tick hk
  have hk1 := (P.E.tick_active _ w _ hk).2.1
  have hk2 := (P.E.tick_active _ w _ hk).2.2
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hsk := P.hSkew
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have h5 : ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) + 5 * Δ S = ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) := by
    exact_mod_cast hv1c5
  have h23 : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) + 4 * Δ S ≤ ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) := by
    exact_mod_cast hc23
  have hER : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) ≤ ((tAwakeEnd : ℕ) : ℝ) := by exact_mod_cast hEnd
  have hkE : x.time k ≤ tAwakeEnd := by linarith
  have hfR : ((M.slotStart S.C (r * S.C.R + 1) : ℕ) : ℝ) ≤ x.time k := by
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show r * S.C.R + 1 ≤ σ + 1 by omega)
    have h : ((M.slotStart S.C (r * S.C.R + 1) + Δ S : ℕ) : ℝ) ≤ ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.slotStart S.C (r * S.C.R + 1) + Δ S ≤ M.voteTime S.C (σ + 1) by omega)
    push_cast at h
    linarith
  refine ⟨by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
      -- the votes clause of slot `σ + 1` is not asked at `k`
      exact P.root_compat_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hfR hkE hwk (by linarith) hX hμ
        (fun h => absurd h (by linarith)),
    fun hR => ?_⟩
  -- the viable head: `viable_candidate_st` at `k`, then `proposal_viable_head_at_tick_st` at `k`
  have hR' : (M.get_fc_root (x.st k w)).AncestorEq X := by
    rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact hR
  have hjv : ((M.viewFreeze S.C σ : ℕ) : ℝ) + Δ S ≤ x.time k := by
    have h : ((M.viewFreeze S.C σ + 2 * Δ S : ℕ) : ℝ) ≤ ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.viewFreeze S.C σ + 2 * Δ S ≤ M.voteTime S.C (σ + 1) by omega)
    push_cast at h
    linarith
  obtain ⟨W, hXW, hWT, hφ⟩ := P.viable_candidate_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hkE hwk hjv
    (by linarith) hX hμ hR'
  obtain ⟨hG1, -, -⟩ := P.gstSync M F U hσ
  obtain ⟨kσ, hkσ, hkσk⟩ := P.tick_before_st M F (c := M.viewFreeze S.C σ) (by omega) hjv hkE hwk
  -- `w`'s clock is less than the view freeze of slot `σ` before its tick to it (it is active from `ΔClockAhead` before
  -- that view freeze, `clockValue_lt_of_tick_of_active`)
  have hcG : tGAT + Δ S ≤ M.viewFreeze S.C σ := by omega
  have hwkσ : w ∉ A.corrupted kσ := P.E.not_mem_corrupted_of_tick hkσ
  have hlt := (clockValue_lt_of_tick_of_active M F) P.E hkσ (by omega) (fun j hj hjk => by
    have hjt : x.time j ≤ x.time k := (time_mono M) x R (le_trans hjk hkσk.le)
    have hj1 : x.time j ≤ x.time (j + 1) := (time_mono M) x R (Nat.le_succ j)
    have hcGR : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) := by exact_mod_cast hcG
    have hjc : w ∉ A.corrupted j := fun h => hwkσ (P.E.corrupted_mono j kσ hjk h)
    exact Activity.mem_active.2 ⟨P.hAwake j w (by linarith) (by linarith) hjc, hjc⟩)
  obtain ⟨hWt, hWv⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.proposal_viable_head_at_tick_st M F U) S A x R
    (M.viewFreeze S.C σ) (σ + 1) w W _ _ P.E kσ k hkσ hlt hkσk.le hwk hWT (by rw [Nat.add_sub_cancel]) ⟨rfl, rfl⟩
    (ancestorEq_trans hR' hXW) hφ
  exact ⟨W, (GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ (σ + 1) W).1
    hWt, hWv, hXW⟩

/-- **The step's frame conditions relative to a line source.** In the phase up to the support cutoff of slot `σ + 3`, when the invariant
holds at every slot up to `σ`, every validator honest at the support cutoff of slot `σ + 2`
satisfies `StepFrameAt` relative to every line source of a slot at most `σ`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.
- `hV`: every vote of slot `σ + 1` that a member of `Hon M S A x (σ + 1)` put on the wire at its tick to the
  vote time of slot `σ + 1` is for a block of its tick input that is `X` or a descendant of `X`.

Read aloud: the step's frame conditions hold relative to every line source, within the phase. -/
theorem stepFrame_source (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd3 : M.supportCutoff S.C (σ + 3) ≤ tAwakeEnd)
    (hw : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 2))) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hV : ∀ u ∈ Hon M S A x (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (σ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (σ + 1))).tree,
        vote = GoldfishVote.mk u (σ + 1) H_u.root ∧ X.AncestorEq H_u) : StepFrameAt M S A x X σ w := by
  have hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd3
  obtain ⟨hvσ, -, hfσ, hsσ, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  obtain ⟨hvσ1, hcσ1, -, hsσ1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  obtain ⟨hv2, hcσ2, -, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  have hv1c : M.voteTime S.C (σ + 1) ≤ M.supportCutoff S.C (σ + 2) := by
    rw [show σ + 2 = σ + 1 + 1 by omega] at hcσ2 ⊢
    omega
  have hv12 : M.voteTime S.C (σ + 1) ≤ M.voteTime S.C (σ + 2) := by
    rw [show σ + 2 = σ + 1 + 1 by omega] at hv2 ⊢
    omega
  have hvE : M.voteTime S.C (σ + 1) ≤ tAwakeEnd := le_trans hv1c hEnd
  -- `w`, honest at the support cutoff of slot `σ + 2`, ticks to the vote time of slot `σ + 1` (`tick_before`)
  obtain ⟨hG1, -, -⟩ := P.gstSync M F U hσ
  obtain ⟨kv, hkv, -⟩ := P.tick_before M F (c := M.voteTime S.C (σ + 1)) (by omega)
    (by rw [show σ + 2 = σ + 1 + 1 by omega] at hcσ2 ⊢; omega) hEnd hw
  obtain ⟨h1, h2⟩ := P.stepFrame_vote_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hkv hX hμ
  refine ⟨h1, h2, ?_⟩
  · -- the finalized block at `w`'s tick input to the support cutoff of slot `σ + 2`: `F_compat_tick`, with the support
    -- cutoff of slot `σ + 3` in the phase ( (a″))
    exact P.F_compat_tick M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd3 hX hμ hV

end PartAHyps

namespace PartAHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)


omit F in
/-- **The old lock's slot starts twelve delays after `tGAT`.** With the phase's anchor and Lemma 41's bound
`μ + 1 − k ≤ μ₀` for a slot `μ` after the round's first, slot `μ₀` starts at or after `tGAT + 12 · Δ S`.

Read aloud: the old lock's slot starts well inside the phase. -/
theorem old_lock_slotStart_ge_tGAT (U : UniformSchedule M.toSlotLayout) (S : Setup V)
    {tGAT r μ μ₀ : ℕ}
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hμ : r * S.C.R + 1 ≤ μ) (hμ₀lo : μ + 1 - S.C.k ≤ μ₀) :
    tGAT + 12 * Δ S ≤ M.slotStart S.C μ₀ := by
  rw [GoldilocksCorrectness.Proofs.Routines.anchorCW_eq, U.slotStart_eq] at hAnchor
  rw [U.slotStart_eq]
  have hk := S.C.k_ge_two
  have h1 : μ + 1 ≤ μ₀ + S.C.k := by omega
  have h2 := Nat.mul_le_mul_left (4 * Δ S) h1
  have h3 := Nat.mul_le_mul_left (4 * Δ S) hμ
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at h2
  rw [Nat.mul_add] at hAnchor
  omega

/-- **The windows of Lemma 31's slot-start form at an old lock's slot.** The windows of
`lem31_saved_confirmations_compatible_of_slotStart` at slot `μ₀`, from the bundle and `old_lock_compat`'s
hypotheses, with `tStart := M.dutyWindowStart S.C μ`: `GST` is at most the start of slot `μ₀`; `tStart` is more
than both clock bounds before it; the updater `u` of slot `μ` and the validator `w` honest at the support cutoff of
slot `μ + 2` are active from `tStart` up to their ticks to the view freeze of slot `μ₀` and over the real times from
the start of slot `μ₀` to that view freeze; roots name blocks up to `ΔClockBehind` after the support cutoff of
slot `μ₀ + 1`.

Read aloud: both validators are active over every window the slot-start form of Lemma 31 asks at the old lock's
slot. -/
theorem old_lock_slotStart_windows (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {μ μ₀ : ℕ}
    (hμ : r * S.C.R + 1 ≤ μ) (hEnd1 : M.supportCutoff S.C (μ + 1) ≤ tAwakeEnd) {u : V}
    (hu : u ∈ updaterAt M S A x μ)
    {w : V} (hw : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (μ + 2)))
    -- Lemma 41's bound and the lock's slot before `μ`
    (hμ₀lo : μ + 1 - S.C.k ≤ μ₀) (hμ₀hi : μ₀ + 1 ≤ μ) :
    GST ≤ M.slotStart S.C μ₀ ∧
    ((M.dutyWindowStart S.C μ : ℕ) : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C μ₀ ∧
    u ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C μ : ℕ) : ℤ) (M.viewFreeze S.C μ₀) ∧
    u ∈ A.activeThroughout x (M.slotStart S.C μ₀) (M.viewFreeze S.C μ₀) ∧
    w ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C μ : ℕ) : ℤ) (M.viewFreeze S.C μ₀) ∧
    w ∈ A.activeThroughout x (M.slotStart S.C μ₀) (M.viewFreeze S.C μ₀) ∧
    RootsNameBlocksUntil M A x (((M.supportCutoff S.C (μ₀ + 1) : ℕ) : ℝ) + ΔClockBehind) := by
  have hk := S.C.k_ge_two
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hsk := P.hSkew
  have htime : Monotone x.time := fun _ _ h => (time_mono M) x P.R h
  -- the slot times
  obtain ⟨-, -, hf0, hs0, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ₀
  obtain ⟨-, hc1, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ₀ + 1)
  obtain ⟨-, hcμ1, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 1)
  obtain ⟨-, hcμ2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 2)
  have hssμ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S μ
  have hssμ0 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S μ₀
  have hssμ1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (μ + 1)
  have hssμ2 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (μ + 2)
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  -- the products over the natural numbers
  have hμ1 : μ + 1 ≤ μ₀ + S.C.k := by omega
  have hp1 := Nat.mul_le_mul_left (4 * Δ S) hμ1
  have hp2 := Nat.mul_le_mul_left (4 * Δ S) hμ₀hi
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at hp1
  rw [Nat.mul_add, Nat.mul_one] at hp2
  rw [Nat.mul_add, Nat.mul_one] at hssμ1
  rw [Nat.mul_add] at hssμ2
  -- the margin from the anchor
  have hkey := old_lock_slotStart_ge_tGAT M U S P.hAnchor hμ hμ₀lo
  have hslo : tGAT ≤ M.slotStart S.C μ₀ := by omega
  -- the duty window of slot `μ` (in the phase: at least `tGAT + Δ S`)
  have hdw := P.dws M F U (show r * S.C.R ≤ μ by omega)
  have hdc := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S μ
  have hdc1 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S (μ + 1)
  rw [Nat.mul_add, Nat.mul_one] at hdc1
  -- (i) `tStart + both clock bounds < slotStart μ₀`
  have htS : M.dutyWindowStart S.C μ + Δ S ≤ M.slotStart S.C μ₀ := by
    rcases hdc with h | ⟨h, -⟩ <;> omega
  have htStart : ((M.dutyWindowStart S.C μ : ℕ) : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C μ₀ := by
    have hR : ((M.dutyWindowStart S.C μ + Δ S : ℕ) : ℝ) ≤ ((M.slotStart S.C μ₀ : ℕ) : ℝ) := by exact_mod_cast htS
    push_cast at hR
    linarith
  -- (ii) the saver `u`: honest at every step up to the start of slot `μ₀ + 1`, from its window as an
  -- updater of slot `μ` (`updaterAt`), so active from `tGAT` to that start (`hAwake`, `P.window`)
  have hu' : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (μ + 1)) (M.supportCutoff S.C (μ + 1)) := hu
  have hle : duty_window_start S.C (μ + 1) ≤ ((M.dutyWindowStart S.C (μ + 1) : ℕ) : ℤ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_eq_toNat M.toSlotLayout F.sched U) S (μ + 1)]
    exact Int.self_le_toNat _
  have hleR : ((duty_window_start S.C (μ + 1) : ℤ) : ℝ) ≤ ((M.dutyWindowStart S.C (μ + 1) : ℕ) : ℝ) := by
    have h := (Int.cast_le (R := ℝ)).2 hle
    push_cast at h
    exact h
  have hN1 : M.dutyWindowStart S.C (μ + 1) + Δ S + 2 * Δ S ≤ M.slotStart S.C (μ₀ + 1) := by
    rcases hdc1 with h | ⟨h, -⟩ <;> omega
  have hN2 : M.slotStart S.C (μ₀ + 1) + Δ S ≤ M.supportCutoff S.C (μ + 1) := by omega
  have huR : u ∈ A.activeThroughout x ((M.dutyWindowStart S.C (μ + 1) + Δ S : ℕ) : ℝ)
      ((M.slotStart S.C (μ₀ + 1) : ℕ) : ℝ) := by
    refine (mem_activeThroughout_of_mem_activeThroughoutToTick M F) P.R P.E hu' ?_ ?_
    · push_cast
      linarith
    · have hR : ((M.slotStart S.C (μ₀ + 1) + Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (μ + 1) : ℕ) : ℝ) := by
        exact_mod_cast hN2
      push_cast at hR
      linarith
  have huH : u ∉ A.corruptedAtTime x ((M.slotStart S.C (μ₀ + 1) : ℕ) : ℝ) :=
    P.E.not_mem_corruptedAtTime_of_mem_activeThroughout P.R.time_zero htime
      (by
        have hR : ((M.dutyWindowStart S.C (μ + 1) + Δ S : ℕ) : ℝ) ≤ ((M.slotStart S.C (μ₀ + 1) : ℕ) : ℝ) := by
          exact_mod_cast (show M.dutyWindowStart S.C (μ + 1) + Δ S ≤ M.slotStart S.C (μ₀ + 1) by omega)
        exact hR)
      huR
  have hEndμ₀ : M.slotStart S.C (μ₀ + 1) ≤ tAwakeEnd := by omega
  have huW : u ∈ A.activeThroughout x tGAT (M.slotStart S.C (μ₀ + 1)) := P.window M F huH hEndμ₀
  -- (iii) the receiver `w`: honest at the support cutoff of slot `μ + 2`, so at the start of slot `μ₀ + 1`
  have hwH : w ∉ A.corruptedAtTime x (M.slotStart S.C (μ₀ + 1)) :=
    (not_mem_corruptedAtTime_of_le M) x P.R P.E (show M.slotStart S.C (μ₀ + 1) ≤ M.supportCutoff S.C (μ + 2) by omega) hw
  have hwW : w ∈ A.activeThroughout x tGAT (M.slotStart S.C (μ₀ + 1)) := P.window M F hwH hEndμ₀
  -- (iv) the two window shapes, from a real-time window `[tGAT, slotStart (μ₀ + 1)]`
  have hfR : ((M.viewFreeze S.C μ₀ : ℕ) : ℝ) + Δ S = ((M.slotStart S.C (μ₀ + 1) : ℕ) : ℝ) := by
    exact_mod_cast (show M.viewFreeze S.C μ₀ + Δ S = M.slotStart S.C (μ₀ + 1) by omega)
  have hdwR : (tGAT : ℝ) + Δ S ≤ ((M.dutyWindowStart S.C μ : ℕ) : ℝ) := by exact_mod_cast hdw
  have hwin : ∀ z : V, z ∈ A.activeThroughout x tGAT (M.slotStart S.C (μ₀ + 1)) →
      z ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C μ : ℕ) : ℤ) (M.viewFreeze S.C μ₀) ∧
      z ∈ A.activeThroughout x (M.slotStart S.C μ₀) (M.viewFreeze S.C μ₀) := by
    intro z hz
    refine ⟨?_, ?_⟩
    · refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x P.R P.E (by omega)
        (by exact_mod_cast (show M.dutyWindowStart S.C μ ≤ M.viewFreeze S.C μ₀ by omega)) ?_
      refine Activity.mem_activeThroughout_of_le ?_ ?_ hz
      · push_cast
        linarith
      · linarith
    · exact Activity.mem_activeThroughout_of_le (by exact_mod_cast hslo)
        (by exact_mod_cast (show M.viewFreeze S.C μ₀ ≤ M.slotStart S.C (μ₀ + 1) by omega)) hz
  -- (v) roots to `ΔClockBehind` after the support cutoff of slot `μ₀ + 1`
  have hRoots : RootsNameBlocksUntil M A x (((M.supportCutoff S.C (μ₀ + 1) : ℕ) : ℝ) + ΔClockBehind) := by
    refine (RootsNameBlocksUntil.mono M) ?_ P.hRoots
    have hR : ((M.supportCutoff S.C (μ₀ + 1) + Δ S : ℕ) : ℝ) ≤ (tAwakeEnd : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (μ₀ + 1) + Δ S ≤ tAwakeEnd by omega)
    push_cast at hR
    linarith
  exact ⟨le_trans P.hGST hslo, htStart, (hwin u huW).1, (hwin u huW).2, (hwin w hwW).1, (hwin w hwW).2, hRoots⟩

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}

/-- **An old lock and a slow block.** A lock entry `e₁` that a validator `w`, honest at the support cutoff
of slot `μ + 2`, holds live at its tick input to the vote time of slot `μ + 1`, of a slot `μ₀ < μ`, is
compatible with a block `X₀` passing the slow test in the update of slot `μ + 1` of an updater `u` of slot
`μ`, read at `u`'s tick input to that update's support cutoff: the slow test reads `u`'s confirmation of
slot `μ₀` (Lemma 37), which extends `X₀` and is compatible with `w`'s confirmation of slot `μ₀`, which
extends `e₁`'s block (Lemmas 39, 40, 31). Every read is at the validator's own tick (rule R3).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: an old live lock is compatible with a block passing a member's slow test. -/
theorem old_lock_compat (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {μ μ₀ : ℕ}
    (hμ : r * S.C.R + 1 ≤ μ) (hEnd1 : M.supportCutoff S.C (μ + 1) ≤ tAwakeEnd) {u : V}
    -- `u` is an updater of slot `μ`
    (hu : u ∈ updaterAt M S A x μ)
    {X₀ : Block V}
    -- `X₀` passes the slow test of slot `μ` on `u`'s tick input to the support cutoff of slot `μ + 1`
    (hslow : M.slow_test S.C (x.tickInput u (M.supportCutoff S.C (μ + 1))) μ X₀ = true)
    -- `w` is honest at the support cutoff of slot `μ + 2`
    {w : V} (hw : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (μ + 2)))
    -- `e₁` is a lock entry of `w`'s tick input to the vote time of slot `μ + 1`
    {e₁ : M.LE} (he₁' : e₁ ∈ (x.tickInput w (M.voteTime S.C (μ + 1))).lockEntries)
    (hlive : ((M.voteTime S.C (μ + 1) : ℕ) : Int) < e₁.d)
    (hd₀ : e₁.d = S.C.t_ (μ₀ + S.C.k) + 5 * S.C.Δ) (hμ₀hi : μ₀ + 1 ≤ μ) :
    e₁.B.compatible X₀ = true := by
  have hk := S.C.k_ge_two
  -- the slow test reads `u`'s confirmation `Cu` of slot `μ₀`, with `X₀` equal to `Cu` or an ancestor of it (Lemma 37);
  -- the lock's slot is at least `μ + 1 − k` (Lemma 41)
  obtain ⟨hk1, hsl⟩ := (GoldilocksCorrectness.Record.Statements.Routines.lem37_slow_test_saved_confirmations F)
    S.C _ μ X₀ hslow
  have hμ₀lo : μ + 1 - S.C.k ≤ μ₀ :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem41_slot_of_live_entry M F U) S
      (μ + 1 - S.C.k) μ₀ (M.voteTime S.C (μ + 1)) e₁ hd₀ hlive
      (by rw [show μ + 1 - S.C.k + S.C.k = μ + 1 by omega])
  obtain ⟨Cu, hCu, -, hX₀Cu⟩ := hsl μ₀ hμ₀lo (show μ₀ < μ by omega)
  -- `u`'s confirmation of slot `μ₀` was saved by its update at its tick to the support cutoff of slot
  -- `μ₀ + 1` (Lemma 40), which ran from a state awake for the slot
  obtain ⟨-, hlu, ⟨τu, hτu, hτule⟩, hSu, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem40_saved_confirmation_provenance M F U) S A x R
      (x.tickStep u (M.supportCutoff S.C (μ + 1))) u μ₀ Cu E hCu
  obtain ⟨nu, sentu, hrunu, hAwu⟩ := (cutoff_tick_outcome_of_tick M F U) x R E μ₀ u τu hlu hτu hτule
  have hAu := (confirmationUpdated_of_cutoff_tickInput M F U) x R μ₀ u nu sentu hrunu hAwu
  -- `w`'s lock entry is of a slot `μ₁` whose update ran at its tick to the support cutoff of slot `μ₁ + 1`
  -- (Lemma 39); the deadline makes `μ₁ = μ₀`
  obtain ⟨μ₁, hd₁, -, hlw, ⟨τw, hτw, hτwle⟩, hprov⟩ :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem39_lock_entry_provenance M F U) S A x R
      (x.tickStep w (M.voteTime S.C (μ + 1))) w e₁ E he₁'
  have hμ₁ : μ₀ = μ₁ := by
    have h1 : S.C.t_ (μ₁ + S.C.k) = S.C.t_ (μ₀ + S.C.k) := add_right_cancel (hd₁.symm.trans hd₀)
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := t_lt_of_lt S (show μ₀ + S.C.k < μ₁ + S.C.k by omega)
      rw [h1] at this
      exact lt_irrefl _ this
    · have := t_lt_of_lt S (show μ₁ + S.C.k < μ₀ + S.C.k by omega)
      rw [h1] at this
      exact lt_irrefl _ this
  subst hμ₁
  obtain ⟨nw, sentw, hrunw, hAww⟩ := (cutoff_tick_outcome_of_tick M F U) x R E μ₀ w τw hlw hτw hτwle
  have hAw := (confirmationUpdated_of_cutoff_tickInput M F U) x R μ₀ w nw sentw hrunw hAww
  obtain ⟨e₂, -, -, -, -, ⟨Cw, hCw, he₂Cw⟩, -, he₁e₂, -⟩ := hprov nw sentw hrunw hAww
  have he₁Cw : e₁.B.AncestorEq Cw := ancestorEq_trans he₁e₂ he₂Cw
  --: Lemma 31 for a slot that starts after `GST`, at slot `μ₀`, with the windows from the
  -- bundle (`old_lock_slotStart_windows`)
  obtain ⟨hG31, htStart, hu₁, hu₀, hw₁, hw₀, hRootsC⟩ :=
    old_lock_slotStart_windows M F U P hμ hEnd1 hu hw hμ₀lo hμ₀hi
  have hRoots : RootsNameBlocksUntil M A x
      (max (x.time (x.tickStep u (M.supportCutoff S.C (μ₀ + 1))))
        (x.time (x.tickStep w (M.supportCutoff S.C (μ₀ + 1))))) := by
    refine (RootsNameBlocksUntil.mono M) ?_ hRootsC
    exact max_le (E.tick_active _ u _ hlu).2.2 (E.tick_active _ w _ hlw).2.2
  have hc :=
    (GoldilocksCorrectness.Record.Proofs.Executions.lem31_saved_confirmations_compatible_of_slotStart M F U) S A x R GST
      μ₀ u w nu nw Cu Cw P.E P.hNet P.hSkew P.hRedeliver hG31
      (M.dutyWindowStart S.C μ) htStart hu₁ hu₀ (M.dutyWindowStart S.C μ) htStart hw₁ hw₀
      _ hlu _ hlw hRoots hAu (hSu nu sentu hrunu hAwu) hAw hCw
  exact compatible_of_ancestorEq_both he₁Cw hX₀Cu (compatible_symm' hc)

/-- **The live locks at the base of a fast line source.** For a block `X₁` fast in the update of slot
`μ + 1` of an updater `u` of slot `μ`, a line source of slot `μ`, when the invariant holds at every slot up
to `μ`: every lock entry the revocation of slot `μ + 1` of a validator `w` honest at the support cutoff of
slot `μ + 2` leaves live, at every outcome of `w`'s tick to the vote time of slot `μ + 1` from its tick
input, from a state awake for the slot, is compatible with `X₁` (Lemma 42 at `u` and `w`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: a fast line source is compatible with every live lock a member's revocation leaves at the
slot after it. -/
theorem base_locks_fast (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {μ : ℕ}
    (hG : ∀ σ', σ' ≤ μ → LineInv M S A x r H₂ σ')
    (hEnd : M.supportCutoff S.C (μ + 2) ≤ tAwakeEnd) {u : V}
    -- `u` is an updater of slot `μ`, whose update of slot `μ + 1` leaves `n₀`
    (hu : u ∈ updaterAt M S A x μ) {n₀ : M.N}
    (hU : ConfirmationUpdated M S.C S.P (x.tickInput u (M.supportCutoff S.C (μ + 1)))
      ((M.supportCutoff S.C (μ + 1) : ℕ) : Int) (μ + 1) n₀)
    -- `X₁` is fast in `n₀` and a line source of slot `μ`
    {X₁ : Block V} (hfast : X₁ ∈ M.fastBlocks n₀) (hsrc : LineSource M S A x r H₂ μ X₁)
    {w : V} (hw : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (μ + 2))) :
    ∀ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (μ + 1)))
        ((M.voteTime S.C (μ + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (μ + 1))) (μ + 1) →
      ∀ e ∈ M.lockEntries n'',
        M.is_live (x.tickInput w (M.voteTime S.C (μ + 1)))
          ((M.voteTime S.C (μ + 1) : ℕ) : Int) e = true → e.B.compatible X₁ = true := by
  intro n'' sent hrun hAw e he hl
  have hμ : r * S.C.R ≤ μ := LineSource.slot_ge M F hsrc
  have hEnd1 : M.supportCutoff S.C (μ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd
  -- the slot times, and the bundle's sync bound over the natural numbers
  obtain ⟨hv0, hc0, hf0, hs0, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ
  obtain ⟨hv1, hc1, hf1, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 1)
  obtain ⟨hv2, hc2, hf2, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 2)
  obtain ⟨-, hc3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 3)
  rw [show μ + 1 + 1 = μ + 2 by omega] at hs1
  rw [show μ + 2 + 1 = μ + 3 by omega] at hs2
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hsk := P.hSkew
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have h8 : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have hd := P.hΔs
    have hR : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hR
  have h9 := Nat.mul_le_mul_left (4 * Δ S) S.C.k_ge_two
  have hmx := le_max_left (Δ S) Δs
  have hmx' := le_max_right (Δ S) Δs
  have hm6 := le_max_left (6 * Δ S) Δs
  have hm6' := le_max_right (6 * Δ S) Δs
  have hm3 := le_max_left (3 * Δ S) Δs
  have hm3' := le_max_right (3 * Δ S) Δs
  have hmax6 : max (6 * Δ S) Δs = 6 * Δ S ∨ max (6 * Δ S) Δs = Δs := max_choice _ _
  have hmax3 : max (3 * Δ S) Δs = 3 * Δ S ∨ max (3 * Δ S) Δs = Δs := max_choice _ _
  have hmax1 : max (Δ S) Δs = Δ S ∨ max (Δ S) Δs = Δs := max_choice _ _
  -- the duty window of slot `μ + 1` starts `4 * Δ S * S.C.k − Δ S` before slot `μ + 1` (it is at least `tGAT + Δ S`)
  have hd1 := P.dws M F U (show r * S.C.R ≤ μ + 1 by omega)
  have hdc := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S (μ + 1)
  have hss1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (μ + 1)
  have hdw : M.dutyWindowStart S.C (μ + 1) + 4 * Δ S * S.C.k = M.slotStart S.C (μ + 1) + Δ S := by
    rcases hdc with h | ⟨h, -⟩
    · rw [hss1]; exact h
    · omega
  have hg := P.gstSync M F U hμ
  -- the saver `u`: active from the duty window's start of slot `μ + 1` up to its tick to the support cutoff
  have hu' : u ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (μ + 1) : ℕ) : ℤ)
      (M.supportCutoff S.C (μ + 1)) := by
    have hle : duty_window_start S.C (μ + 1) ≤ ((M.dutyWindowStart S.C (μ + 1) : ℕ) : ℤ) := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_eq_toNat M.toSlotLayout F.sched U) S (μ + 1)]
      exact Int.self_le_toNat _
    obtain ⟨k', hk', hcase⟩ := Activity.mem_activeThroughoutToTick.1 hu
    refine Activity.mem_activeThroughoutToTick.2 ⟨k', hk', ?_⟩
    rcases hcase with h | ⟨k, hkk, c, hc, hl, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨k, hkk, c, le_trans hc hle, hl, h⟩
  have htStart : ((M.dutyWindowStart S.C (μ + 1) : ℕ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (μ + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) := by
    have hN : M.dutyWindowStart S.C (μ + 1) + Δ S ≤ M.supportCutoff S.C (μ + 1) - max (6 * Δ S) Δs := by
      rcases hmax6 with h | h <;> rw [h] <;> omega
    have hR : ((M.dutyWindowStart S.C (μ + 1) + Δ S : ℕ) : ℝ) ≤
        ((M.supportCutoff S.C (μ + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hN
    push_cast at hR
    linarith
  -- the saver as a holder over the sync delay after the view freeze of slot `μ` less one delay or one sync delay
  have hv₀ : u ∈ A.activeThroughout x ((M.viewFreeze S.C μ - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C μ - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
    have hN1 : M.dutyWindowStart S.C (μ + 1) + Δ S ≤ M.viewFreeze S.C μ - max (Δ S) Δs := by
      rcases hmax1 with h | h <;> rw [h] <;> omega
    have hN2 : M.viewFreeze S.C μ - max (Δ S) Δs + Δs + 3 * Δ S ≤ M.supportCutoff S.C (μ + 1) := by
      rcases hmax1 with h | h <;> rw [h] <;> omega
    have hw' := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) P.R P.E hu'
      (a' := M.viewFreeze S.C μ - max (Δ S) Δs) (e := M.viewFreeze S.C μ - max (Δ S) Δs + Δs)
      (by
        have hR : ((M.dutyWindowStart S.C (μ + 1) + Δ S : ℕ) : ℝ) ≤
            ((M.viewFreeze S.C μ - max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hN1
        push_cast at hR ⊢
        linarith)
      (by
        have hR : ((M.viewFreeze S.C μ - max (Δ S) Δs + Δs + 3 * Δ S : ℕ) : ℝ) ≤
            ((M.supportCutoff S.C (μ + 1) : ℕ) : ℝ) := by exact_mod_cast hN2
        push_cast at hR ⊢
        linarith)
    push_cast at hw'
    exact hw'
  -- the receiver `w`, honest at the support cutoff of slot `μ + 2`: active and honest from `tGAT` to that cutoff
  have hwT := P.window M F hw hEnd
  have htStartW : ((M.dutyWindowStart S.C (μ + 1) : ℕ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.viewFreeze S.C μ - max (3 * Δ S) Δs : ℕ) : ℝ) := by
    have hN : M.dutyWindowStart S.C (μ + 1) + Δ S ≤ M.viewFreeze S.C μ - max (3 * Δ S) Δs := by
      rcases hmax3 with h | h <;> rw [h] <;> omega
    have hR : ((M.dutyWindowStart S.C (μ + 1) + Δ S : ℕ) : ℝ) ≤
        ((M.viewFreeze S.C μ - max (3 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hN
    push_cast at hR
    linarith
  have hwW : w ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (μ + 1) : ℕ) : ℤ) (M.viewFreeze S.C μ) := by
    refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x P.R P.E (by omega)
      (by exact_mod_cast (show M.dutyWindowStart S.C (μ + 1) ≤ M.viewFreeze S.C μ by omega)) ?_
    refine Activity.mem_activeThroughout_of_le ?_ ?_ hwT
    · have hR : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.dutyWindowStart S.C (μ + 1) : ℕ) : ℝ) := by exact_mod_cast hd1
      push_cast at hR ⊢
      linarith
    · have hR : ((M.viewFreeze S.C μ + Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
        exact_mod_cast (show M.viewFreeze S.C μ + Δ S ≤ M.supportCutoff S.C (μ + 2) by omega)
      push_cast at hR ⊢
      linarith
  have hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (μ + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (μ + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
    refine Activity.mem_activeThroughout_of_le ?_ ?_ hwT
    · exact_mod_cast (show tGAT ≤ M.supportCutoff S.C (μ + 1) - max (Δ S) Δs by omega)
    · have hR : ((M.supportCutoff S.C (μ + 1) - max (Δ S) Δs + Δs : ℕ) : ℝ) ≤
          ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
        exact_mod_cast (show M.supportCutoff S.C (μ + 1) - max (Δ S) Δs + Δs ≤ M.supportCutoff S.C (μ + 2) by
          rcases hmax1 with h | h <;> rw [h] <;> omega)
      push_cast at hR ⊢
      linarith
  -- `w` ticks to the vote time of slot `μ + 1` (it is active over that clock value's window)
  have htime : Monotone x.time := fun _ _ h => (time_mono M) x R h
  obtain ⟨kV, hkV, hkVa, hkVb⟩ := P.E.tick_of_active (M.voteTime S.C (μ + 1)) (by omega) w fun i h1 h2 => by
    refine Activity.mem_active_of_mem_activeThroughout_of_time htime hwT ?_ ?_
    · have hR : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.voteTime S.C (μ + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show tGAT + Δ S ≤ M.voteTime S.C (μ + 1) by omega)
      push_cast at hR
      linarith
    · have hR : ((M.voteTime S.C (μ + 1) + Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
        exact_mod_cast (show M.voteTime S.C (μ + 1) + Δ S ≤ M.supportCutoff S.C (μ + 2) by omega)
      push_cast at hR
      linarith
  -- `w`'s finalized block at its tick input to the vote time of slot `μ + 1` is compatible with `X₁` (`F_compat_st`)
  have hlT := x.lbl_tickStep ⟨kV, hkV⟩
  obtain ⟨-, hjta, hjtb⟩ := P.E.tick_active _ _ _ hlT
  have hjB : x.time (x.tickStep w (M.voteTime S.C (μ + 1))) + Δ S ≤ ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
    have hR : ((M.voteTime S.C (μ + 1) + 2 * Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C (μ + 1) + 2 * Δ S ≤ M.supportCutoff S.C (μ + 2) by omega)
    push_cast at hR
    linarith
  have hEndR : ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) ≤ (tAwakeEnd : ℝ) := by exact_mod_cast hEnd
  have hc23 : ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (μ + 3) : ℕ) : ℝ) := by
    exact_mod_cast (show M.supportCutoff S.C (μ + 2) + Δ S ≤ M.supportCutoff S.C (μ + 3) by omega)
  have hF : (x.tickInput w (M.voteTime S.C (μ + 1))).finalized.compatible X₁ = true :=
    P.F_compat_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hμ hEnd (by linarith)
      ((not_mem_corrupted_of_le_time M) x R P.E hw (by linarith)) (by linarith) hsrc le_rfl
      (fun h => absurd h (by linarith))
  -- the revocation at `w`'s tick, then Lemma 42 at the saver `u` and the receiver `w`
  have hLR := (locksRevoked_of_voteTime_outcome M F U) S A x R E (μ + 1) w n'' sent hrun hAw
  have hRoots : RootsNameBlocksUntil M A x ((M.viewFreeze S.C μ : ℝ) + ΔClockBehind) := by
    refine (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) ?_ P.hRoots
    have hR : ((M.viewFreeze S.C μ + Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
      exact_mod_cast (show M.viewFreeze S.C μ + Δ S ≤ M.supportCutoff S.C (μ + 2) by omega)
    push_cast at hR
    linarith
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem42_fast_lock_clears_conflicting_locks M F U)
    S A x P.R GST μ X₁ u w n₀ P.E P.hNet P.hSkew P.hRedeliver P.Sy P.hΔs hRoots P.hParent hg.2.1
    (M.dutyWindowStart S.C (μ + 1)) htStart hu' (M.dutyWindowStart S.C (μ + 1)) htStartW hwW hv₀ hw₀ hU hfast
    kV hkV hF n'' hLR e he

/-- **The live locks at the base of a line source are compatible with it.** For a line source
`X₀` of a slot `μ` (of any kind), when the invariant holds at every slot up to `μ`: every lock entry the
revocation of slot `μ + 1` of a validator `w` honest at the support cutoff of slot `μ + 2` leaves live is
compatible with `X₀`; the revocation is read at every outcome of `w`'s tick to the vote time of slot
`μ + 1` from its tick input, from a state awake for the slot (template A1). A lock of a slot
`μ₀ ≥ r * R + 1` is a line source of slot `μ₀`, so the source's confirmation extends its block; a lock
of a slot `μ₀ ≤ r * R` meets a fast `X₀` (Lemma 42) or a slow `X₀`, whose slow test reads the saver's
confirmation of `μ₀` (Lemmas 37, 39, 40, 31).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: the live locks a member's revocation leaves at its tick to the vote time of the slot after a
line source's slot are compatible with that source. -/
theorem base_locks (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {μ : ℕ}
    (hG : ∀ σ', σ' ≤ μ → LineInv M S A x r H₂ σ')
    (hEnd : M.supportCutoff S.C (μ + 2) ≤ tAwakeEnd) {X₀ : Block V}
    (hsrc : LineSource M S A x r H₂ μ X₀)
    {w : V} (hw : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (μ + 2))) :
    ∀ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (μ + 1)))
        ((M.voteTime S.C (μ + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (μ + 1))) (μ + 1) →
      ∀ e ∈ M.lockEntries n'',
        M.is_live (x.tickInput w (M.voteTime S.C (μ + 1)))
          ((M.voteTime S.C (μ + 1) : ℕ) : Int) e = true → e.B.compatible X₀ = true := by
  intro n'' sent hrun hAw e he hl
  have hk := S.C.k_ge_two
  obtain ⟨hv0, hc0, hf0, hs0, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ
  obtain ⟨hv1, hc1, hf1, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 1)
  obtain ⟨hv2, hc2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 2)
  rw [show μ + 1 + 1 = μ + 2 by omega] at hs1
  have hEnd1 : M.supportCutoff S.C (μ + 1) ≤ tAwakeEnd := by omega
  -- the entry `e₁` of `w`'s tick input that `e` was moved from (`LocksRevoked`, slot `μ + 1 ≥ 1`)
  rcases (locksRevoked_of_voteTime_outcome M F U) S A x R E (μ + 1) w n'' sent hrun hAw with
      ⟨h0, -⟩ | ⟨-, hmv, -⟩
  · exact absurd h0 (Nat.succ_ne_zero _)
  obtain ⟨e₁, he₁, hl₁, -, hmov⟩ := hmv e he
  have hee₁ : e.B.AncestorEq e₁.B := hmov.1.2.2.1
  have hl₁' := hl₁
  simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hl₁'
  -- the line source's saver `u`, its update `n₀`, its confirmation `C₀`
  obtain ⟨u, huU, n₀, C₀, X₁, hU, hn₀, hC₀, hXX₁, hX₁C₀, hkind⟩ := hsrc
  -- where `e₁` comes from (Lemma 39 at `w`'s tick to the vote time of slot `μ + 1`): `w`'s update of a slot
  -- `μ₀ + 1` at its tick to the support cutoff, at an earlier step
  obtain ⟨μ₀, hd₀, hk₁, hl₁t, ⟨τ, hτ, hτle⟩, h39⟩ :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem39_lock_entry_provenance M F U) S A x R
      (x.tickStep w (M.voteTime S.C (μ + 1))) w e₁ E he₁
  have hexT : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (μ + 1)) := by
    by_contra hno
    have h0 : x.tickStep w (M.voteTime S.C (μ + 1)) = 0 := by
      unfold Trace.tickStep
      rw [dif_neg hno]
    omega
  have hlT := x.lbl_tickStep hexT
  -- the tick to the support cutoff of slot `μ₀ + 1` comes first (`clock_mono`), so `μ₀ + 1 ≤ μ`
  have hcT : M.supportCutoff S.C (μ₀ + 1) ≤ M.voteTime S.C (μ + 1) :=
    E.clock_mono _ _ w _ _ hk₁ (E.not_mem_corrupted_of_tick hlT) (Or.inl hl₁t) (Or.inl hlT)
  have hμ₀ : μ₀ + 1 ≤ μ := by
    by_contra h
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show μ + 1 ≤ μ₀ + 1 by omega)
    obtain ⟨-, hc3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ₀ + 1)
    omega
  by_cases hnew : r * S.C.R + 1 ≤ μ₀
  · -- a lock of a slot after the round's first: its block is a line source of slot `μ₀` (`w` is an updater
    -- of slot `μ₀`, the bundle's `hActive`), so the invariant at `μ` puts it on `C₀`'s chain
    have hdw₀ := P.dws M F U (show r * S.C.R ≤ μ₀ by omega)
    have hcm := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show μ₀ + 1 ≤ μ + 2 by omega)
    have hw₀ : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (μ₀ + 1)) :=
      (not_mem_corruptedAtTime_of_le M) x R E hcm hw
    have hwU : w ∈ updaterAt M S A x μ₀ := (P.hActive μ₀ (by omega) (by omega) w hw₀).2
    obtain ⟨n₁, sent₁, hrun₁, hAw₁, hSv₁, -, -, -⟩ :=
      (update_state_of_tick M F U) S A x R μ₀ w E hl₁t ⟨τ, hτ, hτle⟩
    obtain ⟨e₀, -, -, -, -, ⟨C', hC', he₀C'⟩, hkind₀, he₁e₀, -⟩ := h39 n₁ sent₁ hrun₁ hAw₁
    have hsrc₀ : LineSource M S A x r H₂ μ₀ e₁.B :=
      ⟨w, hwU, n₁, C', e₀.B, (confirmationUpdated_of_cutoff_tickInput M F U) x R μ₀ w n₁ sent₁ hrun₁ hAw₁,
        hC', (congrFun hSv₁ μ₀).trans hC', he₁e₀, he₀C', Or.inr (Or.inl ⟨hnew, hkind₀⟩)⟩
    have h1 := (hG μ le_rfl μ₀ e₁.B hsrc₀ hμ₀).2 u huU C₀ hC₀
    exact compatible_of_ancestorEq_both (ancestorEq_trans hee₁ h1) (ancestorEq_trans hXX₁ hX₁C₀)
      ((compatible_iff _ _).2 (Or.inl (ancestorEq_refl _)))
  -- an old lock (`μ₀ ≤ r * R`), by the kind of the source
  rcases hkind with ⟨hμr, hfast, hH⟩ | ⟨hμ1, hfast | hslow⟩ | hμk
  · -- fast at the round's first slot: Lemma 42 (`base_locks_fast`)
    have hsrc₁ : LineSource M S A x r H₂ μ X₁ :=
      ⟨u, huU, n₀, C₀, X₁, hU, hn₀, hC₀, ancestorEq_refl X₁, hX₁C₀, Or.inl ⟨hμr, hfast, hH⟩⟩
    exact compatible_symm' (GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible hXX₁
      (compatible_symm' (P.base_locks_fast M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hEnd huU hU hfast hsrc₁ hw
        n'' sent hrun hAw e he hl)))
  · -- fast after the round's first slot: Lemma 42 (`base_locks_fast`)
    have hsrc₁ : LineSource M S A x r H₂ μ X₁ :=
      ⟨u, huU, n₀, C₀, X₁, hU, hn₀, hC₀, ancestorEq_refl X₁, hX₁C₀, Or.inr (Or.inl ⟨hμ1, Or.inl hfast⟩)⟩
    exact compatible_symm' (GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible hXX₁
      (compatible_symm' (P.base_locks_fast M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hEnd huU hU hfast hsrc₁ hw
        n'' sent hrun hAw e he hl)))
  · -- slow: its slow test reads `u`'s confirmation of slot `μ₀` (`old_lock_compat`)
    exact GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible hee₁
      (compatible_symm' (GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible hXX₁
        (compatible_symm' (P.old_lock_compat M F R E hNet hSkew hRedeliver Sy hΔs U hμ1 hEnd1 huU hslow hw he₁
          hl₁'.1 hd₀ hμ₀))))
  · -- `μ ≥ r * R + k`: a lock live at the vote time of slot `μ + 1` is of a slot at least `μ + 1 − k`
    -- (Lemma 41), after the round's first
    exfalso
    have h41 := (GoldilocksCorrectness.Record.Statements.Executions.lem41_slot_of_live_entry M F U) S
      (μ + 1 - S.C.k) μ₀ (M.voteTime S.C (μ + 1)) e₁ hd₀ hl₁'.1
      (by rw [show μ + 1 - S.C.k + S.C.k = μ + 1 by omega])
    omega

end PartAHyps

namespace PartAHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}

/-- The members of a slot `s ≥ r * R` in the phase are honest active validators and updaters of
it, and the members of slot `s + 1` are members of slot `s`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: the members of a slot of the phase are honest active validators and updaters of it, and
those of the next slot are among them. -/
theorem members_sets (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {s : ℕ}
    (hs : r * S.C.R ≤ s) (hEnd : M.supportCutoff S.C (s + 1) ≤ tAwakeEnd) :
    Hon M S A x s ⊆ honestActiveAt M S A x s ∧ Hon M S A x s ⊆ updaterAt M S A x s := by
  have hdw := P.dws M F U hs
  refine ⟨((GoldilocksCorrectness.Record.Proofs.Executions.roundMembers_subset_honestActiveAt M F U) S A tGAT tAwakeEnd s P.R P.E P.hActive
    (by omega) hEnd).1, fun u hu => ?_⟩
  unfold Hon roundMembers at hu
  exact (P.hActive s (by omega) hEnd u (Finset.mem_sdiff.1 hu).2).2

/-- The committee of every slot `s ≥ r * R` has more than half of its members in `Hon M S Sched s`.

The variables:
- `M`: the model; `F`: its facts; `hE`: the update of slot `s` is at most `tAwakeEnd`, up to which
  the bundle's committee sleepiness is read.

Read aloud: more than half of every committee of the phase is made of members. -/
theorem committee {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {s : ℕ}
    (hs : r * S.C.R ≤ s) (hE : M.supportCutoff S.C (s + 1) ≤ tAwakeEnd) :
    (S.P.committee s).card < 2 * (S.P.committee s ∩ Hon M S A x s).card := by
  exact
    (GoldilocksCorrectness.Record.Proofs.Executions.committee_majority_of_committeeSleepiness M F) S A x (anchorCW S tGAT) s P.hCommittees
      (le_trans P.hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))) hE

/-- **The votes clause of the slot after a line source's own slot.** The case `μ = σ` of `votes_source`: within the
phase up to the support cutoff of slot `σ + 2`, when the invariant holds at every slot up to `σ`, every vote of slot
`σ + 1` that a member of `Hon M S A x (σ + 1)` put on the wire at its tick to the vote time of slot `σ + 1` is for a block
of its tick input that is the line source `X` of slot `σ` or a descendant of `X`. The invariant `LineInv σ` covers only the
sources of slots before `σ`; this is the votes half of the base (`base_source` for a source of a slot `σ ≥ r * R + 1`,
`fast_block_base` for the source of kind (a) at the slot `r * R`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: within the phase, every honest vote of the slot after a line source's slot is for a block of the voter's
tick input that is that source or a descendant of it. -/
theorem votes_source_base (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) {X : Block V}
    (hX : LineSource M S A x r H₂ σ X) :
    ∀ u ∈ Hon M S A x (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (σ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (σ + 1))).tree,
        vote = GoldfishVote.mk u (σ + 1) H_u.root ∧ X.AncestorEq H_u := by
  intro w hw vote hSend
  have hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd
  obtain ⟨u₀, hu₀, n₀, C₀, X₀, hU, hS, hC₀, hXX₀, hX₀C₀, hk⟩ := hX
  have hX₀ : LineSource M S A x r H₂ σ X₀ :=
    ⟨u₀, hu₀, n₀, C₀, X₀, hU, hS, hC₀, ancestorEq_refl X₀, hX₀C₀, hk⟩
  -- the slot times, and the bundle's sync bound over the natural numbers
  obtain ⟨hv0, hc0, hf0, hs0, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  obtain ⟨hv1, hc1, hf1, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  obtain ⟨hv2, hc2, hf2, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  rw [show σ + 1 + 1 = σ + 2 by omega] at hs1
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hsk := P.hSkew
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have h8 : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have hd := P.hΔs
    have hR : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hR
  have h9 := Nat.mul_le_mul_left (4 * Δ S) S.C.k_ge_two
  have hmx := le_max_left (Δ S) Δs
  have hmx' := le_max_right (Δ S) Δs
  have hm6 := le_max_left (6 * Δ S) Δs
  have hm6' := le_max_right (6 * Δ S) Δs
  have hm3 := le_max_left (3 * Δ S) Δs
  have hm3' := le_max_right (3 * Δ S) Δs
  have hmax6 : max (6 * Δ S) Δs = 6 * Δ S ∨ max (6 * Δ S) Δs = Δs := max_choice _ _
  have hmax3 : max (3 * Δ S) Δs = 3 * Δ S ∨ max (3 * Δ S) Δs = Δs := max_choice _ _
  have hmax1 : max (Δ S) Δs = Δ S ∨ max (Δ S) Δs = Δs := max_choice _ _
  -- the duty window of slot `σ + 1` starts `4 * Δ S * S.C.k − Δ S` before slot `σ + 1` (it is at least `tGAT + Δ S`)
  have hd1 := P.dws M F U (show r * S.C.R ≤ σ + 1 by omega)
  have hdc := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S (σ + 1)
  have hss1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hdw : M.dutyWindowStart S.C (σ + 1) + 4 * Δ S * S.C.k = M.slotStart S.C (σ + 1) + Δ S := by
    rcases hdc with h | ⟨h, -⟩
    · rw [hss1]; exact h
    · omega
  have hg := P.gstSync M F U hσ
  have hg1 := P.gstSync M F U (show r * S.C.R ≤ σ + 1 by omega)
  -- the saver `u₀`: active from the duty window's start of slot `σ + 1` up to its tick to the support cutoff
  have hu₀' : u₀ ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (σ + 1) : ℕ) : ℤ)
      (M.supportCutoff S.C (σ + 1)) := by
    have hle : duty_window_start S.C (σ + 1) ≤ ((M.dutyWindowStart S.C (σ + 1) : ℕ) : ℤ) := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_eq_toNat M.toSlotLayout F.sched U) S (σ + 1)]
      exact Int.self_le_toNat _
    obtain ⟨k', hk', hcase⟩ := Activity.mem_activeThroughoutToTick.1 hu₀
    refine Activity.mem_activeThroughoutToTick.2 ⟨k', hk', ?_⟩
    rcases hcase with h | ⟨k, hkk, c, hc, hl, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨k, hkk, c, le_trans hc hle, hl, h⟩
  have htStart : ((M.dutyWindowStart S.C (σ + 1) : ℕ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (σ + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) := by
    have hN : M.dutyWindowStart S.C (σ + 1) + Δ S ≤ M.supportCutoff S.C (σ + 1) - max (6 * Δ S) Δs := by
      rcases hmax6 with h | h <;> rw [h] <;> omega
    have hR : ((M.dutyWindowStart S.C (σ + 1) + Δ S : ℕ) : ℝ) ≤
        ((M.supportCutoff S.C (σ + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hN
    push_cast at hR
    linarith
  -- the saver as a holder over the sync delay after the view freeze of slot `σ` less one delay or one sync delay
  have hv₀ : u₀ ∈ A.activeThroughout x ((M.viewFreeze S.C σ - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C σ - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
    have hN1 : M.dutyWindowStart S.C (σ + 1) + Δ S ≤ M.viewFreeze S.C σ - max (Δ S) Δs := by
      rcases hmax1 with h | h <;> rw [h] <;> omega
    have hN2 : M.viewFreeze S.C σ - max (Δ S) Δs + Δs + 3 * Δ S ≤ M.supportCutoff S.C (σ + 1) := by
      rcases hmax1 with h | h <;> rw [h] <;> omega
    have hw' := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) P.R P.E hu₀'
      (a' := M.viewFreeze S.C σ - max (Δ S) Δs) (e := M.viewFreeze S.C σ - max (Δ S) Δs + Δs)
      (by
        have hR : ((M.dutyWindowStart S.C (σ + 1) + Δ S : ℕ) : ℝ) ≤
            ((M.viewFreeze S.C σ - max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hN1
        push_cast at hR ⊢
        linarith)
      (by
        have hR : ((M.viewFreeze S.C σ - max (Δ S) Δs + Δs + 3 * Δ S : ℕ) : ℝ) ≤
            ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) := by exact_mod_cast hN2
        push_cast at hR ⊢
        linarith)
    push_cast at hw'
    exact hw'
  -- the voter `w`, a member of slot `σ + 1`: active and honest from `tGAT` to the support cutoff of slot `σ + 2`
  have hwT := P.member M F hw hEnd
  have htStartW : ((M.dutyWindowStart S.C (σ + 1) : ℕ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.viewFreeze S.C σ - max (3 * Δ S) Δs : ℕ) : ℝ) := by
    have hN : M.dutyWindowStart S.C (σ + 1) + Δ S ≤ M.viewFreeze S.C σ - max (3 * Δ S) Δs := by
      rcases hmax3 with h | h <;> rw [h] <;> omega
    have hR : ((M.dutyWindowStart S.C (σ + 1) + Δ S : ℕ) : ℝ) ≤
        ((M.viewFreeze S.C σ - max (3 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hN
    push_cast at hR
    linarith
  have hwW : w ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (σ + 1) : ℕ) : ℤ) (M.viewFreeze S.C σ) := by
    refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x P.R P.E (by omega)
      (by exact_mod_cast (show M.dutyWindowStart S.C (σ + 1) ≤ M.viewFreeze S.C σ by omega)) ?_
    refine Activity.mem_activeThroughout_of_le ?_ ?_ hwT
    · have hR : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.dutyWindowStart S.C (σ + 1) : ℕ) : ℝ) := by exact_mod_cast hd1
      push_cast at hR ⊢
      linarith
    · have hR : ((M.viewFreeze S.C σ + Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) := by
        exact_mod_cast (show M.viewFreeze S.C σ + Δ S ≤ M.supportCutoff S.C (σ + 2) by omega)
      push_cast at hR ⊢
      linarith
  have hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (σ + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (σ + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
    refine Activity.mem_activeThroughout_of_le ?_ ?_ hwT
    · exact_mod_cast (show tGAT ≤ M.supportCutoff S.C (σ + 1) - max (Δ S) Δs by omega)
    · have hR : ((M.supportCutoff S.C (σ + 1) - max (Δ S) Δs + Δs : ℕ) : ℝ) ≤
          ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) := by
        exact_mod_cast (show M.supportCutoff S.C (σ + 1) - max (Δ S) Δs + Δs ≤ M.supportCutoff S.C (σ + 2) by
          rcases hmax1 with h | h <;> rw [h] <;> omega)
      push_cast at hR ⊢
      linarith
  -- the voter's frame conditions relative to `X₀` (`stepFrame_vote_source`, at the tick of `hSend`) and its live
  -- locks (`base_locks`)
  obtain ⟨i, hi, hsent⟩ := hSend
  have hwc : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 2)) := by
    unfold Hon roundMembers at hw
    exact (Finset.mem_sdiff.1 hw).2
  obtain ⟨hF2, hF3⟩ := P.stepFrame_vote_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hi hX₀ le_rfl
  -- A4 at the saver `u₀`, for `X₀`
  obtain ⟨H_w, hHw, hvote, hX₀H⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.lem36c_fast_ancestor_extended_held M F U)
    S A x P.R GST σ C₀ X₀ u₀ w n₀ vote P.E P.hNet P.hSkew P.hRedeliver P.Sy P.hΔs
    (P.hRoots.mono M (by exact_mod_cast hEnd1)) P.hParent hg.2.1
    (M.dutyWindowStart S.C (σ + 1)) htStart hu₀' hv₀
    (M.dutyWindowStart S.C (σ + 1)) htStartW hwW hw₀ hU hS hX₀C₀ hF2 hF3
    (P.base_locks M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hEnd hX₀ hwc) ⟨i, hi, hsent⟩
  exact ⟨H_w, hHw, hvote, ancestorEq_trans hXX₀ hX₀H⟩

/-- **The votes clause of the slot after the invariant's slots**. Within the phase up to the support
cutoff of slot `σ + 2`, when the invariant holds at every slot up to `σ`: every vote of slot `σ + 1` that a member of
`Hon M S A x (σ + 1)` put on the wire at its tick to the vote time of slot `σ + 1` is for a block of its tick input that
is the line source `X` (of a slot at most `σ`) or a descendant of `X`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: within the phase, when the invariant holds up to slot `σ`, every honest vote of slot `σ + 1` is for a block
of the voter's tick input that is `X` or a descendant of `X`. -/
theorem votes_source (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ) :
    ∀ u ∈ Hon M S A x (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (σ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (σ + 1))).tree,
        vote = GoldfishVote.mk u (σ + 1) H_u.root ∧ X.AncestorEq H_u := by
  intro u hu vote hSend
  rcases Nat.lt_or_eq_of_le hμ with hlt | heq
  swap
  · -- the source's own slot: the votes half of the base (`votes_source_base`)
    subst heq
    exact P.votes_source_base M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hX u hu vote hSend
  -- a source of a slot `μ < σ`: the invariant at slot `σ` (`hG`) and Lemma 79a at the vote ticks of slot `σ + 1`
  have hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd
  have hEnd0 : M.supportCutoff S.C σ ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd1
  obtain ⟨hvσ1, hcσ1, -, hsσ1, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  obtain ⟨hv2, hcσ2, -, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  have hv1c5 : M.voteTime S.C (σ + 1) + 5 * Δ S = M.supportCutoff S.C (σ + 2) := by
    rw [show σ + 2 = σ + 1 + 1 by omega] at hcσ2 hs2 hv2 ⊢
    omega
  have hvc1 : M.voteTime S.C (σ + 1) ≤ M.supportCutoff S.C (σ + 1) := by omega
  -- every member of `Hon M S A x (σ + 1)` ticks to the vote time of slot `σ + 1` (`tick_before`, read at the support
  -- cutoff of slot `σ + 2`, up to which the member is honest)
  have htk : ∀ w ∈ Hon M S A x (σ + 1), ∃ k : ℕ, x.lbl k = Event.tick w (M.voteTime S.C (σ + 1)) := by
    intro w hw
    have hwc : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 2)) := by
      unfold Hon roundMembers at hw
      exact (Finset.mem_sdiff.1 hw).2
    obtain ⟨hG1, -, -⟩ := P.gstSync M F U (show r * S.C.R ≤ σ + 1 by omega)
    have hmx := le_max_left (Δ S) Δs
    obtain ⟨k, hk, -⟩ := P.tick_before M F (c := M.voteTime S.C (σ + 1)) (t := M.supportCutoff S.C (σ + 2))
      (by omega) (by omega) hEnd hwc
    exact ⟨k, hk⟩
  have hvoters : ∀ u' ∈ S.P.committee σ ∩ Hon M S A x σ, u' ∈ Hon M S A x σ ∧ u' ∈ S.P.committee σ ∧
      ∃ vote : GoldfishVote V, vote.val_index = u' ∧ vote.slot = σ ∧
        ∃ i : ℕ, x.lbl i = Event.tick u' (M.voteTime S.C σ) ∧
          (⟨u', NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i := by
    intro u' hu'
    obtain ⟨hK, hH⟩ := Finset.mem_inter.1 hu'
    obtain ⟨i, vote', hl, hvi, hvs, hsent⟩ :=
      (GoldilocksCorrectness.Record.Proofs.Executions.honest_active_votes M F U) S A x R σ u' P.E P.hSkew
        ((P.members_sets M F U hσ hEnd1).1 hH) hK
    exact ⟨hH, hK, vote', hvi, hvs, i, hl, hsent⟩
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem79a_votes_step_sets M F U) S A x R GST σ
    (Hon M S A x σ) (Hon M S A x (σ + 1)) (S.P.committee σ ∩ Hon M S A x σ) X P.E P.hNet P.hSkew P.hRedeliver P.Sy P.hΔs
    ((per_tick_roots_of_roots_until M F) x P.E P.hRoots (by
      have hB0 := P.E.behind_nonneg
      have hA0 := P.E.ahead_nonneg
      have hsk := P.hSkew
      obtain ⟨-, hcσ, -, hsσ, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
      obtain ⟨-, hcσ', -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
      have h4 : M.supportCutoff S.C σ + Δ S ≤ tAwakeEnd := le_trans (by omega) hEnd1
      have h4R : ((M.supportCutoff S.C σ + Δ S : ℕ) : ℝ) ≤ (tAwakeEnd : ℝ) := by exact_mod_cast h4
      push_cast at h4R
      linarith)) P.hParent
    ((votesCastByOwner_of_unforgeability M F) S A x R P.E) (P.gstSync M F U hσ).2.2
    (hG σ le_rfl μ X hX (by omega)).1
    ((GoldilocksCorrectness.Record.Proofs.Executions.roundMembers_mono M F) S A (σ + 1) (σ + 2) tAwakeEnd R P.E
      (Nat.le_succ _) hEnd).1
    (fun u' hu' => by
      have hH := (Finset.mem_inter.1 hu').2
      unfold Hon roundMembers at hH
      -- a tick to the vote time of slot `σ + 1` is at a real time at most the support cutoff of slot `σ + 1`
      have hnot := Activity.not_mem_corruptedAtTime.1 (Finset.mem_sdiff.1 hH).2
      classical
      intro hX
      obtain ⟨k, w, hk, -, huk⟩ := (Finset.mem_filter.1 hX).2
      have hkt := (P.E.tick_active k w _ hk).2.2
      have hsk := P.hSkew
      have hA0 := P.E.ahead_nonneg
      have hvcR : ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) + Δ S = ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show M.voteTime S.C (σ + 1) + Δ S = M.supportCutoff S.C (σ + 1) by omega)
      exact hnot k (by linarith) huk)
    (fun w hw => ((dutyWindow_gives_core_window_and_hold M F U) x R P.E P.hΔs P.hSkew (P.gstSync M F U hσ).2.2
      (Activity.mem_activeThroughout_of_le le_rfl
      (by exact_mod_cast (show M.voteTime S.C (σ + 1) ≤ M.supportCutoff S.C (σ + 2) by omega))
      (P.member0 M F U (show r * S.C.R ≤ σ + 1 by omega) hw hEnd))).1)
    hvoters
    (fun u' hu' => (holder_window_of_updater_reader M F U) x R P.E P.hΔs P.hSkew (P.gstSync M F U hσ).2.2
      (P.memberU M F U hσ (Finset.mem_inter.1 hu').2 hEnd1))
    (fun w _ votes support_votes hC =>
      ((GoldilocksCorrectness.Record.Proofs.Executions.counting_of_committee_majority_st M F) S A x R P.E σ
        (x.tickStep w (M.voteTime S.C (σ + 1))) (Hon M S A x σ) w (P.committee M F hσ hEnd1)).2.2 votes support_votes hC)
    (fun w hw => by
      obtain ⟨k, hk⟩ := htk w hw
      exact (P.stepFrame_vote_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hk hX hμ).1)
    (fun w hw => by
      obtain ⟨k, hk⟩ := htk w hw
      exact (P.stepFrame_vote_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hk hX hμ).2)
    u hu vote hSend

/-- **An updater's saved confirmation of the slot after the invariant's slots**. Within the phase up to
the support cutoff of slot `σ + 2`, when the invariant holds at every slot up to `σ`: an updater `u` of slot `σ + 1`
whose tick `k` to the support cutoff of slot `σ + 2` is at a real time at most `tAwakeEnd` saves, for slot `σ + 1`, a
confirmation that is the line source `X` (of a slot at most `σ`) or a descendant of `X`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `u`: the updater; `k`:
  its tick.

Read aloud: an updater of slot `σ + 1` whose tick to the cutoff is within the phase saves a confirmation that extends
every line source of an earlier slot. -/
theorem conf_source_at (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) {u : V} (hu : u ∈ updaterAt M S A x (σ + 1)) {k : ℕ}
    (hk : x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 2))) (hkE : x.time k ≤ tAwakeEnd) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ) :
    ∀ C' : Block V, (x.tickOutput u (M.supportCutoff S.C (σ + 2))).savedConfirmation (σ + 1) = some C' →
      X.AncestorEq C' := by
  have hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd
  obtain ⟨-, hcσ2, -, hs2, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  obtain ⟨-, hcσ3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 3)
  have hc23 : M.supportCutoff S.C (σ + 2) + 4 * Δ S ≤ M.supportCutoff S.C (σ + 3) := by
    rw [show σ + 2 + 1 = σ + 3 from rfl] at hs2
    omega
  -- the votes clause of slot `σ + 1`
  have hV := P.votes_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hX hμ
  -- `u`'s finalized block at its tick input to the support cutoff of slot `σ + 2`: `F_compat_st` at its tick `k`
  have hks : x.tickStep u (M.supportCutoff S.C (σ + 2)) = k := (tickStep_eq_of_lbl M) x P.E hk
  have hwk : u ∉ A.corrupted k := P.E.not_mem_corrupted_of_tick hk
  have hk2 := (P.E.tick_active _ u _ hk).2.2
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hsk := P.hSkew
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have h23 : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) + 4 * Δ S ≤ ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) := by
    exact_mod_cast hc23
  have hF : (x.tickInput u (M.supportCutoff S.C (σ + 2))).finalized.compatible X = true := by
    show (x.st (x.tickStep u (M.supportCutoff S.C (σ + 2))) u).finalized.compatible X = true
    rw [hks]
    exact P.F_compat_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hkE hwk (by linarith) hX hμ (fun _ => hV)
  obtain ⟨hHA, -⟩ := P.members_sets M F U (show r * S.C.R ≤ σ + 1 by omega) hEnd
  exact (GoldilocksCorrectness.Record.Proofs.Executions.confirmations_of_votes_clause M F U) S A x R GST (σ + 1) (Hon M S A x (σ + 1)) X u
    P.E P.hNet P.hSkew P.hRedeliver P.Sy P.hΔs ((per_tick_roots_of_roots_until M F) x P.E P.hRoots (by
      have : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) + Δ S ≤ ((tAwakeEnd : ℕ) : ℝ) := by
        exact_mod_cast (show M.supportCutoff S.C (σ + 1) + Δ S ≤ tAwakeEnd by
          obtain ⟨-, hcσ1, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
          rw [show σ + 1 + 1 = σ + 2 from rfl] at hs1
          omega)
      linarith)) P.hParent
    ((votesCastByOwner_of_unforgeability M F) S A x R P.E) (P.gstSync M F U (show r * S.C.R ≤ σ + 1 by omega)).2.2
    hHA (P.committee M F (show r * S.C.R ≤ σ + 1 by omega) hEnd) hV hu hF

/-- A line source's saver: some updater `u` of the source's slot `μ` ticks to the support cutoff of slot `μ + 1` at a
step `k`, and saves there, for slot `μ`, a confirmation `C` that is the source or a descendant of it.

The variables:
- `M`: the model.

Read aloud: a line source is on the confirmation its saver saved at its tick to the slot's update. -/
theorem _root_.GoldilocksCorrectness.Record.Proofs.Executions.LineSource.saved {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    {r H₂ μ : ℕ} {X : Block V} (h : LineSource M S A x r H₂ μ X) :
    ∃ (u : V) (k : ℕ) (C : Block V), u ∈ updaterAt M S A x μ ∧
      x.lbl k = Event.tick u (M.supportCutoff S.C (μ + 1)) ∧
      (x.tickOutput u (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C ∧ X.AncestorEq C := by
  obtain ⟨u, hu, n₀, C₀, X₀, -, -, hC₀, hXX₀, hX₀C₀, -⟩ := h
  obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hu
  exact ⟨u, k, C₀, hu, hk, hC₀, ancestorEq_trans hXX₀ hX₀C₀⟩

/-- `cert_source` with the source's saver: the updater `u` whose tick `k` before `j` ran the update of the source's slot
`μ` saves there, for slot `μ`, a confirmation `C` that is the source `E` or a descendant of it (`cert_source_core_fast`,
the fast block saved by the update, `state_saved_of_update`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: a certificate at a height greater than `H₂` names the entry of a line source, on the confirmation its saver
saved at a tick before the reading. -/
theorem cert_source_saved (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {j : ℕ} {w : V}
    {Y T : Block V} {h : Height} (hj : x.time j ≤ tAwakeEnd)
    (hY : Y ∈ (x.st j w).tree) (hJ : ProgressCertOn M Y h T) (hH : H₂ < h) :
    ∃ (μ : ℕ) (E : Block V) (u : V) (k : ℕ) (C : Block V),
      x.lbl k = Event.tick u (M.supportCutoff S.C (μ + 1)) ∧ k < j ∧ u ∈ updaterAt M S A x μ ∧
      (x.tickOutput u (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C ∧ E.AncestorEq C ∧
      LineSource M S A x r H₂ μ E ∧ IsEntry M S.C E ∧ (M.chainStateOf S.C E).h = h ∧
      T.root = E.root := by
  obtain ⟨r', E', u, k, -, hk, hkj, -, hE, hE1, hE2, hE3, hu, n₀, X₀, hU, hF, hEX⟩ := (cert_source_core_fast M F) R E U Fx
    P.hSkew P.hRoots P.hThird P.hAwake P.hCommittees P.hAnchor P.hOld P.hEnd P.hk₀ P.hOldStep P.hEndStep hj hY hJ hH
  have hU' : ConfirmationUpdated M S.C S.P (x.tickInput u (M.supportCutoff S.C (r' * S.C.R + 1)))
      ((M.supportCutoff S.C (r' * S.C.R + 1) : ℕ) : Int) (r' * S.C.R + 1) n₀ := hU
  obtain ⟨C', hC', hXC'⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_fast_block_saved (Nat.le_add_left 1 _) hU' hF
  rw [Nat.add_sub_cancel] at hC'
  have hst := (state_saved_of_update M F U) S A x R (r' * S.C.R) u n₀ E hu hU'
  exact ⟨r' * S.C.R, E', u, k, C', hk, hkj, hu, hst.trans hC', ancestorEq_trans hEX hXC', hE, hE1, hE2, hE3⟩

/-- `tall_entry_st` with the source's saver (`cert_source_saved`): a block of chain-state height `h ≥ H₂ + 2` held at step
`j` by a validator outside the adversary set there, in the phase, has an ancestor entry at height `h − 1` that is a line
source of a slot `μ'`, on the confirmation its saver saved at its tick to the support cutoff of slot `μ' + 1`, a step less
than `j`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.

Read aloud: a block held at a step, two or more heights past `H₂`, has its entry one height lower on a line source saved
at a tick before that step. -/
theorem tall_entry_saved (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {j : ℕ} {w : V}
    (hjE : x.time j ≤ tAwakeEnd) (hw' : w ∉ A.corrupted j) {Y : Block V}
    (hY : Y ∈ (x.st j w).tree) (hYh : H₂ + 2 ≤ (M.chainStateOf S.C Y).h) :
    ∃ (μ' : ℕ) (E : Block V) (u : V) (k : ℕ) (C : Block V),
      x.lbl k = Event.tick u (M.supportCutoff S.C (μ' + 1)) ∧ k < j ∧ u ∈ updaterAt M S A x μ' ∧
      (x.tickOutput u (M.supportCutoff S.C (μ' + 1))).savedConfirmation μ' = some C ∧ E.AncestorEq C ∧
      LineSource M S A x r H₂ μ' E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = (M.chainStateOf S.C Y).h - 1 ∧ E.AncestorEq Y := by
  have hY' : Y ∈ (x.st j w).tree := hY
  obtain ⟨Y', hY'Y, -, -, -, hT', hcert⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem67_first_advance M F) S.C Y
      ((M.chainStateOf S.C Y).h - 1) (by unfold Height at *; omega) (by unfold Height at *; omega)
  have hY'T := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w Y Y' hY' hY'Y
  have hT'T := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w Y' _ hY'T hT'
  obtain ⟨μ', Eb, u, kc, C, hkc, hkcj, hu, hC, hEC, hE, hEe, hEh, hEr⟩ := P.cert_source_saved M F R E U Fx hjE hY'T hcert
    (by unfold Height at *; omega)
  have hTE := P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hw' hjE hT'T)
    ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x (le_trans ((time_mono M) x R hkcj.le) hjE) (P.source_inHonestTreeBy_tick M F R E U hE hkc)) hEr
  refine ⟨μ', Eb, u, kc, C, hkc, hkcj, hu, hC, hEC, hE, hEe, hEh, ?_⟩
  rw [← hTE]
  exact ancestorEq_trans hT' hY'Y

/-- **A later saver's confirmation extends an earlier line source.** When the invariant holds at every slot up to `σ`, in
the phase up to the support cutoff of slot `σ + 2`: an updater `u` of a slot `μ'` at most `σ + 1` whose tick `k` to the
support cutoff of slot `μ' + 1` is in the phase saves, for slot `μ'`, a confirmation that is every line source of an
earlier slot `μ < μ'`, or a descendant of it (`conf_source_at` at the slot before `μ'`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: the confirmation a saver of a later slot saves within the phase extends every line source of an earlier slot. -/
theorem saved_extends_source (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd)
    {μ μ' : ℕ} {X : Block V} (hX : LineSource M S A x r H₂ μ X) (hμμ' : μ < μ') (hμ' : μ' ≤ σ + 1)
    {u : V} {k : ℕ} {C : Block V} (hu : u ∈ updaterAt M S A x μ')
    (hk : x.lbl k = Event.tick u (M.supportCutoff S.C (μ' + 1))) (hkE : x.time k ≤ tAwakeEnd)
    (hC : (x.tickOutput u (M.supportCutoff S.C (μ' + 1))).savedConfirmation μ' = some C) :
    X.AncestorEq C := by
  obtain ⟨σ₀, rfl⟩ : ∃ σ₀, μ' = σ₀ + 1 := ⟨μ' - 1, by omega⟩
  have hs := hX.slot_ge M F
  exact P.conf_source_at M F R E hNet hSkew hRedeliver Sy hΔs U Fx (σ := σ₀) (fun σ' h => hG σ' (by omega)) (by omega)
    (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd)
    hu hk hkE hX (by omega) C hC

/-- **Two line sources with their savers' ticks in the phase are compatible** (the twin of `sources_compatible` for the
slots up to `σ + 1`). When the invariant holds at every slot up to `σ`, in the phase up to the support cutoff of slot
`σ + 2`: two line sources of slots at most `σ + 1`, each on the confirmation its saver saved at a tick to its slot's
update inside the phase, are compatible. Of one slot, by Lemma 32 at the two savers' ticks; of two slots, the later
saver's confirmation extends the earlier source (`saved_extends_source`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: two line sources whose savers ticked within the phase are compatible. -/
theorem saved_sources_compatible (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd)
    {μ₁ μ₂ : ℕ} {Y₁ Y₂ : Block V} (hY₁ : LineSource M S A x r H₂ μ₁ Y₁) (hY₂ : LineSource M S A x r H₂ μ₂ Y₂)
    (hμ₁ : μ₁ ≤ σ + 1) (hμ₂ : μ₂ ≤ σ + 1) {u₁ u₂ : V} {k₁ k₂ : ℕ} {C₁ C₂ : Block V}
    (hu₁ : u₁ ∈ updaterAt M S A x μ₁) (hk₁ : x.lbl k₁ = Event.tick u₁ (M.supportCutoff S.C (μ₁ + 1)))
    (hk₁E : x.time k₁ ≤ tAwakeEnd)
    (hC₁ : (x.tickOutput u₁ (M.supportCutoff S.C (μ₁ + 1))).savedConfirmation μ₁ = some C₁) (hYC₁ : Y₁.AncestorEq C₁)
    (hu₂ : u₂ ∈ updaterAt M S A x μ₂) (hk₂ : x.lbl k₂ = Event.tick u₂ (M.supportCutoff S.C (μ₂ + 1)))
    (hk₂E : x.time k₂ ≤ tAwakeEnd)
    (hC₂ : (x.tickOutput u₂ (M.supportCutoff S.C (μ₂ + 1))).savedConfirmation μ₂ = some C₂) (hYC₂ : Y₂.AncestorEq C₂) :
    Y₁.compatible Y₂ = true := by
  rcases lt_trichotomy μ₁ μ₂ with h | h | h
  · exact compatible_of_ancestorEq_both
      (P.saved_extends_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hEnd hY₁ h hμ₂ hu₂ hk₂ hk₂E hC₂) hYC₂
      ((compatible_iff _ _).2 (Or.inl (ancestorEq_refl _)))
  · subst h
    have hs := hY₁.slot_ge M F
    have hRoots' : RootsNameBlocksUntil M A x (max (x.time (x.tickStep u₁ (M.supportCutoff S.C (μ₁ + 1))))
        (x.time (x.tickStep u₂ (M.supportCutoff S.C (μ₁ + 1))))) := by
      rw [(tickStep_eq_of_lbl M) x P.E hk₁, (tickStep_eq_of_lbl M) x P.E hk₂]
      exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (max_le hk₁E hk₂E) P.hRoots
    exact compatible_of_ancestorEq_both hYC₁ hYC₂
      ((GoldilocksCorrectness.Record.Proofs.Executions.lem32_saved_confirmations_compatible_state M F U) S A x P.R GST μ₁
        u₁ u₂ C₁ C₂ P.E P.hNet P.hSkew P.hRedeliver P.Sy P.hΔs hRoots' (P.gstSync M F U hs).2.1 hu₁ hu₂ hC₁ hC₂)
  · exact compatible_symm' (compatible_of_ancestorEq_both
      (P.saved_extends_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hEnd hY₂ h hμ₁ hu₁ hk₁ hk₁E hC₁) hYC₁
      ((compatible_iff _ _).2 (Or.inl (ancestorEq_refl _))))

/-- **A viable block on a line source's chain at a step before the next support cutoff.** At a step `j` in the phase at
which `w` is outside the adversary set and whose real time is less than the support cutoff of slot `σ + 2`, when the
invariant holds at every slot up to `σ` and the line source `X` (of a slot at most `σ`) and `L` are in `w`'s tree at `j`:
some block `W` of that tree, `X` or a descendant of `X`, has a chain-state height at least `w`'s `head_height_floor` at
`j`. The line sources read at `j` come from ticks before `j`, so of slots at most `σ + 1`, each with its saver's tick in
the phase; any two of them are compatible (`saved_sources_compatible`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.

Read aloud: at a step before the next support cutoff, when a line source and `L` are in an honest validator's tree, some
block of that tree, that source or a descendant of it, is viable for the validator. -/
theorem viable_candidate_held_st (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ j : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) (hjE : x.time j ≤ tAwakeEnd)
    (hw' : w ∉ A.corrupted j) (hjc : x.time j < ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ)) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hXj : X ∈ (x.st j w).tree) (hLj : L ∈ (x.st j w).tree) :
    ∃ W : Block V, X.AncestorEq W ∧ W ∈ (x.st j w).tree ∧
      M.head_height_floor (x.st j w) ≤ (M.chainStateOf S.C W).h := by
  have hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
  obtain ⟨hv2, hc2, -, hs2, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  obtain ⟨hv3, hc3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 3)
  rw [show σ + 2 + 1 = σ + 3 from rfl] at hs2
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hsk := hSkew
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  -- every tick to the support cutoff of a slot up to `σ + 1` is in the phase (`hSkew`), as in `F_compat`
  have hEndT : ∀ μ'' : ℕ, μ'' ≤ σ → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (μ'' + 1)) →
      x.time k ≤ tAwakeEnd := by
    intro μ'' hμ'' u k hk
    have hkt := (E.tick_active _ _ _ hk).2.2
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show μ'' + 1 ≤ σ + 1 by omega)
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (σ + 1)
    rw [show σ + 1 + 1 = σ + 2 from rfl] at h1
    have hc : ((M.supportCutoff S.C (μ'' + 1) : ℕ) : ℝ) + Δ S ≤ (tAwakeEnd : ℕ) := by
      exact_mod_cast (show M.supportCutoff S.C (μ'' + 1) + Δ S ≤ tAwakeEnd by omega)
    linarith
  have hInv : M.nodeInv S.C S.P S.X (x.st j w) :=
    ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariant M F S A x R E j w) hw').1
  -- a slot whose update ran at a tick before `j` is at most `σ + 1`: a tick to the support cutoff of slot `σ + 3` or
  -- later is at a real time at least that cutoff less `ΔClockAhead`, later than the support cutoff of slot `σ + 2`
  have hslot : ∀ (μ' : ℕ) (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (μ' + 1)) →
      k < j → μ' ≤ σ + 1 := by
    intro μ' u k hk hkj
    by_contra h
    have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show σ + 3 ≤ μ' + 1 by omega)
    have hkt := (E.tick_active _ _ _ hk).2.1
    have hkk := (time_mono M) x R hkj.le
    have h4 : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) + 4 * Δ S ≤ ((M.supportCutoff S.C (μ' + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (σ + 2) + 4 * Δ S ≤ M.supportCutoff S.C (μ' + 1) by omega)
    linarith
  -- `X` with its saver, whose tick is in the phase
  obtain ⟨uX, kX, CX, huX, hkX, hCX, hXCX⟩ := hX.saved M F
  have hkXE := hEndT μ hμ uX kX hkX
  by_cases hMle : hMax M S.C (x.st j w) ≤ H₂ + 1
  · have hfl := (GoldilocksCorrectness.Record.Proofs.Routines.floor_le_h_max M F) S.C S.P S.X (x.st j w) hInv
    rcases (compatible_iff _ _).1 (P.sources_compatible M F R U hG hEnd (P.source_L M F R U hEndR) hX hσ hμ)
      with h | h
    · refine ⟨X, ancestorEq_refl X, hXj, ?_⟩
      have := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C h
      rw [P.hL] at this
      unfold Height at *
      omega
    · refine ⟨L, h, hLj, ?_⟩
      rw [P.hL]
      unfold Height at *
      omega
  · have hM2 : H₂ + 2 ≤ hMax M S.C (x.st j w) := by unfold Height at *; omega
    obtain ⟨-, ⟨Y, hY, hYh⟩, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j w
    obtain ⟨μ', Eb, u', k', C', hk', hkj', hu', hC', hEbC', hE, hEe, hEh, hEY⟩ :=
      P.tall_entry_saved M F R E U Fx hjE hw' hY (by rw [hYh]; exact hM2)
    have hμ' : μ' ≤ σ + 1 := hslot μ' u' k' hk' hkj'
    have hk'E : x.time k' ≤ tAwakeEnd := le_trans ((time_mono M) x R hkj'.le) hjE
    rw [hYh] at hEh
    -- the state is not contested
    have hnc : M.fg_contest (x.st j w) = false := by
      cases hcs : M.fg_contest (x.st j w)
      · rfl
      exfalso
      obtain ⟨hbox, B, hBT, -, hBh, hJB⟩ :=
        (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_spec M F) S.C S.P S.X (x.st j w) hInv hcs
      obtain ⟨μB, EB, uB, kB, CB, hkB, hkjB, huB, hCB, hEBC, hEB, hEBe, hEBh, hEBB⟩ :=
        P.tall_entry_saved M F R E U Fx hjE hw' hBT (by rw [hBh]; exact hM2)
      have hμB : μB ≤ σ + 1 := hslot μB uB kB hkB hkjB
      obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j w
      have hlt : H₂ < (M.chainStateOf S.C D).h_j := by
        rw [← hhjD]
        unfold Height at *
        omega
      obtain ⟨hJC, hJanc, hJh⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F)
        S.C D).1 (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
      have hD' : D ∈ (x.st j w).tree := hD
      have hJT : (M.chainStateOf S.C D).J ∈ (x.st j w).tree :=
        (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w D _ hD' hJanc
      obtain ⟨μJ, EJ, uJ, kJ, CJ, hkJ, hkjJ, huJ, hCJ, hEJC, hEJ, hEJe, hEJh, hEJr⟩ := P.cert_source_saved M F R E U Fx hjE hD'
        ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hJC) hlt
      have hμJ : μJ ≤ σ + 1 := hslot μJ uJ kJ hkJ hkjJ
      have hJE : (M.chainStateOf S.C D).J = EJ :=
        P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hw' hjE hJT)
          ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x
            (le_trans ((time_mono M) x R hkjJ.le) hjE) (P.source_inHonestTreeBy_tick M F R E U hEJ hkJ)) hEJr
      have hEE : EJ = EB := (GoldilocksCorrectness.Record.Proofs.Routines.entry_eq_of_compatible M F) S.C hEJe hEBe (by
          rw [hEJh, hEBh, ← hhjD, hBh, hbox]
          unfold Height at *
          omega)
        (P.saved_sources_compatible M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hEnd hEJ hEB hμJ hμB huJ hkJ
          (le_trans ((time_mono M) x R hkjJ.le) hjE) hCJ hEJC huB hkB (le_trans ((time_mono M) x R hkjB.le) hjE) hCB hEBC)
      apply hJB
      rw [hJD, hJE, hEE]
      exact hEBB
    have hfloor : M.head_height_floor (x.st j w) = hMax M S.C (x.st j w) - 1 :=
      (GoldilocksCorrectness.Record.Proofs.Routines.head_height_floor_of_not_contested M F) S.C S.P S.X
        (x.st j w) hInv hnc
    have hEbT : Eb ∈ (x.st j w).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w Y Eb hY hEY
    rcases (compatible_iff _ _).1 (P.saved_sources_compatible M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hEnd hX hE (by omega) hμ' huX hkX hkXE
        hCX hXCX hu' hk' hk'E hC' hEbC') with h | h
    · exact ⟨Eb, h, hEbT, by rw [hfloor, hEh]⟩
    · refine ⟨X, ancestorEq_refl X, hXj, ?_⟩
      have := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C h
      rw [hfloor, ← hEh]
      exact this

/-- **A viable block on a line source's chain, up to the support cutoff of slot `σ + 2`.** From the vote time of
slot `σ + 1` to the support cutoff of slot `σ + 2`, in the phase, when the invariant holds at every slot up to `σ`
and an honest validator's root is a line source `X` of a slot at most `σ` or an ancestor of it: some block `W`, `X` or
a descendant of `X`, in the validator's tree before `t`, has a chain-state height at least its `head_height_floor`
. The entries of slot `σ + 1` that a tick to the support cutoff of slot `σ + 2`, up to
`ΔClockAhead` early, can bring before `t` are those of savers that ticked before `t`, inside the phase: `votes_source` and
`conf_source_at` cover them.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: up to the next support cutoff, when an honest validator's root is on a line source's chain, some viable
block of its tree is that source or a descendant of it. -/
theorem viable_candidate_held_before (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ t : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) (ht0 : M.voteTime S.C (σ + 1) ≤ t)
    (ht : t ≤ M.supportCutoff S.C (σ + 2)) (hw : w ∉ A.corruptedAtTime x t) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hRX : (M.get_fc_root (x.stateBefore t w)).AncestorEq X) :
    ∃ W : Block V, X.AncestorEq W ∧ W ∈ (x.stateBefore t w).tree ∧
      M.head_height_floor (x.stateBefore t w) ≤ (M.chainStateOf S.C W).h := by
  obtain ⟨hvσ, hcσ, hfσ, hsσ, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  obtain ⟨hvσ1, hcσ1, -, hsσ1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
  have hEndE : t ≤ tAwakeEnd := le_trans ht hEnd
  have ht1 : 1 ≤ t := by omega
  have htj : x.time (x.stepBefore t) < t := ((stepBefore_time M) x R E ht1).1
  have hwj : w ∉ A.corrupted (x.stepBefore t) :=
    Activity.not_mem_corruptedAtTime.1 hw _ ((time_stepBefore_le M) x R E t)
  -- `w` ticks to the view freeze of every slot from `r * R` to `σ` before `t` (`tick_before`)
  have htick : ∀ μ₁ : ℕ, r * S.C.R ≤ μ₁ → μ₁ ≤ σ →
      ∃ k : ℕ, x.lbl k = Event.tick w (M.viewFreeze S.C μ₁) ∧ k ≤ x.stepBefore t := by
    intro μ₁ h1 h2
    obtain ⟨hv₁, -, hf₁, hs₁, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ₁
    obtain ⟨hG1, -, -⟩ := P.gstSync M F U h1
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h2
    exact P.tick_before M F (by omega) (by omega) hEndE hw
  have hFX : ∀ k₁ : ℕ, k₁ ≤ x.stepBefore t → (x.st k₁ w).finalized.AncestorEq X := fun k₁ hk₁ =>
    ancestorEq_trans ((F_ancestorEq_of_le M F) x R P.E w hk₁)
      (ancestorEq_trans ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_stateBefore M F) S A x R P.E t w) hRX)
  -- `X` and `L` in `w`'s tree before `t`: held at `w`'s ticks to the view freezes (`source_held`, `L_held`), kept since
  have hXj : X ∈ (x.st (x.stepBefore t) w).tree := by
    obtain ⟨k₁, hk₁, hk₁t⟩ := htick μ (hX.slot_ge M F) hμ
    have hk₁R : x.tickStep w (M.viewFreeze S.C μ) = k₁ := (tickStep_eq_of_lbl M) x P.E hk₁
    have hTI₁ : x.tickInput w (M.viewFreeze S.C μ) = x.st k₁ w := by
      show x.st (x.tickStep w (M.viewFreeze S.C μ)) w = x.st k₁ w; rw [hk₁R]
    have hE₁ : M.supportCutoff S.C (μ + 1) ≤ tAwakeEnd :=
      le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
    have h := P.source_held M F R E hNet hSkew hRedeliver Sy hΔs U hX hE₁ hk₁ (by
      rw [hTI₁]
      exact (compatible_iff _ _).2 (Or.inl (hFX k₁ hk₁t)))
    rw [hTI₁] at h
    exact (mem_T_mono M F) x R P.E w hk₁t h
  have hLj : L ∈ (x.st (x.stepBefore t) w).tree := by
    obtain ⟨kL, hkL, hkLt⟩ := htick (r * S.C.R) le_rfl hσ
    have hkLR : x.tickStep w (M.viewFreeze S.C (r * S.C.R)) = kL := (tickStep_eq_of_lbl M) x P.E hkL
    have h := P.L_held M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEndR hkL
    rw [show x.tickInput w (M.viewFreeze S.C (r * S.C.R)) = x.st kL w by
      show x.st (x.tickStep w (M.viewFreeze S.C (r * S.C.R))) w = x.st kL w; rw [hkLR]] at h
    exact (mem_T_mono M F) x R P.E w hkLt h
  have htE : ((t : ℕ) : ℝ) ≤ (tAwakeEnd : ℕ) := by exact_mod_cast hEndE
  have htc : ((t : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) := by exact_mod_cast ht
  exact P.viable_candidate_held_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd (by linarith) hwj (by linarith) hX hμ hXj hLj

/-- **The frame at a time relative to a line source.** From the vote time of slot `σ + 1` to the
support cutoff of slot `σ + 2`, in the phase, when the invariant holds at every slot up to `σ`: an
honest validator's root is compatible with every line source `X` of a slot at most `σ`; when the
root is `X` or an ancestor of `X`, some viable head of its frame is `X` or a descendant of `X`;
and its finalized block is compatible with `X`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: the frame of an honest validator at a time of the phase, relative to every line source.
-/
theorem frame_source_at (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ t : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) (ht0 : M.voteTime S.C (σ + 1) ≤ t)
    (ht : t ≤ M.supportCutoff S.C (σ + 2)) (hw : w ∉ A.corruptedAtTime x t) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ) :
    (M.fg_to_ac (x.stateBefore t w)).fc_root.compatible X = true ∧
    ((M.fg_to_ac (x.stateBefore t w)).fc_root.AncestorEq X →
      ∃ W ∈ (M.fg_to_ac (x.stateBefore t w)).tree,
        W ∈ (M.fg_to_ac (x.stateBefore t w)).viable_heads ∧ X.AncestorEq W) ∧
    (x.stateBefore t w).finalized.compatible X = true := by
  -- the votes clause of slot `σ + 1` (`votes_source`, (a″))
  have hV := P.votes_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hX hμ
  obtain ⟨-, -, hfσ, hsσ, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  obtain ⟨hvσ1, -, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hfR : M.slotStart S.C (r * S.C.R + 1) ≤ t := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show r * S.C.R + 1 ≤ σ + 1 by omega)
    have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (σ + 1)
    omega
  have htc := ht
  refine ⟨by rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact P.root_compat M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hfR htc hw hX hμ (fun _ => hV), fun hR => ?_,
    P.F_compat M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd (by omega) htc hw hX hμ (fun _ => hV)⟩
  have hR' : (M.get_fc_root (x.stateBefore t w)).AncestorEq X := by
    rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact hR
  obtain ⟨W, hXW, hWT', hφ⟩ := P.viable_candidate_held_before M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd ht0 ht hw hX hμ hR'
  have hFW : (x.stateBefore t w).finalized.AncestorEq W :=
    ancestorEq_trans ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_stateBefore M F) S A x R E t w) (ancestorEq_trans hR' hXW)
  refine ⟨W, ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hWT', hFW⟩, ?_, hXW⟩
  refine (((GoldilocksCorrectness.Record.Statements.Routines.lem56_frame_of_shape M F) S.C S.P S.X
    (x.stateBefore t w) (show M.nodeInv S.C S.P S.X (x.stateBefore t w) from
          (GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariant M F S A x R E
            (x.stepBefore t) w
            (Activity.not_mem_corruptedAtTime.1 hw _ ((time_stepBefore_le M) x R E t))).1) _ _
    (show FrameShape M (x.stateBefore t w) (M.get_fc_root (x.stateBefore t w))
      (M.head_height_floor (x.stateBefore t w)) from ⟨rfl, rfl⟩)).2.2 W).2
    ⟨hWT', hFW, ancestorEq_trans hR' hXW, hφ⟩

/-- **The step's frame conditions relative to a line source, at a member whose tick is in the phase**.
In the phase up to the support cutoff of slot `σ + 2`, when the invariant holds at every slot up to `σ`, a validator `w`
honest at that cutoff whose tick to it, when it takes it, is inside the phase satisfies `StepFrameAt` relative to every
line source of a slot at most `σ`. `stepFrame_source` with `hEndTick` in place of the support cutoff of slot `σ + 3`
in the phase, and the votes clause derived (`votes_source`): the finalized block is read at `w`'s tick
(`F_compat_st`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: a member whose tick to the support cutoff is within the phase satisfies the step's frame conditions
relative to every line source. -/
theorem stepFrame_source_of_tick (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd)
    (hw : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 2)))
    -- `w`'s tick to the support cutoff of slot `σ + 2`, when it takes it, is inside the phase
    (hEndTick : ∀ k : ℕ, x.lbl k = Event.tick w (M.supportCutoff S.C (σ + 2)) → x.time k ≤ tAwakeEnd)
    {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ) : StepFrameAt M S A x X σ w := by
  -- the votes clause of slot `σ + 1` (`votes_source`)
  have hV := P.votes_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hX hμ
  obtain ⟨hvσ, -, hfσ, hsσ, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  obtain ⟨hvσ1, hcσ1, -, hsσ1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  obtain ⟨hv2, hcσ2, -, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  have hv1c : M.voteTime S.C (σ + 1) ≤ M.supportCutoff S.C (σ + 2) := by
    rw [show σ + 2 = σ + 1 + 1 by omega] at hcσ2 ⊢
    omega
  have hv12 : M.voteTime S.C (σ + 1) ≤ M.voteTime S.C (σ + 2) := by
    rw [show σ + 2 = σ + 1 + 1 by omega] at hv2 ⊢
    omega
  have hvE : M.voteTime S.C (σ + 1) ≤ tAwakeEnd := le_trans hv1c hEnd
  -- `w`, honest at the support cutoff of slot `σ + 2`, ticks to the vote time of slot `σ + 1` (`tick_before`)
  obtain ⟨hG1, -, -⟩ := P.gstSync M F U hσ
  obtain ⟨kv, hkv, -⟩ := P.tick_before M F (c := M.voteTime S.C (σ + 1)) (by omega)
    (by rw [show σ + 2 = σ + 1 + 1 by omega] at hcσ2 ⊢; omega) hEnd hw
  obtain ⟨h1, h2⟩ := P.stepFrame_vote_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hkv hX hμ
  refine ⟨h1, h2, ?_⟩
  · -- the finalized block at `w`'s tick input to the support cutoff of slot `σ + 2`: `F_compat_st` at that tick, inside
    -- the phase by `hEndTick`; with no such tick, the initial state
    obtain ⟨-, hc2, -, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
    obtain ⟨-, hc3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 3)
    have h23 : M.supportCutoff S.C (σ + 2) + 4 * Δ S ≤ M.supportCutoff S.C (σ + 3) := by
      rw [show σ + 2 + 1 = σ + 3 from rfl] at hs2
      omega
    by_cases hex : ∃ k : ℕ, x.lbl k = Event.tick w (M.supportCutoff S.C (σ + 2))
    · obtain ⟨k, hk⟩ := hex
      have hks : x.tickStep w (M.supportCutoff S.C (σ + 2)) = k := (tickStep_eq_of_lbl M) x E hk
      rw [show x.tickInput w (M.supportCutoff S.C (σ + 2)) = x.st k w by
        show x.st (x.tickStep w (M.supportCutoff S.C (σ + 2))) w = x.st k w; rw [hks]]
      have hkt := (E.tick_active _ _ _ hk).2.2
      have h4 : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) + 4 * Δ S ≤ ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) := by
        exact_mod_cast h23
      have hA0 := E.ahead_nonneg
      have hB0 := E.behind_nonneg
      have hsk := hSkew
      have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast one_le_Δ S
      exact P.F_compat_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd (hEndTick k hk)
        (E.not_mem_corrupted_of_tick hk) (by linarith) hX hμ (fun _ => hV)
    · have h0 : x.tickStep w (M.supportCutoff S.C (σ + 2)) = 0 := by
        unfold Trace.tickStep
        rw [dif_neg hex]
      rw [show x.tickInput w (M.supportCutoff S.C (σ + 2)) = x.st 0 w by
        show x.st (x.tickStep w (M.supportCutoff S.C (σ + 2))) w = x.st 0 w; rw [h0],
        (getElem_zero_st M F) x R, F.init.initial_finalized S.C w]
      exact (compatible_iff _ _).2 (Or.inl (GoldilocksCorrectness.Proofs.Routines.genesis_ancestorEq X))

/-- **The base of a line source.** When the invariant holds at every slot up to `μ`, in the phase up to the support
cutoff of slot `μ + 3`, the slot invariant relative to a line source of slot `μ` (of any kind) holds at slot `μ + 1`, and
every updater's confirmation of slot `μ + 1` extends the source: the votes by `votes_source` (A4 at the source's saver);
the live locks of slot `μ + 2` by `locks_step_of_clauses` over `base_locks` and Lemma 32 at the source's saver; the
confirmations by `conf_source_at` (Lemma 78).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: the slot invariant relative to a line source holds at the slot after the source's, and every
updater's confirmation of that slot extends the source. -/
theorem base_source (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {μ : ℕ}
    (hG : ∀ σ', σ' ≤ μ → LineInv M S A x r H₂ σ') (hμ : r * S.C.R ≤ μ)
    (hEnd3 : M.supportCutoff S.C (μ + 3) ≤ tAwakeEnd) {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) :
    HonestChainExtends M S A x (Hon M S A x (μ + 1)) X (μ + 1) ∧
    ∀ u ∈ updaterAt M S A x (μ + 1), ∀ C' : Block V,
      (x.tickOutput u (M.supportCutoff S.C (μ + 2))).savedConfirmation (μ + 1) = some C' → X.AncestorEq C' := by
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hsk := P.hSkew
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hσ : r * S.C.R ≤ μ := hμ
  have hEnd : M.supportCutoff S.C (μ + 2) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd3
  have hEnd1 : M.supportCutoff S.C (μ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd
  have hc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (μ + 1)
  have hc2 : M.supportCutoff S.C (μ + 2) = M.voteTime S.C (μ + 2) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (μ + 2)
  have hc3 : M.supportCutoff S.C (μ + 3) = M.voteTime S.C (μ + 3) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (μ + 3)
  have hv2 : M.voteTime S.C (μ + 2) = M.voteTime S.C (μ + 1) + 4 * Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S (μ + 1)
  have hv3 : M.voteTime S.C (μ + 3) = M.voteTime S.C (μ + 2) + 4 * Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S (μ + 2)
  have hv1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (μ + 1)
  have hs1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (μ + 1)
  have hs2 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (μ + 2)
  have hdc := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S (μ + 2)
  have hk8 := Nat.mul_le_mul_left (4 * Δ S) hk
  have hm2 : 4 * Δ S * (μ + 2) = 4 * Δ S * (μ + 1) + 4 * Δ S := by ring
  -- the votes of slot `μ + 1` (`votes_source`)
  have hV := P.votes_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hX le_rfl
  obtain ⟨hHA1, hUp1⟩ := P.members_sets M F U (show r * S.C.R ≤ μ + 1 by omega) hEnd
  obtain ⟨-, hUp0⟩ := P.members_sets M F U hσ hEnd1
  -- an updater's tick to the support cutoff of slot `s + 1` is inside the phase when that cutoff and one delay are
  have htickE : ∀ (s : ℕ) (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (s + 1)) →
      M.supportCutoff S.C (s + 1) + Δ S ≤ tAwakeEnd → x.time k ≤ tAwakeEnd := by
    intro s u k hk' hE
    have h1 := (P.E.tick_active k u _ hk').2.2
    have : ((M.supportCutoff S.C (s + 1) + Δ S : ℕ) : ℝ) ≤ ((tAwakeEnd : ℕ) : ℝ) := by exact_mod_cast hE
    push_cast at this
    linarith
  -- the updaters' confirmations of slot `μ + 1` (`conf_source_at`)
  have hConf : ∀ u ∈ updaterAt M S A x (μ + 1), ∀ C' : Block V,
      (x.tickOutput u (M.supportCutoff S.C (μ + 2))).savedConfirmation (μ + 1) = some C' → X.AncestorEq C' := by
    intro u hu C' hC'
    obtain ⟨k, hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hu
    exact P.conf_source_at M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hu hk'
      (htickE (μ + 1) u k hk' (by rw [show μ + 1 + 1 = μ + 2 from rfl]; omega)) hX le_rfl C' hC'
  -- the source's saver `u₀` and its confirmation `C₀` of slot `μ`
  obtain ⟨u₀, hu₀, n₀, C₀, X₀, -, -, hC₀, hXX₀, hX₀C₀, -⟩ := id hX
  obtain ⟨k₀, hk₀, -⟩ := Activity.mem_activeThroughoutToTick.1 hu₀
  have hk₀E := htickE μ u₀ k₀ hk₀ (by omega)
  refine ⟨⟨hV, fun w hw n₂ sent₂ hrun₂ hAw₂ e₂ he₂ hlive₂ => ?_, fun v' hv' C' hC' => hConf v' (hUp1 hv') C' hC'⟩, hConf⟩
  -- the live locks of slot `μ + 2` at a member `w` (`locks_step_of_clauses`)
  have hwc : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (μ + 2)) := (Finset.mem_sdiff.1 hw).2
  have hwU : w ∈ updaterAt M S A x μ :=
    hUp0 (((roundMembers_mono M F) S A (μ + 1) (μ + 2) tAwakeEnd R P.E (Nat.le_succ _) hEnd).1 hw)
  -- the facts of slot `μ`: the live locks of `w`'s revocation of slot `μ + 1` (`base_locks`) and `w`'s saved
  -- confirmation of slot `μ`, compatible with the saver's (Lemma 32)
  have hL2 := P.base_locks M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hEnd hX hwc
  have hL3 : ∀ C' : Block V,
      (x.tickOutput w (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C' → C'.compatible X = true := by
    intro C' hC'
    obtain ⟨kw, hkw, -⟩ := Activity.mem_activeThroughoutToTick.1 hwU
    have hkwE := htickE μ w kw hkw (by omega)
    have hRoots' : RootsNameBlocksUntil M A x (max (x.time (x.tickStep w (M.supportCutoff S.C (μ + 1))))
        (x.time (x.tickStep u₀ (M.supportCutoff S.C (μ + 1))))) := by
      rw [(tickStep_eq_of_lbl M) x P.E hkw, (tickStep_eq_of_lbl M) x P.E hk₀]
      exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (max_le hkwE hk₀E) P.hRoots
    exact compatible_of_ancestorEq_both (ancestorEq_refl C') (ancestorEq_trans hXX₀ hX₀C₀)
      ((GoldilocksCorrectness.Record.Proofs.Executions.lem32_saved_confirmations_compatible_state M F U) S A x P.R GST μ
        w u₀ C' C₀ P.E P.hNet P.hSkew P.hRedeliver P.Sy P.hΔs hRoots' (P.gstSync M F U hσ).2.1 hwU hu₀ hC' hC₀)
  -- `w`'s reader up to its tick to the vote time of slot `μ + 1`, from its window from `tGAT`
  have hHon : w ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (μ + 2) : ℕ) : ℤ) (M.voteTime S.C (μ + 1)) := by
    have hd := P.dws M F U (show r * S.C.R ≤ μ + 2 by omega)
    have hdv : M.dutyWindowStart S.C (μ + 2) ≤ M.voteTime S.C (μ + 1) := by omega
    have hdR : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.dutyWindowStart S.C (μ + 2) : ℕ) : ℝ) := by exact_mod_cast hd
    push_cast at hdR
    have hve : ((M.voteTime S.C (μ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C (μ + 1) + Δ S ≤ M.supportCutoff S.C (μ + 2) by omega)
    refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R P.E (by omega) (by exact_mod_cast hdv) ?_
    refine Activity.mem_activeThroughout_of_le ?_ ?_ (P.window M F hwc hEnd)
    · push_cast; linarith
    · linarith
  exact (locks_step_of_clauses M F U) S A x R X μ w P.E hL2 hL3 hHon n₂
    ((locksRevoked_of_vote_tickInput M F U) x R (μ + 2) w n₂ sent₂ hrun₂ hAw₂) e₂ he₂ hlive₂

/-- **The step of a line source.** When the invariant holds at every slot up to `σ`, the slot
invariant relative to a line source of a slot at most `σ` at slot `σ` gives it at slot `σ + 1`
(`lem79_step_sets`, the frames of `stepFrame_source`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: the slot invariant relative to a line source, with every updater's saved confirmation
extending the source, passes from one slot to the next. -/
theorem step_source (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd3 : M.supportCutoff S.C (σ + 3) ≤ tAwakeEnd) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hInv : HonestChainExtends M S A x (Hon M S A x σ) X σ ∧
      ∀ u ∈ updaterAt M S A x σ, ∀ C' : Block V,
        (x.tickOutput u (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' → X.AncestorEq C') :
    HonestChainExtends M S A x (Hon M S A x (σ + 1)) X (σ + 1) ∧
    ∀ u ∈ updaterAt M S A x (σ + 1), ∀ C' : Block V,
      (x.tickOutput u (M.supportCutoff S.C (σ + 2))).savedConfirmation (σ + 1) = some C' → X.AncestorEq C' := by
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hsk := P.hSkew
  have hΔ := one_le_Δ S
  have hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd3
  have hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd
  have hc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hc2 : M.supportCutoff S.C (σ + 2) = M.voteTime S.C (σ + 2) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 2)
  have hc3 : M.supportCutoff S.C (σ + 3) = M.voteTime S.C (σ + 3) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 3)
  have hv2 : M.voteTime S.C (σ + 2) = M.voteTime S.C (σ + 1) + 4 * Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S (σ + 1)
  have hv3 : M.voteTime S.C (σ + 3) = M.voteTime S.C (σ + 2) + 4 * Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S (σ + 2)
  -- the votes of slot `σ + 1` (`votes_source`) and the members' frames (`stepFrame_source`)
  have hV := P.votes_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hX hμ
  have hSF : ∀ w ∈ Hon M S A x (σ + 1), StepFrameAt M S A x X σ w := fun w hw =>
    P.stepFrame_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd3 (Finset.mem_sdiff.1 hw).2 hX hμ hV
  obtain ⟨hHA0, hUp0⟩ := P.members_sets M F U hσ hEnd1
  obtain ⟨hHA1, hUp1⟩ := P.members_sets M F U (show r * S.C.R ≤ σ + 1 by omega) hEnd
  -- the voters of a slot: the committee members of its members, each with its vote
  have hvoters : ∀ s : ℕ, r * S.C.R ≤ s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ u ∈ S.P.committee s ∩ Hon M S A x s, u ∈ Hon M S A x s ∧ u ∈ S.P.committee s ∧
        ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s ∧
          ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
            (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
              x.sent (i + 1) - x.sent i := by
    intro s hs hE u hu
    obtain ⟨hK, hH⟩ := Finset.mem_inter.1 hu
    obtain ⟨i, vote, hl, hvi, hvs, hsent⟩ :=
      (GoldilocksCorrectness.Record.Statements.Executions.honest_active_votes M F U) S A x R s u P.E P.hSkew
        ((P.members_sets M F U hs hE).1 hH) hK
    exact ⟨hH, hK, vote, hvi, hvs, i, hl, hsent⟩
  -- roots, per tick, up to the clock value `M.supportCutoff S.C (σ + 1)`
  have hRT : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) + ΔClockBehind ≤ ((tAwakeEnd : ℕ) : ℝ) := by
    have : ((M.supportCutoff S.C (σ + 1) + Δ S : ℕ) : ℝ) ≤ ((tAwakeEnd : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (σ + 1) + Δ S ≤ tAwakeEnd by omega)
    push_cast at this
    linarith
  have hStep : HonestChainExtends M S A x (Hon M S A x (σ + 1)) X (σ + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Executions.lem79_step_sets M F U) S A x R GST σ (Hon M S A x σ) (Hon M S A x (σ + 1))
      (fun s => S.P.committee s ∩ Hon M S A x s) X P.E P.hNet P.hSkew P.hRedeliver P.Sy P.hΔs
      ((per_tick_roots_of_roots_until M F) x P.E P.hRoots hRT) P.hParent
      ((votesCastByOwner_of_unforgeability M F) S A x R P.E) (P.gstSync M F U hσ).2.2 hInv.1
      ((roundMembers_mono M F) S A (σ + 1) (σ + 2) tAwakeEnd R P.E (Nat.le_succ _) hEnd).1
      hUp0
      (fun u hu => by
        -- the member's reader to its tick to the vote time of slot `σ + 1`, from its window from `tGAT`
        have hd := P.dws M F U (show r * S.C.R ≤ σ + 1 by omega)
        have hdr := (duty_window_start_real_of_pos M F U) S (σ + 1) (by omega)
        have hdv := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_le_voteTime M.toSlotLayout F.sched) S (σ + 1)
        have hdR : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.dutyWindowStart S.C (σ + 1) : ℕ) : ℝ) := by exact_mod_cast hd
        push_cast at hdR
        have hle : duty_window_start S.C (σ + 1) ≤ ((M.voteTime S.C (σ + 1) : ℕ) : ℤ) :=
          le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart M.toSlotLayout F.sched U) S (σ + 1))
            (by exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_le_voteTime M.toSlotLayout F.sched) S (σ + 1))
        have hve : ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) := by
          exact_mod_cast (show M.voteTime S.C (σ + 1) + Δ S ≤ M.supportCutoff S.C (σ + 2) by omega)
        refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R P.E (by omega) hle ?_
        refine Activity.mem_activeThroughout_of_le ?_ ?_ (P.window M F (Finset.mem_sdiff.1 hu).2 hEnd)
        · rw [hdr]; linarith
        · linarith)
      hUp1
      (fun u hu hX => (Finset.mem_sdiff.1 (hHA1 hu)).2 (Finset.mem_union_right _ hX))
      (hvoters σ hσ hEnd1) (hvoters (σ + 1) (by omega) hEnd)
      (fun w _ => ((counting_of_committee_majority_st M F) S A x R P.E σ (x.tickStep w (M.voteTime S.C (σ + 1)))
        (Hon M S A x σ) w (P.committee M F hσ hEnd1)).2.2)
      (fun v' _ => ((counting_of_committee_majority_st M F) S A x R P.E (σ + 1)
        (x.tickStep v' (M.supportCutoff S.C (σ + 2))) (Hon M S A x (σ + 1)) v' (P.committee M F (by omega) hEnd)).2.1)
      (fun w hw => (hSF w hw).1) (fun w hw => (hSF w hw).2.1) (fun w hw => (hSF w hw).2.2)
  refine ⟨hStep, fun u hu C' hC' => ?_⟩
  -- an updater of slot `σ + 1` ticks to the support cutoff of slot `σ + 2` inside the phase
  obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hu
  have hkE : x.time k ≤ tAwakeEnd := by
    have h1 := (P.E.tick_active k u _ hk).2.2
    have : ((M.supportCutoff S.C (σ + 2) + Δ S : ℕ) : ℝ) ≤ ((tAwakeEnd : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (σ + 2) + Δ S ≤ tAwakeEnd by omega)
    push_cast at this
    linarith
  exact P.conf_source_at M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hu hk hkE hX hμ C' hC'

/-- **The line invariant at every slot of the phase.** At every slot `σ` whose support cutoff of
slot `σ + 2` is at most `tAwakeEnd`, the slot invariant holds relative to every line source of a
slot before `σ`: by strong induction on `σ`, the base of each source at the slot after its own
(`base_source`, every kind), and `step_source` after.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: at every slot of the phase, the slot invariant holds relative to every line source of an
earlier slot. -/
theorem lineInv_all (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) :
    ∀ σ : ℕ, M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd → LineInv M S A x r H₂ σ := by
  intro σ
  induction σ using Nat.strong_induction_on with
  | _ σ ih =>
    intro hEσ μ X hX hμσ
    have hs := hX.slot_ge M F
    -- the invariant at every earlier slot, inside the phase
    have hG : ∀ σ', σ' < σ → LineInv M S A x r H₂ σ' := fun σ' h =>
      ih σ' h (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (by omega)) hEσ)
    rcases Nat.lt_or_eq_of_le hμσ with hlt | heq
    · -- a source of a slot `μ` with `μ + 1 < σ`: the step from slot `σ - 1`
      obtain ⟨σ₀, rfl⟩ : ∃ σ₀, σ = σ₀ + 1 := ⟨σ - 1, by omega⟩
      exact P.step_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx (fun σ' h => hG σ' (by omega)) (by omega)
        (by rw [show σ₀ + 3 = σ₀ + 1 + 2 from rfl]; exact hEσ) hX (by omega) (hG σ₀ (by omega) μ X hX (by omega))
    · -- the source's own next slot: the base
      subst heq
      exact P.base_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx (fun σ' h => hG σ' (by omega)) hs
        (by rw [show μ + 3 = μ + 1 + 2 from rfl]; exact hEσ) hX

end PartAHyps

namespace PartAHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}

/-- The line invariant at every slot up to `s`, when the support cutoff of slot `s + 2` is in the
phase.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: the line invariant holds at every slot up to `s`, within the phase. -/
theorem lineInv_upto (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {s : ℕ}
    (hEnd : M.supportCutoff S.C (s + 2) ≤ tAwakeEnd) :
    ∀ σ', σ' ≤ s → LineInv M S A x r H₂ σ' := fun σ' h =>
  P.lineInv_all M F R E hNet hSkew hRedeliver Sy hΔs U Fx σ'
    (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout
      F.sched) S (by linarith)) hEnd)

/-- **A fast block of an honest update at the action time of round `r` has chain-state height at most `H₂ + 1`**
. For an updater `u` of slot `r * R` and a node state `n_u` the update of slot `r * R + 1` leaves from
`u`'s tick input at `aR M S r`, every fast block `X` of `n_u` has chain-state height at most `H₂ + 1`.

Why: `X` passes the fast test, so some honest active committee member `w` of slot `r * R` sent, at its tick `k` to the
vote time of slot `r * R`, a vote for a block `H_w` of its tick input with `X` equal to `H_w` or an ancestor of it
(`fast_block_has_honest_supporter_vote_of_update`; the committee's majority is honest, `hCommittees`). That tick is at
a real time at most the vote time plus `ΔClockBehind`, so every step before it is at a real time whose sum with
`ΔClockAhead` is less than `aR M S r` (`hSkew`), and `hOld` bounds every honest attestation sent before it
(`oldStep_of_clock`); A2 (`held_height_le_before_action`) at the step `k` bounds `H_w`'s height by `H₂ + 1`, and
`X`'s height is at most `H_w`'s.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the bundle of part A; `u`: the updater; `n_u`: the node state its update leaves; `X`: the fast block.

Read aloud: a fast block of an honest update at the action time of round `r` has height at most `H₂ + 1`. -/
theorem fast_block_height_le_at_action_tick (R : RunFacts M S x) (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {u : V} {n_u : M.N} {X : Block V} (hu : u ∈ updaterAt M S A x (r * S.C.R))
    (hUpdate_u : ConfirmationUpdated M S.C S.P (x.tickInput u (aR M S r)) ((aR M S r : ℕ) : Int)
      (r * S.C.R + 1) n_u)
    (hFast_u : X ∈ M.fastBlocks n_u) : (M.chainStateOf S.C X).h ≤ H₂ + 1 := by
  have hΔ := one_le_Δ S
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hEnd : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd := P.hEnd
  obtain ⟨w, -, H_w, hHw, hXH, k, hk, -⟩ :=
    (fast_block_has_honest_supporter_vote_of_update M F U) S A x R (anchorCW S tGAT) (r * S.C.R) u P.E P.hSkew
      ((votesCastByOwner_of_unforgeability M F) S A x R P.E) (P.hRoots.mono M (by exact_mod_cast hEnd))
      (P.hCommittees.mono M hEnd) P.hAnchor hu n_u hUpdate_u X hFast_u
  -- `w`'s tick `k` to the vote time of slot `r * R` is at a real time at most that vote time plus `ΔClockBehind`, at
  -- least one delay before `aR M S r`
  have hkt := (P.E.tick_active k w _ hk).2.2
  obtain ⟨hv0, -, -, hs0, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S
    (r * S.C.R)
  obtain ⟨-, hc1, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S
    (r * S.C.R + 1)
  have h3 : ((M.voteTime S.C (r * S.C.R) : ℕ) : ℝ) + Δ S ≤ ((aR M S r : ℕ) : ℝ) := by
    exact_mod_cast (show M.voteTime S.C (r * S.C.R) + Δ S ≤ M.supportCutoff S.C (r * S.C.R + 1) by omega)
  have hsk := P.hSkew
  have haE : ((aR M S r : ℕ) : ℝ) ≤ ((tAwakeEnd : ℕ) : ℝ) := by exact_mod_cast P.hEnd
  have hkE : x.time k ≤ tAwakeEnd := by linarith
  have hOldK := (oldStep_of_clock M F) P.R P.E P.hOld P.hEnd (i := k) (fun k' hk' => by
    have := (time_mono M) x P.R hk'.le
    linarith)
  have hTI : x.tickInput w (M.voteTime S.C (r * S.C.R)) = x.st k w := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x P.E hk]
  rw [hTI] at hHw
  have hle := (held_height_le_before_action M F Fx) S A x R P.E tAwakeEnd H₂ k k w H_w P.hThird hOldK hkE le_rfl hHw
  exact le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C hXH) hle

/-- **`source_later` with `u`'s tick to `aR M S r'` in the phase.** A fast block of a node state an honest update
leaves at the action time of a round `r' ≥ r` is a line source of the round's first slot: of kind (b) when `r' > r`;
when `r' = r`, of kind (a) at the height `H₂ + 1`, and an ancestor of `L` at a lower height (the height is at most
`H₂ + 1`, `fast_block_height_le_at_action_tick`; at a lower height Lemma 32 makes `X` compatible with `L`, comparing
the confirmations `u` and `v` saved at their ticks to `aR M S r`, both in the phase: `u`'s by `hEndU`, `v`'s by the
bundle's `hEndStep`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the bundle of part A; `r'`: the round; `u`: the updater; `X`: the fast block; `n_u`: the node state;
  `hEndU`: every tick of `u` to `aR M S r'` is at a real time at most `tAwakeEnd`.

Read aloud: a fast block of an honest update of a later round, whose tick is in the phase, is a line source of that
round's first slot. -/
theorem source_later_of_tick_in_phase (R : RunFacts M S x) (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {r' : ℕ} {u : V} {X : Block V} {n_u : M.N} (hr' : r ≤ r') (hu : u ∉ A.corruptedAtTime x (aR M S r'))
    (hUpdate_u : ConfirmationUpdated M S.C S.P (x.tickInput u (aR M S r'))
      ((aR M S r' : ℕ) : Int) (r' * S.C.R + 1) n_u)
    (hFast_u : X ∈ M.fastBlocks n_u) (hEnd : M.supportCutoff S.C (r' * S.C.R + 1) ≤ tAwakeEnd)
    (hEndU : ∀ k : ℕ, x.lbl k = Event.tick u (aR M S r') → x.time k ≤ tAwakeEnd) :
    LineSource M S A x r H₂ (r' * S.C.R) X := by
  have huH : u ∈ Hon M S A x (r' * S.C.R) := by
    unfold Hon roundMembers
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hu⟩
  have hrR : r * S.C.R ≤ r' * S.C.R := Nat.mul_le_mul_right _ hr'
  have hupd : u ∈ updaterAt M S A x (r' * S.C.R) := P.memberU M F U hrR huH hEnd
  have hU : ConfirmationUpdated M S.C S.P (x.tickInput u (M.supportCutoff S.C (r' * S.C.R + 1)))
      ((M.supportCutoff S.C (r' * S.C.R + 1) : ℕ) : Int) (r' * S.C.R + 1) n_u := hUpdate_u
  obtain ⟨C₀, hC₀, hXC₀⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_fast_block_saved
      (Nat.le_add_left 1 _) hU hFast_u
  rw [Nat.add_sub_cancel] at hC₀
  have hst := (state_saved_of_update M F U) S A x R (r' * S.C.R) u n_u P.E hupd hU
  rcases Nat.lt_or_eq_of_le hr' with hlt | heq
  · refine ⟨u, hupd, n_u, C₀, X, hU, hC₀, hst.trans hC₀, ancestorEq_refl X, hXC₀,
      Or.inr (Or.inl ⟨?_, Or.inl hFast_u⟩)⟩
    have h1 := Nat.mul_le_mul_right S.C.R (show r + 1 ≤ r' by omega)
    have h2 := S.C.R_ge_two
    rw [Nat.succ_mul] at h1
    omega
  · subst heq
    have hle := P.fast_block_height_le_at_action_tick M F R U Fx hupd hU hFast_u
    by_cases hh : (M.chainStateOf S.C X).h = H₂ + 1
    · exact ⟨u, hupd, n_u, C₀, X, hU, hC₀, hst.trans hC₀, ancestorEq_refl X, hXC₀,
        Or.inl ⟨rfl, hFast_u, hh⟩⟩
    · -- at a lower height, `X` and `L` are compatible (Lemma 32 on the two savers' confirmations)
      have hvH : v ∈ Hon M S A x (r * S.C.R) := by
        unfold Hon roundMembers
        exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, P.hv⟩
      have hUv : ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (r * S.C.R + 1)))
          ((M.supportCutoff S.C (r * S.C.R + 1) : ℕ) : Int) (r * S.C.R + 1) n' := P.hUpdate
      have hvU : v ∈ updaterAt M S A x (r * S.C.R) := P.memberU M F U le_rfl hvH hEnd
      obtain ⟨C', hC', hLC'⟩ :=
        GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_fast_block_saved
          (Nat.le_add_left 1 _) hUv P.hFast
      rw [Nat.add_sub_cancel] at hC'
      have hstv := (state_saved_of_update M F U) S A x R (r * S.C.R) v n' P.E hvU hUv
      obtain ⟨k₁, hk₁, -⟩ := Activity.mem_activeThroughoutToTick.1 hupd
      obtain ⟨k₂, hk₂, -⟩ := Activity.mem_activeThroughoutToTick.1 hvU
      have hk₂E : x.time k₂ ≤ tAwakeEnd := by
        have h := P.hEndStep
        rw [(tickStep_eq_of_lbl M) x P.E (show x.lbl k₂ = Event.tick v (aR M S r) from hk₂)] at h
        exact h
      have hRoots' : RootsNameBlocksUntil M A x (max (x.time (x.tickStep u (M.supportCutoff S.C (r * S.C.R + 1))))
          (x.time (x.tickStep v (M.supportCutoff S.C (r * S.C.R + 1))))) := by
        rw [(tickStep_eq_of_lbl M) x P.E hk₁, (tickStep_eq_of_lbl M) x P.E hk₂]
        exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
          (max_le (hEndU k₁ hk₁) hk₂E) P.hRoots
      have hc := (GoldilocksCorrectness.Record.Proofs.Executions.lem32_saved_confirmations_compatible_state M F U) S A x
        R GST (r * S.C.R) u v C₀ C' P.E P.hNet P.hSkew P.hRedeliver P.Sy P.hΔs hRoots' (P.gstSync M F U le_rfl).2.1
        hupd hvU (hst.trans hC₀) (hstv.trans hC')
      have hXL := compatible_of_ancestorEq_both hXC₀ hLC' hc
      rcases (compatible_iff _ _).1 hXL with h | h
      · exact (P.source_L M F R U hEnd).anc M F h
      · exfalso
        have := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C h
        rw [P.hL] at this
        unfold Height at *
        omega

/-- A fast block of a node state an honest update leaves (`ConfirmationUpdated`) at the action time
of a round `r' ≥ r` is a line source of the round's first slot: of kind (b) when `r' > r`; when
`r' = r`, of kind (a) at the height `H₂ + 1`, and an ancestor of `L` at a lower height (A2 bounds
the height by `H₂ + 1`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: a fast block of an honest update of a later round is a line source of that round's first
slot. -/
theorem source_later (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {r' : ℕ} {u : V}
    {X : Block V} {n_u : M.N} (hr' : r ≤ r') (hu : u ∉ A.corruptedAtTime x (aR M S r'))
    (hUpdate_u : ConfirmationUpdated M S.C S.P (x.tickInput u (aR M S r'))
      ((aR M S r' : ℕ) : Int) (r' * S.C.R + 1) n_u)
    (hFast_u : X ∈ M.fastBlocks n_u)
    -- the support cutoff of slot `r' * R + 2` is at most `tAwakeEnd`, which bounds the real time of `u`'s tick to the
    -- action time of round `r'` (F-80-1)
    (hEnd : M.supportCutoff S.C (r' * S.C.R + 2) ≤ tAwakeEnd) :
    LineSource M S A x r H₂ (r' * S.C.R) X :=
  P.source_later_of_tick_in_phase M F R U Fx hr' hu hUpdate_u hFast_u
    (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (Nat.le_succ _)) hEnd)
    (fun _ hk => (time_le_of_tick_supportCutoff M F U) E hSkew (μ := r' * S.C.R) hEnd hk)

end PartAHyps

namespace PartAHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}

/-- Every block of `FastFamilyFrom M S Sched x (r * R + k) L s'` is a line source of a slot before
`s'`, for `s' ≥ r * R + 1` in the phase.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: every block of the late family is a line source of an earlier slot. -/
theorem family_source (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {s' : ℕ}
    (hs : r * S.C.R + 1 ≤ s') (hEnd : M.supportCutoff S.C s' ≤ tAwakeEnd) {C : Block V}
    (hC : FastFamilyFrom M S A x (r * S.C.R + S.C.k) L s' C) :
    ∃ μ : ℕ, μ + 1 ≤ s' ∧ LineSource M S A x r H₂ μ C := by
  rcases hC with hCL | ⟨σ, hσ1, hσ2, u, hu, C', hC', hCC'⟩
  · exact ⟨r * S.C.R, hs, (P.source_L M F R U (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S hs) hEnd)).anc M F hCL⟩
  · exact ⟨σ, hσ2, P.source_conf M F R E U hσ1 hu (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S hσ2) hEnd) hC' hCC'⟩

/-- From slot `r * R + 2k − 1` on, the live locks a member holds at the vote time of the next
slot are on members' confirmations of slots from `r * R + k` on: every such lock is of a slot at
least `s + 1 − k` (Lemma 41), on its holder's confirmation of that slot (Lemma 39).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: late in the phase, a member's live locks are on members' confirmations of slots from `k`
past the round's first. -/
theorem late_locks_on_family (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {s : ℕ}
    (hs : r * S.C.R + 2 * S.C.k - 1 ≤ s) {u : V} (hu : u ∈ Hon M S A x s) :
    LiveLocksOnFamilyAt M S A x (FastFamilyFrom M S A x (r * S.C.R + S.C.k) L s) s u := by
  have hk := S.C.k_ge_two
  refine (GoldilocksCorrectness.Record.Proofs.Executions.liveLocksOnFamilyAt_of_live M F U) S A x R E _ s u (fun e he hl => ?_)
  have hl' := hl
  rw [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hl'
  obtain ⟨μ₀, hd, hcut, C', hsv, heC'⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.lock_entry_confirmation M F U) S A x R _ u e P.E he
  have hlo : s + 1 - S.C.k ≤ μ₀ :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem41_slot_of_live_entry M F U) S (s + 1 - S.C.k) μ₀
      (M.voteTime S.C (s + 1)) e hd hl'.1 (by rw [show s + 1 - S.C.k + S.C.k = s + 1 by omega])
  have hhi : μ₀ < s := by
    by_contra h
    obtain ⟨hv1, hc1, -, hs1, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s + 1)
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show s + 1 ≤ μ₀ + 1 by omega)
    omega
  have huμ : u ∈ Hon M S A x μ₀ := by
    unfold Hon roundMembers at hu ⊢
    obtain ⟨-, hu'⟩ := Finset.mem_sdiff.1 hu
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, (not_mem_corruptedAtTime_of_le M) x R P.E (by exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show μ₀ + 1 ≤ s + 1 by omega)) hu'⟩
  exact Or.inr ⟨μ₀, by omega, hhi, u, huμ, C', hsv, heC'⟩

end PartAHyps

/-- **A7a, the frame of an honest validator relative to the fast block.** The proof; the audited
statement is in `Statements/Executions/Lemma89Statements.lean`. The update of `v` at the action time
is an outcome `(n', sent)` of `v`'s tick there with `L` among the fast blocks of `n'` (template A2),
without A2's hypothesis that `v` has been awake since the duty window's start of slot `r * R + 1`:
`hAwake`, `hAnchor` and `hv` give it, as for `fast_block_base`'s twin. Why: `frame_source_at` at the
line source `L`, with the line invariant up to slot `s` (`lineInv_upto`).

Roots name blocks until `M.supportCutoff S.C (s + 2)`: the bundle `PartAHyps` is built with its end
time `M.supportCutoff S.C (s + 2)`, the latest time its kit reads here.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: after the fast block's round, every honest validator's finality gadget lets it follow
the fast block. -/
theorem frame_at_time_relative_to_fast_block (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ s t : ℕ) (v w : V)
      (L : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 2)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    -- the reading time, from the vote time of slot `s + 1` to the update of slot `s + 1`
    (hs : r * S.C.R + 1 ≤ s) (hts : M.voteTime S.C (s + 1) ≤ t)
    (ht : t ≤ M.supportCutoff S.C (s + 2)) (hEnd : M.supportCutoff S.C (s + 2) ≤ tAwakeEnd)
    (hw : w ∉ A.corruptedAtTime x t) :
    (M.fg_to_ac (x.stateBefore t w)).fc_root.compatible L = true ∧
    ((M.fg_to_ac (x.stateBefore t w)).fc_root.AncestorEq L →
      ∃ W ∈ (M.fg_to_ac (x.stateBefore t w)).tree,
        W ∈ (M.fg_to_ac (x.stateBefore t w)).viable_heads ∧ L.AncestorEq W) ∧
    (x.stateBefore t w).finalized.compatible L = true := by
  have P := (PartAHyps.of_tick M F U) R E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST
    (hThird.mono (by exact_mod_cast hEnd))
    (fun i u hi hg hc => hAwake i u (le_trans hi (by exact_mod_cast hEnd)) hg hc)
    (fun s' h1 h2 u hu => hActive s' h1 (le_trans h2 hEnd) u hu)
    (hCommittees.mono M hEnd) hAnchor hOld hv hUpdate hFast hL ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))
  exact P.frame_source_at M F R E hNet hSkew hRedeliver Sy hΔs U Fx (P.lineInv_upto M F R E hNet hSkew hRedeliver Sy hΔs U Fx le_rfl)
    (by omega) le_rfl hts ht hw (P.source_L M F R U ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) (by omega)

/-- **A7b, the chain step's frame conditions relative to the fast block.** The proof; the audited
statement is in `Statements/Executions/Lemma89Statements.lean`. The update of `v` at the action time
is an outcome `(n', sent)` of `v`'s tick there with `L` among the fast blocks of `n'` (template A2),
without A2's hypothesis that `v` has been awake since the duty window's start of slot `r * R + 1`:
`hAwake`, `hAnchor` and `hv` give it, as for `fast_block_base`'s twin. Why: `stepFrame_source` at
the line source `L`.

Roots name blocks until `tAwakeEnd`: the bundle `PartAHyps` is built with its end time `tAwakeEnd`; the
third conjunct of `StepFrameAt` is read at each member's tick to the support cutoff of slot `s + 2`,
which `hEndTick` places at a real time at most `tAwakeEnd`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: every member's vote and update of the next slot can follow the fast block. -/
theorem stepFrame_relative_to_fast_block (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ s : ℕ) (v : V) (L : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (hs : r * S.C.R + 1 ≤ s) (hEnd : M.supportCutoff S.C (s + 2) ≤ tAwakeEnd)
    (hEndTick : ∀ (w : V) (k : ℕ), x.lbl k = Event.tick w (M.supportCutoff S.C (s + 2)) →
      x.time k ≤ tAwakeEnd) :
    ∀ w ∈ Hon M S A x (s + 1), StepFrameAt M S A x L s w := by
  intro w hw
  have P := (PartAHyps.of_tick M F U) R E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird hAwake hActive
    hCommittees hAnchor hOld hv hUpdate hFast hL
    (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd)
  exact P.stepFrame_source_of_tick M F R E hNet hSkew hRedeliver Sy hΔs U Fx
    (P.lineInv_upto M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEnd) (by omega) hEnd (Finset.mem_sdiff.1 hw).2
    (hEndTick w)
    (P.source_L M F R U (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd))
    (by omega)

/-- **A5, the slot invariant restricted to `L` at slot `r * R + 1`.** The proof; the audited
statement is in `Statements/Executions/Lemma89Statements.lean`. The proof sits on this page, after the
line sources it reads (it was on `Lemma89FastBase.lean`, which this page imports).

The route, with `μ := r * R`: the bundle `PartAHyps` with the phase's end read at the support
cutoff of slot `μ + 2` (`PartAHyps.of_tick`; every premise it carries holds up to that cutoff, which
is at most `tAwakeEnd`), and `L` the line source of slot `μ` (`source_L`). The invariant at the
slots up to `μ` asks nothing (no line source has a slot less than `μ`).
- Clause 1, the votes of slot `μ + 1`: `votes_source_base`.
- Clause 2, the live locks of slot `μ + 2`: `locks_step_of_clauses` over `base_locks` and Lemma 32
  between the member and `v`, as `base_source` does.
- Clause 3, the confirmations of slot `μ + 1`: Lemma 78 (`confirmations_of_votes_clause`) at every
  updater of slot `μ + 1`. Its finalized block at its tick to the support cutoff of slot `μ + 2` is
  compatible with `L` by a strong induction over the step of that tick:
  `finalized_compatible_fast_block` at that step, whose later-slot clause holds at slot `μ + 1` by
  the induction hypothesis and Lemma 78 (that updater ticked at an earlier step), and asks nothing at
  later slots (a tick to the support cutoff of slot `μ + 3` or later is at a real time at least
  `4Δ − ΔClockAhead` after that cutoff of slot `μ + 2`, and `u`'s tick at most `ΔClockBehind` after
  it, `hSkew`). `hRootsTick` and `hEndTick` give the roots and the phase's end at the real time of
  every such tick.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `GST`: the time from which the network is
  synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the bound on the
  old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast block; `n'`,
  `sent`: an outcome of `v`'s tick at the support cutoff of slot `r * R + 1`.

Read aloud: the slot after the fast block's round, every honest vote, live lock and confirmation
extends the fast block. -/
theorem fast_block_base (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (r * S.C.R + 2)))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `r * R + 2`
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (r * S.C.R + 2) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hEnd : M.supportCutoff S.C (r * S.C.R + 2) ≤ tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `r * R + 2` is at a real time at most `tAwakeEnd`
    --
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (r * S.C.R + 2) →
      x.time k ≤ tAwakeEnd)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1) :
    HonestChainExtends M S A x (Hon M S A x (r * S.C.R + 1)) L (r * S.C.R + 1) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hsk := hSkew
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  set μ := r * S.C.R with hμ
  have hσ : r * S.C.R ≤ μ := hμ.symm.le
  -- the times
  have hcs1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (μ + 1)
  have hcs2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (μ + 2)
  rw [show μ + 1 + 1 = μ + 2 from rfl] at hcs1
  rw [show μ + 2 + 1 = μ + 3 from rfl] at hcs2
  have hE1 : M.supportCutoff S.C (μ + 1) ≤ M.supportCutoff S.C (μ + 2) := by omega
  have hc2 : M.supportCutoff S.C (μ + 2) = M.voteTime S.C (μ + 2) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (μ + 2)
  have hv2 : M.voteTime S.C (μ + 2) = M.voteTime S.C (μ + 1) + 4 * Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S (μ + 1)
  have hv1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (μ + 1)
  have hs1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (μ + 1)
  have hs2 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (μ + 2)
  have hdc := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S (μ + 2)
  have hk8 := Nat.mul_le_mul_left (4 * Δ S) S.C.k_ge_two
  have hm2 : 4 * Δ S * (μ + 2) = 4 * Δ S * (μ + 1) + 4 * Δ S := by ring
  -- the bundle of part A, with the phase's end at the support cutoff of slot `μ + 2`
  have P := (PartAHyps.of_tick M F U) (tAwakeEnd := M.supportCutoff S.C (μ + 2)) R E hNet hSkew hRedeliver Sy
    hΔs hRoots hParent hGST (hThird.mono (by exact_mod_cast hEnd))
    (fun i u hi => hAwake i u (le_trans hi (by exact_mod_cast hEnd)))
    (fun s h1 h2 => hActive s h1 (le_trans h2 hEnd)) (hCommittees.mono M hEnd) hAnchor hOld hv hUpdate hFast hL
    le_rfl
  -- the invariant at the slots up to `μ` asks nothing: no line source has a slot less than `μ`
  have hG : ∀ σ', σ' ≤ μ → LineInv M S A x r H₂ σ' := fun σ' h μ' X hX hμ' => by
    have := hX.slot_ge M F
    omega
  have hX := P.source_L M F R U hE1
  -- clause 1: the votes of slot `μ + 1`
  have hV := P.votes_source_base M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ le_rfl hX
  obtain ⟨hHA1, hUp1⟩ := P.members_sets M F U (show r * S.C.R ≤ μ + 1 by omega) le_rfl
  obtain ⟨-, hUp0⟩ := P.members_sets M F U hσ hE1
  -- Lemma 78 at an updater of slot `μ + 1`, from its finalized block
  have hRootsP : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (μ + 1) →
      RootsNameBlocksUntil M A x (x.time k) := fun k u c hk hc => hRootsTick k u c hk (le_trans hc hE1)
  have h78 : ∀ u ∈ updaterAt M S A x (μ + 1),
      (x.tickInput u (M.supportCutoff S.C (μ + 1 + 1))).finalized.compatible L = true →
      ∀ C₁ : Block V,
        (x.tickOutput u (M.supportCutoff S.C (μ + 1 + 1))).savedConfirmation (μ + 1) = some C₁ →
        L.AncestorEq C₁ := fun u hu hF =>
    (confirmations_of_votes_clause M F U) S A x R GST (μ + 1) (Hon M S A x (μ + 1)) L u E hNet hSkew
      hRedeliver Sy hΔs hRootsP hParent ((votesCastByOwner_of_unforgeability M F) S A x R E)
      (P.gstSync M F U (show r * S.C.R ≤ μ + 1 by omega)).2.2 hHA1
      (P.committee M F (show r * S.C.R ≤ μ + 1 by omega) le_rfl) hV hu hF
  -- `v`: an updater of slot `μ`, its saved confirmation `C'` extends `L`, and it holds `L` at its tick
  have hvH : v ∈ Hon M S A x μ := by
    unfold Hon roundMembers
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hv⟩
  have hvU : v ∈ updaterAt M S A x μ := P.memberU M F U le_rfl hvH hE1
  have hU : ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (μ + 1)))
      ((M.supportCutoff S.C (μ + 1) : ℕ) : Int) (μ + 1) n' := P.hUpdate
  obtain ⟨C', hC', hLC'⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_fast_block_saved
      (Nat.le_add_left 1 _) hU P.hFast
  rw [Nat.add_sub_cancel] at hC'
  have hSaved : (x.tickOutput v (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C' :=
    ((state_saved_of_update M F U) S A x R μ v n' E hvU hU).trans hC'
  have hLv : L ∈ (x.tickInput v (M.supportCutoff S.C (μ + 1))).tree := (P.L_held_v M F R E U hE1).2
  have hk₀ : x.lbl (x.tickStep v (M.supportCutoff S.C (μ + 1))) = Event.tick v (M.supportCutoff S.C (μ + 1)) :=
    P.hk₀
  -- every updater of slot `μ + 1` reads, at its tick to the support cutoff of slot `μ + 2`, a finalized block
  -- compatible with `L`: by strong induction over the step of that tick
  have hFin : ∀ k : ℕ, ∀ u ∈ updaterAt M S A x (μ + 1),
      x.tickStep u (M.supportCutoff S.C (μ + 2)) = k →
      (x.tickInput u (M.supportCutoff S.C (μ + 2))).finalized.compatible L = true := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro u hu hku
      obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hu
      have hks : x.tickStep u (M.supportCutoff S.C (μ + 2)) = k' := (tickStep_eq_of_lbl M) x E hk'
      have hkk : k' = k := hks.symm.trans hku
      subst hkk
      have hkt := (E.tick_active _ _ _ hk').2.2
      have hwk : u ∉ A.corrupted k' := E.not_mem_corrupted_of_tick hk'
      have hR68 : RootsNameBlocksUntil M A x
          (max (x.time k') (x.time (x.tickStep v (M.supportCutoff S.C (μ + 1))))) := by
        rcases max_cases (x.time k') (x.time (x.tickStep v (M.supportCutoff S.C (μ + 1)))) with
          ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
        · exact hRootsTick k' u _ hk' le_rfl
        · exact hRootsTick _ v _ hk₀ hE1
      have hEndM : max (x.time k') (x.time (x.tickStep v (M.supportCutoff S.C (μ + 1)))) ≤ tAwakeEnd :=
        max_le (hEndTick k' u _ hk' le_rfl) (hEndTick _ v _ hk₀ hE1)
      show (x.st (x.tickStep u (M.supportCutoff S.C (μ + 2))) u).finalized.compatible L = true
      rw [hks]
      refine (finalized_compatible_fast_block M F U Fx) S A x R GST tAwakeEnd μ H₂ k' v u L C' E hNet hSkew
        hRedeliver Sy hΔs hR68 hThird hOld (P.gstSync M F U hσ).2.1 hEndM (le_trans hE1 hEnd) hvU hSaved hLC'
        hLv hL ?_ hwk
      intro s_a u' C₁ hlt hu' hk'' hC₁
      obtain ⟨k₁, hk₁, -⟩ := Activity.mem_activeThroughoutToTick.1 hu'
      have hks₁ : x.tickStep u' (M.supportCutoff S.C (s_a + 1)) = k₁ := (tickStep_eq_of_lbl M) x E hk₁
      rw [hks₁] at hk''
      rcases Nat.lt_or_ge s_a (μ + 2) with hs | hs
      · -- slot `μ + 1`: the induction hypothesis at `u'`'s earlier tick, and Lemma 78
        obtain rfl : s_a = μ + 1 := by omega
        have hF₁ := ih k₁ hk'' u' hu' hks₁
        exact (compatible_iff _ _).2 (Or.inr (h78 u' hu' hF₁ C₁ hC₁))
      · -- a later slot: its tick to the support cutoff comes after `u`'s
        exfalso
        have h1 := (E.tick_active _ _ _ hk₁).2.1
        have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
          (show μ + 3 ≤ s_a + 1 by omega)
        have h4 : ((M.supportCutoff S.C (μ + 3) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s_a + 1) : ℕ) : ℝ) := by
          exact_mod_cast hmono
        have h23 : ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) + 4 * Δ S ≤ ((M.supportCutoff S.C (μ + 3) : ℕ) : ℝ) := by
          exact_mod_cast (show M.supportCutoff S.C (μ + 2) + 4 * Δ S ≤ M.supportCutoff S.C (μ + 3) by omega)
        have hkk := (time_mono M) x R hk''.le
        linarith
  refine ⟨hV, ?_, fun u hu C₁ hC₁ => h78 u (hUp1 hu) (hFin _ u (hUp1 hu) rfl) C₁ hC₁⟩
  -- clause 2: the live locks of slot `μ + 2` at a member `w` (`locks_step_of_clauses`), as `base_source`
  intro w hw n₂ sent₂ hrun₂ hAw₂ e₂ he₂ hlive₂
  have hwc : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (μ + 2)) := (Finset.mem_sdiff.1 hw).2
  have hwU : w ∈ updaterAt M S A x μ :=
    hUp0 (((roundMembers_mono M F) S A (μ + 1) (μ + 2) (M.supportCutoff S.C (μ + 2)) R E (Nat.le_succ _)
      le_rfl).1 hw)
  -- the live locks of `w`'s revocation of slot `μ + 1` (`base_locks`) and `w`'s saved confirmation of slot `μ`,
  -- compatible with `v`'s (Lemma 32)
  have hL2 := P.base_locks M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG le_rfl hX hwc
  have htickE : ∀ {u : V} {k c : ℕ}, x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (μ + 1) →
      x.time k ≤ ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
    intro u k c hk hc
    have h1 := (E.tick_active k u c hk).2.2
    have h2 : ((c + Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
      exact_mod_cast (show c + Δ S ≤ M.supportCutoff S.C (μ + 2) by omega)
    push_cast at h2
    linarith
  have hL3 : ∀ C₁ : Block V,
      (x.tickOutput w (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C₁ → C₁.compatible L = true := by
    intro C₁ hC₁
    obtain ⟨kw, hkw, -⟩ := Activity.mem_activeThroughoutToTick.1 hwU
    have hRoots' : RootsNameBlocksUntil M A x (max (x.time (x.tickStep w (M.supportCutoff S.C (μ + 1))))
        (x.time (x.tickStep v (M.supportCutoff S.C (μ + 1))))) := by
      rw [(tickStep_eq_of_lbl M) x E hkw]
      exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
        (max_le (htickE hkw le_rfl) (htickE hk₀ le_rfl)) hRoots
    exact compatible_of_ancestorEq_both (ancestorEq_refl C₁) hLC'
      ((GoldilocksCorrectness.Record.Proofs.Executions.lem32_saved_confirmations_compatible_state M F U) S A x R GST μ
        w v C₁ C' E hNet hSkew hRedeliver Sy hΔs hRoots' (P.gstSync M F U hσ).2.1 hwU hvU hC₁ hSaved)
  -- `w`'s reader up to its tick to the vote time of slot `μ + 1`, from its window from `tGAT`
  have hHon : w ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (μ + 2) : ℕ) : ℤ) (M.voteTime S.C (μ + 1)) := by
    have hd := P.dws M F U (show r * S.C.R ≤ μ + 2 by omega)
    have hdv : M.dutyWindowStart S.C (μ + 2) ≤ M.voteTime S.C (μ + 1) := by omega
    have hdR : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.dutyWindowStart S.C (μ + 2) : ℕ) : ℝ) := by exact_mod_cast hd
    push_cast at hdR
    have hve : ((M.voteTime S.C (μ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C (μ + 1) + Δ S ≤ M.supportCutoff S.C (μ + 2) by omega)
    refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R E (by omega) (by exact_mod_cast hdv) ?_
    refine Activity.mem_activeThroughout_of_le ?_ ?_ (P.window M F hwc le_rfl)
    · push_cast; linarith
    · linarith
  exact (locks_step_of_clauses M F U) S A x R L μ w E hL2 hL3 hHon n₂
    ((locksRevoked_of_vote_tickInput M F U) x R (μ + 2) w n₂ sent₂ hrun₂ hAw₂) e₂ he₂ hlive₂

/-- **A8a, the slot invariant relative to `L` at every slot of the phase from `r * R + 1`.** The
proof; the audited statement is in `Statements/Executions/Lemma89Statements.lean`. The update of `v`
at the action time is an outcome `(n', sent)` of `v`'s tick there with `L` among the fast blocks of
`n'` (template A2), without A2's hypothesis that `v` has been awake since the duty window's start of
slot `r * R + 1`: `hAwake`, `hAnchor` and `hv` give it, as for `fast_block_base`'s twin. Why:
`lineInv_all` at the line source `L`.

Roots name blocks until `tAwakeEnd`: the bundle `PartAHyps` carries the premise at the phase's
end; the conclusion holds at every slot whose support cutoff of the slot after next is at most
`tAwakeEnd`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: from the slot after the fast block's round to the end of the phase, every honest vote,
live lock and confirmation extends the fast block. -/
theorem fast_line_invariant_L (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1) :
    ∀ s : ℕ, r * S.C.R + 1 ≤ s → M.supportCutoff S.C (s + 2) ≤ tAwakeEnd →
      HonestChainExtends M S A x (Hon M S A x s) L s := by
  intro s hs hE
  have P := (PartAHyps.of_tick M F U) R E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird hAwake hActive
    hCommittees hAnchor hOld hv hUpdate hFast hL (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hE)
  exact (P.lineInv_all M F R E hNet hSkew hRedeliver Sy hΔs U Fx s hE _ L
    (P.source_L M F R U (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hE)) (by omega)).1

/-- **A8d, every later honest fast block is extended by everything after its round.** The proof; the
audited statement is in `Statements/Executions/Lemma89Statements.lean`. The update of `v` at the
action time is an outcome `(n', sent)` of `v`'s tick there with `L` among the fast blocks of `n'`
(template A2), without A2's hypothesis that `v` has been awake since the duty window's start of slot
`r * R + 1`: `hAwake`, `hAnchor` and `hv` give it, as for `fast_block_base`'s twin. The later
round's update of `u` is read in the same way, as an outcome `(n_u, sent_u)` of `u`'s tick at the
action time of round `r'`. Why: `lineInv_all` at the line source `X` (`source_later`).

Roots name blocks until `tAwakeEnd`: the bundle `PartAHyps` carries the premise at the phase's
end; the conclusion holds at every slot whose support cutoff of the slot after next is at most
`tAwakeEnd`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: once an honest validator fast-confirms a block at a round's action time after the fast
block's round, every later honest vote, live lock and confirmation of the phase extends it. -/
theorem fast_line_at_later_round (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ r' : ℕ) (v u : V)
      (L X : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    -- a later round's honest fast block
    (hr' : r ≤ r') (hu : u ∉ A.corruptedAtTime x (aR M S r'))
    (n_u : M.N) (sent_u : List (NamedObject V))
    (hUpdate_u : .ok (n_u, sent_u) ∈ M.tick S.C S.P S.X (x.tickInput u (aR M S r'))
        ((aR M S r' : ℕ) : Int))
    (hFast_u : X ∈ M.fastBlocks n_u) :
    ∀ σ : ℕ, r' * S.C.R + 1 ≤ σ → M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd →
      HonestChainExtends M S A x (Hon M S A x σ) X σ := by
  intro σ hσ hE
  have hrR : r * S.C.R ≤ r' * S.C.R := Nat.mul_le_mul_right _ hr'
  have P := (PartAHyps.of_tick M F U) R E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird hAwake hActive
    hCommittees hAnchor hOld hv hUpdate hFast hL
    (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hE)
  have hE2' : M.supportCutoff S.C (r' * S.C.R + 2) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hE
  have hEndR' : M.supportCutoff S.C (r' * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hE
  -- `u` is an updater of slot `r' * R` (`hActive`), so its tick ran the update of slot `r' * R + 1`
  have huU : u ∈ updaterAt M S A x (r' * S.C.R) :=
    (hActive (r' * S.C.R) (by have := P.dws M F U hrR; omega) hEndR' u hu).2
  have hU_u := (confirmationUpdated_of_phase_tick M F U) x R r' u n_u sent_u E huU hUpdate_u
  exact (P.lineInv_all M F R E hNet hSkew hRedeliver Sy hΔs U Fx σ hE _ X
    (P.source_later_of_tick_in_phase M F R U Fx hr' hu hU_u hFast_u hEndR'
      (fun k hk => (time_le_of_tick_supportCutoff M F U) E hSkew (μ := r' * S.C.R) hE2' hk)) (by omega)).1

/-- **A8c, the members' confirmations form one chain from slot `r * R + k` on.** The proof; the
audited statement is in `Statements/Executions/Lemma89Statements.lean`. The update of `v` at the
action time is an outcome `(n', sent)` of `v`'s tick there with `L` among the fast blocks of `n'`
(template A2), without A2's hypothesis that `v` has been awake since the duty window's start of slot
`r * R + 1`: `hAwake`, `hAnchor` and `hv` give it, as for `fast_block_base`'s twin. Why: a member's
confirmation of a slot `σ ≥ r * R + k` is a line source (`source_conf`), so every member's
confirmation of a later slot extends it (`lineInv_all`, the third clause); two of one slot are
compatible (Lemma 32).

Roots name blocks until `tAwakeEnd`: the bundle `PartAHyps` carries the premise at the phase's
end; the conclusion holds at every slot whose support cutoff of the slot after next is at most
`tAwakeEnd`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: once every lock made before the fast block's round has expired, the honest chain does
not switch again. -/
theorem confirmations_chain_after_old_locks (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1) :
    ∀ s : ℕ, M.supportCutoff S.C (s + 2) ≤ tAwakeEnd →
      ConfirmationsChainOn M S A x (roundMembers M S A x) (r * S.C.R + S.C.k) s := by
  have hk := S.C.k_ge_two
  intro s hE σ σ' w w' C C' h1 h2 h3 hw hw' hC hC'
  have P := (PartAHyps.of_tick M F U) R E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird hAwake hActive
    hCommittees hAnchor hOld hv hUpdate hFast hL (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hE)
  have hE1 : ∀ σ'' : ℕ, σ'' ≤ s → M.supportCutoff S.C (σ'' + 1) ≤ tAwakeEnd :=
    fun σ'' h => le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hE
  refine ⟨fun hlt => ?_, fun heq => ?_⟩
  · have hsrc := P.source_conf M F R E U (σ := σ) h1 hw (hE1 σ (by omega)) hC (ancestorEq_refl C)
    exact (P.lineInv_all M F R E hNet hSkew hRedeliver Sy hΔs U Fx σ' (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hE) σ C
      hsrc (by omega)).2 w' (P.memberU M F U (by omega) hw' (hE1 σ' h3)) C' hC'
  · subst heq
    have hu1 := P.memberU M F U (s := σ) (by omega) hw (hE1 σ h3)
    have hu2 := P.memberU M F U (s := σ) (by omega) hw' (hE1 σ h3)
    have htk : ∀ u : V, u ∈ updaterAt M S A x σ →
        x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) ≤ ((tAwakeEnd : ℕ) : ℝ) := by
      intro u hu
      obtain ⟨k, hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hu
      rw [(tickStep_eq_of_lbl M) x E hk']
      have ht := (E.tick_active _ u _ hk').2.2
      have hsk := hSkew
      have hA0 := E.ahead_nonneg
      have hB0 := E.behind_nonneg
      have hΔ := one_le_Δ S
      have h12 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S
        (σ + 1)
      have h22 : M.supportCutoff S.C (σ + 1 + 1) ≤ tAwakeEnd := le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hE
      have hc : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) + Δ S ≤ ((tAwakeEnd : ℕ) : ℝ) := by
        exact_mod_cast (show M.supportCutoff S.C (σ + 1) + Δ S ≤ tAwakeEnd by omega)
      linarith
    exact (lem32_saved_confirmations_compatible_state M F U) S A x R GST σ w w' C C' E hNet hSkew hRedeliver Sy hΔs
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (max_le (htk w hu1) (htk w' hu2)) hRoots) (P.gstSync M F U (s := σ) (by omega)).2.1 hu1 hu2 hC hC'

/-- **A7c, the frame of an honest validator relative to the late family.** The proof; the audited
statement is in `Statements/Executions/Lemma89Statements.lean`. The update of `v` at the action time
is an outcome `(n', sent)` of `v`'s tick there with `L` among the fast blocks of `n'` (template A2),
without A2's hypothesis that `v` has been awake since the duty window's start of slot `r * R + 1`:
`hAwake`, `hAnchor` and `hv` give it, as for `fast_block_base`'s twin. Why: every block of the
family is a line source of a slot at most `s` (`family_source`), and `frame_source_at`.

Roots name blocks until `M.supportCutoff S.C (s + 2)`: the bundle `PartAHyps` is built with its end
time `M.supportCutoff S.C (s + 2)`, the latest time its kit reads here.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: once the old locks have expired, every honest validator's finality gadget lets it follow
every block the honest chain has confirmed since. -/
theorem frame_at_time_relative_to_late_family (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ s t : ℕ) (v w : V)
      (L : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 2)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (hs : r * S.C.R + S.C.k ≤ s) (hts : M.voteTime S.C (s + 1) ≤ t)
    (ht : t ≤ M.supportCutoff S.C (s + 2)) (hEnd : M.supportCutoff S.C (s + 2) ≤ tAwakeEnd)
    (hw : w ∉ A.corruptedAtTime x t) :
    ∀ C : Block V, FastFamilyFrom M S A x (r * S.C.R + S.C.k) L (s + 1) C →
      (M.fg_to_ac (x.stateBefore t w)).fc_root.compatible C = true ∧
      ((M.fg_to_ac (x.stateBefore t w)).fc_root.AncestorEq C →
        ∃ W ∈ (M.fg_to_ac (x.stateBefore t w)).tree,
          W ∈ (M.fg_to_ac (x.stateBefore t w)).viable_heads ∧ C.AncestorEq W) ∧
      (x.stateBefore t w).finalized.compatible C = true := by
  have hk := S.C.k_ge_two
  have P := (PartAHyps.of_tick M F U) R E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST
    (hThird.mono (by exact_mod_cast hEnd))
    (fun i u hi hg hc => hAwake i u (le_trans hi (by exact_mod_cast hEnd)) hg hc)
    (fun s' h1 h2 u hu => hActive s' h1 (le_trans h2 hEnd) u hu)
    (hCommittees.mono M hEnd) hAnchor hOld hv hUpdate hFast hL ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))
  intro C hC
  obtain ⟨μ, hμ, hsrc⟩ := P.family_source M F R E U (show r * S.C.R + 1 ≤ s + 1 by omega)
    ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hC
  exact P.frame_source_at M F R E hNet hSkew hRedeliver Sy hΔs U Fx (P.lineInv_upto M F R E hNet hSkew hRedeliver Sy hΔs U Fx le_rfl)
    (by omega) le_rfl hts ht hw hsrc (by omega)

/-- **A7d, the chain step's frame conditions relative to the late family.** The proof; the audited
statement is in `Statements/Executions/Lemma89Statements.lean`. The update of `v` at the action time
is an outcome `(n', sent)` of `v`'s tick there with `L` among the fast blocks of `n'` (template A2),
without A2's hypothesis that `v` has been awake since the duty window's start of slot `r * R + 1`:
`hAwake`, `hAnchor` and `hv` give it, as for `fast_block_base`'s twin. Why: every block of the
family is a line source of a slot at most `s` (`family_source`), and `stepFrame_source`.

Roots name blocks until `tAwakeEnd`: the bundle `PartAHyps` is built with its end time `tAwakeEnd`; the
third conjunct of `StepFrameAt` is read at each member's tick to the support cutoff of slot `s + 2`,
which `hEndTick` places at a real time at most `tAwakeEnd`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: every member's vote and update of the next slot can follow every block the honest chain
has confirmed since the old locks expired. -/
theorem stepFrame_relative_to_late_family (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ s : ℕ) (v : V) (L : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (hs : r * S.C.R + S.C.k ≤ s) (hEnd : M.supportCutoff S.C (s + 2) ≤ tAwakeEnd)
    (hEndTick : ∀ (w : V) (k : ℕ), x.lbl k = Event.tick w (M.supportCutoff S.C (s + 2)) →
      x.time k ≤ tAwakeEnd) :
    ∀ w ∈ Hon M S A x (s + 1), ∀ C : Block V,
      FastFamilyFrom M S A x (r * S.C.R + S.C.k) L (s + 1) C →
        StepFrameAt M S A x C s w := by
  have hk := S.C.k_ge_two
  intro w hw C hC
  have P := (PartAHyps.of_tick M F U) R E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird hAwake hActive
    hCommittees hAnchor hOld hv hUpdate hFast hL
    (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd)
  obtain ⟨μ, hμ, hsrc⟩ := P.family_source M F R E U (show r * S.C.R + 1 ≤ s + 1 by omega)
    ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega) |>.trans hEnd) hC
  exact P.stepFrame_source_of_tick M F R E hNet hSkew hRedeliver Sy hΔs U Fx
    (P.lineInv_upto M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEnd) (by omega) hEnd (Finset.mem_sdiff.1 hw).2
    (hEndTick w) hsrc (by omega)

/-- **A8b, the chain and lock invariants for the late family.** The proof; the audited statement is
in `Statements/Executions/Lemma89Statements.lean`. The update of `v` at the action time is an
outcome `(n', sent)` of `v`'s tick there with `L` among the fast blocks of `n'` (template A2),
without A2's hypothesis that `v` has been awake since the duty window's start of slot `r * R + 1`:
`hAwake`, `hAnchor` and `hv` give it, as for `fast_block_base`'s twin. Why: every block of the
family at slot `s` is a line source of a slot before `s` (`family_source`, then `lineInv_all`);
every live lock of a member at the vote time of slot `s + 1` is of a slot at least
`s + 1 − k ≥ r * R + k`, on its holder's confirmation of that slot (`late_locks_on_family`).

Roots name blocks until `tAwakeEnd`: the bundle `PartAHyps` carries the premise at the phase's
end; the conclusion holds at every slot whose support cutoff of the slot after next is at most
`tAwakeEnd`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: once every lock older than the fast block's round has expired and every live lock is of
a slot after the last switch, the honest chain is one line, every honest vote, live lock and
confirmation on it. -/
theorem fast_line_invariant_late_family (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1) :
    ∀ s : ℕ, r * S.C.R + 2 * S.C.k - 1 ≤ s → M.supportCutoff S.C (s + 2) ≤ tAwakeEnd →
      ChainInvFor M S A x (Hon M S A x s)
        (FastFamilyFrom M S A x (r * S.C.R + S.C.k) L s) s ∧
      ∀ u ∈ Hon M S A x s,
        LiveLocksOnFamilyAt M S A x
          (FastFamilyFrom M S A x (r * S.C.R + S.C.k) L s) s u := by
  have hk := S.C.k_ge_two
  intro s hs hE
  have P := (PartAHyps.of_tick M F U) R E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird hAwake hActive
    hCommittees hAnchor hOld hv hUpdate hFast hL (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hE)
  refine ⟨fun C hC => ?_, fun u hu => P.late_locks_on_family M F R E U hs hu⟩
  obtain ⟨μ, hμ, hsrc⟩ := P.family_source M F R E U (show r * S.C.R + 1 ≤ s by omega)
    (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hE) hC
  exact (P.lineInv_all M F R E hNet hSkew hRedeliver Sy hΔs U Fx s hE μ C hsrc hμ).1

/-! ## A6 and the assembly of part A -/

/-- **A6, a certificate at a height greater than `H₂` names an entry of the honest chain from slot
`r * R`.** The proof, from the skeleton (`skeleton_89b/SkeletonPartA.lean`); the audited statement
is in `Statements/Executions/Lemma89Statements.lean`. Why: Lemma 83 with `s₀ := r * R` and
`t₀ := aR M S r`, its `hAgree` from Lemma 82, its `hAdvQ` from `hThird`, its `hOld` in the honest-at
form.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: once the fast block's round has acted, every certificate at a height greater than the
old evidence is honest and on the chain the fast block started. -/
theorem certificate_on_fast_line (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (tAwakeEnd r H₂ j : ℕ) (w : V) (B T : Block V)
    (h : Height)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hj : x.time j ≤ tAwakeEnd) (hEnd : aR M S r ≤ tAwakeEnd)
    (hB : B ∈ (x.st j w).tree) (hJ : ProgressCertOn M B h T) (hH : H₂ < h) :
    ∃ E : Block V, OnHonestChain M S A x (r * S.C.R) E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = h ∧ T.root = E.root := by
  -- Lemma 83's argument at the real honesty time `max (x.time j) (aR M S r)`; the old attestations'
  -- bound is carried from the senders honest at `aR M S r` to those honest at that later real time
  -- (honesty up to a later time implies honesty up to an earlier one); no step at that time is asked
  have hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time j) (aR M S r)) :=
    fun X hX => by
      have h1 := (hThird.mono (max_le hj (by exact_mod_cast hEnd))) X hX
      have h2 := (GoldilocksCorrectness.Statements.Routines.lem65b_quorum_threshold (V := V)).2
      omega
  have hOld' : OldAttestationsAtMostHonestAt M S A x (aR M S r) (max (x.time j) ((aR M S r : ℕ) : ℝ)) H₂ := by
    intro i t v a hl ht hHk hsent
    refine hOld i t v a hl ht ?_ hsent
    rw [Activity.not_mem_corruptedAtTime] at hHk ⊢
    intro i' hi' hc
    exact hHk i' (le_trans hi' (le_max_right _ _)) hc
  obtain ⟨s_a, Eb, -, hE, hEe, hEh, hEr⟩ := (one_certificate_greater_than_threshold_at_real M F Fx) S A x R E
    (r * S.C.R) (aR M S r) H₂ j w B T h (max (x.time j) (aR M S r)) (le_max_left _ _) hAdvQ
    ((lem82_honest_attestations_on_chain M F U) S A x R (r * S.C.R) E) hOld' hB hJ hH
  exact ⟨Eb, ⟨s_a, hE⟩, hEe, hEh, hEr⟩

/-- **Part A, one line from the first honest fast block at the height after the old evidence.** The
proof, from the skeleton (`skeleton_89b/SkeletonPartA.lean`); the audited statement is in
`Statements/Executions/Lemma89Statements.lean`. The update of `v` at the action time is an outcome
`(n', sent)` of `v`'s tick there with `L` among the fast blocks of `n'` (template A2), without A2's
hypothesis that `v` has been awake since the duty window's start of slot `r * R + 1`: `hAwake`,
`hAnchor` and `hv` give it, as for `fast_block_base`'s twin. Why: A8a, A8b and A6.

Roots name blocks until `tAwakeEnd`: the bound of A8a and A8b, whose conclusions hold at every
slot whose support cutoff of the slot after next is at most `tAwakeEnd`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: once one honest validator has fast-confirmed a block one height after everything the
honest validators had attested, no honest validator ever votes, locks or confirms off that block's
chain, the honest chain is one line once the older locks have expired, and every later certificate
is on its line. -/
theorem lem89L_one_line_from_fast_block (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1) :
    (∀ s : ℕ, r * S.C.R + 1 ≤ s → M.supportCutoff S.C (s + 2) ≤ tAwakeEnd →
      HonestChainExtends M S A x (Hon M S A x s) L s) ∧
    (∀ s : ℕ, r * S.C.R + 2 * S.C.k - 1 ≤ s → M.supportCutoff S.C (s + 2) ≤ tAwakeEnd →
      ChainInvFor M S A x (Hon M S A x s)
        (FastFamilyFrom M S A x (r * S.C.R + S.C.k) L s) s ∧
      ∀ u ∈ Hon M S A x s,
        LiveLocksOnFamilyAt M S A x (FastFamilyFrom M S A x (r * S.C.R + S.C.k) L s) s u) ∧
    (∀ (j : ℕ) (w : V) (B T : Block V) (h : Height), x.time j ≤ tAwakeEnd →
      B ∈ (x.st j w).tree → ProgressCertOn M B h T → H₂ < h →
      ∃ E : Block V, OnHonestChain M S A x (r * S.C.R) E ∧ IsEntry M S.C E ∧
        (M.chainStateOf S.C E).h = h ∧ T.root = E.root) :=
  ⟨(fast_line_invariant_L M F U Fx) S A x R GST tGAT tAwakeEnd r H₂ v L E hNet hSkew hRedeliver Sy hΔs
      hRoots hParent hGST hThird hAwake hActive hCommittees hAnchor hOld hv n' sent hUpdate hFast hL,
    (fast_line_invariant_late_family M F U Fx) S A x R GST tGAT tAwakeEnd r H₂ v L E hNet hSkew hRedeliver Sy hΔs
      hRoots hParent hGST hThird hAwake hActive hCommittees hAnchor hOld hv n' sent hUpdate
      hFast hL,
    fun j w B T h hj hB hJ hH =>
      (certificate_on_fast_line M F U Fx) S A x R tAwakeEnd r H₂ j w B T h E hThird hOld hj hEnd hB
        hJ hH⟩

end GoldilocksCorrectness.Record.Proofs.Executions

