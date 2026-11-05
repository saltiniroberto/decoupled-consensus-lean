module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainAfterHealingStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.PhaseKitStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.PhaseDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.LockStatementsForkChoice
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealingStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma79
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma45
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma26
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ConfirmationSteps
public import GoldilocksCorrectness.Statements.Executions.HonestChainAfterHealingStatements
public import GoldilocksCorrectness.Statements.Executions.PhaseKitStatements
public import GoldilocksCorrectness.Statements.Executions.PhaseDefs
public import GoldilocksCorrectness.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Statements.Routines.LockStatements
public import GoldilocksCorrectness.Statements.Executions.HealingStatements
public import GoldilocksCorrectness.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Proofs.Executions.Lemma79
public import GoldilocksCorrectness.Proofs.Executions.Lemma45
public import GoldilocksCorrectness.Proofs.Executions.Lemma26
public import GoldilocksCorrectness.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Proofs.Executions.ConfirmationSteps
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# PhaseChain, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/PhaseChain.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: the phase step, the re-base of the chain
invariant at a common fork-choice root, and Lemma 45b, an honest Goldfish vote extends a lock its
voter holds. The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  dutyWindowStart_succ_le_slotStart dutyWindowStart_succ_le_supportCutoff lockDeadline_injective
  one_le_Δ slotStart_eq slotStart_mono slot_eq_of_mem supportCutoff_eq supportCutoff_lt_of_lt
  supportCutoff_succ_le viewFreeze_eq voteTime_cast voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both)

open GoldilocksCorrectness.Proofs.Routines (tick_emits_vote)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (votesOnceInPoolFor_of_keepsVotes wake_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)



open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated CountedVotes
  LocksRevoked VoterTreeAt)

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
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible awake_since_record_awake)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; this rule, local to the file, proves it at once
--. No statement and no proof term
-- changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## The phase step -/

/-- **The phase step.** The proof; the audited statement is in
`Statements/Executions/PhaseChainStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s'`: the slot of the step;
- `Hon`: the voters of slot `s'`; `Hon'`: the members of slot `s' + 1`; `𝓒`: the family.

Roots name blocks until `M.supportCutoff S.C (s' + 1)`: the proof reads `lem89s_chain_step` at slot
`s'`, whose bound is that time.

Read aloud: inside the phase, the honest chain grows by the confirmations of slot `s'`, each slot's
members awake and honest only through their own slot's update. -/
theorem lem89s_phase_step (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s' : ℕ) (Hon Hon' : Finset V) (𝓒 : Block V → Prop)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s' + 1)))
    -- roots name blocks also up to the real time of every validator's tick to a clock value at most the
    -- support cutoff of slot `s' + 1`
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x) (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s')
    (hHon : Hon ⊆ honestActiveAt M S A x s')
    (hHon' : Hon' ⊆ honestActiveAt M S A x (s' + 1))
    (hSub : Hon' ⊆ Hon)
    (hCommittee : (S.P.committee s').card < 2 * (S.P.committee s' ∩ Hon).card)
    (hCommittee' : (S.P.committee (s' + 1)).card < 2 * (S.P.committee (s' + 1) ∩ Hon').card)
    (hInv : ChainInvFor M S A x Hon 𝓒 s')
    (hLocks : ∀ u ∈ Hon, LiveLocksOnFamilyAt M S A x 𝓒 s' u)
    (hStep : ∀ C : Block V, (𝓒 C ∨ ∃ v ∈ Hon',
        (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C) →
      ∀ w ∈ Hon', StepFrameAt M S A x C s' w) :
    ChainInvFor M S A x Hon' (fun C => 𝓒 C ∨ ∃ v ∈ Hon', ∃ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' ∧
      C.AncestorEq C') (s' + 1) ∧
    ∀ u ∈ Hon', LiveLocksOnFamilyAt M S A x (fun C => 𝓒 C ∨ ∃ v ∈ Hon', ∃ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' ∧
      C.AncestorEq C') (s' + 1) u := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  -- the updaters of slot `s'`: every honest active validator of slot `s' + 1` is one
  have hUpd : Hon' ⊆ updaterAt M S A x s' :=
    fun u hu => (honestActiveAt_succ_subset_updaterAt M F U) S A s' R E hSkew (hHon' hu)
  refine ⟨(lem89s_chain_step M F U) S A x R GST s' Hon Hon' Hon' 𝓒 E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick
    hParent hOwner hGST hHon hHon' hUpd subset_rfl hCommittee hCommittee' hInv
    (fun u hu => Or.inl (hSub hu)) hLocks
    (fun C hC v hv C' hC' => (hInv C hC).2.2 v (hSub hv) C' hC') hStep, ?_⟩
  -- the lock invariant at every member of `Hon'`: its window from the duty window's start of slot `s' + 2`
  -- up to its tick to the vote time of slot `s' + 2`, inside its window as an honest active validator of slot `s' + 1`
  intro u hu
  have hwin := (honestActiveAt_window M F) S A (s' + 1) u E (hHon' hu)
  have hc2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' + 1 + 1)
  have hvt1 : 1 ≤ M.voteTime S.C (s' + 2) := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s' + 2)
    omega
  have hds : duty_window_start S.C (s' + 1) ≤ ((M.dutyWindowStart S.C (s' + 2) : ℕ) : ℤ) := by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart
      M.toSlotLayout F.sched U) S (s' + 1)
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S
      (show s' + 1 ≤ s' + 2 by omega)
    have h3 : ((M.dutyWindowStart S.C (s' + 1) : ℕ) : ℤ) ≤ ((M.dutyWindowStart S.C (s' + 2) : ℕ) : ℤ) := by
      exact_mod_cast h2
    exact le_trans h1 h3
  have hdsR := duty_window_start_real S (s' + 1)
  have hdle := (duty_window_start_le_real M F U) S (s' + 1)
  have hwin' : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s' + 1)) (M.voteTime S.C (s' + 2)) := by
    refine (mem_activeThroughoutToTick_of_le_end_int M) x R E hvt1 ?_ ?_ hwin
    · have h1 : ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) + 3 * Δ S ≤ ((M.voteTime S.C (s' + 2) : ℕ) : ℝ) := by
        have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' + 1)
        have h22 : M.voteTime S.C (s' + 2) = M.voteTime S.C (s' + 1) + 4 * Δ S :=
          (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S (s' + 1)
        exact_mod_cast (show M.supportCutoff S.C (s' + 1) + 3 * Δ S ≤ M.voteTime S.C (s' + 2) by omega)
      have h2 : ((M.dutyWindowStart S.C (s' + 1) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) := by
        exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_le_supportCutoff M.toSlotLayout F.sched U) S
          (by omega)
      have h3 := (duty_window_start_le_real M F U) S (s' + 1)
      have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
      linarith
    · have h4 : ((M.supportCutoff S.C (s' + 1 + 1) : ℕ) : ℝ) = ((M.voteTime S.C (s' + 2) : ℕ) : ℝ) + Δ S := by
        rw [hc2]; push_cast; ring
      linarith
  have hwin'' : u ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (s' + 2) : ℕ) : ℤ) (M.voteTime S.C (s' + 2)) := by
    exact Activity.mem_activeThroughoutToTick_of_le hds hwin'
  exact (liveLocksOnFamilyAt_of_locksRevoked M F U) S A x R E _ _ u <|
    (liveLocksOnFamilyAt_step M F U) S A x R 𝓒 _ s' u E hSkew hwin'' (fun C hC => Or.inl hC)
    (fun C hC => Or.inr ⟨u, hu, C, hC, ancestorEq_refl C⟩) (hLocks u (hSub hu))

/-! ## The re-base: the kit -/

/-- A validator awake and honest from the duty window's start of slot `s` up to its own tick to the
vote time of slot `s` (`A.activeThroughoutToTick`) ticks to that vote time at a step `k'`, and that tick
starts from a state awake since the duty window's start of slot `s` or earlier: the reader's first
conjunct gives the tick, `tickInput_awakeSince_of_mem_activeThroughoutToTick` the wake test (the duty
window's start is before the vote time).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, its run facts, its environment
  facts; `s`: the slot; `u`: the validator.

Read aloud: a validator active from the duty window's start of slot `s` to its tick to the vote time
ticks to the vote time from a state awake since that duty window's start. -/
theorem tick_and_wake_of_tick_window (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (u : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- `u` is awake and honest from the duty window's start of slot `s` up to its tick to the vote time
    (hu : u ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.voteTime S.C s)) :
    ∃ k' : ℕ, x.lbl k' = Event.tick u (M.voteTime S.C s) ∧
      ∃ τ : Time, (x.tickInput u (M.voteTime S.C s)).awakeSince = some τ ∧
        τ ≤ duty_window_start S.C s := by
  have hΔ := one_le_Δ S
  have hk : 2 ≤ S.C.k := S.C.k_ge_two
  have hvt : M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hdR := duty_window_start_real S s
  have hvR : ((M.voteTime S.C s : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s : ℝ) + (Δ S : ℝ) := by
    rw [hvt, (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
    push_cast; ring
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hkR : (2 : ℝ) ≤ (S.C.k : ℝ) := by exact_mod_cast hk
  have hΔk : (Δ S : ℝ) ≤ 4 * (Δ S : ℝ) * (S.C.k : ℝ) := by nlinarith
  obtain ⟨k', hl, -⟩ := Activity.mem_activeThroughoutToTick.1 hu
  have hdw : duty_window_start S.C s < ((M.voteTime S.C s : ℕ) : ℤ) := by
    have h : ((duty_window_start S.C s : ℤ) : ℝ) < (((M.voteTime S.C s : ℕ) : ℤ) : ℝ) := by
      push_cast; rw [hdR, hvR]; linarith
    exact_mod_cast h
  exact ⟨k', hl, (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hu hdw⟩

/-- An honest active validator of slot `s` (`honestActiveAt`), with the two clock bounds together less
than one delay, is awake and honest from the duty window's start of slot `s` up to its own tick to the
vote time of slot `s`: `activeAt`'s window to the support cutoff of slot `s + 1` contains that tick's
window (`mem_activeThroughoutToTick_of_inside`; the duty window's start plus `ΔClockBehind` is before
the vote time minus `ΔClockAhead`, and the vote time plus `ΔClockBehind` before the support cutoff
minus `ΔClockAhead`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, its run facts, its environment
  facts; `s`: the slot; `u`: the validator.

Read aloud: an honest active validator of slot `s` is active from the slot's duty window's start to
its tick to the slot's vote time. -/
theorem voteTime_tick_window_of_honestActiveAt (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (u : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the two clock bounds together are less than one delay
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- `u` is an honest active validator of slot `s`
    (hu : u ∈ honestActiveAt M S A x s) :
    u ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.voteTime S.C s) := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hk : 2 ≤ S.C.k := S.C.k_ge_two
  have hvt : M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hvR : ((M.voteTime S.C s : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s : ℝ) + (Δ S : ℝ) := by
    rw [hvt, (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
    push_cast; ring
  have hcR : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s : ℝ) + 6 * (Δ S : ℝ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1)]
    push_cast; ring
  have hdR := duty_window_start_real S s
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hkR : (2 : ℝ) ≤ (S.C.k : ℝ) := by exact_mod_cast hk
  have hΔk : (Δ S : ℝ) ≤ 4 * (Δ S : ℝ) * (S.C.k : ℝ) := by nlinarith
  have hw : u ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.supportCutoff S.C (s + 1)) :=
    E.mem_activeThroughoutToTick_of_awakeThroughoutToTick (Finset.mem_sdiff.1 hu).1
  exact (mem_activeThroughoutToTick_of_inside M F) R E (c := M.voteTime S.C s) hw (by omega)
    (by rw [hdR, hvR]; linarith) (by rw [hvR, hcR]; linarith)

/-- An honest member of the committee of slot `s` puts a slot-`s` Goldfish vote on the wire at its
tick to the vote time of slot `s`, at the step `k'` of that tick, when that tick starts from a state
awake since the duty window's start of slot `s` or earlier. The vote is the tick's
(`F.tk.tick_emits_vote`): the tick is at the vote time of its slot, its outcome is awake for the slot
(`tick_clock_validator_awakeSince`), and the state it reads names `u` (`lem11_node_invariant` at the
tick, `u` being outside the adversary set at its own tick, `E.not_mem_corrupted_of_tick`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, its run facts, its environment
  facts; `s`: the slot; `u`: the validator; `k'`: the step of its tick to the vote time.

Read aloud: a committee member of slot `s` whose tick to the vote time starts awake since the duty
window's start puts its slot-`s` Goldfish vote on the wire at that tick. -/
theorem honest_votes_of_window (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (u : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- `u` ticks to the vote time of slot `s` at the step `k'`
    {k' : ℕ} (hl : x.lbl k' = Event.tick u (M.voteTime S.C s))
    -- that tick starts from a state awake since the duty window's start of slot `s` or earlier
    (hAw : ∃ τ : Time, (x.tickInput u (M.voteTime S.C s)).awakeSince = some τ ∧ τ ≤ duty_window_start S.C s)
    (hK : u ∈ S.P.committee s) :
    ∃ (vote : GoldfishVote V), vote.val_index = u ∧ vote.slot = s ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (k' + 1) - x.sent k' := by
  have hΔ := one_le_Δ S
  have hvt : M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s, Nat.mul_add, Nat.mul_one]
  have hslot : M.slot S.C (M.voteTime S.C s) = s := (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (by omega) (by omega)
  have hslot' : S.C.slot ((M.voteTime S.C s : ℕ) : Int) = s := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact hslot
  have hvc : ((M.voteTime S.C s : ℕ) : Int) =
      S.C.t_ (S.C.slot ((M.voteTime S.C s : ℕ) : Int)) + S.C.Δ := by
    rw [hslot']; exact (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U) S s
  have hts := (tickStep_eq_of_lbl M) x E hl
  obtain ⟨τ, hτ, hτle⟩ := hAw
  obtain ⟨n', sent, hrun, -, hsent⟩ := R.tick k' u _ hl
  have hrun' : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput u (M.voteTime S.C s))
      ((M.voteTime S.C s : ℕ) : Int) := by
    unfold Trace.tickInput; rw [hts]; exact hrun
  have hnv : (x.tickInput u (M.voteTime S.C s)).v = u := by
    unfold Trace.tickInput; rw [hts]
    exact (lem11_node_invariant M F S A x R E k' u (E.not_mem_corrupted_of_tick hl)).2.1
  have hT1 := F.tk.tick_clock_validator_awakeSince S.C S.P S.X _ _ n' sent hrun'
  have hWS' : M.awake_since n' (duty_window_start S.C (S.C.slot ((M.voteTime S.C s : ℕ) : Int))) =
      true := by
    simp only [F.rd.awake_since_eq, hT1.2.2, hτ, hslot', decide_eq_true_eq]
    exact hτle
  obtain ⟨h, hh⟩ := F.tk.tick_emits_vote S.C S.P S.X _ _ n' sent hrun' hvc hWS'
    (by rw [hnv, hslot']; exact hK)
  rw [hnv, hslot'] at hh
  refine ⟨⟨u, s, h⟩, rfl, rfl, ?_⟩
  rw [hsent, add_tsub_cancel_left]
  exact Multiset.mem_map.2 ⟨_, Multiset.mem_coe.2 hh, rfl⟩

/-- **The re-base, the votes.** When every member's fork-choice root at its tick to the vote time of slot
`s` is `R`, every slot-`s` vote a member put on the wire at its tick at that vote time is its vote
for a block it holds then that is `R` or a descendant of `R`.

Why: the vote names a block the voter holds, on the chain of its own fork-choice root
(`vote_extends_own_root`), and its validator and slot are the voter's and `s`
(`honest_vote_form`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `Hon`: the members;
  `R`: the common root.

Read aloud: when every member's fork-choice root at its tick to the vote time of slot `s` is `R`, every
member's slot-`s` vote is for a block it holds that is `R` or a descendant of `R`. -/
theorem rebase_votes_clause (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Run : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (Hon : Finset V) (R : Block V)
    (hRoot : ∀ w ∈ Hon, M.get_fc_root (x.tickInput w (M.voteTime S.C s)) = R) :
    ∀ u ∈ Hon, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s)).tree,
        vote = GoldfishVote.mk u s H_u.root ∧ R.AncestorEq H_u := by
  intro u hu vote hSend
  obtain ⟨H, hHT, hhead, hroot⟩ := (vote_extends_own_root M F) S A x Run E s u vote hSend
  obtain ⟨hvi, hvs⟩ := (honest_vote_form M F U) S A x Run E s u vote hSend
  rw [hRoot u hu] at hroot
  refine ⟨H, hHT, ?_, hroot⟩
  cases vote
  simp only [GoldfishVote.mk.injEq]
  exact ⟨hvi, hvs, hhead⟩

/-- **The re-base, the voters as a function.** When every member is awake and honest from the duty
window's start of slot `s` up to its own tick to the vote time of slot `s`
(`A.activeThroughoutToTick`), and every member's fork-choice root at its tick to the vote time of slot `s` is `R`,
then some `H : V → Block V` names, for every member `u` of the committee of slot `s`, the block of
the slot-`s` vote `u` put on the wire at its tick at that vote time, a block `u` holds then that
is `R` or a descendant of `R`.

Why: every such member ticks to the vote time from a state awake since the duty window's start
(`tick_and_wake_of_tick_window`) and votes there (`honest_votes_of_window`), and `rebase_votes_clause`
names the block; `choose`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `Hon`: the members;
  `R`: the common root.

Read aloud: when every member's fork-choice root at its tick to the vote time of slot `s` is `R`, a function
names, for every committee member among the members, the block of its slot-`s` vote, held and `R` or
a descendant of `R`. -/
theorem rebase_voters (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Run : RunFacts M S x) (s : ℕ) (Hon : Finset V) (R : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- every member is awake and honest from the duty window's start of slot `s` up to its own tick to
    -- the vote time of slot `s`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.voteTime S.C s))
    (hRoot : ∀ w ∈ Hon, M.get_fc_root (x.tickInput w (M.voteTime S.C s)) = R) :
    ∃ H : V → Block V, ∀ u ∈ S.P.committee s ∩ Hon,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ R.AncestorEq (H u) := by
  have hvote : ∀ u ∈ S.P.committee s ∩ Hon, ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H_u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ R.AncestorEq H_u := by
    intro u hu
    obtain ⟨hK, huH⟩ := Finset.mem_inter.1 hu
    obtain ⟨k', hl, hAw⟩ := (tick_and_wake_of_tick_window M F U) S A x Run s u E (hHon u huH)
    obtain ⟨vote, -, -, hsent⟩ := (honest_votes_of_window M F U) S A x Run s u E hl hAw hK
    obtain ⟨H_u, hHT, hvt, hBH⟩ := (rebase_votes_clause M F U) S A x Run E s Hon R hRoot u huH vote
      ⟨k', hl, hsent⟩
    subst hvt
    exact ⟨H_u, ⟨k', hl, hsent⟩, hHT, hBH⟩
  choose H hH using hvote
  refine ⟨fun u => if h : u ∈ S.P.committee s ∩ Hon then H u h else R, fun u hu => ?_⟩
  simp only [dif_pos hu]
  exact hH u hu

/-- **The lock clause from the votes.** In an execution where every time is reached, corruption is
permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`,
a root names one block among what honest validators hold, a block reaches a validator
only once it holds the parent, and nobody votes in an honest validator's name: if `GST` is at most
the vote time of slot `s`; each member runs the update of slot `s` (`updaterAt`: awake and honest from a tick
at or before the duty window's start of slot `s + 1` up to its own tick to the support cutoff of slot `s + 1`);
the committee of slot `s` has fewer than twice its members in `Hon`; every committee member `u` of `Hon` put on the wire at its tick at the vote
time of slot `s` its slot-`s` vote for `(H u).root`, `H u` a block it holds then that is `B` or a
descendant of `B`; and every member's finalized block at its tick to the support cutoff of slot `s + 1` is
compatible with `B` — then every lock entry a member's revocation of slot `s + 1` leaves, run from the state
its tick to the vote time of slot `s + 1` starts from (rule R3), is on a block compatible with `B`.

Why: `w`'s finalized block `F` at its tick input to the vote time of slot `s + 1` is an ancestor of its
finalized block at its tick input to the support cutoff of slot `s + 1`, or it, so it is compatible with `B` (both
ticks are inside `w`'s reader of slot `s`, the first before the second). When `B` is
`F` or an ancestor of `F`, every entry left is on a block of `w`'s frame tree, which descends from
`F`. When `F` is an ancestor of `B`, every vote of a committee member of `Hon` reached `w`, held
early, by the support cutoff of slot `s` (Lemma 12 in the step form, `lem12_honest_vote_delivered_until_of_steps`,
`w` active at every step from the sync fact's read time to its tick to the support cutoff of slot `s`, by its
reader of slot `s`; each voter's holder window and its honesty at `w`'s tick by the voter's own reader), so it is the member's only slot-`s` vote in
`w`'s pool at its tick input to the vote time of slot `s + 1`, resolving to a block of `w`'s frame tree on `B`'s chain; Lemma 5 concludes.

Read aloud: a majority of honest votes for `B`'s chain at slot `s` leaves no honest lock
conflicting with `B` after the revocation of slot `s + 1`, whatever the locks were before.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot; `Hon`: the members; `B`: the block; `H`: the block of
  each committee member's vote.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C s`: the proof
reads Lemma 12 at slot `s` at the receiver's own tick to that cutoff. -/
theorem locks_clause_of_votes (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hon : Finset V) (B : Block V)
    (H : V → Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x) (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- each member runs the update of slot `s`: it ticks to the support cutoff of slot `s + 1`, active up to that tick
    -- from a tick at or before the duty window's start of slot `s + 1`
    (hHonUpd : ∀ v ∈ Hon, v ∈ updaterAt M S A x s)
    (hCommittee : (S.P.committee s).card < 2 * (S.P.committee s ∩ Hon).card)
    (hVotes : ∀ u ∈ S.P.committee s ∩ Hon,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ B.AncestorEq (H u))
    -- every member's finalized block at its tick to the support cutoff of slot `s + 1` is compatible with `B`
    (hF : ∀ v ∈ Hon,
        (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.compatible B = true) :
    ∀ w ∈ Hon, ∀ n' : M.N,
      LocksRevoked M S.P (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) (s + 1) n' →
      ∀ e ∈ M.lockEntries n', e.B.compatible B = true := by
  intro w hw n' hRevoke e he
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hb1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  -- the times
  obtain ⟨hv0, hc0, -, hs1, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
  obtain ⟨hv1, hc1, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hdw1 := duty_window_start_real S (s + 1)
  push_cast at hdw1
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hkm : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have h' : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast at hΔs ⊢; linarith
    exact_mod_cast h'
  have hm1 := le_max_left (Δ S) Δs
  have hΔ1R : ((Δ S : ℕ) : ℝ) ≤ ((max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hm1
  have hkmR : ((max (Δ S) Δs : ℕ) : ℝ) + 3 * Δ S < 4 * Δ S * S.C.k := by exact_mod_cast hkm
  have hvR : ((M.voteTime S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 5 * Δ S := by
    rw [hv1, hs1, hss]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 6 * Δ S := by
    rw [hc1, hs1, hss]; push_cast; ring
  -- `w`'s ticks to the vote time and to the support cutoff of slot `s + 1`, inside its reader of slot `s`
  have hw' : w ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.voteTime S.C (s + 1)) :=
    (mem_activeThroughoutToTick_of_inside M F) R E (hHonUpd w hw) (by omega)
      (by rw [hdw1, hvR]; linarith) (by rw [hvR, hc1R]; linarith)
  obtain ⟨kc, hkc, -⟩ := Activity.mem_activeThroughoutToTick.1 hw'
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 (hHonUpd w hw)
  have hkc2 := (E.tick_active kc w _ hkc).2.2
  have hk'1 := (E.tick_active k' w _ hk').2.1
  have hkck' : kc ≤ k' := ((lt_of_time_lt M) x R (by rw [hvR] at hkc2; rw [hc1R] at hk'1; linarith)).le
  have hkcs : x.tickStep w (M.voteTime S.C (s + 1)) = kc := (tickStep_eq_of_lbl M) x E hkc
  have hk's : x.tickStep w (M.supportCutoff S.C (s + 1)) = k' := (tickStep_eq_of_lbl M) x E hk'
  -- `w`'s tick to the support cutoff of slot `s`, and its window from Lemma 12's read time to it
  obtain ⟨kR, hkR, hkRw⟩ := (updater_reader_gives_core_window M F U) x R E hΔs hSkew (hHonUpd w hw)
  have hkRs : x.tickStep w (M.supportCutoff S.C s) = kR := (tickStep_eq_of_lbl M) x E hkR
  -- `w`'s finalized block at its tick input to the vote time of slot `s + 1` is compatible with `B`: an ancestor of
  -- its finalized block at its tick input to the support cutoff of slot `s + 1`, or it
  have hFF : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq
      (x.tickInput w (M.supportCutoff S.C (s + 1))).finalized := by
    unfold Trace.tickInput; rw [hkcs, hk's]; exact (F_ancestorEq_of_le M F) x R E w hkck'
  have hFc := GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible hFF (hF w hw)
  rcases (compatible_iff _ _).1 hFc with hFB | hBF
  swap
  · -- `B` is the finalized block or an ancestor of it: every entry left descends from it
    have heT := GoldilocksCorrectness.Record.Proofs.Routines.revoke_locks_entry_mem_tree hb1 hRevoke e he
    exact (compatible_iff _ _).2 (Or.inr (ancestorEq_trans hBF
      (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 heT).2))
  -- the finalized block is an ancestor of `B`, or `B`: Lemma 5 against the members' votes, held at `w`'s tick input
  -- to the vote time of slot `s + 1` (Lemma 12 in the step form)
  have hHeld : ∀ u ∈ S.P.committee s ∩ Hon, HeldEarlyVoteFor M S.C
      (x.tickInput w (M.voteTime S.C (s + 1))) s (H u) u := by
    refine (lem12_honest_vote_delivered_until_of_steps M F U) S A x R GST s (M.voteTime S.C (s + 1))
      (S.P.committee s ∩ Hon) H w E hNet hSkew hRedeliver Sy hΔs ?_ hParent hOwner hGST (by omega) kc hkc ?_ ?_
      ⟨kR, hkR, hkRw⟩ ?_
    · rw [hkRs]; exact hRoots kR w _ hkR le_rfl
    · intro u hu
      -- the voter is outside the adversary set at `w`'s tick to the vote time of slot `s + 1`: its reader of slot `s`
      -- reaches past every honest tick to that vote time
      have hX := (outside_at_honest_ticks_of_mem_activeThroughoutToTick M F) x R E
        (hHonUpd u (Finset.mem_inter.1 hu).2) (c := M.voteTime S.C (s + 1)) (by rw [hvR, hc1R]; linarith)
      have hnc := (not_mem_corrupted_tickStep_of_outside_at_honest_ticks_of_lbl M F) x E hkc hX
      rw [hkcs] at hnc
      exact ⟨(Finset.mem_inter.1 hu).1, hnc, (hVotes u hu).1, (hVotes u hu).2.1⟩
    · intro u hu
      exact (holder_window_of_updater_reader M F U) x R E hΔs hSkew hGST (hHonUpd u (Finset.mem_inter.1 hu).2)
    · intro u hu
      exact ancestorEq_trans hFB (hVotes u hu).2.2
  have hHalf := ((counting_of_committee_majority_st M F) S A x R E s kc Hon w hCommittee).1
  refine ((GoldilocksCorrectness.Record.Statements.Routines.lem5_revoke_locks_entries_compatible F) B
    (S.P.committee s ∩ Hon) hb1 (fun u hu => ?_) (by rw [Nat.add_sub_cancel]; exact hHalf) hRevoke e he).2
  obtain ⟨hp, -, hHΦ, ⟨y, hy, -⟩, huniq⟩ := hHeld u hu
  exact ⟨_, hp, rfl, ⟨y, hy⟩, ⟨H u, hHΦ, rfl, (hVotes u hu).2.2⟩, huniq⟩

/-- **The re-base, the live locks.** In an execution where every time is reached, corruption is
permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`,
a root names one block among what honest validators hold, a block reaches a validator
only once it holds the parent, and nobody votes in an honest validator's name: if `GST` is at most
the vote time of slot `s`; every member is awake and honest from a tick at or before the duty window's start of
slot `s` up to its own tick to the vote time of slot `s`, and runs the update of slot `s`; the committee of slot `s`
has fewer than twice its members in `Hon`; every member's fork-choice root at its tick to the vote time of slot `s` is `R`;
and every member's finalized block at its tick to the support cutoff of slot `s + 1` is compatible with `R` —
then every lock entry a member's revocation of slot `s + 1` leaves is on a block compatible with
`R`.

Why: every committee member of `Hon` voted at slot `s` for a block it held on `R`'s chain
(`rebase_voters`, from `hHonVote`), and `locks_clause_of_votes` concludes (from `hHonUpd`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot; `Hon`: the members; `R`: the common root.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C s`: the proof
reads `locks_clause_of_votes` at slot `s`, whose bound is that one.

Read aloud: when every member's fork-choice root at its tick to the vote time of slot `s` is `R` and every
member's finalized block is compatible with `R`, every lock entry a member's revocation of slot
`s + 1` leaves is compatible with `R`. -/
theorem rebase_locks_clause (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Run : RunFacts M S x) (GST s : ℕ) (Hon : Finset V) (R : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x) (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- every member is awake and honest from the duty window's start of slot `s` up to its own tick to
    -- the vote time of slot `s`
    (hHonVote : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.voteTime S.C s))
    -- each member runs the update of slot `s`: it ticks to the support cutoff of slot `s + 1`, active up to that tick
    -- from a tick at or before the duty window's start of slot `s + 1`
    (hHonUpd : ∀ v ∈ Hon, v ∈ updaterAt M S A x s)
    (hCommittee : (S.P.committee s).card < 2 * (S.P.committee s ∩ Hon).card)
    (hRoot : ∀ w ∈ Hon, M.get_fc_root (x.tickInput w (M.voteTime S.C s)) = R)
    -- every member's finalized block at its tick to the support cutoff of slot `s + 1` is compatible with `R`
    (hF : ∀ v ∈ Hon,
        (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.compatible R = true) :
    ∀ w ∈ Hon, ∀ n' : M.N,
      LocksRevoked M S.P (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) (s + 1) n' →
      ∀ e ∈ M.lockEntries n', e.B.compatible R = true := by
  obtain ⟨H, hH⟩ := (rebase_voters M F U) S A x Run s Hon R E hHonVote hRoot
  exact (locks_clause_of_votes M F U) S A x Run GST s Hon R H E hNet hSkew hRedeliver Sy hΔs hRoots hParent
    hOwner hGST hHonUpd hCommittee hH hF

open Classical in
/-- **The re-base, the confirmations.** Under the execution assumptions of
`rebase_locks_clause`: if `GST` is at most the vote time of slot `s`; every member is awake and
honest from a tick at or before the duty window's start of slot `s` up to its own tick to the vote time of
slot `s`; each member runs the update of slot `s` and is outside the adversary set at every honest
validator's tick to the support cutoff of slot `s + 1`; the committee of slot `s` has fewer than twice its
members in `Hon`; every member's fork-choice root at its tick to the vote time of slot `s` is `R`; and every member's
finalized block at its tick to the support cutoff of slot `s + 1` is compatible with `R` — then every
confirmation of slot `s` a member holds right after that cutoff is `R` or a descendant of `R`.

Why: Lemma 78 at the member, with the committee members of `Hon` as the honest voters, each
voting for a block it holds on `R`'s chain (`rebase_voters`, from `hHonVote`); their honesty at the
member's tick from `hHonTick` (`not_mem_corrupted_tickStep_of_outside_at_honest_ticks`), their holder window
from their reader `hHonUpd` (`holder_window_of_updater_reader`), the roots at the member's own tick from the per-tick `hRoots`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot; `Hon`: the members; `R`: the common root.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C s`: the proof
reads Lemma 78 at slot `s` at the members' own ticks to that cutoff.

Read aloud: when every member's fork-choice root at its tick to the vote time of slot `s` is `R` and every
member's finalized block is compatible with `R`, every member's confirmation of slot `s` is `R` or a
descendant of `R`. -/
theorem rebase_confirmations_clause (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Run : RunFacts M S x) (GST s : ℕ) (Hon : Finset V) (R : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x) (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- every member is awake and honest from the duty window's start of slot `s` up to its own tick to
    -- the vote time of slot `s`
    (hHonVote : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.voteTime S.C s))
    -- each member runs the update of slot `s`: it ticks to the support cutoff of slot `s + 1`, active up to that tick
    -- from a tick at or before the duty window's start of slot `s + 1`
    (hHonUpd : ∀ v ∈ Hon, v ∈ updaterAt M S A x s)
    -- no member is in the adversary set at a step where a validator outside it ticks to the support cutoff of
    -- slot `s + 1` (, the second honesty read of)
    (hHonTick : ∀ u ∈ Hon, u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    (hCommittee : (S.P.committee s).card < 2 * (S.P.committee s ∩ Hon).card)
    (hRoot : ∀ w ∈ Hon, M.get_fc_root (x.tickInput w (M.voteTime S.C s)) = R)
    (hF : ∀ v ∈ Hon,
        (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.compatible R = true) :
    ∀ v ∈ Hon, ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C' →
      R.AncestorEq C' := by
  intro v hv
  -- the voters: each committee member of `Hon` sent its slot-`s` vote for a block it holds on `R`'s chain
  obtain ⟨H, hH⟩ := (rebase_voters M F U) S A x Run s Hon R E hHonVote hRoot
  -- `v`'s tick to the support cutoff of slot `s` (inside its reader), for the roots
  obtain ⟨kR, hkR, -⟩ := (updater_reader_gives_core_window M F U) x Run E hΔs hSkew (hHonUpd v hv)
  exact (GoldilocksCorrectness.Record.Statements.Executions.lem78_update_confirmation_extends_voter_majority_chain M F U)
    S A x Run GST s (S.P.committee s ∩ Hon) H R v E hNet hSkew hRedeliver Sy hΔs
    ((roots_at_own_tick_of_per_tick M F) x E hRoots hkR) hParent hOwner hGST
    (fun u hu => ⟨(Finset.mem_inter.1 hu).1,
      (not_mem_corrupted_tickStep_of_outside_at_honest_ticks M F) x E (hHonUpd v hv)
        (hHonTick u (Finset.mem_inter.1 hu).2),
      (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
    (fun u hu => (holder_window_of_updater_reader M F U) x Run E hΔs hSkew hGST
      (hHonUpd u (Finset.mem_inter.1 hu).2))
    (by
      unfold Trace.tickInput
      exact ((counting_of_committee_majority_st M F) S A x Run E s _ Hon v hCommittee).2.1)
    (hHonUpd v hv) (hF v hv)

/-! ## The re-base -/

open Classical in
/-- **Lemma 89c, the re-base.** The proof; the audited
statement is in `Statements/Executions/PhaseChainStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot; `Hon`: the members; `R`: the common root.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C s`: the proof
reads `rebase_locks_clause` and `rebase_confirmations_clause` at slot `s`, whose bound is that one.

Read aloud: when every member's fork choice at its tick to the vote time of slot `s` is rooted at `R`, no
member's finalized block at its tick to the support cutoff of slot `s + 1` conflicts with `R`, the members stay awake
and honest through the update of slot `s`, each runs that update, and no member is in the adversary set at
a tick of an honest validator to that cutoff, the honest chain re-forms on `R` in one slot. -/
theorem lem89c_rebase (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Run : RunFacts M S x) (GST s : ℕ) (Hon : Finset V) (R : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x) (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- every member is awake and honest from the start of its slot-`s` window, `duty_window_start S.C s`, up to its own
    -- tick to the vote time of slot `s`
    (hHonVote : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.voteTime S.C s))
    -- each member runs the update of slot `s`: it ticks to the support cutoff of slot `s + 1`, active up to that tick
    -- from a tick at or before the duty window's start of slot `s + 1`
    (hHonUpd : ∀ v ∈ Hon, v ∈ updaterAt M S A x s)
    -- no member is in the adversary set at a step where a validator outside it ticks to the support cutoff of
    -- slot `s + 1` (, the second honesty read of)
    (hHonTick : ∀ u ∈ Hon, u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    (hCommittee : (S.P.committee s).card < 2 * (S.P.committee s ∩ Hon).card)
    (hRoot : ∀ w ∈ Hon, M.get_fc_root (x.tickInput w (M.voteTime S.C s)) = R)
    (hF : ∀ v ∈ Hon,
        (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.compatible R = true) :
    HonestChainExtends M S A x Hon R s := by
  refine ⟨(rebase_votes_clause M F U) S A x Run E s Hon R hRoot, fun w hw n' sent hrun hAwake e he _ => ?_,
    (rebase_confirmations_clause M F U) S A x Run GST s Hon R E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner
      hGST hHonVote hHonUpd hHonTick hCommittee hRoot hF⟩
  -- the revocation of slot `s + 1` the outcome ran, from `w`'s tick input (the field `tick_voteTime_locks` of `F.tk2`)
  obtain ⟨hv1, -, -, hs2, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s + 1)
  have hsl : S.C.slot ((M.voteTime S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
      (by omega) (by omega)
  have hInv := (lem11_node_invariantCore_of_run M F S x Run (x.tickStep w (M.voteTime S.C (s + 1))) w).1
  have hRevoke := F.tk2.tick_voteTime_locks_of_core S.C S.P S.X _ _ n' sent hrun hInv
    (by rw [hsl]; exact (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout
      F.sched U) S (s + 1))
    (by rw [hsl]; exact hAwake)
  rw [hsl] at hRevoke
  exact (rebase_locks_clause M F U) S A x Run GST s Hon R E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST
    hHonVote hHonUpd hCommittee hRoot hF w hw n' hRevoke e he

/-! ## Lemma 45b -/

/-- **Lemma 45b, a lock whose window is after `GST` is extended by the next slot's honest votes,
the held form.** The proof; the audited statement is in
`Statements/Executions/PhaseChainStatements.lean`. It is the proof of Lemma 45
(`GoldilocksCorrectness/Proofs/Executions/Lemma45.lean`), steps 1 to 3 verbatim, with step 4
calling Lemma 21b (`lem21b_goldfish_vote_extends_eligible_block_held`) in place of Lemma 21, so
that the block the vote names is kept, held by `w`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the lock;
- `v`: the validator whose update of slot `s + 1` adds the lock entry `e`; `n'`, `sent`: an outcome
of `v`'s tick at the support cutoff of slot `s + 1`, which runs that update; `w`: the voter of slot
`s + 1`; `vote`: its Goldfish vote.

Roots name blocks until `M.supportCutoff S.C (s + 1)`: the proof reads Lemma 42 and Lemma 21b at
slot `s`, and Lemma 31 at a slot `s' < s`, whose bounds are at most that time.

Read aloud: under Lemma 45's hypotheses, `w`'s vote is its slot-`(s + 1)` vote for a block of its
own tree before that vote time that is the lock's block or a descendant of it. -/
theorem lem45b_honest_vote_extends_lock_held (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s : ℕ) (v w : V) (e : M.LE) (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C (s + 1 - S.C.k))
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    -- `w` ticks to the vote time of slot `s + 1`, active up to that tick from the trace's start or from its own tick
    -- to a clock value at most `tStartW`, more than both clock bounds before the window start Lemma 42 reads; `v` and
    -- `w` are active through the sync delay after the two read times of Lemma 42's sync facts
    (tStartW : ℤ) (htStartW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.voteTime S.C (s + 1)))
    (hv₀ : v ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
    (hAwake : AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1))
    (he : e ∈ M.lockEntries n')
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible e.B = true)
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq e.B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
        (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧ W ∈
          (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧
          e.B.AncestorEq W)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    ∃ H_w ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ e.B.AncestorEq H_w := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hs1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  have htime : Monotone x.time := fun _ _ h => (time_mono M) x R h
  -- the slot times
  have hss1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1)
  have hss0 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hsc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have hfr := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hfrk := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S (s + 1 - S.C.k)
  have hk2 := S.C.k_ge_two
  have hsk := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
    (show s + 1 - S.C.k ≤ s by omega)
  have hGSTv : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s := by omega
  -- the reads of Lemmas 21b and 42 at `v` (`lem21b_reads_of_dutyWindow`)
  obtain ⟨htStart, -⟩ := (lem21b_reads_of_dutyWindow M F U) S R E hSkew hΔs (le_of_add_le_right hGSTv) htStartW hv
  -- `v`'s tick `k_v` to the support cutoff of slot `s + 1`, active from that cutoff less `ΔClockAhead`
  have hslR : ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) ≤ (M.supportCutoff S.C (s + 1) : ℝ) := by
    exact_mod_cast Nat.sub_le _ _
  have hdle := (duty_window_start_le_real M F U) S (s + 1)
  obtain ⟨k_v, hk_v, hwinv⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv
    (t₀ := (M.supportCutoff S.C (s + 1) : ℝ) - ΔClockAhead) (by linarith)
  have hti_v : x.tickInput v (M.supportCutoff S.C (s + 1)) = x.st k_v v := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_v]
  have hRootsΦv : GoldilocksCorrectness.Statements.Routines.RootsNameBlocksIn
      (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree := by
    rw [hti_v]
    exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E _ v
  -- the confirmation update `v`'s tick ran
  have hCU := (confirmationUpdated_of_cutoff_tickInput M F U) x R s v n' sent hUpdate hAwake
  -- step 1: Lemma 35 on `v`'s update; `e` is an entry it adds
  obtain ⟨-, h35⟩ := GoldilocksCorrectness.Record.Statements.Routines.lem35_update_confirmation_lock_entries hCU
  rcases h35 e he with hin | ⟨-, -, -, ⟨C', hSaved, hLC'⟩, hFS⟩
  · -- an entry of the input was added by the update of its own slot `s`, before `v`'s tick
    exfalso
    rw [hti_v] at hin
    obtain ⟨s', hd', hlt, -⟩ := (lem39_lock_entry_provenance M F U) S A x R k_v v e E hin
    have hbb : s' = s :=
      GoldilocksCorrectness.Proofs.Routines.lockDeadline_injective S (hd'.symm.trans hd)
    rw [hbb, (tickStep_eq_of_lbl M) x E hk_v] at hlt
    exact lt_irrefl _ hlt
  -- step 2: Lemma 36 gives the early supporters of `e`'s block at `v`
  obtain ⟨Sup, hSup, hElig, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem36_confirmed_ancestor_early_supporters F)
      C' e.B hs1 hRootsΦv
      (by
        rw [Nat.add_sub_cancel, hti_v]
        exact (pool_vote_late_of_tick M F U) S A x R s v E k_v hk_v hwinv)
      hCU hSaved hLC'
  simp only [Nat.add_sub_cancel] at hSup hElig hFS
  -- the roots until the latest real time of `w`'s tick to the view freeze of slot `s`
  have hcf : (M.supportCutoff S.C (s + 1) : ℝ) = (M.viewFreeze S.C s : ℝ) + 3 * Δ S := by
    have h : M.supportCutoff S.C (s + 1) = M.viewFreeze S.C s + 3 * Δ S := by
      rw [hsc, hvt, hfr, hss1, hss0]; ring
    rw [h]; push_cast; ring
  have hRoots' : RootsNameBlocksUntil M A x ((M.viewFreeze S.C s : ℝ) + ΔClockBehind) := by
    refine (RootsNameBlocksUntil.mono M) ?_ hRoots
    rw [hcf]
    linarith
  -- `w`, active up to its tick to the view freeze of slot `s`
  have hvfv : (M.viewFreeze S.C s : ℝ) + ΔClockBehind < (M.voteTime S.C (s + 1) : ℝ) - ΔClockAhead := by
    have h : M.voteTime S.C (s + 1) = M.viewFreeze S.C s + 2 * Δ S := by
      rw [hvt, hfr, hss1, hss0]; ring
    rw [h]; push_cast; linarith
  have hfr1 : 1 ≤ M.viewFreeze S.C s := by rw [hfr]; omega
  have hwF : w ∈ A.activeThroughoutToTick x tStartW (M.viewFreeze S.C s) :=
    (mem_activeThroughoutToTick_of_le_end_int M) x R E hfr1
      (by
        have h3 : ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ) ≤ (M.viewFreeze S.C s : ℝ) := by
          exact_mod_cast Nat.sub_le _ _
        linarith)
      hvfv hw
  -- `w`'s tick `kV` to the vote time of slot `s + 1`, and its finalized block there
  obtain ⟨kV, hkV, hsV⟩ := hSend
  have hti_w : x.tickInput w (M.voteTime S.C (s + 1)) = x.st kV w := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkV]
  have hFroot : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F), hti_w]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E kV w
  have hFw : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.compatible e.B = true :=
    GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible hFroot hF2
  -- step 3: the lock condition at `w`, on the revocation every outcome of `w`'s tick ran
  have hLocks : ∀ (n'' : M.N) (sent'' : List (NamedObject V)),
      .ok (n'', sent'') ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e' ∈ M.lockEntries n'',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e' = true → e'.B.compatible e.B = true := by
    intro n'' sent'' hrun hAwakeW e' he' _
    have hRevoke := (locksRevoked_of_voteTime_outcome M F U) S A x R E (s + 1) w n'' sent'' hrun hAwakeW
    rcases hFS with hFast | hSlow
    · -- fast: Lemma 42
      exact (lem42_fast_lock_clears_conflicting_locks M F U) S A x R GST s e.B v w n' E hNet hSkew hRedeliver
        Sy hΔs hRoots' hParent hGSTv (duty_window_start S.C (s + 1)) htStart hv tStartW htStartW hwF hv₀ hw₀
        hCU hFast kV hkV hFw n'' hRevoke e' he'
    · -- slow: through the slot of each entry `w`'s revocation reads
      obtain ⟨e_w, he_w, hlive_w, -, he'w, -⟩ :=
        GoldilocksCorrectness.Record.Statements.Routines.lem38_revoke_locks_entries_moved hs1 hRevoke e' he'
      have hlt_w : ((M.voteTime S.C (s + 1) : ℕ) : Int) < e_w.d :=
        ((GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F) _ _ _).1 hlive_w |>.1
      rw [hti_w] at he_w
      obtain ⟨s', hd_w, hc_w, hlw', ⟨τw, hτw, hτwle⟩, h39w⟩ :=
        (lem39_lock_entry_provenance M F U) S A x R kV w e_w E he_w
      rw [(tickStep_eq_of_lbl M) x E hlw'] at hc_w
      -- `s' < s`: `w`'s tick to the support cutoff of slot `s' + 1` is before its tick to the vote time of slot
      -- `s + 1`, so to a smaller clock value (`clock_mono`, `tick_unique`)
      have hcv : M.supportCutoff S.C (s' + 1) < M.voteTime S.C (s + 1) := by
        generalize x.tickStep w (M.supportCutoff S.C (s' + 1)) = kc at hc_w hlw'
        have hbc := E.clock_mono _ kV w _ _ hc_w (E.not_mem_corrupted_of_tick hkV) (Or.inl hlw') (Or.inl hkV)
        rcases Nat.lt_or_ge (M.supportCutoff S.C (s' + 1)) (M.voteTime S.C (s + 1)) with h | h
        · exact h
        · have hbb : M.supportCutoff S.C (s' + 1) = M.voteTime S.C (s + 1) := le_antisymm hbc h
          rw [hbb] at hlw'
          exact absurd (E.tick_unique _ kV w _ hlw' hkV) (by omega)
      have hlt : s' < s := by
        by_contra h
        have h' : M.supportCutoff S.C (s + 1) ≤ M.supportCutoff S.C (s' + 1) := by
          rcases Nat.lt_or_eq_of_le (show s + 1 ≤ s' + 1 by omega) with h'' | h''
          · exact le_of_lt ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt_of_lt M.toSlotLayout F.sched) S h'')
          · rw [h'']
        omega
      -- `s + 1 − k ≤ s'`: `e_w` is live at the vote time of slot `s + 1`
      have hlow : s + 1 - S.C.k ≤ s' := by
        by_cases hkb : S.C.k ≤ s + 1
        · refine (lem41_slot_of_live_entry M F U) S (s + 1 - S.C.k) s' (M.voteTime S.C (s + 1)) e_w hd_w hlt_w ?_
          rw [Nat.sub_add_cancel hkb]
        · omega
      -- `e`'s block is `v`'s saved confirmation of slot `s'` or an ancestor of it
      obtain ⟨-, hj⟩ :=
        (GoldilocksCorrectness.Record.Statements.Routines.lem37_slow_test_saved_confirmations F) S.C _ s e.B hSlow
      obtain ⟨Cj, hCj, -, hBj⟩ := hj s' hlow hlt
      rw [hti_v] at hCj
      obtain ⟨hlt40, hl40, ⟨τ₁, hτ₁, hτ₁le⟩, hS40, -⟩ :=
        (lem40_saved_confirmation_provenance M F U) S A x R k_v v s' Cj E hCj
      obtain ⟨n₁, sent₁, hrun₁, hAw₁, -⟩ :=
        (update_state_of_tick M F U) S A x R s' v E hl40 ⟨τ₁, hτ₁, hτ₁le⟩
      have hU₁ := (confirmationUpdated_of_cutoff_tickInput M F U) x R s' v n₁ sent₁ hrun₁ hAw₁
      -- `w`'s update of slot `s' + 1` and the confirmation `e_w` traces to
      obtain ⟨nw, sentw, hrunw, hAww, -⟩ :=
        (update_state_of_tick M F U) S A x R s' w E hlw' ⟨τw, hτw, hτwle⟩
      have hU_w := (confirmationUpdated_of_cutoff_tickInput M F U) x R s' w nw sentw hrunw hAww
      obtain ⟨e₀w, -, -, -, -, ⟨C₀w, hC₀w, hB₀w⟩, -, hBw₀, -⟩ := h39w nw sentw hrunw hAww
      -- Lemma 31 at slot `s'`, its windows read off the two duty tests
      have hfrw := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s'
      have hsw := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hlow
      have hGSTw : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s' := by omega
      have hcb : Δs ≤ M.viewFreeze S.C s' := by
        have := le_max_right (Δ S) Δs
        omega
      obtain ⟨kF₁, hkF₁, -, hwin₁, hv₁₀⟩ :=
        (lem31_windows_of_duty_test M F U) x R E hSkew hΔs hcb hl40 hτ₁ hτ₁le
      obtain ⟨kF₂, hkF₂, -, hwin₂, hv₂₀⟩ :=
        (lem31_windows_of_duty_test M F U) x R E hSkew hΔs hcb hlw' hτw hτwle
      -- the two ticks to the support cutoff of slot `s' + 1` are before the support cutoff of slot `s + 1`
      have hcc : M.supportCutoff S.C (s' + 1) + 4 * Δ S ≤ M.supportCutoff S.C (s + 1) := by
        have hsc' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' + 1)
        have hvt' := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s' + 1)
        have hss' := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
          (show s' + 1 ≤ s by omega)
        have hsS : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
          rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
            (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s, Nat.mul_add,
            Nat.mul_one]
        omega
      have hccR : ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) + 4 * Δ S ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) := by
        exact_mod_cast hcc
      have hR31 : RootsNameBlocksUntil M A x
          (max (x.time (x.tickStep v (M.supportCutoff S.C (s' + 1))))
            (x.time (x.tickStep w (M.supportCutoff S.C (s' + 1))))) := by
        refine (RootsNameBlocksUntil.mono M) ?_ hRoots
        have h1 := (E.tick_active _ v _ hl40).2.2
        have h2 := (E.tick_active _ w _ hlw').2.2
        exact max_le (by linarith) (by linarith)
      have hcomp := (lem31_saved_confirmations_compatible M F U) S A x R GST s' v w n₁ nw Cj C₀w E
        hNet hSkew hRedeliver Sy hGSTw kF₁ hkF₁ hwin₁ hv₁₀ kF₂ hkF₂ hwin₂ hv₂₀ _ hl40 _ hlw' hR31
        hU₁ (hS40 n₁ sent₁ hrun₁ hAw₁) hU_w hC₀w
      exact GoldilocksCorrectness.Proofs.Routines.compatible_symm'
        (GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_both hBj
        (ancestorEq_trans he'w (ancestorEq_trans hBw₀ hB₀w)) hcomp)
  -- step 4: Lemma 21b, which keeps the block the vote names
  exact (lem21b_goldfish_vote_extends_eligible_block_held M F U) S A x R GST s Sup e.B v w vote E hNet hSkew hRedeliver
    Sy hΔs hRoots' hParent hGSTv (duty_window_start S.C (s + 1)) htStart hv tStartW htStartW hwF hv₀ hw₀ hSup hElig
    hF2 hF3 hLocks ⟨kV, hkV, hsV⟩

end GoldilocksCorrectness.Record.Proofs.Executions

