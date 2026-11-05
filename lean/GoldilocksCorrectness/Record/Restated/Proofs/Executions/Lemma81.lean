module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ReadingPointStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainAfterHealingDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.SleepyStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ConfirmationCompatibilityStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.LockStatementsForkChoice
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma21
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma26
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma33
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma36a
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma79
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma81, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma81.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: Lemma 81, after the healed round the honest
confirmations stay on the honest chain, and the slot invariant it carries from slot to slot. The
page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  dutyWindowStart_succ_le_slotStart duty_window_start_mono one_le_Δ slotStart_eq slotStart_mono
  slot_eq_of_mem supportCutoff_cast supportCutoff_eq supportCutoff_lt_of_lt supportCutoff_slot
  supportCutoff_succ_le viewFreeze_cast viewFreeze_eq voteTime_cast voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both compatible_symm')

open GoldilocksCorrectness.Proofs.Routines (slot_lt_of_ancestorEq_of_treeClosed)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)


open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated CountedVotes
  CountedVotesAt EarlySupporterOf LocksRevoked TreeClosed VoterTree VoterTreeAt)

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
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  compatible_iff compatible_of_ancestorEq_compatible mem_voter_block_tree_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; this rule, local to the file, proves it at once
--. No statement and no proof term
-- changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## Lemma 36b -/

/-- **Lemma 36b, a confirmed block is extended by the next slot's honest votes, the held form.**
The proof; the audited statement is in
`Statements/Executions/HonestChainAfterHealingStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot whose confirmation `v`'s update of slot `s + 1` saves;
- `C'`: the saved confirmation; `v`: the validator whose update saves it; `n'`: the node state that
  update leaves; `w`: the voter of slot `s + 1`; `vote`: its Goldfish vote.

Roots name blocks until `M.supportCutoff S.C (s + 1)`: Lemma 21b, which the proof calls, takes
blocks as held up to one delay after `w`'s vote time of slot `s + 1`.

Read aloud: under Lemma 36a's hypotheses, `w`'s vote is its slot-`(s + 1)` vote for a block of its
own tree before that vote time that is `C'` or a descendant of `C'`. -/
theorem lem36b_confirmed_block_extended_held (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (C' : Block V) (v w : V) (n' : M.N)
    (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s)
    -- `v`, awake and honest from the duty window's start of slot `s + 1` up to its tick to that
    -- slot's support cutoff
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    -- `w` is active from `tStartW` up to its tick to the view freeze of slot `s`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.viewFreeze S.C s))
    -- `w` is active for the sync delay after the support cutoff of slot `s + 1` less one delay or one sync
    -- delay, whichever is longer (the holder's window,: Lemma 21b reads `w` as a holder through
    -- Lemma 64)
    (hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hUpdate : ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n')
    (hSaved : n'.savedConfirmation s = some C')
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible C' = true)
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq C' →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
          (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧
          C'.AncestorEq W)
    (hLocks : ∀ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n'',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible C' = true)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    ∃ H_w ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ C'.AncestorEq H_w := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hs1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  obtain ⟨htStart, hv₀'⟩ := (lem21b_reads_of_dutyWindow M F U) S R E hSkew hΔs (le_of_add_le_right hGST) htStartW hv
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
  -- Lemma 36 at `C'` itself, on `v`'s pool at its tick to the support cutoff of slot `s + 1`
  obtain ⟨Sup, hSup, hElig, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem36_confirmed_ancestor_early_supporters F)
      C' C' hs1 hRootsΦv
      (by
        rw [Nat.add_sub_cancel, hti_v]
        exact (pool_vote_late_of_tick M F U) S A x R s v E k_v hk_v hwinv)
      hUpdate (by rw [Nat.add_sub_cancel]; exact hSaved) (GoldilocksCorrectness.Proofs.Routines.ancestorEq_refl C')
  simp only [Nat.add_sub_cancel] at hSup hElig
  -- the roots until the latest real time of `w`'s tick to the view freeze of slot `s`
  have hRoots' : RootsNameBlocksUntil M A x ((M.viewFreeze S.C s : ℝ) + ΔClockBehind) := by
    have hB0 := E.behind_nonneg
    have hA0 := E.ahead_nonneg
    have hss1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1)
    have hss0 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
    have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
    have hsc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
    have hfr := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
    refine (RootsNameBlocksUntil.mono M) ?_ hRoots
    have : (M.supportCutoff S.C (s + 1) : ℝ) = (M.viewFreeze S.C s : ℝ) + 3 * Δ S := by
      have h : M.supportCutoff S.C (s + 1) = M.viewFreeze S.C s + 3 * Δ S := by
        rw [hsc, hvt, hfr, hss1, hss0]; ring
      rw [h]; push_cast; ring
    rw [this]
    have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast one_le_Δ S
    linarith
  -- Lemma 21, the held form, at `C'`
  exact (lem21b_goldfish_vote_extends_eligible_block_held M F U) S A x R GST s Sup C' v w vote E hNet hSkew hRedeliver Sy hΔs hRoots' hParent
    hGST (duty_window_start S.C (s + 1)) htStart hv tStartW htStartW hw hv₀' hw₀ hSup hElig hF2 hF3 hLocks hSend

/-! ## Kit: the windows of the sets of a slot, and a member that joined during a slot -/

omit [RootOrder] in
/-- A validator of `honestActiveAt M S A x s` ticks to the support cutoff of slot `s + 1` and is
active after every step from the first step whose time is the duty window's start of slot `s` up to
that tick, or from its tick to that start up to that tick (`A.activeThroughoutToTick`).

The window ends at the member's tick, as the set's own reader does: nothing is said of
the steps after that tick. `EnvFactsBy.active_of_mem_activeThroughoutToTick` reads it at a step.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `A`: the activity; `s`: the slot; `u`: the validator; `x`: the trace; `E`: the
  environment's facts.

Read aloud: a validator of `honestActiveAt M S A x s` is awake and honest from the duty window's
start of slot `s` up to its tick to the support cutoff of slot `s + 1`. -/
theorem honestActiveAt_window (S : Setup V) (A : Activity V) (s : ℕ) (u : V)
    {x : Trace V (NamedObject V) M.N} {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hu : u ∈ honestActiveAt M S A x s) :
    u ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.supportCutoff S.C (s + 1)) :=
  -- awake up to its tick to the cutoff, and outside the adversary set at that tick (`tick_active`), so at
  -- every earlier step (corruption is permanent)
  E.mem_activeThroughoutToTick_of_awakeThroughoutToTick (Finset.mem_sdiff.1 hu).1

omit [RootOrder] in
/-- A validator of `updaterAt M S A x s` ticks to the support cutoff of slot `s + 1` and is active
after every step from the first step whose time is the duty window's start of slot `s + 1` up to
that tick, or from its tick to that start up to that tick (`A.activeThroughoutToTick`).

The window ends at the member's tick, as the set's own reader does: nothing is said of
the steps after that tick. `EnvFactsBy.active_of_mem_activeThroughoutToTick` reads it at a step.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `A`: the activity; `s`: the slot; `v`: the validator; `x`: the trace; `E`: the
  environment's facts.

Read aloud: a validator of `updaterAt M S A x s` is awake and honest from the duty window's start of
slot `s + 1` up to its tick to the support cutoff of slot `s + 1`. -/
theorem updaterAt_window (S : Setup V) (A : Activity V) (s : ℕ) (v : V)
    {x : Trace V (NamedObject V) M.N} {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hv : v ∈ updaterAt M S A x s) :
    v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)) :=
  hv

/-- With permanent corruption, an honest active validator of slot `s + 1` is an updater of slot
`s`: the duty window of slot `s + 1` to the support cutoff of slot `s + 1` is inside its window,
and its honesty at the support cutoff of slot `s + 2` gives its honesty at that of slot `s + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `s`: the slot.

Read aloud: with permanent corruption, an honest active validator of slot `s + 1` is an updater of
slot `s`. -/
theorem honestActiveAt_succ_subset_updaterAt (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (s : ℕ)
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) :
    honestActiveAt M S A x (s + 1) ⊆ updaterAt M S A x s := by
  intro u hu
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  -- `u` is active from the duty window's start of slot `s + 1` up to its tick to the support cutoff of
  -- slot `s + 2`, so up to its tick to that of slot `s + 1`, inside that window by the clock bounds'
  -- margins (`hSkew`)
  have hwa : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1 + 1)) :=
    E.mem_activeThroughoutToTick_of_awakeThroughoutToTick (Finset.mem_sdiff.1 hu).1
  have hdR := duty_window_start_real S (s + 1)
  have hcR : ∀ s' : ℕ, ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * ((s' : ℕ) : ℝ) + 6 * (Δ S : ℝ) := fun s' => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s' + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s' + 1)]
    push_cast
    ring
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hkR : (2 : ℝ) ≤ (S.C.k : ℝ) := by exact_mod_cast hk
  have hΔk : (Δ S : ℝ) ≤ 4 * (Δ S : ℝ) * (S.C.k : ℝ) := by nlinarith
  have hc1 := ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S s).2
  exact (mem_activeThroughoutToTick_of_inside M F) R E (c := M.supportCutoff S.C (s + 1)) hwa hc1
    (by rw [hdR, hcR s]; push_cast; linarith) (by rw [hcR s, hcR (s + 1)]; push_cast; linarith)

/-- With permanent corruption, an honest active validator of slot `s + 1` is an honest active
validator of slot `s`, or holds, before the vote time of slot `s + 1`, no lock entry live there.

Why: it ticks to the support cutoff of slot `s + 1` and is active from the duty window's start of slot
`s + 1` up to that tick (its reader for slot `s + 1`, cut at that tick), so `mem_activeAt_or_lockFree`;
honest at the support cutoff of slot `s + 2`, it is honest at that of slot `s + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `s`: the slot; `u`: the validator.

Read aloud: with permanent corruption, an honest active validator of slot `s + 1` is one of slot
`s`, or holds no live lock at the vote time of slot `s + 1`. -/
theorem mem_honestActiveAt_or_lockFree (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (s : ℕ) (u : V)
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hu : u ∈ honestActiveAt M S A x (s + 1)) :
    u ∈ honestActiveAt M S A x s ∨
      ∀ e ∈ (x.tickInput u (M.voteTime S.C (s + 1))).lockEntries,
        M.is_live (x.tickInput u (M.voteTime S.C (s + 1))) ((M.voteTime S.C (s + 1) : ℕ) : Int) e = false := by
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hu1 := Finset.mem_sdiff.1 hu
  -- `u` is active from the duty window's start of slot `s + 1` up to its tick to the support cutoff of
  -- slot `s + 2`, so up to its tick to that of slot `s + 1`, inside that window by the clock bounds'
  -- margins (`hSkew`)
  have hwa : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1 + 1)) :=
    E.mem_activeThroughoutToTick_of_awakeThroughoutToTick hu1.1
  have hdR := duty_window_start_real S (s + 1)
  have hcR : ∀ s' : ℕ, ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * ((s' : ℕ) : ℝ) + 6 * (Δ S : ℝ) := fun s' => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s' + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s' + 1)]
    push_cast
    ring
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hkR : (2 : ℝ) ≤ (S.C.k : ℝ) := by exact_mod_cast hk
  have hΔk : (Δ S : ℝ) ≤ 4 * (Δ S : ℝ) * (S.C.k : ℝ) := by nlinarith
  have hc1 := ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S s).2
  have hw := (mem_activeThroughoutToTick_of_inside M F) R E (c := M.supportCutoff S.C (s + 1)) hwa hc1
    (by rw [hdR, hcR s]; push_cast; linarith) (by rw [hcR s, hcR (s + 1)]; push_cast; linarith)
  -- honest at the support cutoff of slot `s + 2` (through its real time and at every honest tick to it),
  -- it is honest at that of slot `s + 1`: the cutoffs are `4 Δ S` apart and `ΔClockBehind < Δ S`
  have hcut : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind ≤
      ((M.supportCutoff S.C (s + 1 + 1) : ℕ) : ℝ) := by
    rw [hcR s, hcR (s + 1)]
    push_cast
    linarith
  have hc := not_mem_corruptedAtTime_union_ticks_of_le E hcut (fun h => hu1.2 (Finset.mem_union_left _ h))
  exact ((mem_activeAt_or_lockFree M F U) S A x R s u E hw).imp (fun h => Finset.mem_sdiff.2 ⟨h, hc⟩) id

omit [RootOrder] in
/-- When `Q` has fewer than twice the members of `Q ∩ H`, the members of `Q` outside `Q ∩ H` are
fewer than those of `Q ∩ H`.

The variables:
- `M`: the model; `F`: its facts;
- `Q`: the committee; `H`: the set counted in it.

Read aloud: when `Q` has fewer than twice the members of `Q ∩ H`, the members of `Q` outside `Q ∩ H`
are fewer than those of `Q ∩ H`. -/
theorem committee_sdiff_lt (Q H : Finset V) (h : |Q| < 2 * |Q ∩ H|) :
    |Q \ (Q ∩ H)| < |Q ∩ H| := by
  have := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left : Q ∩ H ⊆ Q)
  omega

/-! ## Kit: the locks -/

/-- **The lock invariant from the revocation's form.** When every lock entry that the revocation
of the locks of slot `s + 1` at its vote time leaves from the state `u`'s tick to that time starts
from, live then,
is on a block of `𝓒` or an ancestor of one, `LiveLocksOnFamilyAt M S Sched x 𝓒 s u` holds.

Why: every outcome of `u`'s tick at that vote time, from its state awake for slot `s + 1`, ran that
revocation (`locksRevoked_of_voteTime_outcome`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `𝓒`: the family; `s`: the slot;
  `u`: the validator.

Read aloud: the lock invariant at `u` holds when it holds of every state the revocation can
leave. -/
theorem liveLocksOnFamilyAt_of_locksRevoked (U : UniformSchedule M.toSlotLayout) (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (𝓒 : Block V → Prop) (s : ℕ)
    (u : V)
    (h : ∀ n' : M.N,
      LocksRevoked M S.P (x.tickInput u (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) (s + 1) n' →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput u (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true →
        ∃ D : Block V, 𝓒 D ∧ e.B.AncestorEq D) :
    LiveLocksOnFamilyAt M S A x 𝓒 s u := fun n' sent hrun hA =>
  h n' ((locksRevoked_of_voteTime_outcome M F U) S A x R E (s + 1) u n' sent hrun hA)

/-- **A revocation from a state with no live lock leaves no lock.** When no lock entry of a node
state `n₀` is live at `t`, every node state `n'` that the revocation of a slot `s ≥ 1` at `t` can
leave from `n₀` (`LocksRevoked`) holds no lock entry.

Why: every entry the revocation leaves comes from an entry of `u`'s state live at `t` (the
second case of `LocksRevoked`).

The landed statement reads the answer of the revocation; the twin reads every node state the
revocation can leave (`LocksRevoked`), the form of Lemma 79b's twin, which recovers the landed
statement at every answer; a caller holding an outcome of the tick at a vote time, from a state
awake for the slot, reaches it by `locksRevoked_of_voteTime_outcome`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `s`: the slot of the
  revocation; `u`: the validator; `n'`: the node state the revocation leaves.

Read aloud: when no lock entry of `u`'s state before `t` is live at `t`, the revocation a tick of
slot `s ≥ 1` at `t` runs leaves no lock entry. -/
theorem revoke_locks_empty_of_lockFree (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (t s : ℕ) (n₀ n' : M.N) (hs : 1 ≤ s)
    (hfree : ∀ e ∈ n₀.lockEntries, M.is_live n₀ ((t : ℕ) : Int) e = false)
    (hRevoke : LocksRevoked M S.P n₀ ((t : ℕ) : Int) s n') :
    ∀ e ∈ M.lockEntries n', False := by
  intro e he
  -- every entry the revocation leaves comes from an entry of `u`'s state live at `t`
  rcases hRevoke with ⟨h0, -⟩ | ⟨-, hmv, -⟩
  · exact absurd h0 (Nat.one_le_iff_ne_zero.1 hs)
  obtain ⟨e₁, he₁, hlive, -⟩ := hmv e he
  rw [hfree e₁ he₁] at hlive
  exact Bool.false_ne_true hlive

/-- **The lock invariant holds vacuously at a validator with no live lock.** When no lock entry of
the state `u`'s tick to the vote time of slot `s + 1` starts from is live then, every lock entry of every
node state the revocation of slot `s + 1` at that vote time can leave (`LocksRevoked`), live
then, is on a block of `𝓒` or an ancestor of one, for every family `𝓒`: the condition of
`LiveLocksOnFamilyAt M S Sched x 𝓒 s u` on every state the revocation can leave
(`liveLocksOnFamilyAt_of_locksRevoked` gives the condition itself).

The landed statement reads the answer of the revocation; the twin reads every node state the
revocation can leave (`LocksRevoked`), the form of Lemma 79b's twin, which recovers the landed
statement at every answer; a caller holding an outcome of the tick at a vote time, from a state
awake for the slot, reaches it by `locksRevoked_of_voteTime_outcome`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `𝓒`: the family; `s`: the slot;
  `u`: the validator.

Read aloud: when no lock entry of `u`'s state before the vote time of slot `s + 1` is live then, the
lock invariant holds at `u` for every family. -/
theorem liveLocksOnFamilyAt_of_lockFree (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (𝓒 : Block V → Prop) (s : ℕ) (u : V)
    (hfree : ∀ e ∈ (x.tickInput u (M.voteTime S.C (s + 1))).lockEntries,
      M.is_live (x.tickInput u (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) e = false) :
    ∀ n' : M.N,
      LocksRevoked M S.P (x.tickInput u (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) (s + 1) n' →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput u (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true →
        ∃ D : Block V, 𝓒 D ∧ e.B.AncestorEq D := by
  intro n' hRevoke e he _
  exact ((revoke_locks_empty_of_lockFree M F) S A x _ (s + 1) _ n' (Nat.le_add_left 1 s) hfree
    hRevoke e he).elim

/-- **Where a live lock entry between the update of slot `s' + 1` and the revocation of slot
`s' + 2` comes from.** In an execution where every time is reached:
when `w` is awake and honest at every time from the duty window's start of slot `s' + 2` to `t`,
and `t` is after the support cutoff of slot `s' + 1` and at most the vote time of slot `s' + 2`,
then every lock entry `e` that `w` holds before `t` with its deadline after `t` is on `w`'s saved
confirmation of slot `s'` (right after the support cutoff of slot `s' + 1`) or an ancestor of it,
or on the block of an entry live at the vote time of slot `s' + 1` that the outcome of `w`'s tick
there, from its state awake for slot `s' + 1`, holds, or an ancestor of it.

Why: `live_locks_compatible_of_honestChainExtends_tick`'s proof without its invariant. The entry was
added by `w`'s update of a slot `s₁ + 1` with `s₁ ≤ s'` (Lemma 39). When `s₁ = s'`, its block is
the saved confirmation of slot `s'` or an ancestor of it (`update_state_of_lock_entry`). When
`s₁ < s'`, `w` was awake since that update, its tick at the vote time of slot `s' + 1` ran the
revocation (`locksRevoked_of_voteTime_outcome`), and an entry with `e`'s deadline, on a descendant
of `e`'s block, survived it live (Lemma 39's trace).

The landed statement's second case names an answer of `w`'s revocation of slot `s' + 1`; the twin
names an outcome of `w`'s tick at that vote time from its state awake for the slot (what
`LiveLocksOnFamilyAt` reads), which holds the lock entries of that answer.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `t`: the time;
  `w`: the validator.

Read aloud: a lock entry `w` holds before `t`, live after `t`, is on `w`'s saved confirmation of
slot `s'` or an ancestor of it, or on an ancestor of an entry live after `w`'s revocation of slot
`s' + 1`. -/
theorem live_lock_entry_source (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s' t : ℕ) (w : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hHon : w ∈ A.activeThroughoutToTick x (M.dutyWindowStart S.C (s' + 2) : ℤ) t)
    (ht1 : M.supportCutoff S.C (s' + 1) < t)
    (ht2 : t ≤ M.voteTime S.C (s' + 2)) :
    ∀ e ∈ (x.tickInput w t).lockEntries, ((t : ℕ) : Int) < e.d →
      (∃ C' : Block V,
        (x.tickOutput w (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' ∧
        e.B.AncestorEq C') ∨
      ∃ (n₃ : M.N) (sent₃ : List (NamedObject V)),
        .ok (n₃, sent₃) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s' + 1)))
          ((M.voteTime S.C (s' + 1) : ℕ) : Int) ∧
        AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s' + 1))) (s' + 1) ∧
        ∃ e' ∈ M.lockEntries n₃,
          M.is_live (x.tickInput w (M.voteTime S.C (s' + 1)))
            ((M.voteTime S.C (s' + 1) : ℕ) : Int) e' = true ∧ e.B.AncestorEq e'.B := by
  intro e he hlive
  -- the times
  have hΔ := one_le_Δ S
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
  -- `w`'s tick to `t`, and its activity from the duty window's start up to it
  obtain ⟨k', hk', hact⟩ := Activity.mem_activeThroughoutToTick.1 hHon
  have hts : x.tickStep w t = k' := (tickStep_eq_of_lbl M) x E hk'
  have he' : e ∈ (x.st k' w).lockEntries := by
    rw [← hts]
    exact he
  -- where `e` comes from (Lemma 39 at the step `k'`): `w`'s update of a slot `s₁ + 1` at its tick
  -- to the support cutoff `c₁`, at an earlier step, with an outcome of that tick
  obtain ⟨s₁, hd₁, hk₁, hl₁, ⟨τ, hτ, hτle⟩, h39⟩ :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem39_lock_entry_provenance M F U) S A x R k' w e
      E he'
  obtain ⟨n₁, sent₁, hrun₁, hAw₁, hsave, -⟩ :=
    (update_state_of_tick M F U) S A x R s₁ w E hl₁ ⟨τ, hτ, hτle⟩
  obtain ⟨e₀, -, -, -, -, ⟨C', hC', hBC⟩, -, he₀, htr⟩ := h39 n₁ sent₁ hrun₁ hAw₁
  have heC : e.B.AncestorEq C' := ancestorEq_trans he₀ hBC
  -- `c₁` is at most `t` (`clock_mono`), so the slot of `e` is at most `s'`
  have hcT : M.supportCutoff S.C (s₁ + 1) ≤ t :=
    E.clock_mono _ _ w _ _ hk₁ (E.not_mem_corrupted_of_tick hk') (Or.inl hl₁) (Or.inl hk')
  have hs₁ : s₁ ≤ s' := by
    by_contra h
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show s' + 2 ≤ s₁ + 1 by omega)
    have h1 := hv' (s' + 2)
    have h2 := hc' (s₁ + 1)
    have h3 := hv' (s₁ + 1)
    omega
  rcases Nat.lt_or_eq_of_le hs₁ with hlt | heq
  · -- `s₁ < s'`: the revocation at the vote time of slot `s' + 1` kept an entry for `e`
    have hk : s' + 1 ≤ s₁ + S.C.k := by
      by_cases hkle : S.C.k ≤ s' + 1
      · have h41 := (GoldilocksCorrectness.Record.Statements.Executions.lem41_slot_of_live_entry M F U) S
          (s' + 1 - S.C.k) s₁ t e hd₁ hlive (by
            rw [show s' + 1 - S.C.k + S.C.k = s' + 1 by omega]
            have := hc' (s' + 1)
            omega)
        omega
      · omega
    have hdw : M.dutyWindowStart S.C (s' + 2) ≤ M.supportCutoff S.C (s₁ + 1) :=
      (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_le_supportCutoff M.toSlotLayout F.sched U)
        S (by omega)
    have hc₃ : M.supportCutoff S.C (s₁ + 1) + 3 * Δ S ≤ M.voteTime S.C (s' + 1) := by
      have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
        (show s₁ + 1 ≤ s' by omega)
      have h1 := hc' (s₁ + 1)
      have h2 := hv' (s₁ + 1)
      have h3 := hv' (s' + 1)
      have h4 := hss s'
      omega
    have ht₃ : M.voteTime S.C (s' + 1) + Δ S < t := by
      have := hc' (s' + 1)
      omega
    -- `w` is active at every step from its tick to `c₁` to its tick to `t`: the reader's tick to a
    -- value at most the duty window's start comes at or before the tick to `c₁` (`clock_mono`,
    -- `tick_unique`)
    have hactw : ∀ i : ℕ, x.tickStep w (M.supportCutoff S.C (s₁ + 1)) ≤ i → i ≤ k' → w ∈ A.active i := by
      rcases hact with hall | ⟨k, -, c, hca, hlk, hk⟩
      · exact fun i _ h => hall i h
      · have hkk₁ : k ≤ x.tickStep w (M.supportCutoff S.C (s₁ + 1)) := by
          by_contra hlt'
          have hlt'' := Nat.lt_of_not_le hlt'
          have hcc := E.clock_mono _ _ w _ _ hlt'' (E.not_mem_corrupted_of_tick hlk) (Or.inl hl₁) (Or.inl hlk)
          have hca' : c ≤ M.dutyWindowStart S.C (s' + 2) := by exact_mod_cast hca
          have hceq : c = M.supportCutoff S.C (s₁ + 1) := by omega
          rw [hceq] at hlk
          have := E.tick_unique _ _ w _ hl₁ hlk
          omega
        exact fun i h1 h2 => hk i (hkk₁.trans h1) h2
    -- the real times of the two ticks
    have hT₁ := (E.tick_active _ w _ hl₁).2.2
    have hT' := (E.tick_active _ w _ hk').2.1
    have hc₃R : ((M.supportCutoff S.C (s₁ + 1) : ℕ) : ℝ) + 3 * (Δ S : ℝ) ≤ (M.voteTime S.C (s' + 1) : ℕ) := by
      exact_mod_cast hc₃
    have ht₃R : ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) + (Δ S : ℝ) + 1 ≤ (t : ℝ) := by
      exact_mod_cast ht₃
    have hΔR : (0 : ℝ) ≤ (Δ S : ℝ) := Nat.cast_nonneg _
    -- a step whose real time is within one clock bound of the vote time of slot `s' + 1` is between
    -- the two ticks
    have hbetween : ∀ i : ℕ, ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) - ΔClockAhead ≤ x.time i →
        x.time i ≤ ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) + ΔClockBehind →
        x.tickStep w (M.supportCutoff S.C (s₁ + 1)) ≤ i ∧ i ≤ k' := by
      intro i h1 h2
      constructor
      · by_contra hlt'
        have := (time_mono M) x R (Nat.lt_of_not_le hlt').le
        linarith
      · by_contra hlt'
        have := (time_mono M) x R (Nat.lt_of_not_le hlt').le
        linarith
    -- so `w` ticks to the vote time of slot `s' + 1`, between the two ticks
    obtain ⟨k₃, hl₃, h3a, h3b⟩ := E.tick_of_active (M.voteTime S.C (s' + 1)) (by have := hv' (s' + 1); omega) w
      (fun i h1 h2 => hactw i (hbetween i h1 h2).1 (hbetween i h1 h2).2)
    have hts₃ : x.tickStep w (M.voteTime S.C (s' + 1)) = k₃ := (tickStep_eq_of_lbl M) x E hl₃
    have hk₁₃ : x.tickStep w (M.supportCutoff S.C (s₁ + 1)) < k₃ := by
      refine lt_of_le_of_ne (hbetween k₃ h3a h3b).1 fun h => ?_
      rw [h, hl₃] at hl₁
      have := Event.tick.inj hl₁
      omega
    have hk₃' : k₃ < k' := by
      refine lt_of_le_of_ne (hbetween k₃ h3a h3b).2 fun h => ?_
      rw [h, hk'] at hl₃
      have := Event.tick.inj hl₃
      omega
    -- the outcome of that tick
    obtain ⟨n₃, sent₃, hok₃, hst₃, -⟩ := R.tick k₃ w _ hl₃
    have hrun₃ : .ok (n₃, sent₃) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s' + 1)))
        ((M.voteTime S.C (s' + 1) : ℕ) : Int) := by
      unfold Trace.tickInput
      rw [hts₃]
      exact hok₃
    -- the tick reads a state awake since `τ`: no restart between the two ticks
    have hτ' : (x.st (x.tickStep w (M.supportCutoff S.C (s₁ + 1))) w).awakeSince = some τ := hτ
    have hAw₃ : (x.st k₃ w).awakeSince = some τ :=
      (awakeSince_kept_of_awake_steps M F) x R E hk₁₃.le
        (fun i h1 h2 => Activity.mem_awake_of_mem_active (hactw i h1 (by omega))) hτ'
    have hτ₃ : τ ≤ duty_window_start S.C (s' + 1) :=
      le_trans hτle (duty_window_start_mono S (by omega))
    have hAwake : AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s' + 1))) (s' + 1) := by
      refine ⟨τ, ?_, hτ₃⟩
      unfold Trace.tickInput
      rw [hts₃]
      exact hAw₃
    have hRevoke := (locksRevoked_of_voteTime_outcome M F U) S A x R E (s' + 1) w n₃ sent₃ hrun₃ hAwake
    -- the entry for `e` right after that tick, an entry of the tick's outcome, live then
    obtain ⟨e', he'', hd', heB', -⟩ := htr (k₃ + 1) (by omega) (by omega)
    have he'A : e' ∈ M.lockEntries n₃ := by
      rw [← hst₃]
      exact he''
    have hlive' : M.is_live (x.tickInput w (M.voteTime S.C (s' + 1)))
        ((M.voteTime S.C (s' + 1) : ℕ) : Int) e' = true := by
      simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)]
      refine ⟨?_, GoldilocksCorrectness.Record.Proofs.Routines.revoke_locks_entry_mem_tree
        (Nat.le_add_left 1 s') hRevoke e' he'A⟩
      rw [hd']
      exact lt_trans (Int.ofNat_lt.2 (by omega)) hlive
    exact Or.inr ⟨n₃, sent₃, hrun₃, hAwake, e', he'A, hlive', heB'⟩
  · -- `s₁ = s'`: the update of slot `s' + 1` saved `C'`
    subst heq
    refine Or.inl ⟨C', ?_, heC⟩
    rw [hsave]
    exact hC'

/-- **Where a lock entry the revocation of slot `s' + 2` leaves comes from.** In an execution where
every time is reached: when `w` is awake and honest at every time
from the duty window's start of slot `s' + 2` to the vote time of slot `s' + 2`, every lock entry
of every node state that `w`'s revocation of slot `s' + 2` at its vote time can leave
(`LocksRevoked`) is on `w`'s saved confirmation of
slot `s'` or an ancestor of it, or on the block of an entry live at the vote time of slot `s' + 1`
that the outcome of `w`'s tick there, from its state awake for slot `s' + 1`, holds, or an
ancestor of it.

Why: the entry is on the block of an entry of `w`'s state then, or an ancestor of it, whose
deadline is after that time (the second case of `LocksRevoked`); `live_lock_entry_source` at the
vote time of slot `s' + 2`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `w`: the
  validator.

The landed statement reads the answer of the revocation; the twin reads every node state the
revocation can leave (`LocksRevoked`), the form of Lemma 79b's twin, which recovers the landed
statement at every answer; a caller holding an outcome of the tick at a vote time, from a state
awake for the slot, reaches it by `locksRevoked_of_voteTime_outcome`.

The landed statement's second case names an answer of `w`'s revocation of slot `s' + 1`; the twin
names an outcome of `w`'s tick at that vote time from its state awake for the slot (what
`LiveLocksOnFamilyAt` reads), which holds the lock entries of that answer.

Read aloud: a lock entry `w`'s revocation of slot `s' + 2` leaves is on `w`'s saved confirmation of
slot `s'` or an ancestor of it, or on an ancestor of an entry live after `w`'s revocation of slot
`s' + 1`. -/
theorem revoked_lock_source (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s' : ℕ) (w : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hHon : w ∈ A.activeThroughoutToTick x (M.dutyWindowStart S.C (s' + 2) : ℤ) (M.voteTime S.C (s' + 2))) :
    ∀ n' : M.N,
      LocksRevoked M S.P (x.tickInput w (M.voteTime S.C (s' + 2)))
        ((M.voteTime S.C (s' + 2) : ℕ) : Int) (s' + 2) n' →
      ∀ e ∈ M.lockEntries n',
        (∃ C' : Block V,
          (x.tickOutput w (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' ∧
          e.B.AncestorEq C') ∨
        ∃ (n₃ : M.N) (sent₃ : List (NamedObject V)),
          .ok (n₃, sent₃) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s' + 1)))
            ((M.voteTime S.C (s' + 1) : ℕ) : Int) ∧
          AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s' + 1))) (s' + 1) ∧
          ∃ e' ∈ M.lockEntries n₃,
            M.is_live (x.tickInput w (M.voteTime S.C (s' + 1)))
              ((M.voteTime S.C (s' + 1) : ℕ) : Int) e' = true ∧ e.B.AncestorEq e'.B := by
  intro n' hRevoke e' he'
  have hΔ := one_le_Δ S
  have hv₂ : M.voteTime S.C (s' + 2) = M.voteTime S.C (s' + 1) + 4 * Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S (s' + 1)
  have hc₁ : M.supportCutoff S.C (s' + 1) = M.voteTime S.C (s' + 1) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' + 1)
  have hlt₂ : M.supportCutoff S.C (s' + 1) < M.voteTime S.C (s' + 2) := by omega
  -- the entry came from an entry `e` of `w`'s state then, live then, on a descendant of its block
  -- (`LocksRevoked` at a slot after slot `0`)
  rcases hRevoke with ⟨h0, -⟩ | ⟨-, hmv, -⟩
  · exact absurd h0 (Nat.succ_ne_zero _)
  obtain ⟨e, he, hl, -, hmov⟩ := hmv e' he'
  have hB : e'.B.AncestorEq e.B := hmov.1.2.2.1
  have hlt : ((M.voteTime S.C (s' + 2) : ℕ) : Int) < e.d :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F) _ _ _).1 hl |>.1
  rcases (live_lock_entry_source M F U) S A x R s' (M.voteTime S.C (s' + 2)) w E hSkew hHon hlt₂ le_rfl
      e he hlt with ⟨C', h1, h2⟩ | ⟨n₃, sent₃, h1, h1', e'', h2, h3, h4⟩
  · exact Or.inl ⟨C', h1, ancestorEq_trans hB h2⟩
  · exact Or.inr ⟨n₃, sent₃, h1, h1', e'', h2, h3, ancestorEq_trans hB h4⟩

/-- **The lock invariant's step, at one member.** In an execution where every time is reached:
when `u` is awake and honest at every time from the duty window's start
of slot `s' + 2` to the vote time of slot `s' + 2`, every block of `𝓒` is a block of `𝓒'`, `u`'s
saved confirmation of slot `s'` (right after the support cutoff of slot `s' + 1`) is a block of
`𝓒'`, and `LiveLocksOnFamilyAt M S Sched x 𝓒 s' u` holds, then every lock entry of
every node state `u`'s revocation of slot `s' + 2` at its vote time can leave (`LocksRevoked`),
live then, is on a block of `𝓒'` or an ancestor of one: the condition of
`LiveLocksOnFamilyAt M S Sched x 𝓒' (s' + 1) u` on every state the revocation can leave
(`liveLocksOnFamilyAt_of_locksRevoked` gives the condition itself).

The landed statement reads the answer of the revocation; the twin reads every node state the
revocation can leave (`LocksRevoked`), the form of Lemma 79b's twin, which recovers the landed
statement at every answer; a caller holding an outcome of the tick at a vote time, from a state
awake for the slot, reaches it by `locksRevoked_of_voteTime_outcome`.

Why: an entry `u`'s revocation of slot `s' + 2` leaves is on `u`'s saved confirmation of slot `s'`
or an ancestor of it, or on an ancestor of the block of an entry live after the revocation of slot
`s' + 1` (`revoked_lock_source`), which the invariant at slot `s'` puts on the chain of a block of
`𝓒`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `𝓒`, `𝓒'`: the families before and
  after the step; `s'`: the slot; `u`: the validator.

Read aloud: if `u` stays awake and honest through the next slot's vote, and its new confirmation
joins the family, its live locks stay on the chain of the family. -/
theorem liveLocksOnFamilyAt_step (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (𝓒 𝓒' : Block V → Prop) (s' : ℕ) (u : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hHon : u ∈ A.activeThroughoutToTick x (M.dutyWindowStart S.C (s' + 2) : ℤ) (M.voteTime S.C (s' + 2)))
    (hSub : ∀ C : Block V, 𝓒 C → 𝓒' C)
    (hOwn : ∀ C : Block V,
      (x.tickOutput u (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C → 𝓒' C)
    (hPrev : LiveLocksOnFamilyAt M S A x 𝓒 s' u) :
    ∀ n' : M.N,
      LocksRevoked M S.P (x.tickInput u (M.voteTime S.C (s' + 2)))
        ((M.voteTime S.C (s' + 2) : ℕ) : Int) (s' + 2) n' →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput u (M.voteTime S.C (s' + 2)))
          ((M.voteTime S.C (s' + 2) : ℕ) : Int) e = true →
        ∃ D : Block V, 𝓒' D ∧ e.B.AncestorEq D := by
  intro n' hRevoke e he _
  rcases (revoked_lock_source M F U) S A x R s' u E hSkew hHon n' hRevoke e he with
      ⟨C, hC, heC⟩ | ⟨n₃, sent₃, hR₃, hA₃, e', he', hl', hee'⟩
  · exact ⟨C, hOwn C hC, heC⟩
  · obtain ⟨D, hD, he'D⟩ := hPrev n₃ sent₃ hR₃ hA₃ e' he' hl'
    exact ⟨D, hSub D hD, ancestorEq_trans hee' he'D⟩

/-- **The invariant restricted to a block holds for its ancestors.** When `HonestChainExtends S
Sched x Hon B s'` holds and `C` is `B` or an ancestor of `B`, `HonestChainExtends S Sched x Hon C
s'` holds.

Why: a descendant of `B` is a descendant of `C`; a block compatible with `B` is compatible with
`C` (`compatible_of_ancestorEq_compatible`).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Hon`: the members; `B`, `C`: the
  blocks; `s'`: the slot.

Read aloud: the slot invariant restricted to a block holds for every ancestor of that block. -/
theorem honestChainExtends_of_ancestorEq (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Hon : Finset V) (B C : Block V) (s' : ℕ)
    (hCB : C.AncestorEq B) (h : HonestChainExtends M S A x Hon B s') :
    HonestChainExtends M S A x Hon C s' := by
  refine ⟨fun u hu vote hs => ?_, fun w hw n' sent hR hA e he hl => ?_, fun v hv C' hC' => ?_⟩
  · obtain ⟨H, hH, hvt, hBH⟩ := h.1 u hu vote hs
    exact ⟨H, hH, hvt, ancestorEq_trans hCB hBH⟩
  · exact compatible_symm'
      (compatible_of_ancestorEq_compatible hCB (compatible_symm' (h.2.1 w hw n' sent hR hA e he hl)))
  · exact ancestorEq_trans hCB (h.2.2 v hv C' hC')

/-! ## Kit: the honest voters and the updaters -/

omit [RootOrder] in
/-- **Committee sleepiness gives the committee majority.** With `CommitteeSleepiness` from
`anchor` and slot `s + 1` starting at or after `anchor`, the committee of slot `s` has fewer than
twice the members it shares with `honestActiveAt M S Sched s`. Lemma 88's first conclusion, without
its validator and time.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `anchor`: the time from which committee sleepiness
  holds; `s`: the slot; `T`: the time up to which committee sleepiness is read (the update of slot
  `s`, `M.supportCutoff S.C (s + 1)`, is at most `T`).

Read aloud: under committee sleepiness from `anchor`, read up to a time `T` no earlier than the
update of slot `s`, the committee of slot `s` has fewer than twice the members it shares with
`honestActiveAt S Sched s`. -/
theorem committee_majority_of_sleepiness (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (anchor s : ℕ) {T : ℕ}
    (hSleepK : CommitteeSleepinessUntil M S A x anchor T) (hs : anchor ≤ M.slotStart S.C (s + 1))
    (hT : M.supportCutoff S.C (s + 1) ≤ T) :
    |S.P.committee s| < 2 * |S.P.committee s ∩ honestActiveAt M S A x s| := by
  have hK := hSleepK (s + 1) (by omega) hs hT
  rw [Nat.add_sub_cancel, Finset.inter_comm] at hK
  have h1 := Finset.card_sdiff_add_card_inter (S.P.committee s) (honestActiveAt M S A x s)
  omega

/-- **The votes of the first clause, as a function.** When every member of `Hs` is an honest
active validator of slot `s` in its committee, and the slot-`s` vote of every member is its vote
for a block it holds that is `C` or a descendant of `C`, then some `H : V → Block V` names, for
every member `u`, the block of a slot-`s` vote `u` put on the wire at its tick at the vote time of
slot `s`, a block `u` holds then that is `C` or a descendant of `C`.

Why: every member votes (`honest_active_votes`), and the clause names its block; `choose`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `Hs`: the voters;
  `C`: the block.

Read aloud: when every member of `Hs` is an honest active committee member of slot `s` and the first
clause names its vote's block, some function names for every member the block of the vote it put on
the wire, a block it holds that is `C` or a descendant of `C`. -/
theorem voters_of_votes_clause (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (Hs : Finset V) (C : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hHs : ∀ u ∈ Hs, u ∈ honestActiveAt M S A x s ∧ u ∈ S.P.committee s)
    (hC1 : ∀ u ∈ Hs, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s)).tree,
        vote = GoldfishVote.mk u s H_u.root ∧ C.AncestorEq H_u) :
    ∃ H : V → Block V, ∀ u ∈ Hs,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ C.AncestorEq (H u) := by
  have hvote : ∀ u ∈ Hs, ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H_u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ C.AncestorEq H_u := by
    intro u hu
    obtain ⟨i, vote, hl, -, -, hsent⟩ :=
      (honest_active_votes M F U) S A x R s u E hSkew
        (hHs u hu).1 (hHs u hu).2
    obtain ⟨H_u, hHT, hvt, hBH⟩ := hC1 u hu vote ⟨i, hl, hsent⟩
    subst hvt
    exact ⟨H_u, ⟨i, hl, hsent⟩, hHT, hBH⟩
  choose H hH using hvote
  refine ⟨fun u => if h : u ∈ Hs then H u h else C, fun u hu => ?_⟩
  simp only [dif_pos hu]
  exact hH u hu

/-- **The updaters' confirmations extend the chain family.** In an execution where every time is
reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`,
a root names one block among what honest validators hold, a block
reaches a validator only once it holds the parent, and nobody votes in an honest validator's name:
if `GST` is at most the vote time of slot `s`; `Hon` is a set of honest active validators of slot
`s` with more than half of the committee of slot `s`; `ChainInvFor M S Sched x Hon 𝓒 s` holds; `v`
is an updater of slot `s`; and `v`'s finalized block before the support cutoff of slot `s + 1` is
compatible with every block of `𝓒` — then every block of `𝓒` is an ancestor of, or equal to, the
confirmation of slot `s` that `v` holds right after that cutoff.

Why: Lemma 78 at `v`, with the honest voters `S.P.committee s ∩ Hon`, each voting for a block it
holds on the block's chain (the first clause of the invariant), and the voters of `v`'s pool from
the committee (the node invariant).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot; `Hon`: the voters; `𝓒`: the family; `v`: the updater.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C s`: Lemma 78,
which the proof calls at slot `s`, reads them up to the real time of `v`'s own tick to that cutoff.

Read aloud: every block of the family is an ancestor of, or equal to, the confirmation of slot `s`
an updater holds right after the support cutoff of slot `s + 1`. -/
theorem chainInvFor_updater_confirmation (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hon : Finset V) (𝓒 : Block V → Prop)
    (v : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHon : Hon ⊆ honestActiveAt M S A x s)
    (hCommittee : |S.P.committee s| < 2 * |S.P.committee s ∩ Hon|)
    (hInv : ChainInvFor M S A x Hon 𝓒 s)
    (hv : v ∈ updaterAt M S A x s)
    (hF : ∀ C : Block V, 𝓒 C →
      (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.compatible C = true) :
    ∀ C : Block V, 𝓒 C → ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C' →
      C.AncestorEq C' := by
  intro C hC
  -- the voters: the committee members of `Hon`, each voting for a block it holds on `C`'s chain
  obtain ⟨H, hH⟩ := (voters_of_votes_clause M F U) S A x R s (S.P.committee s ∩ Hon) C E hSkew
    (fun u hu => ⟨hHon (Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hu).1⟩)
    (fun u hu => (hInv C hC).1 u (Finset.mem_inter.1 hu).2)
  -- `v`'s tick to the support cutoff of slot `s` (inside its reader), for the roots
  obtain ⟨kR, hkR, -⟩ := (updater_reader_gives_core_window M F U) x R E hΔs hSkew hv
  -- each voter is awake and honest from the duty window's start of slot `s + 1` up to its tick to the support cutoff
  -- of slot `s + 1` (its reader of `activeAt`, moved later)
  have hUpdU : ∀ u ∈ S.P.committee s ∩ Hon, u ∈ updaterAt M S A x s := fun u hu =>
    Activity.mem_activeThroughoutToTick_of_le (duty_window_start_mono S (Nat.le_succ s))
      (E.mem_activeThroughoutToTick_of_awakeThroughoutToTick
        (Finset.mem_sdiff.1 (hHon (Finset.mem_inter.1 hu).2)).1)
  exact (GoldilocksCorrectness.Record.Statements.Executions.lem78_update_confirmation_extends_voter_majority_chain M F U)
    S A x R GST s (S.P.committee s ∩ Hon) H C v E hNet hSkew hRedeliver Sy hΔs
    ((roots_at_own_tick_of_per_tick M F) x E hRoots hkR) hParent hOwner hGST
    (fun u hu => ⟨(Finset.mem_inter.1 hu).1,
      (not_mem_corrupted_tickStep_of_outside_at_honest_ticks M F) x E hv
        (fun hX => (Finset.mem_sdiff.1 (hHon (Finset.mem_inter.1 hu).2)).2 (Finset.mem_union_right _ hX)),
      (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
    (fun u hu => (holder_window_of_updater_reader M F U) x R E hΔs hSkew hGST (hUpdU u hu))
    (by
      unfold Trace.tickInput
      exact (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
        ((GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_exec M F) S A x R E _ v s)
        ((committee_sdiff_lt M F) _ _ hCommittee))
    hv (hF C hC)

/-! ## The chain step -/

/-- **The chain step.** The proof; the audited statement is in
`Statements/Executions/HonestChainAfterHealingStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s'`: the slot of the step;
- `Hon`: the voters of slot `s'`; `Hon'`: the members of slot `s' + 1`; `Upd`: the updaters whose
  confirmations of slot `s'` join the family; `𝓒`: the family.

Roots name blocks until `M.supportCutoff S.C (s' + 1)`, where Lemma 36b reads them, and up to every
validator's tick to a clock value at most that cutoff: Lemmas 78 and
32 read them up to the updaters' own ticks to the cutoff, which can come after its real time; Lemma 26b
reads them up to the voter's tick to the support cutoff of slot `s'`.

Read aloud: the honest chain grows by the confirmations of slot `s'`: when the voters of slot `s'`
satisfy the invariant for every block of the family and their live locks are on its chain, the
members of slot `s' + 1` satisfy it for every block of the family and every block of a new
confirmation's chain. -/
theorem lem89s_chain_step (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s' : ℕ) (Hon Hon' Upd : Finset V)
    (𝓒 : Block V → Prop)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s' + 1)))
    -- roots name blocks also up to every validator's tick to a clock value at most the support cutoff of slot `s' + 1`
    -- ('s shape: Lemmas 78 and 32 read them up to the updaters' own ticks to that cutoff)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s')
    (hHon : Hon ⊆ honestActiveAt M S A x s')
    (hHon' : Hon' ⊆ honestActiveAt M S A x (s' + 1))
    (hUpd : Upd ⊆ updaterAt M S A x s')
    (hHonUpd : Hon' ⊆ Upd)
    (hCommittee : |S.P.committee s'| < 2 * |S.P.committee s' ∩ Hon|)
    (hCommittee' : |S.P.committee (s' + 1)| < 2 * |S.P.committee (s' + 1) ∩ Hon'|)
    (hInv : ChainInvFor M S A x Hon 𝓒 s')
    (hNew : ∀ u ∈ Hon', u ∈ Hon ∨
      ∀ e ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).lockEntries,
        M.is_live (x.tickInput u (M.voteTime S.C (s' + 1)))
          ((M.voteTime S.C (s' + 1) : ℕ) : Int) e = false)
    (hLocks : ∀ u ∈ Hon, LiveLocksOnFamilyAt M S A x 𝓒 s' u)
    (hConfExt : ∀ C : Block V, 𝓒 C → ∀ v ∈ Upd, ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' →
      C.AncestorEq C')
    (hStep : ∀ C : Block V, (𝓒 C ∨ ∃ v ∈ Upd,
        (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C) →
      ∀ w ∈ Hon', StepFrameAt M S A x C s' w) :
    ChainInvFor M S A x Hon' (fun C => 𝓒 C ∨ ∃ v ∈ Upd, ∃ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' ∧
      C.AncestorEq C') (s' + 1) := by
  -- the blocks of the family and the new confirmations themselves; their ancestors follow
  suffices hcore : ∀ B : Block V, (𝓒 B ∨ ∃ v ∈ Upd,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some B) →
      HonestChainExtends M S A x Hon' B (s' + 1) by
    rintro B (hB | ⟨v, hv, C', hsv, hBC'⟩)
    · exact hcore B (Or.inl hB)
    · exact (honestChainExtends_of_ancestorEq M F) S A x Hon' C' B (s' + 1) hBC'
        (hcore C' (Or.inr ⟨v, hv, hsv⟩))
  intro B hB0
  have hB : 𝓒 B ∨ ∃ v ∈ Upd, ∃ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' ∧
      B.AncestorEq C' :=
    hB0.imp id (fun ⟨v, hv, hsv⟩ => ⟨v, hv, B, hsv, ancestorEq_refl B⟩)
  -- the times, as reals
  have hA0 := E.ahead_nonneg
  have hB0' := E.behind_nonneg
  obtain ⟨hv0, hc0, hf0, hs0, -, hk8, hΔ⟩ := (slot_times M F U) S s'
  obtain ⟨hv1, hc1, -, hs1, -, -, -⟩ := (slot_times M F U) S (s' + 1)
  obtain ⟨hv2, hc2, -, -, -, -, -⟩ := (slot_times M F U) S (s' + 1 + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s'
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hc0R : ((M.supportCutoff S.C s' : ℕ) : ℝ) = 4 * Δ S * s' + 2 * Δ S := by
    rw [hc0, hss]; push_cast; ring
  have hf0R : ((M.viewFreeze S.C s' : ℕ) : ℝ) = 4 * Δ S * s' + 3 * Δ S := by
    rw [hf0, hss]; push_cast; ring
  have hv1R : ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 5 * Δ S := by
    rw [hv1, hs0, hss]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 6 * Δ S := by
    rw [hc1, hs0, hss]; push_cast; ring
  have hv2R : ((M.voteTime S.C (s' + 1 + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 9 * Δ S := by
    rw [hv2, hs1, hs0, hss]; push_cast; ring
  have hc2R : ((M.supportCutoff S.C (s' + 1 + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 10 * Δ S := by
    rw [hc2, hs1, hs0, hss]; push_cast; ring
  have hdw1 := duty_window_start_real S (s' + 1)
  push_cast at hdw1
  have hdw2 := duty_window_start_real S (s' + 1 + 1)
  push_cast at hdw2
  have hdle2 := (duty_window_start_le_real M F U) S (s' + 1 + 1)
  have hdN2 : M.dutyWindowStart S.C (s' + 1 + 1) ≤ M.slotStart S.C (s' + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S (s' + 1)
  have hdN2R : ((M.dutyWindowStart S.C (s' + 1 + 1) : ℕ) : ℝ) ≤ 4 * Δ S * s' + 4 * Δ S := by
    have : ((M.dutyWindowStart S.C (s' + 1 + 1) : ℕ) : ℝ) ≤ ((M.slotStart S.C (s' + 1) : ℕ) : ℝ) := by
      exact_mod_cast hdN2
    rw [hs0, hss] at this; push_cast at this; linarith
  have hmΔ : (Δ S : ℝ) ≤ (max (Δ S) Δs : ℝ) := le_max_left _ _
  have hmΔs : (Δs : ℝ) ≤ (max (Δ S) Δs : ℝ) := le_max_right _ _
  -- `hGST` bounds the sync delay by the support cutoff of slot `s'`
  have hΔsle : Δs ≤ M.supportCutoff S.C s' := by have := le_max_right (Δ S) Δs; omega
  have hΔsleR : (Δs : ℝ) ≤ 4 * Δ S * s' + 2 * Δ S := by
    rw [← hc0R]; exact_mod_cast hΔsle
  have hmax1 : max (Δ S) Δs ≤ M.supportCutoff S.C (s' + 1) := by
    have := le_max_right (Δ S) Δs; have := le_max_left (Δ S) Δs
    rcases max_choice (Δ S) Δs with h | h <;> rw [h] <;> omega
  have hmaxR : ((max (Δ S) Δs : ℕ) : ℝ) = (max (Δ S) Δs : ℝ) := by push_cast; rfl
  -- the windows
  have hHonW : ∀ u ∈ Hon, u ∈ A.activeThroughoutToTick x (duty_window_start S.C s')
      (M.supportCutoff S.C (s' + 1)) := fun u hu => (honestActiveAt_window M F) S A s' u E (hHon hu)
  have hHon'W : ∀ u ∈ Hon', u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s' + 1))
      (M.supportCutoff S.C (s' + 1 + 1)) := fun u hu => (honestActiveAt_window M F) S A (s' + 1) u E (hHon' hu)
  have hHonU : ∀ u ∈ Hon, u ∈ updaterAt M S A x s' := fun u hu =>
    Activity.mem_activeThroughoutToTick_of_le (duty_window_start_mono S (Nat.le_succ s')) (hHonW u hu)
  have hHon'U : ∀ u ∈ Hon', u ∈ updaterAt M S A x (s' + 1) := fun u hu =>
    Activity.mem_activeThroughoutToTick_of_le (duty_window_start_mono S (Nat.le_succ (s' + 1))) (hHon'W u hu)
  have hRootsN : ∀ {k : ℕ} {u : V} {c : ℕ}, x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time (x.tickStep u c)) := fun {k u c} hk hc => by
    rw [(tickStep_eq_of_lbl M) x E hk]; exact hRootsTick k u c hk hc
  -- the live locks of a member after its revocation of slot `s' + 1`
  have hLk : ∀ u ∈ Hon', ∀ (n₃ : M.N) (sent₃ : List (NamedObject V)),
      .ok (n₃, sent₃) ∈ M.tick S.C S.P S.X (x.tickInput u (M.voteTime S.C (s' + 1)))
        ((M.voteTime S.C (s' + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput u (M.voteTime S.C (s' + 1))) (s' + 1) →
      ∀ e ∈ M.lockEntries n₃,
        M.is_live (x.tickInput u (M.voteTime S.C (s' + 1)))
          ((M.voteTime S.C (s' + 1) : ℕ) : Int) e = true →
        (∀ C : Block V, 𝓒 C → e.B.compatible C = true) ∧ ∃ D : Block V, 𝓒 D ∧ e.B.AncestorEq D := by
    intro u hu n₃ sent₃ hR hA e he hl
    rcases hNew u hu with hu0 | hfree
    · exact ⟨fun C hC => (hInv C hC).2.1 u hu0 n₃ sent₃ hR hA e he hl,
        hLocks u hu0 n₃ sent₃ hR hA e he hl⟩
    · exact ((revoke_locks_empty_of_lockFree M F) S A x _ (s' + 1) _ n₃ (Nat.le_add_left 1 s')
        hfree ((locksRevoked_of_voteTime_outcome M F U) S A x R E (s' + 1) u n₃ sent₃ hR hA) e
        he).elim
  -- the first clause at slot `s' + 1`
  have hClause1 : ∀ u ∈ Hon', ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).tree,
        vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ B.AncestorEq H_u := by
    intro u hu vote hSend
    obtain ⟨iS, hiS, -⟩ := id hSend
    have hF := hStep B hB0 u hu
    rcases hB with hBold | ⟨v, hv, C', hsv, hBC'⟩
    · -- a block of the family: Lemma 26b over the voters of slot `s'`
      obtain ⟨H, hH⟩ := (voters_of_votes_clause M F U) S A x R s' (S.P.committee s' ∩ Hon) B E hSkew
        (fun u' hu' => ⟨hHon (Finset.mem_inter.1 hu').2, (Finset.mem_inter.1 hu').1⟩)
        (fun u' hu' => (hInv B hBold).1 u' (Finset.mem_inter.1 hu').2)
      obtain ⟨kR, hkR, hkRw⟩ := (updater_reader_gives_core_window M F U) x R E hΔs hSkew
        (hUpd (hHonUpd hu))
      exact (GoldilocksCorrectness.Record.Statements.Executions.lem26b_goldfish_vote_extends_voter_majority_block_held M F U)
        S A x R GST s' (S.P.committee s' ∩ Hon) H B u vote E hNet hSkew hRedeliver Sy hΔs
        (hRootsN hkR (by omega)) hParent hOwner hGST
        (fun u' hu' => ⟨(Finset.mem_inter.1 hu').1,
          (not_mem_corrupted_tickStep_of_outside_at_honest_ticks_of_lbl M F) x E hiS
            ((outside_at_honest_ticks_of_mem_activeThroughoutToTick M F) x R E
              (hHonW u' (Finset.mem_inter.1 hu').2) (by rw [hv1R, hc1R]; linarith)),
          (hH u' hu').1, (hH u' hu').2.1, (hH u' hu').2.2⟩)
        (fun votes sv hC => by
          unfold Trace.tickInput at hC
          exact (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
            ((countedVotes_committee_st M F) S A x R E _ s' u votes sv hC) ((committee_sdiff_lt M F) _ _ hCommittee))
        (fun u' hu' => (holder_window_of_updater_reader M F U) x R E hΔs hSkew hGST
          (hHonU u' (Finset.mem_inter.1 hu').2))
        ⟨kR, hkR, hkRw⟩ hF.1 hF.2.1
        (fun n₃ sent₃ hR hA e he hl => (hLk u hu n₃ sent₃ hR hA e he hl).1 B hBold) hSend
    · -- a block of a new confirmation: Lemma 36b at that confirmation
      obtain ⟨n'', sent'', hrun'', hAw'', hsave⟩ :=
        (update_of_saved_confirmation_of_updater M F U) S A x R s' v C' E (hUpd hv) hsv
      have hUp := (confirmationUpdated_of_cutoff_tickInput M F U) x R s' v n'' sent'' hrun'' hAw''
      have hFC' := hStep C' (Or.inr ⟨v, hv, hsv⟩) u hu
      have hwVF : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s' + 1)) (M.viewFreeze S.C s') :=
        (mem_activeThroughoutToTick_of_inside M F) R E (hHon'W u hu) (by omega)
          (by rw [hdw1, hf0R]; linarith) (by rw [hf0R, hc2R]; linarith)
      have hw₀ : u ∈ A.activeThroughout x ((M.supportCutoff S.C (s' + 1) - max (Δ S) Δs : ℕ) : ℝ)
          (((M.supportCutoff S.C (s' + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
        have h := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E (hHon'W u hu)
          (a' := M.supportCutoff S.C (s' + 1) - max (Δ S) Δs)
          (e := M.supportCutoff S.C (s' + 1) - max (Δ S) Δs + Δs)
          (by rw [hdw1, Nat.cast_sub hmax1, hmaxR, hc1R]; linarith)
          (by
            have hle : M.supportCutoff S.C (s' + 1) - max (Δ S) Δs + Δs ≤ M.supportCutoff S.C (s' + 1) := by
              have := le_max_right (Δ S) Δs; omega
            have hleR : ((M.supportCutoff S.C (s' + 1) - max (Δ S) Δs + Δs : ℕ) : ℝ) ≤
                ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) := by exact_mod_cast hle
            rw [hc1R] at hleR; rw [hc2R]; linarith)
        push_cast at h
        exact h
      obtain ⟨H_u, hHT, hvt, hCH⟩ := (lem36b_confirmed_block_extended_held M F U) S A x R GST s' C' v u
        n'' vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent (by omega) (hUpd hv)
        (duty_window_start S.C (s' + 1))
        (by
          have h3 : max (3 * Δ S) Δs ≤ M.viewFreeze S.C s' := by
            rcases max_choice (3 * Δ S) Δs with h | h <;> rw [h] <;> omega
          rw [Nat.cast_sub h3, hdw1, hf0R]
          rcases max_choice (3 * Δ S) Δs with h | h <;> rw [h] <;> push_cast
          · linarith
          · linarith)
        hwVF hw₀ hUp hsave hFC'.1 hFC'.2.1
        (fun n₃ sent₃ hR hA e he hl => by
          obtain ⟨D, hD, heD⟩ := (hLk u hu n₃ sent₃ hR hA e he hl).2
          exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans heD (hConfExt D hD v hv C' hsv))))
        hSend
      exact ⟨H_u, hHT, hvt, ancestorEq_trans hBC' hCH⟩
  -- the second clause at slot `s' + 1`
  have hrefl : ∀ X : Block V, X.compatible X = true :=
    fun X => (compatible_iff _ _).2 (Or.inl (ancestorEq_refl X))
  have hClause2 : ∀ w ∈ Hon', ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s' + 1 + 1)))
        ((M.voteTime S.C (s' + 1 + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s' + 1 + 1))) (s' + 1 + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s' + 1 + 1)))
          ((M.voteTime S.C (s' + 1 + 1) : ℕ) : Int) e = true → e.B.compatible B = true := by
    intro w hw n' sent hrun hA e he _
    have hR := (locksRevoked_of_voteTime_outcome M F U) S A x R E (s' + 1 + 1) w n' sent hrun hA
    -- `w` is active from the duty window's start of slot `s' + 2` up to its tick to that slot's vote time
    have hwV : w ∈ A.activeThroughoutToTick x (M.dutyWindowStart S.C (s' + 1 + 1) : ℤ) (M.voteTime S.C (s' + 1 + 1)) := by
      have h1 := (mem_activeThroughoutToTick_of_inside M F) R E (hHon'W w hw) (c := M.voteTime S.C (s' + 1 + 1))
        (by omega) (by rw [hdw1, hv2R]; linarith) (by rw [hv2R, hc2R]; linarith)
      refine Activity.mem_activeThroughoutToTick_of_le ?_ h1
      have : ((duty_window_start S.C (s' + 1) : ℤ) : ℝ) ≤ ((M.dutyWindowStart S.C (s' + 1 + 1) : ℕ) : ℝ) := by
        rw [hdw1]; rw [hdw2] at hdle2; linarith
      exact_mod_cast this
    rcases (revoked_lock_source M F U) S A x R s' w E hSkew hwV n' hR e he with
        ⟨Cw, hCw, heC⟩ | ⟨n₃, sent₃, hR₃, hA₃, e', he', hl', hee'⟩
    · rcases hB with hBold | ⟨v, hv, C', hsv, hBC'⟩
      · exact compatible_of_ancestorEq_both heC (hConfExt B hBold w (hHonUpd hw) Cw hCw)
          (hrefl Cw)
      · have hw1 := hUpd (hHonUpd hw)
        have hv1' := hUpd hv
        obtain ⟨kw, hkw, -⟩ := Activity.mem_activeThroughoutToTick.1 hw1
        obtain ⟨kv, hkv, -⟩ := Activity.mem_activeThroughoutToTick.1 hv1'
        have h32 := (GoldilocksCorrectness.Record.Statements.Executions.lem32_saved_confirmations_compatible_state M F U)
          S A x R GST s' w v Cw C' E hNet hSkew hRedeliver Sy hΔs
          (by
            rcases max_choice (x.time (x.tickStep w (M.supportCutoff S.C (s' + 1))))
                (x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)))) with h | h <;> rw [h]
            · exact hRootsN hkw le_rfl
            · exact hRootsN hkv le_rfl)
          (by omega) hw1 hv1' hCw hsv
        exact compatible_of_ancestorEq_both heC hBC' h32
    · obtain ⟨hcomp, D, hD, he'D⟩ := hLk w hw n₃ sent₃ hR₃ hA₃ e' he' hl'
      rcases hB with hBold | ⟨v, hv, C', hsv, hBC'⟩
      · exact compatible_of_ancestorEq_compatible hee' (hcomp B hBold)
      · exact compatible_of_ancestorEq_both
          (ancestorEq_trans hee' (ancestorEq_trans he'D (hConfExt D hD v hv C' hsv))) hBC'
          (hrefl C')
  -- the third clause at slot `s' + 1`
  have hClause3 : ∀ v ∈ Hon', ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1 + 1))).savedConfirmation (s' + 1) = some C' →
      B.AncestorEq C' := by
    intro v hv
    obtain ⟨H, hH⟩ := (voters_of_votes_clause M F U) S A x R (s' + 1) (S.P.committee (s' + 1) ∩ Hon') B
      E hSkew
      (fun u hu => ⟨hHon' (Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hu).1⟩)
      (fun u hu => hClause1 u (Finset.mem_inter.1 hu).2)
    obtain ⟨kv, hkv, -⟩ := Activity.mem_activeThroughoutToTick.1 (hUpd (hHonUpd hv))
    exact (GoldilocksCorrectness.Record.Statements.Executions.lem78_update_confirmation_extends_voter_majority_chain M F U)
      S A x R GST (s' + 1) (S.P.committee (s' + 1) ∩ Hon') H B v E hNet hSkew hRedeliver Sy hΔs
      (hRootsN hkv le_rfl) hParent hOwner (by omega)
      (fun u hu => ⟨(Finset.mem_inter.1 hu).1,
        (not_mem_corrupted_tickStep_of_outside_at_honest_ticks M F) x E (hHon'W v hv)
          (fun hX => (Finset.mem_sdiff.1 (hHon' (Finset.mem_inter.1 hu).2)).2 (Finset.mem_union_right _ hX)),
        (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
      (fun u hu => (holder_window_of_updater_reader M F U) x R E hΔs hSkew (GST := GST) (by omega)
        (hHon'U u (Finset.mem_inter.1 hu).2))
      (by
        unfold Trace.tickInput
        exact (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
          ((GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_exec M F) S A x R E _ v (s' + 1))
          ((committee_sdiff_lt M F) _ _ hCommittee'))
      (hHon'U v hv) (hStep B hB0 v hv).2.2
  exact ⟨hClause1, hClause2, hClause3⟩

/-! ## Lemma 81b and Lemma 81 -/

/-- **Lemma 81b, the chain step after the healed slot.** The proof; the audited statement is in
`Statements/Executions/HonestChainAfterHealingStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the first slot of the chain; `s`: the slot of the step;
  `anchor`: the time from which committee sleepiness holds.

Roots name blocks until `M.supportCutoff S.C (s + 1)`, and up to every validator's tick to a clock value
at most that cutoff (`hRootsTick`): the chain step, which the proof calls at slot `s`, reads both.

Read aloud: `Inv s` and the lock invariant at slot `s` give `Inv (s + 1)`. -/
theorem lem81b_chain_step (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ s anchor : ℕ)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    -- roots name blocks also up to every validator's tick to a clock value at most the support cutoff of slot `s + 1`
    -- ('s shape: Lemmas 78 and 32 read them up to the updaters' own ticks to that cutoff)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hs₀ : s₀ ≤ s)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 2)))
    (hAnchor : anchor ≤ M.slotStart S.C (s + 1))
    (hInv : ChainInvFor M S A x (honestActiveAt M S A x s)
      (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hVoterFrame : ∀ w ∈ honestActiveAt M S A x (s + 1),
      VoterFrameOnChainAt M S A x s₀ (s + 1) w)
    (hUpdaterFrame : ∀ v ∈ updaterAt M S A x s, UpdaterFinalizedOnChainAt M S A x s₀ s v)
    (hUpdaterFrame' : ∀ w ∈ honestActiveAt M S A x (s + 1),
      UpdaterFinalizedOnChainAt M S A x s₀ (s + 1) w) :
    ChainInvFor M S A x (honestActiveAt M S A x (s + 1))
      (OnHonestChainBefore M S A x s₀ (s + 1)) (s + 1) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨hv0, hc0, -, hs0, -, hk8, hΔ⟩ := (slot_times M F U) S s
  obtain ⟨hv1, hc1, -, hs1, -, -, -⟩ := (slot_times M F U) S (s + 1)
  obtain ⟨-, hc2, -, -, -, -, -⟩ := (slot_times M F U) S (s + 1 + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hcs : M.supportCutoff S.C s ≤ M.supportCutoff S.C (s + 1) := by omega
  have hc0R : ((M.supportCutoff S.C s : ℕ) : ℝ) = 4 * Δ S * s + 2 * Δ S := by
    rw [hc0, hss]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 6 * Δ S := by
    rw [hc1, hs0, hss]; push_cast; ring
  have hv1R : ((M.voteTime S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 5 * Δ S := by
    rw [hv1, hs0, hss]; push_cast; ring
  have hc2R : ((M.supportCutoff S.C (s + 1 + 1) : ℕ) : ℝ) = 4 * Δ S * s + 10 * Δ S := by
    rw [hc2, hs1, hs0, hss]; push_cast; ring
  have hdw1 := duty_window_start_real S (s + 1)
  push_cast at hdw1
  have hCom := (committee_majority_of_sleepiness M F) S A x anchor s hSleepK hAnchor
    ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))
  have hCom' := (committee_majority_of_sleepiness M F) S A x anchor (s + 1) hSleepK
    (le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (Nat.le_succ (s + 1)))) le_rfl
  -- every member of slot `s + 1` ticks to the vote time of slot `s + 1`, inside its reader ( reads
  -- `VoterFrameOnChainAt` at that tick)
  have hVT : ∀ w ∈ honestActiveAt M S A x (s + 1), ∃ k : ℕ, x.lbl k = Event.tick w (M.voteTime S.C (s + 1)) := by
    intro w hw
    have h1 : 1 ≤ M.voteTime S.C (s + 1) := by omega
    have hr := (mem_activeThroughoutToTick_of_inside M F) R E ((honestActiveAt_window M F) S A (s + 1) w E hw) h1
      (by rw [hdw1, hv1R]; linarith) (by rw [hv1R, hc2R]; linarith)
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hr
    exact ⟨k, hk⟩
  have hstep := (lem89s_chain_step M F U) S A x R GST s (honestActiveAt M S A x s)
    (honestActiveAt M S A x (s + 1)) (updaterAt M S A x s) (OnHonestChainBefore M S A x s₀ s)
    E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hOwner hGST (subset_refl _) (subset_refl _)
    (subset_refl _) ((honestActiveAt_succ_subset_updaterAt M F U) S A s R E hSkew) hCom hCom' hInv
    (fun u hu => (mem_honestActiveAt_or_lockFree M F U) S A s u R E hSkew hu)
    hLocks
    (fun C hC v hv => (chainInvFor_updater_confirmation M F U) S A x R GST s (honestActiveAt M S A x s)
      (OnHonestChainBefore M S A x s₀ s) v E hNet hSkew hRedeliver Sy hΔs
      ((per_tick_roots_of_roots_until M F) x E hRoots (c₀ := M.supportCutoff S.C s)
        (by rw [hc0R]; push_cast; rw [hc1R]; linarith))
      hParent hOwner hGST (subset_refl _) hCom hInv hv (fun D hD => hUpdaterFrame v hv D hD) C hC)
    (fun C hC w hw => by
      have hC' : OnHonestChainBefore M S A x s₀ (s + 1) C := by
        rcases hC with ⟨s', hs', hAt⟩ | ⟨v, hv, hsv⟩
        · exact ⟨s', by omega, hAt⟩
        · exact ⟨s, by omega, hs₀, v, hv, C, hsv, ancestorEq_refl C⟩
      obtain ⟨k, hk⟩ := hVT w hw
      have hti : x.tickInput w (M.voteTime S.C (s + 1)) = x.st k w := by
        unfold Trace.tickInput
        rw [(tickStep_eq_of_lbl M) x E hk]
      have hVF := hVoterFrame w hw C hC' k hk
      rw [← hti] at hVF
      exact ⟨hVF.1, hVF.2, hUpdaterFrame' w hw C hC'⟩)
  intro B hB
  apply hstep B
  obtain ⟨s', hs', hAt⟩ := hB
  rcases Nat.lt_or_ge s' s with hlt | hge
  · exact Or.inl ⟨s', hlt, hAt⟩
  · have hss' : s' = s := by omega
    subst hss'
    obtain ⟨-, v, hv, C', hsv, hBC'⟩ := hAt
    exact Or.inr ⟨v, hv, C', hsv, hBC'⟩

/-- **The lock invariant at the healed slot.** When `B₀`'s slot is at least `s₀` and every live
lock entry of a node state `n₃` that `u`'s revocation of slot `s₀ + 1` can leave (`LocksRevoked`)
is compatible with `B₀`, every such entry is on
`B₀` or an ancestor of `B₀`.

Why: such an entry is on an ancestor of the block an update of a slot `s₁ + 1` at most `s₀` locked
(Lemmas 38 and 39), a block `u` held at that update's support cutoff, of slot at most `s₁ + 1`. A
strict descendant of `B₀` has a slot greater than `B₀`'s, so compatible means `B₀` or an ancestor.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `B₀`: the
  block; `u`: the validator; `n₃`: the node state the revocation leaves.

The landed statement reads the answer of the revocation; the twin reads every node state the
revocation can leave (`LocksRevoked`), the form of Lemma 79b's twin, which recovers the landed
statement at every answer; a caller holding an outcome of the tick at a vote time, from a state
awake for the slot, reaches it by `locksRevoked_of_voteTime_outcome`.

Read aloud: when every live lock entry `u`'s revocation of slot `s₀ + 1` leaves is compatible with
`B₀`, and `B₀`'s slot is at least `s₀`, every such entry is on `B₀` or an ancestor of `B₀`. -/
theorem liveLocksOnFamilyAt_base (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ : ℕ) (B₀ : Block V) (u : V) (n₃ : M.N)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hB₀slot : s₀ ≤ B₀.slot)
    (hRevoke : LocksRevoked M S.P (x.tickInput u (M.voteTime S.C (s₀ + 1)))
      ((M.voteTime S.C (s₀ + 1) : ℕ) : Int) (s₀ + 1) n₃)
    (hCompat : ∀ e ∈ M.lockEntries n₃,
      M.is_live (x.tickInput u (M.voteTime S.C (s₀ + 1)))
        ((M.voteTime S.C (s₀ + 1) : ℕ) : Int) e = true → e.B.compatible B₀ = true) :
    ∀ e ∈ M.lockEntries n₃,
      M.is_live (x.tickInput u (M.voteTime S.C (s₀ + 1)))
        ((M.voteTime S.C (s₀ + 1) : ℕ) : Int) e = true →
      ∃ D : Block V, D.AncestorEq B₀ ∧ e.B.AncestorEq D := by
  intro e he hl
  refine ⟨B₀, ancestorEq_refl B₀, ?_⟩
  rcases (compatible_iff _ _).1 (hCompat e he hl) with h | hB₀e
  · exact h
  -- `B₀` an ancestor of `e`'s block: they are equal, `e`'s block having slot at most `s₀`; `e`
  -- came from an entry `e₁` of `u`'s state then, on a descendant of its block (`LocksRevoked` at a
  -- slot after slot `0`)
  rcases hRevoke with ⟨h0, -⟩ | ⟨-, hmv, -⟩
  · exact absurd h0 (Nat.succ_ne_zero _)
  obtain ⟨e₁, he₁', -, -, hmov⟩ := hmv e he
  have hee₁ : e.B.AncestorEq e₁.B := hmov.1.2.2.1
  -- where `e₁` comes from (Lemma 39 at the step of `u`'s tick to the vote time): `u`'s update of a
  -- slot `s₁ + 1` at its tick to the support cutoff `c₁`, at an earlier step
  obtain ⟨s₁, -, hk₁, hl₁, ⟨τ, hτ, hτle⟩, h39⟩ :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem39_lock_entry_provenance M F U) S A x R
      (x.tickStep u (M.voteTime S.C (s₀ + 1))) u e₁ E he₁'
  obtain ⟨n₁, sent₁, hrun₁, hAw₁, -⟩ :=
    (update_state_of_tick M F U) S A x R s₁ u E hl₁ ⟨τ, hτ, hτle⟩
  obtain ⟨e₀, -, -, he₀T, -, -, -, he₁e₀, -⟩ := h39 n₁ sent₁ hrun₁ hAw₁
  have hee₀ := ancestorEq_trans hee₁ he₁e₀
  have he₀T' : e₀.B ∈ (x.st (x.tickStep u (M.supportCutoff S.C (s₁ + 1))) u).tree :=
    (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 he₀T).1
  have hu₁ : u ∉ A.corrupted (x.tickStep u (M.supportCutoff S.C (s₁ + 1))) :=
    E.not_mem_corrupted_of_tick hl₁
  -- the slot of a block of `u`'s tree at its tick to `c₁` is at most the slot of `c₁`: the clock
  -- value there is less than `c₁`
  have hslot₀ : e₀.B.slot ≤ s₁ + 1 := by
    have hcs := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout
      F.sched) S s₁
    have h1 := (slot_le_clockValue_of_mem_tree M F) R E hu₁ he₀T'
    have h2 := (clockValue_lt_of_tick_awakeSince_some M F) R E hl₁ (by omega) hτ
    have h3 : S.C.slot ((x.clockValue (x.tickStep u (M.supportCutoff S.C (s₁ + 1))) u : ℕ) : Int) ≤
        S.C.slot ((M.supportCutoff S.C (s₁ + 1) : ℕ) : Int) :=
      GoldilocksCorrectness.Proofs.Routines.slot_mono_int S (by exact_mod_cast h2.le)
    have hc1 : S.C.slot ((M.supportCutoff S.C (s₁ + 1) : ℕ) : Int) = s₁ + 1 := by
      rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
        ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
        hcs.1]
    exact h1.trans (h3.trans hc1.le)
  -- the tick to `c₁` is before the tick to the vote time of slot `s₀ + 1`, so `c₁` is at most that
  -- vote time (`clock_mono`), and `s₁ + 1 ≤ s₀`
  have hexT : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s₀ + 1)) := by
    by_contra hno
    have h0 : x.tickStep u (M.voteTime S.C (s₀ + 1)) = 0 := by
      unfold Trace.tickStep
      rw [dif_neg hno]
    omega
  have hlT := x.lbl_tickStep hexT
  have hcT : M.supportCutoff S.C (s₁ + 1) ≤ M.voteTime S.C (s₀ + 1) :=
    E.clock_mono _ _ u _ _ hk₁ (E.not_mem_corrupted_of_tick hlT) (Or.inl hl₁) (Or.inl hlT)
  have hs₁ : s₁ + 1 ≤ s₀ := by
    by_contra h
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show s₀ + 1 ≤ s₁ + 1 by omega)
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1)
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
      (s₁ + 1)
    have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₁ + 1)
    have hΔ := one_le_Δ S
    omega
  have hBe₀ := ancestorEq_trans hB₀e hee₀
  by_cases hEq : B₀ = e₀.B
  · rw [hEq]
    exact hee₀
  · -- the tree of `u`'s state is closed under parents with earlier slots (the node invariant)
    have hTC : TreeClosed M S.P S.X (x.st (x.tickStep u (M.supportCutoff S.C (s₁ + 1))) u) :=
      F.nd.nodeInv_treeClosed
        (lem11_node_invariant M F S A x R E (x.tickStep u (M.supportCutoff S.C (s₁ + 1))) u hu₁).1
    have hlt := (slot_lt_of_ancestorEq_of_treeClosed_node M F) hTC he₀T' hBe₀ hEq
    have h2 : B₀.slot < s₁ + 1 := lt_of_lt_of_le hlt hslot₀
    exact absurd (lt_of_le_of_lt hB₀slot h2) (by omega)

/-- **Two blocks on the honest chain are compatible.** The proof; the audited statement is in
`Statements/Executions/HonestChainAfterHealingStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot; `B`, `B'`:
  the blocks.

Read aloud: two blocks on the honest chain are on one chain. -/
theorem onHonestChain_compatible (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (s₀ : ℕ) (B B' : Block V)
    (hChain : ConfirmationsChain M S A x s₀)
    (hB : OnHonestChain M S A x s₀ B) (hB' : OnHonestChain M S A x s₀ B') :
    B.compatible B' = true := by
  obtain ⟨s, hs, v, hv, C, hC, hBC⟩ := hB
  obtain ⟨s', hs', v', hv', C', hC', hBC'⟩ := hB'
  have hcc : C.compatible C' = true := by
    rcases Nat.lt_trichotomy s s' with hlt | heq | hgt
    · exact (compatible_iff _ _).2
        (Or.inl ((hChain s s' v v' C C' hs hlt.le hv hv' hC hC').1 hlt))
    · exact (hChain s s' v v' C C' hs heq.le hv hv' hC hC').2 heq
    · exact (compatible_iff _ _).2
        (Or.inr ((hChain s' s v' v C' C hs' hgt.le hv' hv hC' hC).1 hgt))
  exact compatible_of_ancestorEq_both hBC hBC' hcc

/-- **The lock step's window, from an honest active validator of slot `s + 1`.** A validator of
`honestActiveAt M S A x (s + 1)` is active from its tick to a clock value at most the duty window's start of slot `s + 2`
up to its tick to the vote time of slot `s + 2` (`A.activeThroughoutToTick x (dutyWindowStart (s + 2)) (voteTime (s + 2))`).

Why: it is active from the duty window's start of slot `s + 1` up to its tick to the support cutoff of slot `s + 2`
(`honestActiveAt_window`); the vote time of slot `s + 2` is one delay before that cutoff and three after the support cutoff
of slot `s + 1`, so the window ends at its tick to the vote time (`mem_activeThroughoutToTick_of_le_end_int`, the two
clock bounds less than one delay), and a later window start is read by `Activity.mem_activeThroughoutToTick_of_le`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, its facts and the environment's facts; `s`: the slot;
  `u`: the validator.

Read aloud: an honest active validator of slot `s + 1` is active from the duty window's start of slot `s + 2` up to its
tick to the vote time of slot `s + 2`. -/
theorem lockStep_window_of_honestActiveAt (U : UniformSchedule M.toSlotLayout) (S : Setup V) (A : Activity V)
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (s : ℕ) {u : V} (hu : u ∈ honestActiveAt M S A x (s + 1)) :
    u ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (s + 2) : ℕ) : ℤ) (M.voteTime S.C (s + 2)) := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hwin := (honestActiveAt_window M F) S A (s + 1) u E hu
  have hc2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1 + 1)
  have hvt1 : 1 ≤ M.voteTime S.C (s + 2) := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 2)
    omega
  have hds : duty_window_start S.C (s + 1) ≤ ((M.dutyWindowStart S.C (s + 2) : ℕ) : ℤ) := by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart
      M.toSlotLayout F.sched U) S (s + 1)
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S
      (show s + 1 ≤ s + 2 by omega)
    have h3 : ((M.dutyWindowStart S.C (s + 1) : ℕ) : ℤ) ≤ ((M.dutyWindowStart S.C (s + 2) : ℕ) : ℤ) := by
      exact_mod_cast h2
    exact le_trans h1 h3
  have hwin' : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.voteTime S.C (s + 2)) := by
    refine (mem_activeThroughoutToTick_of_le_end_int M) x R E hvt1 ?_ ?_ hwin
    · have h1 : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + 3 * Δ S ≤ ((M.voteTime S.C (s + 2) : ℕ) : ℝ) := by
        have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
        have h22 : M.voteTime S.C (s + 2) = M.voteTime S.C (s + 1) + 4 * Δ S :=
          (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S (s + 1)
        exact_mod_cast (show M.supportCutoff S.C (s + 1) + 3 * Δ S ≤ M.voteTime S.C (s + 2) by omega)
      have h2 : ((M.dutyWindowStart S.C (s + 1) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) := by
        exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_le_supportCutoff M.toSlotLayout F.sched U) S
          (by omega)
      have h3 := (duty_window_start_le_real M F U) S (s + 1)
      have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
      linarith
    · have h4 : ((M.supportCutoff S.C (s + 1 + 1) : ℕ) : ℝ) = ((M.voteTime S.C (s + 2) : ℕ) : ℝ) + Δ S := by
        rw [hc2]; push_cast; ring
      linarith
  exact Activity.mem_activeThroughoutToTick_of_le hds hwin'

/-- **Lemma 81's induction before a slot.** The proof; the audited statement is in
`Statements/Executions/HonestChainAfterHealingStatements.lean`. The induction of
`lem81_confirmations_chain`'s proof, stopped before the slot `n`: the frames are read only at the
slots `s` with `s₀ < s < n`, and the conclusion is for those slots.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `n`: the bound on the slots; `B₀`: the block every updater of slot `s₀`
  saved.

Roots name blocks until `M.supportCutoff S.C (n - 1)`: the conclusion at a slot `s` reads the chain
step at slot `s - 1` (`lem89s_chain_step` at `s₀`, then `lem81b_chain_step`), which takes blocks
as held up to `M.supportCutoff S.C s`, and `s ≤ n - 1`.

Read aloud: from the healed slot on and before slot `n`, every honest vote, live lock and
confirmation extends the chain so far, provided roots name blocks up to the support cutoff of slot
`n − 1` and `VoterFrameOnChainAt`, `UpdaterFinalizedOnChainAt` hold at the slots before `n`. -/
theorem lem81_inv_before (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor n : ℕ) (B₀ : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (n - 1)))
    -- roots name blocks also up to the real time of every validator's tick to a clock value at most the
    -- support cutoff of slot `n − 1`
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (n - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C n))
    (hAnchor : anchor ≤ M.slotStart S.C (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt M S A x s₀,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀)
    (hVoterFrame : ∀ s : ℕ, s₀ < s → s < n → ∀ w ∈ honestActiveAt M S A x s,
      VoterFrameOnChainAt M S A x s₀ s w)
    (hUpdaterFrame : ∀ s : ℕ, s₀ < s → s < n → ∀ v ∈ updaterAt M S A x s,
      UpdaterFinalizedOnChainAt M S A x s₀ s v) :
    ∀ s : ℕ, s₀ < s → s < n →
      ChainInvFor M S A x (honestActiveAt M S A x s)
        (OnHonestChainBefore M S A x s₀ s) s ∧
      ∀ u ∈ honestActiveAt M S A x s,
        LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u := by
  -- nothing to show unless a slot lies strictly between `s₀` and `n`
  by_cases hn₀ : s₀ + 1 < n
  swap
  · intro s h1 h2; omega
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  -- the support cutoff grows with the slot
  have hcm : ∀ a b : ℕ, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun a b h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  -- the two roots rows at the support cutoff of slot `s + 1`, for every `s + 1 ≤ n − 1`
  have hRootsS : ∀ s : ℕ, s + 1 ≤ n - 1 → RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)) := fun s hs =>
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by exact_mod_cast hcm _ _ hs) hRoots
  have hRootsTickS : ∀ s : ℕ, s + 1 ≤ n - 1 → ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c →
      c ≤ M.supportCutoff S.C (s + 1) → RootsNameBlocksUntil M A x (x.time k) := fun s hs k u c hk hc =>
    hRootsTick k u c hk (le_trans hc (hcm _ _ hs))
  -- the times and the counting
  have hΔ := one_le_Δ S
  have hGSTs : ∀ s : ℕ, s₀ ≤ s → GST + max (Δ S) Δs ≤ M.supportCutoff S.C s := fun s hs =>
    le_trans hGST (hcm _ _ hs)
  have hAnch : ∀ s : ℕ, s₀ ≤ s → anchor ≤ M.slotStart S.C (s + 1) :=
    fun s hs => le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  have hCom : ∀ s : ℕ, s₀ ≤ s → s < n →
      |S.P.committee s| < 2 * |S.P.committee s ∩ honestActiveAt M S A x s| :=
    fun s hs hsn => (committee_majority_of_sleepiness M F) S A x anchor s hSleepK (hAnch s hs) (hcm _ _ (by omega))
  have hNewAt : ∀ s : ℕ, ∀ u ∈ honestActiveAt M S A x (s + 1), u ∈ honestActiveAt M S A x s ∨
      ∀ e ∈ (x.tickInput u (M.voteTime S.C (s + 1))).lockEntries,
        M.is_live (x.tickInput u (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = false :=
    fun s u hu => (mem_honestActiveAt_or_lockFree M F U) S A s u R E hSkew hu
  -- `B₀` is on the chain at slot `s₀`
  obtain ⟨u₀, hu₀⟩ : (S.P.committee s₀ ∩ honestActiveAt M S A x s₀).Nonempty :=
    Finset.card_pos.1 (by have := hCom s₀ le_rfl (by omega); omega)
  have hv₀ : u₀ ∈ updaterAt M S A x s₀ :=
    (honestActiveAt_subset_updaterAt M F) S A x R E s₀ (Finset.mem_inter.1 hu₀).2
  have hB₀chain : ∀ C : Block V, C.AncestorEq B₀ → OnHonestChainBefore M S A x s₀ (s₀ + 1) C :=
    fun C hC => ⟨s₀, Nat.lt_succ_self s₀, le_rfl, u₀, hv₀, B₀, hBaseSaved u₀ hv₀, hC⟩
  -- the invariants at the healed slot
  have hBaseInv : ChainInvFor M S A x (honestActiveAt M S A x s₀) (fun D => D.AncestorEq B₀) s₀ :=
    fun C hC => (honestChainExtends_of_ancestorEq M F) S A x _ B₀ C s₀ hC hBase
  have hBaseLocks : ∀ u ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (fun D => D.AncestorEq B₀) s₀ u :=
    fun u hu n₃ sent₃ hrun hA => (liveLocksOnFamilyAt_base M F U) S A x R s₀ B₀ u n₃ E
      hB₀slot ((locksRevoked_of_voteTime_outcome M F U) S A x R E (s₀ + 1) u n₃ sent₃ hrun hA)
      (hBase.2.1 u hu n₃ sent₃ hrun hA)
  have hBaseConf : ∀ C : Block V, C.AncestorEq B₀ → ∀ v ∈ updaterAt M S A x s₀, ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some C' →
      C.AncestorEq C' := by
    intro C hC v hv C' hC'
    rw [hBaseSaved v hv] at hC'
    cases hC'
    exact hC
  -- the slot invariant and the lock invariant at every slot after the healed one and before `n`
  have hAll : ∀ s : ℕ, s₀ + 1 ≤ s → s < n →
      ChainInvFor M S A x (honestActiveAt M S A x s)
        (OnHonestChainBefore M S A x s₀ s) s ∧
      ∀ u ∈ honestActiveAt M S A x s,
        LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base =>
      intro hn
      -- the time facts of the members' ticks to the vote time of slot `s₀ + 1`
      obtain ⟨hv1, -, -, hs1, -, -, -⟩ := (slot_times M F U) S (s₀ + 1)
      obtain ⟨-, hc2, -, -, -, -, -⟩ := (slot_times M F U) S (s₀ + 1 + 1)
      have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s₀
      obtain ⟨-, -, -, hs0, -, hk8, -⟩ := (slot_times M F U) S s₀
      have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
      have hv1R : ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) = 4 * Δ S * s₀ + 5 * Δ S := by
        rw [hv1, hs0, hss]; push_cast; ring
      have hc2R : ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) = 4 * Δ S * s₀ + 10 * Δ S := by
        rw [hc2, hs1, hs0, hss]; push_cast; ring
      have hdw1 := duty_window_start_real S (s₀ + 1)
      push_cast at hdw1
      have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
      have hVT : ∀ w ∈ honestActiveAt M S A x (s₀ + 1), ∃ k : ℕ, x.lbl k = Event.tick w (M.voteTime S.C (s₀ + 1)) := by
        intro w hw
        have h1 : 1 ≤ M.voteTime S.C (s₀ + 1) := by omega
        have hr := (mem_activeThroughoutToTick_of_inside M F) R E ((honestActiveAt_window M F) S A (s₀ + 1) w E hw) h1
          (by rw [hdw1, hv1R]; linarith) (by rw [hv1R, hc2R]; linarith)
        obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hr
        exact ⟨k, hk⟩
      refine ⟨?_, fun u hu => ?_⟩
      · have h := (lem89s_chain_step M F U) S A x R GST s₀ (honestActiveAt M S A x s₀)
          (honestActiveAt M S A x (s₀ + 1)) (updaterAt M S A x s₀) (fun D => D.AncestorEq B₀)
          E hNet hSkew hRedeliver Sy hΔs (hRootsS s₀ (by omega)) (hRootsTickS s₀ (by omega)) hParent hOwner hGST
          (subset_refl _) (subset_refl _) (subset_refl _)
          ((honestActiveAt_succ_subset_updaterAt M F U) S A s₀ R E hSkew)
          (hCom s₀ le_rfl (by omega)) (hCom (s₀ + 1) (by omega) (by omega)) hBaseInv (hNewAt s₀) hBaseLocks hBaseConf
          (fun C hC w hw => by
            have hC' : OnHonestChainBefore M S A x s₀ (s₀ + 1) C := by
              rcases hC with hCB | ⟨v, hv, hsv⟩
              · exact hB₀chain C hCB
              · exact ⟨s₀, Nat.lt_succ_self s₀, le_rfl, v, hv, C, hsv, ancestorEq_refl C⟩
            obtain ⟨k, hk⟩ := hVT w hw
            have hti : x.tickInput w (M.voteTime S.C (s₀ + 1)) = x.st k w := by
              unfold Trace.tickInput
              rw [(tickStep_eq_of_lbl M) x E hk]
            have hVF := hVoterFrame (s₀ + 1) (Nat.lt_succ_self s₀) hn w hw C hC' k hk
            rw [← hti] at hVF
            exact ⟨hVF.1, hVF.2, hUpdaterFrame (s₀ + 1) (Nat.lt_succ_self s₀) hn w
              ((honestActiveAt_subset_updaterAt M F) S A x R E (s₀ + 1) hw) C hC'⟩)
        intro C hC
        apply h C
        obtain ⟨s', hs', hs₀', v, hv, C', hC', hCC'⟩ := hC
        have hss : s' = s₀ := by omega
        subst hss
        exact Or.inr ⟨v, hv, C', hC', hCC'⟩
      · refine (liveLocksOnFamilyAt_of_locksRevoked M F U) S A x R E _ _ u <| (liveLocksOnFamilyAt_step M F U) S A x R
          (fun D => D.AncestorEq B₀) (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ u E hSkew
          ((lockStep_window_of_honestActiveAt M F U) S A R E hSkew s₀ hu)
          hB₀chain
          (fun C hC => ⟨s₀, Nat.lt_succ_self s₀, le_rfl, u,
            (honestActiveAt_succ_subset_updaterAt M F U) S A s₀ R E hSkew hu, C, hC, ancestorEq_refl C⟩)
          ?_
        rcases hNewAt s₀ u hu with h0 | hfree
        · exact hBaseLocks u h0
        · exact (liveLocksOnFamilyAt_of_locksRevoked M F U) S A x R E _ _ u
            ((liveLocksOnFamilyAt_of_lockFree M F) S A x _ s₀ u hfree)
    | succ s hs ih =>
      intro hn
      obtain ⟨ihInv, ihLocks⟩ := ih (by omega)
      refine ⟨(lem81b_chain_step M F U) S A x R GST s₀ s anchor E hNet hSkew hRedeliver Sy hΔs
          (hRootsS s (by omega)) (hRootsTickS s (by omega)) hParent hOwner (hGSTs s (by omega)) (by omega)
          (hSleepK.mono M (hcm _ _ (by omega))) (hAnch s (by omega)) ihInv ihLocks
          (hVoterFrame (s + 1) (by omega) hn) (hUpdaterFrame s (by omega) (by omega))
          (fun w hw => hUpdaterFrame (s + 1) (by omega) hn w
            ((honestActiveAt_subset_updaterAt M F) S A x R E (s + 1) hw)),
        fun u hu => ?_⟩
      refine (liveLocksOnFamilyAt_of_locksRevoked M F U) S A x R E _ _ u <| (liveLocksOnFamilyAt_step M F U) S A x R
        (OnHonestChainBefore M S A x s₀ s) (OnHonestChainBefore M S A x s₀ (s + 1)) s u E hSkew
        ((lockStep_window_of_honestActiveAt M F U) S A R E hSkew s hu)
        (fun C ⟨s', hs', hAt⟩ => ⟨s', by omega, hAt⟩)
        (fun C hC => ⟨s, Nat.lt_succ_self s, by omega, u,
          (honestActiveAt_succ_subset_updaterAt M F U) S A s R E hSkew hu, C, hC, ancestorEq_refl C⟩) ?_
      rcases hNewAt s u hu with h0 | hfree
      · exact ihLocks u h0
      · exact (liveLocksOnFamilyAt_of_locksRevoked M F U) S A x R E _ _ u
          ((liveLocksOnFamilyAt_of_lockFree M F) S A x _ s u hfree)
  exact fun s hs => hAll s hs

end GoldilocksCorrectness.Record.Proofs.Executions

