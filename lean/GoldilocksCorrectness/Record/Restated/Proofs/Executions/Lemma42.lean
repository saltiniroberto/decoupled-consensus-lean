module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ReadingPointStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma31
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Statements.Routines.LockStatements
public import GoldilocksCorrectness.Statements.Executions.ReadingPointStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma31
public import GoldilocksCorrectness.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma42, over a model

The theorem of `GoldilocksCorrectness/Proofs/Executions/Lemma42.lean` over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: Lemma 42, a fast lock clears every conflicting
lock. The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq supportCutoff_cast
  supportCutoff_eq viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes
  votesOnceInPoolFor_of_keepsVotes)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated LocksRevoked
  VotesOnceInPoolFor)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; this rule, local to the file, proves it at once, as in
-- `Lemma21.lean`.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A validator awake and honest from the duty window's start of slot `s` through `e` is active
through the reader's window of length `max (Δ S) Δs` before `b`, ending at `e'`, when `b` is at least
the vote time of `s` less three delays and `e' ≤ e`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup;
- `Δs`: the sync delay; `s`: the slot; `b`: the time the window is counted back from; `e`: the
  end of the duty window held; `e'`: the end of the window built; `v`: the validator.

Read aloud: a validator active through a slot's duty window is active through every window of the
recovery delay's length that starts inside it and ends by the end held. -/
theorem activeThroughout_of_dutyWindow_to (U : UniformSchedule M.toSlotLayout) (S : Setup V)
    {A : Activity V} {x : Trace V (NamedObject V) M.N} {Δs : ℕ} {ΔClockAhead ΔClockBehind : ℝ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {s b e e' : ℕ} {v : V}
    (h : v ∈ A.activeThroughout x (M.dutyWindowStart S.C s) e)
    (hAB : 0 ≤ ΔClockAhead + ΔClockBehind)
    (hb : M.voteTime S.C s ≤ b + 3 * Δ S) (hcb : max (Δ S) Δs ≤ b) (he : e' ≤ e) :
    v ∈ A.activeThroughout x (b - (max (Δ S) Δs)) e' := by
  obtain ⟨hv, -, -, -, hd, hk, hΔ⟩ := (slot_times M F U) S s
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  have hkN : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  refine Activity.mem_activeThroughout_of_le ?_ (by exact_mod_cast he) h
  have hn : M.dutyWindowStart S.C s ≤ b - max (Δ S) Δs := by
    rcases max_choice (Δ S) Δs with hm | hm <;> rcases hd with hd | ⟨hd, -⟩ <;> omega
  have h' : ((M.dutyWindowStart S.C s : ℕ) : ℝ) ≤ ((b - max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hn
  exact le_of_le_of_eq h' (by push_cast [Nat.cast_sub hcb]; ring)

/-- Lemma 42's core: Lemma 42 with the transfer of `w`'s votes to `v` as a hypothesis `hToV42` in
place of the holder window of `w` after the support cutoff of slot `s + 1`. `lem42_fast_lock_clears_conflicting_locks`
supplies `hToV42` by `pool_transfer_of_holder`; `lem42_fast_lock_clears_own_locks`,
for one validator, by `pool_mono`.

The variables:
- `M`: the model; `F`: its facts; the others as `lem42_fast_lock_clears_conflicting_locks`'s.

Read aloud: every lock entry `w`'s revocation of slot `s + 1` leaves is compatible with `L`, when
`L` is a fast block of `v`'s confirmation update of slot `s + 1`, `w`'s finalized block is
compatible with `L`, and every slot-`s` committee vote `w` holds at its tick to the vote time of slot
`s + 1` is in `v`'s pool at its tick to the support cutoff of slot `s + 1` or `v` holds two votes of
its validator. -/
theorem lem42_fast_lock_clears_conflicting_locks_core (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (L : Block V) (v w : V) (n' : M.N)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- a root names one block among what honest validators hold, until the latest real time of `w`'s tick
    -- to the view freeze of slot `s`, the one receiver of a block (T-RC8-2, T-R42's form)
    (hRoots : RootsNameBlocksUntil M A x ((M.viewFreeze S.C s : ℝ) + ΔClockBehind))
    -- a block reaches a validator only once the validator holds its parent
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from one delay or one sync delay before the view freeze of slot `s`
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s)
    -- `v`'s window starts at `tStart`, more than both clock bounds before the support cutoff of slot `s + 1`
    -- less six delays or one sync delay, whichever is longer
    (tStart : ℤ) (htStart :
      (tStart : ℝ) + ΔClockAhead + ΔClockBehind < ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ))
    -- `v` is active from `tStart` up to its tick to the support cutoff of slot `s + 1`
    (hv : v ∈ A.activeThroughoutToTick x tStart (M.supportCutoff S.C (s + 1)))
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    -- `w` is active from `tStartW` up to its tick to the view freeze of slot `s`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.viewFreeze S.C s))
    -- the holder `v` active for the sync delay after the view freeze of slot `s` less one delay or one
    -- sync delay, whichever is longer
    (hv₀ : v ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- every slot-`s` committee vote `w` holds at its tick to the vote time of slot `s + 1` is in `v`'s
    -- pool at its tick to the support cutoff of slot `s + 1`, or `v` holds two votes of its validator
    -- (`pool_transfer_of_holder` for two validators, `pool_mono` for one)
    (hToV42 : ∀ vote' : GoldfishVote V, vote'.slot = s → vote'.val_index ∈ S.P.committee s →
      vote' ∈ M.votesHeldSet (x.tickInput w (M.voteTime S.C (s + 1))) s →
      vote' ∈ M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s ∨
        ∃ v₁ ∈ M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s,
          ∃ v₂ ∈ M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s,
            v₁ ≠ v₂ ∧ v₁.val_index = vote'.val_index ∧ v₂.val_index = vote'.val_index)
    -- `v`'s update of slot `s + 1`, at its tick to the support cutoff of slot `s + 1`, leaves `n'` and makes
    -- `L` a fast block (T-RC8-2,)
    (hUpdate : ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n')
    (hFast : L ∈ n'.fastBlocks)
    -- `w` ticks to the vote time of slot `s + 1` at `kV`, and its finalized block there is compatible with `L`
    (kV : ℕ) (hkV : x.lbl kV = Event.tick w (M.voteTime S.C (s + 1)))
    (hF : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.compatible L = true) :
    -- then every lock entry `w`'s revocation of slot `s + 1` at that tick leaves is on a block compatible
    -- with `L`
    ∀ n'' : M.N,
      LocksRevoked M S.P (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) (s + 1) n'' →
      ∀ e ∈ n''.lockEntries, e.B.compatible L = true := by
  intro n'' hRevoke
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  -- the times
  have hΔ := one_le_Δ S
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hss2 : M.slotStart S.C (s + 2) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1), Nat.mul_add, Nat.mul_add]
    omega
  have hv₃ : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hv₁ : M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hc : M.supportCutoff S.C s = M.voteTime S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have ht₂ : M.supportCutoff S.C (s + 1) = M.voteTime S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have hfr : M.viewFreeze S.C s = M.slotStart S.C s + 3 * Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hfr' : M.supportCutoff S.C s + Δ S = M.viewFreeze S.C s := by omega
  have ht₂' : M.voteTime S.C (s + 1) + Δ S = M.supportCutoff S.C (s + 1) := ht₂.symm
  have hb1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  have hm1 := le_max_left (Δ S) Δs
  have hm2 := le_max_right (Δ S) Δs
  have hm6 : max (6 * Δ S) Δs ≥ 6 * Δ S := le_max_left _ _
  have hm6' : max (6 * Δ S) Δs ≥ Δs := le_max_right _ _
  have hm3 : max (3 * Δ S) Δs ≥ 3 * Δ S := le_max_left _ _
  have hm3' : max (3 * Δ S) Δs ≥ Δs := le_max_right _ _
  -- `v`'s tick `k_v` to the support cutoff of slot `s + 1`, active from the support cutoff of slot `s` less
  -- `ΔClockAhead`
  have hslR : ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) ≤ (M.supportCutoff S.C s : ℝ) := by
    exact_mod_cast (show M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs ≤ M.supportCutoff S.C s by omega)
  obtain ⟨k_v, hk_v, hwinv⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv
    (t₀ := (M.supportCutoff S.C s : ℝ) - ΔClockAhead) (by linarith)
  have hk_vT := (E.tick_active k_v v _ hk_v).2.1
  have hcR : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = (M.supportCutoff S.C s : ℝ) + 4 * Δ S := by
    have : M.supportCutoff S.C (s + 1) = M.supportCutoff S.C s + 4 * Δ S := by omega
    rw [this]; push_cast; ring
  rw [hcR] at hk_vT
  -- `v`'s tick `kₑ` to the support cutoff of slot `s`
  obtain ⟨kₑ, hkₑ, -, -⟩ := E.tick_of_active (M.supportCutoff S.C s) (by omega) v fun j hj1 hj2 => by
    refine hwinv j hj1 ?_
    exact ((lt_of_time_lt M) x R (by linarith)).le
  -- `w`'s tick `k_f` to the view freeze of slot `s`
  have hslW : ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ) ≤ (M.viewFreeze S.C s : ℝ) := by
    exact_mod_cast Nat.sub_le _ _
  obtain ⟨k_f, hk_f, -⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hw
    (t₀ := (M.viewFreeze S.C s : ℝ)) (by linarith)
  have hti_v : x.tickInput v (M.supportCutoff S.C (s + 1)) = x.st k_v v := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_v]
  have hti_w : x.tickInput w (M.voteTime S.C (s + 1)) = x.st kV w := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkV]
  rw [hti_v] at hUpdate
  rw [hti_w] at hF hRevoke
  have hRootsΦv : RootsNameBlocksIn (M.fg_to_ac (x.st k_v v)).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E _ v
  -- step 1: when `L` is `w`'s finalized block or an ancestor of it, every entry left is on a
  -- block of `w`'s frame tree, a descendant of the finalized block or it
  rcases (compatible_iff _ _).1 hF with hFL | hLF
  swap
  · intro e he
    have heT := GoldilocksCorrectness.Record.Proofs.Routines.revoke_locks_entry_mem_tree hb1 hRevoke e he
    exact (compatible_iff _ _).2 (Or.inr (ancestorEq_trans hLF (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 heT).2))
  -- step 2: Lemma 36 on `v`'s update at its tick to the support cutoff of slot `s + 1`
  obtain ⟨C', hSaved, hLC'⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_fast_block_saved hb1 hUpdate hFast
  obtain ⟨Sup, hSup, -, hHalf⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem36_confirmed_ancestor_early_supporters F)
      C' L hb1 hRootsΦv
      (by
        rw [Nat.add_sub_cancel]
        exact (pool_vote_late_of_tick M F U) S A x R s v E k_v hk_v fun j hj hjk => hwinv j (by
          rw [hcR] at hj; linarith) hjk)
      hUpdate hSaved hLC'
  have hHalf' := hHalf hFast
  simp only [Nat.add_sub_cancel] at hSup hHalf'
  have hSupAt : ∀ u ∈ Sup, EarlySupporterAt M (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C s : ℕ) : Int) s L u := by
    intro u hu
    rw [hti_v, (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U)]
    exact hSup u hu
  -- step 3: each member of `Sup` votes once for `L`'s chain in `w`'s pool at its tick to the vote time of
  -- slot `s + 1`: Lemma 63 read on `w`'s pool, with `t_e := c`, `t_f := freeze`, `t_w := t₃`, `t_v := t₂`
  have hPer := (supporters_vote_once_in_pool_at_core M F U) S A x R GST s
      (M.supportCutoff S.C s) (M.viewFreeze S.C s) (M.voteTime S.C (s + 1)) (M.supportCutoff S.C (s + 1))
      (M.supportCutoff S.C (s + 1)) Sup L v w (E.upTo _) hNet hSkew hRedeliver (Sy.upTo _)
      (by rw [hfr']; exact hRoots) hParent (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
      tStartW (by rw [hfr']; exact (lt_natSub_max_of_le (m := Δ S) (by omega) htStartW))
      (by
        have : ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ) ≤ (M.slotStart S.C s : ℝ) := by
          exact_mod_cast (show M.viewFreeze S.C s - max (3 * Δ S) Δs ≤ M.slotStart S.C s by omega)
        linarith)
      (by rw [hfr']; exact hw)
      (by rw [hfr']; exact hv₀) hToV42
      kₑ hkₑ k_f hk_f kV hkV k_v hk_v hSupAt (by rw [hti_w]; exact hFL) (by omega)
  rw [hti_w] at hPer
  -- step 4: Lemma 5 on `w`'s revocation
  intro e he
  exact ((GoldilocksCorrectness.Record.Statements.Routines.lem5_revoke_locks_entries_compatible F) L Sup
    hb1 (by rw [Nat.add_sub_cancel]; exact hPer) (by rw [Nat.add_sub_cancel]; exact hHalf') hRevoke e
    he).2

/-- **Lemma 42, a fast lock clears every conflicting lock.** The proof; the audited statement is
in `Statements/Executions/HealingStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot whose votes `v`'s update of slot `s + 1` counts;
- `L`: the fast block; `v`: the validator whose update makes `L` fast; `w`: the validator whose
  revocation is read; `n'`: the node state `v`'s update leaves.

Read at the validators' own ticks (T-RC8-2): `v`'s update at its tick to the support cutoff of slot
`s + 1`, `w`'s revocation and finalized block at its tick to the vote time of slot `s + 1`; the holders
active for the sync delay after the read times. Roots name blocks until the latest real
time of `w`'s tick to the view freeze of slot `s`: `supporters_vote_once_in_pool_at`, which the proof
calls with `t_e := M.supportCutoff S.C s`, reads a block as delivered before that tick.

Read aloud: every lock entry `w`'s revocation of slot `s + 1` leaves is compatible with `L`, when
`L` is a fast block of `v`'s confirmation update of slot `s + 1` and `w`'s finalized block is
compatible with `L`. -/
theorem lem42_fast_lock_clears_conflicting_locks (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (L : Block V) (v w : V) (n' : M.N)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- a root names one block among what honest validators hold, until the latest real time of `w`'s tick
    -- to the view freeze of slot `s`, the one receiver of a block (T-RC8-2, T-R42's form)
    (hRoots : RootsNameBlocksUntil M A x ((M.viewFreeze S.C s : ℝ) + ΔClockBehind))
    -- a block reaches a validator only once the validator holds its parent
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from one delay or one sync delay before the view freeze of slot `s`
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s)
    -- `v`'s window starts at `tStart`, more than both clock bounds before the support cutoff of slot `s + 1`
    -- less six delays or one sync delay, whichever is longer
    (tStart : ℤ) (htStart :
      (tStart : ℝ) + ΔClockAhead + ΔClockBehind < ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ))
    -- `v` is active from `tStart` up to its tick to the support cutoff of slot `s + 1`
    (hv : v ∈ A.activeThroughoutToTick x tStart (M.supportCutoff S.C (s + 1)))
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    -- `w` is active from `tStartW` up to its tick to the view freeze of slot `s`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.viewFreeze S.C s))
    -- the holders: `v` active for the sync delay after the view freeze of slot `s` less one
    -- delay or one sync delay, whichever is longer; `w` for the sync delay after the support cutoff of
    -- slot `s + 1` less the same
    (hv₀ : v ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `v`'s update of slot `s + 1`, at its tick to the support cutoff of slot `s + 1`, leaves `n'` and makes
    -- `L` a fast block (T-RC8-2,)
    (hUpdate : ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n')
    (hFast : L ∈ n'.fastBlocks)
    -- `w` ticks to the vote time of slot `s + 1` at `kV`, and its finalized block there is compatible with `L`
    (kV : ℕ) (hkV : x.lbl kV = Event.tick w (M.voteTime S.C (s + 1)))
    (hF : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.compatible L = true) :
    -- then every lock entry `w`'s revocation of slot `s + 1` at that tick leaves is on a block compatible
    -- with `L`
    ∀ n'' : M.N,
      LocksRevoked M S.P (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) (s + 1) n'' →
      ∀ e ∈ n''.lockEntries, e.B.compatible L = true := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  -- the times
  have hΔ := one_le_Δ S
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hss2 : M.slotStart S.C (s + 2) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1), Nat.mul_add, Nat.mul_add]
    omega
  have hv₃ : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hv₁ : M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hc : M.supportCutoff S.C s = M.voteTime S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have ht₂ : M.supportCutoff S.C (s + 1) = M.voteTime S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have hfr : M.viewFreeze S.C s = M.slotStart S.C s + 3 * Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hfr' : M.supportCutoff S.C s + Δ S = M.viewFreeze S.C s := by omega
  have ht₂' : M.voteTime S.C (s + 1) + Δ S = M.supportCutoff S.C (s + 1) := ht₂.symm
  have hb1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  have hm1 := le_max_left (Δ S) Δs
  have hm2 := le_max_right (Δ S) Δs
  have hm6 : max (6 * Δ S) Δs ≥ 6 * Δ S := le_max_left _ _
  have hm6' : max (6 * Δ S) Δs ≥ Δs := le_max_right _ _
  have hm3 : max (3 * Δ S) Δs ≥ 3 * Δ S := le_max_left _ _
  have hm3' : max (3 * Δ S) Δs ≥ Δs := le_max_right _ _
  obtain ⟨k_v, hk_v, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  exact lem42_fast_lock_clears_conflicting_locks_core M F U S A x R GST s L v w n' E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST tStart htStart hv tStartW htStartW hw hv₀
    ((pool_transfer_of_holder M F U) S A x R GST s (M.voteTime S.C (s + 1)) (M.supportCutoff S.C (s + 1))
      (M.supportCutoff S.C (s + 1)) w v (E.upTo _) hNet hSkew hRedeliver (Sy.upTo _) (by omega) (by omega)
      (by omega) (by omega) tStart (by rw [ht₂']; exact (lt_natSub_max_of_le (m := Δ S) (by omega) htStart))
      (by rw [ht₂']; exact hv) (by omega) k_v hk_v (by rw [ht₂']; exact hw₀) kV hkV)
    hUpdate hFast kV hkV hF

/-- **Lemma 42 at one validator: its own fast lock clears its conflicting locks**. The
validator `u` whose update of slot `s + 1` makes `L` fast is the one whose revocation is read. It is
`lem42_fast_lock_clears_conflicting_locks_core` at `v := u`, `w := u`, with the transfer `hToV42` by `pool_mono`: what `u`
holds at its tick to the vote time of slot `s + 1` it holds at its later tick to the support cutoff of
slot `s + 1`. No window after `u`'s tick to the support cutoff of slot `s + 1` is asked: a node reading
its own pool serves no other node.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `u`: the validator; the others as
  `lem42_fast_lock_clears_conflicting_locks`'s.

Read aloud: every lock entry `u`'s revocation of slot `s + 1` leaves is compatible with `L`, when `u`'s
own update of slot `s + 1` makes `L` fast and `u`'s finalized block at its tick to the vote time of slot
`s + 1` is compatible with `L`. -/
theorem lem42_fast_lock_clears_own_locks (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (L : Block V) (u : V) (n' : M.N)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- a root names one block among what honest validators hold, until the latest real time of `u`'s tick
    -- to the view freeze of slot `s`, the one receiver of a block (T-RC8-2, T-R42's form)
    (hRoots : RootsNameBlocksUntil M A x ((M.viewFreeze S.C s : ℝ) + ΔClockBehind))
    -- a block reaches a validator only once the validator holds its parent
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from one delay or one sync delay before the view freeze of slot `s`
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s)
    -- `u`'s window starts at `tStart`, more than both clock bounds before the support cutoff of slot `s + 1`
    -- less six delays or one sync delay, whichever is longer
    (tStart : ℤ) (htStart :
      (tStart : ℝ) + ΔClockAhead + ΔClockBehind < ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ))
    -- `u` is active from `tStart` up to its tick to the support cutoff of slot `s + 1`
    (hv : u ∈ A.activeThroughoutToTick x tStart (M.supportCutoff S.C (s + 1)))
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    -- `u` is active from `tStartW` up to its tick to the view freeze of slot `s`
    (hw : u ∈ A.activeThroughoutToTick x tStartW (M.viewFreeze S.C s))
    -- `u` active for the sync delay after the view freeze of slot `s` less one delay or one sync delay,
    -- whichever is longer, a window that ends before `u`'s tick to the support cutoff of
    -- slot `s + 1`
    (hv₀ : u ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `u`'s update of slot `s + 1`, at its tick to the support cutoff of slot `s + 1`, leaves `n'` and makes
    -- `L` a fast block (T-RC8-2,)
    (hUpdate : ConfirmationUpdated M S.C S.P (x.tickInput u (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n')
    (hFast : L ∈ n'.fastBlocks)
    -- `u` ticks to the vote time of slot `s + 1` at `kV`, and its finalized block there is compatible with `L`
    (kV : ℕ) (hkV : x.lbl kV = Event.tick u (M.voteTime S.C (s + 1)))
    (hF : (x.tickInput u (M.voteTime S.C (s + 1))).finalized.compatible L = true) :
    -- then every lock entry `u`'s revocation of slot `s + 1` at that tick leaves is on a block compatible
    -- with `L`
    ∀ n'' : M.N,
      LocksRevoked M S.P (x.tickInput u (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) (s + 1) n'' →
      ∀ e ∈ n''.lockEntries, e.B.compatible L = true := by
  have hΔ := one_le_Δ S
  have ht₂ : M.supportCutoff S.C (s + 1) = M.voteTime S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  obtain ⟨k_v, hk_v, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have hle : kV ≤ k_v := tick_step_le_of_le M F E hkV hk_v (by omega)
  have hti_w : x.tickInput u (M.voteTime S.C (s + 1)) = x.st kV u := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkV]
  have hti_v : x.tickInput u (M.supportCutoff S.C (s + 1)) = x.st k_v u := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_v]
  exact lem42_fast_lock_clears_conflicting_locks_core M F U S A x R GST s L u u n' E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST
    tStart htStart hv tStartW htStartW hw hv₀
    (fun vote' _ _ h => Or.inl (by
      rw [hti_w] at h; rw [hti_v]; exact (pool_mono M F) x R E u hle s h))
    hUpdate hFast kV hkV hF

end GoldilocksCorrectness.Record.Proofs.Executions

