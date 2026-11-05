module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma33
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma33

@[expose] public section

/-!
# Lemma34, over a model

The theorem of `GoldilocksCorrectness/Proofs/Executions/Lemma34.lean` over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: Lemma 34, a fast lock against an older lock,
through the revocation (template A1 on the revocation's clause). The page's routine-level theorems
are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem supportCutoff_eq
  supportCutoff_lt_of_lt voteTime_cast voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (t_eq_mul)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor)

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
open GoldilocksCorrectness.Proofs.Routines (compatible_iff compatible_of_ancestorEq_compatible)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 34, a fast lock against an older lock, through the revocation.** The proof; the
audited statement is in `Statements/Executions/HealingStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot of `e_v`'s lock;
- `w`: the validator whose revocation is read; `e_v`: a lock entry with the deadline of a lock of
  slot `s`; `e_w`: `w`'s older live lock entry.

Read aloud: an older live lock entry of `w`, in the state `w`'s tick `kC` to the support cutoff of
slot `s + 1` leaves, is compatible with the block of `e_v`, when every live lock entry `w`'s tick at
the vote time of slot `s + 1` leaves is compatible with it. -/
theorem lem34_fast_lock_compatible_of_revocation (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (s : ℕ) (w : V) (e_v e_w : M.LE)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hd_v : e_v.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    (kC : ℕ) (hkC : x.lbl kC = Event.tick w (M.supportCutoff S.C (s + 1)))
    (he_w : e_w ∈ (x.tickOutput w (M.supportCutoff S.C (s + 1))).lockEntries)
    (hlive_w : ((M.supportCutoff S.C (s + 1) + 1 : ℕ) : Int) < e_w.d)
    (hOlder : e_w.d < e_v.d)
    (kV : ℕ) (hkV : x.lbl kV = Event.tick w (M.voteTime S.C (s + 1)))
    (hDuty : ∃ τ : Time, (x.tickInput w (M.voteTime S.C (s + 1))).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s + 1))
    (hLocks : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible e_v.B = true) :
    e_v.B.compatible e_w.B = true := by
  have hΔ := one_le_Δ S
  -- the times
  have hss' : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s, Nat.mul_add, Nat.mul_one]
  have hv₃ : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hv₂ : M.supportCutoff S.C (s + 1) = M.voteTime S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have hcb : M.supportCutoff S.C s = M.voteTime S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have hvb : M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hss'' : M.slotStart S.C (s + 1 + 1) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1), Nat.mul_add, Nat.mul_one]
  have hslot₃ : M.slot S.C (M.voteTime S.C (s + 1)) = s + 1 :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (by omega) (by omega)
  -- `he_w` at the step after `w`'s tick to the cutoff
  have htsC : x.tickStep w (M.supportCutoff S.C (s + 1)) = kC := (tickStep_eq_of_lbl M) x E hkC
  have he_w' : e_w ∈ (x.st (kC + 1) w).lockEntries := by
    unfold Trace.tickOutput at he_w
    rw [htsC] at he_w
    exact he_w
  -- the slot `s'` of `e_w`, before `s` (Lemma 39's trace at the step `kC + 1`)
  obtain ⟨s', hd_w, -, hlab, hAw₀, h39⟩ :=
    (lockTracedAfterTick_of_mem M F U) S A x R E w (kC + 1) e_w he_w'
  have hlt : s' < s := by
    by_contra h
    have hΔi : (0 : Int) < S.C.Δ := S.C.Δ_pos
    have h1 : @LT.lt Int _ (S.C.t_ (s' + S.C.k) + 5 * S.C.Δ) (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) := by
      rw [← hd_w, ← hd_v]
      exact hOlder
    have h2 : (((s + S.C.k : ℕ) : Int)) ≤ (((s' + S.C.k : ℕ) : Int)) := by
      exact_mod_cast (show s + S.C.k ≤ s' + S.C.k by omega)
    have h3 : @LE.le Int _ (4 * S.C.Δ * (((s + S.C.k : ℕ) : Int)))
        (4 * S.C.Δ * (((s' + S.C.k : ℕ) : Int))) :=
      Int.mul_le_mul_of_nonneg_left h2 (by omega)
    have h4 : @LT.lt Int _ (4 * S.C.Δ * (((s' + S.C.k : ℕ) : Int)))
        (4 * S.C.Δ * (((s + S.C.k : ℕ) : Int))) := by
      have h1' := h1
      simp only [t_eq_mul] at h1'
      omega
    omega
  -- the update of slot `s' + 1` ran before the vote time of slot `s + 1`
  have hcw : M.supportCutoff S.C (s' + 1) ≤ M.supportCutoff S.C s := by
    rcases Nat.lt_or_eq_of_le (show s' + 1 ≤ s by omega) with h | h
    · exact le_of_lt ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt_of_lt M.toSlotLayout F.sched) S h)
    · rw [h]
  -- the outcome of the tick at the support cutoff of slot `s' + 1` (a run fact at its label)
  obtain ⟨n₀, sent₀, hrun₀, -, -⟩ := R.tick _ w _ hlab
  obtain ⟨e₀, -, -, -, -, -, -, -, htr⟩ := h39 n₀ sent₀ hrun₀ hAw₀
  -- the two ticks of `w` are ordered by their clock values
  have hord₁ : x.tickStep w (M.supportCutoff S.C (s' + 1)) < kV + 1 := by
    have := tick_lt_of_clock_lt M x E hlab hkV (by omega)
    omega
  have hord₂ : kV + 1 ≤ kC + 1 := by
    have := tick_lt_of_clock_lt M x E hkV hkC (by omega)
    omega
  obtain ⟨e', he', hd', hB', -⟩ := htr _ hord₁ hord₂
  -- the tick at the vote time runs from `w`'s tick input there, awake for the slot, and revokes the locks
  obtain ⟨n₃, sent₃, hrun₃, hst₃, -⟩ := R.tick kV w _ hkV
  have htsV : x.tickStep w (M.voteTime S.C (s + 1)) = kV := (tickStep_eq_of_lbl M) x E hkV
  have hti₃ : x.tickInput w (M.voteTime S.C (s + 1)) = x.st kV w := by
    unfold Trace.tickInput
    rw [htsV]
  have hrun₃' : .ok (n₃, sent₃) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
      ((M.voteTime S.C (s + 1) : ℕ) : Int) := by
    rw [hti₃]
    exact hrun₃
  have hAwake : AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) := hDuty
  have hsl : S.C.slot ((M.voteTime S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact hslot₃
  have hInv : M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1))) := by
    rw [hti₃]
    exact (lem11_node_invariant M F S A x R E kV w (E.not_mem_corrupted_of_tick hkV)).1
  have hRevoke := F.tk2.tick_voteTime_locks S.C S.P S.X _ _ n₃ sent₃ hrun₃' hInv
    (by rw [hsl]; exact (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U) S (s + 1))
    (by rw [hsl]; exact hAwake)
  rw [hsl] at hRevoke
  -- `e'` is an entry the revocation left
  have he'A : e' ∈ n₃.lockEntries := by
    rw [← hst₃]
    exact he'
  -- `e'` is live at the vote time
  have hlive : M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
      ((M.voteTime S.C (s + 1) : ℕ) : Int) e' = true := by
    simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)]
    refine ⟨?_, GoldilocksCorrectness.Record.Proofs.Routines.revoke_locks_entry_mem_tree (Nat.le_add_left 1 s) hRevoke e' he'A⟩
    have h1 : ((M.voteTime S.C (s + 1) : ℕ) : Int) < ((M.supportCutoff S.C (s + 1) + 1 : ℕ) : Int) :=
      Int.ofNat_lt.2 (by omega)
    rw [hd']
    exact lt_trans h1 hlive_w
  have hC : e'.B.compatible e_v.B = true := hLocks n₃ sent₃ hrun₃' hAwake e' he'A hlive
  have hC' : e_w.B.compatible e_v.B = true := compatible_of_ancestorEq_compatible hB' hC
  exact (compatible_iff _ _).2 ((compatible_iff _ _).1 hC').symm

end GoldilocksCorrectness.Record.Proofs.Executions

