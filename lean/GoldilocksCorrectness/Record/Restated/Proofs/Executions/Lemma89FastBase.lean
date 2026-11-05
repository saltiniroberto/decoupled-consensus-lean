module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89FastLine
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma79
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma42
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma32
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma31
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HealedChainBefore
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ReadingPointStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ConfirmationCompatibilityStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.PhaseKitStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.SleepyStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealingStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Executions.Lemma89FastLine
public import GoldilocksCorrectness.Proofs.Executions.Lemma89
public import GoldilocksCorrectness.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Proofs.Executions.Lemma79
public import GoldilocksCorrectness.Proofs.Executions.Lemma42
public import GoldilocksCorrectness.Proofs.Executions.Lemma32
public import GoldilocksCorrectness.Proofs.Executions.Lemma31
public import GoldilocksCorrectness.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Statements.Executions.ReadingPointStatements
public import GoldilocksCorrectness.Statements.Executions.ConfirmationCompatibilityStatements
public import GoldilocksCorrectness.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Statements.Executions.PhaseKitStatements
public import GoldilocksCorrectness.Statements.Executions.SleepyStatements
public import GoldilocksCorrectness.Statements.Executions.HealingStatements
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89FastBase, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89FastBase.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the live-lock kit theorem and Lemma
79b from the saved confirmation compatible with the block, every honest finalized block compatible
with the fast block up to the support cutoff of the round's third slot. The base at the slot after
the fast block's round (A5, `fast_block_base`) is proved on `Lemma89FastFamily.lean`, after the line
sources it reads. The page's routine-level theorems are the facts' fields or have their twins in
phase A.
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
  dutyWindowStart_succ_le_slotStart duty_window_start_mono one_le_Δ slotStart_eq slotStart_mono
  slot_eq_of_mem supportCutoff_cast supportCutoff_eq supportCutoff_mono viewFreeze_eq
  voteTime_cast voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated LocksRevoked)

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
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; this rule, local to the file, proves it at once
--. No statement and no proof term
-- changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The live locks of `w` are compatible with `B`, read at `w`'s tick, from the two facts of slot `s'` the proof of
`live_locks_compatible_of_honestChainExtends_tick` reads, at `w` alone and in a weaker form: every live entry an
outcome of `w`'s tick to the vote time of slot `s' + 1` keeps is compatible with `B`, and the confirmation of slot `s'`
`w`'s tick to the support cutoff of slot `s' + 1` saves is compatible with `B` (in place of `B` or a descendant of
`B`). With `w` active up to its tick to the vote time of slot `s' + 1` (the reader of that theorem) and the clock value
`c` greater than the support cutoff of slot `s' + 1` and at most the vote time of slot `s' + 2`: every lock entry of the
state `w`'s tick to `c` starts from whose deadline is greater than `c` is on a block compatible with `B`.

Why: `live_locks_compatible_of_honestChainExtends_tick`'s proof; in the case of an entry of slot `s'`, the entry's
block is the saved confirmation or an ancestor of it, so compatible with `B`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `B`: the block; `s'`: the slot; `c`: the clock value of the
  tick; `w`: the validator.

Read aloud: the live locks in the state a validator's tick starts from are compatible with `B` when the live entries
of its revocation and the confirmation its update saves are. -/
theorem live_locks_compatible_of_clauses (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (B : Block V) (s' c : ℕ) (w : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- every lock entry an outcome of `w`'s tick to the vote time of slot `s' + 1` keeps live, from a state awake for the
    -- slot, is on a block compatible with `B`
    (hL2 : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s' + 1)))
        ((M.voteTime S.C (s' + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s' + 1))) (s' + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s' + 1)))
          ((M.voteTime S.C (s' + 1) : ℕ) : Int) e = true → e.B.compatible B = true)
    -- the confirmation of slot `s'` saved in the state `w`'s tick to the support cutoff of slot `s' + 1` leaves is
    -- compatible with `B`
    (hL3 : ∀ C' : Block V,
      (x.tickOutput w (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' → C'.compatible B = true)
    -- `w` ticks to the vote time of slot `s' + 1`, active up to that tick from the trace's start or from its own tick
    -- to a clock value at most the duty window's start of slot `s' + 2`
    (hHon : w ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (s' + 2) : ℕ) : ℤ) (M.voteTime S.C (s' + 1)))
    (hc1 : M.supportCutoff S.C (s' + 1) < c)
    (hc2 : c ≤ M.voteTime S.C (s' + 2)) :
    ∀ e ∈ (x.tickInput w c).lockEntries, ((c : ℕ) : Int) < e.d →
      e.B.compatible B = true := by
  intro e he hlive
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hv' : ∀ s : ℕ, M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
  have hc' : ∀ s : ℕ, M.supportCutoff S.C s = M.voteTime S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
  have hss : ∀ s : ℕ, M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := fun s => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have htime : Monotone x.time := fun _ _ h => (time_mono M) x R h
  -- where `e` comes from (Lemma 39): `w`'s tick `k₁` to the support cutoff of a slot `s₁ + 1`, before `w`'s tick to `c`
  obtain ⟨s₁, hd₁, hk₁lt, hlk₁, ⟨τ₀, hτ₀, hτ₀le⟩, h39⟩ :=
    (lockTracedAfterTick_of_mem M F U) S A x R E w (x.tickStep w c) e he
  set k₁ := x.tickStep w (M.supportCutoff S.C (s₁ + 1)) with hk₁def
  -- `w` ticks to `c`, at the step `j`
  obtain ⟨j₀, hj₀⟩ := x.exists_tick_of_lt_tickStep hk₁lt
  have hjs : x.tickStep w c = j₀ := (tickStep_eq_of_lbl M) x E hj₀
  rw [hjs] at hk₁lt
  have hwj : w ∉ A.corrupted j₀ := E.not_mem_corrupted_of_tick hj₀
  -- the outcome of `w`'s tick `k₁` (the step's own), awake for slot `s₁ + 1`
  have hti₁ : x.tickInput w (M.supportCutoff S.C (s₁ + 1)) = x.st k₁ w := rfl
  obtain ⟨n₁, sent₁, hrun₁, hst₁, -⟩ := R.tick k₁ w _ hlk₁
  rw [← hti₁] at hrun₁
  obtain ⟨e₀, -, -, -, -, ⟨C', hC', hBC⟩, -, heB₀, htr⟩ := h39 n₁ sent₁ hrun₁ ⟨τ₀, hτ₀, hτ₀le⟩
  have heC : e.B.AncestorEq C' := ancestorEq_trans heB₀ hBC
  -- the slot of `e` is at most `s'`: `w`'s clock does not go back between its two ticks
  have hcc : M.supportCutoff S.C (s₁ + 1) ≤ c := E.clock_mono k₁ j₀ w _ _ hk₁lt hwj (Or.inl hlk₁) (Or.inl hj₀)
  have hs₁ : s₁ ≤ s' := by
    by_contra h
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s' + 2 ≤ s₁ + 1 by omega)
    have h1 := hv' (s' + 2)
    have h2 := hc' (s₁ + 1)
    have h3 := hv' (s₁ + 1)
    omega
  rcases Nat.lt_or_eq_of_le hs₁ with hlt | heq
  · -- `s₁ < s'`: the revocation at `w`'s tick to the vote time of slot `s' + 1` kept an entry for `e`
    have hk : s' + 1 ≤ s₁ + S.C.k := by
      by_cases hkle : S.C.k ≤ s' + 1
      · have h41 := (GoldilocksCorrectness.Record.Statements.Executions.lem41_slot_of_live_entry M F U) S
          (s' + 1 - S.C.k) s₁ c e hd₁ hlive (by
            rw [show s' + 1 - S.C.k + S.C.k = s' + 1 by omega]
            have := hc' (s' + 1)
            omega)
        omega
      · omega
    -- the duty window's start of slot `s' + 2` is at least one delay before the support cutoff of slot `s₁ + 1`
    have hdw : M.dutyWindowStart S.C (s' + 2) + Δ S ≤ M.supportCutoff S.C (s₁ + 1) := by
      have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
        (show s' + 2 ≤ s₁ + 1 + S.C.k by omega)
      have e1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s₁ + 1 + S.C.k)
      have e2 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s₁ + 1)
      rw [Nat.mul_add] at e1
      have hcases := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S (s' + 2)
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s' + 2)] at hm
      have h2 := hc' (s₁ + 1)
      have h3 := hv' (s₁ + 1)
      omega
    have hc₃ : M.supportCutoff S.C (s₁ + 1) ≤ M.voteTime S.C (s' + 1) := by
      have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s₁ + 1 ≤ s' by omega)
      have h1 := hc' (s₁ + 1)
      have h2 := hv' (s₁ + 1)
      have h3 := hv' (s' + 1)
      have h4 := hss s'
      omega
    have hc1' := hc' (s' + 1)
    -- `w`'s tick `k₃` to the vote time of slot `s' + 1`: the tick the reader `hHon` ends at
    obtain ⟨k₃, hl₃, hcase⟩ := Activity.mem_activeThroughoutToTick.1 hHon
    have hw₃ : w ∉ A.corrupted k₃ := E.not_mem_corrupted_of_tick hl₃
    -- the order of the three ticks: `k₁ ≤ k₃ < j₀`
    have hk₁₃ : k₁ ≤ k₃ := by
      by_contra h
      have h' : M.voteTime S.C (s' + 1) ≤ M.supportCutoff S.C (s₁ + 1) :=
        E.clock_mono k₃ k₁ w _ _ (by omega) (E.not_mem_corrupted_of_tick hlk₁) (Or.inl hl₃) (Or.inl hlk₁)
      have heqv : M.voteTime S.C (s' + 1) = M.supportCutoff S.C (s₁ + 1) := le_antisymm h' hc₃
      rw [heqv] at hl₃
      have := E.tick_unique _ _ w _ hl₃ hlk₁
      omega
    have hk₃j : k₃ < j₀ := by
      by_contra h
      rcases Nat.lt_or_eq_of_le (not_lt.1 h) with h' | h'
      · have := E.clock_mono j₀ k₃ w _ _ h' hw₃ (Or.inl hj₀) (Or.inl hl₃)
        omega
      · subst h'
        rw [hj₀] at hl₃
        injection hl₃ with _ h''
        omega
    -- `w` is awake after every step from `k₁` to `k₃`, so its tick to the vote time of slot `s' + 1` starts from a
    -- state awake since `τ₀`, at most the duty window's start of slot `s' + 1`
    have hAwSince : (x.tickInput w (M.voteTime S.C (s' + 1))).awakeSince = some τ₀ := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl₃]
      refine (awakeSince_kept_of_awake_steps M F) x R E hk₁₃ (fun i h1 h2 => ?_) hτ₀
      refine (Activity.mem_active.1 ?_).1
      rcases hcase with hall | ⟨k, -, c₀, hc₀a, hk, hbetween⟩
      · exact hall i (le_of_lt h2)
      · refine hbetween i ?_ (le_of_lt h2)
        -- `k`, `w`'s tick to `c₀ ≤ dutyWindowStart (s' + 2)`, comes at or before `k₁`: `w`'s clock does not go back
        have hc₀ : c₀ ≤ M.dutyWindowStart S.C (s' + 2) := by exact_mod_cast hc₀a
        by_contra hki
        have hk₁k : k₁ < k := by omega
        have := E.clock_mono k₁ k w _ _ hk₁k (E.not_mem_corrupted_of_tick hk) (Or.inl hlk₁) (Or.inl hk)
        omega
    have hAwake : AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s' + 1))) (s' + 1) :=
      ⟨τ₀, hAwSince, le_trans hτ₀le (duty_window_start_mono S (show s₁ + 1 ≤ s' + 1 by omega))⟩
    -- the tick's outcome, the revocation of slot `s' + 1`
    have hti₃ : x.tickInput w (M.voteTime S.C (s' + 1)) = x.st k₃ w := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl₃]
    obtain ⟨n₃, sent₃, hrun₃, hst₃, -⟩ := R.tick k₃ w _ hl₃
    rw [← hti₃] at hrun₃
    have hslot₃ : M.slot S.C (M.voteTime S.C (s' + 1)) = s' + 1 := by
      have := hv' (s' + 1)
      have := hss (s' + 1)
      exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (by omega) (by omega)
    have hsl : S.C.slot ((M.voteTime S.C (s' + 1) : ℕ) : Int) = s' + 1 := by
      rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
        ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
      exact hslot₃
    have hInvW : M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C (s' + 1))) := by
      rw [hti₃]
      exact (lem11_node_invariant M F S A x R E k₃ w hw₃).1
    have hRevoke := F.tk2.tick_voteTime_locks S.C S.P S.X _ _ n₃ sent₃ hrun₃ hInvW
      (by rw [hsl]; exact (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U) S (s' + 1))
      (by rw [hsl]; exact hAwake)
    rw [hsl] at hRevoke
    -- the entry for `e` right after that tick, an entry of the tick's outcome, live then
    obtain ⟨e', he', hd', heB', -⟩ := htr (k₃ + 1) (by omega) (by omega)
    have he'A : e' ∈ n₃.lockEntries := by
      rw [← hst₃]
      exact he'
    have hlive' : M.is_live (x.tickInput w (M.voteTime S.C (s' + 1)))
        ((M.voteTime S.C (s' + 1) : ℕ) : Int) e' = true := by
      simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)]
      refine ⟨?_, GoldilocksCorrectness.Record.Proofs.Routines.revoke_locks_entry_mem_tree (Nat.le_add_left 1 s') hRevoke e'
        he'A⟩
      rw [hd']
      exact lt_trans (Int.ofNat_lt.2 (show M.voteTime S.C (s' + 1) < c by omega)) hlive
    exact compatible_of_ancestorEq_compatible heB'
      (hL2 n₃ sent₃ hrun₃ hAwake e' he'A hlive')
  · -- `s₁ = s'`: the update of slot `s' + 1` saved `C'`, which `hL3` makes compatible with `B`
    subst heq
    have hsv : (x.tickOutput w (M.supportCutoff S.C (s₁ + 1))).savedConfirmation s₁ = some C' := by
      unfold Trace.tickOutput
      rw [← hk₁def, hst₁]
      exact hC'
    exact compatible_of_ancestorEq_compatible heC (hL3 C' hsv)

/-- The lock clause of the slot invariant restricted to `B` at slot `s' + 1`, at `w`, from the facts of slot `s'` of
`live_locks_compatible_of_clauses`: Lemma 79b's proof (`lem79b_honestChainExtends_locks_step`), read at `w`'s tick input
to the vote time of slot `s' + 2`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `B`: the block; `s'`: the slot; `w`: the validator.

The conclusion reads every node state the revocation of slot `s' + 2` may leave from `w`'s tick input to the vote time
of slot `s' + 2` (`LocksRevoked`, the shape of Lemma 79b's twin).

Read aloud: the lock clause of the slot invariant restricted to `B` holds at the next slot, from the
weaker facts of the slot. -/
theorem locks_step_of_clauses (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (B : Block V) (s' : ℕ) (w : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- every lock entry an outcome of `w`'s tick to the vote time of slot `s' + 1` keeps live, from a state awake for the
    -- slot, is on a block compatible with `B`
    (hL2 : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s' + 1)))
        ((M.voteTime S.C (s' + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s' + 1))) (s' + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s' + 1)))
          ((M.voteTime S.C (s' + 1) : ℕ) : Int) e = true → e.B.compatible B = true)
    -- the confirmation of slot `s'` saved in the state `w`'s tick to the support cutoff of slot `s' + 1` leaves is
    -- compatible with `B`
    (hL3 : ∀ C' : Block V,
      (x.tickOutput w (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' → C'.compatible B = true)
    -- `w` ticks to the vote time of slot `s' + 1`, active up to that tick from the trace's start or from its own tick
    -- to a clock value at most the duty window's start of slot `s' + 2`
    (hHon : w ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (s' + 2) : ℕ) : ℤ) (M.voteTime S.C (s' + 1))) :
    ∀ n' : M.N,
      LocksRevoked M S.P (x.tickInput w (M.voteTime S.C (s' + 2)))
        ((M.voteTime S.C (s' + 2) : ℕ) : Int) (s' + 2) n' →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s' + 2)))
          ((M.voteTime S.C (s' + 2) : ℕ) : Int) e = true → e.B.compatible B = true := by
  intro n' hRevoke e' he' _
  have hΔ := one_le_Δ S
  have hv₂ : M.voteTime S.C (s' + 2) = M.voteTime S.C (s' + 1) + 4 * Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S (s' + 1)
  have hc₁ : M.supportCutoff S.C (s' + 1) = M.voteTime S.C (s' + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' + 1)
  have hlt₂ : M.supportCutoff S.C (s' + 1) < M.voteTime S.C (s' + 2) := by omega
  obtain ⟨e, heS, hlive_e, -, hB, -⟩ :=
    GoldilocksCorrectness.Record.Statements.Routines.lem38_revoke_locks_entries_moved
      (Nat.le_add_left 1 (s' + 1)) hRevoke e' he'
  have hlt : ((M.voteTime S.C (s' + 2) : ℕ) : Int) < e.d :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F) _ _ _).1 hlive_e |>.1
  exact compatible_of_ancestorEq_compatible hB
    ((live_locks_compatible_of_clauses M F U) S A x R B s' (M.voteTime S.C (s' + 2)) w E
      hL2 hL3 hHon hlt₂ le_rfl e heS hlt)

/-- **Kit fact, an honest finalized block is compatible with the fast block.** Under unforgeability
and fewer than a third of the validators in the adversary set up to `tAwakeEnd`: when every honest
attestation sent before the support cutoff of slot `s₀ + 1` has height at most `H₂`; `v` is an updater
of slot `s₀` whose update saves `C'` as the confirmation of slot `s₀`, with `L` an ancestor of `C'`
or `C'`, and `v` holds `L`, at the height `H₂ + 1`, at its tick to the support cutoff of slot `s₀ + 1`;
every updater of a slot later than `s₀` whose tick to that slot's support cutoff is before step `j`
has saved, as that slot's confirmation, a block compatible with `L`; and `w` is honest at step `j`:
then `w`'s finalized block at step `j` is compatible with `L`.

Why: `w`'s finalized block is the finalized block of the chain state of a block `D` it holds. At a
finalization height at most `H₂`, Lemma 68 with `v` holding `L` makes it an ancestor of `L`. Past
`H₂`, it is justified on `D`'s chain (Lemma 66), and its certificate names an entry `E` that an
updater `uₐ` of a slot `s_a ≥ s₀` held at its tick to the support cutoff of slot `s_a + 1`, a step
before `j`, `E` being `uₐ`'s saved confirmation of slot `s_a` or an ancestor of it
(`cert_entry_at_slot_saved`); the finalized block is `E` (roots name blocks). At `s_a = s₀`, `uₐ`'s
and `v`'s saved confirmations are compatible (Lemma 32, both updaters of slot `s₀`); at a later slot,
`hLater` gives `uₐ`'s.

The case of a later slot happens under per-node clocks, at clock bounds 0 included: `uₐ`'s tick to
the support cutoff of slot `s₀ + 2` can come before `w`'s tick to the same clock value, and the
attestation it sends can reach `w` first (F-82-1). `hLater` takes that case as a hypothesis; the
caller supplies it by induction over the ticks to that cutoff.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, its run facts; `GST`: the time from
  which the network is synchronous; `tAwakeEnd`: the phase's end; `s₀`: the first slot of the
  round; `H₂`: the bound on the old attestations; `j`: the step; `v`: the updater whose update saves
  `C'`; `w`: the validator whose finalized block is read; `L`: the block; `C'`: the saved
  confirmation.

Roots name blocks until the later of the real times of step `j` and of `v`'s tick to the support
cutoff of slot `s₀ + 1`: the proof compares (Lemma 68) a block `w` holds at step `j` with `L`, held by
`v` at that tick, and, past `H₂`, `w`'s finalized block with the entry an updater held at a step
before `j`.

Read aloud: when every updater of a later slot that ticked to its cutoff before step `j` saved a
confirmation compatible with the fast block, an honest validator's finalized block at step `j` is
compatible with the fast block. -/
theorem finalized_compatible_fast_block (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tAwakeEnd s₀ H₂ j : ℕ) (v w : V) (L C' : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- a root names one block among what honest validators hold, until the later of the real times of
    -- step `j` and of `v`'s tick to the support cutoff of slot `s₀ + 1`
    (hRoots : RootsNameBlocksUntil M A x
      (max (x.time j) (x.time (x.tickStep v (M.supportCutoff S.C (s₀ + 1))))))
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H₂)
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s₀)
    -- step `j`, `v`'s tick to the support cutoff of slot `s₀ + 1` and that cutoff are at most `tAwakeEnd`
    (hEnd : max (x.time j) (x.time (x.tickStep v (M.supportCutoff S.C (s₀ + 1)))) ≤ tAwakeEnd)
    (hcEnd : M.supportCutoff S.C (s₀ + 1) ≤ tAwakeEnd)
    -- `v` is an updater of slot `s₀`, its update saves `C'`, and it holds `L` at that tick
    (hv : v ∈ updaterAt M S A x s₀)
    (hSaved : (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some C')
    (hLC : L.AncestorEq C')
    (hLv : L ∈ (x.tickInput v (M.supportCutoff S.C (s₀ + 1))).tree)
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    -- every updater of a slot `s_a` later than `s₀` that ticks to the support cutoff of slot `s_a + 1`
    -- before step `j` saves, as the confirmation of slot `s_a`, a block compatible with `L`
    (hLater : ∀ (s_a : ℕ) (u : V) (C : Block V), s₀ < s_a → u ∈ updaterAt M S A x s_a →
      x.tickStep u (M.supportCutoff S.C (s_a + 1)) < j →
      (x.tickOutput u (M.supportCutoff S.C (s_a + 1))).savedConfirmation s_a = some C →
      C.compatible L = true)
    (hw : w ∉ A.corrupted j) :
    (x.st j w).finalized.compatible L = true := by
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have hkv : x.tickStep v (M.supportCutoff S.C (s₀ + 1)) = k' := (tickStep_eq_of_lbl M) x E hk'
  have hvk : v ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s₀ + 1))) := by
    rw [hkv]; exact E.not_mem_corrupted_of_tick hk'
  obtain ⟨D, hD, hFD⟩ :=
    (GoldilocksCorrectness.Record.Statements.Executions.finalizedFromChain_of_exec M F) S A x R E j w
  rw [hFD]
  by_cases hle : (M.chainStateOf S.C D).h_F ≤ H₂
  · -- Lemma 68: the finalized block is `L` or an ancestor of `L`
    have hT : A.AdversaryFewerThanThirdUntil x (validator_count V)
        (max (x.time j) (x.time (x.tickStep v (M.supportCutoff S.C (s₀ + 1))))) :=
      hThird.mono hEnd
    have hFL := (GoldilocksCorrectness.Record.Proofs.Executions.lem68_honest_past_finalized M F Fx)
      S A x R E hRoots j _ w v D L hT hw hvk hD hLv (by rw [hL]; exact Nat.lt_succ_of_le hle) le_rfl
    exact (compatible_iff _ _).2 (Or.inl hFL)
  · have hlt : H₂ < (M.chainStateOf S.C D).h_F := Nat.lt_of_not_le hle
    obtain ⟨hJC, -, hFanc, -⟩ :=
      ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2
        (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
    have hFT : (M.chainStateOf S.C D).F ∈ (x.st j w).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E j w D _
        hD hFanc
    have hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V)
        (max (x.time j) (M.supportCutoff S.C (s₀ + 1))) :=
      ((GoldilocksCorrectness.Record.Proofs.Executions.fewerThanQuorum_of_fewerThanThird M F) A x
        tAwakeEnd hThird).mono
        (max_le ((le_max_left _ _).trans hEnd) (by exact_mod_cast hcEnd))
    -- the certificate's entry, held by an updater `uₐ` of a slot `s_a ≥ s₀` at a tick before `j`
    obtain ⟨s_a, uₐ, Eb, hk, hl, hu, -, hEb, hs₀a, -, -, hroot, Cu, hCu, hECu⟩ :=
      (GoldilocksCorrectness.Record.Proofs.Executions.cert_entry_at_slot_saved M F U Fx) S A x R s₀ H₂
        j w D _ _ E hAdvQ hOld hD
        ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hJC)
        hlt
    have hkt : x.time (x.tickStep uₐ (M.supportCutoff S.C (s_a + 1))) ≤ x.time j :=
      (time_mono M) x R hk.le
    -- one root, so one block
    have hFE : (M.chainStateOf S.C D).F = Eb := hRoots _ _
      ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w)
        hw (le_max_left _ _) hFT)
      ((GoldilocksCorrectness.Record.Proofs.Executions.onHonestChainAt_inHonestTreeBy M F U) S A x R E _
        uₐ (M.supportCutoff S.C (s_a + 1)) _ Eb hl (hkt.trans (le_max_left _ _)) hEb) hroot
    rw [hFE]
    rcases Nat.lt_or_ge s₀ s_a with hgt | hle'
    · -- a later slot: `hLater`
      exact compatible_of_ancestorEq_compatible hECu (hLater s_a uₐ Cu hgt hu hk hCu)
    · -- slot `s₀`: Lemma 32 between `uₐ` and `v`
      have hsa : s_a = s₀ := le_antisymm hle' hs₀a
      subst hsa
      have hR32 : RootsNameBlocksUntil M A x
          (max (x.time (x.tickStep uₐ (M.supportCutoff S.C (s_a + 1))))
            (x.time (x.tickStep v (M.supportCutoff S.C (s_a + 1))))) :=
        (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
          (max_le (hkt.trans (le_max_left _ _)) (le_max_right _ _)) hRoots
      have hcc := (GoldilocksCorrectness.Record.Proofs.Executions.lem32_saved_confirmations_compatible_state
        M F U) S A x R GST _ uₐ v Cu C' E hNet hSkew hRedeliver Sy hΔs hR32 hGST hu hv hCu hSaved
      exact compatible_of_ancestorEq_both hECu hLC hcc

end GoldilocksCorrectness.Record.Proofs.Executions

