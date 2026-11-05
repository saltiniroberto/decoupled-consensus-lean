module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89FastLine
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseFrame
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma55
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Unforgeability
public import GoldilocksCorrectness.Proofs.Executions.Lemma89FastLine
public import GoldilocksCorrectness.Proofs.Executions.PhaseFrame
public import GoldilocksCorrectness.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Proofs.Executions.Lemma55
public import GoldilocksCorrectness.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Proofs.Executions.Unforgeability
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89Climb, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89Climb.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: steps B1 to B4 of part B of Lemma 89 on
the fast-confirmation route, an honest attestation is sent at a round's action time, the threshold
exists, the honest greatest chain-state heights between the threshold and the action time, the first
honest attestation above the threshold, and its sender's fast block. The page's routine-level
theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ supportCutoff_succ_times)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated hMax)

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
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; this rule, local to the file, proves it at once
--. No statement and no proof term
-- changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- An honest attestation is sent at the action time of a round: when `v` put the attestation `a` on
the wire at its tick at `t`, `t` is `aR M S r` for some round `r`.

Why: the tick's attestation is the duty's (Lemma 49), so `t` is the action time of the round of
its slot, which is the support cutoff of that round's second slot (`supportCutoff_succ_times`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time of the tick; `v`: the
  attester; `a`: the attestation.

Read aloud: an honest validator attests only at the action time of some round. -/
theorem eq_aR_of_honestAttestationAt (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) (a : Attestation V)
    (hSend : HonestAttestationAt M S A x t v a) :
    ∃ r : ℕ, t = aR M S r := by
  obtain ⟨i, hl, hSent⟩ := hSend
  obtain ⟨-, n', sent, hrun, ha⟩ := (tick_send_of_honestSendAt M F R E) hl hSent
  -- the tick's input state satisfies the node invariant (a wake keeps it)
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput v t) := by
    rw [show x.tickInput v t = x.st i v by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E (i := i) (v := v) (by assumption)]]
    exact (lem11_node_invariant M F S A x R E i v (E.not_mem_corrupted_of_tick hl)).1
  -- Lemma 49 over the record (T8, the field `tick_attestation` of `F.tk3`): the tick is at the
  -- action time of the round of its slot
  obtain ⟨hT, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n' _ sent a hrun
      hInvT ha
  -- the spec's slot of `t` is the layout's (`U`)
  have hsl : S.C.slot ((t : ℕ) : Int) = M.slot S.C t := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
  rw [hsl] at hT
  refine ⟨S.C.round (M.slot S.C t), ?_⟩
  obtain ⟨hslot, hround, hcut, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_times M.toSlotLayout F.sched U) S
      (S.C.round (M.slot S.C t)) (S.C.round (M.slot S.C t) * S.C.R) rfl
  rw [hslot, hround] at hcut
  have h : ((t : ℕ) : Int) = ((aR M S (S.C.round (M.slot S.C t)) : ℕ) : Int) :=
    hT.trans hcut.symm
  exact_mod_cast h

/-- **B1, the threshold exists.** The proof; the audited statement is in
`Statements/Executions/Lemma89Statements.lean`.

The route: every honest attestation sent at a tick before `T₁` is in the sent log of the
configuration `x[stepBefore M x T₁]` (`lt_stepBefore_iff`, `sent_le_of_le`), so the heights of these
attestations are bounded; `H₂` is the least bound (`Nat.find`), which is `0` or attained: a least
bound `H₂ > 0` that no such attestation reached would leave `H₂ − 1` a bound.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `T₁`: the time.

Read aloud: there is a greatest height the honest validators attested before `T₁`. -/
theorem exists_old_height_attained (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (T₁ : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) :
    ∃ H₂ : ℕ, OldHeightAttained M S A x T₁ H₂ := by
  classical
  let Hs : Set ℕ := {h | ∃ (t : ℕ) (v : V) (a : Attestation V), t < T₁ ∧
    HonestAttestationAt M S A x t v a ∧ v ∉ A.corruptedAtTime x T₁ ∧ a.h = h}
  let f : SignedMsg V (NamedObject V) → ℕ := fun sm =>
    match sm.msg with
    | .attest a => a.h
    | _ => 0
  -- a natural `N` greater than `T₁ + ΔClockBehind`: every tick to a clock value less than `T₁` is at a
  -- real time less than `N`
  obtain ⟨N, hN⟩ := exists_nat_gt ((T₁ : ℝ) + ΔClockBehind)
  have hB0 := E.behind_nonneg
  have hN1 : 1 ≤ N := by
    have : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
    exact_mod_cast this
  have hbdd : ∃ Bd : ℕ, ∀ h ∈ Hs, h ≤ Bd := by
    refine ⟨((x.sent (x.stepBefore N + 1)).map f).sup, ?_⟩
    rintro h ⟨t, v, a, ht, ⟨i, hl, hm⟩, -, rfl⟩
    have hm1 : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) :=
      Multiset.mem_of_le (Multiset.sub_le_self _ _) hm
    have hi : i ≤ x.stepBefore N := by
      refine ((time_lt_iff_le_stepBefore M) x R E hN1).1 ?_
      have h1 := ((time_of_lbl_tick M) x R E hl).1.2
      have h2 : (t : ℝ) < T₁ := by exact_mod_cast ht
      linarith
    have hm2 := Multiset.mem_of_le ((sent_le_of_le M F) x R (show i + 1 ≤ x.stepBefore N + 1 by omega)) hm1
    exact Multiset.le_sup (Multiset.mem_map_of_mem f hm2)
  -- the least upper bound of the heights attested before `T₁`
  refine ⟨Nat.find hbdd, ?_, ?_⟩
  · intro i t v a hl ht hHonT hm
    exact Nat.find_spec hbdd a.h ⟨t, v, a, by exact_mod_cast ht, ⟨i, hl, hm⟩, hHonT, rfl⟩
  · rcases Nat.eq_zero_or_pos (Nat.find hbdd) with h0 | hpos
    · exact Or.inl h0
    · right
      by_contra hno
      refine Nat.find_min hbdd (show Nat.find hbdd - 1 < Nat.find hbdd by omega) ?_
      intro h hh
      have hle := Nat.find_spec hbdd h hh
      have hne : h ≠ Nat.find hbdd := by
        rintro rfl
        obtain ⟨t, v, a, ht, hA, hT, hah⟩ := hh
        exact hno ⟨t, v, a, ht, hA, hT, hah⟩
      omega

/-- **The honest greatest chain-state height reaches the threshold one delay after a tick at or after `T₁`.** The lower
bound of B2 and of `ClimbCtx.bounds` (a helper, no audited text): with the threshold `H₂` attained at `T₁`
(`OldHeightAttained`), a validator `w` at its tick `k` to a clock value `t`, honest at `k`, which ticked earlier to a
clock value `c₂` with `T₁ ≤ c₂` and `c₂ + Δ ≤ t`, has greatest chain-state height at least `H₂` in its tick input to `t`.

Why: `H₂` is `0`, or the height of an attestation `a` that an attester `u`, honest at `T₁`, sent at its tick to some
`t' < T₁`. Lemma 89b (`lem89b_at_uniformSchedule_tick`) from the window start `tGAT`, read at `w`'s tick to `c₂`: `u`
is active over `[tGAT, tGAT + Δs]` (honest at `T₁ ≥ tGAT + Δs`, awake in the phase, which lasts past `tGAT + Δs`
because `w`'s tick `k`, in the phase, is to a clock value at least one delay after `T₁`), `w` from `tGAT` up to `k`
(honest at `k`, awake in the phase).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the trace, the run's facts; `GST`: the time from which the network is
  synchronous; `tGAT`, `tAwakeEnd`: the phase; `T₁`, `H₂`: the threshold's time and height; `b`: the bound on the
  deadlines; `t`: the clock value of `w`'s tick `k`; `c₂`: the clock value of `w`'s earlier tick; `w`: the validator.

Read aloud: one delay after a tick to a clock value at least `T₁`, an honest validator's greatest chain-state height at
its tick is at least the threshold. -/
theorem old_height_le_hMax_at_tick (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ H₂ b t c₂ k : ℕ) (w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST
      (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b)
    (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C)
      ΔRedeliver Δs GST b)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT) (hT₁s : tGAT + Δs ≤ T₁)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hH₂ : OldHeightAttained M S A x T₁ H₂)
    (hk : x.lbl k = Event.tick w t) (hkE : x.time k ≤ tAwakeEnd)
    (hRoots : RootsNameBlocksUntil M A x (x.time k)) (hw : w ∉ A.corrupted k)
    (hT₁c₂ : T₁ ≤ c₂) (hc₂t : c₂ + Δ S ≤ t) (hwc₂ : ∃ k' : ℕ, x.lbl k' = Event.tick w c₂) (htb : t ≤ b) :
    H₂ ≤ hMax M S.C (x.tickInput w t) := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hks := (tickStep_eq_of_lbl M) x E hk
  rcases hH₂.2 with h0 | ⟨t', u, a, ht', ⟨i, hl, hm⟩, huT, hah⟩
  · rw [h0]
    exact Nat.zero_le _
  rw [← hah]
  have hkt := (E.tick_active k w t hk).2.1
  -- the phase lasts past `tGAT + Δs`: `w`'s tick `k`, in the phase, is to a clock value at least `T₁ + Δ`, and its real
  -- time is less than `ΔClockAhead < Δ` before that clock value
  have hTE : tGAT + Δs ≤ tAwakeEnd := by
    have h1 : ((tGAT + Δs : ℕ) : ℝ) + Δ S ≤ t := by exact_mod_cast (show tGAT + Δs + Δ S ≤ t by omega)
    have h2 : ((tGAT + Δs : ℕ) : ℝ) ≤ tAwakeEnd := by linarith
    exact_mod_cast h2
  have hu : u ∈ A.activeThroughout x tGAT (tGAT + Δs) := by
    have h := (mem_activeThroughout_of_hAwake_honest_at M F) R E hAwake le_rfl hTE
      ((not_mem_corruptedAtTime_of_le M) x R E hT₁s huT)
    push_cast at h
    exact h
  have hv : ∀ j : ℕ, (tGAT : ℝ) ≤ x.time j → j ≤ x.tickStep w t → w ∈ A.active j := by
    intro j h1 h2
    rw [hks] at h2
    have hwj : w ∉ A.corrupted j := fun h => hw (E.corrupted_mono j k h2 h)
    exact Activity.mem_active.2 ⟨hAwake j w (le_trans (R.time_mono h2) hkE)
      (le_trans h1 (R.time_mono (Nat.le_succ j))) hwj, hwj⟩
  have hmx : max (Δ S) Δs ≤ t - tGAT := max_le (by omega) (by omega)
  exact lem89b_at_uniformSchedule_tick M F U Fx S A x R GST t t' i b tGAT u w a E hNet hSkew hRedeliver Sy hΔs
    (by rw [hks]; exact hRoots) hParent hGST (by omega) (hThird.mono (by rw [hks]; exact hkE)) (by omega) hv
    ⟨k, hk⟩ c₂ hwc₂ hc₂t (by omega) (by omega) hu ⟨hl, hm⟩ htb

/-- **B2, the honest greatest chain-state height from `T₁ + Δ` to `a_r`.** The proof; the audited
statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: at least `H₂` by `lem89b_at` (Lemma 89b on the four facts its proof reads) at the
honest attestation of height `H₂` sent before `T₁`, when `H₂ ≠ 0`; at most `H₂ + 1` because
the greatest chain-state height `hMax M S.C n` of `w`'s tree is the chain-state height of a block
`w` holds at its tick to `t` (`cachesWitnessed_of_exec`) and A2 bounds every block held at a step at
most `k₀`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `T₁`: the time of the
  threshold; `r`: the round; `H₂`: the threshold; `t`: the clock value; `k₀`: the step of `v`'s tick
  to `aR M S r`; `v`: the attester; `w`: the validator.

Roots name blocks until the real time of `w`'s tick `k` to `t`: the proof reads `lem89b_at` at `b := t`,
at that tick.

Read aloud: once the phase has settled, every honest validator knows the threshold's height and
nothing higher than one more than it, up to the step of the first attestation above it. -/
theorem honest_h_max_bounds (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ t k₀ : ℕ) (v w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT) (hT₁s : tGAT + Δs ≤ T₁)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hH₂ : OldHeightAttained M S A x T₁ H₂)
    (hk₀ : x.lbl k₀ = Event.tick v (aR M S r))
    (hOld : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < k₀ → x.lbl k = Event.tick u t →
      u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂)
    (hEnd : x.time k₀ ≤ tAwakeEnd)
    (ht₁ : T₁ + Δ S ≤ t) (k : ℕ) (hk : x.lbl k = Event.tick w t)
    (hRoots : RootsNameBlocksUntil M A x (x.time k)) (htr : k ≤ k₀)
    (hw : w ∉ A.corrupted k)
    -- `w` ticked to the threshold time `T₁`
    (hwt : ∃ k' : ℕ, x.lbl k' = Event.tick w T₁) :
    H₂ ≤ hMax M S.C (x.tickInput w t) ∧ hMax M S.C (x.tickInput w t) ≤ H₂ + 1 := by
  refine ⟨?_, ?_⟩
  · -- the lower bound: Lemma 89b at `w`'s tick `k` to `t`, read at `w`'s earlier tick to `T₁`
    exact old_height_le_hMax_at_tick M F U Fx S A x R GST tGAT tAwakeEnd T₁ H₂ t t T₁ k w
      (GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDelivery.upTo E t) hNet hSkew hRedeliver (Sy.upTo t) hΔs
      hParent hGST hT₁s hThird hAwake hH₂ hk (le_trans (R.time_mono htr) hEnd) hRoots hw le_rfl ht₁ hwt le_rfl
  · -- the upper bound: A2 at `w`'s tick `k` to `t`, a step at most `k₀`
    have hks := (tickStep_eq_of_lbl M) x E hk
    obtain ⟨-, ⟨X, hX, hXh⟩, -⟩ := (cachesWitnessed_of_exec M F) S A x R E k w
    show hMax M S.C (x.st (x.tickStep w t) w) ≤ H₂ + 1
    rw [hks, ← hXh]
    exact (held_height_le_before_action M F Fx) S A x R E tAwakeEnd H₂ k₀ k w X
      hThird hOld hEnd htr hX

/-- **The action times of two rounds are at least four delays apart.** Under a uniform slot layout,
the action time of round `r'` plus four delays is at most the action time of a later round `r`.

Why: `aR M S r = 4 Δ (r R + 1) + 2 Δ` (`supportCutoff_eq`, `voteTime_eq`, `slotStart_eq`), and
`r' R + 1 < r R + 1` with `R ≥ 2`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup;
- `r'`, `r`: the rounds.

Read aloud: a later round's action time comes at least four delays after an earlier one's. -/
theorem aR_add_le_of_lt (U : UniformSchedule M.toSlotLayout) (S : Setup V) {r' r : ℕ} (h : r' < r) :
    aR M S r' + 4 * Δ S ≤ aR M S r := by
  have hR := S.C.R_ge_two
  unfold aR
  rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (r' * S.C.R + 1),
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1),
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (r' * S.C.R + 1),
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1),
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (r' * S.C.R + 1),
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1)]
  have h1 := Nat.mul_le_mul_right S.C.R (Nat.succ_le_of_lt h)
  rw [Nat.succ_mul] at h1
  have h2 : r' * S.C.R + 1 + 1 ≤ r * S.C.R + 1 := by omega
  have h3 := Nat.mul_le_mul_left (4 * Δ S) h2
  rw [Nat.mul_add (4 * Δ S) (r' * S.C.R + 1) 1] at h3
  omega

/-- **B3, the first honest attestation above `H₂`.** The proof; the audited statement is in
`Statements/Executions/Lemma89Statements.lean`.

The route: the least step `k₀` (`Nat.find`) whose tick, to a clock value `t` with `T₁ ≤ t ≤ t₀`, puts
an attestation above `H₂` on the wire by a validator outside the adversary set at `t`; `t` is a round's
action time `aR M S r` (`eq_aR_of_honestAttestationAt`). A tick at a step before `k₀` is to a clock
value at most `aR M S r`, and a tick at a step after `k₀` to a clock value at least `aR M S r`: two ticks
to action times of different rounds are at least four delays apart (`aR_add_le_of_lt`), more than both
clock bounds together (`hSkew`, `tick_active`). So every honest attestation at a tick before `aR M S r`,
or at a step before `k₀`, is at most `H₂`: before `T₁` by `OldHeightAttained`, from `T₁` on by the
minimality.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `T₁`: the time of the threshold;
  `H₂`: the threshold; `t₀`: the time of the given attestation; `tAwakeEnd`: the honesty time of
  the step form; `u`: its sender; `a₀`: the attestation.

Read aloud: the first step at which a validator honest through its clock value attests above the
threshold is a tick to a round's action time, and before it nothing honest was above the threshold. -/
theorem first_attestation_above_bound (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (T₁ H₂ t₀ tAwakeEnd : ℕ) (u : V) (a₀ : Attestation V)
    (hH₂ : OldHeightAttained M S A x T₁ H₂)
    (ht₀ : T₁ ≤ t₀) (hEnd : t₀ ≤ tAwakeEnd)
    (hSend : HonestAttestationAt M S A x t₀ u a₀ ∧ u ∉ A.corruptedAtTime x t₀) (ha₀ : H₂ < a₀.h) :
    ∃ r : ℕ, T₁ ≤ aR M S r ∧ aR M S r ≤ t₀ ∧ OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂ ∧
      ∃ (v : V) (a : Attestation V), HonestAttestationAt M S A x (aR M S r) v a ∧
        v ∉ A.corruptedAtTime x (aR M S r) ∧ H₂ < a.h ∧
        ∃ k₀ : ℕ, x.lbl k₀ = Event.tick v (aR M S r) ∧
          (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k₀ + 1) - x.sent k₀ ∧
          ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < k₀ → x.lbl k = Event.tick u t →
            u ∉ A.corruptedAtTime x tAwakeEnd →
            (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂ := by
  classical
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hP : ∃ k : ℕ, ∃ (v : V) (t : ℕ) (a : Attestation V), x.lbl k = Event.tick v t ∧ T₁ ≤ t ∧ t ≤ t₀ ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k ∧
      v ∉ A.corruptedAtTime x t ∧ H₂ < a.h := by
    obtain ⟨⟨i₀, hl₀, hs₀⟩, hu₀⟩ := hSend
    exact ⟨i₀, u, t₀, a₀, hl₀, ht₀, le_rfl, hs₀, hu₀, ha₀⟩
  obtain ⟨v, t, a, hl, hT, ht0, hs, hvH, ha⟩ := Nat.find_spec hP
  obtain ⟨r, hr⟩ := (eq_aR_of_honestAttestationAt M F U) S A x R E t v a ⟨Nat.find hP, hl, hs⟩
  subst hr
  have hk0 := (E.tick_active _ v _ hl).2
  -- a tick at a step at most the least step is to an action time at most `aR M S r`
  have hbefore : ∀ (k t' : ℕ) (u' : V) (a' : Attestation V), k ≤ Nat.find hP → x.lbl k = Event.tick u' t' →
      (⟨u', NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k →
      t' ≤ aR M S r := by
    intro k t' u' a' hk hl' hs'
    obtain ⟨r', hr'⟩ := (eq_aR_of_honestAttestationAt M F U) S A x R E t' u' a' ⟨k, hl', hs'⟩
    subst hr'
    by_contra hgt
    have hlt : r < r' := by
      rcases lt_trichotomy r' r with h | h | h
      · have := aR_add_le_of_lt M F U S h; omega
      · subst h; omega
      · exact h
    have h4 : ((aR M S r + 4 * Δ S : ℕ) : ℝ) ≤ (aR M S r' : ℝ) := by exact_mod_cast aR_add_le_of_lt M F U S hlt
    push_cast at h4
    have hkt := (E.tick_active k u' _ hl').2
    have hm := (time_mono M) x R hk
    linarith [hkt.1, hk0.2]
  -- a tick at a step at least the least step is to an action time at least `aR M S r`
  have hafter : ∀ (k t' : ℕ) (u' : V) (a' : Attestation V), Nat.find hP ≤ k → x.lbl k = Event.tick u' t' →
      (⟨u', NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k →
      aR M S r ≤ t' := by
    intro k t' u' a' hk hl' hs'
    obtain ⟨r', hr'⟩ := (eq_aR_of_honestAttestationAt M F U) S A x R E t' u' a' ⟨k, hl', hs'⟩
    subst hr'
    by_contra hgt
    have hlt : r' < r := by
      rcases lt_trichotomy r' r with h | h | h
      · exact h
      · subst h; omega
      · have := aR_add_le_of_lt M F U S h; omega
    have h4 : ((aR M S r' + 4 * Δ S : ℕ) : ℝ) ≤ (aR M S r : ℝ) := by exact_mod_cast aR_add_le_of_lt M F U S hlt
    push_cast at h4
    have hkt := (E.tick_active k u' _ hl').2
    have hm := (time_mono M) x R hk
    linarith [hkt.2, hk0.1]
  refine ⟨r, hT, ht0, ?_, v, a, ⟨Nat.find hP, hl, hs⟩, hvH, ha, Nat.find hP, hl, hs, ?_⟩
  · intro i t' w b hl' ht' hHonR hm
    by_cases hlt : t' < T₁
    · exact hH₂.1 i t' w b hl' (by exact_mod_cast hlt)
        ((not_mem_corruptedAtTime_of_le M) x R E (by exact_mod_cast hT) hHonR) hm
    · by_contra hgt
      have ht'N : t' < aR M S r := by exact_mod_cast ht'
      have hki : Nat.find hP ≤ i := Nat.find_min' hP ⟨w, t', b, hl', Nat.le_of_not_lt hlt, by omega, hm,
        (not_mem_corruptedAtTime_of_le M) x R E ht'N.le hHonR, Nat.lt_of_not_le hgt⟩
      have := hafter i t' w b hki hl' hm
      omega
  · intro k t' u' a' hk hl' hu' hs'
    by_cases hlt : t' < T₁
    · exact hH₂.1 k t' u' a' hl' (by exact_mod_cast hlt)
        ((not_mem_corruptedAtTime_of_le M) x R E (show T₁ ≤ tAwakeEnd by omega) hu') hs'
    · by_contra hgt
      have hle := hbefore k t' u' a' hk.le hl' hs'
      exact Nat.find_min hP hk ⟨u', t', a', hl', Nat.le_of_not_lt hlt, by omega, hs',
        (not_mem_corruptedAtTime_of_le M) x R E (show t' ≤ tAwakeEnd by omega) hu', Nat.lt_of_not_le hgt⟩

/-- **B4, the fast block at the first round above the threshold.** The proof; the audited
statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: A1 gives the fast block `L` of a node state `n'` that `v`'s update at `a_r` can leave,
held in `v`'s tick input, the state at step `k₀`, with `h(L) = a.h > H₂`; `attested_height_bound_before`
at `k₀` bounds `h(L) ≤ H₂ + 1`. The
landed conclusion names the update's answer; the twin names a node state the update can leave,
as A1's twin does.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tAwakeEnd`: the phase's end; `r`:
  the round; `H₂`: the threshold; `k₀`: the step of `v`'s tick; `v`: the attester; `a`: the
  attestation.

Read aloud: the first honest validator above the threshold has just fast-confirmed a block exactly
one height above it. -/
theorem fast_block_at_first_round (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (tAwakeEnd r H₂ k₀ : ℕ) (v : V) (a : Attestation V)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hk₀ : x.lbl k₀ = Event.tick v (aR M S r))
    (hSend : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k₀ + 1) - x.sent k₀)
    (hOld : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < k₀ → x.lbl k = Event.tick u t →
      u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂)
    (hEnd : x.time k₀ ≤ tAwakeEnd) (ha : H₂ < a.h) :
    ∃ (n' : M.N) (L : Block V),
      ConfirmationUpdated M S.C S.P (x.tickInput v (aR M S r)) ((aR M S r : ℕ) : Int)
        (r * S.C.R + 1) n' ∧
      L ∈ n'.fastBlocks ∧ L ∈ (x.tickInput v (aR M S r)).tree ∧
      (M.chainStateOf S.C L).h = H₂ + 1 := by
  obtain ⟨n', L, hUpd, hFast, hLv, hLh⟩ :=
    (fast_block_of_honest_attestation M F U) S A x R E r v a ⟨k₀, hk₀, hSend⟩
  have hti : x.tickInput v (aR M S r) = x.st k₀ v := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk₀]
  have hle : (M.chainStateOf S.C L).h ≤ H₂ + 1 :=
    (attested_height_bound_before M F Fx) S A x R E k₀ H₂ v L tAwakeEnd hEnd hThird hOld
      (by rw [← hti]; exact hLv)
  refine ⟨n', L, hUpd, hFast, hLv, ?_⟩
  unfold Height at *
  omega

end GoldilocksCorrectness.Record.Proofs.Executions

