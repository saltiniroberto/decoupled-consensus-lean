module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89CountJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89ClimbUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.NetworkUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Executions.Lemma89CountJUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89CountJUpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89CountJUpTo.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the steps of the climb's count with
the delivery premises up to a bound, namely a held block's spreading with its consequences for the
justification height and the greatest chain-state height, the bundle `ClimbCtxUpTo` of the count's
hypotheses with its readers, and `fork_choice_change_kinds_upTo`, every fork-choice change of the
climb being one of four kinds. The page's routine-level theorems are the facts' fields or have their
twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ)
open GoldilocksCorrectness.Proofs.Routines (slot_mono slot_mono_int)

open GoldilocksCorrectness.Proofs.Routines (block_admissible_of mem_T_receive_block)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery EnvFactsDeliveryUpTo SyncedWithin SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

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
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **A held block reaches every honest awake validator by its tick one delay later, or is low.** From
`GST` on, with the execution assumptions and unforgeability: when `u`, honest at the step `stepBefore M x t₁`
(`t₁ ≤ t`), holds `D` before `t₁`, and `w` ticks at `kR` to a clock value `c` at least one delay after `t`, active
from `a` up to that tick, then at `kR` either `w` holds `D` with its finalized block `D` or an ancestor of `D`, or
`D`'s chain-state height is at most `w`'s cache `h_j`.

Restated: the receiver is read at its tick `kR` (`x.st kR w`) rather than before the real
time `t + Δ S`, which a tick to `t + Δ S` can follow by up to `ΔClockBehind`; the roots are read until the real time
of `kR`, and `tEnd` is at least that time.

Restated with the delivery premises up to `t + Δ S`: the deadline of the one delivery its proof reads.

Why: when `D` is higher than `w`'s `h_j` at `kR`, `w`'s finalized block there is an ancestor of `D`
(`F_ancestorEq_of_high_st`), so compatible with it, and the network delivers `D` by that tick
(`mem_T_before_add_delay_of_held_at_upTo`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `GST`, `tEnd`, `t₁`, `t`: the times;
  `u`: the holder; `w`: the receiver; `D`: the block; `c`, `kR`: the clock value and the step of `w`'s tick;
  `c₂`, `k₂`: those of `w`'s earlier tick.

Read aloud: a block an honest validator holds is held, at its tick one delay later, by every awake honest
validator with its finalized block `D` or an ancestor of `D`, or has chain-state height at most that
validator's justification height. -/
theorem held_spread_upTo (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST tEnd t₁ t kR c k₂ c₂ : ℕ) (u w : V) (D : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (t + Δ S)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (t + Δ S))
    (hRoots : RootsNameBlocksUntil M A x (x.time kR))
    (hParent : ParentHeldAtDelivery M x)
    -- `a` is from `GST` on, at least one delay or one sync delay before `t + Δ S`, and at or before `t₁`
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ t + Δ S) (ha₁ : a ≤ t₁)
    -- the holder `u` is active from `a` through the sync delay after it
    (hu₀ : u ∈ A.activeThroughout x a (a + Δs))
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (ht₁t : t₁ ≤ t) (hEnd : x.time kR ≤ tEnd)
    (hu : u ∉ A.corrupted (x.stepBefore t₁))
    (hD : D ∈ (x.stateBefore t₁ u).tree)
    -- `u` serves `D`: its finalized block before `t₁` is compatible with `D`
    (hsel : (x.stateBefore t₁ u).finalized.compatible D = true)
    -- the receiver `w` ticks to `c`, at least one delay after `t`, active at every step from the real time `a` up to
    -- that tick; it ticked to `c₂`, at least the start of `D`'s slot and at least one delay before `c`
    (hc : t + Δ S ≤ c) (hkR : x.lbl kR = Event.tick w c)
    (hwR : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → w ∈ A.active i)
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : c₂ + Δ S ≤ c) (hDc₂ : M.slotStart S.C D.slot ≤ c₂) :
    (D ∈ (x.st kR w).tree ∧ (x.st kR w).finalized.AncestorEq D)
      ∨
      (M.chainStateOf S.C D).h ≤ (x.st kR w).justifiedHeight := by
  by_cases hlt : (x.st kR w).justifiedHeight < (M.chainStateOf S.C D).h
  · have hwkR : w ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
    have hD' : D ∈ (x.st (x.stepBefore t₁) u).tree := hD
    have hst : x.time (x.stepBefore t₁) ≤ x.time kR := by
      have h1 := (time_stepBefore_le M) x R E t₁
      have h2 := (E.tick_active kR w c hkR).2.1
      have hA0 := E.ahead_nonneg
      have hB0 := E.behind_nonneg
      have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
      have h3 : (t₁ : ℝ) + Δ S ≤ c := by exact_mod_cast (show t₁ + Δ S ≤ c by omega)
      have h4 : (0 : ℝ) < Δ S := by exact_mod_cast hΔ
      linarith
    have hFD := (F_ancestorEq_of_high_st M F Fx) S A x R E hRoots tEnd kR (x.stepBefore t₁) w u D hThird
      hEnd (le_trans hst hEnd) hwkR hu hD' hlt (max_le le_rfl hst)
    refine Or.inl ⟨?_, hFD⟩
    exact (mem_T_before_add_delay_of_held_at_upTo M F U R) E hNet hSkew hRedeliver Sy hRoots hParent ht₁t
      a hGSTa ha₁ hu₀ hu hsel hD hc hkR hwR hk₂ hc₂ hDc₂ ha ((compatible_iff _ _).2 (Or.inl hFD))
  · exact Or.inr (Nat.le_of_not_lt hlt)

/-- **A held block's justification height reaches every honest awake validator's `h_j` by its tick one
delay later.** Under `held_spread_upTo`'s hypotheses, `D`'s justification height is at most `w`'s `h_j` at its
tick `kR`: when `w` holds `D` on its finalized block's chain, by the cache (Lemma 57); otherwise `D`'s
justification height is less than its height (Lemma 47), at most `w`'s `h_j`.

Restated: at `w`'s tick `kR`, as `held_spread_upTo`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- the others as in `held_spread_upTo`.

Read aloud: a held block's justification height is, at a receiver's tick one delay later, at most every awake
honest validator's justification height. -/
theorem held_spread_h_j_upTo (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST tEnd t₁ t kR c k₂ c₂ : ℕ) (u w : V) (D : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (t + Δ S)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (t + Δ S))
    (hRoots : RootsNameBlocksUntil M A x (x.time kR))
    (hParent : ParentHeldAtDelivery M x)
    -- `a` is from `GST` on, at least one delay or one sync delay before `t + Δ S`, and at or before `t₁`
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ t + Δ S) (ha₁ : a ≤ t₁)
    -- the holder `u` is active from `a` through the sync delay after it
    (hu₀ : u ∈ A.activeThroughout x a (a + Δs))
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (ht₁t : t₁ ≤ t) (hEnd : x.time kR ≤ tEnd)
    (hu : u ∉ A.corrupted (x.stepBefore t₁))
    (hD : D ∈ (x.stateBefore t₁ u).tree)
    -- `u` serves `D`: its finalized block before `t₁` is compatible with `D`
    (hsel : (x.stateBefore t₁ u).finalized.compatible D = true)
    -- the receiver `w` ticks to `c`, at least one delay after `t`, active at every step from the real time `a` up to
    -- that tick; it ticked to `c₂`, at least the start of `D`'s slot and at least one delay before `c`
    (hc : t + Δ S ≤ c) (hkR : x.lbl kR = Event.tick w c)
    (hwR : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → w ∈ A.active i)
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : c₂ + Δ S ≤ c) (hDc₂ : M.slotStart S.C D.slot ≤ c₂) :
    (M.chainStateOf S.C D).h_j ≤ (x.st kR w).justifiedHeight := by
  rcases (held_spread_upTo M F) U Fx S A x R GST tEnd t₁ t kR c k₂ c₂ u w D E hNet hSkew hRedeliver Sy hRoots hParent
    a hGSTa ha ha₁ hu₀ hThird ht₁t hEnd hu hD hsel hc hkR hwR hk₂ hc₂ hDc₂ with ⟨hDw, hFD⟩ | hle
  · exact (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E kR w D hDw hFD
  · have h47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1.2.1
    unfold Height at *
    omega

/-- **A held block's height reaches every honest awake validator's greatest chain-state height by its
tick one delay later.** Under `held_spread_upTo`'s hypotheses, `D`'s chain-state height is at most `w`'s
greatest chain-state height at its tick `kR`: a held block is at most the greatest chain-state height
(Lemma 46), and `h_j` is less than the greatest chain-state height.

Restated: at `w`'s tick `kR`, as `held_spread_upTo`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- the others as in `held_spread_upTo`.

Read aloud: a held block's chain-state height is, at a receiver's tick one delay later, at most every awake
honest validator's greatest chain-state height. -/
theorem held_spread_h_max_upTo (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST tEnd t₁ t kR c k₂ c₂ : ℕ) (u w : V) (D : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (t + Δ S)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (t + Δ S))
    (hRoots : RootsNameBlocksUntil M A x (x.time kR))
    (hParent : ParentHeldAtDelivery M x)
    -- `a` is from `GST` on, at least one delay or one sync delay before `t + Δ S`, and at or before `t₁`
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ t + Δ S) (ha₁ : a ≤ t₁)
    -- the holder `u` is active from `a` through the sync delay after it
    (hu₀ : u ∈ A.activeThroughout x a (a + Δs))
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (ht₁t : t₁ ≤ t) (hEnd : x.time kR ≤ tEnd)
    (hu : u ∉ A.corrupted (x.stepBefore t₁))
    (hD : D ∈ (x.stateBefore t₁ u).tree)
    -- `u` serves `D`: its finalized block before `t₁` is compatible with `D`
    (hsel : (x.stateBefore t₁ u).finalized.compatible D = true)
    -- the receiver `w` ticks to `c`, at least one delay after `t`, active at every step from the real time `a` up to
    -- that tick; it ticked to `c₂`, at least the start of `D`'s slot and at least one delay before `c`
    (hc : t + Δ S ≤ c) (hkR : x.lbl kR = Event.tick w c)
    (hwR : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → w ∈ A.active i)
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : c₂ + Δ S ≤ c) (hDc₂ : M.slotStart S.C D.slot ≤ c₂) :
    (M.chainStateOf S.C D).h ≤ hMax M S.C (x.st kR w) := by
  rcases (held_spread_upTo M F) U Fx S A x R GST tEnd t₁ t kR c k₂ c₂ u w D E hNet hSkew hRedeliver Sy hRoots hParent
    a hGSTa ha ha₁ hu₀ hThird ht₁t hEnd hu hD hsel hc hkR hwR hk₂ hc₂ hDc₂ with ⟨hDw, -⟩ | hle
  · exact le_hMax M hDw
  · have h := (h_j_lt_h_max_st M F) S A x R E kR w
    unfold Height at *
    omega

/-- `ClimbCtxUpTo M S Sched x GST tGAT tAwakeEnd T₁ r H₂ k₀`: the hypotheses of `fork_choice_change_kinds`
that its proof reads: the execution assumptions, unforgeability, every validator honest in the
phase awake then, fewer than a third in the adversary set up to its end, the threshold `H₂` at `T₁`
and every honest attestation before `aR M S r` at most `H₂`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round; `H₂`: the threshold.

Roots name blocks until `aR M S r`: every reader of the bundle compares blocks held before times at
most `aR M S r`, the end of the climb.

Restated with the delivery premises up to `aR M S r`: the bound of its roots `hRoots`, the end of
the climb; every reader of the bundle reads deliveries due by then.

Read aloud: the hypotheses of `fork_choice_change_kinds_upTo` that its proof reads. -/
structure ClimbCtxUpTo (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (GST tGAT tAwakeEnd T₁ r H₂ : ℕ) (k₀ : ℕ) (Δs : ℕ) (release : (NamedObject V) → Option ℕ) (ΔRedeliver : ℕ) (ΔClockAhead ΔClockBehind : ℝ) (ΔNet : ℕ) : Prop where
  /-- Blocks and Goldfish votes due by the bound are delivered within `Δ` after `GST`. -/
  E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST release acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (aR M S r)
  /-- The network delay and the two clock bounds fit in the delay `Δ S`. -/
  hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S
  /-- The two clock bounds together are less than one delay `Δ S`. -/
  hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S
  /-- A re-delivery after the receiver's clock reaches an object's release clock value, plus both clock bounds, fits in one delay `Δ S`. -/
  hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S
  /-- What an honest validator active at a time `t` would serve at `t` reaches every validator active
  from `t` within `Δs` of the later of `t` and `GST`, when that is at most the bound. -/
  Sy : GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinUpTo A x (servesMin M S.C) acObject release ΔRedeliver Δs GST (aR M S r)
  /-- The sync delay is at most the protocol's slow window less three delays. -/
  hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k
  hRoots : RootsNameBlocksUntil M A x (aR M S r)
  hParent : ParentHeldAtDelivery M x
  hGST : GST ≤ tGAT
  /-- The recovery delay less one delay after `tGAT` has elapsed by `T₁`. -/
  hT₁ : tGAT + Δs ≤ T₁
  hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd
  hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
    v ∉ A.corrupted i → v ∈ A.awake i
  hH₂ : OldHeightAttained M S A x T₁ H₂
  hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂
  hEnd : aR M S r ≤ tAwakeEnd
  /-- Every attestation put on the wire by a tick at a step before `k₀`, by a validator outside the adversary set
  at `tAwakeEnd`, has height at most `H₂`. -/
  hOldStep : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < k₀ → x.lbl k = Event.tick u t →
    u ∉ A.corruptedAtTime x tAwakeEnd →
    (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂
  /-- The time of step `k₀` is in the phase. -/
  hEndStep : x.time k₀ ≤ tAwakeEnd
  /-- In the phase, a validator outside the adversary set at its tick to a clock value at least
  `T₁ + Δ S` also ticked to the clock value one delay earlier. -/
  hTick : ∀ (c : ℕ) (w : V) (k : ℕ), T₁ ≤ c → x.lbl k = Event.tick w (c + Δ S) →
    x.time k ≤ tAwakeEnd → w ∉ A.corrupted k → ∃ k' : ℕ, x.lbl k' = Event.tick w c

/-- **The climb's bundle at the first step whose real time reaches the support cutoff of slot `r R`**
. From the clock form `hOld` at `aR M S r`, with `tGAT` at most that
support cutoff: `ClimbCtxUpTo` at `k₀ := x.firstAt (M.supportCutoff S.C (r * S.C.R))`.

Why: every step before `k₀` is at a real time less than the support cutoff of slot `r R`, so a tick there is to a clock
value less than that cutoff plus `ΔClockAhead`, less than `aR M S r` (four delays later); a validator outside the
adversary set at `tAwakeEnd` is outside it at `aR M S r`; so `hOld` bounds the attestation (`hOldStep`). Some validator
is outside the adversary set at every step up to `tAwakeEnd` (fewer than a third ever are), so it is awake from `tGAT`
and ticks to one delay after the cutoff, at a real time from the cutoff to `aR M S r`; `k₀` is at or before that tick
(`hEndStep`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; the rest as `ClimbCtxUpTo`'s fields.

Read aloud: the hypotheses of the climb's count hold at the first step whose real time reaches the support cutoff of
slot `r R`. -/
theorem ClimbCtxUpTo.of_clock (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GST tGAT tAwakeEnd T₁ r H₂ : ℕ}
    {Δs : ℕ} {release : (NamedObject V) → Option ℕ} {ΔRedeliver : ℕ} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST release acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (aR M S r))
    (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinUpTo A x (servesMin M S.C) acObject release ΔRedeliver Δs GST (aR M S r))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (aR M S r))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hT₁ : tGAT + Δs ≤ T₁)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hH₂ : OldHeightAttained M S A x T₁ H₂)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hTick : ∀ (c : ℕ) (w : V) (k : ℕ), T₁ ≤ c → x.lbl k = Event.tick w (c + Δ S) →
      x.time k ≤ tAwakeEnd → w ∉ A.corrupted k → ∃ k' : ℕ, x.lbl k' = Event.tick w c)
    -- the phase starts no later than the support cutoff of slot `r R`
    (htG : tGAT ≤ M.supportCutoff S.C (r * S.C.R)) :
    ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ (x.firstAt (M.supportCutoff S.C (r * S.C.R))) Δs release ΔRedeliver
      ΔClockAhead ΔClockBehind ΔNet := by
  classical
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have haR : aR M S r = M.supportCutoff S.C (r * S.C.R) + 4 * Δ S := by
    unfold aR
    exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S _
  set c₀ := M.supportCutoff S.C (r * S.C.R) with hc₀
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hex : ∃ i : ℕ, (c₀ : ℝ) ≤ x.time i := E.time_div c₀
  have hfa : x.firstAt c₀ = Nat.find hex := by
    unfold Trace.firstAt
    rw [dif_pos hex]
  -- a step before `k₀` is at a real time less than `c₀`
  have hbefore : ∀ k : ℕ, k < x.firstAt c₀ → x.time k < (c₀ : ℝ) := by
    intro k hk
    rw [hfa] at hk
    exact not_le.1 (Nat.find_min hex hk)
  -- a validator outside the adversary set at every step up to `tAwakeEnd`
  obtain ⟨v, hv⟩ : ∃ v : V, ∀ i : ℕ, x.time i ≤ tAwakeEnd → v ∉ A.corrupted i := by
    by_contra hno
    push Not at hno
    have h3 := hThird Finset.univ (fun v _ => hno v)
    rw [Finset.card_univ] at h3
    unfold validator_count at h3
    omega
  -- it ticks to one delay after `c₀`
  have hvA : v ∈ A.activeThroughout x (((c₀ + Δ S : ℕ) : ℝ) - ΔClockAhead) (((c₀ + Δ S : ℕ) : ℝ) + ΔClockBehind) := by
    refine Activity.mem_activeThroughout.2 fun i h1 h2 => ?_
    have hiE : x.time i ≤ tAwakeEnd := by
      have : ((c₀ + Δ S : ℕ) : ℝ) + Δ S ≤ (tAwakeEnd : ℝ) := by
        exact_mod_cast (show c₀ + Δ S + Δ S ≤ tAwakeEnd by omega)
      linarith
    have hci := hv i hiE
    refine Activity.mem_active.2 ⟨hAwake i v hiE ?_ hci, hci⟩
    have h1' := htime (Nat.le_succ i)
    have : (tGAT : ℝ) + Δ S ≤ ((c₀ + Δ S : ℕ) : ℝ) := by exact_mod_cast (show tGAT + Δ S ≤ c₀ + Δ S by omega)
    linarith
  have hkv := (tickStep_spec M) x R E (t := c₀ + Δ S) (v := v) (by omega) hvA
  have hk₀v : x.firstAt c₀ ≤ x.tickStep v (c₀ + Δ S) := by
    rw [hfa]
    refine Nat.find_min' hex ?_
    have : (c₀ : ℝ) + Δ S - ΔClockAhead ≤ x.time (x.tickStep v (c₀ + Δ S)) := by
      have h := hkv.2.1
      push_cast at h
      linarith
    linarith
  exact
    { E := E, hNet := hNet, hSkew := hSkew, hRedeliver := hRedeliver, Sy := Sy, hΔs := hΔs, hRoots := hRoots,
      hParent := hParent, hGST := hGST, hT₁ := hT₁, hThird := hThird, hAwake := hAwake, hH₂ := hH₂, hOld := hOld,
      hEnd := hEnd,
      hOldStep := fun k t u a' hk hl hu hs => by
        have h1 := (E.tick_active k u t hl).2.1
        have h2 := hbefore k hk
        refine hOld k t u a' hl ?_ ((not_mem_corruptedAtTime_of_le M) x R E hEnd hu) hs
        rw [haR]
        push_cast
        linarith
      hEndStep := by
        have h := htime hk₀v
        have h2 := hkv.2.2
        have : ((c₀ + Δ S : ℕ) : ℝ) + ΔClockBehind ≤ (tAwakeEnd : ℝ) := by
          have : ((c₀ + Δ S : ℕ) : ℝ) + Δ S ≤ (tAwakeEnd : ℝ) := by
            exact_mod_cast (show c₀ + Δ S + Δ S ≤ tAwakeEnd by omega)
          linarith
        linarith
      hTick := hTick }

namespace ClimbCtxUpTo
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd T₁ r H₂ : ℕ} {k₀ : ℕ}

/-- B2 in the context: from `T₁ + Δ` to `aR M S r`, an honest validator's greatest chain-state
height is `H₂` or `H₂ + 1`.

Restated with the delivery premises up to `aR M S r`: the bound of the bundle `ClimbCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: from `T₁ + Δ` to `aR M S r`, an honest validator's greatest chain-state height is `H₂`
or `H₂ + 1`. -/
theorem bounds (U : UniformSchedule M.toSlotLayout) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {t : ℕ} {w : V}
    (h1 : T₁ + Δ S ≤ t) (k : ℕ) (hk : x.lbl k = Event.tick w t) (h2 : k ≤ k₀)
    (hka : x.time k ≤ aR M S r) (hta : t ≤ aR M S r) (hw : w ∉ A.corrupted k) :
    H₂ ≤ hMax M S.C (x.tickInput w t) ∧ hMax M S.C (x.tickInput w t) ≤ H₂ + 1 := by
  have hks := (tickStep_eq_of_lbl M) x E hk
  have hkE : x.time k ≤ tAwakeEnd := le_trans (R.time_mono h2) C.hEndStep
  refine ⟨?_, ?_⟩
  · -- the lower bound: Lemma 89b at `w`'s tick `k` to `t`, read at its tick to `t − Δ` (the bundle's `hTick`)
    have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
    have hwc := C.hTick (t - Δ S) w k (by omega) (by rw [Nat.sub_add_cancel (by omega)]; exact hk) hkE hw
    exact old_height_le_hMax_at_tick M F U Fx S A x R GST tGAT tAwakeEnd T₁ H₂ (aR M S r) t (t - Δ S) k w
      C.E C.hNet C.hSkew C.hRedeliver C.Sy C.hΔs C.hParent C.hGST C.hT₁ C.hThird C.hAwake C.hH₂ hk hkE
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hka C.hRoots) hw
      (by omega) (by omega) hwc hta
  · -- the upper bound: A2 at `w`'s tick `k`, a step at most `k₀`
    obtain ⟨-, ⟨X, hX, hXh⟩, -⟩ := (cachesWitnessed_of_exec M F) S A x R E k w
    show hMax M S.C (x.st (x.tickStep w t) w) ≤ H₂ + 1
    rw [hks, ← hXh]
    exact (GoldilocksCorrectness.Record.Proofs.Executions.held_height_le_before_action M F Fx) S A x R E
      tAwakeEnd H₂ k₀ k w X C.hThird C.hOldStep C.hEndStep h2 hX

/-- Before `aR M S r`, every validator's greatest chain-state height is at most `H₂ + 1` (A2).

Restated with the delivery premises up to `aR M S r`: the bound of the bundle `ClimbCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: before `aR M S r`, every validator's greatest chain-state height is at most `H₂ + 1`. -/
theorem hmax_le (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {t : ℕ} (w : V)
    (h2 : x.stepBefore t ≤ k₀) : hMax M S.C (x.stateBefore t w) ≤ H₂ + 1 := by
  obtain ⟨-, ⟨X, hX, hXh⟩, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_stateBefore M F) S A x R E t w
  rw [← hXh]
  exact (GoldilocksCorrectness.Record.Proofs.Executions.held_height_le_before_action M F Fx) S A x R E tAwakeEnd H₂ k₀
    (x.stepBefore t) w X C.hThird C.hOldStep C.hEndStep h2 hX

/-- `bounds` at a configuration: a validator outside the adversary set at a step `j` at a time after
`T₁ + Δ` and before `aR M S r` has its greatest chain-state height at `H₂` or `H₂ + 1` there. It is
outside the adversary set at every step at the time `T₁ + Δ` (they come before `j`), so `bounds` holds
before `T₁ + Δ`, and the greatest chain-state height does not decrease up to `j`; the upper bound is A2
(`hmax_le_st`).

Restated with the delivery premises up to `aR M S r`: the bound of the bundle `ClimbCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle; `w`: the
  validator; `j`: the step.

Read aloud: from after `T₁ + Δ` to before `aR M S r`, an honest validator's greatest chain-state height
is `H₂` or `H₂ + 1`. -/
theorem bounds_st (U : UniformSchedule M.toSlotLayout) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {j : ℕ} {w : V}
    {c k : ℕ} (hc : T₁ + Δ S ≤ c) (hk : x.lbl k = Event.tick w c) (hsj : k ≤ j)
    (hw : w ∉ A.corrupted j) (h2 : j ≤ k₀) (hja : x.time j ≤ aR M S r) (hca : c ≤ aR M S r) :
    H₂ ≤ hMax M S.C (x.st j w) ∧ hMax M S.C (x.st j w) ≤ H₂ + 1 := by
  have hb := C.bounds M F U R E Fx (t := c) (w := w) hc k hk (le_trans hsj h2) (le_trans (R.time_mono hsj) hja) hca
    (fun h => hw (E.corrupted_mono k j hsj h))
  have hks := (tickStep_eq_of_lbl M) x E hk
  have hb1 : H₂ ≤ hMax M S.C (x.st k w) := by
    have h := hb.1
    unfold Trace.tickInput at h
    rwa [hks] at h
  refine ⟨le_trans hb1 ((h_max_mono_st M F) S A x R E w hsj), ?_⟩
  obtain ⟨-, ⟨X, hX, hXh⟩, -⟩ := (cachesWitnessed_of_exec M F) S A x R E j w
  rw [← hXh]
  exact (GoldilocksCorrectness.Record.Proofs.Executions.held_height_le_before_action M F Fx) S A x R E
    tAwakeEnd H₂ k₀ j w X C.hThird C.hOldStep C.hEndStep h2 hX

/-- A2 at a configuration: at a step before `aR M S r`, every validator's greatest chain-state height is
at most `H₂ + 1`.

Restated with the delivery premises up to `aR M S r`: the bound of the bundle `ClimbCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle; `w`: the
  validator; `j`: the step.

Read aloud: before `aR M S r`, every validator's greatest chain-state height is at most `H₂ + 1`. -/
theorem hmax_le_st (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {j : ℕ} (w : V)
    (h2 : j ≤ k₀) : hMax M S.C (x.st j w) ≤ H₂ + 1 := by
  obtain ⟨-, ⟨X, hX, hXh⟩, -⟩ := (cachesWitnessed_of_exec M F) S A x R E j w
  rw [← hXh]
  exact (GoldilocksCorrectness.Record.Proofs.Executions.held_height_le_before_action M F Fx) S A x R E
    tAwakeEnd H₂ k₀ j w X C.hThird C.hOldStep C.hEndStep h2 hX

/-- From a time `τ` of the climbing phase (`T₁ ≤ τ`), the window of one delay or one sync delay before
`τ + 1 + Δ` starts at or after `tGAT`, where every validator outside the adversary set is awake.

Why: the bundle's line `tGAT + Δs ≤ T₁` and `T₁ ≤ τ`.

The variables:
- `M`: the model; `F`: its facts; `C`: the bundle; `τ`: the time.

Read aloud: the sync window before `τ + 1 + Δ` lies in the phase. -/
theorem syncWindow {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {τ : ℕ} (hT : T₁ ≤ τ) :
    tGAT + max (Δ S) Δs ≤ τ + 1 + Δ S := by
  have := C.hT₁
  omega

/-- A validator honest at `t ≤ tAwakeEnd` is awake and honest at every time of the phase up to
`t`.

Restated with the delivery premises up to `aR M S r`: the bound of the bundle `ClimbCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `C`: the bundle.

Read aloud: a validator honest at `t ≤ tAwakeEnd` is awake and honest at every time of the phase up
to `t`. -/
theorem awakeHonest (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {Δs : ℕ} {ΔNet : ℕ} (C : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {w : V} {t : ℕ}
    (hw : w ∉ A.corruptedAtTime x t) (ht : t ≤ tAwakeEnd) :
    w ∈ A.activeThroughout x tGAT t :=
  (mem_activeThroughout_of_hAwake_honest_at M F) R E C.hAwake le_rfl ht hw

/-- **A receiver's tick to `τ + Δ` before `aR M S r` puts `τ` before `aR M S r`.** The real time of `w`'s tick `kT` to
`τ + Δ` is at least `τ + Δ − ΔClockAhead`, more than `τ` since `ΔClockAhead < Δ` (`hSkew`), and at most the time of a
later step `i` before `aR M S r`.

The variables:
- `M`: the model; `F`: its facts; `C`: the bundle; `τ`: the clock value; `kT`: `w`'s tick to `τ + Δ`; `i`: a later step.

Read aloud: a validator's tick to `τ + Δ`, at or before a step before `aR M S r`, makes `τ` at most `aR M S r`. -/
theorem tau_le_aR (R : RunFacts M S x) {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    (C : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {τ kT i : ℕ} {w : V} (hkT : x.lbl kT = Event.tick w (τ + Δ S)) (hsi : kT ≤ i) (hta : x.time i < aR M S r) :
    (τ : ℝ) ≤ aR M S r := by
  have h1 := (C.E.tick_active kT w (τ + Δ S) hkT).2.1
  have h2 := R.time_mono hsi
  have hB := C.E.behind_nonneg
  have hS := C.hSkew
  push_cast at h1
  linarith

/-- `held_spread` in the context, holder at a step: a block `D` that `u` holds at a step `j` whose real time
is after `T₁` and whose real time and clock value are at most `τ`, with `u` outside the adversary set at `j` and
its finalized block there compatible with `D`, is, at every step `i` from `w`'s tick to `τ + Δ` on and before
`aR M S r` with `w` outside the adversary set at `i`, in `w`'s tree with `w`'s finalized block an ancestor of
`D` or `D`, or has chain-state height at most `w`'s justification height.

Why: when `D` is higher than `w`'s justification height at `i`, `w`'s finalized block there is an ancestor of
`D` (`F_ancestorEq_of_high_st`); the genesis block is in every tree; otherwise `block_at_tick_of_held_step`
puts `D` in `w`'s tree at its tick to `τ + Δ` (the window from `T₁ − Δs`, where `u` is honest and awake
since its step `j` comes later; `w`'s tick to `τ` by `hTick`; `D`'s slot starts at most at `u`'s clock value
at `j`), and trees grow.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `C`: the
  bundle; `τ`: the clock value; `j`: the holder's step; `kT`: `w`'s tick to `τ + Δ`; `i`: the receiver's
  step.

Read aloud: a block `u` holds at a step by `τ` reaches `w` by its tick to `τ + Δ`, or has chain-state height
at most `w`'s justification height. -/
theorem spread (U : UniformSchedule M.toSlotLayout) (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {τ j i kT : ℕ} {u w : V}
    {D : Block V} (hT : (T₁ : ℝ) < x.time j) (hj : x.time j ≤ τ) (hjc : x.clockValue j u ≤ τ) (hu : u ∉ A.corrupted j)
    (hD : D ∈ (x.st j u).tree)
    (hsel : (x.st j u).finalized.compatible D = true) (hkT : x.lbl kT = Event.tick w (τ + Δ S)) (hsi : kT ≤ i)
    (hwA : ∀ l : ℕ, (tGAT : ℝ) ≤ x.time l → l ≤ kT → w ∈ A.active l)
    (hta : x.time i < aR M S r) (hw : w ∉ A.corrupted i) :
    (D ∈ (x.st i w).tree ∧ (x.st i w).finalized.AncestorEq D) ∨
      (M.chainStateOf S.C D).h ≤ (x.st i w).justifiedHeight := by
  by_cases hlt : (x.st i w).justifiedHeight < (M.chainStateOf S.C D).h
  swap
  · exact Or.inr (Nat.le_of_not_lt hlt)
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hAE : (aR M S r : ℝ) ≤ tAwakeEnd := by exact_mod_cast C.hEnd
  have hjR : x.time j ≤ aR M S r :=
    le_trans hj (C.tau_le_aR M F R hkT hsi hta)
  have hFD := (F_ancestorEq_of_high_st M F Fx) S A x R C.E C.hRoots tAwakeEnd i j w u D C.hThird
    (le_trans hta.le hAE) (le_trans hjR hAE) hw hu hD hlt (max_le hta.le hjR)
  refine Or.inl ⟨?_, hFD⟩
  by_cases hg : D = Block.genesis
  · subst hg
    exact (genesis_mem_T_of_exec M F) S A x R C.E i w
  have hwkT : w ∉ A.corrupted kT := fun h => hw (C.E.corrupted_mono kT i hsi h)
  have hkTi : x.time kT ≤ x.time i := htime hsi
  have hkTt : x.time kT ≤ tAwakeEnd := le_trans hkTi (le_trans hta.le hAE)
  have hT₁τ : T₁ ≤ τ := by
    have : (T₁ : ℝ) < τ := lt_of_lt_of_le hT hj
    exact_mod_cast this.le
  -- the receiver's tick to `τ`, one delay before its tick to `τ + Δ S` (`hTick`)
  obtain ⟨k₂, hk₂⟩ := C.hTick τ w kT hT₁τ hkT hkTt hwkT
  -- the relay's deadline is before `aR M S r`: the receiver ticks to `τ + Δ S` at a real time at least
  -- `τ + Δ S − ΔClockAhead`, before the real time of `i`, and `ΔNet + ΔClockAhead ≤ Δ S` (`hNet`)
  have hτN : τ + ΔNet ≤ aR M S r := by
    have h1 := (C.E.tick_active kT w (τ + Δ S) hkT).2.1
    have hB0 := C.E.behind_nonneg
    have hN := C.hNet
    push_cast at h1
    have : ((τ + ΔNet : ℕ) : ℝ) < aR M S r := by push_cast; linarith
    exact_mod_cast this.le
  -- the block's slot starts at the latest at `u`'s clock value at `j`, at most `τ`
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hHs := (slot_le_clockValue_of_mem_tree M F) R C.E hu hD
  rw [← hsl] at hHs
  have hDc₂ : M.slotStart S.C D.slot ≤ τ :=
    le_trans (((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S D.slot
      (x.clockValue j u)).2 hHs) hjc
  -- the holder is honest and awake from `T₁ − Δs` to `T₁`, before `j`
  have hT1 := C.hT₁
  have hGa := C.hGST
  have haR : ((T₁ - Δs : ℕ) : ℝ) + Δs = T₁ := by
    have : T₁ - Δs + Δs = T₁ := Nat.sub_add_cancel (by omega)
    exact_mod_cast this
  have hu₀ : u ∈ A.activeThroughout x ((T₁ - Δs : ℕ) : ℝ) (((T₁ - Δs : ℕ) : ℝ) + Δs) := by
    refine Activity.mem_activeThroughout.2 (fun l h1 h2 => ?_)
    have hul : u ∉ A.corrupted l :=
      (not_mem_corrupted_of_time_lt M F) R C.E hu (by rw [haR] at h1; linarith)
    have hgl : ((tGAT : ℕ) : ℝ) ≤ ((T₁ - Δs : ℕ) : ℝ) := by exact_mod_cast (show tGAT ≤ T₁ - Δs by omega)
    have hlt' : x.time l ≤ tAwakeEnd := by rw [haR] at h1; linarith
    exact Activity.mem_active.2 ⟨C.hAwake l u hlt' (le_trans hgl h2) hul, hul⟩
  have hsb : x.stepBefore (T₁ - Δs) ≤ j := (stepBefore_le_of_le_time_st M F) R C.E
    (by have : ((T₁ - Δs : ℕ) : ℝ) ≤ T₁ := by exact_mod_cast Nat.sub_le T₁ Δs
        linarith)
  have hFa := GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible ((F_ancestorEq_of_le M F) x R C.E u hsb) hsel
  have hFw : (x.st kT w).finalized.compatible D = true :=
    (compatible_iff _ _).2 (Or.inl (ancestorEq_trans ((F_ancestorEq_of_le M F) x R C.E w hsi) hFD))
  have hmx := le_max_left (Δ S) Δs
  have hmx' := le_max_right (Δ S) Δs
  have hmx'' : max (Δ S) Δs ≤ Δ S + Δs := max_le (by omega) (by omega)
  -- the two bounds on the clock value `τ + Δ S` (T-C-82-3) from `C.hNet`, `C.hSkew` and `0 ≤ ΔClockBehind`
  have hB0 := C.E.behind_nonneg
  have hNτ := C.hNet
  have hSτ := C.hSkew
  refine (mem_T_mono M F) x R C.E w hsi ?_
  exact block_at_tick_of_held_step_deadline M F U S A x R GST (aR M S r) (τ : ℝ) j (T₁ - Δs) (τ + Δ S) τ kT k₂ u w D
    C.E C.hRedeliver C.Sy
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M (le_trans hkTi hta.le) C.hRoots) C.hParent (by omega) (by omega)
    (by push_cast; linarith) (by push_cast; linarith) (by exact_mod_cast hτN) (by omega) hu₀ hj hu hD hFa hg hkT
    (fun l hl hlk => hwA l (le_trans (by exact_mod_cast (show tGAT ≤ T₁ - Δs by omega)) hl) hlk)
    hk₂ le_rfl hDc₂ hFw

/-- `held_spread_h_j` in the context.

Restated with the delivery premises up to `aR M S r`: the bound of the bundle `ClimbCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: a held block's justification height is at most `w`'s justification height before
`τ + 1 + Δ`. -/
theorem spread_h_j (U : UniformSchedule M.toSlotLayout) (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {τ j i kT : ℕ} {u w : V}
    {D : Block V} (hT : (T₁ : ℝ) < x.time j) (hj : x.time j ≤ τ) (hjc : x.clockValue j u ≤ τ) (hu : u ∉ A.corrupted j)
    (hD : D ∈ (x.st j u).tree)
    (hsel : (x.st j u).finalized.compatible D = true) (hkT : x.lbl kT = Event.tick w (τ + Δ S)) (hsi : kT ≤ i)
    (hwA : ∀ l : ℕ, (tGAT : ℝ) ≤ x.time l → l ≤ kT → w ∈ A.active l)
    (hta : x.time i < aR M S r) (hw : w ∉ A.corrupted i) :
    (M.chainStateOf S.C D).h_j ≤ (x.st i w).justifiedHeight := by
  rcases (C.spread M F U R E Fx) hT hj hjc hu hD hsel hkT hsi hwA hta hw with ⟨hDw, hFD⟩ | hle
  · exact (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E i w D hDw hFD
  · have h47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1.2.1
    unfold Height at *
    omega

/-- `held_spread_h_max` in the context.

Restated with the delivery premises up to `aR M S r`: the bound of the bundle `ClimbCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: a held block's chain-state height is at most `w`'s greatest chain-state height before
`τ + 1 + Δ`. -/
theorem spread_h_max (U : UniformSchedule M.toSlotLayout) (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {τ j i kT : ℕ} {u w : V}
    {D : Block V} (hT : (T₁ : ℝ) < x.time j) (hj : x.time j ≤ τ) (hjc : x.clockValue j u ≤ τ) (hu : u ∉ A.corrupted j)
    (hD : D ∈ (x.st j u).tree)
    (hsel : (x.st j u).finalized.compatible D = true) (hkT : x.lbl kT = Event.tick w (τ + Δ S)) (hsi : kT ≤ i)
    (hwA : ∀ l : ℕ, (tGAT : ℝ) ≤ x.time l → l ≤ kT → w ∈ A.active l)
    (hta : x.time i < aR M S r) (hw : w ∉ A.corrupted i) :
    (M.chainStateOf S.C D).h ≤ hMax M S.C (x.st i w) := by
  rcases (C.spread M F U R E Fx) hT hj hjc hu hD hsel hkT hsi hwA hta hw with ⟨hDw, -⟩ | hle
  · exact le_hMax M hDw
  · have h := (h_j_lt_h_max_st M F) S A x R E i w
    unfold Height at *
    omega

/-- The level `j ≤ h_j` spreads: when `u`, honest at `τ ≥ T₁`, has `h_j ≥ j` before `τ + 1`, every
`w` honest at `t ≥ τ + 1 + Δ` before `aR M S r` has `h_j ≥ j` before `τ + 1 + Δ` (the block
witnessing `u`'s cache, `held_spread_h_j`).

Restated with the delivery premises up to `aR M S r`: the bound of the bundle `ClimbCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: a justification height of at least `j` at `u` before `τ + 1` reaches every honest `w`
before `τ + 1 + Δ`. -/
theorem spread_level_h_j (U : UniformSchedule M.toSlotLayout) (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (h : ℕ) {τ j i kT : ℕ}
    {u w : V} (hT : (T₁ : ℝ) < x.time j) (hj : x.time j ≤ τ) (hjc : x.clockValue j u ≤ τ) (hu : u ∉ A.corrupted j)
    (hL : h ≤ (x.st j u).justifiedHeight) (hkT : x.lbl kT = Event.tick w (τ + Δ S)) (hsi : kT ≤ i)
    (hwA : ∀ l : ℕ, (tGAT : ℝ) ≤ x.time l → l ≤ kT → w ∈ A.active l)
    (hta : x.time i < aR M S r) (hw : w ∉ A.corrupted i) :
    h ≤ (x.st i w).justifiedHeight := by
  obtain ⟨⟨D, hD, hJD, hjD⟩, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j u
  have hsp := (C.spread_h_j M F U R E Fx) hT hj hjc hu hD (by
      have hFJ := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_exec M F) S A x R E j u
      rw [hJD] at hFJ
      exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFJ ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).1))) hkT hsi hwA hta hw
  rw [hjD] at hL
  exact le_trans hL hsp

/-- The level `H₂ ≤ head_height_floor` spreads: when `u`, honest at `τ ≥ T₁`, has
`head_height_floor ≥ H₂` before `τ + 1`, so does every `w` honest at `t ≥ τ + 1 + Δ` before
`aR M S r`, before `τ + 1 + Δ`.

Why: either `u`'s greatest chain-state height is at least `H₂ + 1`, and its witness raises `w`'s; or
`u` is contested at greatest chain-state height `H₂`, `h_j = H₂ − 1`, and its contesting block and
its justified block's witness reach `w`, whose state is then contested at `H₂` too, or has greatest
chain-state height `H₂ + 1`.

Restated with the delivery premises up to `aR M S r`: the bound of the bundle `ClimbCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: `head_height_floor` at least `H₂` at `u` before `τ + 1` reaches every honest `w` before
`τ + 1 + Δ`. -/
theorem spread_level_floor (U : UniformSchedule M.toSlotLayout) (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {τ j i kT : ℕ}
    {u w : V} (hT : (T₁ : ℝ) < x.time j) (hj : x.time j ≤ τ) (hjc : x.clockValue j u ≤ τ) (hu : u ∉ A.corrupted j)
    (hL : H₂ ≤ M.head_height_floor (x.st j u)) (hkT : x.lbl kT = Event.tick w (τ + Δ S)) (hsi : kT ≤ i)
    (hwA : ∀ l : ℕ, (tGAT : ℝ) ≤ x.time l → l ≤ kT → w ∈ A.active l)
    (hta : x.time i < aR M S r) (hik : i ≤ k₀) (hw : w ∉ A.corrupted i)
    (hT₁a : T₁ + Δ S ≤ aR M S r) {kL : ℕ} (hkL : x.lbl kL = Event.tick w (T₁ + Δ S)) (hkLi : kL ≤ i) :
    H₂ ≤ M.head_height_floor (x.st i w) := by
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hAE : (aR M S r : ℝ) ≤ tAwakeEnd := by exact_mod_cast C.hEnd
  have hjR : x.time j ≤ aR M S r :=
    le_trans hj (C.tau_le_aR M F R hkT hsi hta)
  have hT₁τ : T₁ ≤ τ := by exact_mod_cast (le_trans hT.le hj)
  have hInvU := (lem11_node_invariant M F S A x R E j u hu).1
  have hInvW := (lem11_node_invariant M F S A x R E i w hw).1
  have hfw := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_sub_one_le_floor M F) S.C S.P S.X (x.st i w) hInvW
  by_cases hX : H₂ + 1 ≤ hMax M S.C (x.st j u)
  · obtain ⟨-, ⟨X, hX', hXh⟩, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j u
    have h := (C.spread_h_max M F U R E Fx) hT hj hjc hu hX'
      ((compatible_iff _ _).2 (Or.inl ((hMax_witness_compatible_finalized M F Fx) x R E C.hRoots j u X
        (C.hThird.mono (le_trans hjR hAE)) hu hX'
        (fun B hB => by rw [hXh]; exact le_hMax M hB) hjR)))
      hkT hsi hwA hta hw
    unfold Height at *
    omega
  rcases Nat.eq_zero_or_pos H₂ with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.st j u) hInvU with ⟨hc, hm, hfl⟩ | ⟨-, hfl⟩
  swap
  · exfalso
    rw [hfl] at hL
    unfold Height at *
    omega
  obtain ⟨-, Ab, hA, hFA', hAh, hJA⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_spec M F) S.C S.P S.X _ hInvU hc
  obtain ⟨⟨D, hD, hJD, hjD⟩, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j u
  have hjw := (C.spread_h_j M F U R E Fx) hT hj hjc hu hD (by
      have hFJ := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_exec M F) S A x R E j u
      rw [hJD] at hFJ
      exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFJ ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).1))) hkT hsi hwA hta hw
  rw [← hjD] at hjw
  by_cases hY : H₂ + 1 ≤ hMax M S.C (x.st i w)
  · unfold Height at *
    omega
  have hb := C.bounds_st M F U R E Fx (j := i) (w := w) le_rfl hkL hkLi hw hik hta.le hT₁a
  have hjl := (h_j_lt_h_max_st M F) S A x R E i w
  rw [hfl] at hL
  have hmu : hMax M S.C (x.st j u) = H₂ := by
    unfold Height at *
    omega
  have hjeq : (x.st i w).justifiedHeight = (x.st j u).justifiedHeight := by
    unfold Height at *
    omega
  have hmw : hMax M S.C (x.st i w) = (x.st i w).justifiedHeight + 1 := by
    unfold Height at *
    omega
  rcases (C.spread M F U R E Fx) hT hj hjc hu hA ((compatible_iff _ _).2 (Or.inl hFA')) hkT hsi hwA hta hw with ⟨hAw, hFA⟩ | hlo
  swap
  · exfalso
    unfold Height at *
    omega
  have hJ := (J_eq_of_h_j_eq_st M F Fx) S A x R E C.hRoots tAwakeEnd i j w u C.hThird
    (le_trans hta.le hAE) (le_trans hjR hAE) hw hu hjeq (max_le hta.le hjR)
  have hcw : M.fg_contest (x.st i w) = true := by
    refine (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_true_of M F) S.C S.P S.X _ hInvW Ab hmw hAw hFA ?_ ?_
    · rw [hAh]
      unfold Height at *
      omega
    · rw [hJ]
      exact hJA
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.st i w) hInvW with ⟨-, -, hflw⟩ | ⟨hcf, -⟩
  · rw [hflw]
    unfold Height at *
    omega
  · rw [hcw] at hcf
    cases hcf

/-- The level `H₂ + 1 ≤ head_height_floor` spreads: when `u`, honest at `τ ≥ T₁`, has
`head_height_floor ≥ H₂ + 1` before `τ + 1`, so does every `w` honest at `t ≥ τ + 1 + Δ` before
`aR M S r`, before `τ + 1 + Δ`.

Why: `u` is then contested at greatest chain-state height `H₂ + 1`, `h_j = H₂` (A2 bounds the
greatest chain-state height); its contesting block and its justified block's witness reach `w`,
whose state is then contested at `H₂ + 1`.

Restated with the delivery premises up to `aR M S r`: the bound of the bundle `ClimbCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: `head_height_floor` at least `H₂ + 1` at `u` before `τ + 1` reaches every honest `w`
before `τ + 1 + Δ`. -/
theorem spread_level_floor_succ (U : UniformSchedule M.toSlotLayout) (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {τ j i kT : ℕ}
    {u w : V} (hT : (T₁ : ℝ) < x.time j) (hj : x.time j ≤ τ) (hjc : x.clockValue j u ≤ τ) (hu : u ∉ A.corrupted j)
    (hL : H₂ + 1 ≤ M.head_height_floor (x.st j u)) (hkT : x.lbl kT = Event.tick w (τ + Δ S)) (hsi : kT ≤ i)
    (hwA : ∀ l : ℕ, (tGAT : ℝ) ≤ x.time l → l ≤ kT → w ∈ A.active l)
    (hta : x.time i < aR M S r) (hik : i ≤ k₀) (hw : w ∉ A.corrupted i) :
    H₂ + 1 ≤ M.head_height_floor (x.st i w) := by
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hAE : (aR M S r : ℝ) ≤ tAwakeEnd := by exact_mod_cast C.hEnd
  have hjR : x.time j ≤ aR M S r :=
    le_trans hj (C.tau_le_aR M F R hkT hsi hta)
  have hT₁τ : T₁ ≤ τ := by exact_mod_cast (le_trans hT.le hj)
  have hInvU := (lem11_node_invariant M F S A x R E j u hu).1
  have hInvW := (lem11_node_invariant M F S A x R E i w hw).1
  -- `j` comes before `w`'s tick to `τ + Δ`: that tick is at a real time at least `τ + Δ − ΔClockAhead`, later
  -- than `τ` (`hSkew`), and the time of `j` is at most `τ`
  have hjsb : j ≤ kT := by
    by_contra hlt
    have hm := (time_mono M) x R (Nat.le_of_lt (Nat.lt_of_not_le hlt))
    have hkt := (C.E.tick_active _ _ _ hkT).2.1
    have hsk := C.hSkew
    have hB0 := C.E.behind_nonneg
    push_cast at hkt
    linarith
  have hmu := C.hmax_le_st M F R E Fx u (j := j) (le_trans hjsb (le_trans hsi hik))
  have hflu := (GoldilocksCorrectness.Record.Proofs.Routines.floor_le_h_max M F) S.C S.P S.X (x.st j u) hInvU
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.st j u) hInvU with ⟨hc, hm, hfl⟩ | ⟨-, hfl⟩
  swap
  · exfalso
    rw [hfl] at hL
    unfold Height at *
    omega
  obtain ⟨-, Ab, hA, hFA', hAh, hJA⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_spec M F) S.C S.P S.X _ hInvU hc
  obtain ⟨⟨D, hD, hJD, hjD⟩, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j u
  have hjw := (C.spread_h_j M F U R E Fx) hT hj hjc hu hD (by
      have hFJ := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_exec M F) S A x R E j u
      rw [hJD] at hFJ
      exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFJ ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).1))) hkT hsi hwA hta hw
  rw [← hjD] at hjw
  have hmw := C.hmax_le_st M F R E Fx w (j := i) hik
  have hjl := (h_j_lt_h_max_st M F) S A x R E i w
  rw [hfl] at hL
  have hjeq : (x.st i w).justifiedHeight = (x.st j u).justifiedHeight := by
    unfold Height at *
    omega
  have hmw' : hMax M S.C (x.st i w) = (x.st i w).justifiedHeight + 1 := by
    unfold Height at *
    omega
  rcases (C.spread M F U R E Fx) hT hj hjc hu hA ((compatible_iff _ _).2 (Or.inl hFA')) hkT hsi hwA hta hw with ⟨hAw, hFA⟩ | hlo
  swap
  · exfalso
    unfold Height at *
    omega
  have hJ := (J_eq_of_h_j_eq_st M F Fx) S A x R E C.hRoots tAwakeEnd i j w u C.hThird
    (le_trans hta.le hAE) (le_trans hjR hAE) hw hu hjeq (max_le hta.le hjR)
  have hcw : M.fg_contest (x.st i w) = true := by
    refine (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_true_of M F) S.C S.P S.X _ hInvW Ab hmw' hAw hFA ?_ ?_
    · rw [hAh]
      unfold Height at *
      omega
    · rw [hJ]
      exact hJA
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.st i w) hInvW with ⟨-, -, hflw⟩ | ⟨hcf, -⟩
  · rw [hflw]
    unfold Height at *
    omega
  · rw [hcw] at hcf
    cases hcf

/-- The level `H₂ ≤ head_height_floor` persists: reached before `t₂`, it holds before
every `t ≥ t₂` before `aR M S r` at which `w` is honest (`contest_persists` when the greatest
chain-state height stays `H₂`).

Restated with the delivery premises up to `aR M S r`: the bound of the bundle `ClimbCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: `head_height_floor` at least `H₂` at `w`, reached before `t₂`, holds before every later
`t` before `aR M S r` at which `w` is honest. -/
theorem mono_level_floor (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {w : V} {t₂ t : ℕ}
    (h2t : t₂ ≤ t) (hta : t < aR M S r) (hw : w ∉ A.corruptedAtTime x t)
    (hL : H₂ ≤ M.head_height_floor (x.stateBefore t₂ w)) :
    H₂ ≤ M.head_height_floor (x.stateBefore t w) := by
  have hft := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_sub_one_le_floor M F) S.C S.P S.X (x.stateBefore t w) ((nodeInv_stateBefore_of_not_mem_corruptedAtTime M F) S A x R E le_rfl hw)
  by_cases hX : H₂ + 1 ≤ hMax M S.C (x.stateBefore t w)
  · unfold Height at *
    omega
  rcases Nat.eq_zero_or_pos H₂ with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  have hmm := (GoldilocksCorrectness.Record.Proofs.Executions.h_max_mono M F) S A x R E w h2t
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.stateBefore t₂ w) ((nodeInv_stateBefore_of_not_mem_corruptedAtTime M F) S A x R E h2t hw) with ⟨hc, -, hfl⟩ | ⟨-, hfl⟩
  swap
  · exfalso
    rw [hfl] at hL
    unfold Height at *
    omega
  have hmeq : hMax M S.C (x.stateBefore t w) = hMax M S.C (x.stateBefore t₂ w) := by
    unfold Height at *
    omega
  have hct := (GoldilocksCorrectness.Record.Proofs.Executions.contest_persists M F Fx) S A x R E C.hRoots tAwakeEnd t₂ t w C.hThird
    h2t (by have := C.hEnd; omega) hw hc hmeq (by omega)
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.stateBefore t w) ((nodeInv_stateBefore_of_not_mem_corruptedAtTime M F) S A x R E le_rfl hw) with ⟨-, -, hflt⟩ | ⟨hcf, -⟩
  · rw [hflt, hmeq, ← hfl]
    exact hL
  · rw [hct] at hcf
    cases hcf

/-- The level `H₂ + 1 ≤ head_height_floor` persists: reached before `t₂`, it holds before every
`t ≥ t₂` before `aR M S r` at which `w` is honest (`contest_persists`, the greatest chain-state
height staying `H₂ + 1`).

Restated with the delivery premises up to `aR M S r`: the bound of the bundle `ClimbCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: `head_height_floor` at least `H₂ + 1` at `w`, reached before `t₂`, holds before every
later `t` before `aR M S r` at which `w` is honest. -/
theorem mono_level_floor_succ (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {w : V}
    {t₂ t : ℕ} (h2t : t₂ ≤ t) (hta : t < aR M S r) (hkt : x.stepBefore t ≤ k₀) (hw : w ∉ A.corruptedAtTime x t)
    (hL : H₂ + 1 ≤ M.head_height_floor (x.stateBefore t₂ w)) :
    H₂ + 1 ≤ M.head_height_floor (x.stateBefore t w) := by
  have hmm := (GoldilocksCorrectness.Record.Proofs.Executions.h_max_mono M F) S A x R E w h2t
  have hm2 := C.hmax_le M F R E Fx w (t := t₂) (le_trans ((stepBefore_mono M) x R E h2t) hkt)
  have hmt := C.hmax_le M F R E Fx w (t := t) hkt
  have hfl2 := (GoldilocksCorrectness.Record.Proofs.Routines.floor_le_h_max_of_core M F) S.C S.P S.X (x.stateBefore t₂ w) ((nodeInvCore_of_stateBefore M F) S A x R E t₂ w)
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases_of_core M F) S.C S.P S.X (x.stateBefore t₂ w) ((nodeInvCore_of_stateBefore M F) S A x R E t₂ w) with ⟨hc, -, hfl⟩ | ⟨-, hfl⟩
  swap
  · exfalso
    rw [hfl] at hL
    unfold Height at *
    omega
  have hmeq : hMax M S.C (x.stateBefore t w) = hMax M S.C (x.stateBefore t₂ w) := by
    unfold Height at *
    omega
  have hct := (GoldilocksCorrectness.Record.Proofs.Executions.contest_persists M F Fx) S A x R E C.hRoots tAwakeEnd t₂ t w C.hThird
    h2t (by have := C.hEnd; omega) hw hc hmeq (by omega)
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases_of_core M F) S.C S.P S.X (x.stateBefore t w) ((nodeInvCore_of_stateBefore M F) S A x R E t w) with ⟨-, -, hflt⟩ | ⟨hcf, -⟩
  · rw [hflt, hmeq, ← hfl]
    exact hL
  · rw [hct] at hcf
    cases hcf

/-- **A fork-choice change of the climb crosses one of four levels.** At a step `j` whose real time
is after `T₁ + Δ` and before `aR M S r`, a `ForkChoiceChangeStep` at a validator honest at `j`
crosses one of the levels `H₂ − 1 ≤ h_j`, `H₂ ≤ head_height_floor`, `H₂ ≤ h_j`, `H₂ + 1 ≤ head_height_floor`: the
level fails at `x.st j w` and holds at `x.st (j + 1) w`.

Why: with the greatest chain-state height at `H₂` or `H₂ + 1` (B2, A2), a rise of
`head_height_floor` (which is the greatest chain-state height or the greatest chain-state height
minus one) is to `H₂` from `H₂ − 1`, or to `H₂ + 1`. A root that becomes the justified block `J`
with greatest chain-state height `h_j + 1` and is no ancestor of the old root comes with a rise of
`h_j` to `H₂ − 1` or `H₂`: were `h_j` unchanged, `J` would be too (Lemma 76) and the greatest
chain-state height as well, and the old root, the finalized block of a contested state (the old `J`
itself otherwise), would leave the new state contested by the same block (Lemma 89a), against its
root being `J`.

Restated with the delivery premises up to `aR M S r`: the bound of the bundle `ClimbCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: a fork-choice change of an honest validator during the climb crosses one of four levels.
-/
theorem classify (U : UniformSchedule M.toSlotLayout) (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {w : V} {j : ℕ}
    (hn2 : T₁ + Δ S ≤ aR M S r) {kT : ℕ} (hkT : x.lbl kT = Event.tick w (T₁ + Δ S)) (h1T : kT < j) (hta : x.time j < aR M S r)
    (hjk : j + 1 ≤ k₀) (hw : w ∉ A.corrupted j)
    (hch : ForkChoiceChangeStep M S A x w j) :
    (¬ H₂ - 1 ≤ (x.st j w).justifiedHeight ∧ H₂ - 1 ≤ (x.st (j + 1) w).justifiedHeight) ∨
    (¬ H₂ ≤ M.head_height_floor (x.st j w) ∧ H₂ ≤ M.head_height_floor (x.st (j + 1) w)) ∨
    (¬ H₂ ≤ (x.st j w).justifiedHeight ∧ H₂ ≤ (x.st (j + 1) w).justifiedHeight) ∨
    (¬ H₂ + 1 ≤ M.head_height_floor (x.st j w) ∧ H₂ + 1 ≤ M.head_height_floor (x.st (j + 1) w)) := by
  -- `w`'s honesty after the step: the change is `w`'s own tick, restart or delivery, which keeps the
  -- adversary set (`honest_succ_of_state_ne`)
  have hv_B3S1_w : w ∉ A.corrupted (j + 1) :=
    ((honest_succ_of_state_ne M F) x R E hw (state_ne_of_change_step M F hch)).1
  -- the change is `w`'s own step: it keeps `w`'s honesty and the time
  obtain ⟨hw1, htj⟩ := (honest_succ_of_state_ne M F) x R E hw (state_ne_of_change_step M F hch)
  have hAE : (aR M S r : ℝ) ≤ tAwakeEnd := by exact_mod_cast C.hEnd
  have hta1 : x.time (j + 1) < aR M S r := by rw [htj]; exact hta
  have hsj : kT ≤ j := h1T.le
  have hb0 := C.bounds_st M F U R E Fx (j := j) (w := w) le_rfl hkT hsj hw (by omega) hta.le hn2
  have hmm := (h_max_mono_st M F) S A x R E w (show j ≤ j + 1 by omega)
  have hb1 := C.hmax_le_st M F R E Fx w (j := j + 1) hjk
  have hInv0 := (lem11_node_invariant M F S A x R E j w hw).1
  have hInv1 := (lem11_node_invariant M F S A x R E (j + 1) w hv_B3S1_w).1
  rcases hch with ⟨hr1, hm1, hnot⟩ | hfl
  · have hlt : (x.st j w).justifiedHeight < (x.st (j + 1) w).justifiedHeight := by
      by_contra hge
      push Not at hge
      have hj0 := (h_j_lt_h_max_st M F) S A x R E j w
      have heq : (x.st j w).justifiedHeight = (x.st (j + 1) w).justifiedHeight := by
        unfold Height at *
        omega
      have hmeq : hMax M S.C (x.st j w) = hMax M S.C (x.st (j + 1) w) := by
        unfold Height at *
        omega
      have hJ := (J_eq_of_h_j_eq_st M F Fx) S A x R E C.hRoots tAwakeEnd j (j + 1) w w C.hThird
        (le_trans hta.le hAE) (le_trans hta1.le hAE) hw hw1 heq (max_le hta.le hta1.le)
      have hc1 : M.fg_contest (x.st (j + 1) w) = false := by
        rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.st (j + 1) w) hInv1 with ⟨-, -, h⟩ | ⟨hF, hor⟩
        · exact h
        · exfalso
          rcases hor with hc | hne
          · obtain ⟨-, B, -, hFB, -, hJB⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_spec M F) S.C S.P S.X _ hInv1 hc
            exact hJB (by rw [← hr1, hF]; exact hFB)
          · exact hne hm1
      rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.st j w) hInv0 with ⟨hr0, -, -⟩ | ⟨-, hor0⟩
      · apply hnot
        rw [hr1, hr0, ← hJ]
        exact ancestorEq_refl _
      · rcases hor0 with hc0 | hne0
        · obtain ⟨-, Ab, hA, -, hAh, hJA⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_spec M F) S.C S.P S.X _ hInv0 hc0
          have hAt := (mem_T_mono M F) x R E w (show j ≤ j + 1 by omega) hA
          have hFA := (F_ancestorEq_of_high_st M F Fx) S A x R E C.hRoots tAwakeEnd (j + 1) j w w Ab
            C.hThird (le_trans hta1.le hAE) (le_trans hta.le hAE) hw1 hw hA
            (by rw [hAh, hmeq, hm1]; exact Nat.lt_succ_self _) (max_le hta1.le hta.le)
          have hct := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_true_of M F) S.C S.P S.X _ hInv1 Ab hm1 hAt hFA
            (by rw [hAh, hmeq])
            (by rw [← hJ]; exact hJA)
          rw [hc1] at hct
          cases hct
        · apply hne0
          unfold Height at *
          omega
    by_cases hjv : (x.st (j + 1) w).justifiedHeight + 1 = H₂
    · left
      unfold Height at *
      exact ⟨by omega, by omega⟩
    · right; right; left
      unfold Height at *
      exact ⟨by omega, by omega⟩
  · have hf0 := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_sub_one_le_floor M F) S.C S.P S.X (x.st j w) hInv0
    have hf1 := (GoldilocksCorrectness.Record.Proofs.Routines.floor_le_h_max M F) S.C S.P S.X (x.st (j + 1) w) hInv1
    by_cases hf : M.head_height_floor (x.st (j + 1) w) = H₂ + 1
    · right; right; right
      unfold Height at *
      exact ⟨by omega, by omega⟩
    · right; left
      unfold Height at *
      exact ⟨by omega, by omega⟩

end ClimbCtxUpTo

/-- **The four kinds of fork-choice change.** The
proof; the audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: every fork-choice change crosses one of four levels
(`ClimbCtx.classify`); each level reached by
an honest validator reaches every honest validator within one delay (`spread_level_…`) and stays
reached (`mono_level_…`, `h_j_mono`), so its crossings lie within one delay after the first time
from `T₁` some honest validator has it (`kind_time`).

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round; `H₂`: the threshold.

Roots name blocks until `aR M S r`: every change the conclusion classifies is at a time before
`aR M S r`, and the levels are read before times at most `aR M S r` (the bundle `ClimbCtx`).

Restated with the delivery premises up to `aR M S r`: the bound of its roots `hRoots`; every
delivery its proof reads is due by then.

The readers read `w`'s greatest chain-state height at its tick to `T₁ + Δ`, so the statement takes
`T₁ + Δ ≤ aR M S r` (`hT₁a`; the threshold's time one delay before the action time of round `r`), which
its caller has from `hT₁0` when some honest round opening slot precedes `r * R` (F-P1-17).

Read aloud: before the fast block's round, the members' roots and `head_height_floor`s change in at
most four bursts, each within one delay. -/
theorem fork_choice_change_kinds_upTo (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ : ℕ)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (aR M S r)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (aR M S r))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (aR M S r))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT) (hT₁s : tGAT + Δs ≤ T₁)
    (hTick : ∀ (c : ℕ) (w : V) (k : ℕ), T₁ ≤ c → x.lbl k = Event.tick w (c + Δ S) → x.time k ≤ tAwakeEnd → w ∉ A.corrupted k → ∃ k' : ℕ, x.lbl k' = Event.tick w c)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hH₂ : OldHeightAttained M S A x T₁ H₂)
    (k₀ : ℕ)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    -- every attestation put on the wire by a tick at a step before `k₀`, by a validator outside the adversary set at
    -- `tAwakeEnd`, has height at most `H₂`
    (hOldStep : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < k₀ → x.lbl k = Event.tick u t →
      u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂)
    (hEnd : aR M S r ≤ tAwakeEnd)
    -- one delay after the threshold's time is at most the action time of round `r`
    (hT₁a : T₁ + Δ S ≤ aR M S r) :
    ∃ τ : Fin 4 → ℝ, ∀ (w : V) (j : ℕ), x.lbl (x.tickStep w (T₁ + Δ S)) = Event.tick w (T₁ + Δ S) →
      x.tickStep w (T₁ + Δ S) < j → x.time j < aR M S r →
      j + 1 ≤ k₀ → w ∉ A.corrupted j → ForkChoiceChangeStep M S A x w j →
      ∃ c : Fin 4, τ c ≤ x.time j ∧
        (∀ (k' c' : ℕ), x.lbl k' = Event.tick w c' → τ c + ΔClockAhead + Δ S ≤ c' → j < k') ∧ (T₁ : ℝ) < τ c := by
  classical
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hAE : (aR M S r : ℝ) ≤ tAwakeEnd := by exact_mod_cast hEnd
  -- the bundle's end step: the earlier of `k₀` and the configuration in force at `aR M S r`
  have hk₁E : x.time (min k₀ (x.stepBefore (aR M S r))) ≤ tAwakeEnd :=
    le_trans (R.time_mono (min_le_right _ _)) (le_trans ((time_stepBefore_le M) x R E (aR M S r)) hAE)
  have C : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ (min k₀ (x.stepBefore (aR M S r))) Δs (releaseOf M S.C)
      ΔRedeliver ΔClockAhead ΔClockBehind ΔNet :=
    { E := E, hNet := hNet, hSkew := hSkew, hRedeliver := hRedeliver, Sy := Sy, hΔs := hΔs, hRoots := hRoots,
      hParent := hParent, hGST := hGST, hT₁ := hT₁s, hThird := hThird, hAwake := hAwake, hH₂ := hH₂, hOld := hOld,
      hEnd := hEnd, hOldStep := fun k t u a' hk => hOldStep k t u a' (lt_of_lt_of_le hk (min_le_left _ _)),
      hEndStep := hk₁E, hTick := hTick }
  -- a crossing step of a validator honest at it is its own step: it keeps its honesty and the time
  have hkeep : ∀ (P : M.N → Prop) (w : V) (j : ℕ),
      (w ∉ A.corrupted j ∧ j + 1 ≤ min k₀ (x.stepBefore (aR M S r)) ∧
        ∃ kT : ℕ, x.lbl kT = Event.tick w (T₁ + Δ S) ∧ kT < j) →
      ¬ P (x.st j w) → P (x.st (j + 1) w) → w ∉ A.corrupted (j + 1) ∧ x.time (j + 1) = x.time j := by
    intro P w j hw hn hy
    exact (honest_succ_of_state_ne M F) x R E hw.1 (fun h => hn (by rw [h] at hy; exact hy))
  -- the receiver of a spread is active from `tGAT` up to its tick
  have hwA : ∀ (w : V) (j kT : ℕ), kT ≤ j → x.time j < aR M S r → w ∉ A.corrupted j →
      ∀ l : ℕ, (tGAT : ℝ) ≤ x.time l → l ≤ kT → w ∈ A.active l := by
    intro w j kT hsi hta hw l h1 h2
    have hwl : w ∉ A.corrupted l := fun h => hw (E.corrupted_mono l j (le_trans h2 hsi) h)
    exact Activity.mem_active.2 ⟨hAwake l w (le_trans (R.time_mono (le_trans h2 hsi)) (le_trans hta.le hAE))
      (le_trans h1 (R.time_mono (Nat.le_succ l))) hwl, hwl⟩
  -- the four levels, each crossed only before the crossing validator's tick to its time plus one delay
  obtain ⟨τ0, h0⟩ := kind_time_step_real M F x.time (fun w j => x.clockValue j w) (fun w k c => x.lbl k = Event.tick w c)
    (fun u k => u ∉ A.corrupted k)
    (fun w j => w ∉ A.corrupted j ∧ j + 1 ≤ min k₀ (x.stepBefore (aR M S r)) ∧
      ∃ kT : ℕ, x.lbl kT = Event.tick w (T₁ + Δ S) ∧ kT < j)
    (fun w j => H₂ - 1 ≤ (x.st j w).justifiedHeight) T₁ (Δ S) (aR M S r) ΔClockAhead hA0 (fun _ _ h => R.time_mono h)
    (fun u k => (clockValue_le_time_add_ahead M F) x R E k u)
    (fun w j => hkeep (fun n => H₂ - 1 ≤ n.justifiedHeight) w j)
    (fun τ u k hT hj hjc hu hL w j kT hkT hsi hta hw =>
      (C.spread_level_h_j M F U R E Fx (H₂ - 1)) hT hj hjc hu hL hkT hsi
        (hwA w j kT hsi hta hw.1) hta hw.1)
  obtain ⟨τ1, h1⟩ := kind_time_step_real M F x.time (fun w j => x.clockValue j w) (fun w k c => x.lbl k = Event.tick w c)
    (fun u k => u ∉ A.corrupted k)
    (fun w j => w ∉ A.corrupted j ∧ j + 1 ≤ min k₀ (x.stepBefore (aR M S r)) ∧
      ∃ kT : ℕ, x.lbl kT = Event.tick w (T₁ + Δ S) ∧ kT < j)
    (fun w j => H₂ ≤ M.head_height_floor (x.st j w)) T₁ (Δ S) (aR M S r) ΔClockAhead hA0 (fun _ _ h => R.time_mono h)
    (fun u k => (clockValue_le_time_add_ahead M F) x R E k u)
    (fun w j => hkeep (fun n => H₂ ≤ M.head_height_floor n) w j)
    (fun τ u k hT hj hjc hu hL w j kT hkT hsi hta hw => by
      obtain ⟨kL, hkL, hkLj⟩ := hw.2.2
      exact (C.spread_level_floor M F U R E Fx) hT hj hjc hu hL hkT hsi
        (hwA w j kT hsi hta hw.1) hta (by have := hw.2.1; omega) hw.1 hT₁a hkL hkLj.le)
  obtain ⟨τ2, h2⟩ := kind_time_step_real M F x.time (fun w j => x.clockValue j w) (fun w k c => x.lbl k = Event.tick w c)
    (fun u k => u ∉ A.corrupted k)
    (fun w j => w ∉ A.corrupted j ∧ j + 1 ≤ min k₀ (x.stepBefore (aR M S r)) ∧
      ∃ kT : ℕ, x.lbl kT = Event.tick w (T₁ + Δ S) ∧ kT < j)
    (fun w j => H₂ ≤ (x.st j w).justifiedHeight) T₁ (Δ S) (aR M S r) ΔClockAhead hA0 (fun _ _ h => R.time_mono h)
    (fun u k => (clockValue_le_time_add_ahead M F) x R E k u)
    (fun w j => hkeep (fun n => H₂ ≤ n.justifiedHeight) w j)
    (fun τ u k hT hj hjc hu hL w j kT hkT hsi hta hw =>
      (C.spread_level_h_j M F U R E Fx H₂) hT hj hjc hu hL hkT hsi
        (hwA w j kT hsi hta hw.1) hta hw.1)
  obtain ⟨τ3, h3⟩ := kind_time_step_real M F x.time (fun w j => x.clockValue j w) (fun w k c => x.lbl k = Event.tick w c)
    (fun u k => u ∉ A.corrupted k)
    (fun w j => w ∉ A.corrupted j ∧ j + 1 ≤ min k₀ (x.stepBefore (aR M S r)) ∧
      ∃ kT : ℕ, x.lbl kT = Event.tick w (T₁ + Δ S) ∧ kT < j)
    (fun w j => H₂ + 1 ≤ M.head_height_floor (x.st j w)) T₁ (Δ S) (aR M S r) ΔClockAhead hA0 (fun _ _ h => R.time_mono h)
    (fun u k => (clockValue_le_time_add_ahead M F) x R E k u)
    (fun w j => hkeep (fun n => H₂ + 1 ≤ M.head_height_floor n) w j)
    (fun τ u k hT hj hjc hu hL w j kT hkT hsi hta hw =>
      (C.spread_level_floor_succ M F U R E Fx) hT hj hjc hu hL hkT hsi
        (hwA w j kT hsi hta hw.1) hta (by have := hw.2.1; omega) hw.1)
  refine ⟨fun c : Fin 4 => match c with | 0 => τ0 | 1 => τ1 | 2 => τ2 | 3 => τ3, ?_⟩
  intro w j hlbl hlt hta hjk hw hch
  obtain ⟨-, htj⟩ := (honest_succ_of_state_ne M F) x R E hw (state_ne_of_change_step M F hch)
  -- the change step is before the configuration in force at `aR M S r`
  have hjk₁ : j + 1 ≤ min k₀ (x.stepBefore (aR M S r)) := by
    refine le_min hjk ?_
    have : j < x.stepBefore (aR M S r) := ((lt_stepBefore_iff M) x R E).2 (by rw [htj]; exact hta)
    omega
  -- the change step is after `T₁`: it comes after `w`'s tick to `T₁ + Δ`, whose real time is less than
  -- `ΔClockAhead < Δ` before that clock value
  have hT₁j : (T₁ : ℝ) < x.time j := by
    have h1 := (E.tick_active _ w (T₁ + Δ S) hlbl).2.1
    have h2 := R.time_mono hlt.le
    push_cast at h1
    have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
    linarith
  have hR : w ∉ A.corrupted j ∧ j + 1 ≤ min k₀ (x.stepBefore (aR M S r)) ∧
      ∃ kT : ℕ, x.lbl kT = Event.tick w (T₁ + Δ S) ∧ kT < j := ⟨hw, hjk₁, _, hlbl, hlt⟩
  rcases (C.classify M F U R E Fx) hT₁a hlbl hlt hta hjk₁ hw hch with h | h | h | h
  · exact ⟨0, h0 w j hT₁j hta hR h.1 h.2⟩
  · exact ⟨1, h1 w j hT₁j hta hR h.1 h.2⟩
  · exact ⟨2, h2 w j hT₁j hta hR h.1 h.2⟩
  · exact ⟨3, h3 w j hT₁j hta hR h.1 h.2⟩

end GoldilocksCorrectness.Record.Proofs.Executions

