module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89Climb
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Climb
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89ClimbUpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89ClimbUpTo.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: step B2 of part B of Lemma 89, the
honest greatest chain-state heights between the threshold and the action time, with the delivery
premises up to a bound. The page's routine-level theorems are the facts' fields or have their twins
in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated hMax)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
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
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **B2, the honest greatest chain-state height from `T₁ + Δ` to `a_r`.** The proof; the audited
statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: at least `H₂` by `lem89b_at` (Lemma 89b on the four facts its proof reads) at the
honest attestation of height `H₂` sent before `T₁`, when `H₂ ≠ 0`; at most `H₂ + 1` because
the greatest chain-state height `hMax M S.C n` of `w`'s tree is the chain-state height of a block
`w` holds (`cachesWitnessed_of_stateBefore`) and A2 bounds every such block.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `T₁`: the time of the
  threshold; `r`: the round; `H₂`: the threshold; `t`: the clock value; `k₀`: the step of `v`'s tick
  to `aR M S r`; `v`: the attester; `w`: the validator.

Roots name blocks until the real time of `w`'s tick `k` to `t`: the proof reads `lem89b_at` at `b := t`,
at that tick.

Restated with the delivery premises up to `t`: the bound of its roots, `lem89b_at` read at `b := t`.

Read aloud: once the phase has settled, every honest validator knows the threshold's height and
nothing higher than one more than it, up to the step of the first attestation above it, with the delivery
premises up to the bound. -/
theorem honest_h_max_bounds_upTo (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ t k₀ : ℕ) (v w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks t) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST t)
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
    exact old_height_le_hMax_at_tick M F U Fx S A x R GST tGAT tAwakeEnd T₁ H₂ t t T₁ k w E hNet hSkew hRedeliver Sy hΔs
      hParent hGST hT₁s hThird hAwake hH₂ hk (le_trans (R.time_mono htr) hEnd) hRoots hw le_rfl ht₁ hwt le_rfl
  · -- the upper bound: A2 at `w`'s tick `k` to `t`, a step at most `k₀`
    have hks := (tickStep_eq_of_lbl M) x E hk
    obtain ⟨-, ⟨X, hX, hXh⟩, -⟩ := (cachesWitnessed_of_exec M F) S A x R E k w
    show hMax M S.C (x.st (x.tickStep w t) w) ≤ H₂ + 1
    rw [hks, ← hXh]
    exact (held_height_le_before_action M F Fx) S A x R E tAwakeEnd H₂ k₀ k w X
      hThird hOld hEnd htr hX

end GoldilocksCorrectness.Record.Proofs.Executions

