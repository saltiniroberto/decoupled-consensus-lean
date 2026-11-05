module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.Lemma89fStatementsUpTo
public import GoldilocksCorrectness.Statements.Executions.Lemma89fStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89UpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89UpTo.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: the base at an opening's slot from a
stable window, with the delivery premises up to the bound the theorems read.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **The base at an opening's slot `s`, from a stable window.** `lem89fq_front` with
`s_w := s − 2k` and `s' := s − 1`: when the frames of the members are stable through the `2k − 1`
slots before `s`, the chain invariant and the lock invariant hold at slot `s − 1` for the family
of the members' live lock blocks and roots.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times of the phase; `s`: the honest round opening slot; `Hon`: one member set per slot.

Roots name blocks until `M.supportCutoff S.C (s - 1)`: `lem89fq_front` at `s' := s − 1`.

Restated with the delivery premises up to `M.supportCutoff S.C (s - 1)`: the bound of
`lem89fq_front_upTo` at `s' := s − 1`, the bound of its roots.

Read aloud: a window stable through the `2k − 1` slots before `s` gives the chain invariant and the
lock invariant at slot `s − 1` for the family of the members' live lock blocks and roots, with the
delivery premises up to the bound. -/
theorem front_of_frontWindowStable_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd s : ℕ) (Hon : ℕ → Finset V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s - 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s - 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s - 1)))
    -- roots name blocks also up to the real time of every validator's tick to a clock value at most the
    -- support cutoff of slot `s − 1` (, for `lem89fq_front`)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x) (hOwner : VotesCastByOwner M A x)
    (hGST : GST ≤ tGAT)
    (hGSTw : GST + max (Δ S) Δs ≤ M.viewFreeze S.C (s - 2 * S.C.k))
    (hk : 2 * S.C.k ≤ s)
    (hHonMono : ∀ s₁, s - 2 * S.C.k ≤ s₁ → s₁ < s - 1 → Hon (s₁ + 1) ⊆ Hon s₁)
    (hHon : ∀ s₁, s - 2 * S.C.k ≤ s₁ → s₁ ≤ s - 1 → ∀ v ∈ Hon s₁,
      v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₁ + 1)))
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : ∀ s₁, s - 2 * S.C.k + S.C.k ≤ s₁ → s₁ ≤ s - 1 →
      (S.P.committee s₁).card < 2 * (S.P.committee s₁ ∩ Hon s₁).card)
    (hsw : tGAT ≤ M.dutyWindowStart S.C (s - 2 * S.C.k))
    (hEnd : M.supportCutoff S.C (s - 1 + 1) ≤ tAwakeEnd)
    (hStable : FrontWindowStable M S A x Hon (s - 2 * S.C.k) (s - 1)) :
    ChainInvFor M S A x (Hon (s - 1)) (FrontFamily M S A x (Hon (s - 1)) (s - 1)) (s - 1) ∧
    ∀ u ∈ Hon (s - 1),
      LiveLocksOnFamilyAt M S A x (FrontFamily M S A x (Hon (s - 1)) (s - 1)) (s - 1) u :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem89fq_front_upTo M F U) S A x R GST tGAT tAwakeEnd
    (s - 2 * S.C.k) (s - 1) Hon E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hOwner hGST hGSTw
    hHonMono hHon hAwake hActive hCommittees hsw (by omega) hEnd hStable.1 hStable.2

end GoldilocksCorrectness.Record.Proofs.Executions

