module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.Lemma89fStatementsUpTo

@[expose] public section

/-!
# `Lemma89.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `front_of_frontWindowStable`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq)
open GoldilocksCorrectness.Statements.Routines (JustificationCertOn ProgressCertOn
  RootsNameBlocksIn)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **The base at an opening's slot `s`, from a stable window.** `lem89fq_front` with
`s_w := s − 2k` and `s' := s − 1`: when the frames of the members are stable through the `2k − 1`
slots before `s`, the chain invariant and the lock invariant hold at slot `s − 1` for the family
of the members' live lock blocks and roots.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times of the phase; `s`: the honest round opening slot; `Hon`: one member set per slot.

Roots name blocks until `supportCutoff S (s - 1)`: `lem89fq_front` at `s' := s − 1`.

Restated with the delivery premises up to `supportCutoff S (s - 1)`: the bound of `lem89fq_front_upTo` at `s' := s − 1`, the bound of its roots. -/
theorem front_of_frontWindowStable_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd s : ℕ) (Hon : ℕ → Finset V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s - 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s - 1)))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s - 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ tGAT)
    (hk : 2 * S.C.k ≤ s)
    (hHonMono : ∀ s₁, s - 2 * S.C.k ≤ s₁ → s₁ < s - 1 → Hon (s₁ + 1) ⊆ Hon s₁)
    (hHon : ∀ s₁, s - 2 * S.C.k ≤ s₁ → s₁ ≤ s - 1 → ∀ v ∈ Hon s₁,
      v ∉ Sched.adv ((supportCutoff S (s₁ + 1) : ℕ) : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv (t : Int) → v ∈ Sched.awake (t : Int))
    (hCommittees : ∀ s₁, s - 2 * S.C.k + S.C.k ≤ s₁ → s₁ ≤ s - 1 →
      (S.P.committee s₁).card < 2 * (S.P.committee s₁ ∩ Hon s₁).card)
    (hsw : tGAT ≤ dutyWindowStart S (s - 2 * S.C.k))
    (hEnd : supportCutoff S (s - 1 + 1) ≤ tAwakeEnd)
    (hStable : FrontWindowStable S Sched x Hon (s - 2 * S.C.k) (s - 1)) :
    ChainInvFor S Sched x (Hon (s - 1)) (FrontFamily S Sched x (Hon (s - 1)) (s - 1)) (s - 1) ∧
    ∀ u ∈ Hon (s - 1),
      LiveLocksOnFamilyAt S Sched x (FrontFamily S Sched x (Hon (s - 1)) (s - 1)) (s - 1) u :=
  GoldilocksCorrectness.Statements.Executions.lem89fq_front_upTo S Sched x GST tGAT tAwakeEnd
    (s - 2 * S.C.k) (s - 1) Hon hDiv hMono hSync hCatch hRoots hParent hOwner hGST
    hHonMono hHon hAwake hCommittees hsw (by omega) hEnd hStable.1 hStable.2

end GoldilocksCorrectness.Proofs.Executions

