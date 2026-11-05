module
public import GoldilocksCorrectness.Statements.Executions.ConfirmedTipStatements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma90InclusionUpTo

@[expose] public section

/-!
# `ConfirmedTipStatements.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Statements/Executions/ConfirmedTipStatements.lean` that
name a delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound
on the deadlines. The
bound of each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads,
written in the twin's own parameters.

* `lem90_included_update_facts_until`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff
  proposalWindowStart)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
open Framework.StsMultisetLog (AtomicAction SignedMsg)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

/-- **The per-validator export of the inclusion, on the chain before slot `s − 1`, with the caches
up to the support cutoff of slot `s + 1`.** In an execution where every time is reached, corruption
is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST` (synchrony from the
receiver's wake, and catch-up on wake), a block reaches a validator only
once it holds the parent, and nobody votes in an honest validator's name; under unforgeability, with
fewer than a quorum of validators ever in the adversary set and committee sleepiness from `anchor`,
at or before `x[i₁].time`; with `GST` at most the vote time of slot `s₀` and the support cutoff of
slot `s₀ + 1` at or before `x[i₁].time`; with every honest attestation sent before the support
cutoff of slot `s₀ + 1` of height at most `H`, and the lock invariant at the healed slot `s₀` itself
(`hLocks₀`: every live lock entry an honest active validator of slot `s₀` keeps after its revocation
of slot `s₀ + 1` is on a block of the honest chain before slot `s₀ + 1` or on an ancestor of one);
with roots naming blocks among what honest validators hold by the support cutoff of slot `s + 1`;
with the updaters' confirmations of the slots from `s₀` to before `s − 1` forming one chain
(`ConfirmationsChainBefore`), the chain invariant and the lock invariant at every slot after `s₀`
and at most `s`, and the caches of every validator honest at a step at a time from `x[i₁].time` to
the support cutoff of slot `s + 1` on the honest chain with justification height greater than `H`:
for a slot `s` starting after `x[i₁].time` whose proposer is awake and honest from the start of the
proposal window of slot `s` to the support cutoff `c` of slot `s + 1`, whose tick at the start of
slot `s` put `B` on the wire, and no block it held before the start of slot `s` having `B`'s root:
every updater `v` of slot `s` runs the update of slot `s + 1` at `c` with some answer `A'`, which
saves `B` as the confirmation of slot `s`, has `B` among its fast blocks and the lock entry on `B`
with the deadline of a slot-`s` lock, keeps every lock entry live at `c` on `B` or an ancestor of
`B`, and records `B` as the confirmed tip; and `v`'s state right after `c` has `A'`'s saved
confirmations, fast blocks, lock entries and record.

Why: steps 2 to 5 of the inclusion, which read the chain only for blocks on it before slot `s − 1`
(the proposer's root and anchor, the voters' roots, the blocks Lemma 91 (b) to (d) compare), the
invariant and the locks only at slots `s − 1` and `s`, and the caches only up to the update.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `s`: the slot; `B`: the proposal; `v`: the updater.



Read aloud: with the lock invariant also at the healed slot, every updater of the slot confirms the
honest proposal fast, locks it, records it, and keeps no live lock off its chain, reading nothing
after the slot's update.

Restated with the delivery premises up to `supportCutoff S s`: the slot-`s` votes reach every updater by then, and the proposal of slot `s` reaches its voters by `voteTime S s`. -/
theorem lem90_included_update_facts_until_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H s : ℕ) (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s - 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ u ∈ honestActiveAt S Sched s',
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' u)
    (hLocks₀ : ∀ u ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ supportCutoff S (s + 1) →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hs : x[i₁].time < slotStart S s)
    (hp : ∀ t : ℕ, proposalWindowStart S s ≤ t → t ≤ supportCutoff S (s + 1) →
      S.P.proposer s ∈ Sched.awake (t : Int) ∧ S.P.proposer s ∉ Sched.adv (t : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hNoCollision : ¬ RootCollisionAtProposal S Sched x s B)
    (hv : v ∈ updaterAt S Sched s) :
    ∃ A' : ACState V,
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A' ∧
      A'.saved_confirmation s = some B ∧
      B ∈ A'.fast_blocks ∧
      LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∈ A'.lock_entries ∧
      (∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
          ((supportCutoff S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
      A'.latest_confirmed = B ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation =
        A'.saved_confirmation ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.fast_blocks = A'.fast_blocks ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.lock_entries = A'.lock_entries ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.latest_confirmed =
        A'.latest_confirmed :=
  GoldilocksCorrectness.Proofs.Executions.lem90_included_update_facts_until_upTo S Sched x GST s₀ anchor
    i₁ H s B v hDiv hMono hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST
    ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hs hp hPropose hNoCollision hv

end GoldilocksCorrectness.Statements.Executions

