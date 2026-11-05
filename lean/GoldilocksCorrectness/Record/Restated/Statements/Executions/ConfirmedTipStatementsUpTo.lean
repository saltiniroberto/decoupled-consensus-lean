module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ConfirmedTipStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma90InclusionUpTo
public import GoldilocksCorrectness.Statements.Executions.ConfirmedTipStatements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# ConfirmedTipStatementsUpTo, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/ConfirmedTipStatementsUpTo.lean`,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the facts of the
update that includes the honest proposal, with the delivery premises up to the bound, the theorem of
the same name of `Record/Restated/Proofs/Executions/Lemma90InclusionUpTo.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff
  proposalWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F
open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
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
every updater `v` of slot `s`, right after `c`, has saved `B` as the confirmation of slot `s`,
holds `B` among its fast blocks and a lock entry on `B` with the deadline of a slot-`s` lock, has
every lock entry it holds that is live at `c` on `B` or an ancestor of
`B`, and has `B` as its confirmed tip.

The landed statement names the answer `A'` of `v`'s update of slot `s + 1` at `c` and equates `v`'s
state right after `c` with it. The twin states the five facts of that state (D-20A1 (e)); its
recovery takes `A'` from the outcome of `v`'s tick at `c` (`update_state_of_duty`) and Lemma 15.

Why: steps 2 to 5 of the inclusion, which read the chain only for blocks on it before slot `s − 1`
(the proposer's root and anchor, the voters' roots, the blocks Lemma 91 (b) to (d) compare), the
invariant and the locks only at slots `s − 1` and `s`, and the caches only up to the update.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `s`: the slot; `B`: the proposal; `v`: the updater.



Why `hHold` and `hHoldP`: the votes of
slot `s - 1` reach the proposer, and the votes of slot `s` reach every updater, by the synchrony condition
`SyncedWithin`, which serves a message only while its holder stays active for `Δs` after the real time it
serves at; the honest committee members of those two slots, and the proposer, are those holders.

Read aloud: with the lock invariant also at the healed slot, and the honest voters of slots `s - 1` and `s`
and the proposer active for the sync delay after the times the synchrony condition reads them, every updater of the slot confirms the
honest proposal fast, locks it, records it, and keeps no live lock off its chain, reading nothing
after the slot's update.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the slot-`s` votes reach every
updater by then, and the proposal of slot `s` reaches its voters by `M.voteTime S.C s`. -/
theorem lem90_included_update_facts_until_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H s : ℕ) (B : Block V) (v : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s - 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' u)
    (hLocks₀ : ∀ u ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (hs : x.time i₁ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₁ < x.time k)
    (hp : S.P.proposer s ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C s)
        (M.supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)))
    -- the honest voters of slots `s - 1` and `s` are active through the sync delay after Lemma 12's read time of
    -- their slot, and the proposer through the sync delay after `M.slotStart S.C s - max (Δ S) Δs`
    --, the amended row `hHoldP`, under)
    (hHold : ∀ s' : ℕ, s ≤ s' + 1 → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoCollision : ¬ RootCollisionAtProposal M S A x s B)
    (hv : v ∈ updaterAt M S A x s) :
    (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B ∧
      B ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries,
        M.le_B e = B ∧ M.le_d e = S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∧
      (∀ e ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries,
        M.is_live (x.tickInput v (M.supportCutoff S.C (s + 1)))
          ((M.supportCutoff S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).latestConfirmed = B :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem90_included_update_facts_until_upTo M F U Fx) S
    A x R GST s₀ anchor i₁ H s B v E hNet hSkew hRedeliver Sy hΔs hRoots hParent hAdvQ hSleepK
    hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hs hp hHold hHoldP hPropose hNoCollision hv

end GoldilocksCorrectness.Record.Statements.Executions

