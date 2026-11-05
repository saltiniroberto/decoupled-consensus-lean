module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodInduction
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma90InclusionUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma26UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodEntryDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma85
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma90
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ConfirmedTipStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.NextSlotVoteStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedAttestationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.SleepyStatements
public import GoldilocksCorrectness.Proofs.Executions.PeriodInduction
public import GoldilocksCorrectness.Proofs.Executions.Lemma90InclusionUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma26UpTo
public import GoldilocksCorrectness.Proofs.Executions.PeriodEntryDelivery
public import GoldilocksCorrectness.Proofs.Executions.Lemma85
public import GoldilocksCorrectness.Proofs.Executions.Lemma90
public import GoldilocksCorrectness.Statements.Executions.ConfirmedTipStatementsUpTo
public import GoldilocksCorrectness.Statements.Executions.NextSlotVoteStatementsUpTo
public import GoldilocksCorrectness.Statements.Executions.HealedAttestationStatements
public import GoldilocksCorrectness.Statements.Executions.SleepyStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# AsyncHandover, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/AsyncHandover.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 99 without the confirmed tips read
before the healing phase, namely the first six clauses of `HandoverFactsOfChainBlock` from the
healed facts bounded at the hand-over update, its last clause for the confirmed tips read from the
healing phase's start on, and their three helpers. The page's routine-level theorems are the facts'
fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart
  proposalWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart
  dutyWindowStart_succ_lt_supportCutoff one_le_Δ slotStart_mono slot_le_of_supportCutoff_lt
  supportCutoff_eq supportCutoff_mono voteTime_eq)

open GoldilocksCorrectness.Statements.Routines (confirmedOf)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Proofs.Executions (mem_awakeThroughout_of_forall)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (CachesCompatibleWith)

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
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once. No statement and no proof term changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## Helpers -/

/-- A block on the honest chain at a slot `σ ≤ s` is `B` or an ancestor of `B`, when every block of
the honest chain before slot `s` is, and every updater of slot `s` saved `B`.

Why: at `σ < s` the first hypothesis; at `σ = s` the block is an ancestor of an updater's saved
confirmation of slot `s`, which is `B`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `s`: the slot;
  `B`: the block; `σ`: the slot of `D`; `D`: the block on the chain.

Read aloud: a block on the honest chain at a slot `σ` at most `s` is `B` or an ancestor of `B`, when
every block of the honest chain before slot `s` is and every updater of slot `s` saved `B`. -/
theorem onHonestChainAt_ancestorEq_of_le {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} {s₀ s : ℕ} {B : Block V}
    (hBefore : ∀ C : Block V, OnHonestChainBefore M S A x s₀ s C → C.AncestorEq B)
    (hSaved : ∀ v ∈ updaterAt M S A x s,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B)
    {σ : ℕ} {D : Block V} (hD : OnHonestChainAt M S A x s₀ σ D) (hσ : σ ≤ s) :
    D.AncestorEq B := by
  rcases Nat.lt_or_eq_of_le hσ with hlt | heq
  · exact hBefore D ⟨σ, hlt, hD⟩
  · subst heq
    obtain ⟨-, v, hv, C, hC, hDC⟩ := hD
    rw [hSaved v hv] at hC
    injection hC with hBC
    rw [hBC]
    exact hDC

/-- An honest active validator of slot `s + 1` is an updater of slot `s`: it is active from the duty
window's start of slot `s + 1` up to its tick to the support cutoff of slot `s + 2`, so up to its tick
to the support cutoff of slot `s + 1` (`honestActiveAt_succ_subset_updaterAt`).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`: the setup, the schedule; `s`: the slot; `w`: the validator; `R`, `E`: the run's and
  the environment's facts.

Read aloud: an honest active validator of slot `s + 1` is an updater of slot `s`. -/
theorem updaterAt_of_honestActiveAt_succ (U : UniformSchedule M.toSlotLayout) (S : Setup V) (A : Activity V)
    (s : ℕ) (w : V) {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hw : w ∈ honestActiveAt M S A x (s + 1)) : w ∈ updaterAt M S A x s :=
  (honestActiveAt_succ_subset_updaterAt M F U) S A s R E hSkew hw

/-- **The honest proposal of the hand-over slot, read at slot `s`.** Under Lemma 99's hypotheses
without the voter condition at slot `s + 1`: every block on the honest chain at a slot at most `s`
is `B` or an ancestor of `B`; every updater of slot `s` saved `B`; and `HonestChainExtends` holds for
`B` at slot `s` at the honest active validators of `s`.

Why: `honest_proposal_saved_until_upTo` at `q := s − 2` (the slot is at least `s₀ + 2`, the healed
slot's update being at or before `x[i₁].time`), with the lock invariant at slot `s − 2` from
`locks_before_of_locks_le`; and `onHonestChainAt_ancestorEq_of_le`.

Its roots, quorum and caches rows read up to the real time of each updater's tick to the hand-over update, with the
proposer's tick at or after `x[i₁].time` and the holder rows `hHold`, `hHoldP`: the rows
`honest_proposal_saved_until_upTo` reads at slot `s`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold; `s`: the hand-over slot;
  `B`: its proposal.

Read aloud: under Lemma 99's hypotheses without the voter condition at slot `s + 1`, every block on
the honest chain at a slot at most `s` is `B` or an ancestor of `B`, every updater of slot `s` saved
`B`, and `HonestChainExtends` holds for `B` at slot `s`. -/
theorem handover_chain_of_healed_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H s : ℕ) (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : ∀ v ∈ updaterAt M S A x s, RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : ∀ v ∈ updaterAt M S A x s, A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
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
    (hCaches : ∀ v ∈ updaterAt M S A x s, ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j →
      x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (hs : x.time i₁ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₁ < x.time k)
    (hHold : ∀ s' : ℕ, s - 1 ≤ s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hp : S.P.proposer s ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C s)
        (M.supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)))
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoCollision : ¬ RootCollisionAtProposal M S A x s B) :
    (∀ (σ : ℕ) (D : Block V), OnHonestChainAt M S A x s₀ σ D → σ ≤ s → D.AncestorEq B) ∧
    (∀ v ∈ updaterAt M S A x s,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B) ∧
    HonestChainExtends M S A x (honestActiveAt M S A x s) B s := by
  have hΔ := one_le_Δ S
  -- the natural-number fact the phase's end step's real time gives
  have hcs : M.supportCutoff S.C (s₀ + 1) < M.slotStart S.C s := by
    have := lt_of_le_of_lt ht₀ hs.1
    exact_mod_cast this
  -- the slot is at least `s₀ + 2`
  have hss₀ : s₀ + 2 ≤ s := by
    by_contra hc
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s ≤ s₀ + 1 by omega)
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₀ + 1)
    have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1)
    omega
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, s = q + 2 := ⟨s - 2, by omega⟩
  obtain ⟨ip, hl, hsent⟩ := hPropose
  have hRootNew : ∀ B' ∈ (x.tickInput (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2))).tree,
      B'.root ≠ B.root := fun B' hB' h => hNoCollision ⟨B', hB', h⟩
  have hChain' : ConfirmationsChainBefore M S A x s₀ (q + 1) := by
    rwa [show q + 2 - 1 = q + 1 by omega] at hChain
  have hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u :=
    (locks_before_of_locks_le M F) S A x s₀ q (fun s' h1 h2 => hLocks s' h1 (by omega)) hLocks₀
      (by omega)
  obtain ⟨hBefore, -, -, hHCE, hSaved, -, -⟩ :=
    (honest_proposal_saved_until_upTo M F U Fx) S A x R GST s₀ anchor i₁ H q ip B E hNet hSkew hRedeliver Sy hΔs
      hRoots hParent hAdvQ (hSleepK.mono M (by first | omega | (norm_cast; omega) | (norm_cast; done))) hAnchor hGST hChain' hInv hLocks hOld hCaches ht₀
      (by omega) hs hLk (fun s' h1 h2 => hHold s' (by omega) h2) hp hHoldP hl hsent hRootNew
  exact ⟨fun σ D hD hσ => (onHonestChainAt_ancestorEq_of_le M F) hBefore hSaved hD hσ, hSaved, hHCE⟩

/-! ## Lemma 99, the first six clauses -/

/-- **A lock entry live at a time is live at every earlier time.** `M.is_live n t e` asks `t` to be
less than the entry's deadline and the entry's block to be in the tree of `M.fg_to_ac n`
(`is_live_iff`, from `F.rd.is_live_eq`); the second does not read `t`, and the first holds at every
`t' ≤ t` when it holds at `t`.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `t`, `t'`: the times, `t' ≤ t`; `e`: the lock entry.

Read aloud: an entry still live at a later time was live at every earlier time. -/
theorem is_live_of_le {n : M.N} {t t' : Int} {e : M.LE} (h : M.is_live n t e = true) (htt : t' ≤ t) :
    M.is_live n t' e = true := by
  rw [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at h ⊢
  exact ⟨lt_of_le_of_lt htt h.1, h.2⟩

/-- **Lemma 99, the first six clauses of the hand-over facts.** The proof; the audited statement is
in `Statements/Executions/AsyncHandoverStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold; `s`: the hand-over slot;
  `B`: its proposal.

Read aloud: after the healed phase, with the network synchronous through the hand-over slot's votes
and the slot-`(s + 1)` voters' fork choice following the honest chain, right after the hand-over
update every updater of slot `s` holds the lock on `B` and records `B`; no honest validator's
caches, certificates or attestations conflict with `B`; and every honest active vote of slot `s + 1`
is on `B`'s chain. -/
theorem handoverFacts_six_of_healed_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H s : ℕ) (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- the end of the window clauses 3 to 5 conclude in: at most one behind-bound after the hand-over update
    -- (; at `tW := cut(s + 1) + ΔClockBehind` the window of)
    (tW : ℝ) (htW : tW ≤ (M.supportCutoff S.C (s + 1) : ℝ) + ΔClockBehind)
    (hRoots : RootsNameBlocksUntil M A x tW)
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) tW)
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
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ tW →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (hRootsU : ∀ v ∈ updaterAt M S A x s, RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hAdvQU : ∀ v ∈ updaterAt M S A x s, A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hCachesU : ∀ v ∈ updaterAt M S A x s, ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j →
      x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (hFrames : ∀ w ∈ honestActiveAt M S A x (s + 1), VoterFrameOnChainAt M S A x s₀ (s + 1) w)
    (hs : x.time i₁ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₁ < x.time k)
    (hHold : ∀ s' : ℕ, s - 1 ≤ s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hp : S.P.proposer s ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C s)
        (M.supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)))
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoCollision : ¬ RootCollisionAtProposal M S A x s B) :
    H < (M.chainStateOf S.C B).h ∧
    (∀ w ∈ updaterAt M S A x s,
      (x.tickOutput w (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B ∧
      (x.tickOutput w (M.supportCutoff S.C (s + 1))).latestConfirmed = B ∧
      HolderInvAt M S x s B (x.tickStep w (M.supportCutoff S.C (s + 1)) + 1) w) ∧
    (∀ (j : ℕ) (u : V), (M.supportCutoff S.C (s + 1) : ℝ) ≤ x.time j → x.time j ≤ tW → u ∉ A.corrupted j →
      CachesCompatibleWith M S B H (x.st j u)) ∧
    (∀ j : ℕ, (M.supportCutoff S.C (s + 1) : ℝ) ≤ x.time j → x.time j ≤ tW → CertificatesCompatibleWithAtOfChainBlock M A x H B j) ∧
    (∀ j : ℕ, (M.supportCutoff S.C (s + 1) : ℝ) ≤ x.time j → x.time j ≤ tW →
      AttestationsCompatibleWithBeforeOfHeldEntry M S A x B H (M.supportCutoff S.C (s₀ + 1)) j) ∧
    (∀ Δs b₀ b₁ : ℕ, VotesExtendAt M S A x s B Δs b₀ b₁ (s + 1)) := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  -- the facts at slot `s`, with the rows at each updater's tick (`handover_chain_of_healed_upTo`)
  obtain ⟨hle, hSaved, hHCE⟩ := (handover_chain_of_healed_upTo M F U Fx) S A x R GST s₀ anchor i₁ H s B E hNet
    hSkew hRedeliver Sy hΔs hRootsU hParent hAdvQU hSleepK hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCachesU
    hs hHold hp hHoldP hPropose hNoCollision
  -- the slot's times
  obtain ⟨hv0, hc0, -, hs0, -, -, -⟩ := (slot_times M F U) S s
  obtain ⟨hv1, hc1, -, -, -, -, -⟩ := (slot_times M F U) S (s + 1)
  have hcR1 : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = (M.slotStart S.C s : ℝ) + 6 * Δ S := by
    rw [hc1, hs0]; push_cast; ring
  have hvR1 : ((M.voteTime S.C (s + 1) : ℕ) : ℝ) = (M.slotStart S.C s : ℝ) + 5 * Δ S := by
    rw [hv1, hs0]; push_cast; ring
  have hcR0 : ((M.supportCutoff S.C s : ℕ) : ℝ) = (M.slotStart S.C s : ℝ) + 2 * Δ S := by
    rw [hc0]; push_cast; ring
  -- the slot is at least `s₀ + 2`
  have hss₀ : s₀ + 2 ≤ s := by
    have hcs : M.supportCutoff S.C (s₀ + 1) < M.slotStart S.C s := by
      have := lt_of_le_of_lt ht₀ hs.1
      exact_mod_cast this
    by_contra hc
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show s ≤ s₀ + 1 by omega)
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₀ + 1)
    have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1)
    omega
  have hi₁c : x.time i₁ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) := by linarith [hs.1]
  -- a slot whose next slot's support cutoff a validator ticked to by one behind-bound after the hand-over update is
  -- at most `s`: that tick is at a real time at least the cutoff less `ΔClockAhead` (`tick_active`), and
  -- `ΔClockAhead + ΔClockBehind < Δ S` (`hSkew`)
  have hσs : ∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
      x.time k ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind → σ ≤ s := by
    intro σ k u hl hk
    have h1 := (E.tick_active k u _ hl).2.1
    have h3 : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) < ((M.supportCutoff S.C (s + 1) + Δ S : ℕ) : ℝ) := by
      push_cast; linarith
    have h4 : M.supportCutoff S.C (σ + 1) < M.supportCutoff S.C (s + 1) + Δ S := by exact_mod_cast h3
    by_contra hc
    have := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_add_Δ_le_slotStart_of_lt M.toSlotLayout
      F.sched) S (show s + 1 < σ + 1 by omega)
    have := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (s + 1)
    have := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (σ + 1)
    omega
  have hAgree := (GoldilocksCorrectness.Record.Proofs.Executions.lem82_honest_attestations_on_chain M F U) S A x R
    s₀ E
  -- a committee member of slot `s` that is an updater of slot `s` (Lemma 88's first conjunct)
  have hanchor : anchor ≤ M.slotStart S.C (s + 1) := by
    have h : (anchor : ℝ) < (M.slotStart S.C s : ℝ) := lt_of_le_of_lt hAnchor hs.1
    have h' : anchor < M.slotStart S.C s := by exact_mod_cast h
    omega
  obtain ⟨hMaj, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.lem88_counting_of_committeeSleepiness M F)
    S A x R E anchor s (S.P.proposer s) 0 hSleepK hanchor le_rfl
  obtain ⟨u₀, hu₀⟩ : ∃ u : V, u ∈ honestActiveAt M S A x s ∩ S.P.committee s := by
    have hpos : 0 < (honestActiveAt M S A x s ∩ S.P.committee s).card := by omega
    exact Finset.card_pos.1 hpos
  have hHonU : ∀ u ∈ honestActiveAt M S A x s, u ∈ updaterAt M S A x s := fun u hu =>
    Activity.mem_activeThroughoutToTick_of_le
      (GoldilocksCorrectness.Proofs.Routines.duty_window_start_mono S (Nat.le_succ s))
      ((honestActiveAt_window M F) S A s u E hu)
  have hu₀U : u₀ ∈ updaterAt M S A x s := hHonU u₀ (Finset.mem_inter.1 hu₀).1
  -- clause 1: at `u₀`'s tick to the hand-over update, its justified block is on the honest chain at a slot at most
  -- `s`, so `B` or an ancestor of `B`, at a height greater than `H`
  have hcl1 : H < (M.chainStateOf S.C B).h := by
    obtain ⟨k₀, hk₀, -⟩ := Activity.mem_activeThroughoutToTick.1 hu₀U
    have hk₀s : x.tickStep u₀ (M.supportCutoff S.C (s + 1)) = k₀ := (tickStep_eq_of_lbl M) x E hk₀
    have hk₀t := (E.tick_active k₀ u₀ _ hk₀).2
    have hi₁k₀ : x.time i₁ ≤ x.time k₀ := by linarith [hs.1, hk₀t.1]
    have hu₀c : u₀ ∉ A.corrupted k₀ := E.not_mem_corrupted_of_tick hk₀
    have hC := hCachesU u₀ hu₀U k₀ u₀ hi₁k₀ (by rw [hk₀s]) hu₀c
    obtain ⟨σ, ⟨k, u, hk, hl⟩, hJσ⟩ := (justified_onHonestChainAt_of_caches M F U Fx) S A x R s₀
      (M.supportCutoff S.C (s₀ + 1)) H k₀ u₀ E (by rw [← hk₀s]; exact hRootsU u₀ hu₀U)
      ((hAdvQU u₀ hu₀U).mono (by rw [hk₀s]; exact max_le le_rfl (le_trans ht₀ hi₁k₀))) hAgree hOld hu₀c hC.1
    have hσ : σ ≤ s := hσs σ k u hl (by linarith [(time_mono M) x R hk.le, hk₀t.2])
    have hJB := hle σ _ hJσ hσ
    have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C hJB
    have h1 := hC.1
    have h2 := hC.2.2.2.1
    omega_nat
  -- clause 2: the lock holders, each at its own tick to the hand-over update
  -- (`included_update_facts_q_until_upTo` at `q := s − 2`)
  have hcl2 : ∀ w ∈ updaterAt M S A x s,
      (x.tickOutput w (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B ∧
      (x.tickOutput w (M.supportCutoff S.C (s + 1))).latestConfirmed = B ∧
      HolderInvAt M S x s B (x.tickStep w (M.supportCutoff S.C (s + 1)) + 1) w := by
    intro w hw
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hw
    obtain ⟨q, rfl⟩ : ∃ q : ℕ, s = q + 2 := ⟨s - 2, by omega⟩
    obtain ⟨ip, hl, hsent⟩ := hPropose
    have hRootNew : ∀ B' ∈ (x.tickInput (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2))).tree,
        B'.root ≠ B.root := fun B' hB' h => hNoCollision ⟨B', hB', h⟩
    have hChain' : ConfirmationsChainBefore M S A x s₀ (q + 1) := by
      rwa [show q + 2 - 1 = q + 1 by omega] at hChain
    have hLk : ∀ u ∈ honestActiveAt M S A x q,
        LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u :=
      (locks_before_of_locks_le M F) S A x s₀ q (fun s' h1 h2 => hLocks s' h1 (by omega)) hLocks₀
        (by omega)
    obtain ⟨hSv, -, hLE, hLive, hLC⟩ := (included_update_facts_q_until_upTo M F U Fx) S A x R GST s₀ anchor i₁ H q
      ip B w E hNet hSkew hRedeliver Sy hΔs (hRootsU w hw) hParent (hAdvQU w hw) hSleepK hAnchor hGST hChain' hInv
      hLocks hOld (fun j u hj h2 hu => hCachesU w hw j u ((time_mono M) x R hj.le) h2 hu) ht₀ (by omega) hs hLk
      (fun s' h1 h2 => hHold s' (by omega) h2) hp hHoldP hl hsent hRootNew hw
    refine ⟨hSv, hLC, Or.inl hLE, ?_, (latest_confirmed_mem_T_of_exec M F U) x R E _ w, ?_, ?_⟩
    · show B.AncestorEq (x.tickOutput w (M.supportCutoff S.C (q + 2 + 1))).latestConfirmed
      rw [hLC]
      exact ancestorEq_refl B
    · intro D hD
      exact (compatible_iff D B).2 (Or.inl
        ((GoldilocksCorrectness.Record.Proofs.Executions.fast_blocks_ancestorEq_saved_of_updater M F U) S A x R
          (q + 2) w B E hw hSv D hD))
    · -- the clock after the tick is the hand-over update, so a lock entry live at a later clock value is live at
      -- the update
      intro e he t hct hlive
      have hcv : x.clockValue (x.tickStep w (M.supportCutoff S.C (q + 2 + 1)) + 1) w =
          M.supportCutoff S.C (q + 2 + 1) := x.clockValue_succ_of_tick (x.lbl_tickStep ⟨k, hk⟩)
      rw [hcv] at hct
      exact (compatible_iff _ _).2 (Or.inl (hLive e he _ ((is_live_of_le M F) hlive (by exact_mod_cast hct))))
  -- clause 3: the caches at a step of the window, on `B`'s chain through the justified block's slot
  have hcl3 : ∀ (j : ℕ) (u : V), ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j → x.time j ≤ tW →
      u ∉ A.corrupted j → CachesCompatibleWith M S B H (x.st j u) := by
    intro j u hj1 hj2 hu
    have hC := hCaches j u (le_trans hi₁c hj1) hj2 hu
    obtain ⟨σ, ⟨k, u', hk, hl⟩, hJσ⟩ := (justified_onHonestChainAt_of_caches M F U Fx) S A x R s₀
      (M.supportCutoff S.C (s₀ + 1)) H j u E
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hj2 hRoots)
      (hAdvQ.mono (max_le hj2 (by linarith [ht₀, hi₁c, hj1, hj2]))) hAgree hOld hu hC.1
    have hσ : σ ≤ s := hσs σ k u' hl (by linarith [(time_mono M) x R hk.le])
    exact ⟨hC.1, Or.inl (hle σ _ hJσ hσ), hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2⟩
  -- clause 5: the attestations sent before a step of the window, each from the source its tick took
  have hcl5 : ∀ j : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j → x.time j ≤ tW →
      AttestationsCompatibleWithBeforeOfHeldEntry M S A x B H (M.supportCutoff S.C (s₀ + 1)) j := by
    intro j hj1 hj2 i t v a hi hl hsent
    refine ⟨fun ht hc => hOld i t v a hl (by exact_mod_cast ht) hc hsent, fun ht _ => ?_⟩
    obtain ⟨s', src, C, rfl, hv, -, hsT, hSv, hsrcC, hh, hT⟩ :=
      (attest_tick_update_source M F U) S A x R i _ v a E hl hsent
    have hs₀s' : s₀ ≤ s' := by
      by_contra hlt
      have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt_of_lt M.toSlotLayout F.sched) S
        (show s' + 1 < s₀ + 1 by omega)
      omega
    have hs's : s' ≤ s := hσs s' i v hl (by linarith [(time_mono M) x R hi.le])
    obtain ⟨hE1, hE2, hE3⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.isEntry_T_h M F) S.C src
    have hsrcB : src.AncestorEq B := hle s' src ⟨hs₀s', v, hv, C, hSv, hsrcC⟩ hs's
    refine ⟨(M.chainStateOf S.C src).T_h, Or.inl (ancestorEq_trans hE3 hsrcB), hE1, hE2.trans hh, hT, ?_⟩
    exact (inHonestTreeBy_of_st M F) x R E (E.not_mem_corrupted_of_tick hl) le_rfl
      ((GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E i v src _ hsT hE3)
  -- clause 4: the certificates, from the attestations
  have hcl4 : ∀ j : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j → x.time j ≤ tW →
      CertificatesCompatibleWithAtOfChainBlock M A x H B j := fun j hj1 hj2 =>
    (GoldilocksCorrectness.Record.Proofs.Executions.certificatesCompatibleWithAtOfChainBlock_of_attestations M F)
      S A x R E j ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hj2 hRoots)
      (hAdvQ.mono (max_le hj2 (by linarith [ht₀, hi₁c, hj1, hj2]))) (hcl5 j hj1 hj2)
  -- clause 6: the votes of slot `s + 1`, by Lemma 26b over the committee members of slot `s`
  have hGSTs : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s :=
    le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show s₀ ≤ s by omega))
  have hBchain : OnHonestChainBefore M S A x s₀ (s + 1) B :=
    ⟨s, Nat.lt_succ_self s, by omega, u₀, hu₀U, B, hSaved u₀ hu₀U, ancestorEq_refl B⟩
  have hMaj' : (S.P.committee s).card < 2 * (S.P.committee s ∩ honestActiveAt M S A x s).card := by
    rw [Finset.inter_comm]; exact hMaj
  have hkey : ∀ w ∈ honestActiveAt M S A x (s + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
        (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_w ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree,
        vote = GoldfishVote.mk w (s + 1) H_w.root ∧ B.AncestorEq H_w := by
    intro w hw vote hSend
    obtain ⟨iS, hiS, -⟩ := id hSend
    have hwU : w ∈ updaterAt M S A x s := (updaterAt_of_honestActiveAt_succ M F) U S A s w R E hSkew hw
    obtain ⟨Hf, hHf⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.exists_votes_on_chain M F U) S A x R s
      (S.P.committee s ∩ honestActiveAt M S A x s) B E hSkew
      (fun u hu => Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hu).1⟩)
      (fun u hu => hHCE.1 u (Finset.mem_inter.1 hu).2)
    -- `w`'s tick to the support cutoff of slot `s`, before its tick to the hand-over update
    obtain ⟨kR, hkR, hkRw⟩ := (updater_reader_gives_core_window M F U) x R E hΔs hSkew hwU
    obtain ⟨kw, hkw, -⟩ := Activity.mem_activeThroughoutToTick.1 hwU
    have hkRt := (E.tick_active kR w _ hkR).2
    have hkwt := (E.tick_active kw w _ hkw).2
    have hRootsKR : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))) := by
      rw [(tickStep_eq_of_lbl M) x E hkR]
      refine (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) ?_ (hRootsU w hwU)
      rw [(tickStep_eq_of_lbl M) x E hkw]
      linarith [hkRt.2, hkwt.1]
    have hTI : x.tickInput w (M.voteTime S.C (s + 1)) = x.st iS w := by
      unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hiS]
    obtain ⟨hF2, hF3⟩ := hFrames w hw B hBchain iS hiS
    -- the live locks after `w`'s revocation at the vote time of slot `s + 1` are on the honest chain before `s`
    have hLk : ∀ (n' : M.N) (sent : List (NamedObject V)),
        .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) →
        AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
        ∀ e ∈ M.lockEntries n',
          M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
            ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true := by
      obtain ⟨q, hq⟩ : ∃ q : ℕ, s = q + 2 := ⟨s - 2, by omega⟩
      subst hq
      intro n' sent hrun hA e he hlive
      obtain ⟨D, ⟨σ, hσ, hD⟩, heD⟩ := (updater_locks_on_chain_of_updaterAt M F U) S A x R E hSkew s₀ q
        (by omega) (hLocks (q + 1) (by omega) (by omega)) w hwU n' sent hrun hA e he hlive
      exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans heD (hle σ D hD hσ.le)))
    exact (GoldilocksCorrectness.Record.Proofs.Executions.lem26b_goldfish_vote_extends_voter_majority_block_held_upTo
      M F U) S A x R GST s (S.P.committee s ∩ honestActiveAt M S A x s) Hf B w vote E hNet hSkew hRedeliver Sy hΔs
      hRootsKR hParent (GoldilocksCorrectness.Record.Proofs.Executions.votesCastByOwner_of_unforgeability M F S A x R E)
      hGSTs
      (fun u hu => ⟨(hHf u hu).1,
        (not_mem_corrupted_tickStep_of_outside_at_honest_ticks_of_lbl M F) x E hiS
          ((outside_at_honest_ticks_of_mem_activeThroughoutToTick M F) x R E
            ((honestActiveAt_window M F) S A s u E (Finset.mem_inter.1 hu).2) (by rw [hvR1, hcR1]; linarith)),
        (hHf u hu).2.2.1, (hHf u hu).2.2.2.1, (hHf u hu).2.2.2.2⟩)
      (fun votes sv hC => ((counting_of_committee_majority_st M F) S A x R E s
        (x.tickStep w (M.voteTime S.C (s + 1))) (honestActiveAt M S A x s) w hMaj').2.2 votes sv hC)
      (fun u hu => hHold s (by omega) le_rfl u (Finset.mem_inter.1 hu).2 (Finset.mem_inter.1 hu).1)
      ⟨kR, hkR, hkRw⟩ (by rw [hTI]; exact hF2) (by rw [hTI]; exact hF3) hLk hSend
  have hcl6 : ∀ Δs b₀ b₁ : ℕ, VotesExtendAt M S A x s B Δs b₀ b₁ (s + 1) := fun _ _ _ =>
    ⟨fun u hu vote hsend => hkey u (Finset.mem_inter.1 hu).2 vote hsend,
      fun _ u hu vote hsend => hkey u hu vote hsend⟩
  exact ⟨hcl1, hcl2, hcl3, hcl4, hcl5, hcl6⟩

/-! ## Lemma 99, the confirmed tips from `x[i₁].time` on -/

/-- **Lemma 99, the confirmed tips read from `x[i₁].time` to the hand-over update.** The proof; the
audited statement is in `Statements/Executions/AsyncHandoverStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold; `s`: the hand-over slot;
  `B`: its proposal.

Read aloud: what any honest validator had confirmed from `x[i₁].time` to the hand-over update is an
ancestor of the hand-over proposal. -/
theorem confirmed_tips_preceq_handover_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H s : ℕ) (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (M.supportCutoff S.C (s + 1)))
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
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ M.supportCutoff S.C (s + 1) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (hRootsU : ∀ v ∈ updaterAt M S A x s, RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hAdvQU : ∀ v ∈ updaterAt M S A x s, A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hCachesU : ∀ v ∈ updaterAt M S A x s, ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j →
      x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (hLatest : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ M.supportCutoff S.C (s + 1) →
      u ∉ A.corrupted j → (∃ σ : ℕ,
        x.lbl (x.tickStep u (M.supportCutoff S.C (σ + 1))) = Event.tick u (M.supportCutoff S.C (σ + 1)) ∧
        x.tickStep u (M.supportCutoff S.C (σ + 1)) < j ∧
        OnHonestChainAt M S A x s₀ σ (x.st j u).latestConfirmed) ∧
        (x.st j u).latestConfirmed ∈ (x.st j u).tree)
    (hs : x.time i₁ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₁ < x.time k)
    (hHold : ∀ s' : ℕ, s - 1 ≤ s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hp : S.P.proposer s ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C s)
        (M.supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)))
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoCollision : ¬ RootCollisionAtProposal M S A x s B) :
    ∀ (v : V) (T : ℕ) (P : Block V), A.HonestThroughTime x (x.time T) v → x.time i₁ ≤ x.time T →
      x.time T ≤ M.supportCutoff S.C (s + 1) →
      P.AncestorEq (M.ac_confirmed (x.st T v)) → P.AncestorEq B := by
  obtain ⟨hle, -, -⟩ := (handover_chain_of_healed_upTo M F U Fx) S A x R GST s₀ anchor i₁ H s B E hNet hSkew hRedeliver Sy hΔs hRootsU hParent hAdvQU hSleepK hAnchor hGST ht₀ hChain hInv hLocks
    hLocks₀ hOld hCachesU hs hHold hp hHoldP hPropose hNoCollision
  intro v T P hv hT1 hT2 hP
  have hvT : v ∉ A.corrupted T := hv _ le_rfl
  -- a slot whose next slot's support cutoff some validator ticked to before `T` is at most `s`: that tick is at a time
  -- at least the cutoff less `ΔClockAhead` (`tick_active`), at most `x.time T`, and `ΔClockAhead < Δ S` (`hSkew`)
  have hσs : ∀ σ : ℕ, (∃ (k : ℕ) (u : V), k < T ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1))) → σ ≤ s := by
    rintro σ ⟨k, u, hk, hl⟩
    have h1 := (E.tick_active k u _ hl).2.1
    have h2 : x.time k ≤ x.time T := (time_mono M) x R hk.le
    have hB := E.behind_nonneg
    have h3 : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) < ((M.supportCutoff S.C (s + 1) + Δ S : ℕ) : ℝ) := by
      push_cast; linarith
    have h4 : M.supportCutoff S.C (σ + 1) < M.supportCutoff S.C (s + 1) + Δ S := by exact_mod_cast h3
    by_contra hc
    have := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_add_Δ_le_slotStart_of_lt M.toSlotLayout F.sched) S
      (show s + 1 < σ + 1 by omega)
    have := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (s + 1)
    have := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (σ + 1)
    omega
  -- the confirmed tip is the record when the record is in the frame's tree, the frame's finalized block otherwise
  have hOn' : ∃ σ : ℕ, σ ≤ s ∧ OnHonestChainAt M S A x s₀ σ (M.ac_confirmed (x.st T v)) := by
    rw [F.rd.ac_confirmed_eq]
    split
    · -- the record's slot: `v`'s own tick to the next slot's cutoff at a step before `T`
      obtain ⟨σ, hl, hlt, hOn⟩ := (hLatest T v hT1 hT2 hvT).1
      exact ⟨σ, hσs σ ⟨_, v, hlt, hl⟩, hOn⟩
    · rw [(GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]
      obtain ⟨σ, hσ, hOn⟩ := (finalized_onHonestChainAt_of_caches M F U Fx) S A x R s₀ H T v E
        ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hT2 hRoots)
        (hAdvQ.mono ((max_le hT2 (le_trans (le_trans ht₀ hT1) hT2)))) hOld hvT (hCaches T v hT1 hT2 hvT)
      exact ⟨σ, hσs σ hσ, hOn⟩
  obtain ⟨σ, hσ, hOn⟩ := hOn'
  exact ancestorEq_trans hP (hle σ _ hOn hσ)

end GoldilocksCorrectness.Record.Proofs.Executions

