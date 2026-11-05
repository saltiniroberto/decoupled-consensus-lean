module
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

@[expose] public section

/-! The audited statements are in
`Statements/Executions/AsyncHandoverStatements.lean`.

Lemma 99 was to conclude `HandoverFactsOfChainBlock` from the healed facts bounded at the hand-over
update. Its last clause speaks of the confirmed tips read at every step up to that update, from
step 0; the healed facts speak of the steps from `x[i₁].time` on only, and before the healing phase
an honest validator can record a block the healed chain abandons (finding F1 of the brief). So the
lemma lands as two kit theorems:

- `handoverFacts_six_of_healed_upTo`: the first six clauses of `HandoverFactsOfChainBlock`;
- `confirmed_tips_preceq_handover_upTo`: the last clause for the confirmed tips read at steps from
  `x[i₁].time` on.

The helpers: `onHonestChainAt_ancestorEq_of_le` (a block on the honest chain at a slot at most `s`
is `B` or an ancestor of `B`), `updaterAt_of_honestActiveAt_succ`, and `handover_chain_of_healed_upTo`
(the facts of `honest_proposal_saved_until_upTo` read at slot `s`).
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart
  proposalWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart
  dutyWindowStart_succ_lt_supportCutoff one_le_Δ slotStart_mono slot_le_of_supportCutoff_lt
  supportCutoff_eq supportCutoff_mono voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_height_mono)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Statements.Routines (confirmedOf)

open GoldilocksCorrectness.Statements.Routines (CachesCompatibleWith)

open GoldilocksCorrectness.Proofs.Routines (is_live_iff)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg AtomicHonest)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

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
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `s`: the slot;
  `B`: the block; `σ`: the slot of `D`; `D`: the block on the chain. -/
theorem onHonestChainAt_ancestorEq_of_le {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {s₀ s : ℕ} {B : Block V}
    (hBefore : ∀ C : Block V, OnHonestChainBefore S Sched x s₀ s C → C.AncestorEq B)
    (hSaved : ∀ v ∈ updaterAt S Sched s,
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some B)
    {σ : ℕ} {D : Block V} (hD : OnHonestChainAt S Sched x s₀ σ D) (hσ : σ ≤ s) :
    D.AncestorEq B := by
  rcases Nat.lt_or_eq_of_le hσ with hlt | heq
  · exact hBefore D ⟨σ, hlt, hD⟩
  · subst heq
    obtain ⟨-, v, hv, C, hC, hDC⟩ := hD
    rw [hSaved v hv] at hC
    injection hC with hBC
    rw [hBC]
    exact hDC

omit [RootOrder] in
/-- An honest active validator of slot `s + 1` is an updater of slot `s`: it is awake from the duty
window's start of slot `s + 1` to the support cutoff of slot `s + 2`, and honest then.

The variables:
- `S`, `Sched`: the setup, the schedule; `s`: the slot; `w`: the validator. -/
theorem updaterAt_of_honestActiveAt_succ (S : Setup V) (Sched : Schedule V)
    (s : ℕ) (w : V) (hMono : Sched.MonotoneCorruption)
    (hw : w ∈ honestActiveAt S Sched (s + 1)) : w ∈ updaterAt S Sched s := by
  have hwin := honestActiveAt_window S Sched (s + 1) w hMono hw
  have hc : supportCutoff S (s + 1) ≤ supportCutoff S (s + 1 + 1) := supportCutoff_mono S (by omega)
  have hd : dutyWindowStart S (s + 1) ≤ supportCutoff S (s + 1) :=
    (dutyWindowStart_succ_lt_supportCutoff S s).le
  exact Finset.mem_sdiff.2 ⟨mem_awakeThroughout_of_forall (fun t h1 h2 =>
    (hwin t h1 (le_trans h2 hc)).1), (hwin _ hd hc).2⟩

/-- **The honest proposal of the hand-over slot, read at slot `s`.** Under Lemma 99's hypotheses
without the voter condition at slot `s + 1`: every block on the honest chain at a slot at most `s`
is `B` or an ancestor of `B`; every updater of slot `s` saved `B`; `HonestChainExtends` holds for
`B` at slot `s` at the honest active validators of `s`; and every updater of slot `s` keeps, after
its revocation of slot `s + 1`, no live lock off `B`'s chain.

Why: `honest_proposal_saved_until_upTo` at `q := s − 2` (the slot is at least `s₀ + 2`, the healed
slot's update being at or before `x[i₁].time`), with the lock invariant at slot `s − 2` from
`locks_before_of_locks_le`; and `onHonestChainAt_ancestorEq_of_le`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold; `s`: the hand-over slot;
  `B`: its proposal. -/
theorem handover_chain_of_healed_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H s : ℕ) (B : Block V)
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
    (hNoCollision : ¬ RootCollisionAtProposal S Sched x s B) :
    (∀ (σ : ℕ) (D : Block V), OnHonestChainAt S Sched x s₀ σ D → σ ≤ s → D.AncestorEq B) ∧
    (∀ v ∈ updaterAt S Sched s,
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some B) ∧
    HonestChainExtends S Sched x (honestActiveAt S Sched s) B s ∧
    (∀ v ∈ updaterAt S Sched s, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) v).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) v).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) v).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) := by
  have hΔ := one_le_Δ S
  -- the slot is at least `s₀ + 2`
  have hss₀ : s₀ + 2 ≤ s := by
    by_contra hc
    have h1 := slotStart_mono S (show s ≤ s₀ + 1 by omega)
    have h2 := supportCutoff_eq S (s₀ + 1)
    have h3 := voteTime_eq S (s₀ + 1)
    omega
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, s = q + 2 := ⟨s - 2, by omega⟩
  obtain ⟨ip, hl, hsent⟩ := hPropose
  have hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (q + 2)) (S.P.proposer (q + 2))).S.T,
      B'.root ≠ B.root := fun B' hB' h => hNoCollision ⟨B', hB', h⟩
  have hChain' : ConfirmationsChainBefore S Sched x s₀ (q + 1) := by
    rwa [show q + 2 - 1 = q + 1 by omega] at hChain
  have hLk : ∀ u ∈ honestActiveAt S Sched q,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (q + 1)) q u :=
    locks_before_of_locks_le S Sched x s₀ q (fun s' h1 h2 => hLocks s' h1 (by omega)) hLocks₀
      (by omega)
  obtain ⟨hBefore, -, -, hHCE, hSaved, hUpd, -⟩ :=
    honest_proposal_saved_until_upTo S Sched x GST s₀ anchor i₁ H q ip B hDiv hMono hSync hCatch
      hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST hChain' hInv hLocks hOld hCaches ht₀
      (by omega) hs hLk hp hl hsent hRootNew
  exact ⟨fun σ D hD hσ => onHonestChainAt_ancestorEq_of_le hBefore hSaved hD hσ, hSaved, hHCE,
    fun v hv => (hUpd v hv).2.2⟩

/-! ## Lemma 99, the first six clauses -/

/-- **Lemma 99, the first six clauses of the hand-over facts.** The proof; the audited statement is
in `Statements/Executions/AsyncHandoverStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold; `s`: the hand-over slot;
  `B`: its proposal. -/
theorem handoverFacts_six_of_healed_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H s : ℕ) (B : Block V)
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
    (hFrames : ∀ w ∈ honestActiveAt S Sched (s + 1), VoterFrameOnChainAt S Sched x s₀ (s + 1) w)
    (hs : x[i₁].time < slotStart S s)
    (hp : ∀ t : ℕ, proposalWindowStart S s ≤ t → t ≤ supportCutoff S (s + 1) →
      S.P.proposer s ∈ Sched.awake (t : Int) ∧ S.P.proposer s ∉ Sched.adv (t : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hNoCollision : ¬ RootCollisionAtProposal S Sched x s B) :
    H < (chainStateOf S.C B).h ∧
    (∀ w ∈ updaterAt S Sched s,
      (stateBefore x (supportCutoff S (s + 1) + 1) w).A.saved_confirmation s = some B ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) w).A.latest_confirmed = B ∧
      HolderInvAt S Sched x s B (stepBefore x (supportCutoff S (s + 1) + 1)) w) ∧
    (∀ (j : ℕ) (u : V), x[j].time = supportCutoff S (s + 1) → u ∉ Sched.adv (x[j].time : Int) →
      CachesCompatibleWith S B H (x[j][u].st)) ∧
    CertificatesCompatibleWithAtOfChainBlock S Sched x H B
      (stepBefore x (supportCutoff S (s + 1) + 1)) ∧
    AttestationsCompatibleWithBeforeOfHeldEntry S Sched x B H (supportCutoff S (s₀ + 1))
      (stepBefore x (supportCutoff S (s + 1) + 1)) ∧
    (∀ b₀ b₁ : ℕ, VotesExtendAt S Sched x s B b₀ b₁ (s + 1)) := by
  have hΔ := one_le_Δ S
  -- the facts at slot `s`
  obtain ⟨hle, hSaved, hHCE, hRev⟩ := handover_chain_of_healed_upTo S Sched x GST s₀ anchor i₁ H
    s B hDiv hMono hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST ht₀ hChain
    hInv hLocks hLocks₀ hOld hCaches hs hp hPropose hNoCollision
  -- the times
  have hv1 := voteTime_eq S (s + 1)
  have hc1 := supportCutoff_eq S (s + 1)
  have hss1 := slotStart_mono S (show s ≤ s + 1 by omega)
  have hss₀ : s₀ ≤ s := by
    by_contra hc
    have h1 := slotStart_mono S (show s ≤ s₀ by omega)
    have h2 := supportCutoff_eq S (s₀ + 1)
    have h3 := voteTime_eq S (s₀ + 1)
    have h4 := slotStart_mono S (show s₀ ≤ s₀ + 1 by omega)
    omega
  obtain ⟨-, hj₀t, -⟩ := stepBefore_spec x hDiv (show 1 ≤ supportCutoff S (s + 1) + 1 by omega)
  have hj₀c : x[stepBefore x (supportCutoff S (s + 1) + 1)].time = supportCutoff S (s + 1) := by
    omega
  have hRj₀ : RootsNameBlocksUntil S Sched x x[stepBefore x (supportCutoff S (s + 1) + 1)].time := by
    rw [hj₀c]; exact hRoots
  have hi₁c : x[i₁].time ≤ supportCutoff S (s + 1) := by omega
  -- an updater of slot `s`
  have hanchor : anchor ≤ slotStart S (s + 1) := by omega
  have hK := hSleepK (s + 1) (by omega) hanchor
  rw [Nat.add_sub_cancel] at hK
  obtain ⟨u₀, hu₀⟩ : ∃ u : V, u ∈ honestActiveAt S Sched s ∩ S.P.committee s := by
    have hpos : 0 < (honestActiveAt S Sched s ∩ S.P.committee s).card := by omega
    exact Finset.card_pos.1 hpos
  have hu₀U : u₀ ∈ updaterAt S Sched s :=
    Statements.Executions.honestActiveAt_subset_updaterAt S Sched s (Finset.mem_inter.1 hu₀).1
  -- the caches at the step right after the hand-over update are on `B`'s chain
  have hAgree := Statements.Executions.lem82_honest_attestations_on_chain S Sched x s₀ hDiv hMono
  have hJ : ∀ u : V, u ∉ Sched.adv ((supportCutoff S (s + 1) : ℕ) : Int) →
      CachesOnChain S Sched x s₀ H (x[stepBefore x (supportCutoff S (s + 1) + 1)][u].st) ∧
        (x[stepBefore x (supportCutoff S (s + 1) + 1)][u].st).S.J.AncestorEq B := by
    intro u hu
    have hu' : u ∉ Sched.adv (x[stepBefore x (supportCutoff S (s + 1) + 1)].time : Int) := by
      rw [hj₀c]; exact hu
    have hC := hCaches _ u (by rw [hj₀c]; exact hi₁c) (le_of_eq hj₀c) hu'
    obtain ⟨σ, hσ, hJσ⟩ := justified_onHonestChainAt_of_caches S Sched x s₀
      (supportCutoff S (s₀ + 1)) H _ u hU hMono hRj₀ hAdvQ hAgree hOld hu' hC.1
    rw [hj₀c] at hσ
    exact ⟨hC, hle σ _ hJσ ((slot_le_of_supportCutoff_lt S σ s).2.2 hσ)⟩
  -- the caches after every step read as the cutoff, of a validator honest at the cutoff
  have hJs : ∀ (j : ℕ) (u : V), x[j].time = supportCutoff S (s + 1) →
      u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st) ∧ (x[j][u].st).S.J.AncestorEq B := by
    intro j u hjc hu'
    have hRj : RootsNameBlocksUntil S Sched x x[j].time := by rw [hjc]; exact hRoots
    have hC := hCaches j u (by rw [hjc]; exact hi₁c) (le_of_eq hjc) hu'
    obtain ⟨σ, hσ, hJσ⟩ := justified_onHonestChainAt_of_caches S Sched x s₀
      (supportCutoff S (s₀ + 1)) H _ u hU hMono hRj hAdvQ hAgree hOld hu' hC.1
    rw [hjc] at hσ
    exact ⟨hC, hle σ _ hJσ ((slot_le_of_supportCutoff_lt S σ s).2.2 hσ)⟩
  -- clause 1: `H < h(B)`
  have hcl1 : H < (chainStateOf S.C B).h := by
    obtain ⟨hC, hJB⟩ := hJ u₀ (Finset.mem_sdiff.1 hu₀U).2
    have h1 := hC.1
    have h2 := hC.2.2.2.1
    have h3 := chainStateOf_height_mono S.C hJB
    omega_nat
  -- clause 2: the lock holders
  have hcl2 : ∀ w ∈ updaterAt S Sched s,
      (stateBefore x (supportCutoff S (s + 1) + 1) w).A.saved_confirmation s = some B ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) w).A.latest_confirmed = B ∧
      HolderInvAt S Sched x s B (stepBefore x (supportCutoff S (s + 1) + 1)) w := by
    intro w hw
    obtain ⟨A', hUpd, hSv, -, hLE, hLive, hLC, hSt1, -, hSt3, hSt4⟩ :=
      Statements.Executions.lem90_included_update_facts_until_upTo S Sched x GST s₀ anchor i₁ H s
        B w hDiv hMono hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST ht₀
        hChain hInv hLocks hLocks₀ hOld hCaches hs hp hPropose hNoCollision hw
    have hSaved' : (stateBefore x (supportCutoff S (s + 1) + 1) w).A.saved_confirmation s =
        some B := by rw [hSt1]; exact hSv
    refine ⟨hSaved', by rw [hSt4]; exact hLC, Or.inl ?_, ?_, ?_, ?_, ?_⟩
    · show _ ∈ (stateBefore x (supportCutoff S (s + 1) + 1) w).A.lock_entries
      rw [hSt3]
      exact hLE
    · show B.AncestorEq (stateBefore x (supportCutoff S (s + 1) + 1) w).A.latest_confirmed
      rw [hSt4, hLC]
      exact ancestorEq_refl B
    · exact latest_confirmed_mem_T_of_exec x _ w
    · intro D hD
      exact (compatible_iff D B).2 (Or.inl (fast_blocks_ancestorEq_saved_of_updater S Sched x s w B
        hDiv hMono hw hSaved' D hD))
    · intro e he hlive
      have he' : e ∈ A'.lock_entries := by
        have : e ∈ (stateBefore x (supportCutoff S (s + 1) + 1) w).A.lock_entries := he
        rwa [hSt3] at this
      -- the step of the tick at the hand-over update, and the one before it
      obtain ⟨-, hkt, -⟩ := stepBefore_spec x hDiv (show 1 ≤ supportCutoff S (s + 1) by omega)
      have hkj : stepBefore x (supportCutoff S (s + 1)) ≤
          stepBefore x (supportCutoff S (s + 1) + 1) := by
        by_contra hc
        have := time_mono x (show stepBefore x (supportCutoff S (s + 1) + 1) ≤
          stepBefore x (supportCutoff S (s + 1)) by omega)
        omega
      -- `e`'s block is held before the tick
      have heT : e.B ∈ (stateBefore x (supportCutoff S (s + 1)) w).S.T := by
        rcases (GoldilocksCorrectness.Proofs.Routines.update_confirmation_in_frame S.C S.P _ A'
            _ _ _ hUpd).2.2.1 e he' with h | ⟨h, -⟩
        · exact lock_entry_mem_T_of_exec S Sched x w _ e (Finset.mem_filter.1 h).1
        · exact ((mem_fg_to_ac_tree _ _).1 h).1
      have hFF := F_ancestorEq_of_le x w hkj
      simp only [is_live_iff] at hlive
      have hlive' : is_live (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) w).S)
          ((supportCutoff S (s + 1) : ℕ) : Int) e = true := by
        simp only [is_live_iff]
        refine ⟨by rw [hj₀c] at hlive; exact hlive.1, (mem_fg_to_ac_tree _ _).2 ⟨heT, ?_⟩⟩
        exact ancestorEq_trans hFF ((mem_fg_to_ac_tree _ _).1 hlive.2).2
      exact (compatible_iff _ _).2 (Or.inl (hLive e he' hlive'))
  -- clause 3: the caches
  have hcl3 : ∀ (j : ℕ) (u : V), x[j].time = supportCutoff S (s + 1) →
      u ∉ Sched.adv (x[j].time : Int) → CachesCompatibleWith S B H (x[j][u].st) := by
    intro j u hjc hu
    obtain ⟨hC, hJB⟩ := hJs j u hjc hu
    exact ⟨hC.1, Or.inl hJB, hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2⟩
  -- clause 5: the attestations
  have hcl5 : AttestationsCompatibleWithBeforeOfHeldEntry S Sched x B H (supportCutoff S (s₀ + 1))
      (stepBefore x (supportCutoff S (s + 1) + 1)) := by
    intro i t v a hi hl' hAw hHon hsent'
    have htt := time_of_lbl_tickAllAwake x hl'
    have htc : t ≤ supportCutoff S (s + 1) := by
      have := time_mono x (show i + 1 ≤ stepBefore x (supportCutoff S (s + 1) + 1) by omega)
      omega
    refine ⟨fun ht => hOld i t v a hl' ht hAw hHon hsent', fun ht => ?_⟩
    obtain ⟨s', E, C, hs₀s', ht', hv', hsv, hEC, hEe, hEh, hEr⟩ :=
      Statements.Executions.lem82b_entry_at_slot S Sched x s₀ i t v a hDiv hMono hl' ht hAw hHon
        hsent'
    have hOn : OnHonestChainAt S Sched x s₀ s' E := ⟨hs₀s', v, hv', C, hsv, hEC⟩
    have hs's : s' ≤ s := (slot_le_of_supportCutoff_lt S s' s).2.2 (by rw [← ht']; exact htc)
    exact ⟨E, Or.inl (hle s' E hOn hs's), hEe, hEh, hEr,
      onHonestChainAt_inHonestTreeBy S Sched x hMono s₀ s' t E hOn (le_of_eq ht'.symm)⟩
  -- clause 4: the certificates, from the attestations
  have hcl4 : CertificatesCompatibleWithAtOfChainBlock S Sched x H B
      (stepBefore x (supportCutoff S (s + 1) + 1)) :=
    certificatesCompatibleWithAtOfChainBlock_of_attestations S Sched x _ hU hRj₀ (hAdvQ _) hcl5
  -- clause 6: the votes of slot `s + 1`
  have hGSTs : GST ≤ voteTime S s := by
    have h1 := voteTime_eq S s₀
    have h2 := voteTime_eq S s
    have h3 := slotStart_mono S hss₀
    omega
  have hkey : ∀ w ∈ honestActiveAt S Sched (s + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
        (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_w ∈ (stateBefore x (voteTime S (s + 1)) w).S.T,
        vote = GoldfishVote.mk w (s + 1) H_w.root ∧ B.AncestorEq H_w := by
    intro w hw vote hSend
    obtain ⟨Hf, hHf⟩ := exists_votes_on_chain S Sched x s
      (honestActiveAt S Sched s ∩ S.P.committee s) B hDiv hMono subset_rfl
      (fun u hu => hHCE.1 u (Finset.mem_inter.1 hu).1)
    have hwU := updaterAt_of_honestActiveAt_succ S Sched s w hMono hw
    have hBchain : OnHonestChainBefore S Sched x s₀ (s + 1) B :=
      ⟨s, Nat.lt_succ_self s, hss₀, u₀, hu₀U, B, hSaved u₀ hu₀U, ancestorEq_refl B⟩
    obtain ⟨hF2, hF3⟩ := hFrames w hw B hBchain
    have hwin := honestActiveAt_window S Sched (s + 1) w hMono hw
    have hdw := dutyWindowStart_succ_le_slotStart S s
    have hvs := voteTime_eq S s
    have hcs := supportCutoff_mono S (show s ≤ s + 1 + 1 by omega)
    exact Statements.Executions.lem26b_goldfish_vote_extends_voter_majority_block_held_upTo S
      Sched x GST s _ Hf B w vote hDiv hMono hSync hCatch
      (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner hGSTs
      (fun u hu => by
        obtain ⟨hK', hadv, hsnd, hT, hBH⟩ := hHf u hu
        refine ⟨hK', fun h => hadv (hMono _ _ ?_ h), hsnd, hT, hBH⟩
        exact_mod_cast (by omega : voteTime S (s + 1) ≤ supportCutoff S (s + 1)))
      (Statements.Executions.lem88_counting_of_committeeSleepiness S Sched x anchor s w
        (voteTime S (s + 1)) hSleepK hanchor).2.2
      (fun t h1 h2 => hwin t (by omega) (by omega)) hF2 hF3
      (fun A' hA' e he hl => (compatible_iff _ _).2 (Or.inl (hRev w hwU A' hA' e he hl))) hSend
  have hcl6 : ∀ b₀ b₁ : ℕ, VotesExtendAt S Sched x s B b₀ b₁ (s + 1) := fun _ _ =>
    ⟨fun u hu vote hsend => hkey u (Finset.mem_inter.1 hu).2 vote hsend,
      fun _ u hu vote hsend => hkey u hu vote hsend⟩
  exact ⟨hcl1, hcl2, hcl3, hcl4, hcl5, hcl6⟩

/-! ## Lemma 99, the confirmed tips from `x[i₁].time` on -/

/-- **Lemma 99, the confirmed tips read from `x[i₁].time` to the hand-over update.** The proof; the
audited statement is in `Statements/Executions/AsyncHandoverStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold; `s`: the hand-over slot;
  `B`: its proposal. -/
theorem confirmed_tips_preceq_handover_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H s : ℕ) (B : Block V)
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
    (hLatest : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ supportCutoff S (s + 1) →
      u ∉ Sched.adv (x[j].time : Int) → (∃ σ : ℕ, supportCutoff S (σ + 1) ≤ x[j].time ∧
        OnHonestChainAt S Sched x s₀ σ (x[j][u].st).A.latest_confirmed) ∧
        (x[j][u].st).A.latest_confirmed ∈ (x[j][u].st).S.T)
    (hs : x[i₁].time < slotStart S s)
    (hp : ∀ t : ℕ, proposalWindowStart S s ≤ t → t ≤ supportCutoff S (s + 1) →
      S.P.proposer s ∈ Sched.awake (t : Int) ∧ S.P.proposer s ∉ Sched.adv (t : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hNoCollision : ¬ RootCollisionAtProposal S Sched x s B) :
    ∀ (v : V) (T : ℕ) (P : Block V), HonestThrough x T v → x[i₁].time ≤ x[T].time →
      x[T].time ≤ supportCutoff S (s + 1) →
      P.AncestorEq (confirmedOf (x[T][v].st)) → P.AncestorEq B := by
  obtain ⟨hle, -, -, -⟩ := handover_chain_of_healed_upTo S Sched x GST s₀ anchor i₁ H s B hDiv hMono
    hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST ht₀ hChain hInv hLocks
    hLocks₀ hOld hCaches hs hp hPropose hNoCollision
  intro v T P hv hT1 hT2 hP
  have hvT : v ∉ Sched.adv (x[T].time : Int) := hv _ le_rfl
  obtain ⟨σ, hσ, hOn⟩ := confirmedOf_onHonestChainAt S Sched x s₀ H T v hDiv hMono
    (hRoots.mono hT2) hU hAdvQ hOld hvT (hLatest T v hT1 hT2 hvT).1 (hCaches T v hT1 hT2 hvT)
  exact ancestorEq_trans hP
    (hle σ _ hOn ((slot_le_of_supportCutoff_lt S σ s).2.2 (le_trans hσ hT2)))

end GoldilocksCorrectness.Proofs.Executions
