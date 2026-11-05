module
public import GoldilocksCorrectness.Statements.Executions.FinalityLivenessDefs
public import GoldilocksCorrectness.Statements.Executions.FinalityLivenessKitStatements
public import GoldilocksCorrectness.Statements.Executions.HealedAttestationStatements
public import GoldilocksCorrectness.Statements.Executions.FrameShapeStatements
public import GoldilocksCorrectness.Proofs.Executions.FinalityLivenessKit
public import GoldilocksCorrectness.Proofs.Executions.Lemma90Inclusion
public import GoldilocksCorrectness.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Proofs.Executions.Lemma79
public import GoldilocksCorrectness.Proofs.Routines.Schedule

@[expose] public section

/-!
# The round's members after healing: their frame at the action time, and their targets

The part of the route of Lemma 94 that holds, as kit
theorems:

- `no_honest_timeout_after_healing_before`: `no_honest_timeout_after_healing` with the honest chain
  read only before a slot `n`, for an attestation sent at a time at most the support cutoff of
  slot `n`;
- `round_member_frame_after_healing`: for an honest round opening slot `s` after the hand-over and
  its proposal `B` with no root collision, every member of `honestActiveAt S Sched s` updates slot
  `s + 1` saving `B` fast, keeps its live locks on `B`'s chain, and before the support cutoff of
  slot `s + 1` holds `B`, has its fork-choice root on `B`'s chain, its `head_height_floor` at most
  `B`'s height, and its record at `B`'s height clean of a lock on another block;
- `round_attesters_target_after_healing`: every such member puts on the wire, at a tick at a time at
  most that support cutoff, a target at `B`'s height naming the root of `B`'s `T_h`.

Lemma 94's clause on the finality pair (the target carries `(h_j(B), J(B))` when
`h_F(B) < h_j(B)`) is not here: it is false as probed: a descendant of `B` of slot `s + 1` that the adversary
completes to a justification at `B`'s height, or to a finalization at `h_j(B)`, with honest
attestations of an earlier round, is the head the member's duty reads at the action time, and the
finality pair is then dropped.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono dutyWindowStart_succ_le_slotStart
  one_le_Δ slotStart_eq slot_after_healed_round slot_le_of_supportCutoff_lt
  slot_lt_of_supportCutoff_le supportCutoff_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed HeightCacheBounds)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks FrameShape lem66_chain_state_certified
  lem67_first_advance RecordConsistent)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  create_attestation_timeout)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## No honest timeout, on the chain before a slot -/

/-- **`no_honest_timeout_after_healing` on the chain before a slot.** The statement of
`no_honest_timeout_after_healing` (`Statements/Executions/FinalityLivenessKitStatements.lean`) with
the honest confirmations forming a chain only before the slot `n`
(`ConfirmationsChainBefore S Sched x s₀ n`), for an attestation sent at a time `t` at most the
support cutoff of slot `n`.

Why: the proof of `no_honest_timeout_after_healing`; the two attestations it compares are sent at
times at most `t`, at the support cutoff of slot `s' + 1` for the slot `s'` of the entry Lemma 82
names, so every such `s'` is less than `n`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the bound
  on the heights of the honest attestations sent before the healed round's action time; `n`: the
  bound on the slots of the chain;
- `i`: the step; `t`: its time; `v`: the validator; `a`: the attestation. -/
theorem no_honest_timeout_after_healing_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H n i t : ℕ) (v : V) (a : Attestation V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hChain : ConfirmationsChainBefore S Sched x s₀ n)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hl : x.lbl i = AtomicAction.tickAllAwake t) (ht₀ : supportCutoff S (s₀ + 1) ≤ t)
    (htn : t ≤ supportCutoff S n)
    (hAwake : v ∈ Sched.awake (t : Int)) (hHon : v ∉ Sched.adv (t : Int))
    (hSent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent)
    (hH : H < a.h) :
    a.τ = false := by
  have hAgree := lem82_honest_attestations_on_chain S Sched x s₀ hDiv hMono
  induction i using Nat.strong_induction_on generalizing t a with
  | _ i ih =>
  by_contra hτ
  have hτ' : a.τ = true := by simpa using hτ
  -- the attestation is the one the client built from the validator's record
  obtain ⟨-, n', sent, hrun, ha⟩ := tick_send_of_honestSendAt hl hSent
  obtain ⟨-, fi, source, -, -, hca, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem49_tick_attests S.C S.P S.X _ n' _ sent a hrun ha
  obtain ⟨hah, haT, hcase⟩ := create_attestation_timeout _ _ _ _ _ _ _ a hca hτ'
  rw [tickInputState_Λ] at hcase
  have hΛ : RecordConsistent (x[i][v].st).Λ := recordConsistent_of_exec S Sched x i v
  have hti := (time_of_lbl_tickAllAwake x hl).1
  rcases hcase with htimeout | ⟨T', htarget, hne⟩
  · -- a timeout at the attestation's height was sent earlier, at a tick
    obtain ⟨c, hc, hch, hcτ⟩ := (hΛ.timeoutRec _).1 htimeout
    obtain ⟨j, t', a', hj, hl', hAw', hHon', hsent', -, hcont, -⟩ :=
      record_content_sent_step S Sched x v i c hc
    have ht'le : t' ≤ t := by
      have h1 := (time_of_lbl_tickAllAwake x hl').2
      have h2 := time_mono x (show j + 1 ≤ i by omega)
      omega
    have hh' : a'.h = a.h := by
      rw [hah, ← hch]; exact congrArg AttestationContent.h hcont
    have hτa' : a'.τ = true := by
      rw [← hcτ]; exact congrArg AttestationContent.τ hcont
    rcases Nat.lt_or_ge t' (supportCutoff S (s₀ + 1)) with hlt | hge
    · have hle := hOld j t' v a' hl' hlt hAw' hHon' hsent'
      rw [hh'] at hle
      exact absurd hle (Nat.not_le.mpr hH)
    · have := ih j hj t' a' hl' hge (le_trans ht'le htn) hAw' hHon' hsent'
        (by rw [hh']; exact hH)
      rw [hτa'] at this
      cases this
  · -- a target at the attestation's height for another block was sent earlier, at a tick
    obtain ⟨c, hc, hch, hcτ, hcT⟩ := (hΛ.targetRec _ _).1 htarget
    obtain ⟨j, t', a', hj, hl', hAw', hHon', hsent', -, hcont, -⟩ :=
      record_content_sent_step S Sched x v i c hc
    have ht'le : t' ≤ t := by
      have h1 := (time_of_lbl_tickAllAwake x hl').2
      have h2 := time_mono x (show j + 1 ≤ i by omega)
      omega
    have hh' : a'.h = a.h := by
      rw [hah, ← hch]; exact congrArg AttestationContent.h hcont
    have hT' : a'.T = T' := by
      rw [← hcT]; exact congrArg AttestationContent.T hcont
    rcases Nat.lt_or_ge t' (supportCutoff S (s₀ + 1)) with hlt | hge
    · have hle := hOld j t' v a' hl' hlt hAw' hHon' hsent'
      rw [hh'] at hle
      exact absurd hle (Nat.not_le.mpr hH)
    · -- both attestations name the honest chain's entry at the height (Lemma 82)
      obtain ⟨s, E, -, hts, hE1, hE2, hE3, hE4⟩ := hAgree i t v a hl ht₀ hAwake hHon hSent
      obtain ⟨s', E', -, hts', hE1', hE2', hE3', hE4'⟩ :=
        hAgree j t' v a' hl' hge hAw' hHon' hsent'
      have hsn : s < n := slot_lt_of_supportCutoff_le S (hts ▸ htn)
      have hs'n : s' < n := slot_lt_of_supportCutoff_le S (hts' ▸ le_trans ht'le htn)
      -- two entries of the honest chain before `n` at one height are one block
      have hEE : E = E' := by
        have hheq : (chainStateOf S.C E).h = (chainStateOf S.C E').h := by rw [hE3, hE3', hh']
        exact entry_eq_of_onHonestChainBefore S Sched x s₀ n E E' hChain ⟨s, hsn, hE1⟩
          ⟨s', hs'n, hE1'⟩ hE2 hE2' hheq
      apply hne
      rw [← hT', hE4', ← hEE, ← hE4, haT]

/-! ## The round's members: the frame at the action time -/

/-- **Kit theorem, the frame of a member of the round at its action time.** For an honest round
opening slot `s` after the hand-over step `i₂` whose proposer's tick put `B` on the wire, with no
block the proposer held before `t_s` having `B`'s root, and a member `u` of
`honestActiveAt S Sched s`: every block on the honest chain before slot `s` is `B` or an ancestor
of `B`; `B` is of slot `s`; every updater of slot `s` saves `B` as its confirmation of slot `s`;
`H < h(B)`; `u`'s update of slot `s + 1` at the support cutoff `a` of slot `s + 1` answers some
`A'` saving `B` with `B` among its fast blocks; every lock entry `u`'s revocation of slot `s + 1`
leaves live is compatible with `B`; and on `u`'s state before `a`: the fork-choice root is `B` or
an ancestor of `B`, `head_height_floor` is at most `h(B)`, `B` is in the tree, and the cache `h_j`
is less than `h(B)`, or the record holds no lock at `h(B)`, or its lock there is the root of
`T_h(B)`.

Why: the inclusion (`honest_proposal_saved_until`, `included_update_facts_q_until`,
`honest_proposal_extends_chain_until`) gives the chain, the update and the root. The FG state of
`u` before `a` is not contested (Lemma 91 (d)), so its `head_height_floor` (the least chain-state height a viable block may have) is `h_max − 1`; a block at `h_max`
with `h_max − 1 > h(B)` would carry a progress certificate at `h_max − 1 > H` naming an entry of
the chain before slot `s` (`cert_entry_at_slot`), an ancestor of `B` of greater height. A lock at
`h(B) = h_j` was written by a finality pair `u` signed from a chain state of a block it held with
that justification (`lock_justified_of_exec`); its certificate names an entry of the chain before
`s` at `h(B)` (Lemma 83), which is `T_h(B)` (Lemma 47 (e)).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `s`: the slot; `B`: the proposal; `u`: the member. -/
theorem round_member_frame_after_healing (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₂ H s : ℕ) (B : Block V) (u : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₂].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₂].time)
    (hChain : ConfirmationsChainBefore S Sched x s₀ s)
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ w ∈ honestActiveAt S Sched s',
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (w : V), x[i₂].time ≤ x[j].time → x[j].time ≤ supportCutoff S (s + 1) →
      w ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][w].st))
    (hAfter : x[i₂].time < slotStart S s)
    (hOpener : HonestOpenerAt S Sched s)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hNoCollision : ¬ RootCollisionAtProposal S Sched x s B)
    (hu : u ∈ honestActiveAt S Sched s) :
    (∀ C : Block V, OnHonestChainBefore S Sched x s₀ s C → C.AncestorEq B) ∧
    B.slot = s ∧
    (∀ w ∈ updaterAt S Sched s,
      (stateBefore x (supportCutoff S (s + 1) + 1) w).A.saved_confirmation s = some B) ∧
    H < (chainStateOf S.C B).h ∧
    (∃ A' : ACState V,
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) u).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) u).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A' ∧
      A'.saved_confirmation s = some B ∧ B ∈ A'.fast_blocks) ∧
    (∀ A'' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) u).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) u).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A'' →
      ∀ e ∈ A''.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) u).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true) ∧
    (get_fc_root (stateBefore x (supportCutoff S (s + 1)) u).S).AncestorEq B ∧
    head_height_floor (stateBefore x (supportCutoff S (s + 1)) u).S ≤ (chainStateOf S.C B).h ∧
    B ∈ (stateBefore x (supportCutoff S (s + 1)) u).S.T ∧
    ((stateBefore x (supportCutoff S (s + 1)) u).S.h_j < (chainStateOf S.C B).h ∨
      (stateBefore x (supportCutoff S (s + 1)) u).Λ.lock (chainStateOf S.C B).h = none ∨
      (stateBefore x (supportCutoff S (s + 1)) u).Λ.lock (chainStateOf S.C B).h =
        some (chainStateOf S.C B).T_h.root) := by
  obtain ⟨hs2, -, -⟩ := slot_after_healed_round S s₀ s (lt_of_le_of_lt ht₀ hAfter)
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  obtain ⟨ip, hl, hsent⟩ := hPropose
  have hΔ := one_le_Δ S
  have hc3 := supportCutoff_eq S (q + 2 + 1)
  have hv3 := voteTime_eq S (q + 2 + 1)
  have hv2 := voteTime_eq S (q + 2)
  have hss : slotStart S (q + 2 + 1) = slotStart S (q + 2) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (q + 2), Nat.mul_add, Nat.mul_one]
  have hLk := locks_before_of_locks_le S Sched x s₀ q (fun s' h₁ h₂ => hLocks s' h₁ (by omega))
    hLocks₀ (by omega)
  have hChainq : ConfirmationsChainBefore S Sched x s₀ (q + 1) :=
    fun a b c d e f h1 h2 h3 => hChain a b c d e f h1 h2 (by omega)
  have hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (q + 2)) (S.P.proposer (q + 2))).S.T,
      B'.root ≠ B.root := fun B' hB' hr => hNoCollision ⟨B', hB', hr⟩
  obtain ⟨hChainB, hBslot, -, -, hSavedAll, hFrame, -⟩ := honest_proposal_saved_until S Sched x GST
    s₀ anchor i₂ H q ip B hDiv hMono hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK hAnchor
    hGST hChainq hInv hLocks hOld hCaches ht₀ (by omega) hAfter hLk hOpener hl hsent hRootNew
  have hu' : u ∈ updaterAt S Sched (q + 2) := honestActiveAt_subset_updaterAt S Sched (q + 2) hu
  obtain ⟨A', hUpd, hSv, hFb, -⟩ := included_update_facts_q_until S Sched x GST s₀ anchor i₂ H q ip
    B u hDiv hMono hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST hChainq hInv
    hLocks hOld hCaches ht₀ (by omega) hAfter hLk hOpener hl hsent hRootNew hu'
  obtain ⟨hFu, hρu, hRev⟩ := hFrame u hu'
  -- `u` holds `B` before the action time
  have hBin : B ∈ (stateBefore x (supportCutoff S (q + 2 + 1)) u).S.T := by
    obtain ⟨-, -, -, -, -, hHold⟩ := honest_proposal_extends_chain_until S Sched x GST s₀ anchor i₂
      H q ip B hDiv hMono hSync hCatch (hRoots.mono (by omega)) hParent hOwner hU hAdvQ hSleepK
      hAnchor hGST hChainq (fun s' h₁ h₂ => hInv s' h₁ (by omega))
      (fun s' h₁ h₂ => hLocks s' h₁ (by omega)) hOld
      (fun j w h₁ h₂ h₃ => hCaches j w h₁ (by omega) h₃) ht₀ (by omega) hAfter hLk
      hOpener hl hsent hRootNew
    exact (stateBefore_grows x hDiv u (show voteTime S (q + 2) ≤ supportCutoff S (q + 2 + 1) by
      omega)).1 (hHold u hu)
  -- the step before the action time
  have h1 : 1 ≤ supportCutoff S (q + 2 + 1) := by omega
  set j := stepBefore x (supportCutoff S (q + 2 + 1)) with hjdef
  have htj : x[j].time + 1 = supportCutoff S (q + 2 + 1) := time_stepBefore_add_one x hDiv h1
  have hst : stateBefore x (supportCutoff S (q + 2 + 1)) u = x[j][u].st := rfl
  have huw := honestActiveAt_window S Sched (q + 2) u hMono hu
  have hdw : dutyWindowStart S (q + 2) ≤ slotStart S (q + 1) :=
    dutyWindowStart_succ_le_slotStart S (q + 1)
  have hss1 : slotStart S (q + 2) = slotStart S (q + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (q + 1), show q + 2 = (q + 1) + 1 from rfl, Nat.mul_add,
      Nat.mul_one]
  have huc : u ∉ Sched.adv ((supportCutoff S (q + 2 + 1) : ℕ) : Int) :=
    (huw _ (by omega) le_rfl).2
  have huj : u ∉ Sched.adv (x[j].time : Int) := fun h => huc (hMono _ _ (by omega) h)
  have hij : x[i₂].time ≤ x[j].time := by omega
  have hd := lem91d_not_contested_until S Sched x s₀ i₂ j (q + 2) H u hDiv hMono hU hAdvQ hChain
    hOld (fun j' w h₁ h₂ h₃ => hCaches j' w h₁ (by omega) h₃) hij huj
    (fun s_a h => (slot_le_of_supportCutoff_lt S s_a (q + 2)).2.1 (by omega))
  -- the caches of `u` and a witness of its justification
  obtain ⟨hHu, -, -, -, -⟩ := hCaches j u hij (by omega) huj
  obtain ⟨⟨D, hD, -, hDj⟩, ⟨X, hX, hXh⟩, -⟩ := cachesWitnessed_of_exec S Sched x j u
  have hCS : ChainStatesComputed S.C (x[j][u].st).S :=
    (lem11_node_invariant S Sched x j u).1.2.2.2.2.2.1
  have hCB : HeightCacheBounds (x[j][u].st).S := (lem46_finality_caches S Sched x j u).2
  have hDh : (chainStateOf S.C D).h ≤ (x[j][u].st).S.h_max := by
    rw [← hCS D hD]
    exact hCB D hD
  have hD47 := (lem47_chain_state_heights S.C D D).1.2.1
  have hjm : (x[j][u].st).S.h_j + 1 ≤ (x[j][u].st).S.h_max := by
    rw [hDj]
    omega_nat
  -- the floor is at most `h(B)`
  have hfloor : (x[j][u].st).S.h_max - 1 ≤ (chainStateOf S.C B).h := by
    by_contra hgt
    have hH1 : H < (x[j][u].st).S.h_max - 1 := by omega_nat
    obtain ⟨Y, hYX, -, -, -, -, hPC⟩ := lem67_first_advance S.C X ((x[j][u].st).S.h_max - 1)
      (by omega_nat) (by rw [hXh]; omega_nat)
    have hYT : Y ∈ (x[j][u].st).S.T := ancestors_mem_T_of_exec S Sched x j u X Y hX hYX
    obtain ⟨s_a, E, hcut, hAt, -, hEh, -⟩ := cert_entry_at_slot S Sched x s₀ H j u Y _ _ hDiv
      hMono hU (hAdvQ _) hOld hYT hPC hH1
    have hsa : s_a < q + 2 := (slot_le_of_supportCutoff_lt S s_a (q + 2)).2.1 (by omega)
    have hEB := hChainB E ⟨s_a, hsa, hAt⟩
    have := (lem47_chain_state_heights S.C E B).2.2.2.1 hEB
    rw [hEh] at this
    exact hgt this
  have hφ : head_height_floor (x[j][u].st).S ≤ (chainStateOf S.C B).h := by
    rw [hd.2]; exact hfloor
  have hHB : H < (chainStateOf S.C B).h := by omega_nat
  refine ⟨hChainB, hBslot, hSavedAll, hHB, ⟨A', hUpd, hSv, hFb⟩,
    fun A'' hrev e he hlive => (compatible_iff _ _).2 (Or.inl (hRev A'' hrev e he hlive)), hρu,
    by rw [hst]; exact hφ, hBin, ?_⟩
  rw [hst]
  -- the record at `h(B)`
  by_cases hlt : (x[j][u].st).S.h_j < (chainStateOf S.C B).h
  · exact Or.inl hlt
  right
  have hjB : (x[j][u].st).S.h_j = (chainStateOf S.C B).h := by omega_nat
  cases hlk : (x[j][u].st).Λ.lock (chainStateOf S.C B).h with
  | none => exact Or.inl rfl
  | some T' =>
    right
    obtain ⟨j', hj', D', hD'T, h1', hD'j, hD'J⟩ := lock_justified_of_exec S Sched x j u _ T' hlk
    have hcert := ((lem66_chain_state_certified S.C D').1 (hD'j ▸ h1')).1
    rw [hD'j] at hcert
    obtain ⟨s_a, E, hcut, hAt, hEe, hEh, hEr⟩ :=
      lem83_one_justification_greater_than_threshold S Sched x s₀ (supportCutoff S (s₀ + 1)) H j'
        u D' _ _ hU (hAdvQ _) (lem82_honest_attestations_on_chain S Sched x s₀ hDiv hMono)
        (oldAttestationsAtMostHonestAt_of_oldAttestationsAtMost S Sched x _ _ H hOld) hD'T hcert
        hHB
    have hj'j : x[j'].time ≤ x[j].time := time_mono x (Nat.le_of_lt hj')
    have hsa : s_a < q + 2 := (slot_le_of_supportCutoff_lt S s_a (q + 2)).2.1 (by omega)
    have hEB := hChainB E ⟨s_a, hsa, hAt⟩
    have hTE : (chainStateOf S.C E).T_h = (chainStateOf S.C B).T_h :=
      (lem47_chain_state_heights S.C E B).2.2.2.2 hEB hEh
    unfold IsEntry at hEe
    rw [← hD'J, hEr, ← hEe, hTE]

/-! ## The round's members: their targets -/

/-- **Kit theorem, the round's members' targets after healing (the part of Lemma 94 that holds).**
For an honest round opening slot `s = r * R` after the hand-over step `i₂` whose proposer's tick put
`B` on the wire, with no block the proposer held before `t_s` having `B`'s root, every member `u` of
`honestActiveAt S Sched s` put on the wire, at a tick at a time at most the support cutoff of slot
`s + 1`, a target of its own at `B`'s height naming the root of `B`'s `T_h`.

Why: Lemma 61 over the frame of `round_member_frame_after_healing`: `u` attests at the action time,
or its record already holds an attestation at `h(B)` naming `T_h(B)`, sent at an earlier tick
(`record_content_sent`); either is a target, since `h(B) > H`
(`no_honest_timeout_after_healing_before`, the attestations read being sent at times at most the
support cutoff of slot `s + 1`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the round; `s`: its first slot; `B`: the proposal; `u`: the member. -/
theorem round_attesters_target_after_healing (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₂ H r s : ℕ) (B : Block V) (u : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₂].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₂].time)
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s + 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ w ∈ honestActiveAt S Sched s',
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (w : V), x[i₂].time ≤ x[j].time → x[j].time ≤ supportCutoff S (s + 1) →
      w ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][w].st))
    (hs : s = r * S.C.R) (hAfter : x[i₂].time < slotStart S s)
    (hOpener : HonestOpenerAt S Sched s)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hNoCollision : ¬ RootCollisionAtProposal S Sched x s B)
    (hu : u ∈ honestActiveAt S Sched s) :
    ∃ (i t : ℕ) (a : Attestation V), x.lbl i = AtomicAction.tickAllAwake t ∧
      t ≤ supportCutoff S (s + 1) ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent ∧
      a.val_index = u ∧ a.h = (chainStateOf S.C B).h ∧ a.T = (chainStateOf S.C B).T_h.root ∧
      a.τ = false := by
  have hChain' : ConfirmationsChainBefore S Sched x s₀ s :=
    fun a b c d e f h1 h2 h3 => hChain a b c d e f h1 h2 (by omega)
  obtain ⟨-, hBslot, -, hHB, ⟨A', hUpd, hSv, hFb⟩, hRev, hρ, hφ, hBin, hBox⟩ :=
    round_member_frame_after_healing S Sched x GST s₀ anchor i₂ H s B u hDiv hMono hSync hCatch
      hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST ht₀ hChain' hInv hLocks hLocks₀ hOld
      hCaches hAfter hOpener hPropose hNoCollision hu
  have hΔ := one_le_Δ S
  have hdw : dutyWindowStart S s ≤ dutyWindowStart S (s + 1) := dutyWindowStart_mono S (by omega)
  have hdw' : dutyWindowStart S (s + 1) ≤ slotStart S s := dutyWindowStart_succ_le_slotStart S s
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S s, Nat.mul_add, Nat.mul_one]
  have hc1 := supportCutoff_eq S (s + 1)
  have hv1 := voteTime_eq S (s + 1)
  have hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int) := fun t h1 h2 =>
    honestActiveAt_window S Sched s u hMono hu t (le_trans hdw h1) h2
  have hLk := update_lock_entries_ancestorEq S Sched x s B u A' hDiv hMono hv hUpd hSv hBslot hRev
  -- every attestation of `u` at `h(B)` up to the support cutoff of slot `s + 1` is a target
  have hτ : ∀ (j t' : ℕ) (a : Attestation V), x.lbl j = AtomicAction.tickAllAwake t' →
      t' ≤ supportCutoff S (s + 1) → u ∈ Sched.awake (t' : Int) → u ∉ Sched.adv (t' : Int) →
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[j + 1].sent - x[j].sent →
      a.h = (chainStateOf S.C B).h → a.τ = false := by
    intro j t' a hl ht' haw hhon hsent hah
    rcases Nat.lt_or_ge t' (supportCutoff S (s₀ + 1)) with hlt | hge
    · have := hOld j t' u a hl hlt haw hhon hsent
      rw [hah] at this
      exact absurd this (Nat.not_le.mpr hHB)
    · exact no_honest_timeout_after_healing_before S Sched x s₀ H (s + 1) j t' u a hDiv hMono
        hChain hOld hl hge ht' haw hhon hsent (by rw [hah]; exact hHB)
  rcases lem61_honest_validator_attests_frame S Sched x r s B u A' _ _ hDiv hMono hs hv hUpd hSv
      hFb hLk ⟨rfl, rfl⟩ hρ hφ hBin hBox with ⟨i, a, hl, hsent, hav, hah, haT⟩ | ⟨b, hb, hbh, hbT⟩
  · have hw := hv _ (by omega) le_rfl
    exact ⟨i, _, a, hl, le_rfl, hsent, hav, hah, haT, hτ i _ a hl le_rfl hw.1 hw.2 hsent hah⟩
  · obtain ⟨j, t', a, hl, ht', hawk, hadv, hsent, hav, hac, -⟩ :=
      record_content_sent S Sched x _ u b hDiv hb
    have hah : a.h = (chainStateOf S.C B).h := by
      rw [← hbh, ← hac]
      rfl
    have haT : a.T = (chainStateOf S.C B).T_h.root := by
      rw [← hbT, ← hac]
      rfl
    exact ⟨j, t', a, hl, ht'.le, hsent, hav, hah, haT, hτ j t' a hl ht'.le hawk hadv hsent hah⟩

end GoldilocksCorrectness.Proofs.Executions
