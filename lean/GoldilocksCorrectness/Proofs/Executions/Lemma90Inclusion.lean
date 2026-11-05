module
public import GoldilocksCorrectness.Proofs.View.Bridges
public import GoldilocksCorrectness.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Proofs.Routines.Lemma77
public import GoldilocksCorrectness.Proofs.Executions.Lemma78
public import GoldilocksCorrectness.Proofs.Executions.Lemma90
public import GoldilocksCorrectness.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Proofs.Executions.Sleepy
public import GoldilocksCorrectness.Proofs.Executions.ProposalWalk
public import GoldilocksCorrectness.Statements.Executions.OrderedFloorStatements
public import GoldilocksCorrectness.Statements.Executions.PhaseKitStatements
public import GoldilocksCorrectness.Statements.Executions.FrameShapeStatements
public import GoldilocksCorrectness.Statements.Executions.FastConfirmationStatements
public import GoldilocksCorrectness.Statements.Executions.ProposalPropagationStatements
public import GoldilocksCorrectness.Statements.Executions.SleepyStatements
public import GoldilocksCorrectness.Statements.Executions.HealedFrameStatements
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Proofs.Routines.Node

@[expose] public section

/-!
# Lemma 90, inclusion: the honest proposal is confirmed after healing

The proofs of `lem90_included_update_facts` and `lem90_confirmed_included`, stated in
`GoldilocksCorrectness/Statements/Executions/ConfirmedTipStatements.lean`, both with the lock
invariant at the healed slot itself (`hLocks₀`).

Write `p` for the proposer of the slot `s = q + 2` and `B` for its proposal. The route:

1. the proposal exists (`honest_proposer_proposes`);
2. the proposer's root and anchor are on the chain before `q + 1`, so the proposal's parent extends
   every block of that chain (`honest_proposal_extends_chain`);
3. every honest vote of slot `q + 2` names `B` (Lemma 59 with ordered `head_height_floor` values (the least chain-state height a viable block may have), Lemma 91);
4. every updater of slot `q + 2` saves `B`, fast and locked (Lemmas 27 and 60);
5. its record and its confirmed tip are `B` (`latest_confirmed_after_healed_update`);
6. at every later slot an honest active validator's update saves a descendant of `B`
   (`updater_saves_after_healing`), and the confirmed tip only grows (Lemma 90, growth).

Step 2 reads, at the slot `s = s₀ + 2`, the lock invariant at the healed slot `s₀` (the
proposer's anchor may be a block locked by an entry its revocation of slot `s₀ + 1` left), which
`hLocks` gives only from slot `s₀ + 1` on. Both statements take it as `hLocks₀`, which
`base_locks_on_chain` derives from Lemma 81's premises.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart
  proposalWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  dutyWindowStart_succ_le_slotStart one_le_Δ proposalWindowStart_eq proposal_window_start_eq
  slotStart_cast slotStart_eq slotStart_mono slot_after_healed_round slot_eq_of_mem
  slot_le_of_supportCutoff_lt supportCutoff_cast supportCutoff_eq supportCutoff_lt_of_lt
  voteTime_cast voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes
  fg_to_ac_F is_live_iff mem_viable_tree_iff pool_of_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines
open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

end GoldilocksCorrectness.Proofs.Routines

namespace GoldilocksCorrectness.Proofs.Executions

open GoldilocksCorrectness.Proofs.Routines (tick_emits_proposal)
open GoldilocksCorrectness.Statements.Routines (confirmedOf)

open GoldilocksCorrectness.Proofs.Routines (ac_on_tick_emits_vote get_anchor_cases_live_lock get_anchor_mem_T)

open GoldilocksCorrectness.Proofs.Routines (fc_root_eq mem_fg_to_ac_tree)
open GoldilocksCorrectness.Statements.Routines (JustifiedInTree)

open GoldilocksCorrectness.Proofs.Routines (DREBEmits DREBEmits.bind DREBEmits.ite DREBEmits.pure lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf chainStateOf)

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks ProposalCountedVotes FrameShape
  lem67_first_advance lem56_frame_of_shape)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_of_parent? awake_since_record_awake deepest?_mem update_confirmation_latest_cases
  advance_some ac_confirmed_cases)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

omit [RootOrder] in
/-- The support cutoff grows with the slot: `supportCutoff_mono` of `Lemma89f.lean`, which this file
does not import (the forms on the chain before a slot read it).

The variables:
- `S`: the setup; `a ≤ b`: the two slots. -/
private theorem supportCutoff_le_of_le (S : Setup V) {a b : ℕ} (h : a ≤ b) :
    supportCutoff S a ≤ supportCutoff S b := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · exact le_of_lt (supportCutoff_lt_of_lt S h)
  · rw [h]

/-! ## Step 1: the proposal -/

/-- **Kit fact, an honest proposer proposes.** When the proposer of slot `q + 2` is awake and
honest from the start of the proposal window of slot `q + 2` to its start, its tick at the start of
slot `q + 2` puts a block on the wire.

Why: the tick answers (`ticksSucceed_of_exec`), the proposer has been awake since the duty window's
start of slot `q + 1`, which is the proposal window's start, so the proposal test passes, and the
proposal sends its block (`tick_emits_proposal`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `q`: the slot is `q + 2`. -/
theorem honest_proposer_proposes (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (q : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hp : ∀ t : ℕ, proposalWindowStart S (q + 2) ≤ t → t ≤ slotStart S (q + 2) →
      S.P.proposer (q + 2) ∈ Sched.awake (t : Int) ∧ S.P.proposer (q + 2) ∉ Sched.adv (t : Int)) :
    ∃ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S (q + 2)) ∧
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent := by
  have hΔ := one_le_Δ S
  have hss : slotStart S (q + 2) = slotStart S (q + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (q + 1), show q + 2 = (q + 1) + 1 from rfl, Nat.mul_add,
      Nat.mul_one]
  have hss' : slotStart S (q + 2 + 1) = slotStart S (q + 2) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (q + 2), Nat.mul_add, Nat.mul_one]
  have hdw := dutyWindowStart_succ_le_slotStart S q
  have hsq : slotStart S q ≤ slotStart S (q + 1) := slotStart_mono S (Nat.le_succ q)
  have hslot : S.C.slot ((slotStart S (q + 2) : ℕ) : Int) = q + 2 :=
    slot_eq_of_mem S le_rfl (by omega)
  have h1 : 1 ≤ slotStart S (q + 2) := by omega
  set p := S.P.proposer (q + 2) with hpdef
  have hl := (stepBefore_spec x hDiv h1).1
  have hpw := proposalWindowStart_eq S q
  have hvA := (hp (slotStart S (q + 2)) (by omega) le_rfl).1
  have hHon := (hp (slotStart S (q + 2)) (by omega) le_rfl).2
  obtain ⟨n', sent, hrun, -⟩ := tick_step_outcome x hl hvA hHon
  obtain ⟨τ, hτ, hτle⟩ := awakeSince_le_dutyWindowStart_b S Sched x (q + 1) (slotStart S (q + 2))
    p hDiv hMono (by omega) (fun t' h1 h2 => (hp t' (by omega) h2).1) hHon
  have hnv : (tickInputState x (stepBefore x (slotStart S (q + 2))) (slotStart S (q + 2)) p).v =
      p := by
    have h := (lem11_node_invariant S Sched x (stepBefore x (slotStart S (q + 2))) p).2.1
    unfold tickInputState
    split <;> (try rw [wake_eq]) <;> exact h
  have hL := (tick_emits_proposal S.C S.P S.X _ _).of_outcome hrun
  obtain ⟨B, hB⟩ := hL (by rw [hslot]; exact Nat.succ_pos _) (by rw [hslot]; exact slotStart_cast S (q + 2))
    (by rw [hnv, hslot])
    (awake_since_record_awake hτ (by rw [hslot, proposal_window_start_eq]; exact hτle))
  exact ⟨_, B, hl, step_sent_of_tick_send hl (Finset.mem_sdiff.2 ⟨hvA, hHon⟩) hrun hB⟩


/-! ## The proposer's frame on the chain -/

/-- The root of the fork choice of `u`'s state before `t` is on the honest chain before slot `q`,
when `t` is after `x[i₁].time` and at most the support cutoff of slot `q + 1`, and `u` is honest at
`t`: Lemma 91 (f) at the step before `t`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `q`: the slot;
  `i₁`: the step at the phase's end; `H`: the threshold; `t`: the time; `u`: the validator.

Roots name blocks until `t`: Lemma 91 (f) at the step before `t` compares blocks held by then.

Caches up to `t`: Lemma 91 (f) at the step before `t` reads `u`'s caches there. -/
theorem proposer_root_on_chain_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ q i₁ H t : ℕ) (u : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x t) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ t →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (ht1 : x[i₁].time < t) (ht2 : t ≤ supportCutoff S (q + 1))
    (hu : u ∉ Sched.adv (t : Int)) :
    OnHonestChainBefore S Sched x s₀ q (fg_to_ac (stateBefore x t u).S).fc_root := by
  have h1t : 1 ≤ t := by omega
  have htj := time_stepBefore_add_one x hDiv h1t
  have hst : stateBefore x t u = x[stepBefore x t][u].st := rfl
  rw [hst]
  refine lem91f_voter_root_on_chain_before_until S Sched x s₀ i₁ (stepBefore x t) q H u hDiv hMono
    (hRoots.mono (by omega))
    hU hAdvQ hOld (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃) (by omega)
    (fun h => hu (hMono _ _ (by omega) h)) ?_
  intro s_a hs_a
  exact (slot_le_of_supportCutoff_lt S s_a q).2.1 (by omega)

/-- The root of the fork choice of `u`'s state before `t` is on the honest chain before slot `q`,
when `t` is after `x[i₁].time` and at most the support cutoff of slot `q + 1`, and `u` is honest at
`t`: Lemma 91 (f) at the step before `t`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `q`: the slot;
  `i₁`: the step at the phase's end; `H`: the threshold; `t`: the time; `u`: the validator.

Roots name blocks until `t`: Lemma 91 (f) at the step before `t` compares blocks held by then.

It is `proposer_root_on_chain_until` with the caches restricted to the steps it reads. -/
theorem proposer_root_on_chain (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ q i₁ H t : ℕ) (u : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x t) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (ht1 : x[i₁].time < t) (ht2 : t ≤ supportCutoff S (q + 1))
    (hu : u ∉ Sched.adv (t : Int)) :
    OnHonestChainBefore S Sched x s₀ q (fg_to_ac (stateBefore x t u).S).fc_root :=
  proposer_root_on_chain_until S Sched x s₀ q i₁ H t u hDiv hMono hRoots hU hAdvQ hOld (fun j u h₁
    _ h₂ => hCaches j u h₁ h₂) ht1 ht2 hu

/-- **Kit fact, the proposer's anchor is on the chain.** The anchor of the proposer `p` of slot
`q + 2` at the start of that slot is on the honest chain before slot `q + 1`, when `p` is an honest
active validator of slot `q + 1` and the lock invariant holds at slot `q` for the chain before
`q + 1` (`hLk`).

Why: the anchor is the root of the fork choice (Lemma 91 (f)) or an ancestor of the block of a live
lock entry. Such an entry is on `p`'s confirmation of slot `q` or an ancestor of it, or on an
ancestor of an entry `p`'s revocation of slot `q + 1` left live (`live_lock_entry_source`); the
latter is on the chain by `hLk` when `p` is an honest active validator of slot `q`, and there is
none when `p` slept before (`lock_free_after_wake`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `q`: the slot
  of the proposal is `q + 2`; `i₁`: the step at the phase's end; `H`: the threshold; `p`: the
  proposer.

Roots name blocks until `slotStart S (q + 2)`: the root of the proposer's fork choice before the
start of slot `q + 2` (`proposer_root_on_chain`).

Caches up to `slotStart S (q + 2)`: the proposer's caches before the start of slot `q + 2`
(`proposer_root_on_chain_until`). -/
theorem proposer_anchor_on_chain_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ q i₁ H : ℕ) (p : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x (slotStart S (q + 2)))
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ slotStart S (q + 2) →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hs₀q : s₀ ≤ q) (hs : x[i₁].time < slotStart S (q + 2))
    (hpA : p ∈ honestActiveAt S Sched (q + 1))
    (hLk : ∀ u ∈ honestActiveAt S Sched q,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (q + 1)) q u) :
    OnHonestChainBefore S Sched x s₀ (q + 1)
      (get_anchor (stateBefore x (slotStart S (q + 2)) p).A
        (fg_to_ac (stateBefore x (slotStart S (q + 2)) p).S) ((slotStart S (q + 2) : ℕ) : Int)) := by
  have hΔ := one_le_Δ S
  have hss : slotStart S (q + 2) = slotStart S (q + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (q + 1), show q + 2 = (q + 1) + 1 from rfl, Nat.mul_add,
      Nat.mul_one]
  have hv2 := voteTime_eq S (q + 2)
  have hv1 := voteTime_eq S (q + 1)
  have hc1 := supportCutoff_eq S (q + 1)
  have hc2 := supportCutoff_eq S (q + 2)
  have hw := honestActiveAt_window S Sched (q + 1) p hMono hpA
  have hdw := dutyWindowStart_succ_le_slotStart S q
  have hc2b := supportCutoff_eq S (q + 1 + 1)
  have hv2b := voteTime_eq S (q + 1 + 1)
  have hss2 : slotStart S (q + 1 + 1) = slotStart S (q + 2) := rfl
  have hsq : slotStart S q ≤ slotStart S (q + 1) := slotStart_mono S (Nat.le_succ q)
  have hpt : p ∉ Sched.adv ((slotStart S (q + 2) : ℕ) : Int) :=
    (hw (slotStart S (q + 2)) (by omega) (by omega)).2
  have hroot := proposer_root_on_chain_until S Sched x s₀ (q + 1) i₁ H (slotStart S (q + 2)) p hDiv
    hMono hRoots hU hAdvQ hOld hCaches hs (by omega) hpt
  rcases get_anchor_cases_live_lock (stateBefore x (slotStart S (q + 2)) p).A
      (fg_to_ac (stateBefore x (slotStart S (q + 2)) p).S) ((slotStart S (q + 2) : ℕ) : Int) with
    h | ⟨e, he, hlive, hae⟩
  · rw [h]; exact hroot
  · have hdl : ((slotStart S (q + 2) : ℕ) : Int) < e.d := by
      rw [is_live_iff] at hlive
      exact hlive.1
    rcases live_lock_entry_source S Sched x q (slotStart S (q + 2)) p hDiv
        (fun t'' h1 h2 => hw t'' (le_trans (dutyWindowStart_mono S (by omega)) h1) (by omega)) (by omega) (by omega) e he hdl with
      ⟨C', hC', heC⟩ | ⟨A₃, hrev, e', he', hlive', hee'⟩
    · exact onHonestChainBefore_of_ancestorEq S Sched x s₀ (q + 1)
        ⟨q, Nat.lt_succ_self q, hs₀q, p, honestActiveAt_succ_subset_updaterAt S Sched q hMono hpA,
          C', hC', ancestorEq_refl C'⟩ (ancestorEq_trans hae heC)
    · rcases mem_honestActiveAt_or_slept S Sched q p hMono hpA with hpq | hslept
      · obtain ⟨D, hD, he'D⟩ := hLk p hpq A₃ hrev e' he' hlive'
        exact onHonestChainBefore_of_ancestorEq S Sched x s₀ (q + 1) hD
          (ancestorEq_trans hae (ancestorEq_trans hee' he'D))
      · exact (revoke_locks_empty_of_lockFree S Sched x (voteTime S (q + 1)) (q + 1) p A₃
          (Nat.le_add_left 1 q) (lock_free_after_wake S Sched x q p hDiv hMono hslept) hrev e'
          he').elim

/-- **Kit fact, the proposer's anchor is on the chain.** The anchor of the proposer `p` of slot
`q + 2` at the start of that slot is on the honest chain before slot `q + 1`, when `p` is an honest
active validator of slot `q + 1` and the lock invariant holds at slot `q` for the chain before
`q + 1` (`hLk`).

Why: the anchor is the root of the fork choice (Lemma 91 (f)) or an ancestor of the block of a live
lock entry. Such an entry is on `p`'s confirmation of slot `q` or an ancestor of it, or on an
ancestor of an entry `p`'s revocation of slot `q + 1` left live (`live_lock_entry_source`); the
latter is on the chain by `hLk` when `p` is an honest active validator of slot `q`, and there is
none when `p` slept before (`lock_free_after_wake`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `q`: the slot
  of the proposal is `q + 2`; `i₁`: the step at the phase's end; `H`: the threshold; `p`: the
  proposer.

Roots name blocks until `slotStart S (q + 2)`: the root of the proposer's fork choice before the
start of slot `q + 2` (`proposer_root_on_chain`).

It is `proposer_anchor_on_chain_until` with the caches restricted to the steps it reads. -/
theorem proposer_anchor_on_chain (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ q i₁ H : ℕ) (p : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x (slotStart S (q + 2)))
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hs₀q : s₀ ≤ q) (hs : x[i₁].time < slotStart S (q + 2))
    (hpA : p ∈ honestActiveAt S Sched (q + 1))
    (hLk : ∀ u ∈ honestActiveAt S Sched q,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (q + 1)) q u) :
    OnHonestChainBefore S Sched x s₀ (q + 1)
      (get_anchor (stateBefore x (slotStart S (q + 2)) p).A
        (fg_to_ac (stateBefore x (slotStart S (q + 2)) p).S) ((slotStart S (q + 2) : ℕ) : Int)) :=
  proposer_anchor_on_chain_until S Sched x s₀ q i₁ H p hDiv hMono hRoots hU hAdvQ hOld (fun
    j u h₁ _ h₂ => hCaches j u h₁ h₂) hs₀q hs hpA hLk

/-- The first clause of the chain invariant at slot `r`, as a function: some `H` names, for every
honest active committee member `u` of slot `r`, the block of `u`'s slot-`r` vote, held by `u`, of
which every block of the chain before `r` is an ancestor or which it is.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `r`: the slot;
  `C₀`: a block of the chain before `r`. -/
theorem chain_votes_of_inv (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ r : ℕ) (C₀ : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hInv : ChainInvFor S Sched x (honestActiveAt S Sched r) (OnHonestChainBefore S Sched x s₀ r) r)
    (hC₀ : OnHonestChainBefore S Sched x s₀ r C₀) :
    ∃ H : V → Block V, ∀ u ∈ honestActiveAt S Sched r ∩ S.P.committee r,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S r) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u r (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S r) u).S.T ∧
      ∀ C : Block V, OnHonestChainBefore S Sched x s₀ r C → C.AncestorEq (H u) := by
  obtain ⟨H, hH⟩ := voters_of_votes_clause S Sched x r (honestActiveAt S Sched r ∩ S.P.committee r)
    C₀ hDiv hMono (fun u hu => Finset.mem_inter.1 hu)
    (fun u hu => (hInv C₀ hC₀).1 u (Finset.mem_inter.1 hu).1)
  refine ⟨H, fun u hu => ⟨(hH u hu).1, (hH u hu).2.1, fun C hC => ?_⟩⟩
  obtain ⟨H', hH'T, heq, hCH'⟩ := (hInv C hC).1 u (Finset.mem_inter.1 hu).1 _ (hH u hu).1
  have hroot : (H u).root = H'.root := by
    have := congrArg GoldfishVote.head heq
    exact this
  have hInvU := (lem11_node_invariant S Sched x (stepBefore x (voteTime S r)) u).1
  have hHH : H u = H' := hInvU.2.2.2.2.2.2.2.2.2.1.1 _ (hH u hu).2.1 _ hH'T hroot
  rw [hHH]
  exact hCH'

/-- After the phase's end, an honest validator's `h_max` is at least `H + 2`: its justification
height is more than `H` (`CachesOnChain`) and less than `h_max`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₁`: the step
  at the phase's end; `H`: the threshold; `j`: the step; `u`: the validator.

Caches up to `x[j].time`: the proof reads `u`'s caches at step `j` only. -/
theorem h_max_ge_of_caches_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ i₁ H j : ℕ) (u : V)
    (hCaches : ∀ (k : ℕ) (u : V), x[i₁].time ≤ x[k].time → x[k].time ≤ x[j].time →
      u ∉ Sched.adv (x[k].time : Int) → CachesOnChain S Sched x s₀ H (x[k][u].st))
    (hj : x[i₁].time ≤ x[j].time) (hu : u ∉ Sched.adv (x[j].time : Int)) :
    H + 2 ≤ (x[j][u].st).S.h_max := by
  obtain ⟨hHp, -, -, -, -⟩ := hCaches j u hj le_rfl hu
  obtain ⟨⟨Dp, hDp, -, hhjDp⟩, -, -⟩ := cachesWitnessed_of_exec S Sched x j u
  have hInvP := (lem11_node_invariant S Sched x j u).1
  have hDpm : (chainStateOf S.C Dp).h ≤ (x[j][u].st).S.h_max := by
    have := hInvP.2.2.2.2.2.2.2.2.2.1.2.1.2 Dp hDp
    rw [hInvP.2.2.2.2.2.1 Dp hDp] at this
    exact this
  have hjh := (lem47_chain_state_heights S.C Dp Dp).1.2.1
  rw [hhjDp] at hHp
  omega_nat

/-- After the phase's end, an honest validator's `h_max` is at least `H + 2`: its justification
height is more than `H` (`CachesOnChain`) and less than `h_max`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₁`: the step
  at the phase's end; `H`: the threshold; `j`: the step; `u`: the validator.

It is `h_max_ge_of_caches_until` with the caches restricted to the steps it reads. -/
theorem h_max_ge_of_caches (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ i₁ H j : ℕ) (u : V)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hj : x[i₁].time ≤ x[j].time) (hu : u ∉ Sched.adv (x[j].time : Int)) :
    H + 2 ≤ (x[j][u].st).S.h_max :=
  h_max_ge_of_caches_until S Sched x s₀ i₁ H j u (fun k u h₁ _ h₂ => hCaches k u h₁ h₂) hj hu

/-- The honest chain before slot `q + 1` has a block at the chain-state height `m − 1`, with `m`
the `h_max` of the proposer's state before the start of slot `q + 2`.

Why: the proposer holds a block at `m`; the block that raised its chain past `m − 1` carries a
certificate at `m − 1 > H`, and the certificate route names an entry of the chain at `m − 1`
confirmed at a slot `s_a` with `s_a + 2 ≤ q + 2`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `q`: the slot
  of the proposal is `q + 2`; `i₁`: the step at the phase's end; `H`: the threshold; `p`: the
  proposer.

Caches up to `slotStart S (q + 2)`: the proof reads `p`'s caches before the start of slot
`q + 2`. -/
theorem proposer_entry_on_chain_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ q i₁ H : ℕ) (p : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ slotStart S (q + 2) →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hs : x[i₁].time < slotStart S (q + 2))
    (hp : p ∉ Sched.adv ((slotStart S (q + 2) : ℕ) : Int)) :
    ∃ E : Block V, OnHonestChainBefore S Sched x s₀ (q + 1) E ∧
      (chainStateOf S.C E).h = (stateBefore x (slotStart S (q + 2)) p).S.h_max - 1 := by
  have hΔ := one_le_Δ S
  have hv2 := voteTime_eq S (q + 2)
  have hv2b := voteTime_eq S (q + 1 + 1)
  have hss2 : slotStart S (q + 1 + 1) = slotStart S (q + 2) := rfl
  have h1t : 1 ≤ slotStart S (q + 2) := by omega
  obtain ⟨jp, hjp⟩ : ∃ jp, jp = stepBefore x (slotStart S (q + 2)) := ⟨_, rfl⟩
  have htp : x[jp].time + 1 = slotStart S (q + 2) := by
    rw [hjp]; exact time_stepBefore_add_one x hDiv h1t
  have hstp : stateBefore x (slotStart S (q + 2)) p = x[jp][p].st := by
    unfold stateBefore; rw [hjp]
  have hpj : p ∉ Sched.adv (x[jp].time : Int) := fun h => hp (hMono _ _ (by omega) h)
  have hip : x[i₁].time ≤ x[jp].time := by omega
  have hm2 := h_max_ge_of_caches_until S Sched x s₀ i₁ H jp p
    (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃) hip
    hpj
  obtain ⟨-, ⟨Y, hY, hYh⟩, -⟩ := cachesWitnessed_of_exec S Sched x jp p
  rw [hstp]
  obtain ⟨Y₁, hY₁Y, -, -, -, -, hPC⟩ := lem67_first_advance S.C Y
    ((x[jp][p].st).S.h_max - 1) (by omega_nat) (by rw [hYh]; omega_nat)
  have hY₁T : Y₁ ∈ (x[jp][p].st).S.T := ancestors_mem_T_of_exec S Sched x jp p Y Y₁ hY hY₁Y
  obtain ⟨s_a, E, hcut, hAt, -, hEh, -⟩ := cert_entry_at_slot S Sched x s₀ H jp p Y₁ _ _ hDiv
    hMono hU (hAdvQ _) hOld hY₁T hPC (by omega_nat)
  have hsa := (slot_le_of_supportCutoff_lt S s_a (q + 2)).1 (by omega)
  exact ⟨E, ⟨s_a, by omega, hAt⟩, hEh⟩

/-- The honest chain before slot `q + 1` has a block at the chain-state height `m − 1`, with `m`
the `h_max` of the proposer's state before the start of slot `q + 2`.

Why: the proposer holds a block at `m`; the block that raised its chain past `m − 1` carries a
certificate at `m − 1 > H`, and the certificate route names an entry of the chain at `m − 1`
confirmed at a slot `s_a` with `s_a + 2 ≤ q + 2`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `q`: the slot
  of the proposal is `q + 2`; `i₁`: the step at the phase's end; `H`: the threshold; `p`: the
  proposer.

It is `proposer_entry_on_chain_until` with the caches restricted to the steps it reads. -/
theorem proposer_entry_on_chain (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ q i₁ H : ℕ) (p : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hs : x[i₁].time < slotStart S (q + 2))
    (hp : p ∉ Sched.adv ((slotStart S (q + 2) : ℕ) : Int)) :
    ∃ E : Block V, OnHonestChainBefore S Sched x s₀ (q + 1) E ∧
      (chainStateOf S.C E).h = (stateBefore x (slotStart S (q + 2)) p).S.h_max - 1 :=
  proposer_entry_on_chain_until S Sched x s₀ q i₁ H p hDiv hMono hU hAdvQ hOld (fun j u h₁ _ h₂ =>
    hCaches j u h₁ h₂) hs hp

/-! ## Steps 2 and 3: the parent and the votes -/

/-- **Steps 2 and 3 of the inclusion: the proposal's parent extends the chain, and every honest
vote names the proposal.** Under the hypotheses of the inclusion at slot `q + 2`, with the lock
invariant at slot `q` (`hLk`) and `B` the proposal of slot `q + 2` with a root new to its proposer:
every block of the chain before `q + 1` is `B`'s parent or an ancestor of it; `B` is a non-genesis
block of slot `q + 2`; every vote an honest active validator `w` of slot `q + 2` sends at the vote
time of slot `q + 2` names `B`; and every such `w` holds `B` before that vote time.

Why: the proposer's root and anchor are on the chain (Lemma 91 (f), `proposer_anchor_on_chain`);
every honest committee member of slot `q + 1` voted for a block extending the chain, which reaches
the proposer as a viable head; so the proposal's parent extends every block of the chain
(`proposal_parent_extends_majority_block`, `get_anchor_ancestorEq_proposal_parent`). Lemma 59 with
ordered `head_height_floor` values (`lem59le_goldfish_vote_names_honest_proposal_frame`) then names `B` in every
honest vote: the `head_height_floor` values are ordered by Lemma 91 (c) and (d), and `head_height_floor` at the voter is at most the
parent's height by Lemma 91 (b). Lemmas 22a and 22 deliver `B`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the
  proposal.

Roots name blocks until `voteTime S (q + 2)`: the proof reads the proposer's root and anchor
before the start of slot `q + 2`, the voters' roots and Lemmas 22, 59 (ordered `head_height_floor` values) and 91
(c) up to the vote time of slot `q + 2`.

Caches up to `voteTime S (q + 2)`: the proof reads the proposer's caches before the start of slot
`q + 2` and the voters' before the vote time of slot `q + 2` (Lemmas 91 (b), (c), (d) and (f)). -/
theorem honest_proposal_extends_chain_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S (q + 2)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀)
    (hChain : ConfirmationsChainBefore S Sched x s₀ (q + 1))
    (hInv : ∀ s : ℕ, s₀ < s → s ≤ q + 1 →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → s ≤ q + 1 → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ voteTime S (q + 2) →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (hs₀q : s₀ ≤ q) (hs : x[i₁].time < slotStart S (q + 2))
    (hLk : ∀ u ∈ honestActiveAt S Sched q,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (q + 1)) q u)
    (hp : ∀ t : ℕ, proposalWindowStart S (q + 2) ≤ t → t ≤ supportCutoff S (q + 3) →
      S.P.proposer (q + 2) ∈ Sched.awake (t : Int) ∧ S.P.proposer (q + 2) ∉ Sched.adv (t : Int))
    (hl : x.lbl ip = AtomicAction.tickAllAwake (slotStart S (q + 2)))
    (hsent : (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x[ip + 1].sent - x[ip].sent)
    (hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (q + 2)) (S.P.proposer (q + 2))).S.T,
      B'.root ≠ B.root) :
    (∀ C : Block V, OnHonestChainBefore S Sched x s₀ (q + 1) C → C.AncestorEq B.parent) ∧
    B.slot = q + 2 ∧ B ≠ Block.genesis ∧ B.parent.AncestorEq B ∧
    (∀ w ∈ honestActiveAt S Sched (q + 2), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (q + 2)) ∧
        (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) → vote.head = B.root) ∧
    (∀ w ∈ honestActiveAt S Sched (q + 2), B ∈ (stateBefore x (voteTime S (q + 2)) w).S.T) := by
  -- the times
  have hΔ := one_le_Δ S
  have hss : slotStart S (q + 2) = slotStart S (q + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (q + 1), show q + 2 = (q + 1) + 1 from rfl, Nat.mul_add,
      Nat.mul_one]
  have hss' : slotStart S (q + 1) = slotStart S q + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S q, Nat.mul_add, Nat.mul_one]
  have hv2 := voteTime_eq S (q + 2)
  have hv1 := voteTime_eq S (q + 1)
  have hv0 := voteTime_eq S s₀
  have hc1 := supportCutoff_eq S (q + 1)
  have hc2 := supportCutoff_eq S (q + 2)
  have hc3 := supportCutoff_eq S (q + 3)
  have hv3 := voteTime_eq S (q + 3)
  have hss3 : slotStart S (q + 3) = slotStart S (q + 2) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (q + 2), show q + 3 = (q + 2) + 1 from rfl, Nat.mul_add,
      Nat.mul_one]
  have hss2 : slotStart S (q + 1 + 1) = slotStart S (q + 2) := rfl
  have hvb : voteTime S (q + 1 + 1) = voteTime S (q + 2) := rfl
  have hcb : supportCutoff S (q + 1 + 1) = supportCutoff S (q + 2) := rfl
  have hcb' : supportCutoff S (q + 2 + 1) = supportCutoff S (q + 3) := rfl
  have hdwb : dutyWindowStart S (q + 1 + 1) = dutyWindowStart S (q + 2) := rfl
  have hvb' : voteTime S (q + 2 + 1) = voteTime S (q + 3) := rfl
  have hssb' : slotStart S (q + 2 + 1) = slotStart S (q + 3) := rfl
  have hcb'' : supportCutoff S (q + 1 + 1 + 1) = supportCutoff S (q + 3) := rfl
  have hvb'' : voteTime S (q + 1 + 1 + 1) = voteTime S (q + 3) := rfl
  have hdw1 := dutyWindowStart_succ_le_slotStart S q
  have hdw2 := dutyWindowStart_succ_le_slotStart S (q + 1)
  have hsq0 : slotStart S s₀ ≤ slotStart S q := slotStart_mono S hs₀q
  have hpw := proposalWindowStart_eq S q
  set p := S.P.proposer (q + 2) with hpdef
  -- the proposer's window
  have hp' : ∀ t : ℕ, dutyWindowStart S (q + 1) ≤ t → t ≤ supportCutoff S (q + 3) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int) := fun t h1 h2 =>
    hp t (by rw [hpw]; exact h1) h2
  have hpA : p ∈ honestActiveAt S Sched (q + 1) := by
    refine Finset.mem_sdiff.2 ⟨mem_awakeThroughout_of_forall (fun t h1 h2 =>
      (hp' t h1 (by omega)).1), (hp' (supportCutoff S (q + 1 + 1)) (by omega) (by omega)).2⟩
  have hpt : p ∉ Sched.adv ((slotStart S (q + 2) : ℕ) : Int) :=
    (hp' (slotStart S (q + 2)) (by omega) (by omega)).2
  -- the chain before `q + 1`, and what is on it
  have hρp := proposer_root_on_chain_until S Sched x s₀ (q + 1) i₁ H (slotStart S (q + 2)) p hDiv
    hMono (hRoots.mono (by omega)) hU hAdvQ hOld
    (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃) hs (by omega) hpt
  have hap := proposer_anchor_on_chain_until S Sched x s₀ q i₁ H p hDiv hMono
    (hRoots.mono (by omega)) hU hAdvQ
    hOld (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃) hs₀q hs hpA hLk
  obtain ⟨Hf, hHf⟩ := chain_votes_of_inv S Sched x s₀ (q + 1) _ hDiv hMono
    (hInv (q + 1) (by omega) le_rfl) hρp
  obtain ⟨E, hE, hEh⟩ := proposer_entry_on_chain_until S Sched x s₀ q i₁ H p hDiv hMono hU hAdvQ
    hOld (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃) hs hpt
  have h88 := lem88_counting_of_committeeSleepiness S Sched x anchor (q + 1) p
    (slotStart S (q + 2)) hSleepK (by omega)
  obtain ⟨u₀, hu₀⟩ : (honestActiveAt S Sched (q + 1) ∩ S.P.committee (q + 1)).Nonempty :=
    Finset.card_pos.1 (by omega)
  -- the proposer's frame
  have h1p : 1 ≤ slotStart S (q + 2) := by omega
  have htjp := time_stepBefore_add_one x hDiv h1p
  have hpjp : p ∉ Sched.adv (x[stepBefore x (slotStart S (q + 2))].time : Int) :=
    fun h => hpt (hMono _ _ (by omega) h)
  have hφp : head_height_floor (stateBefore x (slotStart S (q + 2)) p).S =
      (stateBefore x (slotStart S (q + 2)) p).S.h_max - 1 :=
    (lem91d_not_contested_until S Sched x s₀ i₁ (stepBefore x (slotStart S (q + 2))) (q + 1) H p
      hDiv hMono hU hAdvQ hChain hOld
      (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃)
      (by omega) hpjp (fun s_a h => by
        have := (slot_le_of_supportCutoff_lt S s_a (q + 2)).1
          (by have := voteTime_eq S (q + 2); omega)
        omega)).2
  have hInvP := (lem11_node_invariant S Sched x (stepBefore x (slotStart S (q + 2))) p).1
  have hFρp : (stateBefore x (slotStart S (q + 2)) p).S.F.AncestorEq
      (get_fc_root (stateBefore x (slotStart S (q + 2)) p).S) :=
    F_ancestorEq_fc_root_of_stateBefore S Sched x _ p
  rw [fc_root_eq] at hρp
  -- every voter's block reaches the proposer, as a viable head
  have hHp : ∀ u ∈ honestActiveAt S Sched (q + 1) ∩ S.P.committee (q + 1),
      Hf u ∈ (stateBefore x (slotStart S (q + 2)) p).S.T := by
    intro u hu
    obtain ⟨-, hT, hCH⟩ := hHf u hu
    have huw := honestActiveAt_window S Sched (q + 1) u hMono (Finset.mem_inter.1 hu).1
    have hu1 : u ∉ Sched.adv ((voteTime S (q + 1) : ℕ) : Int) :=
      (huw (voteTime S (q + 1)) (by omega) (by omega)).2
    have hgr := stateBefore_grows x hDiv p (show voteTime S (q + 1) + Δ S ≤ slotStart S (q + 2) by
      omega)
    have hmem := mem_T_before_add_delay hDiv hMono hSync hCatch (hRoots.mono (by omega))
      hParent
      (t := voteTime S (q + 1)) (u := u) (w := p) (by omega) (by omega) hu1 hT
      (fun t' h1 h2 => hp' t' (by omega) (by omega))
      ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hgr.2.1
        (ancestorEq_trans hFρp (hCH _ hρp)))))
    exact hgr.1 hmem
  have hHv : ∀ u ∈ honestActiveAt S Sched (q + 1) ∩ S.P.committee (q + 1),
      Hf u ∈ (fg_to_ac (stateBefore x (slotStart S (q + 2)) p).S).tree ∧
      Hf u ∈ (fg_to_ac (stateBefore x (slotStart S (q + 2)) p).S).viable_heads ∧
      head_height_floor (stateBefore x (slotStart S (q + 2)) p).S ≤ (chainStateOf S.C (Hf u)).h := by
    intro u hu
    have hT := hHp u hu
    have hCH := (hHf u hu).2.2
    have hFH := ancestorEq_trans hFρp (hCH _ hρp)
    have hφ : head_height_floor (stateBefore x (slotStart S (q + 2)) p).S ≤
        (chainStateOf S.C (Hf u)).h := by
      rw [hφp, ← hEh]
      exact (lem47_chain_state_heights S.C E (Hf u)).2.2.2.1 (hCH E hE)
    refine ⟨(mem_fg_to_ac_tree _ _).2 ⟨hT, hFH⟩, ((lem56_frame_of_shape _ _ _ ⟨rfl, rfl⟩).2.2
      (Hf u)).2 ⟨hT, hFH, hCH _ hρp, ?_⟩, hφ⟩
    have hσ : (stateBefore x (slotStart S (q + 2)) p).S.σ (Hf u) = chainStateOf S.C (Hf u) :=
      hInvP.2.2.2.2.2.1 (Hf u) hT
    rw [hσ]
    exact hφ
  -- the proposal's parent extends every block of the chain before `q + 1`
  have hPE : ∀ X : Block V, OnHonestChainBefore S Sched x s₀ (q + 1) X →
      (get_anchor (stateBefore x (slotStart S (q + 1 + 1)) p).A
        (fg_to_ac (stateBefore x (slotStart S (q + 1 + 1)) p).S)
        ((slotStart S (q + 1 + 1) : ℕ) : Int)).AncestorEq X →
      X.AncestorEq B.parent ∧ B.slot = q + 1 + 1 ∧ B ≠ Block.genesis ∧
      B.parent? = some B.parent ∧
      (B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (q + 1 + 1)) p).S)
          (fg_to_ac (stateBefore x (slotStart S (q + 1 + 1)) p).S).tree ∨
        B.parent = get_anchor (stateBefore x (slotStart S (q + 1 + 1)) p).A
          (fg_to_ac (stateBefore x (slotStart S (q + 1 + 1)) p).S)
          ((slotStart S (q + 1 + 1) : ℕ) : Int)) := by
    intro X hX haX
    obtain ⟨-, hT₀, -⟩ := hHf u₀ hu₀
    exact proposal_parent_extends_majority_block S Sched x GST (q + 1) ip
      (honestActiveAt S Sched (q + 1) ∩ S.P.committee (q + 1)) Hf X B p hDiv hMono hSync hCatch
      (hRoots.mono (by omega)) hParent hOwner (by omega)
      (fun u hu => ⟨(Finset.mem_inter.1 hu).2,
        ((honestActiveAt_window S Sched (q + 1) u hMono (Finset.mem_inter.1 hu).1)
          (slotStart S (q + 1 + 1)) (by omega) (by omega)).2,
        (hHf u hu).1, (hHf u hu).2.1, (hHf u hu).2.2 X hX⟩)
      (fun votes_p support_p hPCV => by rw [hPCV.1]; exact h88.2.1)
      (fun t h1 h2 => hp' t (by omega) (by omega)) hl hsent
      ⟨Hf u₀, (hHv u₀ hu₀).1, (hHv u₀ hu₀).2.1, (hHf u₀ hu₀).2.2 X hX⟩ haX
  obtain ⟨-, hBslot, hBne, hBpar?, hBparT⟩ := hPE _ hap (ancestorEq_refl _)
  have hPB : B.parent.AncestorEq B := ancestorEq_of_parent? hBpar?
  have hParentChain : ∀ C : Block V, OnHonestChainBefore S Sched x s₀ (q + 1) C →
      C.AncestorEq B.parent := by
    intro C hC
    rcases (compatible_iff _ _).1 (onHonestChainBefore_compatible S Sched x s₀ (q + 1) C _ hChain
      hC hap) with h | h
    · exact ancestorEq_trans h (get_anchor_ancestorEq_proposal_parent S Sched x (q + 2) ip B p hl
        hsent)
    · exact (hPE C hC h).1
  -- the proposer holds its proposal
  have hJIT : JustifiedInTree (stateBefore x (slotStart S (q + 2)) p).S :=
    hInvP.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1
  have hBparT' : B.parent ∈ (stateBefore x (slotStart S (q + 2)) p).S.T := by
    rcases hBparT with h | h
    · exact ((mem_fg_to_ac_tree _ _).1 ((mem_viable_tree_iff _ _ _).1 h).1).1
    · rw [h]; exact get_anchor_mem_T _ _ _ hInvP.2.2.2.1 hJIT
  have hFB : (stateBefore x (slotStart S (q + 2)) p).S.F.AncestorEq B :=
    ancestorEq_trans hFρp (ancestorEq_trans (hParentChain _ hρp) hPB)
  have hBp : B ∈ (x[ip + 1][p].st).S.T :=
    GoldilocksCorrectness.Statements.Executions.lem22a_proposer_holds_own_proposal S Sched x
      (q + 1) ip B p hDiv hMono hl hsent hRootNew hBparT' ((compatible_iff _ _).2 (Or.inl hFB))
  have hm1 : (stateBefore x (slotStart S (q + 2)) p).S.h_max - 1 ≤
      (chainStateOf S.C B.parent).h := by
    rw [← hEh]; exact (lem47_chain_state_heights S.C E B.parent).2.2.2.1 (hParentChain E hE)
  have hpv : p ∉ Sched.adv ((voteTime S (q + 2) : ℕ) : Int) :=
    (hp' (voteTime S (q + 2)) (by omega) (by omega)).2
  -- at every honest active validator of slot `q + 2`
  have hW : ∀ w ∈ honestActiveAt S Sched (q + 2),
      (get_fc_root (stateBefore x (voteTime S (q + 2)) w).S).AncestorEq B ∧
      B ∈ (stateBefore x (voteTime S (q + 2)) w).S.T := by
    intro w hwA
    have hw2 := honestActiveAt_window S Sched (q + 2) w hMono hwA
    have hwv : w ∉ Sched.adv ((voteTime S (q + 2) : ℕ) : Int) :=
      (hw2 (voteTime S (q + 2)) (by omega) (by omega)).2
    have hρw := proposer_root_on_chain_until S Sched x s₀ (q + 1) i₁ H (voteTime S (q + 2)) w hDiv
      hMono hRoots hU hAdvQ hOld hCaches (by omega) (by omega) hwv
    rw [fc_root_eq] at hρw
    have hρwB := ancestorEq_trans (hParentChain _ hρw) hPB
    refine ⟨hρwB, ?_⟩
    exact GoldilocksCorrectness.Statements.Executions.lem22_proposal_held_by_voter S Sched x GST
      (q + 1) ip B p w hDiv hMono hSync hCatch hRoots hParent (by omega) hpt
      (fun t h1 h2 => hw2 t (by omega) (by omega)) hl hsent hBp
      ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans
        (F_ancestorEq_fc_root_of_stateBefore S Sched x _ w) hρwB)))
  refine ⟨hParentChain, hBslot, hBne, hPB, fun w hwA vote hSend => ?_, fun w hwA => (hW w hwA).2⟩
  -- the vote names `B` (Lemma 59 with ordered `head_height_floor` values)
  have hw2 := honestActiveAt_window S Sched (q + 2) w hMono hwA
  have hwv : w ∉ Sched.adv ((voteTime S (q + 2) : ℕ) : Int) :=
    (hw2 (voteTime S (q + 2)) (by omega) (by omega)).2
  have h1v : 1 ≤ voteTime S (q + 2) := by omega
  have htjw := time_stepBefore_add_one x hDiv h1v
  have hwjw : w ∉ Sched.adv (x[stepBefore x (voteTime S (q + 2))].time : Int) :=
    fun h => hwv (hMono _ _ (by omega) h)
  have hφw : head_height_floor (stateBefore x (voteTime S (q + 2)) w).S =
      (stateBefore x (voteTime S (q + 2)) w).S.h_max - 1 :=
    (lem91d_not_contested_until S Sched x s₀ i₁ (stepBefore x (voteTime S (q + 2))) (q + 1) H w
      hDiv hMono hU hAdvQ hChain hOld
      (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃)
      (by omega) hwjw (fun s_a h => by
        have := (slot_le_of_supportCutoff_lt S s_a (q + 2)).1 (by omega)
        omega)).2
  have hc := lem91c_proposer_h_max_le_voter_h_max_until S Sched x GST s₀ (q + 2) i₁ H p w hDiv
    hMono
    hSync hCatch hRoots hParent hU hAdvQ hGST ht₀ hs hChain hOld hCaches hpt
    (fun t h1 h2 => hw2 t (by omega) (by omega))
  have h88w := lem88_counting_of_committeeSleepiness S Sched x anchor (q + 1) w
    (voteTime S (q + 1 + 1)) hSleepK (by omega)
  have hb := lem91b_voter_head_height_floor_le_parent_until S Sched x s₀ (q + 2) i₁ H p w B.parent
    hDiv
    hMono hU hAdvQ hs hChain hOld hCaches hpt hwv
    (fun C hC => hParentChain C hC) hm1
  exact GoldilocksCorrectness.Statements.Executions.lem59le_goldfish_vote_names_honest_proposal_frame
    S Sched x GST (q + 1) (honestActiveAt S Sched (q + 1) ∩ S.P.committee (q + 1)) Hf _ B p w vote
    _ _ _ _ hDiv hMono hSync hCatch hRoots hParent hOwner (by omega)
    (fun u hu => ⟨(Finset.mem_inter.1 hu).2,
      ((honestActiveAt_window S Sched (q + 1) u hMono (Finset.mem_inter.1 hu).1)
        (voteTime S (q + 1 + 1)) (by omega) (by omega)).2,
      (hHf u hu).1, (hHf u hu).2.1, (hHf u hu).2.2 _ hap⟩)
    (fun votes_w support_w hCV => h88w.2.2 votes_w support_w hCV)
    (fun t h1 h2 => hp' t (by omega) (by omega)) (fun t h1 h2 => hw2 t (by omega) (by omega))
    ⟨ip, hl, hsent⟩ hSend
    (fun B' hB' hsl => GoldilocksCorrectness.Statements.Executions.only_block_of_unforgeability S
      Sched x hU (q + 1 + 1) (voteTime S (q + 1 + 1)) B B' p w
      (fun t' h hv => hpv (hMono t' _ h hv)) rfl ⟨ip, hl, hsent⟩ hB' hsl)
    hRootNew ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (by rw [hφp, hφw]; omega_nat)
    ⟨Hf u₀, hHp u₀ hu₀, (hHf u₀ hu₀).2.2 _ hap, (hHf u₀ hu₀).2.2 _ hρp, (hHv u₀ hu₀).2.2⟩
    (ancestorEq_refl _) (hW w hwA).1
    (fun A' hrev e he hlive => by
      rcases mem_honestActiveAt_or_slept S Sched (q + 1) w hMono hwA with h | hsl
      · obtain ⟨D, hD, heD⟩ := hLocks (q + 1) (by omega) le_rfl w h A' hrev e he hlive
        exact ancestorEq_trans heD (ancestorEq_trans (hParentChain D hD) hPB)
      · exact (revoke_locks_empty_of_lockFree S Sched x (voteTime S (q + 1 + 1)) (q + 1 + 1) w A'
          (Nat.le_add_left 1 _) (lock_free_after_wake S Sched x (q + 1) w hDiv hMono hsl) hrev e
          he).elim)
    hb

/-- **Steps 2 and 3 of the inclusion: the proposal's parent extends the chain, and every honest
vote names the proposal.** Under the hypotheses of the inclusion at slot `q + 2`, with the lock
invariant at slot `q` (`hLk`) and `B` the proposal of slot `q + 2` with a root new to its proposer:
every block of the chain before `q + 1` is `B`'s parent or an ancestor of it; `B` is a non-genesis
block of slot `q + 2`; every vote an honest active validator `w` of slot `q + 2` sends at the vote
time of slot `q + 2` names `B`; and every such `w` holds `B` before that vote time.

Why: the proposer's root and anchor are on the chain (Lemma 91 (f), `proposer_anchor_on_chain`);
every honest committee member of slot `q + 1` voted for a block extending the chain, which reaches
the proposer as a viable head; so the proposal's parent extends every block of the chain
(`proposal_parent_extends_majority_block`, `get_anchor_ancestorEq_proposal_parent`). Lemma 59 with
ordered `head_height_floor` values (`lem59le_goldfish_vote_names_honest_proposal_frame`) then names `B` in every
honest vote: the `head_height_floor` values are ordered by Lemma 91 (c) and (d), and `head_height_floor` at the voter is at most the
parent's height by Lemma 91 (b). Lemmas 22a and 22 deliver `B`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the
  proposal.

Roots name blocks until `voteTime S (q + 2)`: the proof reads the proposer's root and anchor
before the start of slot `q + 2`, the voters' roots and Lemmas 22, 59 (ordered `head_height_floor` values) and 91
(c) up to the vote time of slot `q + 2`.

It is `honest_proposal_extends_chain_until` with the caches restricted to the steps it reads. -/
theorem honest_proposal_extends_chain (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S (q + 2)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (hs₀q : s₀ ≤ q) (hs : x[i₁].time < slotStart S (q + 2))
    (hLk : ∀ u ∈ honestActiveAt S Sched q,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (q + 1)) q u)
    (hp : ∀ t : ℕ, proposalWindowStart S (q + 2) ≤ t → t ≤ supportCutoff S (q + 3) →
      S.P.proposer (q + 2) ∈ Sched.awake (t : Int) ∧ S.P.proposer (q + 2) ∉ Sched.adv (t : Int))
    (hl : x.lbl ip = AtomicAction.tickAllAwake (slotStart S (q + 2)))
    (hsent : (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x[ip + 1].sent - x[ip].sent)
    (hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (q + 2)) (S.P.proposer (q + 2))).S.T,
      B'.root ≠ B.root) :
    (∀ C : Block V, OnHonestChainBefore S Sched x s₀ (q + 1) C → C.AncestorEq B.parent) ∧
    B.slot = q + 2 ∧ B ≠ Block.genesis ∧ B.parent.AncestorEq B ∧
    (∀ w ∈ honestActiveAt S Sched (q + 2), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (q + 2)) ∧
        (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) → vote.head = B.root) ∧
    (∀ w ∈ honestActiveAt S Sched (q + 2), B ∈ (stateBefore x (voteTime S (q + 2)) w).S.T) :=
  honest_proposal_extends_chain_until S Sched x GST s₀ anchor i₁ H q ip B hDiv hMono hSync hCatch
    hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST (confirmationsChainBefore_of_chain S
    Sched x s₀ _ hChain) (fun s h₁ _ => hInv s h₁) (fun s h₁ _ => hLocks s h₁) hOld (fun j u h₁ _ h₂
    => hCaches j u h₁ h₂) ht₀ hs₀q hs hLk hp hl hsent hRootNew

/-! ## Steps 4 and 5: the update of the proposal's slot -/

omit [RootOrder] in
/-- An updater of slot `s` is an honest active validator of slot `s`, or was asleep at some time
from the duty window's start of slot `s` to before that of slot `s + 1`.

The variables:
- `S`: the setup; `Sched`: the schedule; `s`: the slot; `v`: the validator. -/
theorem updater_active_or_slept (S : Setup V) (Sched : Schedule V) (s : ℕ) (v : V)
    (hv : v ∈ updaterAt S Sched s) :
    v ∈ honestActiveAt S Sched s ∨ ∃ t : ℕ, dutyWindowStart S s ≤ t ∧
      t < dutyWindowStart S (s + 1) ∧ v ∉ Sched.awake (t : Int) := by
  unfold updaterAt at hv
  rw [Finset.mem_sdiff, mem_awakeThroughout_iff] at hv
  obtain ⟨hAwI, hHon⟩ := hv
  by_contra hno
  push Not at hno
  obtain ⟨hA, hsl⟩ := hno
  apply hA
  unfold honestActiveAt activeAt
  rw [Finset.mem_sdiff, mem_awakeThroughout_iff]
  refine ⟨fun t'' h1 h2 => ?_, hHon⟩
  have h0 : (0 : Int) ≤ t'' := le_trans (Int.natCast_nonneg _) h1
  have hn : ((t''.toNat : ℕ) : Int) = t'' := Int.toNat_of_nonneg h0
  by_cases hlt : t''.toNat < dutyWindowStart S (s + 1)
  · have := hsl t''.toNat (by omega) hlt
    rw [hn] at this
    exact this
  · exact hAwI t'' (by omega) h2

/-- **Step 4 of the inclusion: every updater saves the proposal, fast and locked.** Under the
hypotheses of `honest_proposal_extends_chain`: every block of the chain before `q + 2` is `B` or an
ancestor of `B`; `B` is a non-genesis block of slot `q + 2`; `HonestChainExtends` holds for `B` at
slot `q + 2` at its honest active validators; every updater of slot `q + 2` saves `B` (Lemma 27),
has its finalized block and its fork-choice root on `B`'s chain, keeps no live lock off `B`'s
chain after its revocation of slot `q + 3`, and has `B` fast and locked (Lemma 60).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the
  proposal.

Roots name blocks until `supportCutoff S (q + 2 + 1)`: the updaters' fork-choice roots before
the support cutoff of slot `q + 3` (`proposer_root_on_chain`), and Lemmas 27 and 60 at slot
`q + 2`.

Caches up to `supportCutoff S (q + 2 + 1)`: `honest_proposal_extends_chain_until`, and the
updaters' caches before the support cutoff of slot `q + 3` (`proposer_root_on_chain_until`). -/
theorem honest_proposal_saved_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (q + 2 + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀)
    (hChain : ConfirmationsChainBefore S Sched x s₀ (q + 1))
    (hInv : ∀ s : ℕ, s₀ < s → s ≤ q + 2 →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → s ≤ q + 2 → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ supportCutoff S (q + 2 + 1) →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (hs₀q : s₀ ≤ q) (hs : x[i₁].time < slotStart S (q + 2))
    (hLk : ∀ u ∈ honestActiveAt S Sched q,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (q + 1)) q u)
    (hp : ∀ t : ℕ, proposalWindowStart S (q + 2) ≤ t → t ≤ supportCutoff S (q + 3) →
      S.P.proposer (q + 2) ∈ Sched.awake (t : Int) ∧ S.P.proposer (q + 2) ∉ Sched.adv (t : Int))
    (hl : x.lbl ip = AtomicAction.tickAllAwake (slotStart S (q + 2)))
    (hsent : (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x[ip + 1].sent - x[ip].sent)
    (hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (q + 2)) (S.P.proposer (q + 2))).S.T,
      B'.root ≠ B.root) :
    (∀ C : Block V, OnHonestChainBefore S Sched x s₀ (q + 2) C → C.AncestorEq B) ∧
    B.slot = q + 2 ∧ B ≠ Block.genesis ∧
    HonestChainExtends S Sched x (honestActiveAt S Sched (q + 2)) B (q + 2) ∧
    (∀ v ∈ updaterAt S Sched (q + 2),
      (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.saved_confirmation (q + 2) = some B) ∧
    (∀ v ∈ updaterAt S Sched (q + 2),
      (stateBefore x (supportCutoff S (q + 2 + 1)) v).S.F.AncestorEq B ∧
      (get_fc_root (stateBefore x (supportCutoff S (q + 2 + 1)) v).S).AncestorEq B ∧
      ∀ A' : ACState V,
        revoke_locks S.P (expireLocks (stateBefore x (voteTime S (q + 2 + 1)) v).A
          ((voteTime S (q + 2 + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (q + 2 + 1)) v).S)
          ((voteTime S (q + 2 + 1) : ℕ) : Int) (q + 2 + 1) = .ok A' →
        ∀ e ∈ A'.lock_entries,
          is_live (fg_to_ac (stateBefore x (voteTime S (q + 2 + 1)) v).S)
            ((voteTime S (q + 2 + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
    (∀ v ∈ updaterAt S Sched (q + 2),
      B ∈ (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.fast_blocks ∧
      LockEntry.mk B (S.C.t_ (q + 2 + S.C.k) + 5 * S.C.Δ) ∈
        (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.lock_entries) := by
  have hΔ := one_le_Δ S
  have hss : slotStart S (q + 2) = slotStart S (q + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (q + 1), show q + 2 = (q + 1) + 1 from rfl, Nat.mul_add,
      Nat.mul_one]
  have hss3 : slotStart S (q + 3) = slotStart S (q + 2) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (q + 2), show q + 3 = (q + 2) + 1 from rfl, Nat.mul_add,
      Nat.mul_one]
  have hv2 := voteTime_eq S (q + 2)
  have hv3 := voteTime_eq S (q + 3)
  have hc3 := supportCutoff_eq S (q + 3)
  have hc2 := supportCutoff_eq S (q + 2)
  have hvb' : voteTime S (q + 2 + 1) = voteTime S (q + 3) := rfl
  have hcb' : supportCutoff S (q + 2 + 1) = supportCutoff S (q + 3) := rfl
  have hssb' : slotStart S (q + 2 + 1) = slotStart S (q + 3) := rfl
  have hdw3 := dutyWindowStart_succ_le_slotStart S (q + 2)
  have hdwb : dutyWindowStart S (q + 2 + 1) = dutyWindowStart S (q + 3) := rfl
  have hvb : voteTime S (q + 1 + 1) = voteTime S (q + 2) := rfl
  have hssb : slotStart S (q + 1 + 1) = slotStart S (q + 2) := rfl
  have hcb : supportCutoff S (q + 1 + 1) = supportCutoff S (q + 2) := rfl
  have hdw2 : dutyWindowStart S (q + 2) ≤ slotStart S (q + 1) := dutyWindowStart_succ_le_slotStart S (q + 1)
  have hsq1 : slotStart S (q + 1) ≤ slotStart S (q + 2) := slotStart_mono S (by omega)
  have hsq0 : slotStart S s₀ ≤ slotStart S (q + 2) := slotStart_mono S (by omega)
  have hv0 := voteTime_eq S s₀
  obtain ⟨hParentChain, hBslot, hBne, hPB, hVote, hBw⟩ := honest_proposal_extends_chain_until S
    Sched x GST s₀ anchor i₁ H q ip B hDiv hMono hSync hCatch (hRoots.mono (by omega))
    hParent hOwner hU hAdvQ hSleepK
    hAnchor hGST hChain (fun s h₁ h₂ => hInv s h₁ (by omega))
    (fun s h₁ h₂ => hLocks s h₁ (by omega))
    hOld
    (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃) ht₀ hs₀q hs hLk hp hl hsent
    hRootNew
  -- the voters of slot `q + 2` and their votes, which are for `B`
  have h88 := lem88_counting_of_committeeSleepiness S Sched x anchor (q + 2) (S.P.proposer (q + 2))
    (slotStart S (q + 2)) hSleepK (by omega)
  obtain ⟨w₀, hw₀⟩ : (honestActiveAt S Sched (q + 2) ∩ S.P.committee (q + 2)).Nonempty :=
    Finset.card_pos.1 (by omega)
  have hInv2 := hInv (q + 2) (by omega) le_rfl
  -- the votes of slot `q + 2`, in the form of the first clause
  have hClause : ∀ u ∈ honestActiveAt S Sched (q + 2), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (q + 2)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∀ C : Block V, OnHonestChainBefore S Sched x s₀ (q + 2) C →
        vote = GoldfishVote.mk u (q + 2) B.root ∧ C.AncestorEq B := by
    intro u hu vote hsend C hC
    obtain ⟨H', hH'T, heq, hCH'⟩ := (hInv2 C hC).1 u hu vote hsend
    have hhead : H'.root = B.root := by
      have h1 := hVote u hu vote hsend
      rw [heq] at h1
      exact h1
    have hInvU := (lem11_node_invariant S Sched x (stepBefore x (voteTime S (q + 2))) u).1
    have hHB : H' = B := hInvU.2.2.2.2.2.2.2.2.2.1.1 _ hH'T _ (hBw u hu) hhead
    rw [hHB] at hCH' heq
    exact ⟨heq, hCH'⟩
  have hChainLeB : ∀ C : Block V, OnHonestChainBefore S Sched x s₀ (q + 2) C → C.AncestorEq B := by
    intro C hC
    obtain ⟨i, vote, hli, -, -, hsi⟩ := honest_active_votes S Sched x (q + 2) w₀ hDiv hMono
      (Finset.mem_inter.1 hw₀).1 (Finset.mem_inter.1 hw₀).2
    exact (hClause w₀ (Finset.mem_inter.1 hw₀).1 vote ⟨i, hli, hsi⟩ C hC).2
  -- a block of the chain before `q + 2`, to read the first clause at
  obtain ⟨i₀, vote₀, hl₀, -, -, hs₀⟩ := honest_active_votes S Sched x (q + 2) w₀ hDiv hMono
    (Finset.mem_inter.1 hw₀).1 (Finset.mem_inter.1 hw₀).2
  have hw₀w := honestActiveAt_window S Sched (q + 2) w₀ hMono (Finset.mem_inter.1 hw₀).1
  have hC₀ := proposer_root_on_chain_until S Sched x s₀ (q + 1) i₁ H (voteTime S (q + 2)) w₀ hDiv
    hMono (hRoots.mono (by omega)) hU hAdvQ hOld
    (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃) (by omega) (by omega)
    (hw₀w (voteTime S (q + 2)) (by omega) (by omega)).2
  have hC₀' : OnHonestChainBefore S Sched x s₀ (q + 2) _ :=
    ⟨hC₀.choose, by have := hC₀.choose_spec.1; omega, hC₀.choose_spec.2⟩
  -- the votes with `B` as their block
  have hVotesB : ∀ u ∈ honestActiveAt S Sched (q + 2), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (q + 2)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      vote = GoldfishVote.mk u (q + 2) B.root :=
    fun u hu vote hsend => (hClause u hu vote hsend _ hC₀').1
  -- the frame at every updater of slot `q + 2`
  have hUpd : ∀ v ∈ updaterAt S Sched (q + 2),
      (stateBefore x (supportCutoff S (q + 2 + 1)) v).S.F.AncestorEq B ∧
      (get_fc_root (stateBefore x (supportCutoff S (q + 2 + 1)) v).S).AncestorEq B ∧
      ∀ A' : ACState V,
        revoke_locks S.P (expireLocks (stateBefore x (voteTime S (q + 2 + 1)) v).A
          ((voteTime S (q + 2 + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (q + 2 + 1)) v).S)
          ((voteTime S (q + 2 + 1) : ℕ) : Int) (q + 2 + 1) = .ok A' →
        ∀ e ∈ A'.lock_entries,
          is_live (fg_to_ac (stateBefore x (voteTime S (q + 2 + 1)) v).S)
            ((voteTime S (q + 2 + 1) : ℕ) : Int) e = true → e.B.AncestorEq B := by
    intro v hv
    have hvw := updaterAt_window S Sched (q + 2) v hMono hv
    have hvc : v ∉ Sched.adv ((supportCutoff S (q + 2 + 1) : ℕ) : Int) :=
      (hvw (supportCutoff S (q + 2 + 1)) (by omega) le_rfl).2
    have hρv := proposer_root_on_chain_until S Sched x s₀ (q + 2) i₁ H (supportCutoff S (q + 2 + 1))
      v hDiv hMono hRoots hU hAdvQ hOld hCaches (by omega) (by omega) hvc
    rw [fc_root_eq] at hρv
    have hρB := hChainLeB _ hρv
    refine ⟨ancestorEq_trans (F_ancestorEq_fc_root_of_stateBefore S Sched x _ v) hρB, hρB,
      fun A' hrev e he hlive => ?_⟩
    rcases updater_active_or_slept S Sched (q + 2) v hv with h | hsl
    · obtain ⟨D, hD, heD⟩ := hLocks (q + 2) (by omega) le_rfl v h A' hrev e he hlive
      exact ancestorEq_trans heD (hChainLeB D hD)
    · exact (revoke_locks_empty_of_lockFree S Sched x (voteTime S (q + 2 + 1)) (q + 2 + 1) v A'
        (Nat.le_add_left 1 _) (lock_free_after_wake S Sched x (q + 2) v hDiv hMono hsl) hrev e
        he).elim
  -- every updater saves `B` (Lemma 27)
  have hSaved : ∀ v ∈ updaterAt S Sched (q + 2),
      (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.saved_confirmation (q + 2) = some B := by
    intro v hv
    obtain ⟨hFv, -, hLv⟩ := hUpd v hv
    have h88v := lem88_counting_of_committeeSleepiness S Sched x anchor (q + 2) v
      (supportCutoff S (q + 2 + 1)) hSleepK (by omega)
    refine (GoldilocksCorrectness.Statements.Executions.lem27_update_confirmation_confirms_voter_majority_block
      S Sched x GST (q + 2) (honestActiveAt S Sched (q + 2) ∩ S.P.committee (q + 2)) B v hDiv hMono
      hSync hCatch (hRoots.mono (by omega)) hParent hOwner (by omega) (fun u hu => ?_)
      h88v.2.1 hBne
      (updaterAt_window S Sched (q + 2) v hMono hv) hFv
      (fun A' hrev e he hlive => (compatible_iff _ _).2 (Or.inl (hLv A' hrev e he hlive)))).1
    have huA := (Finset.mem_inter.1 hu).1
    have huw := honestActiveAt_window S Sched (q + 2) u hMono huA
    obtain ⟨i, vote, hli, -, -, hsi⟩ := honest_active_votes S Sched x (q + 2) u hDiv hMono
      huA (Finset.mem_inter.1 hu).2
    have hvB := hVotesB u huA vote ⟨i, hli, hsi⟩
    subst hvB
    exact ⟨(Finset.mem_inter.1 hu).2, (huw (supportCutoff S (q + 2 + 1)) (by omega) le_rfl).2,
      ⟨i, hli, hsi⟩, hBw u huA⟩
  -- every updater makes `B` fast and locks it (Lemma 60)
  have hFast : ∀ v ∈ updaterAt S Sched (q + 2),
      B ∈ (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.fast_blocks ∧
      LockEntry.mk B (S.C.t_ (q + 2 + S.C.k) + 5 * S.C.Δ) ∈
        (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.lock_entries := by
    intro v hv
    obtain ⟨-, hρv, -⟩ := hUpd v hv
    have h88v := lem88_counting_of_committeeSleepiness S Sched x anchor (q + 2) v
      (supportCutoff S (q + 2 + 1)) hSleepK (by omega)
    refine GoldilocksCorrectness.Statements.Executions.lem60_update_confirmation_fast_locks_frame
      S Sched x GST (q + 2) (honestActiveAt S Sched (q + 2) ∩ S.P.committee (q + 2)) B v hDiv hMono
      hSync hCatch (hRoots.mono (by omega)) hParent hOwner (by omega) (fun u hu => ?_)
      h88v.2.1
      (by have := h88v.1; omega) hBne (updaterAt_window S Sched (q + 2) v hMono hv) hρv
    have huA := (Finset.mem_inter.1 hu).1
    have huw := honestActiveAt_window S Sched (q + 2) u hMono huA
    obtain ⟨i, vote, hli, -, -, hsi⟩ := honest_active_votes S Sched x (q + 2) u hDiv hMono
      huA (Finset.mem_inter.1 hu).2
    have hvB := hVotesB u huA vote ⟨i, hli, hsi⟩
    subst hvB
    exact ⟨(Finset.mem_inter.1 hu).2, (huw (supportCutoff S (q + 2 + 1)) (by omega) le_rfl).2,
      ⟨i, hli, hsi⟩, hBw u huA⟩
  refine ⟨hChainLeB, hBslot, hBne, ⟨fun u hu vote hsend => ⟨B, hBw u hu,
    hVotesB u hu vote hsend, ancestorEq_refl B⟩, fun w hw A' hrev e he hlive => ?_,
    fun v hv C' hC' => ?_⟩, hSaved, hUpd, hFast⟩
  · exact (compatible_iff _ _).2 (Or.inl ((hUpd w (honestActiveAt_subset_updaterAt S Sched _ hw)).2.2
      A' hrev e he hlive))
  · rw [hSaved v (honestActiveAt_subset_updaterAt S Sched _ hv)] at hC'
    cases hC'
    exact ancestorEq_refl B

/-- **Step 4 of the inclusion: every updater saves the proposal, fast and locked.** Under the
hypotheses of `honest_proposal_extends_chain`: every block of the chain before `q + 2` is `B` or an
ancestor of `B`; `B` is a non-genesis block of slot `q + 2`; `HonestChainExtends` holds for `B` at
slot `q + 2` at its honest active validators; every updater of slot `q + 2` saves `B` (Lemma 27),
has its finalized block and its fork-choice root on `B`'s chain, keeps no live lock off `B`'s
chain after its revocation of slot `q + 3`, and has `B` fast and locked (Lemma 60).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the
  proposal.

Roots name blocks until `supportCutoff S (q + 2 + 1)`: the updaters' fork-choice roots before
the support cutoff of slot `q + 3` (`proposer_root_on_chain`), and Lemmas 27 and 60 at slot
`q + 2`.

It is `honest_proposal_saved_until` with the caches restricted to the steps it reads. -/
theorem honest_proposal_saved (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (q + 2 + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (hs₀q : s₀ ≤ q) (hs : x[i₁].time < slotStart S (q + 2))
    (hLk : ∀ u ∈ honestActiveAt S Sched q,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (q + 1)) q u)
    (hp : ∀ t : ℕ, proposalWindowStart S (q + 2) ≤ t → t ≤ supportCutoff S (q + 3) →
      S.P.proposer (q + 2) ∈ Sched.awake (t : Int) ∧ S.P.proposer (q + 2) ∉ Sched.adv (t : Int))
    (hl : x.lbl ip = AtomicAction.tickAllAwake (slotStart S (q + 2)))
    (hsent : (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x[ip + 1].sent - x[ip].sent)
    (hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (q + 2)) (S.P.proposer (q + 2))).S.T,
      B'.root ≠ B.root) :
    (∀ C : Block V, OnHonestChainBefore S Sched x s₀ (q + 2) C → C.AncestorEq B) ∧
    B.slot = q + 2 ∧ B ≠ Block.genesis ∧
    HonestChainExtends S Sched x (honestActiveAt S Sched (q + 2)) B (q + 2) ∧
    (∀ v ∈ updaterAt S Sched (q + 2),
      (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.saved_confirmation (q + 2) = some B) ∧
    (∀ v ∈ updaterAt S Sched (q + 2),
      (stateBefore x (supportCutoff S (q + 2 + 1)) v).S.F.AncestorEq B ∧
      (get_fc_root (stateBefore x (supportCutoff S (q + 2 + 1)) v).S).AncestorEq B ∧
      ∀ A' : ACState V,
        revoke_locks S.P (expireLocks (stateBefore x (voteTime S (q + 2 + 1)) v).A
          ((voteTime S (q + 2 + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (q + 2 + 1)) v).S)
          ((voteTime S (q + 2 + 1) : ℕ) : Int) (q + 2 + 1) = .ok A' →
        ∀ e ∈ A'.lock_entries,
          is_live (fg_to_ac (stateBefore x (voteTime S (q + 2 + 1)) v).S)
            ((voteTime S (q + 2 + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
    (∀ v ∈ updaterAt S Sched (q + 2),
      B ∈ (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.fast_blocks ∧
      LockEntry.mk B (S.C.t_ (q + 2 + S.C.k) + 5 * S.C.Δ) ∈
        (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.lock_entries) :=
  honest_proposal_saved_until S Sched x GST s₀ anchor i₁ H q ip B hDiv hMono hSync hCatch
    hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST (confirmationsChainBefore_of_chain S Sched x
    s₀ _ hChain) (fun s h₁ _ => hInv s h₁) (fun s h₁ _ => hLocks s h₁) hOld (fun j u h₁ _ h₂ =>
    hCaches j u h₁ h₂) ht₀ hs₀q hs hLk hp hl hsent hRootNew

/-! ## Step 6: the growth -/

/-- The live lock entries of an updater `v` of slot `s₀` before the support cutoff of slot
`s₀ + 1` are compatible with `B₀`, when, if `v` is an honest active validator of slot `s₀`, the live
entries its revocation of slot `s₀ + 1` leaves are. `live_locks_compatible_at_healed_update`'s
proof with that hypothesis in place of `HonestChainExtends`'s second clause.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the slot; `B₀`: the block;
  `v`: the updater. -/
theorem live_locks_compatible_of_revocation (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ : ℕ) (B₀ : Block V) (v : V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- `v` is an updater of slot `s₀`
    (hv : v ∈ updaterAt S Sched s₀)
    -- when `v` is an honest active validator of slot `s₀`, the live entries its revocation of slot
    -- `s₀ + 1` leaves are compatible with `B₀`
    (hRev : v ∈ honestActiveAt S Sched s₀ → ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s₀ + 1)) v).A
        ((voteTime S (s₀ + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s₀ + 1)) v).S)
        ((voteTime S (s₀ + 1) : ℕ) : Int) (s₀ + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s₀ + 1)) v).S)
          ((voteTime S (s₀ + 1) : ℕ) : Int) e = true → e.B.compatible B₀ = true) :
    ∀ e ∈ (stateBefore x (supportCutoff S (s₀ + 1)) v).A.lock_entries,
      is_live (fg_to_ac (stateBefore x (supportCutoff S (s₀ + 1)) v).S)
        ((supportCutoff S (s₀ + 1) : ℕ) : Int) e = true → e.B.compatible B₀ = true := by
  intro e he₂ hlive
  have hvU := hv
  unfold updaterAt at hvU
  rw [Finset.mem_sdiff, mem_awakeThroughout_iff] at hvU
  obtain ⟨hAwI, hHon⟩ := hvU
  have hAw : ∀ t' : ℕ, dutyWindowStart S (s₀ + 1) ≤ t' → t' ≤ supportCutoff S (s₀ + 1) →
      v ∈ Sched.awake (t' : Int) :=
    fun t' h1 h2 => hAwI t' (by exact_mod_cast h1) (by exact_mod_cast h2)
  have hdl : ((supportCutoff S (s₀ + 1) : ℕ) : Int) < e.d := by
    rw [is_live_iff] at hlive
    exact hlive.1
  -- the times
  have hΔ := one_le_Δ S
  have hv₃ : voteTime S (s₀ + 1) = slotStart S (s₀ + 1) + Δ S := voteTime_eq S (s₀ + 1)
  have hv₂ : supportCutoff S (s₀ + 1) = voteTime S (s₀ + 1) + Δ S := supportCutoff_eq S (s₀ + 1)
  have hdw : dutyWindowStart S (s₀ + 1) ≤ slotStart S s₀ := dutyWindowStart_succ_le_slotStart S s₀
  have hss : slotStart S (s₀ + 1) = slotStart S s₀ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss' : slotStart S (s₀ + 1 + 1) = slotStart S (s₀ + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s₀ + 1), Nat.mul_add, Nat.mul_one]
  have hslot : ∀ t : ℕ, voteTime S (s₀ + 1) ≤ t → t ≤ supportCutoff S (s₀ + 1) →
      S.C.slot (t : Int) = s₀ + 1 :=
    fun t h1 h2 => slot_eq_of_mem S (by omega) (by omega)
  have hslot₃ := hslot (voteTime S (s₀ + 1)) le_rfl (by omega)
  -- the tick at the vote time of slot `s₀ + 1` ran the revocation
  obtain ⟨hl₃, -, hti₃'⟩ := stepBefore_spec x hDiv (by omega : 1 ≤ voteTime S (s₀ + 1))
  have hv₃a : v ∈ Sched.awake ((voteTime S (s₀ + 1) : ℕ) : Int) ∧
      v ∉ Sched.adv ((voteTime S (s₀ + 1) : ℕ) : Int) :=
    ⟨hAw _ (by omega) (by omega),
      fun h => hHon (hMono _ _ (by exact_mod_cast (by omega : voteTime S (s₀ + 1) ≤
        supportCutoff S (s₀ + 1))) h)⟩
  obtain ⟨n₃, sent₃, hrun₃, hst₃⟩ := tick_step_outcome x hl₃ hv₃a.1 hv₃a.2
  have hAw₃ := awakeSince_le_dutyWindowStart_b S Sched x (s₀ + 1) (voteTime S (s₀ + 1)) v hDiv
    hMono (by omega) (fun t h1 h2 => hAw t h1 (by omega)) hv₃a.2
  have hA₃ : (tickInputState x (stepBefore x (voteTime S (s₀ + 1))) (voteTime S (s₀ + 1)) v).A =
      (stateBefore x (voteTime S (s₀ + 1)) v).A := (tickInputState_frame x _ _ v).2.1
  have hS₃ : (tickInputState x (stepBefore x (voteTime S (s₀ + 1))) (voteTime S (s₀ + 1)) v).S =
      (stateBefore x (voteTime S (s₀ + 1)) v).S := (tickInputState_frame x _ _ v).1
  obtain ⟨A₃, hRevoke, hlock₃⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem13_tick_revokes_locks S.C S.P S.X _ n₃ _ sent₃
      hrun₃ (by rw [hslot₃, voteTime_cast]) (by rw [hslot₃]; exact hAw₃)
  rw [hslot₃, hA₃, hS₃] at hRevoke
  -- from the tick at the vote time to the cutoff the lock entries only shrink
  have hsub : (stateBefore x (supportCutoff S (s₀ + 1)) v).A.lock_entries ⊆ A₃.lock_entries := by
    rw [← hlock₃, ← hst₃]
    refine stateBefore_lock_entries_subset x hDiv v (by omega) (by omega) ?_
    intro t'' h1 h2
    rw [hti₃'] at h1
    rw [hslot t'' (by omega) (by omega), ← voteTime_cast, ← supportCutoff_cast]
    constructor <;> intro h <;> omega
  have heA := hsub he₂
  by_cases hA : v ∈ honestActiveAt S Sched s₀
  · -- an honest active validator: the second clause of `HonestChainExtends`
    refine hRev hA A₃ hRevoke e heA ?_
    rw [is_live_iff]
    have h32 : ((voteTime S (s₀ + 1) : ℕ) : Int) < ((supportCutoff S (s₀ + 1) : ℕ) : Int) :=
      Int.ofNat_lt.2 (by omega)
    exact ⟨lt_trans h32 hdl,
      GoldilocksCorrectness.Proofs.Routines.revoke_locks_entry_mem_tree (Nat.le_add_left 1 s₀)
        hRevoke e heA⟩
  · -- otherwise `v` slept in the duty window of slot `s₀`, and the revocation left no lock
    exfalso
    have hSlept : ∃ t : ℕ, dutyWindowStart S s₀ ≤ t ∧ t < dutyWindowStart S (s₀ + 1) ∧
        v ∉ Sched.awake (t : Int) := by
      by_contra hno
      apply hA
      unfold honestActiveAt activeAt
      rw [Finset.mem_sdiff, mem_awakeThroughout_iff]
      refine ⟨fun t'' h1 h2 => ?_, hHon⟩
      have h0 : (0 : Int) ≤ t'' := le_trans (Int.natCast_nonneg _) h1
      have hn : ((t''.toNat : ℕ) : Int) = t'' := Int.toNat_of_nonneg h0
      by_cases hlt : t''.toNat < dutyWindowStart S (s₀ + 1)
      · by_contra hna
        exact hno ⟨t''.toNat, by omega, hlt, by rw [hn]; exact hna⟩
      · exact hAwI t'' (by omega) h2
    exact GoldilocksCorrectness.Proofs.Executions.revoke_locks_empty_of_lockFree S Sched x
      (voteTime S (s₀ + 1)) (s₀ + 1) v A₃ (Nat.le_add_left 1 s₀)
      (GoldilocksCorrectness.Proofs.Executions.lock_free_after_wake S Sched x s₀ v hDiv hMono
        hSlept) hRevoke e heA


/-- **Kit fact, an updater after healing saves a confirmation.** Every updater `v` of a slot
`s' > s₀` starting after the phase's end saves some confirmation of slot `s'`.

Why: the honest committee members of slot `s'` voted for blocks extending the root of `v`'s fork
choice, which is on the chain (Lemma 91 (f)) and extends `v`'s finalized block; their votes reach
`v` early (Lemma 12) and are more than half of its pool's voters (Lemma 88), so the update saves the
end of its walk (`update_confirmation_saves_of_supporters`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `s'`: the slot; `v`: the updater.

Roots name blocks until `supportCutoff S (s' + 1)`: the updater's fork-choice root before the
support cutoff of slot `s' + 1` (`proposer_root_on_chain`), and Lemma 12 at slot `s'`.

Caches up to `supportCutoff S (s' + 1)`: the updater's caches before the support cutoff of slot
`s' + 1` (`proposer_root_on_chain_until`). -/
theorem updater_saves_after_healing_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H s' : ℕ) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀)
    (hInv : ∀ s : ℕ, s₀ < s → s ≤ s' →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ supportCutoff S (s' + 1) →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hs₀ : s₀ < s') (hs : x[i₁].time < slotStart S s')
    (hv : v ∈ updaterAt S Sched s') :
    ∃ C' : Block V,
      (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' := by
  have hΔ := one_le_Δ S
  have hss : slotStart S (s' + 1) = slotStart S s' + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s' + 1) = slotStart S (s' + 1) + Δ S := voteTime_eq S (s' + 1)
  have hv₂ : supportCutoff S (s' + 1) = voteTime S (s' + 1) + Δ S := supportCutoff_eq S (s' + 1)
  have hc₁ : supportCutoff S s' = voteTime S s' + Δ S := supportCutoff_eq S s'
  have hv₁ : voteTime S s' = slotStart S s' + Δ S := voteTime_eq S s'
  have hv₀ := voteTime_eq S s₀
  have hsq : slotStart S s₀ ≤ slotStart S s' := slotStart_mono S hs₀.le
  have hdw : dutyWindowStart S (s' + 1) ≤ slotStart S s' := dutyWindowStart_succ_le_slotStart S s'
  have hdwc : dutyWindowStart S (s' + 1) < supportCutoff S (s' + 1) := by omega
  have hvw := updaterAt_window S Sched s' v hMono hv
  have hvc := hvw (supportCutoff S (s' + 1)) hdwc.le le_rfl
  have hAw := awakeSince_le_dutyWindowStart_b S Sched x (s' + 1) (supportCutoff S (s' + 1)) v hDiv
    hMono hdwc (fun t h1 h2 => (hvw t h1 h2).1) hvc.2
  obtain ⟨A'', hUpdate, hsave, -, -, -⟩ := update_state_of_duty S Sched x s' v hDiv hvc hAw
  rw [hsave]
  -- the root of `v`'s fork choice is on the chain before `s'`, and so every voter's block extends
  -- `v`'s finalized block
  have hρ := proposer_root_on_chain_until S Sched x s₀ s' i₁ H (supportCutoff S (s' + 1)) v hDiv
    hMono hRoots hU hAdvQ hOld hCaches (by omega) le_rfl hvc.2
  rw [fc_root_eq] at hρ
  obtain ⟨Hf, hHf⟩ := chain_votes_of_inv S Sched x s₀ s' _ hDiv hMono (hInv s' hs₀ le_rfl) hρ
  have hFρ := F_ancestorEq_fc_root_of_stateBefore S Sched x (supportCutoff S (s' + 1)) v
  have h88 := lem88_counting_of_committeeSleepiness S Sched x anchor s' v
    (supportCutoff S (s' + 1)) hSleepK (by omega)
  have hHeld : ∀ u ∈ honestActiveAt S Sched s' ∩ S.P.committee s',
      HeldEarlyVoteFor S.C (stateBefore x (supportCutoff S (s' + 1)) v).A
        (fg_to_ac (stateBefore x (supportCutoff S (s' + 1)) v).S) s' (Hf u) u :=
    GoldilocksCorrectness.Statements.Executions.lem12_honest_vote_delivered_until S Sched x GST s'
      (supportCutoff S (s' + 1)) _ Hf v hDiv hMono hSync hCatch (hRoots.mono (by omega))
      hParent hOwner
      (by omega) (by omega)
      (fun u hu => ⟨(Finset.mem_inter.1 hu).2,
        ((honestActiveAt_window S Sched s' u hMono (Finset.mem_inter.1 hu).1)
          (supportCutoff S (s' + 1)) (dutyWindowStart_le_supportCutoff S (by omega)) le_rfl).2,
        (hHf u hu).1, (hHf u hu).2.1⟩)
      (fun t h1 h2 => hvw t (by omega) (by omega))
      (fun u hu => ancestorEq_trans hFρ ((hHf u hu).2.2 _ hρ))
  have hRoots₂ : GoldilocksCorrectness.Statements.Routines.RootsNameBlocksIn
      (fg_to_ac (stateBefore x (supportCutoff S (s' + 1)) v).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ v
  have hSup : ∀ u ∈ honestActiveAt S Sched s' ∩ S.P.committee s', EarlySupporterOf S.C
      (expireLocks (stateBefore x (supportCutoff S (s' + 1)) v).A
        ((supportCutoff S (s' + 1) : ℕ) : Int))
      (fg_to_ac (stateBefore x (supportCutoff S (s' + 1)) v).S) (s' + 1 - 1)
      (fg_to_ac (stateBefore x (supportCutoff S (s' + 1)) v).S).F u :=
    fun u hu => (earlySupporterOf_of_keepsVotes (expireLocks_keepsVotes _ _) _ _ _ _ _).2
      (heldEarlyVoteFor_earlySupporterOf S.C _ _ s' _ (Hf u) u (hHeld u hu)
        (by rw [fg_to_ac_F]; exact ancestorEq_trans hFρ ((hHf u hu).2.2 _ hρ)))
  have h := GoldilocksCorrectness.Proofs.Routines.update_confirmation_saves_of_supporters S.C S.P
    _ A'' _ _ (s' + 1) _ _ (Nat.le_add_left 1 s') hRoots₂ (ancestorEq_refl _) hSup
    (by rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)]; exact pool_slot_of_stateBefore S Sched x _ v s')
    (by rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)]; exact h88.2.1) hUpdate
  rw [Nat.add_sub_cancel] at h
  exact h

/-- **Kit fact, an updater after healing saves a confirmation.** Every updater `v` of a slot
`s' > s₀` starting after the phase's end saves some confirmation of slot `s'`.

Why: the honest committee members of slot `s'` voted for blocks extending the root of `v`'s fork
choice, which is on the chain (Lemma 91 (f)) and extends `v`'s finalized block; their votes reach
`v` early (Lemma 12) and are more than half of its pool's voters (Lemma 88), so the update saves the
end of its walk (`update_confirmation_saves_of_supporters`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `s'`: the slot; `v`: the updater.

Roots name blocks until `supportCutoff S (s' + 1)`: the updater's fork-choice root before the
support cutoff of slot `s' + 1` (`proposer_root_on_chain`), and Lemma 12 at slot `s'`.

It is `updater_saves_after_healing_until` with the caches restricted to the steps it reads. -/
theorem updater_saves_after_healing (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H s' : ℕ) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hs₀ : s₀ < s') (hs : x[i₁].time < slotStart S s')
    (hv : v ∈ updaterAt S Sched s') :
    ∃ C' : Block V,
      (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' :=
  updater_saves_after_healing_until S Sched x GST s₀ anchor i₁ H s' v hDiv hMono hSync hCatch
    hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST (fun s h₁ _ => hInv s h₁) hOld (fun j u h₁ _
    h₂ => hCaches j u h₁ h₂) hs₀ hs hv

/-- An honest confirmation is on the honest chain.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `L`: the
  block. -/
theorem isHonestConfirmation_onHonestChain {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {s₀ : ℕ} {L : Block V}
    (h : IsHonestConfirmation S Sched x s₀ L) : OnHonestChain S Sched x s₀ L := by
  obtain ⟨s, hs, v, hv, hL⟩ := h
  exact ⟨s, hs, v, hv, L, hL, ancestorEq_refl L⟩

/-- **Step 6 of the inclusion: the proposal stays an ancestor of the confirmed tip.** For an honest
active validator `v` of a slot `s' ≥ q + 2`, honest one time after the support cutoff of slot
`s' + 1`, `B` is `v`'s confirmed tip right after that cutoff or an ancestor of it.

Why: `v`'s update of slot `s' + 1` saved a confirmation `C'` (`updater_saves_after_healing`), a
descendant of `B` or `B` (Lemma 81's chain), which no live lock vetoes (the lock invariant); so
the record is `C'` or a descendant; the confirmed tip is the record or the finalized block, which
then descends from the record.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `s'`: the slot; `B`: the proposal; `u₀`: an updater
  of slot `q + 2`; `v`: the validator.

Roots name blocks until `supportCutoff S (s' + 1) + 1`: `v`'s fork-choice root right after the
support cutoff of slot `s' + 1` (`proposer_root_on_chain`), and `updater_saves_after_healing` at
slot `s'`.

Caches up to `supportCutoff S (s' + 1) + 1`: `v`'s caches right after the support cutoff of slot
`s' + 1` (`proposer_root_on_chain_until`), and `updater_saves_after_healing_until`. -/
theorem proposal_ancestor_of_tip_after_update_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H q s' : ℕ) (B : Block V) (u₀ v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1) + 1))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time →
      x[j].time ≤ supportCutoff S (s' + 1) + 1 → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hLatest : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[j][u].st).A.latest_confirmed ∧
        (x[j][u].st).A.latest_confirmed ∈ (x[j][u].st).S.T)
    (hs₀q : s₀ ≤ q) (hs : x[i₁].time < slotStart S (q + 2)) (hqs : q + 2 ≤ s')
    (hSavedAll : ∀ u ∈ updaterAt S Sched (q + 2),
      (stateBefore x (supportCutoff S (q + 2 + 1) + 1) u).A.saved_confirmation (q + 2) = some B)
    (hu₀ : u₀ ∈ updaterAt S Sched (q + 2))
    (hv : v ∈ honestActiveAt S Sched s')
    (hvc1 : v ∉ Sched.adv (((supportCutoff S (s' + 1) + 1 : ℕ)) : Int)) :
    B.AncestorEq (confirmedOf (stateBefore x (supportCutoff S (s' + 1) + 1) v)) := by
  have hΔ := one_le_Δ S
  have hsq : slotStart S (q + 2) ≤ slotStart S s' := slotStart_mono S hqs
  have hv₂ : supportCutoff S (s' + 1) = voteTime S (s' + 1) + Δ S := supportCutoff_eq S (s' + 1)
  have hv₃ : voteTime S (s' + 1) = slotStart S (s' + 1) + Δ S := voteTime_eq S (s' + 1)
  have hss : slotStart S (s' + 1) = slotStart S s' + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hc2 : supportCutoff S (s' + 1 + 1) = voteTime S (s' + 1 + 1) + Δ S :=
    supportCutoff_eq S (s' + 1 + 1)
  have hv4 : voteTime S (s' + 1 + 1) = slotStart S (s' + 1 + 1) + Δ S := voteTime_eq S (s' + 1 + 1)
  have hss2 : slotStart S (s' + 1 + 1) = slotStart S (s' + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s' + 1), Nat.mul_add, Nat.mul_one]
  have hdw : dutyWindowStart S (s' + 1) ≤ slotStart S s' := dutyWindowStart_succ_le_slotStart S s'
  have hvU := honestActiveAt_subset_updaterAt S Sched s' hv
  have hvw := updaterAt_window S Sched s' v hMono hvU
  have hvc := hvw (supportCutoff S (s' + 1)) (by omega) le_rfl
  -- `v`'s update of slot `s' + 1` saved a confirmation `C'`, a descendant of `B` or `B`
  obtain ⟨C', hC'⟩ := updater_saves_after_healing_until S Sched x GST s₀ anchor i₁ H s' v hDiv
    hMono
    hSync hCatch (hRoots.mono (by omega)) hParent hOwner hU hAdvQ hSleepK hAnchor hGST
    (fun s h₁ _ => hInv s h₁)
    hOld
    (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃) (by omega) (by omega) hvU
  have hBC' : B.AncestorEq C' := by
    rcases Nat.lt_or_eq_of_le hqs with hlt | heq
    · exact (hChain (q + 2) s' u₀ v B C' (by omega) hqs hu₀ hvU (hSavedAll u₀ hu₀) hC').1 hlt
    · subst heq
      rw [hSavedAll v hvU] at hC'
      cases hC'
      exact ancestorEq_refl B
  -- every block of the chain before `s'` is `C'` or an ancestor of it
  have hBeforeLe : ∀ D : Block V, OnHonestChainBefore S Sched x s₀ s' D → D.AncestorEq C' := by
    intro D hD
    obtain ⟨s'', hs'', hs₀'', u, hu, C'', hC'', hDC''⟩ := hD
    exact ancestorEq_trans hDC'' ((hChain s'' s' u v C'' C' hs₀'' hs''.le hu hvU hC'' hC').1 hs'')
  -- the update, its record, and no veto
  have hAw := awakeSince_le_dutyWindowStart_b S Sched x (s' + 1) (supportCutoff S (s' + 1)) v hDiv
    hMono (by omega) (fun t h1 h2 => (hvw t h1 h2).1) hvc.2
  obtain ⟨A'', hUpd, hSv, -, -, hLc⟩ := update_state_of_duty S Sched x s' v hDiv hvc hAw
  have hA''C : A''.saved_confirmation s' = some C' := by rw [← hSv]; exact hC'
  have hNoVeto : live_lock_vetoes
      (expireLocks (stateBefore x (supportCutoff S (s' + 1)) v).A
        ((supportCutoff S (s' + 1) : ℕ) : Int))
      (fg_to_ac (stateBefore x (supportCutoff S (s' + 1)) v).S)
      ((supportCutoff S (s' + 1) : ℕ) : Int) C' = false := by
    apply GoldilocksCorrectness.Proofs.Routines.live_lock_vetoes_eq_false
    intro e he hlive
    refine live_locks_compatible_of_revocation S Sched x s' C' v hDiv hMono hvU
      (fun hA A₃ hrev e' he' hl' => ?_) e (Finset.mem_filter.1 he).1 hlive
    obtain ⟨D, hD, he'D⟩ := hLocks s' (by omega) v hA A₃ hrev e' he' hl'
    exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans he'D (hBeforeLe D hD)))
  have hBL : B.AncestorEq (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.latest_confirmed := by
    rw [hLc]
    rcases update_confirmation_latest_cases _ _ _ _ _ _ _ (Nat.add_one_ne_zero s') hUpd with
      ⟨hn, -⟩ | ⟨C₁, hC₁, ⟨hv', -⟩ | ⟨-, hadv⟩⟩
    · rw [Nat.add_sub_cancel, hA''C] at hn
      cases hn
    · rw [Nat.add_sub_cancel, hA''C] at hC₁
      cases hC₁
      rw [hNoVeto] at hv'
      cases hv'
    · rw [Nat.add_sub_cancel, hA''C] at hC₁
      cases hC₁
      rw [hadv]
      rcases advance_some (fg_to_ac (stateBefore x (supportCutoff S (s' + 1)) v).S)
          (expireLocks (stateBefore x (supportCutoff S (s' + 1)) v).A
            ((supportCutoff S (s' + 1) : ℕ) : Int)).latest_confirmed C' with
        ⟨-, hanc, ha⟩ | ⟨-, ha⟩
      · rw [ha]; exact ancestorEq_trans hBC' hanc
      · rw [ha]; exact hBC'
  -- the confirmed tip right after the update
  have h1c : 1 ≤ supportCutoff S (s' + 1) + 1 := by omega
  have htc := time_stepBefore_add_one x hDiv h1c
  have hvcj : v ∉ Sched.adv (x[stepBefore x (supportCutoff S (s' + 1) + 1)].time : Int) :=
    fun h => hvc1 (hMono _ _ (by omega) h)
  obtain ⟨hLh, hLT⟩ := hLatest (stepBefore x (supportCutoff S (s' + 1) + 1)) v (by omega) hvcj
  have hρ := proposer_root_on_chain_until S Sched x s₀ (s' + 1) i₁ H (supportCutoff S (s' + 1) + 1)
    v hDiv hMono hRoots hU hAdvQ hOld hCaches (by omega) (by omega) hvc1
  rw [fc_root_eq] at hρ
  have hFρ := F_ancestorEq_fc_root_of_stateBefore S Sched x (supportCutoff S (s' + 1) + 1) v
  unfold confirmedOf
  rcases ac_confirmed_cases (stateBefore x (supportCutoff S (s' + 1) + 1) v).A
      (fg_to_ac (stateBefore x (supportCutoff S (s' + 1) + 1) v).S) with ⟨-, h⟩ | ⟨hnot, h⟩
  · rw [h]; exact hBL
  · rw [h]
    have hFchain : OnHonestChain S Sched x s₀
        (stateBefore x (supportCutoff S (s' + 1) + 1) v).S.F := by
      obtain ⟨s'', -, hAt⟩ := onHonestChainBefore_of_ancestorEq S Sched x s₀ (s' + 1) hρ hFρ
      exact ⟨s'', hAt⟩
    rcases (compatible_iff _ _).1 (onHonestChain_compatible S Sched x s₀ _ _ hChain
        (isHonestConfirmation_onHonestChain hLh) hFchain) with h1 | h1
    · rw [fg_to_ac_F]; exact ancestorEq_trans hBL h1
    · exact absurd ((mem_fg_to_ac_tree _ _).2 ⟨hLT, h1⟩) hnot

/-- **Step 6 of the inclusion, on the chain before `s' + 1`: the proposal stays an ancestor of
the confirmed tip.** For an honest
active validator `v` of a slot `s' ≥ q + 2`, honest one time after the support cutoff of slot
`s' + 1`, `B` is `v`'s confirmed tip right after that cutoff or an ancestor of it.

Why: `v`'s update of slot `s' + 1` saved a confirmation `C'` (`updater_saves_after_healing`), a
descendant of `B` or `B` (Lemma 81's chain), which no live lock vetoes (the lock invariant); so
the record is `C'` or a descendant; the confirmed tip is the record or the finalized block, which
then descends from the record.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `s'`: the slot; `B`: the proposal; `u₀`: an updater
  of slot `q + 2`; `v`: the validator.

Roots name blocks until `supportCutoff S (s' + 1) + 1`: `v`'s fork-choice root right after the
support cutoff of slot `s' + 1` (`proposer_root_on_chain`), and `updater_saves_after_healing` at
slot `s'`.

Caches up to `supportCutoff S (s' + 1) + 1`: `v`'s caches right after the support cutoff of slot
`s' + 1` (`proposer_root_on_chain_until`), and `updater_saves_after_healing_until`.

On the chain before `s' + 1`, the invariant and the locks up to slot `s'`, the record on the chain
at a slot whose update ran by then: the proof compares confirmations of slots from `q + 2` to `s'`,
`v`'s record and its finalized block right after the support cutoff of slot `s' + 1`, both then on
the chain before `s' + 1`. -/
theorem proposal_ancestor_of_tip_after_update_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H q s' : ℕ) (B : Block V) (u₀ v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1) + 1))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀)
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s' + 1))
    (hInv : ∀ s : ℕ, s₀ < s → s ≤ s' →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → s ≤ s' → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time →
      x[j].time ≤ supportCutoff S (s' + 1) + 1 → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hLatest : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time →
      x[j].time ≤ supportCutoff S (s' + 1) + 1 → u ∉ Sched.adv (x[j].time : Int) →
      (∃ σ : ℕ, supportCutoff S (σ + 1) ≤ x[j].time ∧
        OnHonestChainAt S Sched x s₀ σ (x[j][u].st).A.latest_confirmed) ∧
        (x[j][u].st).A.latest_confirmed ∈ (x[j][u].st).S.T)
    (hs₀q : s₀ ≤ q) (hs : x[i₁].time < slotStart S (q + 2)) (hqs : q + 2 ≤ s')
    (hSavedAll : ∀ u ∈ updaterAt S Sched (q + 2),
      (stateBefore x (supportCutoff S (q + 2 + 1) + 1) u).A.saved_confirmation (q + 2) = some B)
    (hu₀ : u₀ ∈ updaterAt S Sched (q + 2))
    (hv : v ∈ honestActiveAt S Sched s')
    (hvc1 : v ∉ Sched.adv (((supportCutoff S (s' + 1) + 1 : ℕ)) : Int)) :
    B.AncestorEq (confirmedOf (stateBefore x (supportCutoff S (s' + 1) + 1) v)) := by
  have hΔ := one_le_Δ S
  have hsq : slotStart S (q + 2) ≤ slotStart S s' := slotStart_mono S hqs
  have hv₂ : supportCutoff S (s' + 1) = voteTime S (s' + 1) + Δ S := supportCutoff_eq S (s' + 1)
  have hv₃ : voteTime S (s' + 1) = slotStart S (s' + 1) + Δ S := voteTime_eq S (s' + 1)
  have hss : slotStart S (s' + 1) = slotStart S s' + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hc2 : supportCutoff S (s' + 1 + 1) = voteTime S (s' + 1 + 1) + Δ S :=
    supportCutoff_eq S (s' + 1 + 1)
  have hv4 : voteTime S (s' + 1 + 1) = slotStart S (s' + 1 + 1) + Δ S := voteTime_eq S (s' + 1 + 1)
  have hss2 : slotStart S (s' + 1 + 1) = slotStart S (s' + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s' + 1), Nat.mul_add, Nat.mul_one]
  have hdw : dutyWindowStart S (s' + 1) ≤ slotStart S s' := dutyWindowStart_succ_le_slotStart S s'
  have hvU := honestActiveAt_subset_updaterAt S Sched s' hv
  have hvw := updaterAt_window S Sched s' v hMono hvU
  have hvc := hvw (supportCutoff S (s' + 1)) (by omega) le_rfl
  -- `v`'s update of slot `s' + 1` saved a confirmation `C'`, a descendant of `B` or `B`
  obtain ⟨C', hC'⟩ := updater_saves_after_healing_until S Sched x GST s₀ anchor i₁ H s' v hDiv
    hMono
    hSync hCatch (hRoots.mono (by omega)) hParent hOwner hU hAdvQ hSleepK hAnchor hGST hInv
    hOld
    (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃) (by omega) (by omega) hvU
  have hBC' : B.AncestorEq C' := by
    rcases Nat.lt_or_eq_of_le hqs with hlt | heq
    · exact (hChain (q + 2) s' u₀ v B C' (by omega) hqs (Nat.lt_succ_self s') hu₀ hvU
        (hSavedAll u₀ hu₀) hC').1 hlt
    · subst heq
      rw [hSavedAll v hvU] at hC'
      cases hC'
      exact ancestorEq_refl B
  -- every block of the chain before `s'` is `C'` or an ancestor of it
  have hBeforeLe : ∀ D : Block V, OnHonestChainBefore S Sched x s₀ s' D → D.AncestorEq C' := by
    intro D hD
    obtain ⟨s'', hs'', hs₀'', u, hu, C'', hC'', hDC''⟩ := hD
    exact ancestorEq_trans hDC''
      ((hChain s'' s' u v C'' C' hs₀'' hs''.le (Nat.lt_succ_self s') hu hvU hC'' hC').1 hs'')
  -- the update, its record, and no veto
  have hAw := awakeSince_le_dutyWindowStart_b S Sched x (s' + 1) (supportCutoff S (s' + 1)) v hDiv
    hMono (by omega) (fun t h1 h2 => (hvw t h1 h2).1) hvc.2
  obtain ⟨A'', hUpd, hSv, -, -, hLc⟩ := update_state_of_duty S Sched x s' v hDiv hvc hAw
  have hA''C : A''.saved_confirmation s' = some C' := by rw [← hSv]; exact hC'
  have hNoVeto : live_lock_vetoes
      (expireLocks (stateBefore x (supportCutoff S (s' + 1)) v).A
        ((supportCutoff S (s' + 1) : ℕ) : Int))
      (fg_to_ac (stateBefore x (supportCutoff S (s' + 1)) v).S)
      ((supportCutoff S (s' + 1) : ℕ) : Int) C' = false := by
    apply GoldilocksCorrectness.Proofs.Routines.live_lock_vetoes_eq_false
    intro e he hlive
    refine live_locks_compatible_of_revocation S Sched x s' C' v hDiv hMono hvU
      (fun hA A₃ hrev e' he' hl' => ?_) e (Finset.mem_filter.1 he).1 hlive
    obtain ⟨D, hD, he'D⟩ := hLocks s' (by omega) le_rfl v hA A₃ hrev e' he' hl'
    exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans he'D (hBeforeLe D hD)))
  have hBL : B.AncestorEq (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.latest_confirmed := by
    rw [hLc]
    rcases update_confirmation_latest_cases _ _ _ _ _ _ _ (Nat.add_one_ne_zero s') hUpd with
      ⟨hn, -⟩ | ⟨C₁, hC₁, ⟨hv', -⟩ | ⟨-, hadv⟩⟩
    · rw [Nat.add_sub_cancel, hA''C] at hn
      cases hn
    · rw [Nat.add_sub_cancel, hA''C] at hC₁
      cases hC₁
      rw [hNoVeto] at hv'
      cases hv'
    · rw [Nat.add_sub_cancel, hA''C] at hC₁
      cases hC₁
      rw [hadv]
      rcases advance_some (fg_to_ac (stateBefore x (supportCutoff S (s' + 1)) v).S)
          (expireLocks (stateBefore x (supportCutoff S (s' + 1)) v).A
            ((supportCutoff S (s' + 1) : ℕ) : Int)).latest_confirmed C' with
        ⟨-, hanc, ha⟩ | ⟨-, ha⟩
      · rw [ha]; exact ancestorEq_trans hBC' hanc
      · rw [ha]; exact hBC'
  -- the confirmed tip right after the update
  have h1c : 1 ≤ supportCutoff S (s' + 1) + 1 := by omega
  have htc := time_stepBefore_add_one x hDiv h1c
  have hvcj : v ∉ Sched.adv (x[stepBefore x (supportCutoff S (s' + 1) + 1)].time : Int) :=
    fun h => hvc1 (hMono _ _ (by omega) h)
  obtain ⟨⟨σL, hσL, hLh⟩, hLT⟩ := hLatest (stepBefore x (supportCutoff S (s' + 1) + 1)) v (by omega)
    (by omega) hvcj
  have hρ := proposer_root_on_chain_until S Sched x s₀ (s' + 1) i₁ H (supportCutoff S (s' + 1) + 1)
    v hDiv hMono hRoots hU hAdvQ hOld hCaches (by omega) (by omega) hvc1
  rw [fc_root_eq] at hρ
  have hFρ := F_ancestorEq_fc_root_of_stateBefore S Sched x (supportCutoff S (s' + 1) + 1) v
  unfold confirmedOf
  rcases ac_confirmed_cases (stateBefore x (supportCutoff S (s' + 1) + 1) v).A
      (fg_to_ac (stateBefore x (supportCutoff S (s' + 1) + 1) v).S) with ⟨-, h⟩ | ⟨hnot, h⟩
  · rw [h]; exact hBL
  · rw [h]
    have hFchain : OnHonestChainBefore S Sched x s₀ (s' + 1)
        (stateBefore x (supportCutoff S (s' + 1) + 1) v).S.F :=
      onHonestChainBefore_of_ancestorEq S Sched x s₀ (s' + 1) hρ hFρ
    have hLchain : OnHonestChainBefore S Sched x s₀ (s' + 1)
        (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.latest_confirmed :=
      ⟨σL, Nat.lt_succ_of_le ((slot_le_of_supportCutoff_lt S σL s').2.2 (by omega)), hLh⟩
    rcases (compatible_iff _ _).1 (onHonestChainBefore_compatible S Sched x s₀ (s' + 1) _ _ hChain
        hLchain hFchain) with h1 | h1
    · rw [fg_to_ac_F]; exact ancestorEq_trans hBL h1
    · exact absurd ((mem_fg_to_ac_tree _ _).2 ⟨hLT, h1⟩) hnot

/-- **Step 6 of the inclusion: the proposal stays an ancestor of the confirmed tip.** For an honest
active validator `v` of a slot `s' ≥ q + 2`, honest one time after the support cutoff of slot
`s' + 1`, `B` is `v`'s confirmed tip right after that cutoff or an ancestor of it.

Why: `v`'s update of slot `s' + 1` saved a confirmation `C'` (`updater_saves_after_healing`), a
descendant of `B` or `B` (Lemma 81's chain), which no live lock vetoes (the lock invariant); so
the record is `C'` or a descendant; the confirmed tip is the record or the finalized block, which
then descends from the record.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `s'`: the slot; `B`: the proposal; `u₀`: an updater
  of slot `q + 2`; `v`: the validator.

Roots name blocks until `supportCutoff S (s' + 1) + 1`: `v`'s fork-choice root right after the
support cutoff of slot `s' + 1` (`proposer_root_on_chain`), and `updater_saves_after_healing` at
slot `s'`.

It is `proposal_ancestor_of_tip_after_update_until`
with the caches restricted to the steps it reads. -/
theorem proposal_ancestor_of_tip_after_update (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H q s' : ℕ) (B : Block V) (u₀ v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1) + 1))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hLatest : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[j][u].st).A.latest_confirmed ∧
        (x[j][u].st).A.latest_confirmed ∈ (x[j][u].st).S.T)
    (hs₀q : s₀ ≤ q) (hs : x[i₁].time < slotStart S (q + 2)) (hqs : q + 2 ≤ s')
    (hSavedAll : ∀ u ∈ updaterAt S Sched (q + 2),
      (stateBefore x (supportCutoff S (q + 2 + 1) + 1) u).A.saved_confirmation (q + 2) = some B)
    (hu₀ : u₀ ∈ updaterAt S Sched (q + 2))
    (hv : v ∈ honestActiveAt S Sched s')
    (hvc1 : v ∉ Sched.adv (((supportCutoff S (s' + 1) + 1 : ℕ)) : Int)) :
    B.AncestorEq (confirmedOf (stateBefore x (supportCutoff S (s' + 1) + 1) v)) :=
  proposal_ancestor_of_tip_after_update_until S Sched x GST s₀ anchor i₁ H q s' B u₀ v hDiv hMono
    hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST hChain hInv hLocks hOld
    (fun j u h₁ _ h₂ => hCaches j u h₁ h₂) hLatest hs₀q hs hqs hSavedAll hu₀ hv hvc1

/-! ## The export and the inclusion -/

/-- `lem90_included_update_facts` at the slot `q + 2`, with the lock invariant at slot `q` (`hLk`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the
  proposal; `v`: the updater.

Roots name blocks until `supportCutoff S (q + 2 + 1)`: `honest_proposal_saved`.

Caches up to `supportCutoff S (q + 2 + 1)`: `honest_proposal_saved_until`. -/
theorem included_update_facts_q_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (q + 2 + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀)
    (hChain : ConfirmationsChainBefore S Sched x s₀ (q + 1))
    (hInv : ∀ s : ℕ, s₀ < s → s ≤ q + 2 →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → s ≤ q + 2 → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ supportCutoff S (q + 2 + 1) →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (hs₀q : s₀ ≤ q) (hs : x[i₁].time < slotStart S (q + 2))
    (hLk : ∀ u ∈ honestActiveAt S Sched q,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (q + 1)) q u)
    (hp : ∀ t : ℕ, proposalWindowStart S (q + 2) ≤ t → t ≤ supportCutoff S (q + 2 + 1) →
      S.P.proposer (q + 2) ∈ Sched.awake (t : Int) ∧ S.P.proposer (q + 2) ∉ Sched.adv (t : Int))
    (hl : x.lbl ip = AtomicAction.tickAllAwake (slotStart S (q + 2)))
    (hsent : (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x[ip + 1].sent - x[ip].sent)
    (hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (q + 2)) (S.P.proposer (q + 2))).S.T,
      B'.root ≠ B.root)
    (hv : v ∈ updaterAt S Sched (q + 2)) :
    ∃ A' : ACState V,
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (q + 2 + 1)) v).A
          ((supportCutoff S (q + 2 + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (q + 2 + 1)) v).S)
        ((supportCutoff S (q + 2 + 1) : ℕ) : Int) (q + 2 + 1) = .ok A' ∧
      A'.saved_confirmation (q + 2) = some B ∧
      B ∈ A'.fast_blocks ∧
      LockEntry.mk B (S.C.t_ (q + 2 + S.C.k) + 5 * S.C.Δ) ∈ A'.lock_entries ∧
      (∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (supportCutoff S (q + 2 + 1)) v).S)
          ((supportCutoff S (q + 2 + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
      A'.latest_confirmed = B ∧
      (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.saved_confirmation =
        A'.saved_confirmation ∧
      (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.fast_blocks = A'.fast_blocks ∧
      (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.lock_entries = A'.lock_entries ∧
      (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.latest_confirmed =
        A'.latest_confirmed := by
  have hΔ := one_le_Δ S
  obtain ⟨-, hBslot, -, hBase, hSavedAll, hFrame, hFast⟩ := honest_proposal_saved_until S Sched x
    GST s₀
    anchor i₁ H q ip B hDiv hMono hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK
    hAnchor hGST hChain hInv hLocks hOld hCaches ht₀ hs₀q hs hLk hp hl hsent hRootNew
  have hdw : dutyWindowStart S (q + 2 + 1) ≤ slotStart S (q + 2) :=
    dutyWindowStart_succ_le_slotStart S (q + 2)
  have hc := supportCutoff_eq S (q + 2 + 1)
  have hvt := voteTime_eq S (q + 2 + 1)
  have hss : slotStart S (q + 2 + 1) = slotStart S (q + 2) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (q + 2), Nat.mul_add, Nat.mul_one]
  have hvw := updaterAt_window S Sched (q + 2) v hMono hv
  have hvc := hvw (supportCutoff S (q + 2 + 1)) (by omega) le_rfl
  have hAw := awakeSince_le_dutyWindowStart_b S Sched x (q + 2 + 1) (supportCutoff S (q + 2 + 1)) v
    hDiv hMono (by omega) (fun t h1 h2 => (hvw t h1 h2).1) hvc.2
  obtain ⟨A'', hUpdC, hSv, hFb, hLe, hLc⟩ := update_state_of_duty S Sched x (q + 2) v hDiv
    hvc hAw
  have hSaved : A''.saved_confirmation (q + 2) = some B := by rw [← hSv]; exact hSavedAll v hv
  refine ⟨A'', hUpdC, hSaved, by rw [← hFb]; exact (hFast v hv).1,
    by rw [← hLe]; exact (hFast v hv).2, ?_, ?_, hSv, hFb, hLe, hLc⟩
  · exact update_lock_entries_ancestorEq S Sched x (q + 2) B v A'' hDiv hMono hvw hUpdC
      hSaved hBslot (fun A₃ hrev e he hl => (compatible_iff _ _).2
        (Or.inl ((hFrame v hv).2.2 A₃ hrev e he hl)))
  · rw [← hLc]
    exact latest_confirmed_after_healed_update S Sched x (q + 2) B v hDiv hMono
      (by rw [hBslot]) hBase hSavedAll hv

/-- `lem90_included_update_facts` at the slot `q + 2`, with the lock invariant at slot `q` (`hLk`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the
  proposal; `v`: the updater.

Roots name blocks until `supportCutoff S (q + 2 + 1)`: `honest_proposal_saved`.

It is `included_update_facts_q_until` with the caches restricted to the steps it reads. -/
theorem included_update_facts_q (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (q + 2 + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (hs₀q : s₀ ≤ q) (hs : x[i₁].time < slotStart S (q + 2))
    (hLk : ∀ u ∈ honestActiveAt S Sched q,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (q + 1)) q u)
    (hp : ∀ t : ℕ, proposalWindowStart S (q + 2) ≤ t → t ≤ supportCutoff S (q + 2 + 1) →
      S.P.proposer (q + 2) ∈ Sched.awake (t : Int) ∧ S.P.proposer (q + 2) ∉ Sched.adv (t : Int))
    (hl : x.lbl ip = AtomicAction.tickAllAwake (slotStart S (q + 2)))
    (hsent : (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x[ip + 1].sent - x[ip].sent)
    (hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (q + 2)) (S.P.proposer (q + 2))).S.T,
      B'.root ≠ B.root)
    (hv : v ∈ updaterAt S Sched (q + 2)) :
    ∃ A' : ACState V,
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (q + 2 + 1)) v).A
          ((supportCutoff S (q + 2 + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (q + 2 + 1)) v).S)
        ((supportCutoff S (q + 2 + 1) : ℕ) : Int) (q + 2 + 1) = .ok A' ∧
      A'.saved_confirmation (q + 2) = some B ∧
      B ∈ A'.fast_blocks ∧
      LockEntry.mk B (S.C.t_ (q + 2 + S.C.k) + 5 * S.C.Δ) ∈ A'.lock_entries ∧
      (∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (supportCutoff S (q + 2 + 1)) v).S)
          ((supportCutoff S (q + 2 + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
      A'.latest_confirmed = B ∧
      (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.saved_confirmation =
        A'.saved_confirmation ∧
      (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.fast_blocks = A'.fast_blocks ∧
      (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.lock_entries = A'.lock_entries ∧
      (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.latest_confirmed =
        A'.latest_confirmed :=
  included_update_facts_q_until S Sched x GST s₀ anchor i₁ H q ip B v hDiv hMono hSync hCatch
    hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST (confirmationsChainBefore_of_chain S Sched x
    s₀ _ hChain) (fun s h₁ _ => hInv s h₁) (fun s h₁ _ => hLocks s h₁) hOld (fun j u h₁ _ h₂ =>
    hCaches j u h₁ h₂) ht₀ hs₀q hs hLk hp hl hsent hRootNew hv

/-- `ConfirmedIncludedBetween`'s claim at the slot `q + 2`, with the lock invariant at slot `q`
(`hLk`): `included_q` with the support cutoff of slot `q + 3` at most `t` and the confirmed tips
read at steps at times at most `t`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `t`: the time up to which the confirmed tips are read.

Roots name blocks until `t`: the update of slot `q + 2` at the support cutoff of slot `q + 3`, at
most `t`, and, at a later slot `s'`, blocks held up to `supportCutoff S (s' + 1) + 1`, at most the
time of the step read, at most `t` (`proposal_ancestor_of_tip_after_update`).

Caches up to `t`, with the roots: the caches are read at the steps the proof reads, at times at
most `t`. Named `_upTo`, since `included_q_until` is the landed form bounded in its roots only. -/
theorem included_q_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H q t : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ t →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (hs₀q : s₀ ≤ q) (hs : x[i₁].time < slotStart S (q + 2))
    -- the update of slot `q + 2` is at most `t`
    (hqt : supportCutoff S (q + 2 + 1) ≤ t)
    (hLk : ∀ u ∈ honestActiveAt S Sched q,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (q + 1)) q u)
    (hp : ∀ t : ℕ, proposalWindowStart S (q + 2) ≤ t → t ≤ supportCutoff S (q + 2 + 1) →
      S.P.proposer (q + 2) ∈ Sched.awake (t : Int) ∧ S.P.proposer (q + 2) ∉ Sched.adv (t : Int))
    (hLatest : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[j][u].st).A.latest_confirmed ∧
        (x[j][u].st).A.latest_confirmed ∈ (x[j][u].st).S.T) :
    (∃ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S (q + 2)) ∧
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent) ∧
    ∀ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S (q + 2)) →
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent →
      RootCollisionAtProposal S Sched x (q + 2) B ∨
      ((∀ v ∈ honestActiveAt S Sched (q + 2),
        (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.saved_confirmation (q + 2) =
          some B ∧
        confirmedOf (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v) = B) ∧
      (∀ (v : V) (j s' : ℕ), HonestThrough x j v → q + 2 ≤ s' → v ∈ honestActiveAt S Sched s' →
        supportCutoff S (s' + 1) < x[j].time → x[j].time ≤ t →
        B.AncestorEq (confirmedOf (x[j][v].st)))) := by
  have hΔ := one_le_Δ S
  have hc := supportCutoff_eq S (q + 2 + 1)
  have hvt := voteTime_eq S (q + 2 + 1)
  have hss : slotStart S (q + 2 + 1) = slotStart S (q + 2) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (q + 2), Nat.mul_add, Nat.mul_one]
  refine ⟨honest_proposer_proposes S Sched x q hDiv hMono
    (fun t h1 h2 => hp t h1 (by omega)), fun ip B hl hsent => ?_⟩
  by_cases hcol : RootCollisionAtProposal S Sched x (q + 2) B
  · exact Or.inl hcol
  right
  have hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (q + 2)) (S.P.proposer (q + 2))).S.T,
      B'.root ≠ B.root := fun B' hB' hr => hcol ⟨B', hB', hr⟩
  obtain ⟨hChainLeB, hBslot, -, hBase, hSavedAll, -, -⟩ := honest_proposal_saved_until S Sched x
    GST s₀ anchor i₁ H q ip B hDiv hMono hSync hCatch
    (hRoots.mono hqt) hParent hOwner hU hAdvQ hSleepK
    hAnchor hGST (confirmationsChainBefore_of_chain S Sched x s₀ _ hChain) (fun s h₁ _ => hInv s h₁)
    (fun s h₁ _ => hLocks s h₁) hOld
    (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃) ht₀ hs₀q hs hLk hp hl hsent
    hRootNew
  -- every block of the chain before `q + 3` is `B` or an ancestor of `B`
  have hChainLeB3 : ∀ C : Block V, OnHonestChainBefore S Sched x s₀ (q + 2 + 1) C →
      C.AncestorEq B := by
    intro C hC
    obtain ⟨s'', hs'', hs₀'', u, hu, C'', hC'', hCC''⟩ := hC
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hs'') with hlt | heq
    · exact hChainLeB C ⟨s'', hlt, hs₀'', u, hu, C'', hC'', hCC''⟩
    · subst heq
      rw [hSavedAll u hu] at hC''
      cases hC''
      exact hCC''
  refine ⟨fun v hvA => ?_, fun v j s' hHon hqs hvA hlt hjt => ?_⟩
  · -- right after the update of slot `q + 2`, the record and the confirmed tip are `B`
    have hvU := honestActiveAt_subset_updaterAt S Sched (q + 2) hvA
    have hLc := latest_confirmed_after_healed_update S Sched x (q + 2) B v hDiv hMono
      (by rw [hBslot]) hBase hSavedAll hvU
    refine ⟨hSavedAll v hvU, ?_⟩
    have hvw := honestActiveAt_window S Sched (q + 2) v hMono hvA
    have h1c : 1 ≤ supportCutoff S (q + 2 + 1) + 1 := by omega
    have htc := time_stepBefore_add_one x hDiv h1c
    have hvcj : v ∉ Sched.adv (x[stepBefore x (supportCutoff S (q + 2 + 1) + 1)].time : Int) := by
      have := (hvw (supportCutoff S (q + 2 + 1))
        (dutyWindowStart_le_supportCutoff S (by omega)) le_rfl).2
      rw [show x[stepBefore x (supportCutoff S (q + 2 + 1) + 1)].time =
        supportCutoff S (q + 2 + 1) by omega]
      exact this
    have hLT := (hLatest _ v (by omega) hvcj).2
    have hρ := lem91f_voter_root_on_chain_before_until S Sched x s₀ i₁
      (stepBefore x (supportCutoff S (q + 2 + 1) + 1)) (q + 2 + 1) H v hDiv hMono
      (hRoots.mono (by omega)) hU hAdvQ
      hOld (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃) (by omega)
      hvcj (fun s_a hsa =>
        Nat.lt_succ_of_le ((slot_le_of_supportCutoff_lt S s_a (q + 2)).2.2 (by omega)))
    rw [fc_root_eq] at hρ
    have hFB : (x[stepBefore x (supportCutoff S (q + 2 + 1) + 1)][v].st).S.F.AncestorEq B :=
      ancestorEq_trans (F_ancestorEq_fc_root_of_exec S Sched x _ v) (hChainLeB3 _ hρ)
    unfold confirmedOf
    have hst : stateBefore x (supportCutoff S (q + 2 + 1) + 1) v =
        x[stepBefore x (supportCutoff S (q + 2 + 1) + 1)][v].st := rfl
    rw [hst] at hLc ⊢
    rcases ac_confirmed_cases (x[stepBefore x (supportCutoff S (q + 2 + 1) + 1)][v].st).A
        (fg_to_ac (x[stepBefore x (supportCutoff S (q + 2 + 1) + 1)][v].st).S) with
      ⟨-, h⟩ | ⟨hnot, -⟩
    · rw [h, hLc]
    · rw [hLc] at hnot hLT
      exact absurd ((mem_fg_to_ac_tree _ _).2 ⟨hLT, hFB⟩) hnot
  · -- later: the confirmed tip right after the update of slot `s'` descends from `B`, and grows
    have h88 := lem88_counting_of_committeeSleepiness S Sched x anchor (q + 2) v
      (slotStart S (q + 2)) hSleepK (by omega)
    obtain ⟨u₀, hu₀⟩ : (honestActiveAt S Sched (q + 2) ∩ S.P.committee (q + 2)).Nonempty :=
      Finset.card_pos.1 (by omega)
    have hu₀U := honestActiveAt_subset_updaterAt S Sched (q + 2) (Finset.mem_inter.1 hu₀).1
    have h1c : 1 ≤ supportCutoff S (s' + 1) + 1 := by omega
    have htc := time_stepBefore_add_one x hDiv h1c
    have hvc1 : v ∉ Sched.adv (((supportCutoff S (s' + 1) + 1 : ℕ)) : Int) :=
      hHon _ (by exact_mod_cast (show supportCutoff S (s' + 1) + 1 ≤ x[j].time by omega))
    have hB0 := proposal_ancestor_of_tip_after_update_until S Sched x GST s₀ anchor i₁ H q s' B u₀ v
      hDiv
      hMono hSync hCatch (hRoots.mono (by omega)) hParent hOwner
      hU hAdvQ hSleepK hAnchor hGST hChain hInv
      hLocks hOld
      (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃) hLatest hs₀q hs hqs hSavedAll hu₀U hvA
      hvc1
    have hj₀j : stepBefore x (supportCutoff S (s' + 1) + 1) ≤ j :=
      (lt_of_time_lt x (by omega)).le
    have hsq : slotStart S (q + 2) ≤ slotStart S s' := slotStart_mono S hqs
    have hcs := supportCutoff_eq S (s' + 1)
    have hvs := voteTime_eq S (s' + 1)
    have hss' : slotStart S (s' + 1) = slotStart S s' + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq S s', Nat.mul_add, Nat.mul_one]
    have hmono := (GoldilocksCorrectness.Proofs.View.confirmedMonotoneBetween_unfold x _ _).1
      (lem90_confirmed_monotone_until S Sched x s₀ H i₁ t hChain hLatest hCaches) v _ j hj₀j hHon
      (by omega) hjt
    exact ancestorEq_trans hB0 hmono

/-- `ConfirmedIncludedBetween`'s claim at the slot `q + 2`, with the lock invariant at slot `q`
(`hLk`), on the chain before the slots whose update is at most `t`: `included_q` with the support
cutoff of slot `q + 3` at most `t` and the confirmed tips read at steps at times at most `t`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `t`: the time up to which the confirmed tips are read.

Roots name blocks until `t`: the update of slot `q + 2` at the support cutoff of slot `q + 3`, at
most `t`, and, at a later slot `s'`, blocks held up to `supportCutoff S (s' + 1) + 1`, at most the
time of the step read, at most `t` (`proposal_ancestor_of_tip_after_update`).

Caches up to `t`, with the roots: the caches are read at the steps the proof reads, at times at
most `t`. Named `_upTo`, since `included_q_until` is the landed form bounded in its roots only. -/
theorem included_q_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H q t : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀)
    (hChain : ∀ σ : ℕ, supportCutoff S (σ + 1) ≤ t →
      ConfirmationsChainBefore S Sched x s₀ (σ + 1))
    (hInv : ∀ s : ℕ, s₀ < s → supportCutoff S (s + 1) ≤ t →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → supportCutoff S (s + 1) ≤ t → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ t →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (hs₀q : s₀ ≤ q) (hs : x[i₁].time < slotStart S (q + 2))
    -- the update of slot `q + 2` is at most `t`
    (hqt : supportCutoff S (q + 2 + 1) ≤ t)
    (hLk : ∀ u ∈ honestActiveAt S Sched q,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (q + 1)) q u)
    (hp : ∀ t : ℕ, proposalWindowStart S (q + 2) ≤ t → t ≤ supportCutoff S (q + 2 + 1) →
      S.P.proposer (q + 2) ∈ Sched.awake (t : Int) ∧ S.P.proposer (q + 2) ∉ Sched.adv (t : Int))
    (hLatest : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ t →
      u ∉ Sched.adv (x[j].time : Int) → (∃ σ : ℕ, supportCutoff S (σ + 1) ≤ x[j].time ∧
        OnHonestChainAt S Sched x s₀ σ (x[j][u].st).A.latest_confirmed) ∧
        (x[j][u].st).A.latest_confirmed ∈ (x[j][u].st).S.T) :
    (∃ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S (q + 2)) ∧
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent) ∧
    ∀ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S (q + 2)) →
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent →
      RootCollisionAtProposal S Sched x (q + 2) B ∨
      ((∀ v ∈ honestActiveAt S Sched (q + 2),
        (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.saved_confirmation (q + 2) =
          some B ∧
        confirmedOf (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v) = B) ∧
      (∀ (v : V) (j s' : ℕ), HonestThrough x j v → q + 2 ≤ s' → v ∈ honestActiveAt S Sched s' →
        supportCutoff S (s' + 1) < x[j].time → x[j].time ≤ t →
        B.AncestorEq (confirmedOf (x[j][v].st)))) := by
  have hΔ := one_le_Δ S
  have hc := supportCutoff_eq S (q + 2 + 1)
  have hvt := voteTime_eq S (q + 2 + 1)
  have hss : slotStart S (q + 2 + 1) = slotStart S (q + 2) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (q + 2), Nat.mul_add, Nat.mul_one]
  refine ⟨honest_proposer_proposes S Sched x q hDiv hMono
    (fun t h1 h2 => hp t h1 (by omega)), fun ip B hl hsent => ?_⟩
  by_cases hcol : RootCollisionAtProposal S Sched x (q + 2) B
  · exact Or.inl hcol
  right
  have hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (q + 2)) (S.P.proposer (q + 2))).S.T,
      B'.root ≠ B.root := fun B' hB' hr => hcol ⟨B', hB', hr⟩
  obtain ⟨hChainLeB, hBslot, -, hBase, hSavedAll, -, -⟩ := honest_proposal_saved_until S Sched x
    GST s₀ anchor i₁ H q ip B hDiv hMono hSync hCatch
    (hRoots.mono hqt) hParent hOwner hU hAdvQ hSleepK
    hAnchor hGST (hChain q (le_trans (supportCutoff_le_of_le S (by omega)) hqt))
    (fun s h₁ h₂ => hInv s h₁ (le_trans (supportCutoff_le_of_le S (by omega)) hqt))
    (fun s h₁ h₂ => hLocks s h₁ (le_trans (supportCutoff_le_of_le S (by omega)) hqt)) hOld
    (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃) ht₀ hs₀q hs hLk hp hl hsent
    hRootNew
  -- every block of the chain before `q + 3` is `B` or an ancestor of `B`
  have hChainLeB3 : ∀ C : Block V, OnHonestChainBefore S Sched x s₀ (q + 2 + 1) C →
      C.AncestorEq B := by
    intro C hC
    obtain ⟨s'', hs'', hs₀'', u, hu, C'', hC'', hCC''⟩ := hC
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hs'') with hlt | heq
    · exact hChainLeB C ⟨s'', hlt, hs₀'', u, hu, C'', hC'', hCC''⟩
    · subst heq
      rw [hSavedAll u hu] at hC''
      cases hC''
      exact hCC''
  refine ⟨fun v hvA => ?_, fun v j s' hHon hqs hvA hlt hjt => ?_⟩
  · -- right after the update of slot `q + 2`, the record and the confirmed tip are `B`
    have hvU := honestActiveAt_subset_updaterAt S Sched (q + 2) hvA
    have hLc := latest_confirmed_after_healed_update S Sched x (q + 2) B v hDiv hMono
      (by rw [hBslot]) hBase hSavedAll hvU
    refine ⟨hSavedAll v hvU, ?_⟩
    have hvw := honestActiveAt_window S Sched (q + 2) v hMono hvA
    have h1c : 1 ≤ supportCutoff S (q + 2 + 1) + 1 := by omega
    have htc := time_stepBefore_add_one x hDiv h1c
    have hvcj : v ∉ Sched.adv (x[stepBefore x (supportCutoff S (q + 2 + 1) + 1)].time : Int) := by
      have := (hvw (supportCutoff S (q + 2 + 1))
        (dutyWindowStart_le_supportCutoff S (by omega)) le_rfl).2
      rw [show x[stepBefore x (supportCutoff S (q + 2 + 1) + 1)].time =
        supportCutoff S (q + 2 + 1) by omega]
      exact this
    have hLT := (hLatest _ v (by omega) (by omega) hvcj).2
    have hρ := lem91f_voter_root_on_chain_before_until S Sched x s₀ i₁
      (stepBefore x (supportCutoff S (q + 2 + 1) + 1)) (q + 2 + 1) H v hDiv hMono
      (hRoots.mono (by omega)) hU hAdvQ
      hOld (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃) (by omega)
      hvcj (fun s_a hsa =>
        Nat.lt_succ_of_le ((slot_le_of_supportCutoff_lt S s_a (q + 2)).2.2 (by omega)))
    rw [fc_root_eq] at hρ
    have hFB : (x[stepBefore x (supportCutoff S (q + 2 + 1) + 1)][v].st).S.F.AncestorEq B :=
      ancestorEq_trans (F_ancestorEq_fc_root_of_exec S Sched x _ v) (hChainLeB3 _ hρ)
    unfold confirmedOf
    have hst : stateBefore x (supportCutoff S (q + 2 + 1) + 1) v =
        x[stepBefore x (supportCutoff S (q + 2 + 1) + 1)][v].st := rfl
    rw [hst] at hLc ⊢
    rcases ac_confirmed_cases (x[stepBefore x (supportCutoff S (q + 2 + 1) + 1)][v].st).A
        (fg_to_ac (x[stepBefore x (supportCutoff S (q + 2 + 1) + 1)][v].st).S) with
      ⟨-, h⟩ | ⟨hnot, -⟩
    · rw [h, hLc]
    · rw [hLc] at hnot hLT
      exact absurd ((mem_fg_to_ac_tree _ _).2 ⟨hLT, hFB⟩) hnot
  · -- later: the confirmed tip right after the update of slot `s'` descends from `B`, and grows
    have h88 := lem88_counting_of_committeeSleepiness S Sched x anchor (q + 2) v
      (slotStart S (q + 2)) hSleepK (by omega)
    obtain ⟨u₀, hu₀⟩ : (honestActiveAt S Sched (q + 2) ∩ S.P.committee (q + 2)).Nonempty :=
      Finset.card_pos.1 (by omega)
    have hu₀U := honestActiveAt_subset_updaterAt S Sched (q + 2) (Finset.mem_inter.1 hu₀).1
    have h1c : 1 ≤ supportCutoff S (s' + 1) + 1 := by omega
    have htc := time_stepBefore_add_one x hDiv h1c
    have hvc1 : v ∉ Sched.adv (((supportCutoff S (s' + 1) + 1 : ℕ)) : Int) :=
      hHon _ (by exact_mod_cast (show supportCutoff S (s' + 1) + 1 ≤ x[j].time by omega))
    have hcs' : supportCutoff S (s' + 1) ≤ t := by omega
    have hB0 := proposal_ancestor_of_tip_after_update_before S Sched x GST s₀ anchor i₁ H q s' B u₀
      v
      hDiv
      hMono hSync hCatch (hRoots.mono (by omega)) hParent hOwner
      hU hAdvQ hSleepK hAnchor hGST (hChain s' hcs')
      (fun s h₁ h₂ => hInv s h₁ (le_trans (supportCutoff_le_of_le S (by omega)) hcs'))
      (fun s h₁ h₂ => hLocks s h₁ (le_trans (supportCutoff_le_of_le S (by omega)) hcs')) hOld
      (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃)
      (fun k u h₁ h₂ h₃ => hLatest k u h₁ (by omega) h₃) hs₀q hs hqs hSavedAll hu₀U hvA
      hvc1
    have hj₀j : stepBefore x (supportCutoff S (s' + 1) + 1) ≤ j :=
      (lt_of_time_lt x (by omega)).le
    have hsq : slotStart S (q + 2) ≤ slotStart S s' := slotStart_mono S hqs
    have hcs := supportCutoff_eq S (s' + 1)
    have hvs := voteTime_eq S (s' + 1)
    have hss' : slotStart S (s' + 1) = slotStart S s' + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq S s', Nat.mul_add, Nat.mul_one]
    have hmono := (GoldilocksCorrectness.Proofs.View.confirmedMonotoneBetween_unfold x _ _).1
      (lem90_confirmed_monotone_before S Sched x s₀ H i₁ t hDiv hMono hRoots hU hAdvQ hOld hChain
        hLatest hCaches) v _ j hj₀j hHon (by omega) hjt
    exact ancestorEq_trans hB0 hmono

/-- `ConfirmedIncludedBetween`'s claim at the slot `q + 2`, with the lock invariant at slot `q`
(`hLk`): `included_q` with the support cutoff of slot `q + 3` at most `t` and the confirmed tips
read at steps at times at most `t`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `t`: the time up to which the confirmed tips are read.

Roots name blocks until `t`: the update of slot `q + 2` at the support cutoff of slot `q + 3`, at
most `t`, and, at a later slot `s'`, blocks held up to `supportCutoff S (s' + 1) + 1`, at most the
time of the step read, at most `t` (`proposal_ancestor_of_tip_after_update`).

It is `included_q_upTo` with the caches restricted to the steps it reads. -/
theorem included_q_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H q t : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (hs₀q : s₀ ≤ q) (hs : x[i₁].time < slotStart S (q + 2))
    -- the update of slot `q + 2` is at most `t`
    (hqt : supportCutoff S (q + 2 + 1) ≤ t)
    (hLk : ∀ u ∈ honestActiveAt S Sched q,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (q + 1)) q u)
    (hp : ∀ t : ℕ, proposalWindowStart S (q + 2) ≤ t → t ≤ supportCutoff S (q + 2 + 1) →
      S.P.proposer (q + 2) ∈ Sched.awake (t : Int) ∧ S.P.proposer (q + 2) ∉ Sched.adv (t : Int))
    (hLatest : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[j][u].st).A.latest_confirmed ∧
        (x[j][u].st).A.latest_confirmed ∈ (x[j][u].st).S.T) :
    (∃ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S (q + 2)) ∧
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent) ∧
    ∀ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S (q + 2)) →
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent →
      RootCollisionAtProposal S Sched x (q + 2) B ∨
      ((∀ v ∈ honestActiveAt S Sched (q + 2),
        (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.saved_confirmation (q + 2) =
          some B ∧
        confirmedOf (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v) = B) ∧
      (∀ (v : V) (j s' : ℕ), HonestThrough x j v → q + 2 ≤ s' → v ∈ honestActiveAt S Sched s' →
        supportCutoff S (s' + 1) < x[j].time → x[j].time ≤ t →
        B.AncestorEq (confirmedOf (x[j][v].st)))) :=
  included_q_upTo S Sched x GST s₀ anchor i₁ H q t hDiv hMono hSync hCatch hRoots hParent
    hOwner hU hAdvQ hSleepK hAnchor hGST hChain hInv hLocks hOld (fun j u h₁ _ h₂ => hCaches j u h₁
    h₂) ht₀ hs₀q hs hqt hLk hp hLatest

/-- `ConfirmedIncludedAfterHealing`'s claim at the slot `q + 2`, with the lock invariant at slot `q`
(`hLk`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`.

Roots name blocks among everything honest validators hold (`RootsNameBlocks`, not bounded): the
conclusion's last clause is for every slot `s' ≥ q + 2` and every later step, and at slot `s'` the
proof reads blocks held up to `supportCutoff S (s' + 1) + 1`
(`proposal_ancestor_of_tip_after_update`), so no time in the theorem's own parameters bounds the
reading. It is `included_q_until` read at every time `t`: the support cutoff of slot
`q + 3` for the first parts, and the later of that and the time of the step read for the last. -/
theorem included_q (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H q : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocks S Sched x)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (hs₀q : s₀ ≤ q) (hs : x[i₁].time < slotStart S (q + 2))
    (hLk : ∀ u ∈ honestActiveAt S Sched q,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (q + 1)) q u)
    (hp : ∀ t : ℕ, proposalWindowStart S (q + 2) ≤ t → t ≤ supportCutoff S (q + 2 + 1) →
      S.P.proposer (q + 2) ∈ Sched.awake (t : Int) ∧ S.P.proposer (q + 2) ∉ Sched.adv (t : Int))
    (hLatest : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[j][u].st).A.latest_confirmed ∧
        (x[j][u].st).A.latest_confirmed ∈ (x[j][u].st).S.T) :
    (∃ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S (q + 2)) ∧
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent) ∧
    ∀ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S (q + 2)) →
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent →
      RootCollisionAtProposal S Sched x (q + 2) B ∨
      ((∀ v ∈ honestActiveAt S Sched (q + 2),
        (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v).A.saved_confirmation (q + 2) =
          some B ∧
        confirmedOf (stateBefore x (supportCutoff S (q + 2 + 1) + 1) v) = B) ∧
      (∀ (v : V) (j s' : ℕ), HonestThrough x j v → q + 2 ≤ s' → v ∈ honestActiveAt S Sched s' →
        supportCutoff S (s' + 1) < x[j].time →
        B.AncestorEq (confirmedOf (x[j][v].st)))) := by
  have key := fun (t : ℕ) (ht : supportCutoff S (q + 2 + 1) ≤ t) =>
    included_q_until S Sched x GST s₀ anchor i₁ H q t hDiv hMono hSync hCatch
      (rootsNameBlocksUntil_of_rootsNameBlocks x t hRoots) hParent hOwner hU hAdvQ hSleepK hAnchor
      hGST hChain hInv hLocks hOld hCaches ht₀ hs₀q hs ht hLk hp hLatest
  obtain ⟨h1, h2⟩ := key (supportCutoff S (q + 2 + 1)) le_rfl
  refine ⟨h1, fun ip B hl hsent => ?_⟩
  by_cases hcol : RootCollisionAtProposal S Sched x (q + 2) B
  · exact Or.inl hcol
  right
  refine ⟨?_, fun v j s' hHon hqs hvA hlt => ?_⟩
  · rcases h2 ip B hl hsent with h | ⟨h, -⟩
    · exact absurd h hcol
    · exact h
  · rcases (key (max (supportCutoff S (q + 2 + 1)) x[j].time) (le_max_left _ _)).2 ip B hl hsent
      with h | ⟨-, h⟩
    · exact absurd h hcol
    · exact h v j s' hHon hqs hvA hlt (le_max_right _ _)

/-- **Kit fact, the lock invariant at the healed slot.** The discharge of `hLocks₀` from the
premises of Lemma 81: when committee sleepiness holds from `anchor` at or before the start of slot
`s₀ + 1`, `B₀`'s slot is at least `s₀`, `HonestChainExtends` holds for `B₀` at slot `s₀` at the
honest active validators of slot `s₀`, and every updater of slot `s₀` saves `B₀`, then every honest
active validator of slot `s₀` satisfies the lock invariant at slot `s₀` for the chain before
`s₀ + 1`.

Why: `liveLocksOnFamilyAt_base` puts every live entry on `B₀` or an ancestor of it, and `B₀` is on
the chain at slot `s₀` (some honest committee member of slot `s₀` is an updater that saved it).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `anchor`: the
  time from which committee sleepiness holds; `B₀`: the healed block; `u`: the validator. -/
theorem base_locks_on_chain (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ anchor : ℕ) (B₀ : Block V) (u : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ slotStart S (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt S Sched s₀,
      (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some B₀)
    (hu : u ∈ honestActiveAt S Sched s₀) :
    LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u := by
  have hCom := committee_majority_of_sleepiness S Sched anchor s₀ hSleepK hAnchor
  obtain ⟨u₀, hu₀⟩ : (S.P.committee s₀ ∩ honestActiveAt S Sched s₀).Nonempty :=
    Finset.card_pos.1 (by omega)
  have hv₀ := honestActiveAt_subset_updaterAt S Sched s₀ (Finset.mem_inter.1 hu₀).2
  intro A₃ hR e he hl
  obtain ⟨D, hD, heD⟩ := liveLocksOnFamilyAt_base S Sched x s₀ B₀ u hDiv hMono hB₀slot
    (hBase.2.1 u hu) A₃ hR e he hl
  exact ⟨D, ⟨s₀, Nat.lt_succ_self s₀, le_rfl, u₀, hv₀, B₀, hBaseSaved u₀ hv₀, hD⟩, heD⟩

/-- The lock invariant at a slot `q ≥ s₀` for the chain before `q + 1`: from `hLocks` when
`q > s₀`, from `hLocks₀` when `q = s₀`; `hLocks` read up to slot `q`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `q`: the
  slot. -/
theorem locks_before_of_locks_le (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ q : ℕ)
    (hLocks : ∀ s : ℕ, s₀ < s → s ≤ q → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hLocks₀ : ∀ u ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u)
    (hs₀q : s₀ ≤ q) :
    ∀ u ∈ honestActiveAt S Sched q,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (q + 1)) q u := by
  intro u hu
  rcases Nat.lt_or_eq_of_le hs₀q with hlt | heq
  · intro A' hrev e he hl
    obtain ⟨D, ⟨s'', hs'', hAt⟩, heD⟩ := hLocks q hlt le_rfl u hu A' hrev e he hl
    exact ⟨D, ⟨s'', Nat.lt_succ_of_lt hs'', hAt⟩, heD⟩
  · subst heq
    exact hLocks₀ u hu

/-- The lock invariant at a slot `q ≥ s₀` for the chain before `q + 1`: from `hLocks` when
`q > s₀`, from `hLocks₀` when `q = s₀`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `q`: the
  slot. It is `locks_before_of_locks_le`. -/
theorem locks_before_of_locks (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ q : ℕ)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hLocks₀ : ∀ u ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u)
    (hs₀q : s₀ ≤ q) :
    ∀ u ∈ honestActiveAt S Sched q,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (q + 1)) q u :=
  locks_before_of_locks_le S Sched x s₀ q (fun s h₁ _ => hLocks s h₁) hLocks₀ hs₀q

/-- **The per-validator export of the inclusion.** The proof; the audited
statement is in `Statements/Executions/ConfirmedTipStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `s`: the slot; `B`: the proposal; `v`: the updater.

Roots name blocks until `supportCutoff S (s + 1)`: `included_update_facts_q` at `q := s − 2`.

Caches up to `supportCutoff S (s + 1)`: `included_update_facts_q_until` at `q := s − 2`. -/
theorem lem90_included_update_facts_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H s : ℕ) (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
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
        A'.latest_confirmed := by
  obtain ⟨hs2, -, -⟩ := slot_after_healed_round S s₀ s (lt_of_le_of_lt ht₀ hs)
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  obtain ⟨ip, hl, hsent⟩ := hPropose
  exact included_update_facts_q_until S Sched x GST s₀ anchor i₁ H q ip B v hDiv hMono hSync hCatch
    hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST hChain hInv hLocks hOld hCaches ht₀
    (by omega) hs (locks_before_of_locks_le S Sched x s₀ q
    (fun s h₁ h₂ => hLocks s h₁ (by omega)) hLocks₀ (by omega)) hp hl hsent
    (fun B' hB' hr => hNoCollision ⟨B', hB', hr⟩) hv

/-- **The per-validator export of the inclusion.** The proof; the audited
statement is in `Statements/Executions/ConfirmedTipStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `s`: the slot; `B`: the proposal; `v`: the updater.

Roots name blocks until `supportCutoff S (s + 1)`: `included_update_facts_q` at `q := s − 2`.

It is `lem90_included_update_facts_until` with the caches restricted to the steps it reads. -/
theorem lem90_included_update_facts (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H s : ℕ) (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hLocks₀ : ∀ u ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
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
  lem90_included_update_facts_until S Sched x GST s₀ anchor i₁ H s B v hDiv hMono hSync hCatch
    hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST ht₀
    (confirmationsChainBefore_of_chain S Sched x s₀ _ hChain) (fun s h₁ _ => hInv s h₁) (fun s h₁ _
    => hLocks s h₁) hLocks₀ hOld (fun j u h₁ _ h₂ => hCaches j u h₁ h₂) hs hp hPropose hNoCollision
    hv

/-- **Lemma 90, inclusion, read up to a time `t`**. The proof; the audited statement is
in `Statements/Executions/ConfirmedTipStatements.lean`.

Why `htE`: at a slot `s`, the proof reads the proposer's caches
and record at the step before the start of slot `s`, and `hCaches` and `hLatest` speak only of steps
at times at least `x[i₁].time`; so the slots read are those starting at or after `tE`, and each of
them starts after `x[i₁].time`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold; `t`: the time up to
  which the inclusion is read.
- `tE`: the time from which the slots are read.

Roots name blocks until `t`: `included_q_until` at every slot whose update, the support cutoff of
the next slot, is at most `t`, reading the confirmed tips at steps at times at most `t`.

Caches up to `t`, with the roots: `included_q_upTo` at every slot whose update is at most `t`.
Named `_upTo`, since `lem90_confirmed_included_until` is the landed form bounded in its roots
only. -/
theorem lem90_confirmed_included_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H t tE : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (htE : ∀ s : ℕ, tE ≤ slotStart S s → x[i₁].time < slotStart S s)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hLocks₀ : ∀ u ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ t →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hLatest : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[j][u].st).A.latest_confirmed ∧
        (x[j][u].st).A.latest_confirmed ∈ (x[j][u].st).S.T)
    : ConfirmedIncludedBetween S Sched x tE t := by
  rw [GoldilocksCorrectness.Proofs.View.confirmedIncludedBetween_unfold]
  intro s hsE hst hp
  have hs := htE s hsE
  obtain ⟨hs2, -, -⟩ := slot_after_healed_round S s₀ s (lt_of_le_of_lt ht₀ hs)
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  -- the slot lemma also concludes the saved confirmation, which the conclusion no longer reads
  -- (b (a))
  exact (included_q_upTo S Sched x GST s₀ anchor i₁ H q t hDiv hMono hSync hCatch hRoots
    hParent hOwner hU hAdvQ hSleepK hAnchor hGST hChain hInv hLocks hOld hCaches ht₀ (by omega) hs
    hst (locks_before_of_locks S Sched x s₀ q hLocks hLocks₀ (by omega)) hp hLatest).imp_right
    fun h i B hl hsent => (h i B hl hsent).imp_right fun h' => ⟨fun v hv => (h'.1 v hv).2, h'.2⟩

/-- **Lemma 90, inclusion, read up to a time `t`**. The proof; the audited statement is
in `Statements/Executions/ConfirmedTipStatements.lean`.

Why `htE`: at a slot `s`, the proof reads the proposer's caches
and record at the step before the start of slot `s`, and `hCaches` and `hLatest` speak only of steps
at times at least `x[i₁].time`; so the slots read are those starting at or after `tE`, and each of
them starts after `x[i₁].time`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold; `t`: the time up to
  which the inclusion is read.
- `tE`: the time from which the slots are read.

Roots name blocks until `t`: `included_q_until` at every slot whose update, the support cutoff of
the next slot, is at most `t`, reading the confirmed tips at steps at times at most `t`.

On the chain before the slots whose update is at most `t`, the invariant and the locks at those
slots, the records on the chain at slots whose update ran by then: `included_q_before`.

Caches up to `t`, with the roots: `included_q_upTo` at every slot whose update is at most `t`.
Named `_upTo`, since `lem90_confirmed_included_until` is the landed form bounded in its roots
only. -/
theorem lem90_confirmed_included_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H t tE : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (htE : ∀ s : ℕ, tE ≤ slotStart S s → x[i₁].time < slotStart S s)
    (hChain : ∀ σ : ℕ, supportCutoff S (σ + 1) ≤ t →
      ConfirmationsChainBefore S Sched x s₀ (σ + 1))
    (hInv : ∀ s : ℕ, s₀ < s → supportCutoff S (s + 1) ≤ t →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → supportCutoff S (s + 1) ≤ t → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hLocks₀ : ∀ u ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ t →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hLatest : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ t →
      u ∉ Sched.adv (x[j].time : Int) → (∃ σ : ℕ, supportCutoff S (σ + 1) ≤ x[j].time ∧
        OnHonestChainAt S Sched x s₀ σ (x[j][u].st).A.latest_confirmed) ∧
        (x[j][u].st).A.latest_confirmed ∈ (x[j][u].st).S.T)
    : ConfirmedIncludedBetween S Sched x tE t := by
  rw [GoldilocksCorrectness.Proofs.View.confirmedIncludedBetween_unfold]
  intro s hsE hst hp
  have hs := htE s hsE
  obtain ⟨hs2, -, -⟩ := slot_after_healed_round S s₀ s (lt_of_le_of_lt ht₀ hs)
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  -- the slot lemma also concludes the saved confirmation, which the conclusion no longer reads
  -- (b (a))
  exact (included_q_before S Sched x GST s₀ anchor i₁ H q t hDiv hMono hSync hCatch hRoots
    hParent hOwner hU hAdvQ hSleepK hAnchor hGST hChain hInv hLocks hOld hCaches ht₀ (by omega) hs
    hst (locks_before_of_locks_le S Sched x s₀ q
      (fun s h₁ h₂ => hLocks s h₁ (le_trans (supportCutoff_le_of_le S (by omega)) hst)) hLocks₀
      (by omega)) hp hLatest).imp_right
    fun h i B hl hsent => (h i B hl hsent).imp_right fun h' => ⟨fun v hv => (h'.1 v hv).2, h'.2⟩

/-- **Lemma 90, inclusion, read up to a time `t`**. The proof; the audited statement is
in `Statements/Executions/ConfirmedTipStatements.lean`.

Why `htE`: at a slot `s`, the proof reads the proposer's caches
and record at the step before the start of slot `s`, and `hCaches` and `hLatest` speak only of steps
at times at least `x[i₁].time`; so the slots read are those starting at or after `tE`, and each of
them starts after `x[i₁].time`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold; `t`: the time up to
  which the inclusion is read.
- `tE`: the time from which the slots are read.

Roots name blocks until `t`: `included_q_until` at every slot whose update, the support cutoff of
the next slot, is at most `t`, reading the confirmed tips at steps at times at most `t`.

It is `lem90_confirmed_included_upTo` with the caches restricted to the steps it reads. -/
theorem lem90_confirmed_included_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H t tE : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (htE : ∀ s : ℕ, tE ≤ slotStart S s → x[i₁].time < slotStart S s)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hLocks₀ : ∀ u ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hLatest : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[j][u].st).A.latest_confirmed ∧
        (x[j][u].st).A.latest_confirmed ∈ (x[j][u].st).S.T)
    : ConfirmedIncludedBetween S Sched x tE t :=
  lem90_confirmed_included_upTo S Sched x GST s₀ anchor i₁ H t tE hDiv hMono hSync hCatch
    hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST ht₀ htE hChain hInv hLocks hLocks₀ hOld
    (fun j u h₁ _ h₂ => hCaches j u h₁ h₂) hLatest

/-- **Lemma 90, inclusion.** The proof; the audited
statement is in `Statements/Executions/ConfirmedTipStatements.lean`.

Why `htE`: at a slot `s`, the proof reads the proposer's caches
and record at the step before the start of slot `s`, and `hCaches` and `hLatest` speak only of steps
at times at least `x[i₁].time`; so the slots read are those starting at or after `tE`, and each of
them starts after `x[i₁].time`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold.
- `tE`: the time from which the slots are read.

Roots name blocks among everything honest validators hold (`RootsNameBlocks`, not bounded): the
conclusion `ConfirmedIncludedAfterHealing` is for every slot starting at or after `tE`, and
`included_q` reads, for each, blocks held at every later slot's update. It is
`lem90_confirmed_included_until` at every time `t`.
-/
theorem lem90_confirmed_included (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H tE : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocks S Sched x)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (htE : ∀ s : ℕ, tE ≤ slotStart S s → x[i₁].time < slotStart S s)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hLocks₀ : ∀ u ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hLatest : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[j][u].st).A.latest_confirmed ∧
        (x[j][u].st).A.latest_confirmed ∈ (x[j][u].st).S.T)
    : ConfirmedIncludedAfterHealing S Sched x tE :=
  (confirmedIncludedAfterHealing_iff S Sched x _).2 fun t =>
    lem90_confirmed_included_until S Sched x GST s₀ anchor i₁ H t tE hDiv hMono hSync hCatch
      (rootsNameBlocksUntil_of_rootsNameBlocks x t hRoots) hParent hOwner hU hAdvQ hSleepK hAnchor
      hGST ht₀ htE hChain hInv hLocks hLocks₀ hOld hCaches hLatest

end GoldilocksCorrectness.Proofs.Executions
