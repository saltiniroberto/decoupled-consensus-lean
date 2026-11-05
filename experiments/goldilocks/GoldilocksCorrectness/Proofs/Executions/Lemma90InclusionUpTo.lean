module
public import GoldilocksCorrectness.Proofs.Executions.Lemma90Inclusion
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.Lemma91UpTo
public import GoldilocksCorrectness.Proofs.Executions.ProposalWalkUpTo
public import GoldilocksCorrectness.Statements.Executions.ProposalPropagationStatementsUpTo
public import GoldilocksCorrectness.Statements.Executions.OrderedFloorStatementsUpTo
public import GoldilocksCorrectness.Statements.Executions.FastConfirmationStatementsUpTo
public import GoldilocksCorrectness.Statements.Executions.FrameShapeStatementsUpTo

@[expose] public section

/-!
# `Lemma90Inclusion.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma90Inclusion.lean` that name a
delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the
deadlines. The bound of
each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in
the twin's own parameters.

* `honest_proposal_extends_chain_until`, `honest_proposal_saved_until`,
  `included_update_facts_q_until`, `lem90_included_update_facts_until`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart
  proposalWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ
  proposalWindowStart_eq slotStart_eq slotStart_mono slot_after_healed_round
  slot_le_of_supportCutoff_lt supportCutoff_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (fc_root_eq mem_fg_to_ac_tree)
open GoldilocksCorrectness.Statements.Routines (JustifiedInTree)

open GoldilocksCorrectness.Proofs.Routines (get_anchor_mem_T)

open GoldilocksCorrectness.Proofs.Routines (mem_viable_tree_iff)

namespace GoldilocksCorrectness.Proofs.Executions

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
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

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
ordered `head_height_floor` values (the least chain-state height a viable block may have) (`lem59le_goldfish_vote_names_honest_proposal_frame`) then names `B` in every
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
`q + 2` and the voters' before the vote time of slot `q + 2` (Lemmas 91 (b), (c), (d) and (f)).

Restated with the delivery premises up to `voteTime S (q + 2)`: the proposal of slot `q + 2` reaches its voters by then (`lem22_proposal_held_by_voter_upTo`, `lem59le_goldfish_vote_names_honest_proposal_frame_upTo`, `lem91c_proposer_h_max_le_voter_h_max_until_upTo`). -/
theorem honest_proposal_extends_chain_until_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (voteTime S (q + 2)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (voteTime S (q + 2)))
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
    have hmem := mem_T_before_add_delay_upTo hDiv hMono (SynchronyFromWakeUpTo.mono (by omega) hSync)
      (CatchUpOnWakeUpTo.mono (by omega) hCatch) (hRoots.mono (by omega))
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
    exact proposal_parent_extends_majority_block_upTo S Sched x GST (q + 1) ip
      (honestActiveAt S Sched (q + 1) ∩ S.P.committee (q + 1)) Hf X B p hDiv hMono
      (SynchronyFromWakeUpTo.mono (by omega) hSync) (CatchUpOnWakeUpTo.mono (by omega) hCatch)
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
    exact GoldilocksCorrectness.Statements.Executions.lem22_proposal_held_by_voter_upTo S Sched x GST
      (q + 1) ip B p w hDiv hMono hSync hCatch hRoots hParent (by omega) hpt
      (fun t h1 h2 => hw2 t (by omega) (by omega)) hl hsent hBp
      ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans
        (F_ancestorEq_fc_root_of_stateBefore S Sched x _ w) hρwB)))
  refine ⟨hParentChain, hBslot, hBne, hPB, fun w hwA vote hSend => ?_, fun w hwA => (hW w hwA).2⟩
  -- the vote names `B` (Lemma 59 with ordered floors)
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
  have hc := lem91c_proposer_h_max_le_voter_h_max_until_upTo S Sched x GST s₀ (q + 2) i₁ H p w hDiv
    hMono
    hSync hCatch hRoots hParent hU hAdvQ hGST ht₀ hs hChain hOld hCaches hpt
    (fun t h1 h2 => hw2 t (by omega) (by omega))
  have h88w := lem88_counting_of_committeeSleepiness S Sched x anchor (q + 1) w
    (voteTime S (q + 1 + 1)) hSleepK (by omega)
  have hb := lem91b_voter_head_height_floor_le_parent_until S Sched x s₀ (q + 2) i₁ H p w B.parent
    hDiv
    hMono hU hAdvQ hs hChain hOld hCaches hpt hwv
    (fun C hC => hParentChain C hC) hm1
  exact GoldilocksCorrectness.Statements.Executions.lem59le_goldfish_vote_names_honest_proposal_frame_upTo
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
updaters' caches before the support cutoff of slot `q + 3` (`proposer_root_on_chain_until`).

Restated with the delivery premises up to `supportCutoff S (q + 2)`: the slot-`(q + 2)` votes reach every updater by then (`lem27_update_confirmation_confirms_voter_majority_block_upTo`, `lem60_update_confirmation_fast_locks_frame_upTo`). -/
theorem honest_proposal_saved_until_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (q + 2)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (q + 2)))
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
  obtain ⟨hParentChain, hBslot, hBne, hPB, hVote, hBw⟩ := honest_proposal_extends_chain_until_upTo S
    Sched x GST s₀ anchor i₁ H q ip B hDiv hMono (SynchronyFromWakeUpTo.mono (by omega) hSync)
    (CatchUpOnWakeUpTo.mono (by omega) hCatch) (hRoots.mono (by omega))
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
    refine (GoldilocksCorrectness.Statements.Executions.lem27_update_confirmation_confirms_voter_majority_block_upTo
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
    refine GoldilocksCorrectness.Statements.Executions.lem60_update_confirmation_fast_locks_frame_upTo
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

/-- `lem90_included_update_facts` at the slot `q + 2`, with the lock invariant at slot `q` (`hLk`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the
  proposal; `v`: the updater.

Roots name blocks until `supportCutoff S (q + 2 + 1)`: `honest_proposal_saved`.

Caches up to `supportCutoff S (q + 2 + 1)`: `honest_proposal_saved_until`.

Restated with the delivery premises up to `supportCutoff S (q + 2)`: the bound of `honest_proposal_saved_until_upTo`. -/
theorem included_update_facts_q_until_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (q + 2)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (q + 2)))
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
  obtain ⟨-, hBslot, -, hBase, hSavedAll, hFrame, hFast⟩ := honest_proposal_saved_until_upTo S Sched x
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

/-- **The per-validator export of the inclusion.** The proof; the audited
statement is in `Statements/Executions/ConfirmedTipStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `s`: the slot; `B`: the proposal; `v`: the updater.

Roots name blocks until `supportCutoff S (s + 1)`: `included_update_facts_q` at `q := s − 2`.

Caches up to `supportCutoff S (s + 1)`: `included_update_facts_q_until` at `q := s − 2`.

Restated with the delivery premises up to `supportCutoff S s`: the bound of `included_update_facts_q_until_upTo` at `s = q + 2`. -/
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
        A'.latest_confirmed := by
  obtain ⟨hs2, -, -⟩ := slot_after_healed_round S s₀ s (lt_of_le_of_lt ht₀ hs)
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  obtain ⟨ip, hl, hsent⟩ := hPropose
  exact included_update_facts_q_until_upTo S Sched x GST s₀ anchor i₁ H q ip B v hDiv hMono hSync hCatch
    hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST hChain hInv hLocks hOld hCaches ht₀
    (by omega) hs (locks_before_of_locks_le S Sched x s₀ q
    (fun s h₁ h₂ => hLocks s h₁ (by omega)) hLocks₀ (by omega)) hp hl hsent
    (fun B' hB' hr => hNoCollision ⟨B', hB', hr⟩) hv

end GoldilocksCorrectness.Proofs.Executions

