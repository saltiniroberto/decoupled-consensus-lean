module
public import GoldilocksCorrectness.Proofs.Executions.PhaseChain
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.Lemma81UpTo
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatementsUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma31UpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma42UpTo

@[expose] public section

/-!
# `PhaseChain.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/PhaseChain.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `lem89s_phase_step`, `locks_clause_of_votes`, `lem45b_honest_vote_extends_lock_held`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  dutyWindowStart_succ_le_slotStart dutyWindowStart_succ_le_supportCutoff lockDeadline_injective
  one_le_Δ slotStart_eq slotStart_mono supportCutoff_eq supportCutoff_lt_of_lt supportCutoff_succ_le
  viewFreeze_eq voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both)
open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes
  fc_root_eq pool_of_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (votesOnceInPoolFor_of_keepsVotes)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn VotesOnceInPoolFor expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible awake_since_record_awake revoke_locks_entry_mem_tree)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **The phase step.** The proof; the audited statement is in
`Statements/Executions/PhaseChainStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s'`: the slot of the step;
- `Hon`: the voters of slot `s'`; `Hon'`: the members of slot `s' + 1`; `𝓒`: the family.

Roots name blocks until `supportCutoff S (s' + 1)`: the proof reads `lem89s_chain_step` at slot
`s'`, whose bound is that time.

Restated with the delivery premises up to `supportCutoff S (s' + 1)`: the chain step at slot `s'` reads deliveries due by then (`lem89s_chain_step_upTo`). -/
theorem lem89s_phase_step_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s' : ℕ) (Hon Hon' : Finset V) (𝓒 : Block V → Prop)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s' + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s' + 1)))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s')
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S s' ≤ t → t ≤ supportCutoff S (s' + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hHon' : ∀ v ∈ Hon', ∀ t : ℕ, dutyWindowStart S (s' + 1) ≤ t → t ≤ supportCutoff S (s' + 2) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hSub : Hon' ⊆ Hon)
    (hCommittee : (S.P.committee s').card < 2 * (S.P.committee s' ∩ Hon).card)
    (hCommittee' : (S.P.committee (s' + 1)).card < 2 * (S.P.committee (s' + 1) ∩ Hon').card)
    (hInv : ChainInvFor S Sched x Hon 𝓒 s')
    (hLocks : ∀ u ∈ Hon, LiveLocksOnFamilyAt S Sched x 𝓒 s' u)
    (hStep : ∀ C : Block V, (𝓒 C ∨ ∃ v ∈ Hon',
        (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C) →
      ∀ w ∈ Hon', StepFrameAt S Sched x C s' w) :
    ChainInvFor S Sched x Hon' (fun C => 𝓒 C ∨ ∃ v ∈ Hon', ∃ C' : Block V,
      (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' ∧
      C.AncestorEq C') (s' + 1) ∧
    ∀ u ∈ Hon', LiveLocksOnFamilyAt S Sched x (fun C => 𝓒 C ∨ ∃ v ∈ Hon', ∃ C' : Block V,
      (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' ∧
      C.AncestorEq C') (s' + 1) u := by
  -- the times
  have hΔ := one_le_Δ S
  have hc1 : supportCutoff S (s' + 1) = voteTime S (s' + 1) + Δ S := supportCutoff_eq S (s' + 1)
  have hc2 : supportCutoff S (s' + 2) = voteTime S (s' + 2) + Δ S := supportCutoff_eq S (s' + 2)
  have hv2 : voteTime S (s' + 1 + 1) = voteTime S (s' + 1) + 4 * Δ S := voteTime_succ S (s' + 1)
  have hd0 : dutyWindowStart S s' ≤ supportCutoff S (s' + 1) :=
    dutyWindowStart_le_supportCutoff S (by omega)
  have hd1 : dutyWindowStart S (s' + 1) ≤ supportCutoff S (s' + 1) :=
    dutyWindowStart_le_supportCutoff S (by omega)
  have hd2 : dutyWindowStart S (s' + 1) ≤ supportCutoff S (s' + 1 + 1) :=
    dutyWindowStart_le_supportCutoff S (by omega)
  have hcc : supportCutoff S (s' + 1) ≤ supportCutoff S (s' + 2) := supportCutoff_succ_le S s'
  -- the three sets of the chain step
  have hHonA : Hon ⊆ honestActiveAt S Sched s' := by
    intro u hu
    unfold honestActiveAt activeAt
    rw [Finset.mem_sdiff]
    exact ⟨mem_awakeThroughout_of_forall (fun t h1 h2 => (hHon u hu t h1 h2).1),
      (hHon u hu _ hd0 le_rfl).2⟩
  have hHon'A : Hon' ⊆ honestActiveAt S Sched (s' + 1) := by
    intro u hu
    unfold honestActiveAt activeAt
    rw [Finset.mem_sdiff]
    exact ⟨mem_awakeThroughout_of_forall (fun t h1 h2 => (hHon' u hu t h1 h2).1),
      (hHon' u hu _ hd2 le_rfl).2⟩
  have hUpd : Hon' ⊆ updaterAt S Sched s' := by
    intro u hu
    unfold updaterAt
    rw [Finset.mem_sdiff]
    exact ⟨mem_awakeThroughout_of_forall (fun t h1 h2 => (hHon' u hu t h1 (le_trans h2 hcc)).1),
      (hHon' u hu _ hd1 hcc).2⟩
  -- every block of the family is an ancestor of every member's confirmation of slot `s'`
  have hConfExt : ∀ C : Block V, 𝓒 C → ∀ v ∈ Hon', ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' →
      C.AncestorEq C' :=
    fun C hC v hv C' hC' => (hInv C hC).2.2 v (hSub hv) C' hC'
  refine ⟨lem89s_chain_step_upTo S Sched x GST s' Hon Hon' Hon' 𝓒 hDiv hMono hSync hCatch hRoots
    hParent hOwner hGST hHonA hHon'A hUpd subset_rfl hCommittee hCommittee' hInv
    (fun u hu => Or.inl (hSub hu)) hLocks hConfExt hStep, ?_⟩
  -- the lock invariant at every member of `Hon'`
  intro u hu
  exact liveLocksOnFamilyAt_step S Sched x 𝓒 _ s' u hDiv
    (fun t h1 h2 => hHon' u hu t (le_trans (dutyWindowStart_mono S (by omega)) h1) (by omega)) (fun C hC => Or.inl hC)
    (fun C hC => Or.inr ⟨u, hu, C, hC, ancestorEq_refl C⟩) (hLocks u (hSub hu))

/-- **The lock clause from the votes.** In an execution where every time is reached, corruption is
permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`,
a root names one block among what honest validators hold, a block reaches a validator
only once it holds the parent, and nobody votes in an honest validator's name: if `GST` is at most
the vote time of slot `s`; the members are awake and honest at every time from the duty window's
start of slot `s` to the vote time of slot `s + 1`; the committee of slot `s` has fewer than twice
its members in `Hon`; every committee member `u` of `Hon` put on the wire at its tick at the vote
time of slot `s` its slot-`s` vote for `(H u).root`, `H u` a block it holds then that is `B` or a
descendant of `B`; and every member's finalized block before the support cutoff of slot `s + 1` is
compatible with `B` — then every lock entry a member's revocation of slot `s + 1` leaves is on a
block compatible with `B`.

Why: `w`'s finalized block `F` before the vote time of slot `s + 1` is an ancestor of its finalized
block before the support cutoff of slot `s + 1`, or it, so it is compatible with `B`. When `B` is
`F` or an ancestor of `F`, every entry left is on a block of `w`'s frame tree, which descends from
`F`. When `F` is an ancestor of `B`, every vote of a committee member of `Hon` reached `w`, held
early, by the support cutoff of slot `s` (Lemma 12), so it is the member's only slot-`s` vote in
`w`'s pool, resolving to a block of `w`'s frame tree on `B`'s chain; Lemma 5 concludes.

Read aloud: a majority of honest votes for `B`'s chain at slot `s` leaves no honest lock
conflicting with `B` after the revocation of slot `s + 1`, whatever the locks were before.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot; `Hon`: the members; `B`: the block; `H`: the block of
  each committee member's vote.

Roots name blocks until `supportCutoff S s`: the proof reads Lemma 12 at slot `s`, whose bound
is that time.

Restated with the delivery premises up to `supportCutoff S s`: Lemma 12 at slot `s` reads the votes due by then (`lem12_honest_vote_delivered_upTo`). -/
theorem locks_clause_of_votes_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hon : Finset V) (B : Block V)
    (H : V → Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S s ≤ t → t ≤ voteTime S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hCommittee : (S.P.committee s).card < 2 * (S.P.committee s ∩ Hon).card)
    (hVotes : ∀ u ∈ S.P.committee s ∩ Hon,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ B.AncestorEq (H u))
    (hF : ∀ v ∈ Hon, (stateBefore x (supportCutoff S (s + 1)) v).S.F.compatible B = true) :
    ∀ w ∈ Hon, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries, e.B.compatible B = true := by
  intro w hw A' hRevoke e he
  -- the times
  have hΔ := one_le_Δ S
  have hb1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  have hv1 : voteTime S (s + 1) = voteTime S s + 4 * Δ S := voteTime_succ S s
  have hc0 : supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S s
  have hc1 : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hdw : dutyWindowStart S s ≤ voteTime S s := by
    have h1 := dutyWindowStart_mono S (Nat.le_add_right s 1)
    have h2 := dutyWindowStart_succ_le_slotStart S s
    have h3 := voteTime_eq S s
    omega
  -- `w`'s finalized block before the vote time of slot `s + 1` is compatible with `B`
  have hFF : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq
      (stateBefore x (supportCutoff S (s + 1)) w).S.F :=
    F_ancestorEq_of_le x w (stepBefore_mono x hDiv (by omega))
  have hFc := compatible_of_ancestorEq_compatible hFF (hF w hw)
  rcases (compatible_iff _ _).1 hFc with hFB | hBF
  swap
  · -- `B` is the finalized block or an ancestor of it: every entry left descends from it
    have heT := revoke_locks_entry_mem_tree hb1 hRevoke e he
    exact (compatible_iff _ _).2 (Or.inr (ancestorEq_trans hBF ((mem_fg_to_ac_tree _ _).1 heT).2))
  -- the finalized block is an ancestor of `B`, or `B`: Lemma 5 against the members' votes
  have hHeld : ∀ u ∈ S.P.committee s ∩ Hon, HeldEarlyVoteFor S.C
      (stateBefore x (voteTime S (s + 1)) w).A
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) s (H u) u :=
    GoldilocksCorrectness.Statements.Executions.lem12_honest_vote_delivered_upTo S Sched x GST s
      (S.P.committee s ∩ Hon) H w hDiv hMono hSync hCatch hRoots hParent hOwner hGST
      (fun u hu => ⟨(Finset.mem_inter.1 hu).1,
        (hHon u (Finset.mem_inter.1 hu).2 _ (by omega) le_rfl).2, (hVotes u hu).1,
        (hVotes u hu).2.1⟩)
      (fun t h1 h2 => hHon w hw t (by omega) (by omega))
      (fun u hu => ancestorEq_trans hFB (hVotes u hu).2.2)
  have hPer : ∀ u ∈ S.P.committee s ∩ Hon, VotesOnceInPoolFor
      (stateBefore x (voteTime S (s + 1)) w).A
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) s B u := by
    intro u hu
    obtain ⟨vote, hv, hvi, hres, ⟨H', hH'T, hroot, hHH'⟩, huniq⟩ :=
      GoldilocksCorrectness.Statements.Executions.heldEarlyVoteFor_votesOnceInPoolFor S.C _ _ s
        (H u) u (hHeld u hu)
    exact ⟨vote, hv, hvi, hres, ⟨H', hH'T, hroot, ancestorEq_trans (hVotes u hu).2.2 hHH'⟩, huniq⟩
  have hHalf := (counting_of_committee_majority S Sched x s 0 Hon w hCommittee).1
  have hRootsΦw : RootsNameBlocksIn (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ w
  exact (GoldilocksCorrectness.Statements.Routines.lem5_revoke_locks_entries_compatible S.P _ A'
    _ _ (s + 1) B (S.P.committee s ∩ Hon) hb1 hRootsΦw
    (by
      rw [Nat.add_sub_cancel]
      exact fun u hu => (votesOnceInPoolFor_of_keepsVotes (expireLocks_keepsVotes _ _) _ _ _ _).2
        (hPer u hu))
    (by rw [Nat.add_sub_cancel]; exact hHalf)
    hRevoke e he).2

/-- **Lemma 45b, a lock whose window is after `GST` is extended by the next slot's honest votes,
the held form.** The proof; the audited statement is in
`Statements/Executions/PhaseChainStatements.lean`. It is the proof of Lemma 45
(`GoldilocksCorrectness/Proofs/Executions/Lemma45.lean`), steps 1 to 3 verbatim, with step 4
calling Lemma 21b (`lem21b_goldfish_vote_extends_eligible_block_held`) in place of Lemma 21, so
that the block the vote names is kept, held by `w`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the lock;
- `v`: the validator whose update of slot `s + 1` adds the lock entry `e`; `A'`: that update's
  answer; `w`: the voter of slot `s + 1`; `vote`: its Goldfish vote.

Roots name blocks until `supportCutoff S (s + 1)`: the proof reads Lemma 42 and Lemma 21b at
slot `s`, and Lemma 31 at a slot `s' < s`, whose bounds are at most that time.

Restated with the delivery premises up to `supportCutoff S (s + 1)`: Lemma 42 and Lemma 21b at slot `s` read deliveries due by then, and Lemma 31 at a slot `s' < s` reads earlier. -/
theorem lem45b_honest_vote_extends_lock_held_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s : ℕ) (v w : V) (A' : ACState V) (e : LockEntry V) (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s + 1)))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ supportCutoff S (s + 1 - S.C.k))
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hw : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A')
    (he : e ∈ A'.lock_entries)
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    (hF2 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.compatible e.B = true)
    (hF3 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq e.B →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads ∧
          e.B.AncestorEq W)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent) :
    ∃ H_w ∈ (stateBefore x (voteTime S (s + 1)) w).S.T,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ e.B.AncestorEq H_w := by
  have hFroot : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root := by
    rw [fc_root_eq]; exact F_ancestorEq_fc_root_of_stateBefore S Sched x (voteTime S (s + 1)) w
  -- the times
  have hΔ := one_le_Δ S
  have hb1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hvb : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hcb : supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S s
  have ht₂ : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hfr : viewFreeze S s = slotStart S s + 3 * Δ S := viewFreeze_eq S s
  have hdw : dutyWindowStart S (s + 1) ≤ slotStart S s := dutyWindowStart_succ_le_slotStart S s
  have hGSTb : GST ≤ supportCutoff S s := by
    have h := slotStart_mono S (show s + 1 - S.C.k ≤ s by have := S.C.k_ge_two; omega)
    rw [supportCutoff_eq S (s + 1 - S.C.k), voteTime_eq S (s + 1 - S.C.k)] at hGST
    omega
  have hRootsΦv : RootsNameBlocksIn
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ v
  -- step 1: Lemma 35 on `v`'s update; `e` is an entry it adds
  obtain ⟨-, h35⟩ := GoldilocksCorrectness.Statements.Routines.lem35_update_confirmation_lock_entries
    S.C S.P _ A' _ _ (s + 1) hUpdate
  rcases h35 e he with hin | ⟨-, -, -, ⟨C', hSaved, hLC'⟩, hFS⟩
  · -- an entry of the input was added by the update of its own slot `s`, before `c`
    exfalso
    have hin' : e ∈ (stateBefore x (supportCutoff S (s + 1)) v).A.lock_entries := by
      simp only [expireLocks, Finset.mem_filter] at hin
      exact hin.1
    obtain ⟨s', hd', hlt, -⟩ :=
      GoldilocksCorrectness.Proofs.Executions.lem39_lock_entry_provenance S Sched x _ v e hDiv hin'
    have hbb : s' = s := lockDeadline_injective S (hd'.symm.trans hd)
    rw [hbb] at hlt
    exact lt_irrefl _ hlt
  -- step 2: Lemma 36 gives the early supporters of `e`'s block at `v`
  obtain ⟨Sup, hSup, hElig, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem36_confirmed_ancestor_early_supporters S.C S.P
      _ A' _ _ (s + 1) C' e.B hb1 hRootsΦv
      (by rw [Nat.add_sub_cancel, pool_of_keepsVotes (expireLocks_keepsVotes _ _)]
          exact pool_vote_late S Sched x s v hDiv)
      hUpdate hSaved hLC'
  simp only [Nat.add_sub_cancel] at hSup hElig hFS
  -- `expireLocks` keeps the pool and the stamps
  have hSup' : ∀ u ∈ Sup, EarlySupporterOf S.C (stateBefore x (supportCutoff S (s + 1)) v).A
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) s e.B u := fun u hu =>
    (earlySupporterOf_of_keepsVotes (expireLocks_keepsVotes _ _) _ _ _ _ _).1 (hSup u hu)
  have hElig' : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Sup.card := by
    rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)] at hElig; exact hElig
  -- step 3: the lock condition at `w`
  have hLocks : ∀ A'' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A'' →
      ∀ e' ∈ A''.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e' = true → e'.B.compatible e.B = true := by
    rcases hFS with hFast | hSlow
    · -- fast: Lemma 42
      intro A'' hRevoke e' he' _
      exact lem42_fast_lock_clears_conflicting_locks_upTo S Sched x GST s e.B v w A' hDiv hMono hSync
        hCatch hRoots hParent (by omega)
        (fun t h1 h2 => hv t (by omega) h2) (fun t h1 h2 => hw t (by omega) (by omega)) hUpdate
        hFast (compatible_of_ancestorEq_compatible hFroot hF2) A'' hRevoke e' he'
    · -- slow: through the slot of each entry `w`'s revocation reads
      intro A'' hRevoke e' he' _
      obtain ⟨e_w, he_w, -, -, he'w, -⟩ :=
        GoldilocksCorrectness.Statements.Routines.lem38_revoke_locks_entries_moved S.P _ A'' _ _
          (s + 1) hb1 hRevoke e' he'
      have he_w' : e_w ∈ (stateBefore x (voteTime S (s + 1)) w).A.lock_entries ∧
          ((voteTime S (s + 1) : ℕ) : Int) < e_w.d := by
        simp only [expireLocks, Finset.mem_filter] at he_w
        exact he_w
      -- the slot `s'` of `e_w`, and `w`'s saved confirmation of it
      obtain ⟨s', hd_w, hc_w, C_w, hC_w, hB_w⟩ :=
        lock_entry_saved_confirmation x hDiv _ w e_w he_w'.1
      -- `s' < s`: the update of slot `s' + 1` ran before `t₃`
      have hlt : s' < s := by
        by_contra h
        have h' : supportCutoff S (s + 1) ≤ supportCutoff S (s' + 1) := by
          rcases Nat.lt_or_eq_of_le (show s + 1 ≤ s' + 1 by omega) with h'' | h''
          · exact le_of_lt (supportCutoff_lt_of_lt S h'')
          · rw [h'']
        omega
      -- `s + 1 − k ≤ s'`: `e_w` is live at `t₃`
      have hlow : s + 1 - S.C.k ≤ s' := by
        by_cases hkb : S.C.k ≤ s + 1
        · refine GoldilocksCorrectness.Proofs.Executions.lem41_slot_of_live_entry S
            (s + 1 - S.C.k) s' (voteTime S (s + 1)) e_w hd_w he_w'.2 ?_
          rw [Nat.sub_add_cancel hkb]
        · omega
      -- `e`'s block is `v`'s saved confirmation of slot `s'` or an ancestor of it
      obtain ⟨-, hj⟩ :=
        GoldilocksCorrectness.Statements.Routines.lem37_slow_test_saved_confirmations S.C _ _ s
          e.B hSlow
      obtain ⟨Cj, hCj, -, hBj⟩ := hj s' hlow hlt
      have hCj' : (stateBefore x (supportCutoff S (s + 1)) v).A.saved_confirmation s' =
          some Cj := hCj
      -- the two updates of slot `s' + 1` that saved `Cj` and `C_w`
      obtain ⟨-, -, ⟨A_v, hUv, hSv⟩, -⟩ :=
        GoldilocksCorrectness.Proofs.Executions.lem40_saved_confirmation_provenance S Sched x
          (supportCutoff S (s + 1)) v s' Cj hDiv hCj'
      obtain ⟨-, -, ⟨A_w, hUw, hSw⟩, -⟩ :=
        GoldilocksCorrectness.Proofs.Executions.lem40_saved_confirmation_provenance S Sched x
          (voteTime S (s + 1)) w s' C_w hDiv hC_w
      -- the times of slot `s'`
      have hssw : slotStart S (s' + 1) = slotStart S s' + 4 * Δ S := by
        rw [slotStart_eq, slotStart_eq S s', Nat.mul_add, Nat.mul_one]
      have hssle : slotStart S (s' + 1) ≤ slotStart S s := slotStart_mono S hlt
      have hvw : voteTime S s' = slotStart S s' + Δ S := voteTime_eq S s'
      have hcw : supportCutoff S s' = voteTime S s' + Δ S := supportCutoff_eq S s'
      have hcw1 : supportCutoff S (s' + 1) = voteTime S (s' + 1) + Δ S :=
        supportCutoff_eq S (s' + 1)
      have hvw1 : voteTime S (s' + 1) = slotStart S (s' + 1) + Δ S := voteTime_eq S (s' + 1)
      have hfrw : viewFreeze S s' = slotStart S s' + 3 * Δ S := viewFreeze_eq S s'
      have hdww : dutyWindowStart S (s + 1) ≤ supportCutoff S s' :=
        dutyWindowStart_succ_le_supportCutoff S (by omega)
      have hGSTw : GST ≤ supportCutoff S s' := by
        have h := slotStart_mono S hlow
        rw [supportCutoff_eq S (s + 1 - S.C.k), voteTime_eq S (s + 1 - S.C.k)] at hGST
        omega
      have hcomp := GoldilocksCorrectness.Proofs.Executions.lem31_saved_confirmations_compatible_upTo S
        Sched x GST s' w v A_w A_v C_w Cj hDiv hMono
        (hSync.mono (le_trans (by omega : supportCutoff S s' + Δ S ≤ supportCutoff S (s' + 1))
          (le_of_lt (supportCutoff_lt_of_lt S (by omega)))))
        (hCatch.mono (le_trans (by omega : supportCutoff S s' + Δ S ≤ supportCutoff S (s' + 1))
          (le_of_lt (supportCutoff_lt_of_lt S (by omega)))))
        (hRoots.mono (le_of_lt (supportCutoff_lt_of_lt S (by omega)))) hGSTw
        (fun t h1 h2 => hw t (by omega) (by omega)) (fun t h1 h2 => hv t (by omega) (by omega))
        (hw _ (by omega) (by omega)).2 (hv _ (by omega) (by omega)).2 hUw hSw hUv hSv
      exact compatible_of_ancestorEq_both (ancestorEq_trans he'w hB_w) hBj hcomp
  -- step 4: Lemma 21b, which keeps the block the vote names
  exact GoldilocksCorrectness.Proofs.Executions.lem21b_goldfish_vote_extends_eligible_block_held_upTo S
    Sched x GST s Sup e.B v w vote hDiv hMono hSync hCatch hRoots hParent (by omega)
    (fun t h1 h2 => hv t (by omega) h2) (fun t h1 h2 => hw t (by omega) (by omega))
    hSup' hElig' hF2 hF3 hLocks hSend

end GoldilocksCorrectness.Proofs.Executions

