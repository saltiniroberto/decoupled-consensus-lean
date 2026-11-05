module
public import GoldilocksCorrectness.Proofs.Executions.Lemma27
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatementsUpTo

@[expose] public section

/-!
# `Lemma27.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma27.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `lock_entries_compatible_of_half`, `confirmation_of_voter_majority`,
  `lem27_update_confirmation_confirms_voter_majority_block`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq
  slot_eq_of_mem supportCutoff_cast supportCutoff_eq voteTime_cast voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (expireLocks_keepsVotes votesOnceInPoolFor_of_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (is_live_iff)

open GoldilocksCorrectness.Proofs.Routines (earlyVoteOnceFor_of_keepsVotes fg_to_ac_F
  pool_of_keepsVotes)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans KeepsConfirmation
  revoke_locks_entry_mem_tree)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Under the half condition, every lock entry live at `t₃` that `v`'s revocation of slot `s + 1`
leaves is on a block compatible with `B`, when every `u ∈ Hs` is an honest member of the slot-`s`
committee that sent at the vote time of slot `s` a vote for `B`, a block it holds, and `v` is awake
and honest from the duty window's start of slot `s + 1` to `t₂`, with its finalized block before
`t₂` an ancestor of `B` or `B`.

Why: by Lemma 12 at `t₃` every `u ∈ Hs` has its vote for `B` in `v`'s pool as its only slot-`s`
vote, and Lemma 5 with the half condition makes every entry of the revocation's answer compatible
with `B`.

Roots name blocks until `supportCutoff S s`: the bound of the Lemma 12 call at slot `s` it
passes the premise to.

Restated with the delivery premises up to `supportCutoff S s`: the slot-`s` votes reach `v` by then (`lem12_honest_vote_delivered_until_upTo`). -/
theorem lock_entries_compatible_of_half_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (supportCutoff S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      B ∈ (stateBefore x (voteTime S s) u).S.T)
    -- the slot-`s` committee is at most twice `Hs`
    (hHalf : (S.P.committee s).card ≤ 2 * Hs.card)
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hF1 : (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B) :
    ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) v).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) v).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) v).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true := by
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₂ : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hc₁ : supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S s
  have hv₁ : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hdw : dutyWindowStart S (s + 1) ≤ slotStart S s := dutyWindowStart_succ_le_slotStart S s
  have hv₁' : ∀ t : ℕ, slotStart S s ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int) :=
    fun t h1 h2 => hv t (le_trans hdw h1) h2
  have hF₃ : (stateBefore x (voteTime S (s + 1)) v).S.F.AncestorEq B :=
    ancestorEq_trans (stateBefore_grows x hDiv v (by omega : voteTime S (s + 1) ≤
      supportCutoff S (s + 1))).2.1 hF1
  have hHeld₃ : ∀ u ∈ Hs, HeldEarlyVoteFor S.C (stateBefore x (voteTime S (s + 1)) v).A
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) v).S) s B u :=
    GoldilocksCorrectness.Statements.Executions.lem12_honest_vote_delivered_until_upTo S Sched x GST s
      (voteTime S (s + 1)) Hs (fun _ => B) v hDiv hMono hSync hCatch hRoots hParent
      hOwner hGST (by omega)
      (fun u hu => ⟨(hHs u hu).1, fun h => (hHs u hu).2.1 (hMono _ _ (by omega) h),
        (hHs u hu).2.2.1, (hHs u hu).2.2.2⟩)
      (fun t h1 h2 => hv₁' t (by omega) (by omega)) (fun _ _ => hF₃)
  have hRoots₃ : RootsNameBlocksIn (fg_to_ac (stateBefore x (voteTime S (s + 1)) v).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ v
  intro A' hRevoke e he _
  refine (GoldilocksCorrectness.Statements.Routines.lem5_revoke_locks_entries_compatible S.P _ A'
    _ _ (s + 1) B Hs (Nat.le_add_left 1 s) hRoots₃ (fun u hu => ?_) hHalf hRevoke e he).2
  refine (votesOnceInPoolFor_of_keepsVotes (expireLocks_keepsVotes _ _) _ _ _ _).2 ?_
  obtain ⟨hp, -, hBΦ, ⟨y, hy, -⟩, huniq⟩ := hHeld₃ u hu
  exact ⟨_, hp, rfl, ⟨y, hy⟩, ⟨B, hBΦ, rfl, ancestorEq_refl B⟩, huniq⟩

/-- `v`'s confirmation update at `t₂` saves `B`, advances the confirmed tip with `B`, and, under
the half condition, makes `B` fast and adds the lock entry on `B`, under Lemma 27's hypotheses:
the voter bound on `v`'s slot-`s` pool before `t₂` and the lock condition on `v`'s revocation of
slot `s + 1`.

Why: the proof of Lemma 18 with the voter bound for the committee majority, `hLocks` for Lemma 5,
and Lemmas 25 and 28 for Lemma 8b.

Roots name blocks until `supportCutoff S s`: the bound of the Lemma 12 call at slot `s` it
passes the premise to.

Restated with the delivery premises up to `supportCutoff S s`: the slot-`s` votes reach `v` by then (`lem12_honest_vote_delivered_until_upTo`). -/
theorem confirmation_of_voter_majority_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (supportCutoff S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      B ∈ (stateBefore x (voteTime S s) u).S.T)
    -- the validators with a slot-`s` vote in `v`'s pool before `t₂` are fewer than twice `Hs`
    (hVoters : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Hs.card)
    (hBne : B ≠ Block.genesis)
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hF1 : (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    -- the block of every lock entry live at `t₃` that `v`'s revocation leaves is compatible
    -- with `B`
    (hLocks : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) v).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) v).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) v).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true) :
    (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some B ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.latest_confirmed =
        advance (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
          (stateBefore x (supportCutoff S (s + 1)) v).A.latest_confirmed (some B) ∧
      ((S.P.committee s).card ≤ 2 * Hs.card →
        B ∈ (stateBefore x (supportCutoff S (s + 1) + 1) v).A.fast_blocks ∧
        LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∈
          (stateBefore x (supportCutoff S (s + 1) + 1) v).A.lock_entries) := by
  -- step 0: the times
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss' : slotStart S (s + 1 + 1) = slotStart S (s + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₂ : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hc₁ : supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S s
  have hv₁ : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hdw : dutyWindowStart S (s + 1) ≤ slotStart S s := dutyWindowStart_succ_le_slotStart S s
  have hslot : ∀ t : ℕ, voteTime S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      S.C.slot (t : Int) = s + 1 :=
    fun t h1 h2 => slot_eq_of_mem S (by omega) (by omega)
  have hslot₃ := hslot (voteTime S (s + 1)) le_rfl (by omega)
  have hslot₂ := hslot (supportCutoff S (s + 1)) (by omega) le_rfl
  -- step 1: `v` awake and honest from the start of slot `s`
  have hv₁' : ∀ t : ℕ, slotStart S s ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int) :=
    fun t h1 h2 => hv t (le_trans hdw h1) h2
  -- step 2: the delivered votes at `t₂`; `Hs` is not empty by the voter bound
  have hHeld₂ : ∀ u ∈ Hs, HeldEarlyVoteFor S.C (stateBefore x (supportCutoff S (s + 1)) v).A
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) s B u :=
    GoldilocksCorrectness.Statements.Executions.lem12_honest_vote_delivered_until_upTo S Sched x GST s
      (supportCutoff S (s + 1)) Hs (fun _ => B) v hDiv hMono hSync hCatch hRoots hParent
      hOwner hGST (by omega) hHs (fun t h1 h2 => hv₁' t (by omega) (by omega)) (fun _ _ => hF1)
  obtain ⟨u₀, hu₀⟩ : Hs.Nonempty :=
    Finset.card_pos.1 (by omega)
  -- step 3: the tick at `t₃`
  obtain ⟨hl₃, hti₃, hti₃'⟩ := stepBefore_spec x hDiv (by omega : 1 ≤ voteTime S (s + 1))
  have hv₃a := hv (voteTime S (s + 1)) (by omega) (by omega)
  obtain ⟨n₃, sent₃, hrun₃, hst₃⟩ := tick_step_outcome x hl₃ hv₃a.1 hv₃a.2
  have hAw₃ := awakeSince_le_dutyWindowStart_b S Sched x (s + 1) (voteTime S (s + 1)) v hDiv
    hMono (by omega) (fun t h1 h2 => (hv t h1 (by omega)).1) hv₃a.2
  have hA₃ : (tickInputState x (stepBefore x (voteTime S (s + 1))) (voteTime S (s + 1)) v).A =
      (stateBefore x (voteTime S (s + 1)) v).A := (tickInputState_frame x _ _ v).2.1
  have hS₃ : (tickInputState x (stepBefore x (voteTime S (s + 1))) (voteTime S (s + 1)) v).S =
      (stateBefore x (voteTime S (s + 1)) v).S := (tickInputState_frame x _ _ v).1
  obtain ⟨A', hRevoke, hlock₃⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem13_tick_revokes_locks S.C S.P S.X _ n₃ _ sent₃
      hrun₃ (by rw [hslot₃, voteTime_cast]) (by rw [hslot₃]; exact hAw₃)
  rw [hslot₃, hA₃, hS₃] at hRevoke
  -- step 4: the locks, by the lock condition on the revocation's answer
  have hLocksA' := hLocks A' hRevoke
  -- step 5: from the tick at `t₃` to `t₂` the lock entries only shrink
  have hsub : (stateBefore x (supportCutoff S (s + 1)) v).A.lock_entries ⊆ A'.lock_entries := by
    rw [← hlock₃, ← hst₃]
    refine stateBefore_lock_entries_subset x hDiv v (by omega) (by omega) ?_
    intro t'' h1 h2
    rw [hti₃'] at h1
    rw [hslot t'' (by omega) (by omega), ← voteTime_cast, ← supportCutoff_cast]
    constructor <;> intro h <;> omega
  -- step 6: the tick at `t₂`
  obtain ⟨hl₂, hti₂, hti₂'⟩ := stepBefore_spec x hDiv (by omega : 1 ≤ supportCutoff S (s + 1))
  have hv₂a := hv (supportCutoff S (s + 1)) (by omega) le_rfl
  obtain ⟨n₂, sent₂, hrun₂, hst₂⟩ := tick_step_outcome x hl₂ hv₂a.1 hv₂a.2
  have hAw₂ := awakeSince_le_dutyWindowStart_b S Sched x (s + 1) (supportCutoff S (s + 1)) v hDiv
    hMono (by omega) (fun t h1 h2 => (hv t h1 h2).1) hv₂a.2
  have hA₂ : (tickInputState x (stepBefore x (supportCutoff S (s + 1))) (supportCutoff S (s + 1))
      v).A = (stateBefore x (supportCutoff S (s + 1)) v).A := (tickInputState_frame x _ _ v).2.1
  have hS₂ : (tickInputState x (stepBefore x (supportCutoff S (s + 1))) (supportCutoff S (s + 1))
      v).S = (stateBefore x (supportCutoff S (s + 1)) v).S := (tickInputState_frame x _ _ v).1
  obtain ⟨A'', hUpdate, hsave, hfast, hlocks, hlatest⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem15_tick_updates_confirmation S.C S.P S.X _ n₂ _
      sent₂ hrun₂ (by rw [hslot₂, supportCutoff_cast]) (by rw [hslot₂]; exact hAw₂)
  rw [hslot₂, hA₂, hS₂] at hUpdate
  -- step 7: Lemmas 25 and 28 on the update; "no live lock vetoes `B`" moves the liveness of an
  -- entry from `t₂` under `Φ₂` to `t₃` under `Φ₃`
  have hRoots₂ : RootsNameBlocksIn (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ v
  have hB₂ : B ∈ (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree :=
    (hHeld₂ u₀ hu₀).2.2.1
  have hNoVeto : ∀ e ∈ (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
      ((supportCutoff S (s + 1) : ℕ) : Int)).lock_entries,
      is_live (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true := by
    intro e he hlive
    have heA' : e ∈ A'.lock_entries := hsub (Finset.mem_filter.1 he).1
    refine hLocksA' e heA' ?_
    simp only [is_live_iff] at hlive ⊢
    have h32 : ((voteTime S (s + 1) : ℕ) : Int) < ((supportCutoff S (s + 1) : ℕ) : Int) :=
      Int.ofNat_lt.2 (by omega)
    exact ⟨lt_trans h32 hlive.1, revoke_locks_entry_mem_tree (Nat.le_add_left 1 s) hRevoke e heA'⟩
  have hPathF : ∀ P' : Block V,
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).F.AncestorEq P' →
      P'.AncestorEq B → P' ∈ (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree :=
    fun P' h1 h2 => frame_path_of_exec S Sched x _ v B P' hB₂ h1 h2
  have hHsE : ∀ u ∈ Hs, GoldilocksCorrectness.Statements.Routines.EarlyVoteOnceFor S.C
      (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
        ((supportCutoff S (s + 1) : ℕ) : Int))
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) (s + 1 - 1) B u := by
    intro u hu
    refine (earlyVoteOnceFor_of_keepsVotes (expireLocks_keepsVotes _ _) _ _ _ _ _).2 ?_
    obtain ⟨hmem, -, -, hres, huniq⟩ := hHeld₂ u hu
    exact ⟨_, hmem, rfl, rfl, hres, huniq⟩
  have h25 :=
    GoldilocksCorrectness.Statements.Routines.lem25_update_confirmation_confirms_voter_majority_block
      S.C S.P (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
        ((supportCutoff S (s + 1) : ℕ) : Int)) A''
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) ((supportCutoff S (s + 1) : ℕ) : Int)
      (s + 1) B Hs (Nat.le_add_left 1 s) hRoots₂ hBne (by rw [fg_to_ac_F]; exact hF1) hPathF hHsE
      (by rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)]
          exact pool_slot_of_stateBefore S Sched x _ v s)
      (by rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)]; exact hVoters) hNoVeto hUpdate
  rw [Nat.add_sub_cancel] at h25
  -- step 8: from the tick at `t₂` to `t₂ + 1` the four fields are kept
  have hkeep := stateBefore_succ_keepsConfirmation x hDiv v hti₂'
  rw [hst₂] at hkeep
  obtain ⟨k1, k2, k3, k4⟩ := hkeep
  refine ⟨?_, ?_, fun hHalf => ?_⟩
  · rw [k2, hsave]
    exact h25.1
  · rw [k4, hlatest]
    exact h25.2
  · have h28 :=
      GoldilocksCorrectness.Statements.Routines.lem28_update_confirmation_fast_locks_voter_majority_block
        S.C S.P (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int)) A''
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) B Hs (Nat.le_add_left 1 s) hRoots₂ hBne
        (by rw [fg_to_ac_F]; exact hF1) hPathF hHsE
        (by rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)]
            exact pool_slot_of_stateBefore S Sched x _ v s)
        (by rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)]; exact hVoters) hHalf hNoVeto
        hUpdate
    rw [Nat.add_sub_cancel] at h28
    refine ⟨?_, ?_⟩
    · rw [k3, hfast]
      exact h28.1
    · rw [k1, hlocks]
      exact h28.2

/-- Lemma 27, an honest validator's confirmation update confirms a block a voter majority voted
for. Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/FastConfirmationStatements.lean`.

Roots name blocks until `supportCutoff S s`: the bound of `confirmation_of_voter_majority`,
which it calls.

Restated with the delivery premises up to `supportCutoff S s`: the slot-`s` votes reach `v` by then (`lem12_honest_vote_delivered_until_upTo`). -/
theorem lem27_update_confirmation_confirms_voter_majority_block_upTo (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V)
    (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (supportCutoff S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      B ∈ (stateBefore x (voteTime S s) u).S.T)
    -- the validators with a slot-`s` vote in `v`'s pool before `t₂` are fewer than twice `Hs`
    (hVoters : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Hs.card)
    (hBne : B ≠ Block.genesis)
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hF1 : (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    -- the block of every lock entry live at `t₃` that `v`'s revocation leaves is compatible
    -- with `B`
    (hLocks : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) v).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) v).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) v).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true) :
    (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some B ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.latest_confirmed =
        advance (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
          (stateBefore x (supportCutoff S (s + 1)) v).A.latest_confirmed (some B) :=
  have h := confirmation_of_voter_majority_upTo S Sched x GST s Hs B v hDiv hMono hSync hCatch
    hRoots hParent hOwner hGST hHs hVoters hBne hv hF1 hLocks
  ⟨h.1, h.2.1⟩

end GoldilocksCorrectness.Proofs.Executions

