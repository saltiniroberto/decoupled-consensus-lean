module
public import GoldilocksCorrectness.Proofs.Routines.Lemma77Compat
public import GoldilocksCorrectness.Proofs.Executions.Lemma78UpTo
public import GoldilocksCorrectness.Proofs.Executions.VoteDeliveryUpTo

@[expose] public section

/-! New statements, the compatible variants of Lemma 78
(`lem78_update_confirmation_extends_voter_majority_chain`) and of its twin before a bound; the
landed ones stay as they are. The audited statements are in
`Statements/Executions/ConfirmationCompatStatements.lean`. Write `c := supportCutoff S (s + 1)`.

- `lem78c_of_delivered`: the common step. When `v`'s finalized block before `c` is `B` or an
  ancestor of `B`, and every member's vote and block are in `v`'s pool and tree before the support
  cutoff of `s`, Lemma 77c applies at `v`'s update at `c`; when `B` is an ancestor of that
  finalized block, the saved block descends from it (`saved_confirmation_F_ancestorEq`).
- `lem78c_update_confirmation_compatible_of_voter_majority` and its twin `_upTo`: the deliveries
  by `vote_in_pool_before_add_delay` and `mem_T_before_add_delay` (or their twins before the
  bound), the uniqueness by `unique_vote_of_owner`, as Lemma 12's steps 2 to 4.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq
  slot_eq_of_mem supportCutoff_cast supportCutoff_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (expireLocks_keepsVotes fg_to_ac_F pool_of_keepsVotes)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  compatible_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **The common step of Lemma 78c.** For `v` awake and honest from the duty window of slot
`s + 1` to `c`, with its finalized block before `c` compatible with `B`: when, in the case that
finalized block is `B` or an ancestor of `B`, every member `u` of `Hs` has its slot-`s` vote for
`H u` in `v`'s pool and `H u` in `v`'s tree before the support cutoff of `s`, every member is
honest at `c`, every `H u` is compatible with `B`, and fewer than twice `Hs` validators have a
slot-`s` vote in `v`'s pool before `c`, the confirmation `v`'s update at `c` saves for `s` is
compatible with `B`.

Why: the vote stays in the pool, stamped before the support cutoff of `s`, so before the late
cutoff; it is its voter's only vote of the slot (`unique_vote_of_owner`); a block of `v`'s frame
tree named by its head is `H u` (no two blocks of a node's tree share a root); then Lemma 77c.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot of the votes; `Hs`:
  the voters; `H`: their blocks; `B`: the block; `v`: the validator whose update it is. -/
theorem lem78c_of_delivered (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (Hs : Finset V) (H : V → Block V) (B : Block V)
    (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hOwner : VotesCastByOwner S Sched x)
    (hHon : ∀ u ∈ Hs, u ∉ Sched.adv (supportCutoff S (s + 1) : Int))
    (hDel : (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B → ∀ u ∈ Hs,
      GoldfishVote.mk u s (H u).root ∈ (stateBefore x (supportCutoff S s) v).A.pool s ∧
      H u ∈ (stateBefore x (supportCutoff S s) v).S.T)
    (hHB : ∀ u ∈ Hs, (H u).compatible B = true)
    (hVoters : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Hs.card)
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hF : (stateBefore x (supportCutoff S (s + 1)) v).S.F.compatible B = true) :
    ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some C' →
      C'.compatible B = true := by
  intro C' hC'
  -- the times
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₂ : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hc₁ : supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S s
  have hv₁ : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hdw : dutyWindowStart S (s + 1) ≤ slotStart S s := dutyWindowStart_succ_le_slotStart S s
  have hdwc : dutyWindowStart S (s + 1) < supportCutoff S (s + 1) := by omega
  -- the update at `c` and the state right after it
  have hvc := hv (supportCutoff S (s + 1)) hdwc.le le_rfl
  have hAw := awakeSince_le_dutyWindowStart_b S Sched x (s + 1) (supportCutoff S (s + 1)) v hDiv
    hMono hdwc (fun t h1 h2 => (hv t h1 h2).1) hvc.2
  obtain ⟨A'', hUpdate, hsave, -, -, -⟩ := update_state_of_duty S Sched x s v hDiv hvc hAw
  rw [hsave] at hC'
  rcases (compatible_iff _ _).1 hF with hFB | hBF
  · -- the finalized block is `B` or an ancestor of `B`: Lemma 77c
    have hDel' := hDel hFB
    have hle : supportCutoff S s ≤ supportCutoff S (s + 1) := by omega
    have hstep := stepBefore_mono x hDiv hle
    have hcut : ((((supportCutoff S s : ℕ) : Int)) : Stamp) =
        ((S.C.t_ s + 2 * S.C.Δ : Time) : Stamp) := by
      rw [supportCutoff_cast]
    have hΔpos : (0 : Int) < S.C.Δ := S.C.Δ_pos
    have hlt26 : ((S.C.t_ s + 2 * S.C.Δ : Time) : Stamp) <
        ((S.C.t_ s + 6 * S.C.Δ : Time) : Stamp) :=
      WithBot.coe_lt_coe.2 (Int.add_lt_add_left (Int.mul_lt_mul_of_pos_right (by decide) hΔpos) _)
    have hHs77 : ∀ u ∈ Hs, ∃ vote ∈ (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int)).pool (s + 1 - 1), vote.val_index = u ∧
        (∃ τ : Stamp, (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
            ((supportCutoff S (s + 1) : ℕ) : Int)).timestamp_vote vote = some τ ∧
          τ < ((S.C.t_ (s + 1 - 1) + 6 * S.C.Δ : Time) : Stamp)) ∧
        (∀ vote' ∈ (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int)).pool (s + 1 - 1), vote'.val_index = u →
            vote' = vote) ∧
        ∀ D ∈ (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree,
          D.root = vote.head → D.compatible B = true := by
      rw [Nat.add_sub_cancel, pool_of_keepsVotes (expireLocks_keepsVotes _ _)]
      intro u hu
      obtain ⟨hvote, hblock⟩ := hDel' u hu
      have hvote₃ : GoldfishVote.mk u s (H u).root ∈
          (stateBefore x (supportCutoff S (s + 1)) v).A.pool s := pool_mono x v hstep s hvote
      have hblock₃ : H u ∈ (stateBefore x (supportCutoff S (s + 1)) v).S.T :=
        mem_T_mono x v hstep hblock
      obtain ⟨τ, hτ, hτlt⟩ := (voteStamp_lt_iff hDiv hvote₃).2 hvote
      rw [hcut] at hτlt
      refine ⟨GoldfishVote.mk u s (H u).root, hvote₃, rfl, ⟨τ, hτ, lt_trans hτlt hlt26⟩,
        fun vote' hv' hval' => unique_vote_of_owner hDiv hMono hOwner (hHon u hu) hv' hvote₃ hval'
          rfl, fun D hD hDr => ?_⟩
      have hDT : D ∈ (stateBefore x (supportCutoff S (s + 1)) v).S.T :=
        ((mem_fg_to_ac_tree _ _).1 hD).1
      have hDH : D = H u := (lem11_node_invariant S Sched x
        (stepBefore x (supportCutoff S (s + 1))) v).1.2.2.2.2.2.2.2.2.2.1.1 D hDT (H u) hblock₃ hDr
      rw [hDH]
      exact hHB u hu
    have h77 := GoldilocksCorrectness.Proofs.Routines.lem77c_update_confirmation_compatible_of_majority
      S.C S.P (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
        ((supportCutoff S (s + 1) : ℕ) : Int)) A''
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
      ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) B Hs (Nat.le_add_left 1 s)
      (rootsNameBlocksIn_frame_of_exec_node S Sched x _ v) hHs77
      (by rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)]; exact hVoters) hUpdate
    rw [Nat.add_sub_cancel] at h77
    exact h77 C' hC'
  · -- `B` is an ancestor of the finalized block: the saved block descends from it
    have h := GoldilocksCorrectness.Statements.Routines.saved_confirmation_F_ancestorEq S.C S.P _
      A'' _ _ (s + 1) (Nat.le_add_left 1 s) hUpdate
    rw [Nat.add_sub_cancel] at h
    exact (compatible_iff _ _).2 (Or.inr (ancestorEq_trans hBF
      (by rw [← fg_to_ac_F]; exact h C' hC')))

/-- The receiver's side of the deliveries: when `v`'s finalized block before `c` is `B` or an
ancestor of `B`, its finalized block one delay after the vote time of `s` is compatible with every
block compatible with `B`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `B`: the block; `v`:
  the receiver; `D`: the block compatible with `B`. -/
theorem F_compatible_of_le_ancestorEq (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (B : Block V) (v : V) (D : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hFB : (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    (hDB : D.compatible B = true) :
    (stateBefore x (voteTime S s + Δ S) v).S.F.compatible D = true := by
  have hle : voteTime S s + Δ S ≤ supportCutoff S (s + 1) := by
    have h1 := supportCutoff_eq S (s + 1)
    have h2 := voteTime_eq S (s + 1)
    have h3 := voteTime_eq S s
    have h4 : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    omega
  have hFe := ancestorEq_trans (stateBefore_grows x hDiv v hle).2.1 hFB
  rcases (compatible_iff _ _).1 hDB with hDB' | hBD
  · exact (compatible_iff _ _).2 (ancestorEq_compatible hFe hDB')
  · exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFe hBD))

/-- **Lemma 78c, an honest confirmation update over a majority whose votes are compatible with
`B`.** The proof; the audited statement is in
`Statements/Executions/ConfirmationCompatStatements.lean`. `lem78c_of_delivered`, with each
member's vote delivered into `v`'s pool (`vote_in_pool_before_add_delay`, `unique_vote_of_owner`)
and its block into `v`'s tree (`mem_T_before_add_delay`) before the support cutoff of `s`, as
Lemma 12's steps 2 to 4.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the votes; `Hs`: the voters; `H`: their blocks; `B`:
  the block; `v`: the validator whose update it is. -/
theorem lem78c_update_confirmation_compatible_of_voter_majority (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (supportCutoff S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ (H u).compatible B = true)
    (hVoters : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Hs.card)
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hF : (stateBefore x (supportCutoff S (s + 1)) v).S.F.compatible B = true) :
    ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some C' →
      C'.compatible B = true := by
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₂ : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hc₁ : supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S s
  have hv₁ : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hdw : dutyWindowStart S (s + 1) ≤ slotStart S s := dutyWindowStart_succ_le_slotStart S s
  refine lem78c_of_delivered S Sched x s Hs H B v hDiv hMono hOwner (fun u hu => (hHs u hu).2.1)
    ?_ (fun u hu => (hHs u hu).2.2.2.2) hVoters hv hF
  intro hFB u hu
  obtain ⟨hcomm, hhon, ⟨i, hl, hsent⟩, hHT, hHB⟩ := hHs u hu
  have ht₁ : 1 ≤ voteTime S s := by omega
  have hslot : S.C.slot (voteTime S s : Int) = s := slot_eq_of_mem S (by omega) (by omega)
  have hu₁ : u ∉ Sched.adv (voteTime S s : Int) := fun h =>
    hhon (hMono _ _ (by exact_mod_cast (by omega : voteTime S s ≤ supportCutoff S (s + 1))) h)
  have hu₂ : u ∉ Sched.adv (supportCutoff S s : Int) := fun h =>
    hhon (hMono _ _ (by exact_mod_cast (by omega : supportCutoff S s ≤ supportCutoff S (s + 1))) h)
  have hw₁ : ∀ t' : ℕ, voteTime S s ≤ t' → t' ≤ voteTime S s + Δ S →
      v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int) :=
    fun t' h1 h2 => hv t' (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · rcases vote_in_pool_before_add_delay (vote := GoldfishVote.mk u s (H u).root) hDiv hMono
        hSync hCatch hl hsent hGST hslot.symm hcomm hu₁ hw₁ with
      ⟨h, -⟩ | ⟨v₁, h₁, v₂, h₂, hne, hi₁, hi₂⟩
    · rw [← hc₁] at h
      exact h
    · rw [← hc₁] at h₁ h₂
      exact absurd (unique_vote_of_owner hDiv hMono hOwner hu₂ h₁ h₂ hi₁ hi₂) hne
  · have h := mem_T_before_add_delay hDiv hMono hSync hCatch (hRoots.mono (by omega))
      hParent ht₁ hGST hu₁ hHT hw₁ (F_compatible_of_le_ancestorEq S Sched x s B v (H u) hDiv hFB hHB)
    rw [← hc₁] at h
    exact h

/-- **Lemma 78c with the delivery premises up to the support cutoff of `s`.** The proof; the
audited statement is in `Statements/Executions/ConfirmationCompatStatements.lean`. Lemma 78c's
proof with the deliveries' twins before the bound (`vote_in_pool_before_add_delay_upTo`,
`mem_T_before_add_delay_upTo`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the votes; `Hs`: the voters; `H`: their blocks; `B`:
  the block; `v`: the validator whose update it is. -/
theorem lem78c_update_confirmation_compatible_of_voter_majority_upTo (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (B : Block V) (v : V)
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
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ (H u).compatible B = true)
    (hVoters : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Hs.card)
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hF : (stateBefore x (supportCutoff S (s + 1)) v).S.F.compatible B = true) :
    ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some C' →
      C'.compatible B = true := by
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₂ : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hc₁ : supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S s
  have hv₁ : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hdw : dutyWindowStart S (s + 1) ≤ slotStart S s := dutyWindowStart_succ_le_slotStart S s
  refine lem78c_of_delivered S Sched x s Hs H B v hDiv hMono hOwner (fun u hu => (hHs u hu).2.1)
    ?_ (fun u hu => (hHs u hu).2.2.2.2) hVoters hv hF
  intro hFB u hu
  obtain ⟨hcomm, hhon, ⟨i, hl, hsent⟩, hHT, hHB⟩ := hHs u hu
  have ht₁ : 1 ≤ voteTime S s := by omega
  have hslot : S.C.slot (voteTime S s : Int) = s := slot_eq_of_mem S (by omega) (by omega)
  have hu₁ : u ∉ Sched.adv (voteTime S s : Int) := fun h =>
    hhon (hMono _ _ (by exact_mod_cast (by omega : voteTime S s ≤ supportCutoff S (s + 1))) h)
  have hu₂ : u ∉ Sched.adv (supportCutoff S s : Int) := fun h =>
    hhon (hMono _ _ (by exact_mod_cast (by omega : supportCutoff S s ≤ supportCutoff S (s + 1))) h)
  have hw₁ : ∀ t' : ℕ, voteTime S s ≤ t' → t' ≤ voteTime S s + Δ S →
      v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int) :=
    fun t' h1 h2 => hv t' (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · rcases vote_in_pool_before_add_delay_upTo (vote := GoldfishVote.mk u s (H u).root) hDiv hMono
        (hSync.mono (by omega)) (hCatch.mono (by omega)) hl hsent hGST hslot.symm hcomm hu₁ hw₁ with
      ⟨h, -⟩ | ⟨v₁, h₁, v₂, h₂, hne, hi₁, hi₂⟩
    · rw [← hc₁] at h
      exact h
    · rw [← hc₁] at h₁ h₂
      exact absurd (unique_vote_of_owner hDiv hMono hOwner hu₂ h₁ h₂ hi₁ hi₂) hne
  · have h := mem_T_before_add_delay_upTo hDiv hMono (hSync.mono (by omega))
      (hCatch.mono (by omega)) (hRoots.mono (by omega))
      hParent ht₁ hGST hu₁ hHT hw₁ (F_compatible_of_le_ancestorEq S Sched x s B v (H u) hDiv hFB hHB)
    rw [← hc₁] at h
    exact h

end GoldilocksCorrectness.Proofs.Executions
