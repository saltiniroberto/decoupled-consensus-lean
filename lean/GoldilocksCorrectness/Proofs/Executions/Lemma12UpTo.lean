module
public import GoldilocksCorrectness.Proofs.Executions.Lemma12
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.VoteDeliveryUpTo

@[expose] public section

/-!
# `Lemma12.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma12.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `lem12_honest_vote_delivered_until`, `lem12_honest_vote_delivered`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem supportCutoff_cast
  supportCutoff_eq voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (tau_eq_ok_some)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  blockWithRoot_eq_ok find?_eq_some dre_bind_ok liftM_some occurrenceBefore_eq_true_iff)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The delivery lemma at any time `t₃` from the support cutoff of slot `s` on: `lem12`'s proof with
`t₃` in place of the vote time of slot `s + 1`, which it reads only through
`supportCutoff S s ≤ t₃` and `u`'s honesty up to it. `hw` covers only slot `s`'s vote time to its
support cutoff, the window the proof uses. Its
reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/DeliveryStatements.lean`. Roots name blocks until
`supportCutoff S s`: the proof takes `H u` as held by `w` at a delivery before the support cutoff
(`mem_T_before_add_delay` at the vote time).

Restated with the delivery premises up to `supportCutoff S s`: the votes and blocks of slot `s` reach `w` by then. -/
theorem lem12_honest_vote_delivered_until_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s t₃ : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (ht₃ : supportCutoff S s ≤ t₃)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (t₃ : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T)
    -- `w` is awake and honest from slot `s`'s vote time to its support cutoff
    (hw : ∀ t : ℕ, voteTime S s ≤ t → t ≤ supportCutoff S s →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hF : ∀ u ∈ Hs, (stateBefore x t₃ w).S.F.AncestorEq (H u)) :
    ∀ u ∈ Hs, HeldEarlyVoteFor S.C (stateBefore x t₃ w).A
      (fg_to_ac (stateBefore x t₃ w).S) s (H u) u := by
  intro u hu
  obtain ⟨hcomm, hhon, ⟨i, hl, hsent⟩, hHT⟩ := hHs u hu
  -- the times
  have hΔ := one_le_Δ S
  have ht₂ : voteTime S s + Δ S = supportCutoff S s := (supportCutoff_eq S s).symm
  have hv₁ : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have ht₁ : 1 ≤ voteTime S s := by omega
  have hle₂₃ : supportCutoff S s ≤ t₃ := ht₃
  have hslot : S.C.slot (voteTime S s : Int) = s := slot_eq_of_mem S (by omega) (by omega)
  -- honesty along the way
  have hu₁ : u ∉ Sched.adv (voteTime S s : Int) := fun h =>
    hhon (hMono _ _ (by exact_mod_cast (by omega : voteTime S s ≤ t₃)) h)
  have hu₂ : u ∉ Sched.adv (supportCutoff S s : Int) := fun h =>
    hhon (hMono _ _ (by exact_mod_cast hle₂₃) h)
  have hw₁ : ∀ t' : ℕ, voteTime S s ≤ t' → t' ≤ voteTime S s + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int) :=
    fun t' h1 h2 => hw t' h1 (by omega)
  -- steps 2 and 4: the vote is in `w`'s pool before `t₂`
  have hvote : GoldfishVote.mk u s (H u).root ∈
      (stateBefore x (supportCutoff S s) w).A.pool s := by
    rcases vote_in_pool_before_add_delay_upTo (vote := GoldfishVote.mk u s (H u).root) hDiv hMono
        (SynchronyFromWakeUpTo.mono (by omega) hSync) (CatchUpOnWakeUpTo.mono (by omega) hCatch)
        hl hsent (by omega) hslot.symm hcomm hu₁ hw₁ with
      ⟨h, -⟩ | ⟨v₁, h₁, v₂, h₂, hne, hi₁, hi₂⟩
    · rw [ht₂] at h
      exact h
    · rw [ht₂] at h₁ h₂
      exact absurd (unique_vote_of_owner hDiv hMono hOwner hu₂ h₁ h₂ hi₁ hi₂) hne
  -- step 3: `H u` is in `w`'s tree before `t₂`
  have hcompat : (stateBefore x (voteTime S s + Δ S) w).S.F.compatible (H u) = true :=
    (compatible_iff _ _).2 (Or.inl (ancestorEq_trans
      (stateBefore_grows x hDiv w (by omega : voteTime S s + Δ S ≤ t₃)).2.1
      (hF u hu)))
  have hblock : H u ∈ (stateBefore x (supportCutoff S s) w).S.T := by
    have h := mem_T_before_add_delay_upTo hDiv hMono (SynchronyFromWakeUpTo.mono (by omega) hSync)
      (CatchUpOnWakeUpTo.mono (by omega) hCatch) (hRoots.mono (by omega))
      hParent ht₁ hGST hu₁ hHT hw₁ hcompat
    rw [ht₂] at h
    exact h
  -- from `t₂` to `t₃`
  have hstep := stepBefore_mono x hDiv hle₂₃
  have hvote₃ : GoldfishVote.mk u s (H u).root ∈
      (stateBefore x t₃ w).A.pool s := pool_mono x w hstep s hvote
  have hblock₃ : H u ∈ (stateBefore x t₃ w).S.T := mem_T_mono x w hstep hblock
  -- step 5: the two stamps
  have hcut : ((((supportCutoff S s : ℕ) : Int)) : Stamp) =
      ((S.C.t_ s + 2 * S.C.Δ : Time) : Stamp) := by
    rw [supportCutoff_cast]
  obtain ⟨τv, hτv, hτvlt⟩ := (voteStamp_lt_iff hDiv hvote₃).2 hvote
  obtain ⟨τH, hτH, hτHlt⟩ := (blockStamp_lt_iff hDiv hblock₃).2 hblock
  rw [hcut] at hτvlt hτHlt
  -- the frame's tree, and its roots
  have hHΦ : H u ∈ (fg_to_ac (stateBefore x t₃ w).S).tree :=
    (mem_fg_to_ac_tree _ _).2 ⟨hblock₃, hF u hu⟩
  have hT₃ : x[stepBefore x t₃].time + 1 = t₃ :=
    (stepBefore_spec x hDiv (by omega)).2.1
  have hR : GoldilocksCorrectness.Statements.Routines.RootsNameBlocksIn
      (fg_to_ac (stateBefore x t₃ w).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ w
  have hHslot : (H u).slot ≤ s := hslot ▸ slot_le_of_mem_T_before hDiv hMono hHT
  -- the resolution
  have htau : (stateBefore x t₃ w).A.tau
      (fg_to_ac (stateBefore x t₃ w).S) (GoldfishVote.mk u s (H u).root) =
        .ok (some (max τv τH)) :=
    tau_eq_ok_some hR hHΦ rfl hHslot hτv hτH
  refine ⟨hvote₃, ⟨τv, hτv, hτvlt⟩, hHΦ, ⟨max τv τH, htau, ?_⟩, ?_⟩
  · exact (occurrenceBefore_eq_true_iff _ _).2 ⟨_, rfl, max_lt hτvlt hτHlt⟩
  · intro vote' hv' hi'
    exact unique_vote_of_owner hDiv hMono hOwner hhon hv' hvote₃ hi' rfl

/-- The delivery lemma. `hw` covers only slot `s`'s vote time to its support cutoff, the window
the proof uses. Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/DeliveryStatements.lean`. Roots name blocks until
`supportCutoff S s`: `lem12_honest_vote_delivered_until`'s bound.

Restated with the delivery premises up to `supportCutoff S s`: `lem12_honest_vote_delivered_until_upTo`'s bound. -/
theorem lem12_honest_vote_delivered_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (voteTime S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T)
    -- `w` is awake and honest from slot `s`'s vote time to its support cutoff
    (hw : ∀ t : ℕ, voteTime S s ≤ t → t ≤ supportCutoff S s →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hF : ∀ u ∈ Hs, (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq (H u)) :
    ∀ u ∈ Hs, HeldEarlyVoteFor S.C (stateBefore x (voteTime S (s + 1)) w).A
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) s (H u) u := by
  have hΔ := one_le_Δ S
  have hle : supportCutoff S s ≤ voteTime S (s + 1) := by
    rw [supportCutoff_eq, voteTime_succ]
    omega
  exact lem12_honest_vote_delivered_until_upTo S Sched x GST s (voteTime S (s + 1)) Hs H w hDiv hMono
    hSync hCatch hRoots hParent hOwner hGST hle hHs hw hF

end GoldilocksCorrectness.Proofs.Executions

