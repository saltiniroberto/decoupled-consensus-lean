module
public import GoldilocksCorrectness.Proofs.Executions.Lemma31
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery

@[expose] public section

/-!
# `Lemma31.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma31.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `lem31_saved_confirmations_compatible`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq supportCutoff_cast
  supportCutoff_eq viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (expireLocks_keepsVotes pool_of_keepsVotes
  tau_of_keepsVotes)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 31, two honest confirmation updates of a slot save compatible blocks.** In an
execution synchronous from the support cutoff of slot `s`, the confirmation updates of slot
`s + 1`, for the slot `s`, on the states of `v₁` and `v₂` before the support cutoff of slot
`s + 1`, their expired lock entries removed, that save `C₁` and `C₂` as the confirmation of slot
`s`, save compatible blocks, when each validator is awake and honest from the support cutoff of
slot `s` to its view freeze and honest at the support cutoff of slot `s + 1`.

Why: Lemma 30. A vote resolving early at one validator was held there before the support cutoff
of slot `s`, was re-sent then, and reaches the other within one delay, while it is awake; every
pool vote before the update is stamped before it; the two frame trees hold only blocks of honest
validators, where a root names one block.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot confirmed;
- `v₁`, `v₂`: the two validators; `A₁'`, `A₂'`: the AC states the two updates answer;
- `C₁`, `C₂`: the blocks saved.

Read aloud: in a synchronous execution from the support cutoff of slot `s`, if two validators,
each awake and honest from that cutoff for one delay and honest when the update for slot `s` runs,
have that update save `C₁` and `C₂`, then `C₁` and `C₂` are on one chain.

Roots name blocks until `supportCutoff S (s + 1)`: the proof compares the blocks of the two
frame trees on `v₁`'s and `v₂`'s states before the support cutoff of slot `s + 1`.

Restated with the delivery premises up to `supportCutoff S s + Δ S`: Lemma 62, in each direction, reads the re-sends at the support cutoff of slot `s`, due one delay after it. -/
theorem lem31_saved_confirmations_compatible_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (v₁ v₂ : V) (A₁' A₂' : ACState V)
    (C₁ C₂ : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s + Δ S))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s + Δ S))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    -- the network is synchronous from the support cutoff of slot `s` on
    (hGST : GST ≤ supportCutoff S s)
    -- `v₁` is awake and honest from the support cutoff of slot `s` to its view freeze
    (hv₁ : ∀ t : ℕ, supportCutoff S s ≤ t → t ≤ viewFreeze S s →
      v₁ ∈ Sched.awake (t : Int) ∧ v₁ ∉ Sched.adv (t : Int))
    -- `v₂` is awake and honest from the support cutoff of slot `s` to its view freeze
    (hv₂ : ∀ t : ℕ, supportCutoff S s ≤ t → t ≤ viewFreeze S s →
      v₂ ∈ Sched.awake (t : Int) ∧ v₂ ∉ Sched.adv (t : Int))
    -- `v₁` and `v₂` are honest at the support cutoff of slot `s + 1`, when the updates run
    (hHon₁ : v₁ ∉ Sched.adv (supportCutoff S (s + 1) : Int))
    (hHon₂ : v₂ ∉ Sched.adv (supportCutoff S (s + 1) : Int))
    -- the update of slot `s + 1` on `v₁`'s state before `t₂`, its expired locks removed, answers
    -- `A₁'` and saves `C₁` as the confirmation of slot `s`
    (hUpdate₁ : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v₁).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v₁).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A₁')
    (hSaved₁ : A₁'.saved_confirmation s = some C₁)
    -- likewise at `v₂`
    (hUpdate₂ : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v₂).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v₂).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A₂')
    (hSaved₂ : A₂'.saved_confirmation s = some C₂) :
    -- then `C₁` and `C₂` are compatible
    C₁.compatible C₂ = true := by
  -- the roots name blocks across the two frame trees
  have hRoots₁₂ : RootsNameBlocksIn
      ((fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v₁).S).tree ∪
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v₂).S).tree) := by
    have hin : ∀ B ∈ (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v₁).S).tree ∪
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v₂).S).tree,
        inHonestTreeBy x (supportCutoff S (s + 1)) B := by
      have hΔ := one_le_Δ S
      have hv₂t : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
      have ht₂ : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
      have hT := (stepBefore_spec x hDiv (show 1 ≤ supportCutoff S (s + 1) by omega)).2.1
      intro B hB
      rcases Finset.mem_union.1 hB with hB | hB
      · exact ⟨_, v₁, honest_stepBefore_supportCutoff S Sched x s v₁ hDiv hMono hHon₁,
          by omega, ((mem_fg_to_ac_tree _ _).1 hB).1⟩
      · exact ⟨_, v₂, honest_stepBefore_supportCutoff S Sched x s v₂ hDiv hMono hHon₂,
          by omega, ((mem_fg_to_ac_tree _ _).1 hB).1⟩
    exact fun B hB B' hB' hroot => hRoots B B' (hin B hB) (hin B' hB') hroot
  -- the times
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss2 : slotStart S (s + 2) = slotStart S (s + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_add]
    omega
  have hv₁t : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hc : supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S s
  have hv₂t : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have ht₂ : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hfr : viewFreeze S s = slotStart S s + 3 * Δ S := viewFreeze_eq S s
  -- the early votes of each validator reach the other (Lemma 62, once in each direction)
  have h12 := GoldilocksCorrectness.Statements.Executions.lem62_early_vote_reaches_at S Sched x GST
    s (supportCutoff S s) (supportCutoff S (s + 1)) (supportCutoff S (s + 1))
    (supportCutoff S s + Δ S) v₁ v₂ (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v₁).S) hDiv
    hMono hSync hCatch hGST (by omega) (by omega)
    (fun t h1 h2 => hv₂ t h1 (by omega)) le_rfl
  have h21 := GoldilocksCorrectness.Statements.Executions.lem62_early_vote_reaches_at S Sched x GST
    s (supportCutoff S s) (supportCutoff S (s + 1)) (supportCutoff S (s + 1))
    (supportCutoff S s + Δ S) v₂ v₁ (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v₂).S) hDiv
    hMono hSync hCatch hGST (by omega) (by omega)
    (fun t h1 h2 => hv₁ t h1 (by omega)) le_rfl
  rw [supportCutoff_cast] at h12 h21
  have key := GoldilocksCorrectness.Statements.Routines.lem30_saved_confirmations_compatible S.C
    S.P _ A₁' _ A₂' _ _ _ _ (s + 1) C₁ C₂ (Nat.le_add_left 1 s) hRoots₁₂
    (by rw [Nat.add_sub_cancel, pool_of_keepsVotes (expireLocks_keepsVotes _ _)]
        exact pool_vote_late S Sched x s v₁ hDiv)
    (by rw [Nat.add_sub_cancel, pool_of_keepsVotes (expireLocks_keepsVotes _ _)]
        exact pool_vote_late S Sched x s v₂ hDiv)
    (by simp only [Nat.add_sub_cancel, pool_of_keepsVotes (expireLocks_keepsVotes _ _),
          tau_of_keepsVotes (expireLocks_keepsVotes _ _)]
        exact h12)
    (by simp only [Nat.add_sub_cancel, pool_of_keepsVotes (expireLocks_keepsVotes _ _),
          tau_of_keepsVotes (expireLocks_keepsVotes _ _)]
        exact h21)
    hUpdate₁ (by rw [Nat.add_sub_cancel]; exact hSaved₁) hUpdate₂
    (by rw [Nat.add_sub_cancel]; exact hSaved₂)
  exact key

end GoldilocksCorrectness.Proofs.Executions

