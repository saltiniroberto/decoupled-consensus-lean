module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Stability
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatementsUpTo

@[expose] public section

/-!
# `Lemma89Stability.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89Stability.lean` that name a
delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the
deadlines. The bound of
each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in
the twin's own parameters.

* `mem_T_of_delivery_high`, `confirmation_saved_of_votes`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq
  supportCutoff_eq voteTime_eq)

open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes
  fg_to_ac_F pool_of_keepsVotes)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **A block an honest validator holds reaches another within one delay, when it is higher than
the other's cache `h_j`.** Under the execution assumptions and unforgeability, from `GST` on, with
fewer than a third of the validators in the adversary set up to `tEnd`: when `v` is honest at
`t₀ ≥ 1` and holds `Y` before `t₀`, `u` is awake and honest from `t₀` to `t₀ + Δ ≤ tEnd`, and `Y`'s
chain-state height is greater than `u`'s cache `h_j` before `t₀ + Δ`, then `u` holds `Y` before
`t₀ + Δ`.

Why: `u`'s finalized block then is an ancestor of `Y` (`F_ancestorEq_of_high`), so compatible with
it, and `mem_T_before_add_delay_of_held`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tEnd`, `t₀`: the times;
  `v`, `u`: the holder and the receiver; `Y`: the block.

Roots name blocks until `tR`, at least `t₀ + Δ S`: `Y`, held by `v` before `t₀`, reaches `u` by
`t₀ + Δ S`, and `F_ancestorEq_of_high` at those two times.

Restated with the delivery premises up to `tR`: the bound of its roots, at least `t₀ + Δ S` (`htR`), the deadline of the one delivery its proof reads; the implicit `tR` moved ahead of the premises. -/
theorem mem_T_of_delivery_high_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST : ℕ) (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) {tR : ℕ}
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject tR)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject tR)
    (hRoots : RootsNameBlocksUntil S Sched x tR)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (tEnd t₀ : ℕ) (v u : V) (Y : Block V)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int)) (hEnd : t₀ + Δ S ≤ tEnd)
    (h1 : 1 ≤ t₀) (hGST : GST ≤ t₀)
    (hv : v ∉ Sched.adv (t₀ : Int)) (hY : Y ∈ (stateBefore x t₀ v).S.T)
    (hu : ∀ t' : ℕ, t₀ ≤ t' → t' ≤ t₀ + Δ S →
      u ∈ Sched.awake (t' : Int) ∧ u ∉ Sched.adv (t' : Int))
    (hlt : (stateBefore x (t₀ + Δ S) u).S.h_j < (chainStateOf S.C Y).h)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : t₀ + Δ S ≤ tR) :
    Y ∈ (stateBefore x (t₀ + Δ S) u).S.T := by
  have hFY := F_ancestorEq_of_high S Sched x hMono hU hRoots tEnd (t₀ + Δ S) t₀ u v Y hThird hEnd
    (by omega) (hu (t₀ + Δ S) (by omega) le_rfl).2 hv hY hlt (max_le htR (by omega))
  exact mem_T_before_add_delay_of_held_upTo hDiv hMono (hSync.mono htR) (hCatch.mono htR) (hRoots.mono htR) hParent
    (t₁ := t₀) (t := t₀) h1 le_rfl hGST hv hY hu ((compatible_iff _ _).2 (Or.inl hFY))

/-- **An honest update saves a confirmation when a voter majority votes on the chain of the
updater's finalized block.** Lemma 78's hypotheses with `B` the finalized block of `v` before the
support cutoff `c` of slot `s + 1`: when `GST` is at most the vote time of slot `s`; every member of
`Hs` is in the slot-`s` committee, honest through `c`, sent its slot-`s` vote for `H u`, a block it
holds that is `v`'s finalized block or a descendant of it; the validators with a slot-`s` vote in
`v`'s pool before `c` are fewer than twice `Hs`; and `v` is awake and honest from the duty window's
start of slot `s + 1` to `c` — then `v` holds right after `c` some confirmation of slot `s`.

Why: Lemma 78's first case: Lemma 12 delivers every member's vote to `v`, held early, so each is an
early supporter of `v`'s finalized block, and `update_confirmation_saves`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the votes; `Hs`: the honest voters; `H`: the block each
  voter's vote is for; `v`: the updater.

Roots name blocks until `supportCutoff S s`: Lemma 12 at slot `s`.

Restated with the delivery premises up to `supportCutoff S s`: the bound of its roots, Lemma 12 at slot `s` (`lem12_honest_vote_delivered_until_upTo`). -/
theorem confirmation_saved_of_votes_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (v : V)
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
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧
      (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq (H u))
    (hVoters : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Hs.card)
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int)) :
    ∃ C' : Block V,
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some C' := by
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₂ : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hc₁ : supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S s
  have hv₁ : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hdw : dutyWindowStart S (s + 1) ≤ slotStart S s := dutyWindowStart_succ_le_slotStart S s
  have hdwc : dutyWindowStart S (s + 1) < supportCutoff S (s + 1) := by omega
  have hvc := hv (supportCutoff S (s + 1)) hdwc.le le_rfl
  have hAw := awakeSince_le_dutyWindowStart_b S Sched x (s + 1) (supportCutoff S (s + 1)) v hDiv
    hMono hdwc (fun t h1 h2 => (hv t h1 h2).1) hvc.2
  obtain ⟨A'', hUpdate, hsave, -, -, -⟩ := update_state_of_duty S Sched x s v hDiv hvc hAw
  rw [hsave]
  have hHeld : ∀ u ∈ Hs, HeldEarlyVoteFor S.C (stateBefore x (supportCutoff S (s + 1)) v).A
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) s (H u) u :=
    GoldilocksCorrectness.Statements.Executions.lem12_honest_vote_delivered_until_upTo S Sched x GST s
      (supportCutoff S (s + 1)) Hs H v hDiv hMono hSync hCatch hRoots hParent hOwner hGST
      (by omega)
      (fun u hu => ⟨(hHs u hu).1, (hHs u hu).2.1, (hHs u hu).2.2.1, (hHs u hu).2.2.2.1⟩)
      (fun t h1 h2 => hv t (by omega) (by omega))
      (fun u hu => (hHs u hu).2.2.2.2)
  have hRoots₂ : RootsNameBlocksIn
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ v
  have hSup : ∀ u ∈ Hs, EarlySupporterOf S.C
      (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
        ((supportCutoff S (s + 1) : ℕ) : Int))
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) (s + 1 - 1)
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).F u :=
    fun u hu => (earlySupporterOf_of_keepsVotes (expireLocks_keepsVotes _ _) _ _ _ _ _).2
      (heldEarlyVoteFor_earlySupporterOf S.C _ _ s _ (H u) u (hHeld u hu)
        (by rw [fg_to_ac_F]; exact (hHs u hu).2.2.2.2))
  have h := GoldilocksCorrectness.Proofs.Routines.update_confirmation_saves S.C S.P
    (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
      ((supportCutoff S (s + 1) : ℕ) : Int)) A''
    (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
    ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) Hs (Nat.le_add_left 1 s) hRoots₂ hSup
    (by rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)]; exact pool_slot_of_stateBefore S Sched x _ v s)
    (by rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)]; exact hVoters) hUpdate
  rw [Nat.add_sub_cancel] at h
  exact h

end GoldilocksCorrectness.Proofs.Executions

