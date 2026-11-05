module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89StabilityB6
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.Lemma89rUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89StabilityUpTo
public import GoldilocksCorrectness.Proofs.Executions.VoteDeliveryUpTo

@[expose] public section

/-!
# `Lemma89StabilityB6.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89StabilityB6.lean` that name a
delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the
deadlines. The bound of
each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in
the twin's own parameters.

* `floor_le_of_viable`, `finalized_compatible_of_viable`, `root_compatible_of_viable`,
  `honest_supporter_of_update`, `honest_supporter_of_saved`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq
  slot_eq_of_mem supportCutoff_cast supportCutoff_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (fg_contest_true_of floor_cases h_max_le_floor_add_one
  mem_fg_to_ac_tree root_cases)

open GoldilocksCorrectness.Proofs.Routines (update_confirmation_supporter)

open GoldilocksCorrectness.Proofs.Routines (expireLocks_keepsVotes pool_of_keepsVotes)

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

/-- **The `head_height_floor` of a validator one delay before a viable block of another is at most
that block's height.** Under the execution assumptions and unforgeability, from `GST` on, with
fewer than a third of the validators in the adversary set up to `tEnd`: when `w` is honest at `t₀`,
`u` is awake and honest from `t₀` to `t₀ + Δ ≤ tEnd`, and `W` is a viable head of `u`'s frame
before `t₀ + Δ`, then `w`'s `head_height_floor` before `t₀` is at most `W`'s chain-state height
(`floor_le_of_delivery_unordered`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tEnd`, `t₀`: the times;
  `w`, `u`: the two validators; `W`: the block.

Roots name blocks until `tR`, at least `t₀ + Δ S`: the proof reads
`floor_le_of_delivery_unordered` at `t₀`, whose blocks are held by `t₀ + Δ`.

Restated with the delivery premises up to `tR`: the bound of its roots, at least `t₀ + Δ S` (`htR`), the deadline of the one delivery its proof reads; the implicit `tR` moved ahead of the premises. -/
theorem floor_le_of_viable_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST : ℕ) (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) {tR : ℕ}
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject tR)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject tR)
    (hRoots : RootsNameBlocksUntil S Sched x tR)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (tEnd t₀ : ℕ) (w u : V) (W : Block V)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int)) (hEnd : t₀ + Δ S ≤ tEnd)
    (hGST : GST ≤ t₀) (hw : w ∉ Sched.adv (t₀ : Int))
    (hu : ∀ t' : ℕ, t₀ ≤ t' → t' ≤ t₀ + Δ S →
      u ∈ Sched.awake (t' : Int) ∧ u ∉ Sched.adv (t' : Int))
    (hW : W ∈ (fg_to_ac (stateBefore x (t₀ + Δ S) u).S).viable_heads)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : t₀ + Δ S ≤ tR) :
    head_height_floor (stateBefore x t₀ w).S ≤ (chainStateOf S.C W).h := by
  have hA : AdversaryFewerThanThirdUntil Sched (validator_count V) ((t₀ + Δ S : ℕ) : Int) :=
    adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hEnd) hThird
  have h := floor_le_of_delivery_unordered_upTo S Sched x GST t₀ w u hDiv hMono (hSync.mono htR) (hCatch.mono htR)
    (hRoots.mono htR) hParent hU hA hGST hw hu
  exact le_trans h (viable_props S Sched x _ u W hW).2.2.2

/-- **A validator's finalized block one delay before a viable block of another is compatible with
it.** The hypotheses of `floor_le_of_viable`, with `t₀ ≥ 1`.

Why (`f` the finalization height of the chain state of a block `D` that finalized `w`'s block):
when `W` is higher than `f`, Lemma 89a. Otherwise `head_height_floor` at `u` (the least chain-state height a viable block may have) is at most `f`, so its cache `h_j` is
less than `D`'s height, `D` reaches `u` and gives it the cache `h_j = f`: `u` then has
`h_max = f + 1`, is not contested (its `head_height_floor` would be `f + 1`, greater than `W`'s height), so
its root is its justified block, which is `w`'s finalized block (Lemma 76), an ancestor of the
viable `W`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tEnd`, `t₀`: the times;
  `w`, `u`: the two validators; `W`: the block.

Roots name blocks until `tR`, at least `t₀ + Δ S`: every block the proof compares is held by `w`
before `t₀` or by `u` before `t₀ + Δ`.

Restated with the delivery premises up to `tR`: the bound of its roots, at least `t₀ + Δ S` (`htR`), read through `mem_T_of_delivery_high_upTo` at that bound; the implicit `tR` moved ahead of the premises. -/
theorem finalized_compatible_of_viable_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST : ℕ) (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) {tR : ℕ}
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject tR)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject tR)
    (hRoots : RootsNameBlocksUntil S Sched x tR)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (tEnd t₀ : ℕ) (w u : V) (W : Block V)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int)) (hEnd : t₀ + Δ S ≤ tEnd)
    (h1 : 1 ≤ t₀) (hGST : GST ≤ t₀) (hw : w ∉ Sched.adv (t₀ : Int))
    (hu : ∀ t' : ℕ, t₀ ≤ t' → t' ≤ t₀ + Δ S →
      u ∈ Sched.awake (t' : Int) ∧ u ∉ Sched.adv (t' : Int))
    (hW : W ∈ (fg_to_ac (stateBefore x (t₀ + Δ S) u).S).viable_heads)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : t₀ + Δ S ≤ tR) :
    (stateBefore x t₀ w).S.F.compatible W = true := by
  obtain ⟨hWT, -, hrW, hflW⟩ := viable_props S Sched x _ u W hW
  have huE : u ∉ Sched.adv ((t₀ + Δ S : ℕ) : Int) := (hu (t₀ + Δ S) (by omega) le_rfl).2
  obtain ⟨D, hD, hF⟩ := finalizedFromChain_of_exec S Sched x (stepBefore x t₀) w
  have hSt : stateBefore x t₀ w = x[stepBefore x t₀][w].st := rfl
  rw [← hSt] at hD hF
  by_cases hlt : (chainStateOf S.C D).h_F < (chainStateOf S.C W).h
  · rw [hF, compatible_iff]
    exact Or.inl (finalized_ancestorEq_of_held S Sched x hMono hU hRoots tEnd t₀ (t₀ + Δ S) w u D
      W hThird (by omega) hEnd hw huE hD hWT hlt (by omega))
  push Not at hlt
  by_cases hf0 : (chainStateOf S.C D).h_F = 0
  · rw [hF, GoldilocksCorrectness.Proofs.Routines.chainStateOf_F_genesis S.C D hf0, compatible_iff]
    exact Or.inl (genesis_ancestorEq W)
  have hf1 : 1 ≤ (chainStateOf S.C D).h_F := Nat.one_le_iff_ne_zero.mpr hf0
  have h47 := (lem47_chain_state_heights S.C D D).1
  have hmu := h_max_le_floor_add_one (stateBefore x (t₀ + Δ S) u).S
  have hju := h_j_lt_h_max S Sched x (t₀ + Δ S) u
  have hDh : (stateBefore x (t₀ + Δ S) u).S.h_j < (chainStateOf S.C D).h := by
    unfold Height at *
    omega
  have hDu := mem_T_of_delivery_high_upTo S Sched x GST hDiv hMono hSync hCatch hRoots hParent
    hU tEnd t₀ w u D hThird hEnd h1 hGST hw hD hu hDh htR
  have hFuD := F_ancestorEq_of_high S Sched x hMono hU hRoots tEnd (t₀ + Δ S) (t₀ + Δ S) u u D
    hThird hEnd hEnd huE huE hDu hDh (by omega)
  have hjD := h_j_of_mem_T_of_stateBefore S Sched x _ u D hDu hFuD
  rw [σ_eq_of_stateBefore S Sched x _ u D hDu] at hjD
  have hjeq : (stateBefore x (t₀ + Δ S) u).S.h_j = (chainStateOf S.C D).h_F := by
    unfold Height at *
    omega
  have hmeq : (stateBefore x (t₀ + Δ S) u).S.h_max = (stateBefore x (t₀ + Δ S) u).S.h_j + 1 := by
    unfold Height at *
    omega
  have hroot : get_fc_root (stateBefore x (t₀ + Δ S) u).S = (stateBefore x (t₀ + Δ S) u).S.J := by
    rcases root_cases (stateBefore x (t₀ + Δ S) u).S with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exfalso
      rcases h with h | h
      · obtain ⟨-, -, hfl⟩ :=
          GoldilocksCorrectness.Statements.Routines.frameShape_of_boxThree _ h
        rw [hfl] at hflW
        unfold Height at *
        omega
      · exact h hmeq
  have hFJ := F_eq_J_of_height S Sched x hMono hU hRoots tEnd t₀ (t₀ + Δ S) w u D hThird
    (by omega) hEnd hw huE hD hF hf1 hjeq (by omega)
  rw [hFJ, ← hroot, compatible_iff]
  exact Or.inl hrW

/-- **A validator's fork-choice root one delay before a viable block of another, when it holds
that block, is compatible with it.** The hypotheses of `finalized_compatible_of_viable`, with `W`
held by `w` before `t₀`.

Why: the root is the finalized block (`finalized_compatible_of_viable`) or the justified block
`J` at a height `j`, with `h_max = j + 1` and the state not contested, so `head_height_floor = j`,
at most `W`'s height (`floor_le_of_viable`), and `W`'s height is at most `j + 1`. At `j + 1`, `W`
is a descendant of the finalized block (Lemma 89a) at the height `h_max`, so of `J` (not
contested). At `j`, `J`'s witness reaches `u`, whose cache becomes `j` and justified block `J`
(Lemma 76); `u` is not contested (its `head_height_floor` would be `j + 1`), so its root is `J`, an ancestor of
the viable `W`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tEnd`, `t₀`: the times;
  `w`, `u`: the two validators; `W`: the block.

Roots name blocks until `tR`, at least `t₀ + Δ S`: every block the proof compares is held by `w`
before `t₀` or by `u` before `t₀ + Δ`.

Restated with the delivery premises up to `tR`: the bound of its roots, at least `t₀ + Δ S` (`htR`), read through `mem_T_of_delivery_high_upTo` at that bound; the implicit `tR` moved ahead of the premises. -/
theorem root_compatible_of_viable_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST : ℕ) (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) {tR : ℕ}
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject tR)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject tR)
    (hRoots : RootsNameBlocksUntil S Sched x tR)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (tEnd t₀ : ℕ) (w u : V) (W : Block V)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int)) (hEnd : t₀ + Δ S ≤ tEnd)
    (h1 : 1 ≤ t₀) (hGST : GST ≤ t₀) (hw : w ∉ Sched.adv (t₀ : Int))
    (hu : ∀ t' : ℕ, t₀ ≤ t' → t' ≤ t₀ + Δ S →
      u ∈ Sched.awake (t' : Int) ∧ u ∉ Sched.adv (t' : Int))
    (hW : W ∈ (fg_to_ac (stateBefore x (t₀ + Δ S) u).S).viable_heads)
    (hWw : W ∈ (stateBefore x t₀ w).S.T)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : t₀ + Δ S ≤ tR) :
    (get_fc_root (stateBefore x t₀ w).S).compatible W = true := by
  obtain ⟨-, -, hrW, hflW⟩ := viable_props S Sched x _ u W hW
  have huE : u ∉ Sched.adv ((t₀ + Δ S : ℕ) : Int) := (hu (t₀ + Δ S) (by omega) le_rfl).2
  have hflw := floor_le_of_viable_upTo S Sched x GST hDiv hMono hSync hCatch hRoots hParent hU
    tEnd t₀ w u W hThird hEnd hGST hw hu hW htR
  rcases root_cases (stateBefore x t₀ w).S with ⟨hrJ, hmJ, hcJ⟩ | ⟨hrF, -⟩
  · have hfl : head_height_floor (stateBefore x t₀ w).S = (stateBefore x t₀ w).S.h_j := by
      rcases floor_cases (stateBefore x t₀ w).S with ⟨hc, -, -⟩ | ⟨-, h⟩
      · rw [hcJ] at hc
        cases hc
      · rw [h, hmJ]
        rfl
    have hWh := height_le_h_max S Sched x t₀ w W hWw
    rw [hrJ, compatible_iff]
    by_cases hWj : (chainStateOf S.C W).h = (stateBefore x t₀ w).S.h_j + 1
    · -- `W` at the height `h_max`: a descendant of `J`
      left
      have hFW := F_ancestorEq_of_high S Sched x hMono hU hRoots tEnd t₀ t₀ w w W hThird
        (by omega) (by omega) hw hw hWw (by unfold Height at *; omega) (by omega)
      by_contra hJW
      have hc := fg_contest_true_of (stateBefore x t₀ w).S W hmJ hWw hFW
        (by rw [σ_eq_of_stateBefore S Sched x t₀ w W hWw, hWj, hmJ]) hJW
      rw [hcJ] at hc
      cases hc
    · -- `W` at the height `j`: `J`'s witness reaches `u`
      left
      have hWj' : (chainStateOf S.C W).h = (stateBefore x t₀ w).S.h_j := by
        rw [hfl] at hflw
        unfold Height at *
        omega
      obtain ⟨⟨Y, hY, hJY, hjY⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x t₀ w
      have hYh := (lem47_chain_state_heights S.C Y Y).1.2.1
      have hmu := h_max_le_floor_add_one (stateBefore x (t₀ + Δ S) u).S
      have hju := h_j_lt_h_max S Sched x (t₀ + Δ S) u
      have hYlt : (stateBefore x (t₀ + Δ S) u).S.h_j < (chainStateOf S.C Y).h := by
        unfold Height at *
        omega
      have hYu := mem_T_of_delivery_high_upTo S Sched x GST hDiv hMono hSync hCatch hRoots
        hParent hU tEnd t₀ w u Y hThird hEnd h1 hGST hw hY hu hYlt htR
      have hFuY := F_ancestorEq_of_high S Sched x hMono hU hRoots tEnd (t₀ + Δ S) (t₀ + Δ S) u u Y
        hThird hEnd hEnd huE huE hYu hYlt (by omega)
      have hjY' := h_j_of_mem_T_of_stateBefore S Sched x _ u Y hYu hFuY
      rw [σ_eq_of_stateBefore S Sched x _ u Y hYu] at hjY'
      have hjeq : (stateBefore x t₀ w).S.h_j = (stateBefore x (t₀ + Δ S) u).S.h_j := by
        unfold Height at *
        omega
      have hmeq : (stateBefore x (t₀ + Δ S) u).S.h_max =
          (stateBefore x (t₀ + Δ S) u).S.h_j + 1 := by
        unfold Height at *
        omega
      have hJJ := J_eq_of_h_j_eq S Sched x hMono hU hRoots tEnd t₀ (t₀ + Δ S) w u hThird (by omega)
        hEnd hw huE hjeq (by omega)
      have hroot : get_fc_root (stateBefore x (t₀ + Δ S) u).S =
          (stateBefore x (t₀ + Δ S) u).S.J := by
        rcases root_cases (stateBefore x (t₀ + Δ S) u).S with ⟨h, -⟩ | ⟨-, h⟩
        · exact h
        · exfalso
          rcases h with h | h
          · obtain ⟨-, -, hfl'⟩ :=
              GoldilocksCorrectness.Statements.Routines.frameShape_of_boxThree _ h
            rw [hfl'] at hflW
            unfold Height at *
            omega
          · exact h hmeq
      rw [hJJ, ← hroot]
      exact hrW
  · rw [hrF]
    exact finalized_compatible_of_viable_upTo S Sched x GST hDiv hMono hSync hCatch hRoots
      hParent hU tEnd t₀ w u W hThird hEnd h1 hGST hw hu hW htR

/-- **A confirmation saved by an update has an honest supporter.** In an execution where every
time is reached, corruption is permanent, blocks and votes are delivered within `Δ` after `GST`,
roots name blocks, and nobody votes in an honest validator's name:
when `GST` is at most the vote time of slot `σ`; every member of `Hs` is honest active at slot `σ`
and in its committee; the validators with a slot-`σ` vote in `v`'s pool before the support cutoff
of slot `σ + 1` are fewer than twice `Hs`; `v` is awake and honest from the vote time of slot `σ`
to that cutoff; and the confirmation update of slot `σ + 1` on `v`'s state before the cutoff
answers `A''`, which saves `X` as the confirmation of slot `σ` — then some member `u` of `Hs` put
on the wire at its tick at the vote time of slot `σ` its vote for a block `H_u` it held then, `X`
or a descendant of `X`.

Why: every member's vote reaches `v`'s pool, stamped before the support cutoff of slot `σ`, as its
only slot-`σ` vote there (`vote_in_pool_before_add_delay`, `unique_vote_of_owner`); the update saved
`X`, so `update_confirmation_supporter` gives a member whose vote's head is the root of a block of
`v`'s frame tree that is `X` or a descendant of `X`, and that block is the member's voted block
(roots name blocks).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `σ`: the slot of the votes; `v`: the updater; `Hs`: the honest voters;
  `X`: the confirmation.

Roots name blocks until `supportCutoff S (σ + 1)`: the proof compares a block `v` holds before
the support cutoff of slot `σ + 1` with the voted block `u` holds before the vote time of slot
`σ`.

Restated with the delivery premises up to `supportCutoff S σ`: the deadline of the slot-`σ` votes its proof reads (`vote_in_pool_before_add_delay_upTo` at the vote time of slot `σ`). -/
theorem honest_supporter_of_update_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST σ : ℕ) (v : V) (Hs : Finset V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S σ))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S σ))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (σ + 1)))
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S σ)
    (hHs : ∀ u ∈ Hs, u ∈ honestActiveAt S Sched σ ∧ u ∈ S.P.committee σ)
    (hVoters : voters_count ((stateBefore x (supportCutoff S (σ + 1)) v).A.pool σ) <
      2 * Hs.card)
    (hv : ∀ t : ℕ, voteTime S σ ≤ t → t ≤ supportCutoff S (σ + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (A'' : ACState V)
    (hUpdate : update_confirmation S.C S.P
      (expireLocks (stateBefore x (supportCutoff S (σ + 1)) v).A
        ((supportCutoff S (σ + 1) : ℕ) : Int))
      (fg_to_ac (stateBefore x (supportCutoff S (σ + 1)) v).S)
      ((supportCutoff S (σ + 1) : ℕ) : Int) (σ + 1) = .ok A'')
    (X : Block V) (hX : A''.saved_confirmation σ = some X) :
    ∃ u ∈ Hs, ∃ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) ∧
      ∃ H_u ∈ (stateBefore x (voteTime S σ) u).S.T, vote = GoldfishVote.mk u σ H_u.root ∧
        X.AncestorEq H_u := by
  have hΔ := one_le_Δ S
  have hss : slotStart S (σ + 1) = slotStart S σ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (σ + 1) = slotStart S (σ + 1) + Δ S := voteTime_eq S (σ + 1)
  have hv₂ : supportCutoff S (σ + 1) = voteTime S (σ + 1) + Δ S := supportCutoff_eq S (σ + 1)
  have hc₁ : supportCutoff S σ = voteTime S σ + Δ S := supportCutoff_eq S σ
  have hv₁ : voteTime S σ = slotStart S σ + Δ S := voteTime_eq S σ
  have hslot : S.C.slot ((voteTime S σ : ℕ) : Int) = σ := slot_eq_of_mem S (by omega) (by omega)
  -- the members' votes
  have hvotes : ∀ u ∈ Hs, ∃ (i : ℕ) (vote : GoldfishVote V),
      x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧ vote.val_index = u ∧ vote.slot = σ ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent :=
    fun u hu => honest_active_votes S Sched x σ u hDiv hMono (hHs u hu).1 (hHs u hu).2
  choose iv₀ vf₀ hvf₀ using hvotes
  let iv : V → ℕ := fun u => if h : u ∈ Hs then iv₀ u h else 0
  let vf : V → GoldfishVote V := fun u => if h : u ∈ Hs then vf₀ u h else GoldfishVote.mk u σ
    (Block.genesis : Block V).root
  have hvf : ∀ u ∈ Hs, x.lbl (iv u) = AtomicAction.tickAllAwake (voteTime S σ) ∧
      (vf u).val_index = u ∧ (vf u).slot = σ ∧
      (⟨u, NamedObject.gfVote (vf u)⟩ : SignedMsg V (NamedObject V)) ∈
        x[iv u + 1].sent - x[iv u].sent := by
    intro u hu
    simp only [iv, vf, dif_pos hu]
    exact hvf₀ u hu
  have hcut : ((((supportCutoff S σ : ℕ) : Int)) : Stamp) =
      ((S.C.t_ σ + 2 * S.C.Δ : Time) : Stamp) := by
    rw [supportCutoff_cast]
  have hpool : ∀ u ∈ Hs, vf u ∈ (stateBefore x (supportCutoff S (σ + 1)) v).A.pool σ ∧
      (vf u).val_index = u ∧
      (∃ τ : Stamp, (stateBefore x (supportCutoff S (σ + 1)) v).A.timestamp_vote (vf u) =
        some τ ∧ τ < ((S.C.t_ σ + 6 * S.C.Δ : Time) : Stamp)) ∧
      ∀ vote' ∈ (stateBefore x (supportCutoff S (σ + 1)) v).A.pool σ,
        vote'.val_index = u → vote' = vf u := by
    intro u hu
    obtain ⟨hl, hval, hsl, hsent⟩ := hvf u hu
    have huh : u ∉ Sched.adv ((supportCutoff S (σ + 1) : ℕ) : Int) :=
      (Finset.mem_sdiff.1 (hHs u hu).1).2
    have hut : ∀ t : ℕ, t ≤ supportCutoff S (σ + 1) → u ∉ Sched.adv (t : Int) :=
      fun t ht h => huh (hMono _ _ (by exact_mod_cast ht) h)
    have hsent' : (⟨(vf u).val_index, NamedObject.gfVote (vf u)⟩ : SignedMsg V (NamedObject V)) ∈
        x[iv u + 1].sent - x[iv u].sent := by rw [hval]; exact hsent
    have hcomm : (vf u).val_index ∈ S.P.committee (vf u).slot := by
      rw [hval, hsl]; exact (hHs u hu).2
    have hpool₁ : vf u ∈ (stateBefore x (voteTime S σ + Δ S) v).A.pool σ := by
      rcases vote_in_pool_before_add_delay_upTo hDiv hMono (hSync.mono (supportCutoff_eq S σ).ge)
          (hCatch.mono (supportCutoff_eq S σ).ge) hl hsent' hGST
          (by rw [hsl, hslot]) hcomm (by rw [hval]; exact hut _ (by omega))
          (fun t' h1 h2 => hv t' (by omega) (by omega)) with
        ⟨h, -⟩ | ⟨v₁, h₁, v₂, h₂, hne, hi₁, hi₂⟩
      · rw [hsl] at h
        exact h
      · rw [hsl] at h₁ h₂
        rw [hval] at hi₁ hi₂
        exact absurd (unique_vote_of_owner hDiv hMono hOwner (hut _ (by omega)) h₁ h₂ hi₁ hi₂)
          hne
    have hstep := stepBefore_mono x hDiv (show voteTime S σ + Δ S ≤ supportCutoff S (σ + 1) by
      omega)
    have hpool₂ : vf u ∈ (stateBefore x (supportCutoff S (σ + 1)) v).A.pool σ :=
      pool_mono x v hstep σ hpool₁
    refine ⟨hpool₂, hval, ?_, fun vote' hv' hi' =>
      unique_vote_of_owner hDiv hMono hOwner huh hv' hpool₂ hi' hval⟩
    obtain ⟨st, hst, hstlt⟩ := (voteStamp_lt_iff hDiv hpool₂).2 hpool₁
    refine ⟨st, hst, ?_⟩
    rw [← hc₁, hcut] at hstlt
    have hlt : S.C.t_ σ + 2 * S.C.Δ < S.C.t_ σ + 6 * S.C.Δ :=
      Int.add_lt_add_left (Int.mul_lt_mul_of_pos_right (by decide) S.C.Δ_pos) _
    exact lt_trans hstlt (WithBot.coe_lt_coe.2 hlt)
  -- the update
  have hvc := hv (supportCutoff S (σ + 1)) (by omega) le_rfl
  obtain ⟨u, hu, H, hH, hr, hXH⟩ := update_confirmation_supporter S.C S.P
    (expireLocks (stateBefore x (supportCutoff S (σ + 1)) v).A
      ((supportCutoff S (σ + 1) : ℕ) : Int)) A''
    (fg_to_ac (stateBefore x (supportCutoff S (σ + 1)) v).S)
    ((supportCutoff S (σ + 1) : ℕ) : Int) σ Hs vf
    (rootsNameBlocksIn_frame_of_exec_node S Sched x _ v)
    (by rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)]; exact hpool)
    (by rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)]; exact hVoters) hUpdate X hX
  obtain ⟨hl, hval, hsl, hsent⟩ := hvf u hu
  obtain ⟨H_u, hHT, hvote, -⟩ := honest_vote_spec S Sched x hDiv σ u (vf u) ⟨iv u, hl, hsent⟩
  refine ⟨u, hu, vf u, ⟨iv u, hl, hsent⟩, H_u, hHT, hvote, ?_⟩
  -- the block of `v`'s tree with the vote's head root is `H_u`
  have hHv : H ∈ (stateBefore x (supportCutoff S (σ + 1)) v).S.T :=
    ((mem_fg_to_ac_tree _ _).1 hH).1
  have huh : u ∉ Sched.adv ((supportCutoff S (σ + 1) : ℕ) : Int) :=
    (Finset.mem_sdiff.1 (hHs u hu).1).2
  have ht1 := time_stepBefore_le x (voteTime S σ)
  have ht2 := time_stepBefore_le x (supportCutoff S (σ + 1))
  have ht1' : x[stepBefore x (voteTime S σ)].time ≤ supportCutoff S (σ + 1) := by omega
  have hu' : u ∉ Sched.adv (x[stepBefore x (voteTime S σ)].time : Int) := fun h =>
    huh (hMono _ _ (by exact_mod_cast ht1') h)
  have hv' : v ∉ Sched.adv (x[stepBefore x (supportCutoff S (σ + 1))].time : Int) := fun h =>
    hvc.2 (hMono _ _ (by exact_mod_cast ht2) h)
  have hroot : H.root = H_u.root := by rw [hr, hvote]
  have hHH : H = H_u :=
    hRoots H H_u ⟨stepBefore x (supportCutoff S (σ + 1)), v, hv', ht2, hHv⟩
      ⟨stepBefore x (voteTime S σ), u, hu', ht1', hHT⟩ hroot
  rw [← hHH]
  exact hXH

/-- **A saved confirmation has an honest supporter.** `honest_supporter_of_update` with the
confirmation read on `v`'s node state right after the support cutoff of slot `σ + 1`, `v` awake and
honest from the duty window's start of slot `σ + 1` to that cutoff (`update_state_of_duty`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `σ`: the slot of the votes; `v`: the updater; `Hs`: the honest voters;
  `X`: the confirmation.

Roots name blocks until `supportCutoff S (σ + 1)`: the bound of `honest_supporter_of_update`.

Restated with the delivery premises up to `supportCutoff S σ`: the bound of `honest_supporter_of_update_upTo`. -/
theorem honest_supporter_of_saved_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST σ : ℕ) (v : V) (Hs : Finset V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S σ))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S σ))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (σ + 1)))
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S σ)
    (hHs : ∀ u ∈ Hs, u ∈ honestActiveAt S Sched σ ∧ u ∈ S.P.committee σ)
    (hVoters : voters_count ((stateBefore x (supportCutoff S (σ + 1)) v).A.pool σ) <
      2 * Hs.card)
    (hv : ∀ t : ℕ, dutyWindowStart S (σ + 1) ≤ t → t ≤ supportCutoff S (σ + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (X : Block V)
    (hX : (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some X) :
    ∃ u ∈ Hs, ∃ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) ∧
      ∃ H_u ∈ (stateBefore x (voteTime S σ) u).S.T, vote = GoldfishVote.mk u σ H_u.root ∧
        X.AncestorEq H_u := by
  have hΔ := one_le_Δ S
  have hdw : dutyWindowStart S (σ + 1) ≤ slotStart S σ := dutyWindowStart_succ_le_slotStart S σ
  have hv₁ : voteTime S σ = slotStart S σ + Δ S := voteTime_eq S σ
  have hss : slotStart S (σ + 1) = slotStart S σ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hc := supportCutoff_eq S (σ + 1)
  have hv₃ := voteTime_eq S (σ + 1)
  have hdwc : dutyWindowStart S (σ + 1) < supportCutoff S (σ + 1) := by omega
  have hvc := hv (supportCutoff S (σ + 1)) hdwc.le le_rfl
  have hAw := awakeSince_le_dutyWindowStart_b S Sched x (σ + 1) (supportCutoff S (σ + 1)) v hDiv
    hMono hdwc (fun t h1 h2 => (hv t h1 h2).1) hvc.2
  obtain ⟨A'', hUpdate, hsave, -, -, -⟩ := update_state_of_duty S Sched x σ v hDiv hvc hAw
  rw [hsave] at hX
  exact honest_supporter_of_update_upTo S Sched x GST σ v Hs hDiv hMono hSync hCatch hRoots hOwner
    hGST hHs hVoters (fun t h1 h2 => hv t (by omega) h2) A'' hUpdate X hX

end GoldilocksCorrectness.Proofs.Executions

