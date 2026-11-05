module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Climb
public import GoldilocksCorrectness.Proofs.Executions.Lemma78
public import GoldilocksCorrectness.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Proofs.Routines.Lemma77
public import GoldilocksCorrectness.Proofs.Routines.Frame
public import GoldilocksCorrectness.Proofs.Routines.WalkEnd
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts

@[expose] public section

/-!
# Lemma 89, part B: the kit of the stability fact

The kit of B5 and B6 of Lemma 89's skeleton on the fast-confirmation route
 that does not read the fork-choice change: the caches
of a node state, the finalized block below every honest-held block higher than the cache `h_j`, a
block delivered within one delay, the end of an honest Goldfish vote, and a confirmation saved when
a voter majority votes on the chain of the updater's finalized block. B5, B6 and the kit that reads
the fork-choice change are in `Proofs/Executions/Lemma89StabilityJ.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq
  slot_eq_of_mem supportCutoff_eq viewFreeze_cast voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes
  fc_root_eq fg_to_ac_F pool_of_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

open GoldilocksCorrectness.Proofs.Routines (mem_viable_tree_iff)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines
open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

end GoldilocksCorrectness.Proofs.Routines

namespace GoldilocksCorrectness.Proofs.Executions

open GoldilocksCorrectness.Proofs.Routines (get_anchor_cases get_anchor_mem_T walk_end_extends)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree mem_viable_heads_iff)

open GoldilocksCorrectness.Proofs.Routines (lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf chainStateOf)

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; this rule, local to the file, proves it at once
--. No statement and no proof term
-- changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## The caches of a node state -/

/-- A held block's chain state in a node state is the block's own (Lemma 11).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
  `B`: the block. -/
theorem σ_eq_of_stateBefore (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) (B : Block V)
    (hB : B ∈ (stateBefore x t v).S.T) :
    (stateBefore x t v).S.σ B = chainStateOf S.C B :=
  (lem11_node_invariant S Sched x (stepBefore x t) v).1.2.2.2.2.2.1 B hB

/-- A held block's chain-state height is at most the cache `h_max` (Lemma 46).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
  `B`: the block. -/
theorem height_le_h_max (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) (B : Block V)
    (hB : B ∈ (stateBefore x t v).S.T) :
    (chainStateOf S.C B).h ≤ (stateBefore x t v).S.h_max := by
  have h := (lem46_finality_caches S Sched x (stepBefore x t) v).2 B hB
  rw [← σ_eq_of_stateBefore S Sched x t v B hB]
  exact h

/-- The cache `h_j` is less than the cache `h_max`: the justified block's witness has a chain-state
height greater than its justification height (Lemma 47) and at most `h_max` (Lemma 46).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator. -/
theorem h_j_lt_h_max (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) :
    (stateBefore x t v).S.h_j < (stateBefore x t v).S.h_max := by
  obtain ⟨⟨D, hD, -, hj⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x t v
  have h1 := (lem47_chain_state_heights S.C D D).1.2.1
  have h2 := height_le_h_max S Sched x t v D hD
  rw [hj]
  exact lt_of_lt_of_le h1 h2

/-- The cache `h_max` does not decrease: the block witnessing it stays in the tree.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `v`: the validator; `t ≤ t'`: the
  two times. -/
theorem h_max_mono (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hDiv : TimeDiverges x.toTrace) (v : V) {t t' : ℕ}
    (htt : t ≤ t') :
    (stateBefore x t v).S.h_max ≤ (stateBefore x t' v).S.h_max := by
  obtain ⟨-, ⟨X, hX, hXh⟩, -⟩ := cachesWitnessed_of_stateBefore S Sched x t v
  rw [← hXh]
  exact height_le_h_max S Sched x t' v X ((stateBefore_grows x hDiv v htt).1 hX)

/-- **The finalized block is an ancestor of every honest-held block higher than the cache `h_j`.**
Under unforgeability, roots naming blocks, permanent corruption and fewer than a third of the
validators in the adversary set up to `tEnd`: when `w` is honest at `t ≤ tEnd`, `p` is honest at
`t' ≤ tEnd` and holds `B` before `t'`, and `B`'s chain-state height is greater than `w`'s cache
`h_j` before `t`, then `w`'s finalized block before `t` is `B` or an ancestor of `B`.

Why: `w`'s finalized block is the finalized block of the chain state of a block `D` it holds
(`finalizedFromChain_of_exec`), at a finalization height at most `D`'s justification height
(Lemma 47), at most `w`'s `h_j` (Lemma 57, `D` being on the finalized block's chain); Lemma 89a.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`: the time up to which the
  adversary bound holds; `t`, `t'`: the two times; `w`, `p`: the two validators; `B`: the block.

Roots name blocks until `tR`, at least `max t t'`: the proof compares (Lemma 89a) a block `w`
holds before `t` with `B`, which `p` holds before `t'`. -/
theorem F_ancestorEq_of_high (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) {tR : ℕ} (hRoots : RootsNameBlocksUntil S Sched x tR)
    (tEnd t t' : ℕ) (w p : V) (B : Block V)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int)) (ht : t ≤ tEnd) (ht' : t' ≤ tEnd)
    (hw : w ∉ Sched.adv (t : Int)) (hp : p ∉ Sched.adv (t' : Int))
    (hB : B ∈ (stateBefore x t' p).S.T)
    (hlt : (stateBefore x t w).S.h_j < (chainStateOf S.C B).h)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max t t' ≤ tR) :
    (stateBefore x t w).S.F.AncestorEq B := by
  obtain ⟨D, hD, hF⟩ := finalizedFromChain_of_exec S Sched x (stepBefore x t) w
  have hSt : stateBefore x t w = x[stepBefore x t][w].st := rfl
  rw [← hSt] at hD hF
  by_cases h0 : (chainStateOf S.C D).h_F = 0
  · rw [hF, GoldilocksCorrectness.Proofs.Routines.chainStateOf_F_genesis S.C D h0]
    exact genesis_ancestorEq B
  have hFD : (chainStateOf S.C D).F.AncestorEq D :=
    ((GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified S.C D).2.2
      (Nat.one_le_iff_ne_zero.mpr h0)).2.2.1
  have hjD : ((stateBefore x t w).S.σ D).h_j ≤ (stateBefore x t w).S.h_j :=
    h_j_of_mem_T_of_stateBefore S Sched x t w D hD (by rw [hF]; exact hFD)
  rw [σ_eq_of_stateBefore S Sched x t w D hD] at hjD
  have hFj := (lem47_chain_state_heights S.C D D).1.2.2
  have hlt' : (chainStateOf S.C D).h_F < (chainStateOf S.C B).h :=
    lt_of_le_of_lt hFj (lt_of_le_of_lt hjD hlt)
  have hti := time_stepBefore_le x t
  have htj := time_stepBefore_le x t'
  have hT : AdversaryFewerThanThirdUntil Sched (validator_count V)
      (max (x[stepBefore x t].time : Int) (x[stepBefore x t'].time : Int)) :=
    adversaryFewerThanThirdUntil_of_le (max_le (by exact_mod_cast (show x[stepBefore x t].time ≤
      tEnd by omega)) (by exact_mod_cast (show x[stepBefore x t'].time ≤ tEnd by omega))) hThird
  have hw' : w ∉ Sched.adv (x[stepBefore x t].time : Int) :=
    fun h => hw (hMono _ _ (by exact_mod_cast hti) h)
  have hp' : p ∉ Sched.adv (x[stepBefore x t'].time : Int) :=
    fun h => hp (hMono _ _ (by exact_mod_cast htj) h)
  have h68 := lem68_honest_past_finalized S Sched x hU hRoots (stepBefore x t)
    (stepBefore x t') w p D B hT hw' hp' hD hB hlt' (le_trans (max_le_max hti htj) htR)
  rw [hF]
  exact h68

/-- **The cache `h_j` of an honest validator does not decrease.** Under the assumptions of
`F_ancestorEq_of_high`: when `w` is honest at `t'` and `t ≤ t' ≤ tEnd`, `w`'s cache `h_j` before
`t` is at most its cache `h_j` before `t'`.

Why: the block `D` witnessing the cache before `t` stays in the tree and has a chain-state height
greater than its justification height (Lemma 47); were the later cache smaller, `w`'s later
finalized block would be an ancestor of `D` (`F_ancestorEq_of_high`), and then `D`'s justification
height is at most the later cache (Lemma 57).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`: the time up to which the
  adversary bound holds; `t ≤ t'`: the two times; `w`: the validator.

Roots name blocks until `tR`, at least `t'`: `F_ancestorEq_of_high` at the times `t'` and
`t ≤ t'`. -/
theorem h_j_mono (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    {tR : ℕ} (hRoots : RootsNameBlocksUntil S Sched x tR) (tEnd t t' : ℕ) (w : V)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int)) (htt : t ≤ t') (ht' : t' ≤ tEnd)
    (hw : w ∉ Sched.adv (t' : Int))
    -- the latest time the proof takes a block as held is at most the bound
    (htR : t' ≤ tR) :
    (stateBefore x t w).S.h_j ≤ (stateBefore x t' w).S.h_j := by
  by_contra hlt
  push Not at hlt
  obtain ⟨⟨D, hD, -, hj⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x t w
  have hD' : D ∈ (stateBefore x t' w).S.T := (stateBefore_grows x hDiv w htt).1 hD
  have hDh := (lem47_chain_state_heights S.C D D).1.2.1
  have hwt : w ∉ Sched.adv (t : Int) := fun h => hw (hMono _ _ (by exact_mod_cast htt) h)
  have hFD := F_ancestorEq_of_high S Sched x hMono hU hRoots tEnd t' t w w D hThird ht'
    (le_trans htt ht') hw hwt hD (by rw [hj] at hlt; exact lt_trans hlt hDh)
    (max_le htR (le_trans htt htR))
  have hjD := h_j_of_mem_T_of_stateBefore S Sched x t' w D hD' hFD
  rw [σ_eq_of_stateBefore S Sched x t' w D hD'] at hjD
  rw [hj] at hlt
  exact absurd hjD (not_le.mpr hlt)

/-! ## The root and `head_height_floor` (the least chain-state height a viable block may have) of an FG state -/

/-! ## A block delivered within one delay -/

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
`t₀ + Δ S`, and `F_ancestorEq_of_high` at those two times. -/
theorem mem_T_of_delivery_high (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST : ℕ) (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    {tR : ℕ} (hRoots : RootsNameBlocksUntil S Sched x tR)
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
  exact mem_T_before_add_delay_of_held hDiv hMono hSync hCatch (hRoots.mono htR) hParent
    (t₁ := t₀) (t := t₀) h1 le_rfl hGST hv hY hu ((compatible_iff _ _).2 (Or.inl hFY))

/-! ## The voter's tree -/

/-- A block `w` held before `t₀`, with `t₀` at most the view freeze of slot `s' − 1` and at most the
vote time of slot `s'`, and with `w`'s finalized block before that vote time an ancestor of it, is
in `w`'s voter tree of slot `s'`.

Why: as `proposal_viable_head_at`: the block keeps its stamp, which is before `t₀`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`, `s'`: the time and the slot;
  `w`: the voter; `B`: the block; `tree`: the voter's tree. -/
theorem mem_voter_tree_of_held (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hDiv : TimeDiverges x.toTrace)
    (t₀ s' : ℕ) (w : V) (B : Block V)
    (tree : Finset (Block V))
    (hBin : B ∈ (stateBefore x t₀ w).S.T)
    (ht₀ : t₀ ≤ viewFreeze S (s' - 1)) (ht₀' : t₀ ≤ voteTime S s')
    (hFB : (stateBefore x (voteTime S s') w).S.F.AncestorEq B)
    (htree : voter_block_tree S.C (stateBefore x (voteTime S s') w).A
      (fg_to_ac (stateBefore x (voteTime S s') w).S) s' = .ok tree) :
    B ∈ tree := by
  have hG := stateBefore_grows x hDiv w ht₀'
  have hT : B ∈ (stateBefore x (voteTime S s') w).S.T := hG.1 hBin
  have hΦ : B ∈ (fg_to_ac (stateBefore x (voteTime S s') w).S).tree :=
    (mem_fg_to_ac_tree _ _).2 ⟨hT, hFB⟩
  obtain ⟨st, hst, hlt⟩ := blockStamp_before hDiv hBin
  have hkept : (stateBefore x (voteTime S s') w).A.timestamp_block B =
      (stateBefore x t₀ w).A.timestamp_block B := hG.2.2.2.1 B hBin
  have hle : ((((t₀ : ℕ) : Int)) : Stamp) ≤ ((S.C.t_ (s' - 1) + 3 * S.C.Δ : Time) : Stamp) := by
    rw [← viewFreeze_cast]
    exact WithBot.coe_le_coe.2 (by exact_mod_cast ht₀)
  exact (GoldilocksCorrectness.Statements.Routines.mem_voter_block_tree_iff_at S.C _ _ s' tree
    htree B).2 ⟨hΦ, st, by rw [hkept]; exact hst, Or.inl (lt_of_lt_of_le hlt hle)⟩

/-! ## The end of the Goldfish fork choice -/

/-- The voter's tree of slot `s'` holds every block from the fork-choice root to one of its
blocks: such a block is held (it is an ancestor of a held block), the finalized block is an
ancestor of it, and it was held before the view freeze, or leads to a slot-`s'` block, whenever the
block of the tree it is an ancestor of was or does.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot of the vote; `w`: the
  voter; `tree`: the voter's tree. -/
theorem voter_tree_closed (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hDiv : TimeDiverges x.toTrace)
    (s' : ℕ) (w : V) (tree : Finset (Block V))
    (htree : voter_block_tree S.C (stateBefore x (voteTime S s') w).A
      (fg_to_ac (stateBefore x (voteTime S s') w).S) s' = .ok tree) :
    ∀ Z ∈ tree, ∀ c : Block V,
      (fg_to_ac (stateBefore x (voteTime S s') w).S).fc_root.AncestorEq c → c.AncestorEq Z →
      c ∈ tree := by
  intro Z hZ c hρc hcZ
  have hiff := GoldilocksCorrectness.Statements.Routines.mem_voter_block_tree_iff_at S.C _ _ s'
    tree htree
  obtain ⟨hZΦ, τ, hτ, hor⟩ := (hiff Z).1 hZ
  have hZT : Z ∈ (stateBefore x (voteTime S s') w).S.T := ((mem_fg_to_ac_tree _ _).1 hZΦ).1
  have hcT : c ∈ (stateBefore x (voteTime S s') w).S.T :=
    ancestors_mem_T_of_exec S Sched x _ w Z c hZT hcZ
  have hFc : (stateBefore x (voteTime S s') w).S.F.AncestorEq c :=
    ancestorEq_trans (F_ancestorEq_fc_root_of_stateBefore S Sched x _ w)
      (by rw [← fc_root_eq]; exact hρc)
  have hcΦ : c ∈ (fg_to_ac (stateBefore x (voteTime S s') w).S).tree :=
    (mem_fg_to_ac_tree _ _).2 ⟨hcT, hFc⟩
  obtain ⟨τc, hτc, -⟩ := blockStamp_before hDiv hcT
  rcases hor with hlt | ⟨B', hB', hslot, hZB'⟩
  · -- `Z` was held before the view freeze, and so was `c`
    have hfz : ((S.C.t_ (s' - 1) + 3 * S.C.Δ : Time) : Stamp) =
        ((((viewFreeze S (s' - 1) : ℕ) : Int)) : Stamp) := by
      rw [viewFreeze_cast]
    rw [hfz] at hlt
    have hZf : Z ∈ (stateBefore x (viewFreeze S (s' - 1)) w).S.T :=
      (blockStamp_lt_iff hDiv hZT).1 ⟨τ, hτ, hlt⟩
    have hcf : c ∈ (stateBefore x (viewFreeze S (s' - 1)) w).S.T :=
      ancestors_mem_T_of_exec S Sched x _ w Z c hZf hcZ
    obtain ⟨st, hst, hstlt⟩ := (blockStamp_lt_iff hDiv hcT).2 hcf
    refine (hiff c).2 ⟨hcΦ, st, hst, Or.inl ?_⟩
    rw [hfz]
    exact hstlt
  · exact (hiff c).2 ⟨hcΦ, τc, hτc, Or.inr ⟨B', hB', hslot, ancestorEq_trans hcZ hZB'⟩⟩

/-- **An honest vote, its block, and the blocks it extends.** When `u`'s tick at the vote time of
slot `s'` put `vote` on the wire, `vote` is `u`'s slot-`s'` vote for a block `H_u` that `u` holds
before the vote time, `u`'s fork-choice root then is `H_u` or an ancestor of it, and `H_u` is `F'`
or a descendant of `F'` for every block `F'` such that: `u` held, before a time `t₀` at most the
view freeze of slot `s' − 1` and at most that vote time, a block `Y` that is a viable head of its
frame before the vote time; every viable head of that frame is `F'` or a descendant of `F'`; and no
strict ancestor of `F'` is a viable head of it.

Why: the vote names the end of the Goldfish fork choice from the anchor through the viable tree of
the voter's tree (Lemma 14), and the anchor is the root or a descendant of it; `Y` is in the
voter's tree (`mem_voter_tree_of_held`), which holds every block from the root to one of its
blocks (`voter_tree_closed`); and `walk_end_extends`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `u`: the voter;
  `vote`: the vote. -/
theorem honest_vote_spec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hDiv : TimeDiverges x.toTrace)
    (s' : ℕ) (u : V) (vote : GoldfishVote V)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    ∃ H_u ∈ (stateBefore x (voteTime S s') u).S.T,
      vote = GoldfishVote.mk u s' H_u.root ∧
      (get_fc_root (stateBefore x (voteTime S s') u).S).AncestorEq H_u ∧
      ∀ (t₀ : ℕ) (Y F' : Block V), Y ∈ (stateBefore x t₀ u).S.T →
        t₀ ≤ viewFreeze S (s' - 1) → t₀ ≤ voteTime S s' →
        Y ∈ (fg_to_ac (stateBefore x (voteTime S s') u).S).viable_heads →
        (∀ W ∈ (fg_to_ac (stateBefore x (voteTime S s') u).S).viable_heads, F'.AncestorEq W) →
        (∀ B : Block V, B.AncestorEq F' → B ≠ F' →
          B ∉ (fg_to_ac (stateBefore x (voteTime S s') u).S).viable_heads) →
        F'.AncestorEq H_u := by
  have hΔ := one_le_Δ S
  have hv₃ : voteTime S s' = slotStart S s' + Δ S := voteTime_eq S s'
  have hss : slotStart S (s' + 1) = slotStart S s' + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hslot₃ : S.C.slot ((voteTime S s' : ℕ) : Int) = s' :=
    slot_eq_of_mem S (by omega) (by omega)
  obtain ⟨i, hl, hm⟩ := hSend
  have hi : stepBefore x (voteTime S s') = i := stepBefore_eq_of_lbl x hl
  obtain ⟨-, n', sent, hrun, hvote⟩ := tick_send_of_honestSendAt hl hm
  have hRootsΦ : RootsNameBlocksIn (fg_to_ac (stateBefore x (voteTime S s') u).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ u
  have hA : (tickInputState x i (voteTime S s') u).A = (stateBefore x (voteTime S s') u).A := by
    rw [(tickInputState_frame x i _ u).2.1]
    unfold stateBefore
    rw [hi]
  have hS : (tickInputState x i (voteTime S s') u).S = (stateBefore x (voteTime S s') u).S := by
    rw [(tickInputState_frame x i _ u).1]
    unfold stateBefore
    rw [hi]
  obtain ⟨-, hvi, hvs, -, A', votes, support_votes, vbt, H_u, -, -, hvbt, hWalk, hhead, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem14_tick_vote_walk S.C S.P S.X _ n' _ sent vote
      hrun hvote
  rw [hslot₃, hA, hS] at hvbt
  rw [hslot₃, hS] at hWalk
  have hv : (tickInputState x i (voteTime S s') u).v = u := by
    have h := (lem11_node_invariant S Sched x i u).2.1
    unfold tickInputState
    split <;> (try rw [wake_eq]) <;> exact h
  rw [hv] at hvi
  rw [hslot₃] at hvs
  have hvote' : vote = GoldfishVote.mk u s' H_u.root := by
    rw [← hvi, ← hvs, ← hhead]
  have hHT : H_u ∈ (stateBefore x (voteTime S s') u).S.T := by
    rcases GoldilocksCorrectness.Proofs.Routines.ghost_mem_tree_or_eq ((goldfish_fork_choice_eq ..).symm.trans hWalk) with h | h
    · rw [h]
      exact get_anchor_mem_T _ _ _
        (lem11_node_invariant S Sched x (stepBefore x (voteTime S s')) u).1.2.2.2.1
        (lem57_justification_cache_and_record S Sched x (stepBefore x (voteTime S s')) u).2.2.1
    · have h1 := ((mem_viable_tree_iff _ _ _).1 h).1
      have h2 := ((GoldilocksCorrectness.Proofs.Routines.mem_voter_block_tree_iff S.C _ _ s' vbt
        hvbt H_u).1 h1).1
      exact ((mem_fg_to_ac_tree _ _).1 h2).1
  have hAH : (get_anchor A' (fg_to_ac (stateBefore x (voteTime S s') u).S)
      ((voteTime S s' : ℕ) : Int)).AncestorEq H_u := by
    rcases GoldilocksCorrectness.Proofs.Routines.ghost_spec ((goldfish_fork_choice_eq ..).symm.trans hWalk) with hH | ⟨hAH, -⟩
    · rw [hH]
      exact ancestorEq_refl _
    · exact hAH
  have hVT : vbt ⊆ (fg_to_ac (stateBefore x (voteTime S s') u).S).tree := fun B hB =>
    ((GoldilocksCorrectness.Statements.Routines.mem_voter_block_tree_iff_at S.C _ _ s' vbt hvbt
      B).1 hB).1
  have hRA := GoldilocksCorrectness.Proofs.Routines.fc_root_ancestorEq_get_anchor A'
    (fg_to_ac (stateBefore x (voteTime S s') u).S) ((voteTime S s' : ℕ) : Int)
  rw [fc_root_eq] at hRA
  refine ⟨H_u, hHT, hvote', ancestorEq_trans hRA hAH, ?_⟩
  intro t₀ Y F' hYT ht₀ ht₀' hYv hP hQ
  have hYvbt : Y ∈ vbt := mem_voter_tree_of_held S Sched x hDiv t₀ s' u Y vbt hYT ht₀ ht₀'
    ((mem_viable_heads_iff _ _).1 hYv).2.1 hvbt
  exact walk_end_extends S.C _ _ _ vbt votes support_votes (s' - 1) H_u F' Y hRootsΦ hVT
    (voter_tree_closed S Sched x hDiv s' u vbt hvbt) (get_anchor_cases _ _ _) hWalk
    (fun W hW => ((mem_viable_heads_iff _ _).1 hW).2.2.1) hYvbt hYv hP hQ

/-! ## A confirmation saved -/

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

Roots name blocks until `supportCutoff S s`: Lemma 12 at slot `s`. -/
theorem confirmation_saved_of_votes (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (v : V)
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
    GoldilocksCorrectness.Statements.Executions.lem12_honest_vote_delivered_until S Sched x GST s
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

/-! ## Two honest-held blocks -/

/-- **Lemma 89a in the time form.** Under unforgeability, roots naming blocks, permanent
corruption and fewer than a third of the validators in the adversary set up to `tEnd`: when `v` is
honest at `t ≤ tEnd` and holds `D` before `t`, `p` is honest at `t' ≤ tEnd` and holds `B` before
`t'`, and `B`'s chain-state height is greater than the finalization height of `D`'s chain state,
then the finalized block of `D`'s chain state is `B` or an ancestor of `B`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`, `t`, `t'`: the times;
  `v`, `p`: the two holders; `D`, `B`: the two blocks.

Roots name blocks until `tR`, at least `max t t'`: Lemma 89a at the steps before `t` and before
`t'`. -/
theorem finalized_ancestorEq_of_held (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) {tR : ℕ} (hRoots : RootsNameBlocksUntil S Sched x tR)
    (tEnd t t' : ℕ) (v p : V) (D B : Block V)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int)) (ht : t ≤ tEnd) (ht' : t' ≤ tEnd)
    (hv : v ∉ Sched.adv (t : Int)) (hp : p ∉ Sched.adv (t' : Int))
    (hD : D ∈ (stateBefore x t v).S.T) (hB : B ∈ (stateBefore x t' p).S.T)
    (hlt : (chainStateOf S.C D).h_F < (chainStateOf S.C B).h)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max t t' ≤ tR) :
    (chainStateOf S.C D).F.AncestorEq B := by
  have hti := time_stepBefore_le x t
  have htj := time_stepBefore_le x t'
  have hT : AdversaryFewerThanThirdUntil Sched (validator_count V)
      (max (x[stepBefore x t].time : Int) (x[stepBefore x t'].time : Int)) :=
    adversaryFewerThanThirdUntil_of_le (max_le (by exact_mod_cast (show x[stepBefore x t].time ≤
      tEnd by omega)) (by exact_mod_cast (show x[stepBefore x t'].time ≤ tEnd by omega))) hThird
  have hv' : v ∉ Sched.adv (x[stepBefore x t].time : Int) :=
    fun h => hv (hMono _ _ (by exact_mod_cast hti) h)
  have hp' : p ∉ Sched.adv (x[stepBefore x t'].time : Int) :=
    fun h => hp (hMono _ _ (by exact_mod_cast htj) h)
  exact lem68_honest_past_finalized S Sched x hU hRoots (stepBefore x t) (stepBefore x t') v p D B
    hT hv' hp' hD hB hlt (le_trans (max_le_max hti htj) htR)

/-- **Two justification certificates at one height, on the chains of two honest-held blocks, name
one block, when both blocks are held** (Lemma 76 and roots naming blocks). Under unforgeability,
roots naming blocks, permanent corruption and fewer than a third of the validators in the adversary
set up to `tEnd`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`, `t`, `t'`: the times;
  `p`, `w`: the two holders; `B₁`, `B₂`: the blocks carrying the certificates; `h`: the height;
  `T`, `T'`: the justified blocks.

Roots name blocks until `tR`, at least `max t t'`: the proof compares `T`, held by `p` before
`t`, with `T'`, held by `w` before `t'`. -/
theorem eq_of_cert_same_height (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) {tR : ℕ} (hRoots : RootsNameBlocksUntil S Sched x tR)
    (tEnd t t' : ℕ) (p w : V) (B₁ B₂ T T' : Block V) (h : Height)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int)) (ht : t ≤ tEnd) (ht' : t' ≤ tEnd)
    (hp : p ∉ Sched.adv (t : Int)) (hw : w ∉ Sched.adv (t' : Int))
    (hB₁ : B₁ ∈ (stateBefore x t p).S.T) (hB₂ : B₂ ∈ (stateBefore x t' w).S.T)
    (hJ : GoldilocksCorrectness.Statements.Routines.JustificationCertOn B₁ h T)
    (hJ' : GoldilocksCorrectness.Statements.Routines.JustificationCertOn B₂ h T')
    (hT : T ∈ (stateBefore x t p).S.T) (hT' : T' ∈ (stateBefore x t' w).S.T)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max t t' ≤ tR) :
    T = T' := by
  have hti := time_stepBefore_le x t
  have htj := time_stepBefore_le x t'
  have hA : AdversaryFewerThanThirdUntil Sched (validator_count V)
      (max (x[stepBefore x t].time : Int) (x[stepBefore x t'].time : Int)) :=
    adversaryFewerThanThirdUntil_of_le (max_le (by exact_mod_cast (show x[stepBefore x t].time ≤
      tEnd by omega)) (by exact_mod_cast (show x[stepBefore x t'].time ≤ tEnd by omega))) hThird
  have hp' : p ∉ Sched.adv (x[stepBefore x t].time : Int) :=
    fun h => hp (hMono _ _ (by exact_mod_cast hti) h)
  have hw' : w ∉ Sched.adv (x[stepBefore x t'].time : Int) :=
    fun h => hw (hMono _ _ (by exact_mod_cast htj) h)
  have hroot := lem76_honest_one_justification S Sched x hU (stepBefore x t) (stepBefore x t') p w
    hA B₁ B₂ hB₁ hB₂ h T T' hJ hJ'
  exact hRoots T T' ⟨stepBefore x t, p, hp', le_trans hti (le_trans (le_max_left _ _) htR), hT⟩
    ⟨stepBefore x t', w, hw', le_trans htj (le_trans (le_max_right _ _) htR), hT'⟩ hroot

end GoldilocksCorrectness.Proofs.Executions
