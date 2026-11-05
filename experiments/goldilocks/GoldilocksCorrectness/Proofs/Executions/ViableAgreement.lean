module
public import GoldilocksCorrectness.Proofs.Routines.WalkEnd
public import GoldilocksCorrectness.Proofs.Executions.Invariants
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Executions.ProposalWalk
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Proofs.Executions.Relay
public import GoldilocksCorrectness.Proofs.Routines.Merge
public import GoldilocksCorrectness.Proofs.Routines.Blocks

@[expose] public section

/-! Write `t₁ := slotStart S (s + 1)`,
the time of `p`'s proposal, and `t₃ := voteTime S (s + 1)`, the time of `w`'s vote; `S_p`, `A_p`,
`Φ_p` for the FG state, the AC state and the frame `fg_to_ac S_p` of `p`'s state before `t₁`, and
`S_w`, `A_w`, `Φ_w` for those of `w`'s state before `t₃`. A path block is a block `Y` with
`X ⪯ Y ⪯ B.parent`.

- `viable_heads_agree_of_floor_eq`: when `B`'s parent is in `S_p.T`, `B` is in `S_w.T`, `p`'s
  finalized block and fork-choice root are ancestors of `X` or `X`, and the two `head_height_floor` values
  `head_height_floor S_p` and `head_height_floor S_w` are equal, a path block that has `w`'s
  fork-choice root as an ancestor (or is that root) is a viable head at `p` exactly when it is one
  at `w`. Both states hold each path block, and hold for it the chain state computed from the block
  alone (`ChainStatesComputed`), so the two viability tests compare one height with the two `head_height_floor` values.
- `child_mem_proposer_viable_tree`: every child, in `w`'s viable tree, of a path block, other than
  `B`, is in `p`'s viable tree, when `head_height_floor S_p ≤ head_height_floor S_w`. A child on the path is in `p`'s tree as
  an ancestor of the end of `p`'s walk, or that end; a child off the path was stamped at `w` before the view freeze of
  slot `s` (the other case of `voter_block_tree` would make it an ancestor of `B`, by `hOnly`), so
  it reached `p` by `t₁`, and so did the viable head `w`'s viable tree gives it.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq viewFreeze_cast viewFreeze_eq
  voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (parent_ancestorEq)

open GoldilocksCorrectness.Proofs.Routines (fc_root_eq mem_fg_to_ac_tree mem_viable_heads_iff)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

open GoldilocksCorrectness.Proofs.Routines (mem_viable_tree_iff)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_antisymm
  compatible_iff fc_root_ancestorEq_get_anchor mem_voter_block_tree_iff ancestorEq_of_parent?
  ancestorEq_parent_of_ne depth_of_parent?)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The proposer `p` of slot `s + 1` and its voter `w` agree on the viable heads along the path from
`X` to `B`'s parent, when their `head_height_floor` values are equal. If `p`'s tree before the start `t₁` of slot
`s + 1` holds `B`'s parent, `w`'s tree before the vote time `t₃` of slot `s + 1` holds `B`, the
finalized block and the root of the fork choice of `p`'s node state are `X` or ancestors of `X`,
and the two node states
have the same least viable height (`head_height_floor`), then every block that is `X` or a
descendant of `X`, the root of `w`'s fork choice or a descendant of it, and `B`'s parent or an
ancestor of it, is a viable head at `p` exactly when it is one at `w`.





The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `s`: the slot of the votes;
- `X`: the block the slot-`s` majority extends; `B`: the block `p` proposed at `t₁`;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`.

Read aloud: on the path from `X` to `B`'s parent, past the root of the voter's fork choice, the
proposer and the voter see the same viable heads, when their least viable heights are equal. -/
theorem viable_heads_agree_of_floor_eq (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (X B : Block V) (p w : V)
    (hParentHeld : B.parent ∈ (stateBefore x (slotStart S (s + 1)) p).S.T)
    (hBw : B ∈ (stateBefore x (voteTime S (s + 1)) w).S.T)
    (hFXp : (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq X)
    (hRXp : (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).fc_root.AncestorEq X)
    (hFloor : head_height_floor (stateBefore x (slotStart S (s + 1)) p).S =
      head_height_floor (stateBefore x (voteTime S (s + 1)) w).S) :
    ∀ Y : Block V, X.AncestorEq Y →
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq Y →
      Y.AncestorEq B.parent →
      (Y ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads ↔
        Y ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads) := by
  have hFRw : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root := by
    rw [fc_root_eq]; exact F_ancestorEq_fc_root_of_stateBefore S Sched x (voteTime S (s + 1)) w
  intro Y hXY hRY hYP
  -- both trees hold `Y`
  have hYp : Y ∈ (stateBefore x (slotStart S (s + 1)) p).S.T :=
    ancestors_mem_T_of_exec S Sched x _ p _ Y hParentHeld hYP
  have hYw : Y ∈ (stateBefore x (voteTime S (s + 1)) w).S.T :=
    ancestors_mem_T_of_exec S Sched x _ w _ Y hBw (ancestorEq_trans hYP (parent_ancestorEq B))
  -- both states hold `Y`'s own chain state
  have hCp : ChainStatesComputed S.C (stateBefore x (slotStart S (s + 1)) p).S :=
    (lem11_node_invariant S Sched x (stepBefore x (slotStart S (s + 1))) p).1.2.2.2.2.2.1
  have hCw : ChainStatesComputed S.C (stateBefore x (voteTime S (s + 1)) w).S :=
    (lem11_node_invariant S Sched x (stepBefore x (voteTime S (s + 1))) w).1.2.2.2.2.2.1
  have hσ : (stateBefore x (slotStart S (s + 1)) p).S.σ Y =
      (stateBefore x (voteTime S (s + 1)) w).S.σ Y := by
    rw [hCp Y hYp, hCw Y hYw]
  rw [mem_viable_heads_iff, mem_viable_heads_iff]
  constructor
  · rintro ⟨-, -, -, hfl⟩
    refine ⟨hYw, ancestorEq_trans hFRw hRY, hRY, ?_⟩
    rw [← hFloor, ← hσ]
    exact hfl
  · rintro ⟨-, -, -, hfl⟩
    refine ⟨hYp, ancestorEq_trans hFXp hXY, ancestorEq_trans hRXp hXY, ?_⟩
    rw [hFloor, hσ]
    exact hfl

/-- Every child, in the voter's viable tree, of a block on the path from `X` to `B`'s parent, other
than `B`, is in the proposer's viable tree. In an execution where every time is reached, corruption
is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST` (synchrony from the
receiver's wake, and catch-up on wake), a root names one block among
what honest validators hold, and a block reaches a validator only once it holds the parent: if `GST`
is at most the vote time of slot `s`; `p` is awake and honest at every time from the view freeze of
slot `s` to the start `t₁` of slot `s + 1`, and `w` at every time from `t₁` to the vote time `t₃` of
slot `s + 1`; `w`'s tree before `t₃` holds no slot-`(s + 1)` block other than `B`; `B`'s parent is
in `p`'s viable tree or is `p`'s anchor at `t₁`; that anchor is `X` or an ancestor of `X`; and
`head_height_floor` at `p` is at most the one at `w` — then for every tree `vbt` that `voter_block_tree` answers at `w` for slot
`s + 1`, every block `Y` that is `X` or a descendant of `X`, and `B`'s parent or an ancestor of it,
and every child `D ≠ B` of `Y` in `w`'s viable tree over `vbt`, `D` is in `p`'s viable tree.





The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `X`: the block the slot-`s` majority extends; `B`: the block `p` proposed at `t₁`;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`.

Read aloud: what the voter can step to from a block of the path, other than `B`, the proposer
could step to as well.

Roots name blocks until `slotStart S (s + 1)`: the proof takes a block `w` held before the view
freeze of slot `s` as held by `p` one delay later, at the start of slot `s + 1`
(`mem_T_before_add_delay` at the view freeze). -/
theorem child_mem_proposer_viable_tree (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (X B : Block V) (p w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (slotStart S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hp : ∀ t : ℕ, viewFreeze S s ≤ t → t ≤ slotStart S (s + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    (hw : ∀ t : ℕ, slotStart S (s + 1) ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hOnly : ∀ B' ∈ (stateBefore x (voteTime S (s + 1)) w).S.T, B'.slot = s + 1 → B' = B)
    -- `B`'s parent is the end of `p`'s walk: in `p`'s viable tree, or `p`'s anchor
    (hHp : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
        (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree ∨
      B.parent = get_anchor (stateBefore x (slotStart S (s + 1)) p).A
        (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) ((slotStart S (s + 1) : ℕ) : Int))
    (hApX : (get_anchor (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      ((slotStart S (s + 1) : ℕ) : Int)).AncestorEq X)
    (hFloorLe : head_height_floor (stateBefore x (slotStart S (s + 1)) p).S ≤
      head_height_floor (stateBefore x (voteTime S (s + 1)) w).S) :
    ∀ vbt : Finset (Block V),
      voter_block_tree S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) = .ok vbt →
      ∀ Y : Block V, X.AncestorEq Y → Y.AncestorEq B.parent →
        ∀ D ∈ viable_tree (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) vbt,
          D.parent? = some Y → D ≠ B →
          D ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
            (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree := by
  have hF2p : (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).fc_root := by
    rw [fc_root_eq]; exact F_ancestorEq_fc_root_of_stateBefore S Sched x (slotStart S (s + 1)) p
  intro vbt hvbt Y hXY hYP D hD hDpar hDB
  -- the times
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₁ : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hvf : viewFreeze S s = slotStart S s + 3 * Δ S := viewFreeze_eq S s
  have hvfΔ : viewFreeze S s + Δ S = slotStart S (s + 1) := by omega
  -- the freeze `voter_block_tree` reads for slot `s + 1` is `viewFreeze S s`
  have hfz : ((S.C.t_ (s + 1 - 1) + 3 * S.C.Δ : Time) : Stamp) =
      (((viewFreeze S s : ℕ) : Int) : Stamp) := by
    rw [viewFreeze_cast, Nat.add_sub_cancel]
  -- the ancestry facts at `p`
  have hRpA : (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).fc_root.AncestorEq
      (get_anchor (stateBefore x (slotStart S (s + 1)) p).A
        (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) ((slotStart S (s + 1) : ℕ) : Int)) :=
    fc_root_ancestorEq_get_anchor _ _ _
  have hYD : Y.AncestorEq D := ancestorEq_of_parent? hDpar
  have hXD : X.AncestorEq D := ancestorEq_trans hXY hYD
  have hRpD : (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).fc_root.AncestorEq D :=
    ancestorEq_trans hRpA (ancestorEq_trans hApX hXD)
  have hFpD : (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq D :=
    ancestorEq_trans hF2p hRpD
  -- `w`'s viable tree over `vbt`, unfolded at `D`
  rw [mem_viable_tree_iff] at hD ⊢
  obtain ⟨hDv, -, W, hWmem, hDW⟩ := hD
  obtain ⟨hWv, hWvh⟩ := Finset.mem_inter.1 hWmem
  by_cases hDP : D.AncestorEq B.parent
  · -- case A, `D` on the path: `D` is `B`'s parent or an ancestor of it
    rcases hHp with hBin | hBeq
    · -- `B`'s parent is in `p`'s viable tree, and so is `D`, with the same viable head
      rw [mem_viable_tree_iff] at hBin
      obtain ⟨hBΦ, -, W', hW'mem, hBW'⟩ := hBin
      have hBT := ((mem_fg_to_ac_tree _ _).1 hBΦ).1
      exact ⟨(mem_fg_to_ac_tree _ _).2 ⟨ancestors_mem_T_of_exec S Sched x _ p _ D hBT hDP, hFpD⟩,
        hRpD, W', hW'mem, ancestorEq_trans hDP hBW'⟩
    · -- `B`'s parent is `p`'s anchor: then `D` is an ancestor of its own parent `Y`, impossible
      exfalso
      have hDY : D.AncestorEq Y := by
        rw [hBeq] at hDP
        exact ancestorEq_trans hDP (ancestorEq_trans hApX hXY)
      have hDeq : D = Y := ancestorEq_antisymm hDY hYD
      have hdep := depth_of_parent? hDpar
      rw [hDeq] at hdep
      omega
  · -- case B, `D` off the path: what `vbt` holds of `D`'s descendants reached `p` by `t₁`
    have hReach : ∀ Z ∈ vbt, D.AncestorEq Z → Z ∈ (stateBefore x (slotStart S (s + 1)) p).S.T := by
      intro Z hZ hDZ
      obtain ⟨hZΦ, τ, hτ, hfr | ⟨B', hB'Φ, hB's, hZB'⟩⟩ :=
        (mem_voter_block_tree_iff S.C _ _ (s + 1) vbt hvbt Z).1 hZ
      · -- `Z` was stamped at `w` before the view freeze of slot `s`
        have hZw : Z ∈ (stateBefore x (voteTime S (s + 1)) w).S.T :=
          ((mem_fg_to_ac_tree _ _).1 hZΦ).1
        rw [hfz] at hfr
        have hZf : Z ∈ (stateBefore x (viewFreeze S s) w).S.T :=
          (blockStamp_lt_iff hDiv hZw).1 ⟨τ, hτ, hfr⟩
        have hcompat : (stateBefore x (viewFreeze S s + Δ S) p).S.F.compatible Z = true := by
          rw [hvfΔ]
          exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFpD hDZ))
        have h := mem_T_before_add_delay hDiv hMono hSync hCatch (hRoots.mono (by omega))
          hParent (t := viewFreeze S s) (u := w) (w := p) (by omega) (by omega)
          (fun h => (hw (slotStart S (s + 1)) le_rfl (by omega)).2 (hMono _ _ (by omega) h)) hZf
          (fun t' h1 h2 => hp t' h1 (by omega))
          hcompat
        rwa [hvfΔ] at h
      · -- `Z` leads to a slot-`(s + 1)` block of `w`'s tree, which is `B`: then `D` is on the path
        exfalso
        have hB'B := hOnly B' ((mem_fg_to_ac_tree _ _).1 hB'Φ).1 hB's
        rw [hB'B] at hZB'
        exact hDP (ancestorEq_parent_of_ne (ancestorEq_trans hDZ hZB') hDB)
    have hDp := hReach D hDv (ancestorEq_refl D)
    have hWp := hReach W hWv hDW
    -- `W` is a viable head at `p`: the same chain state, and `p`'s floor is at most `w`'s
    obtain ⟨hWw, -, -, hflw⟩ := (mem_viable_heads_iff _ _).1 hWvh
    have hCp : ChainStatesComputed S.C (stateBefore x (slotStart S (s + 1)) p).S :=
      (lem11_node_invariant S Sched x (stepBefore x (slotStart S (s + 1))) p).1.2.2.2.2.2.1
    have hCw : ChainStatesComputed S.C (stateBefore x (voteTime S (s + 1)) w).S :=
      (lem11_node_invariant S Sched x (stepBefore x (voteTime S (s + 1))) w).1.2.2.2.2.2.1
    have hFpW := ancestorEq_trans hFpD hDW
    have hfl : head_height_floor (stateBefore x (slotStart S (s + 1)) p).S ≤
        ((stateBefore x (slotStart S (s + 1)) p).S.σ W).h := by
      rw [hCp W hWp, ← hCw W hWw]
      exact le_trans hFloorLe hflw
    exact ⟨(mem_fg_to_ac_tree _ _).2 ⟨hDp, hFpD⟩, hRpD, W,
      Finset.mem_inter.2 ⟨(mem_fg_to_ac_tree _ _).2 ⟨hWp, hFpW⟩,
        (mem_viable_heads_iff _ _).2 ⟨hWp, hFpW, ancestorEq_trans hRpD hDW, hfl⟩⟩, hDW⟩

end GoldilocksCorrectness.Proofs.Executions
