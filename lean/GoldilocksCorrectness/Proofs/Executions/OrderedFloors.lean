module
public import GoldilocksCorrectness.Proofs.Executions.Boxes
public import GoldilocksCorrectness.Proofs.Executions.ViableAgreement

@[expose] public section

/-!
# The `head_height_floor` values (the least chain-state height a viable block may have) ordered: the voter's least viable height at least the proposer's

Write `t₁ := slotStart S (s + 1)`, the time of `p`'s proposal, and `t₃ := voteTime S (s + 1)`,
the time of `w`'s vote; `S_p` for the FG state of `p`'s state before `t₁` and `S_w` for that of
`w`'s state before `t₃`.

- `lem59le_frame`: when `p`'s frame has the root `ρ_p` and `head_height_floor` equal to `φ`, `w`'s has `head_height_floor` equal to
  `φ_w` with `φ ≤ φ_w`, `p` holds `B`'s parent and `ρ_p` is `X` or an ancestor of `X`, every block
  from `X` to `B`'s parent that is a viable head at `w` is a viable head at `p`: the direction of
  `viable_heads_agree_of_floor_eq` that survives ordered `head_height_floor` values.
- `lem59le_boxOne`, `lem59le_boxTwo`, `lem59le_boxThree`: the box instances of Lemma 59
  (`lem59_boxOne`, `lem59_boxTwo`, `lem59_boxThree`) with the two `h_max` ordered in place of
  equal, giving the two frame shapes and the order of their `head_height_floor` values.

Each is proved in an `_at` form with the reading times parameters; the landed forms are its
instances.


-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (slotStart voteTime)

open GoldilocksCorrectness.Proofs.Routines (parent_ancestorEq)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

open GoldilocksCorrectness.Proofs.Routines (mem_viable_tree_iff)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (FrameShape BoxOne BoxTwo BoxThree
  frameShape_of_boxOne frameShape_of_boxTwo frameShape_of_boxThree lem56_frame_of_shape)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans ancestorEq_refl)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `lem59le_frame` with `p`'s and `w`'s states read before two times `t_p` and `t_w` in place of
the start and the vote time of slot `s + 1`. The proof; the audited statement is in
`Statements/Executions/OrderedFloorStatements.lean`. -/
theorem lem59le_frame_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t_p t_w : ℕ) (X B : Block V) (p w : V)
    (ρ_p ρ_w : Block V) (φ φ_w : Height)
    -- `p`'s frame before `t_p` has the root `ρ_p` and `head_height_floor` equal to `φ`
    (hShapeP : FrameShape (stateBefore x t_p p).S ρ_p φ)
    -- `w`'s frame before `t_w` has the root `ρ_w` and `head_height_floor` equal to `φ_w`
    (hShapeW : FrameShape (stateBefore x t_w w).S ρ_w φ_w)
    -- `head_height_floor` at `p` is at most the one at `w`
    (hFloorLe : φ ≤ φ_w)
    -- `p`'s tree before `t_p` holds `B`'s parent
    (hParentHeld : B.parent ∈ (stateBefore x t_p p).S.T)
    -- `ρ_p` is `X` or an ancestor of `X`
    (hRXp : ρ_p.AncestorEq X) :
    ∀ Y : Block V, X.AncestorEq Y → ρ_w.AncestorEq Y → Y.AncestorEq B.parent →
      Y ∈ (fg_to_ac (stateBefore x t_w w).S).viable_heads →
      Y ∈ (fg_to_ac (stateBefore x t_p p).S).viable_heads := by
  intro Y hXY _ hYP hYw
  obtain ⟨-, -, hHp⟩ := lem56_frame_of_shape _ _ _ hShapeP
  obtain ⟨-, -, hHw⟩ := lem56_frame_of_shape _ _ _ hShapeW
  obtain ⟨hYwT, -, -, hflw⟩ := (hHw Y).1 hYw
  -- `p`'s tree holds `Y`
  have hYp : Y ∈ (stateBefore x t_p p).S.T :=
    ancestors_mem_T_of_exec S Sched x _ p _ Y hParentHeld hYP
  -- both states hold `Y`'s own chain state
  have hCp : ChainStatesComputed S.C (stateBefore x t_p p).S :=
    (lem11_node_invariant S Sched x (stepBefore x t_p) p).1.2.2.2.2.2.1
  have hCw : ChainStatesComputed S.C (stateBefore x t_w w).S :=
    (lem11_node_invariant S Sched x (stepBefore x t_w) w).1.2.2.2.2.2.1
  have hσ : (stateBefore x t_p p).S.σ Y =
      (stateBefore x t_w w).S.σ Y := by
    rw [hCp Y hYp, hCw Y hYwT]
  -- `p`'s finalized block is `ρ_p` or an ancestor of it (Lemma 46)
  have hFρp : (stateBefore x t_p p).S.F.AncestorEq ρ_p := by
    rw [← hShapeP.1]
    exact F_ancestorEq_fc_root_of_stateBefore S Sched x _ p
  have hρY : ρ_p.AncestorEq Y := ancestorEq_trans hRXp hXY
  refine (hHp Y).2 ⟨hYp, ancestorEq_trans hFρp hρY, hρY, ?_⟩
  rw [hσ]
  exact le_trans hFloorLe hflw

/-- **The viable heads along the path, with ordered `head_height_floor` values.** When `p`'s frame before the start
`t₁` of slot `s + 1` has the root `ρ_p` and `head_height_floor` equal to `φ`, `w`'s frame before the vote time `t₃`
of slot `s + 1` has the root `ρ_w` and `head_height_floor` equal to `φ_w`, `φ` is at most `φ_w`, `p`'s tree before
`t₁` holds `B`'s parent, and `ρ_p` is `X` or an ancestor of `X`: then every block that is `X` or a
descendant of `X`, `ρ_w` or a descendant of `ρ_w`, and `B`'s parent or an ancestor of it, and that
is a viable head at `w`, is a viable head at `p`.

Why: `p`'s tree holds the block, as an ancestor of `B`'s parent, or that parent; `w`'s holds it,
as a viable head; both hold for it its own chain state (`ChainStatesComputed`); its height is at
least `φ_w`, so at least `φ`; `ρ_p` is an ancestor of it through `X`, and so is `p`'s finalized
block (Lemma 46); so it is a viable head at `p` (Lemma 56).

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `s`: the slot of the votes;
- `X`: the block the slot-`s` majority extends; `B`: the block `p` proposed at `t₁`;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `ρ_p`, `ρ_w`: the roots of `p`'s and `w`'s fork choices; `φ`, `φ_w`: their `head_height_floor` values.

Read aloud: on the path from `X` to `B`'s parent past `w`'s root, a block viable at `w` is viable
at `p`, when `head_height_floor` at `w` is at least the one at `p`.



It is the instance of `lem59le_frame_at` at `t_p := slotStart S (s + 1)`,
`t_w := voteTime S (s + 1)`. -/
theorem lem59le_frame (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (X B : Block V) (p w : V)
    (ρ_p ρ_w : Block V) (φ φ_w : Height)
    -- `p`'s frame before `t₁` has the root `ρ_p` and `head_height_floor` equal to `φ`
    (hShapeP : FrameShape (stateBefore x (slotStart S (s + 1)) p).S ρ_p φ)
    -- `w`'s frame before `t₃` has the root `ρ_w` and `head_height_floor` equal to `φ_w`
    (hShapeW : FrameShape (stateBefore x (voteTime S (s + 1)) w).S ρ_w φ_w)
    -- `head_height_floor` at `p` is at most the one at `w`
    (hFloorLe : φ ≤ φ_w)
    -- `p`'s tree before `t₁` holds `B`'s parent
    (hParentHeld : B.parent ∈ (stateBefore x (slotStart S (s + 1)) p).S.T)
    -- `ρ_p` is `X` or an ancestor of `X`
    (hRXp : ρ_p.AncestorEq X) :
    ∀ Y : Block V, X.AncestorEq Y → ρ_w.AncestorEq Y → Y.AncestorEq B.parent →
      Y ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads →
      Y ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads :=
  lem59le_frame_at S Sched x (slotStart S (s + 1)) (voteTime S (s + 1)) X B p w ρ_p ρ_w φ φ_w
    hShapeP hShapeW hFloorLe hParentHeld hRXp

/-- `lem59le_boxOne` with `w`'s state read before a time `t_w` in place of the vote time of slot
`s + 1`. The proof; the audited statement is in
`Statements/Executions/OrderedFloorStatements.lean`. -/
theorem lem59le_boxOne_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s t_w : ℕ) (X B : Block V) (p w : V)
    (hBoxP : BoxOne (stateBefore x (slotStart S (s + 1)) p).S)
    (hBoxW : BoxOne (stateBefore x t_w w).S)
    (hHmaxLe : (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤
      (stateBefore x t_w w).S.h_max)
    (hFw : (stateBefore x t_w w).S.F.AncestorEq B)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree)
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S (s + 1)) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq W ∧
        (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C W).h) :
    FrameShape (stateBefore x (slotStart S (s + 1)) p).S
        (stateBefore x (slotStart S (s + 1)) p).S.F
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      FrameShape (stateBefore x t_w w).S
        (stateBefore x t_w w).S.F
        ((stateBefore x t_w w).S.h_max - 1) ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤
        (stateBefore x t_w w).S.h_max - 1 ∧
      (stateBefore x t_w w).S.F.AncestorEq B ∧
      (∃ W ∈ (stateBefore x (slotStart S (s + 1)) p).S.T,
        X.AncestorEq W ∧ (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq W ∧
          (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C W).h) ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C B).h := by
  have hP := (frameShape_of_boxOne _ hBoxP).2
  have hW := (frameShape_of_boxOne _ hBoxW).2
  have hfl := proposal_viable S Sched x s B p hPropose hParentIn
  rw [hP.2] at hfl
  exact ⟨hP, hW, Nat.sub_le_sub_right hHmaxLe 1, hFw, hHeadP, hfl⟩

/-- Lemma 59 in box 1 with ordered `h_max`. The proof; the audited statement is in
`Statements/Executions/OrderedFloorStatements.lean`.

It is the instance of `lem59le_boxOne_at` at `t_w := voteTime S (s + 1)`. -/
theorem lem59le_boxOne (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (X B : Block V) (p w : V)
    (hBoxP : BoxOne (stateBefore x (slotStart S (s + 1)) p).S)
    (hBoxW : BoxOne (stateBefore x (voteTime S (s + 1)) w).S)
    (hHmaxLe : (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤
      (stateBefore x (voteTime S (s + 1)) w).S.h_max)
    (hFw : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq B)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree)
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S (s + 1)) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq W ∧
        (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C W).h) :
    FrameShape (stateBefore x (slotStart S (s + 1)) p).S
        (stateBefore x (slotStart S (s + 1)) p).S.F
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      FrameShape (stateBefore x (voteTime S (s + 1)) w).S
        (stateBefore x (voteTime S (s + 1)) w).S.F
        ((stateBefore x (voteTime S (s + 1)) w).S.h_max - 1) ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤
        (stateBefore x (voteTime S (s + 1)) w).S.h_max - 1 ∧
      (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq B ∧
      (∃ W ∈ (stateBefore x (slotStart S (s + 1)) p).S.T,
        X.AncestorEq W ∧ (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq W ∧
          (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C W).h) ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C B).h :=
  lem59le_boxOne_at S Sched x s (voteTime S (s + 1)) X B p w hBoxP hBoxW hHmaxLe hFw hPropose
    hParentIn hHeadP

/-- `lem59le_boxTwo` with `w`'s state read before a time `t_w` in place of the vote time of slot
`s + 1`. The proof; the audited statement is in
`Statements/Executions/OrderedFloorStatements.lean`. -/
theorem lem59le_boxTwo_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s t_w : ℕ) (B J₀ : Block V) (p w : V)
    (hBoxP : BoxTwo (stateBefore x (slotStart S (s + 1)) p).S J₀)
    (hBoxW : (BoxTwo (stateBefore x t_w w).S J₀ ∧ J₀ ≠ Block.genesis) ∨
      (BoxThree (stateBefore x t_w w).S ∧
        (stateBefore x (slotStart S (s + 1)) p).S.h_max =
          (stateBefore x t_w w).S.h_max ∧
        (stateBefore x t_w w).S.F.AncestorEq B))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) :
    FrameShape (stateBefore x (slotStart S (s + 1)) p).S J₀
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      (∃ ρ_w : Block V, ∃ φ_w : Height,
        FrameShape (stateBefore x t_w w).S ρ_w φ_w ∧
        (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ φ_w ∧ ρ_w.AncestorEq B) ∧
      J₀.AncestorEq B.parent ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C B).h := by
  have hP := frameShape_of_boxTwo _ _ hBoxP
  -- `B`'s parent is in `p`'s viable tree, so the root `J₀` is an ancestor of it
  have hJP : J₀.AncestorEq B.parent := by
    have hR := (lem56_frame_of_shape _ _ _ hP).1
    simp only [mem_viable_tree_iff] at hParentIn
    obtain ⟨-, hRB, -⟩ := hParentIn
    rw [hR] at hRB
    exact hRB
  have hfl := proposal_viable S Sched x s B p hPropose hParentIn
  rw [hP.2] at hfl
  refine ⟨hP, ?_, hJP, hfl⟩
  rcases hBoxW with ⟨hBoxW, hJ₀⟩ | ⟨hBoxW, hHmax, hFw⟩
  · -- `w` in box 2 with `J₀`: the root `J₀` and the floor `p`'s `h_max − 1`
    have hW := frameShape_of_boxTwo _ _ hBoxW
    have hmax : (stateBefore x t_w w).S.h_max =
        (stateBefore x (slotStart S (s + 1)) p).S.h_max := by
      rw [hBoxW.1, hBoxP.1, h_j_eq_of_boxTwo S Sched x _ w J₀ hBoxW hJ₀,
        h_j_eq_of_boxTwo S Sched x _ p J₀ hBoxP hJ₀]
    rw [hmax] at hW
    exact ⟨J₀, _, hW, le_refl _, ancestorEq_trans hJP (parent_ancestorEq B)⟩
  · -- `w` contested with `p`'s `h_max`: the root `w`'s finalized block and the floor `h_max`
    have hW := (frameShape_of_boxThree _ hBoxW).2
    refine ⟨_, _, hW, ?_, hFw⟩
    rw [← hHmax]
    exact Nat.sub_le _ 1

/-- Lemma 59 in box 2 with the voter in box 2 or contested. The proof; the audited statement is
in `Statements/Executions/OrderedFloorStatements.lean`.

It is the instance of `lem59le_boxTwo_at` at `t_w := voteTime S (s + 1)`. -/
theorem lem59le_boxTwo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (B J₀ : Block V) (p w : V)
    (hBoxP : BoxTwo (stateBefore x (slotStart S (s + 1)) p).S J₀)
    (hBoxW : (BoxTwo (stateBefore x (voteTime S (s + 1)) w).S J₀ ∧ J₀ ≠ Block.genesis) ∨
      (BoxThree (stateBefore x (voteTime S (s + 1)) w).S ∧
        (stateBefore x (slotStart S (s + 1)) p).S.h_max =
          (stateBefore x (voteTime S (s + 1)) w).S.h_max ∧
        (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq B))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) :
    FrameShape (stateBefore x (slotStart S (s + 1)) p).S J₀
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      (∃ ρ_w : Block V, ∃ φ_w : Height,
        FrameShape (stateBefore x (voteTime S (s + 1)) w).S ρ_w φ_w ∧
        (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ φ_w ∧ ρ_w.AncestorEq B) ∧
      J₀.AncestorEq B.parent ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C B).h :=
  lem59le_boxTwo_at S Sched x s (voteTime S (s + 1)) B J₀ p w hBoxP hBoxW hPropose hParentIn

/-- `lem59le_boxThree` with `w`'s state read before a time `t_w` in place of the vote time of slot
`s + 1`. The proof; the audited statement is in
`Statements/Executions/OrderedFloorStatements.lean`. -/
theorem lem59le_boxThree_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s t_w : ℕ) (B : Block V) (p w : V)
    (hBoxP : BoxThree (stateBefore x (slotStart S (s + 1)) p).S)
    (hBoxW : BoxThree (stateBefore x t_w w).S)
    (hHmaxLe : (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤
      (stateBefore x t_w w).S.h_max)
    (hFw : (stateBefore x t_w w).S.F.AncestorEq B)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) :
    FrameShape (stateBefore x (slotStart S (s + 1)) p).S
        (stateBefore x (slotStart S (s + 1)) p).S.F
        (stateBefore x (slotStart S (s + 1)) p).S.h_max ∧
      FrameShape (stateBefore x t_w w).S
        (stateBefore x t_w w).S.F
        (stateBefore x t_w w).S.h_max ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤
        (stateBefore x t_w w).S.h_max ∧
      (stateBefore x t_w w).S.F.AncestorEq B ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤ (chainStateOf S.C B).h := by
  have hP := (frameShape_of_boxThree _ hBoxP).2
  have hW := (frameShape_of_boxThree _ hBoxW).2
  have hfl := proposal_viable S Sched x s B p hPropose hParentIn
  rw [hP.2] at hfl
  exact ⟨hP, hW, hHmaxLe, hFw, hfl⟩

/-- Lemma 59 in box 3 with ordered `h_max`. The proof; the audited statement is in
`Statements/Executions/OrderedFloorStatements.lean`.

It is the instance of `lem59le_boxThree_at` at `t_w := voteTime S (s + 1)`. -/
theorem lem59le_boxThree (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (B : Block V) (p w : V)
    (hBoxP : BoxThree (stateBefore x (slotStart S (s + 1)) p).S)
    (hBoxW : BoxThree (stateBefore x (voteTime S (s + 1)) w).S)
    (hHmaxLe : (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤
      (stateBefore x (voteTime S (s + 1)) w).S.h_max)
    (hFw : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq B)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) :
    FrameShape (stateBefore x (slotStart S (s + 1)) p).S
        (stateBefore x (slotStart S (s + 1)) p).S.F
        (stateBefore x (slotStart S (s + 1)) p).S.h_max ∧
      FrameShape (stateBefore x (voteTime S (s + 1)) w).S
        (stateBefore x (voteTime S (s + 1)) w).S.F
        (stateBefore x (voteTime S (s + 1)) w).S.h_max ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤
        (stateBefore x (voteTime S (s + 1)) w).S.h_max ∧
      (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq B ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤ (chainStateOf S.C B).h :=
  lem59le_boxThree_at S Sched x s (voteTime S (s + 1)) B p w hBoxP hBoxW hHmaxLe hFw hPropose
    hParentIn

end GoldilocksCorrectness.Proofs.Executions
