module
public import GoldilocksCorrectness.Statements.Executions.FrameShapeStatements
public import GoldilocksCorrectness.Statements.Executions.ProposalViabilityStatements

@[expose] public section

/-!
# The box instances of Lemmas 59 and 61

The proofs of the statements of `GoldilocksCorrectness/Statements/Executions/BoxStatements.lean`:
each box (`BoxOne`, `BoxTwo`, `BoxThree`) gives the frame shape at the states Lemmas 59 and 61
read (Lemma 56's readers), and with it their frame hypotheses. The `head_height_floor` (the least chain-state height a viable block may have) bound on the honest
proposal is `proposal_viable`; the equal `h_max` of box 2 is Lemma 57's justified height; the
record of Lemma 61 is Lemma 57's. Each lemma is proved in an `_at` form, the reading time of `w`
(Lemma 59) or `v` (Lemma 61) a parameter, through `frame_hypotheses_at` for Lemma 61; the landed
forms are its instances.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (slotStart voteTime supportCutoff)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Statements.Routines (JustifiedHeight)

open GoldilocksCorrectness.Proofs.Routines (mem_viable_tree_iff)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (FrameShape BoxOne BoxTwo BoxThree
  frameShape_of_boxOne frameShape_of_boxTwo frameShape_of_boxThree lem56_frame_of_shape)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- In box 2 with a justified block `J₀` other than the genesis block, the cache `h_j` of a
validator's state before the time `t` is `J₀`'s chain-state height (Lemma 57, with Lemma 11).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
- `J₀`: the justified block. -/
theorem h_j_eq_of_boxTwo (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (t : ℕ) (v : V) (J₀ : Block V)
    (hBox : BoxTwo (stateBefore x t v).S J₀)
    (hJ₀ : J₀ ≠ Block.genesis) :
    (stateBefore x t v).S.h_j = (chainStateOf S.C J₀).h := by
  obtain ⟨-, hJH, hJT, -, -⟩ := lem57_justification_cache_and_record S Sched x (stepBefore x t) v
  have hJ : (stateBefore x t v).S.J = J₀ := hBox.2.2
  have hJT' : (stateBefore x t v).S.J ∈ (stateBefore x t v).S.T := hJT
  have hσ : (stateBefore x t v).S.σ (stateBefore x t v).S.J =
      chainStateOf S.C (stateBefore x t v).S.J :=
    (lem11_node_invariant S Sched x (stepBefore x t) v).1.2.2.2.2.2.1 _ hJT'
  have hJH' : JustifiedHeight (stateBefore x t v).S := hJH
  rcases hJH' with hg | hh
  · exact absurd (hJ.symm.trans hg) hJ₀
  · rw [hσ, hJ] at hh
    exact hh.symm

/-- `lem59_boxOne` with `w`'s state read before a time `t_w` in place of the vote time of slot
`s + 1`. The proof; the audited statement is in `Statements/Executions/BoxStatements.lean`. -/
theorem lem59_boxOne_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s t_w : ℕ) (X B : Block V) (p w : V)
    (hBoxP : BoxOne (stateBefore x (slotStart S (s + 1)) p).S)
    (hBoxW : BoxOne (stateBefore x t_w w).S)
    (hHmax : (stateBefore x (slotStart S (s + 1)) p).S.h_max =
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
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      (stateBefore x t_w w).S.F.AncestorEq B ∧
      (∃ W ∈ (stateBefore x (slotStart S (s + 1)) p).S.T,
        X.AncestorEq W ∧ (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq W ∧
          (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C W).h) ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C B).h := by
  have hP := (frameShape_of_boxOne _ hBoxP).2
  have hW := (frameShape_of_boxOne _ hBoxW).2
  rw [← hHmax] at hW
  have hfl := proposal_viable S Sched x s B p hPropose hParentIn
  rw [hP.2] at hfl
  exact ⟨hP, hW, hFw, hHeadP, hfl⟩

/-- Lemma 59 in box 1. The proof; the audited statement is in
`Statements/Executions/BoxStatements.lean`.

It is the instance of `lem59_boxOne_at` at `t_w := voteTime S (s + 1)`. -/
theorem lem59_boxOne (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (X B : Block V) (p w : V)
    (hBoxP : BoxOne (stateBefore x (slotStart S (s + 1)) p).S)
    (hBoxW : BoxOne (stateBefore x (voteTime S (s + 1)) w).S)
    (hHmax : (stateBefore x (slotStart S (s + 1)) p).S.h_max =
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
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq B ∧
      (∃ W ∈ (stateBefore x (slotStart S (s + 1)) p).S.T,
        X.AncestorEq W ∧ (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq W ∧
          (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C W).h) ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C B).h :=
  lem59_boxOne_at S Sched x s (voteTime S (s + 1)) X B p w hBoxP hBoxW hHmax hFw hPropose hParentIn
    hHeadP

/-- `lem59_boxTwo` with `w`'s state read before a time `t_w` in place of the vote time of slot
`s + 1`. The proof; the audited statement is in `Statements/Executions/BoxStatements.lean`. -/
theorem lem59_boxTwo_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s t_w : ℕ) (B J₀ : Block V) (p w : V)
    (hBoxP : BoxTwo (stateBefore x (slotStart S (s + 1)) p).S J₀)
    (hBoxW : BoxTwo (stateBefore x t_w w).S J₀)
    (hJ₀ : J₀ ≠ Block.genesis)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) :
    FrameShape (stateBefore x (slotStart S (s + 1)) p).S J₀
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      FrameShape (stateBefore x t_w w).S J₀
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      J₀.AncestorEq B.parent ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C B).h := by
  have hP := frameShape_of_boxTwo _ _ hBoxP
  have hW := frameShape_of_boxTwo _ _ hBoxW
  -- the two `h_max` are `J₀`'s height plus one
  have hmax : (stateBefore x t_w w).S.h_max =
      (stateBefore x (slotStart S (s + 1)) p).S.h_max := by
    rw [hBoxW.1, hBoxP.1, h_j_eq_of_boxTwo S Sched x _ w J₀ hBoxW hJ₀,
      h_j_eq_of_boxTwo S Sched x _ p J₀ hBoxP hJ₀]
  rw [hmax] at hW
  -- `B`'s parent is in `p`'s viable tree, so the root `J₀` is an ancestor of it
  have hJP : J₀.AncestorEq B.parent := by
    have hR := (lem56_frame_of_shape _ _ _ hP).1
    simp only [mem_viable_tree_iff] at hParentIn
    obtain ⟨-, hRB, -⟩ := hParentIn
    rw [hR] at hRB
    exact hRB
  have hfl := proposal_viable S Sched x s B p hPropose hParentIn
  rw [hP.2] at hfl
  exact ⟨hP, hW, hJP, hfl⟩

/-- Lemma 59 in box 2. The proof; the audited statement is in
`Statements/Executions/BoxStatements.lean`.

It is the instance of `lem59_boxTwo_at` at `t_w := voteTime S (s + 1)`. -/
theorem lem59_boxTwo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (B J₀ : Block V) (p w : V)
    (hBoxP : BoxTwo (stateBefore x (slotStart S (s + 1)) p).S J₀)
    (hBoxW : BoxTwo (stateBefore x (voteTime S (s + 1)) w).S J₀)
    (hJ₀ : J₀ ≠ Block.genesis)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) :
    FrameShape (stateBefore x (slotStart S (s + 1)) p).S J₀
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      FrameShape (stateBefore x (voteTime S (s + 1)) w).S J₀
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      J₀.AncestorEq B.parent ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C B).h :=
  lem59_boxTwo_at S Sched x s (voteTime S (s + 1)) B J₀ p w hBoxP hBoxW hJ₀ hPropose hParentIn

/-- `lem59_boxThree` with `w`'s state read before a time `t_w` in place of the vote time of slot
`s + 1`. The proof; the audited statement is in `Statements/Executions/BoxStatements.lean`. -/
theorem lem59_boxThree_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s t_w : ℕ) (B : Block V) (p w : V)
    (hBoxP : BoxThree (stateBefore x (slotStart S (s + 1)) p).S)
    (hBoxW : BoxThree (stateBefore x t_w w).S)
    (hHmax : (stateBefore x (slotStart S (s + 1)) p).S.h_max =
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
        (stateBefore x (slotStart S (s + 1)) p).S.h_max ∧
      (stateBefore x t_w w).S.F.AncestorEq B ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤ (chainStateOf S.C B).h := by
  have hP := (frameShape_of_boxThree _ hBoxP).2
  have hW := (frameShape_of_boxThree _ hBoxW).2
  rw [← hHmax] at hW
  have hfl := proposal_viable S Sched x s B p hPropose hParentIn
  rw [hP.2] at hfl
  exact ⟨hP, hW, hFw, hfl⟩

/-- Lemma 59 in box 3. The proof; the audited statement is in
`Statements/Executions/BoxStatements.lean`.

It is the instance of `lem59_boxThree_at` at `t_w := voteTime S (s + 1)`. -/
theorem lem59_boxThree (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (B : Block V) (p w : V)
    (hBoxP : BoxThree (stateBefore x (slotStart S (s + 1)) p).S)
    (hBoxW : BoxThree (stateBefore x (voteTime S (s + 1)) w).S)
    (hHmax : (stateBefore x (slotStart S (s + 1)) p).S.h_max =
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
        (stateBefore x (slotStart S (s + 1)) p).S.h_max ∧
      (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq B ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤ (chainStateOf S.C B).h :=
  lem59_boxThree_at S Sched x s (voteTime S (s + 1)) B p w hBoxP hBoxW hHmax hFw hPropose hParentIn

/-- The hypotheses of Lemma 55 on the viable tree and the record, from `FrameShape` of `v`'s FG
state before a time `t`: `lem61_frame_hypotheses` with `t` in place of the support cutoff of slot
`s + 1`, which its proof does not read.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time `v`'s state is read;
- `B`: the block; `v`: the validator; `ρ`, `φ`: the root and the `head_height_floor` value that
  `FrameShape` gives. -/
theorem frame_hypotheses_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (B : Block V) (v : V) (ρ : Block V) (φ : Height)
    (hShape : FrameShape (stateBefore x t v).S ρ φ)
    (hRootV : ρ.AncestorEq B)
    (hBHeight : φ ≤ (chainStateOf S.C B).h)
    (hBin : B ∈ (stateBefore x t v).S.T)
    (hLockBox : (stateBefore x t v).S.h_j < (chainStateOf S.C B).h ∨
      (stateBefore x t v).Λ.lock (chainStateOf S.C B).h = none ∨
      (stateBefore x t v).Λ.lock (chainStateOf S.C B).h = some (chainStateOf S.C B).T_h.root) :
    B ∈ viable_tree (fg_to_ac (stateBefore x t v).S) (fg_to_ac (stateBefore x t v).S).tree ∧
      ((stateBefore x t v).Λ.lock (chainStateOf S.C B).h = none ∨
        ((stateBefore x t v).Λ.lock (chainStateOf S.C B).h = some (chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (stateBefore x t v).Λ.sent,
            b.h = (chainStateOf S.C B).h → b.T = (chainStateOf S.C B).T_h.root)) := by
  refine ⟨mem_viable_tree_of_frameShape_of_stateBefore S Sched x _ v B ρ φ hShape hRootV hBHeight
    hBin, ?_⟩
  rcases hLockBox with hlt | hnone | hlock
  · exact Or.inl (lock_none_of_h_j_lt_of_stateBefore S Sched x _ v _ hlt)
  · exact Or.inl hnone
  · exact Or.inr ⟨hlock, lockNamesSent_of_stateBefore S Sched x _ v _ _ hlock⟩

/-- `lem61_boxOne` with `v`'s state read before a time `t_v` in place of the support cutoff of slot
`s + 1`. The proof; the audited statement is in `Statements/Executions/BoxStatements.lean`. -/
theorem lem61_boxOne_at (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (t_v : ℕ) (B : Block V) (v : V)
    (hBox : BoxOne (stateBefore x t_v v).S)
    (hFv : (stateBefore x t_v v).S.F.AncestorEq B)
    (hBHeight : (stateBefore x t_v v).S.h_max - 1 ≤ (chainStateOf S.C B).h)
    (hBin : B ∈ (stateBefore x t_v v).S.T) :
    B ∈ viable_tree (fg_to_ac (stateBefore x t_v v).S)
        (fg_to_ac (stateBefore x t_v v).S).tree ∧
      ((stateBefore x t_v v).Λ.lock (chainStateOf S.C B).h = none ∨
        ((stateBefore x t_v v).Λ.lock (chainStateOf S.C B).h =
            some (chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (stateBefore x t_v v).Λ.sent,
            b.h = (chainStateOf S.C B).h → b.T = (chainStateOf S.C B).T_h.root)) := by
  have hShape := (frameShape_of_boxOne _ hBox).2
  have hb : (stateBefore x t_v v).S.h_j + 1 <
      (stateBefore x t_v v).S.h_max := hBox
  have hlt : (stateBefore x t_v v).S.h_j < (chainStateOf S.C B).h := by
    unfold Height at *
    omega
  exact frame_hypotheses_at S Sched x t_v B v _ _
    hShape hFv hBHeight hBin (Or.inl hlt)

/-- Lemma 61 in box 1. The proof; the audited statement is in
`Statements/Executions/BoxStatements.lean`.

It is the instance of `lem61_boxOne_at` at `t_v := supportCutoff S (s + 1)`. -/
theorem lem61_boxOne (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (s : ℕ) (B : Block V) (v : V)
    (hBox : BoxOne (stateBefore x (supportCutoff S (s + 1)) v).S)
    (hFv : (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    (hBHeight : (stateBefore x (supportCutoff S (s + 1)) v).S.h_max - 1 ≤ (chainStateOf S.C B).h)
    (hBin : B ∈ (stateBefore x (supportCutoff S (s + 1)) v).S.T) :
    B ∈ viable_tree (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree ∧
      ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
        ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
            some (chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) v).Λ.sent,
            b.h = (chainStateOf S.C B).h → b.T = (chainStateOf S.C B).T_h.root)) :=
  lem61_boxOne_at S Sched x (supportCutoff S (s + 1)) B v hBox hFv hBHeight hBin

/-- `lem61_boxTwo` with `v`'s state read before a time `t_v` in place of the support cutoff of slot
`s + 1`. The proof; the audited statement is in `Statements/Executions/BoxStatements.lean`. -/
theorem lem61_boxTwo_at (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (t_v : ℕ) (B J₀ : Block V) (v : V)
    (hBox : BoxTwo (stateBefore x t_v v).S J₀)
    (hJB : J₀.AncestorEq B)
    (hBHeight : (stateBefore x t_v v).S.h_max - 1 ≤ (chainStateOf S.C B).h)
    (hLockT : ∀ T' : BlockId,
      (stateBefore x t_v v).Λ.lock
        ((stateBefore x t_v v).S.h_max - 1) = some T' →
      T' = (chainStateOf S.C B).T_h.root)
    (hBin : B ∈ (stateBefore x t_v v).S.T) :
    B ∈ viable_tree (fg_to_ac (stateBefore x t_v v).S)
        (fg_to_ac (stateBefore x t_v v).S).tree ∧
      ((stateBefore x t_v v).Λ.lock (chainStateOf S.C B).h = none ∨
        ((stateBefore x t_v v).Λ.lock (chainStateOf S.C B).h =
            some (chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (stateBefore x t_v v).Λ.sent,
            b.h = (chainStateOf S.C B).h → b.T = (chainStateOf S.C B).T_h.root)) := by
  have hShape := frameShape_of_boxTwo _ _ hBox
  have hmax := hBox.1
  by_cases hlt : (stateBefore x t_v v).S.h_j < (chainStateOf S.C B).h
  · exact frame_hypotheses_at S Sched x t_v B v _ _
      hShape hJB hBHeight hBin (Or.inl hlt)
  · -- `B`'s height is `h_max − 1`, the cache `h_j`
    have hH : (chainStateOf S.C B).h =
        (stateBefore x t_v v).S.h_max - 1 := by
      unfold Height at *
      omega
    by_cases hl : (stateBefore x t_v v).Λ.lock (chainStateOf S.C B).h = none
    · exact frame_hypotheses_at S Sched x t_v B v _ _
        hShape hJB hBHeight hBin (Or.inr (Or.inl hl))
    · obtain ⟨T', hT'⟩ := Option.ne_none_iff_exists'.1 hl
      have hTT : T' = (chainStateOf S.C B).T_h.root := hLockT T' (by rw [← hH]; exact hT')
      rw [hTT] at hT'
      exact frame_hypotheses_at S Sched x t_v B v _ _
        hShape hJB hBHeight hBin (Or.inr (Or.inr hT'))

/-- Lemma 61 in box 2. The proof; the audited statement is in
`Statements/Executions/BoxStatements.lean`.

It is the instance of `lem61_boxTwo_at` at `t_v := supportCutoff S (s + 1)`. -/
theorem lem61_boxTwo (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (s : ℕ) (B J₀ : Block V) (v : V)
    (hBox : BoxTwo (stateBefore x (supportCutoff S (s + 1)) v).S J₀)
    (hJB : J₀.AncestorEq B)
    (hBHeight : (stateBefore x (supportCutoff S (s + 1)) v).S.h_max - 1 ≤ (chainStateOf S.C B).h)
    (hLockT : ∀ T' : BlockId,
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock
        ((stateBefore x (supportCutoff S (s + 1)) v).S.h_max - 1) = some T' →
      T' = (chainStateOf S.C B).T_h.root)
    (hBin : B ∈ (stateBefore x (supportCutoff S (s + 1)) v).S.T) :
    B ∈ viable_tree (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree ∧
      ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
        ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
            some (chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) v).Λ.sent,
            b.h = (chainStateOf S.C B).h → b.T = (chainStateOf S.C B).T_h.root)) :=
  lem61_boxTwo_at S Sched x (supportCutoff S (s + 1)) B J₀ v hBox hJB hBHeight hLockT hBin

/-- `lem61_boxThree` with `v`'s state read before a time `t_v` in place of the support cutoff of
slot `s + 1`. The proof; the audited statement is in `Statements/Executions/BoxStatements.lean`. -/
theorem lem61_boxThree_at (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (t_v : ℕ) (B : Block V) (v : V)
    (hBox : BoxThree (stateBefore x t_v v).S)
    (hFv : (stateBefore x t_v v).S.F.AncestorEq B)
    (hBHeight : (stateBefore x t_v v).S.h_max ≤ (chainStateOf S.C B).h)
    (hBin : B ∈ (stateBefore x t_v v).S.T) :
    B ∈ viable_tree (fg_to_ac (stateBefore x t_v v).S)
        (fg_to_ac (stateBefore x t_v v).S).tree ∧
      ((stateBefore x t_v v).Λ.lock (chainStateOf S.C B).h = none ∨
        ((stateBefore x t_v v).Λ.lock (chainStateOf S.C B).h =
            some (chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (stateBefore x t_v v).Λ.sent,
            b.h = (chainStateOf S.C B).h → b.T = (chainStateOf S.C B).T_h.root)) := by
  obtain ⟨hmax, hShape⟩ := frameShape_of_boxThree _ hBox
  have hlt : (stateBefore x t_v v).S.h_j < (chainStateOf S.C B).h := by
    unfold Height at *
    omega
  exact frame_hypotheses_at S Sched x t_v B v _ _
    hShape hFv hBHeight hBin (Or.inl hlt)

/-- Lemma 61 in box 3. The proof; the audited statement is in
`Statements/Executions/BoxStatements.lean`.

It is the instance of `lem61_boxThree_at` at `t_v := supportCutoff S (s + 1)`. -/
theorem lem61_boxThree (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (s : ℕ) (B : Block V) (v : V)
    (hBox : BoxThree (stateBefore x (supportCutoff S (s + 1)) v).S)
    (hFv : (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    (hBHeight : (stateBefore x (supportCutoff S (s + 1)) v).S.h_max ≤ (chainStateOf S.C B).h)
    (hBin : B ∈ (stateBefore x (supportCutoff S (s + 1)) v).S.T) :
    B ∈ viable_tree (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree ∧
      ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
        ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
            some (chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) v).Λ.sent,
            b.h = (chainStateOf S.C B).h → b.T = (chainStateOf S.C B).T_h.root)) :=
  lem61_boxThree_at S Sched x (supportCutoff S (s + 1)) B v hBox hFv hBHeight hBin

end GoldilocksCorrectness.Proofs.Executions
