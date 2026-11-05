module
public import GoldilocksCorrectness.Proofs.View.Bridges
public import GoldilocksCorrectness.Proofs.Executions.Lemma89CountJ
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts

@[expose] public section

/-!

The kit, for a validator `w` with no fork-choice change over a range of times:

- `root_below_kept`: `w`'s root stays an ancestor of an honest-held block `X` and its
  `head_height_floor` at most `X`'s height;
- `frame_compat_kept`: `w`'s root stays compatible with an honest-held block `W` and its
  `head_height_floor` at most `W`'s height;
- `stepFrame_of_compat`: from those at the two reading points, `StepFrameAt` relative to every
  ancestor of `W`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (delivery_of_round dutyWindowStart_le_voteTime
  dutyWindowStart_mono dutyWindowStart_of_anchor dutyWindowStart_succ_le_slotStart one_le_Δ
  slotStart_eq slotStart_mono slot_eq_of_mem supportCutoff_eq supportCutoff_mono viewFreeze_eq
  voteTime_eq voteTime_mono voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (fc_root_eq h_j_lt_floor_of_root_F mem_fg_to_ac_tree
  mem_viable_heads_iff root_cases)

open GoldilocksCorrectness.Proofs.Routines (get_anchor_cases get_anchor_cases_locked)

open GoldilocksCorrectness.Proofs.Routines (fg_to_ac_F get_head_eq is_live_iff mem_viable_tree_iff)

open GoldilocksCorrectness.Proofs.Routines (anchorCW_eq)

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

/-! ## A validator's frame through times with no fork-choice change -/

/-- **The root stays an ancestor of an honest-held block while the fork choice does not change.**
Under unforgeability, roots naming blocks, permanent corruption and fewer than a third of the
validators in the adversary set up to `tEnd`: when `p`, honest at `tp ≤ tEnd`, holds `X` before
`tp`, and `w`'s root before `t₁` is `X` or an ancestor of `X` with its `head_height_floor` at most
`X`'s chain-state height, then the same holds before every `t₂ ≥ t₁` up to `tEnd` at which `w` is
honest, when `w` has no `ForkChoiceChangeAt` from `t₁` to before `t₂`.

Why: by induction on the time. At a step with no change, `head_height_floor` does not rise; the
root given by `get_fc_root`'s first case is an ancestor of the old root, and the root given by its
second case is the finalized block, with `h_j` less than `head_height_floor`, so less than `X`'s
height, and the finalized block is an ancestor of `X` (`F_ancestorEq_of_high`, Lemma 89a).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`, `t₁`, `tp`: the times; `w`:
  the validator; `p`: the holder of `X`; `X`: the block.

Roots name blocks until `tR`, at least `tEnd`: the conclusion is for every time `t₂` at most
`tEnd`, and the step to `t + 1` compares (`F_ancestorEq_of_high`) blocks `w` holds before `t + 1`
with `X`, held by `p` before `tp ≤ tEnd`. -/
theorem root_below_kept (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) {tR : ℕ} (hRoots : RootsNameBlocksUntil S Sched x tR)
    (tEnd t₁ tp : ℕ) (w p : V)
    (X : Block V) (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int)) (htp : tp ≤ tEnd)
    (hp : p ∉ Sched.adv (tp : Int)) (hX : X ∈ (stateBefore x tp p).S.T)
    (hr : (get_fc_root (stateBefore x t₁ w).S).AncestorEq X)
    (hf : head_height_floor (stateBefore x t₁ w).S ≤ (chainStateOf S.C X).h)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : tEnd ≤ tR) :
    ∀ t₂ : ℕ, t₁ ≤ t₂ → t₂ ≤ tEnd → w ∉ Sched.adv (t₂ : Int) →
      (∀ t : ℕ, t₁ ≤ t → t < t₂ → ¬ ForkChoiceChangeAt S Sched x w t) →
      (get_fc_root (stateBefore x t₂ w).S).AncestorEq X ∧
        head_height_floor (stateBefore x t₂ w).S ≤ (chainStateOf S.C X).h := by
  intro t₂ h12
  induction t₂, h12 using Nat.le_induction with
  | base => exact fun _ _ _ => ⟨hr, hf⟩
  | succ t h1t ih =>
    intro h2 hw hNo
    have hw' : w ∉ Sched.adv (t : Int) :=
      fun h => hw (hMono _ _ (by exact_mod_cast (Nat.le_succ t)) h)
    obtain ⟨hrt, hft⟩ := ih (by omega) hw' (fun t' h1 h2 => hNo t' h1 (by omega))
    have hnc := hNo t h1t (Nat.lt_succ_self t)
    unfold ForkChoiceChangeAt at hnc
    push Not at hnc
    obtain ⟨hroot, hfl⟩ := hnc
    have hft' : head_height_floor (stateBefore x (t + 1) w).S ≤ (chainStateOf S.C X).h :=
      le_trans hfl hft
    refine ⟨?_, hft'⟩
    rcases root_cases (stateBefore x (t + 1) w).S with ⟨hJ, hm1, -⟩ | ⟨hF, hor⟩
    · exact ancestorEq_trans (hroot hJ hm1) hrt
    · have hm := h_j_lt_h_max S Sched x (t + 1) w
      have hfj := h_j_lt_floor_of_root_F _ hm hor
      rw [hF]
      exact F_ancestorEq_of_high S Sched x hMono hU hRoots tEnd (t + 1) tp w p X hThird h2 htp hw
        hp hX (lt_of_lt_of_le hfj hft') (max_le (le_trans h2 htR) (le_trans htp htR))

/-- **The root stays compatible with an honest-held block while the fork choice does not
change.** Under `root_below_kept`'s assumptions with `W` in place of `X`: when `w`'s root before
`t₁` is compatible with `W` and its `head_height_floor` at most `W`'s chain-state height, the same
holds before every `t₂ ≥ t₁` up to `tEnd` at which `w` is honest, when `w` has no
`ForkChoiceChangeAt` from `t₁` to before `t₂`.

Why: as `root_below_kept`; a root given by `get_fc_root`'s first case is an ancestor of the old
root, so compatible with `W` when the old root is (two ancestors of one block are ordered).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`, `t₁`, `tp`: the times; `w`:
  the validator; `p`: the holder of `W`; `W`: the block.

Roots name blocks until `tR`, at least `tEnd`: the conclusion is for every time `t₂` at most
`tEnd`, and the step to `t + 1` compares (`F_ancestorEq_of_high`) blocks `w` holds before `t + 1`
with `W`, held by `p` before `tp ≤ tEnd`. -/
theorem frame_compat_kept (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) {tR : ℕ} (hRoots : RootsNameBlocksUntil S Sched x tR)
    (tEnd t₁ tp : ℕ) (w p : V)
    (W : Block V) (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int)) (htp : tp ≤ tEnd)
    (hp : p ∉ Sched.adv (tp : Int)) (hW : W ∈ (stateBefore x tp p).S.T)
    (hr : (get_fc_root (stateBefore x t₁ w).S).compatible W = true)
    (hf : head_height_floor (stateBefore x t₁ w).S ≤ (chainStateOf S.C W).h)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : tEnd ≤ tR) :
    ∀ t₂ : ℕ, t₁ ≤ t₂ → t₂ ≤ tEnd → w ∉ Sched.adv (t₂ : Int) →
      (∀ t : ℕ, t₁ ≤ t → t < t₂ → ¬ ForkChoiceChangeAt S Sched x w t) →
      (get_fc_root (stateBefore x t₂ w).S).compatible W = true ∧
        head_height_floor (stateBefore x t₂ w).S ≤ (chainStateOf S.C W).h := by
  intro t₂ h12
  induction t₂, h12 using Nat.le_induction with
  | base => exact fun _ _ _ => ⟨hr, hf⟩
  | succ t h1t ih =>
    intro h2 hw hNo
    have hw' : w ∉ Sched.adv (t : Int) :=
      fun h => hw (hMono _ _ (by exact_mod_cast (Nat.le_succ t)) h)
    obtain ⟨hrt, hft⟩ := ih (by omega) hw' (fun t' h1 h2 => hNo t' h1 (by omega))
    have hnc := hNo t h1t (Nat.lt_succ_self t)
    unfold ForkChoiceChangeAt at hnc
    push Not at hnc
    obtain ⟨hroot, hfl⟩ := hnc
    have hft' : head_height_floor (stateBefore x (t + 1) w).S ≤ (chainStateOf S.C W).h :=
      le_trans hfl hft
    refine ⟨?_, hft'⟩
    rcases root_cases (stateBefore x (t + 1) w).S with ⟨hJ, hm1, -⟩ | ⟨hF, hor⟩
    · have hle := hroot hJ hm1
      rcases (compatible_iff _ _).1 hrt with hrW | hWr
      · exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hle hrW))
      · exact (compatible_iff _ _).2 (ancestorEq_compatible hle hWr)
    · have hm := h_j_lt_h_max S Sched x (t + 1) w
      have hfj := h_j_lt_floor_of_root_F _ hm hor
      rw [hF]
      exact (compatible_iff _ _).2 (Or.inl (F_ancestorEq_of_high S Sched x hMono hU hRoots tEnd
        (t + 1) tp w p W hThird h2 htp hw hp hW (lt_of_lt_of_le hfj hft')
        (max_le (le_trans h2 htR) (le_trans htp htR))))

/-- **`StepFrameAt` from a compatible block.** When `C` is `W` or an ancestor of `W`, `w` holds `W`
before a time `th` at most the view freeze of slot `s'` and the vote time of slot `s' + 1`, `w`'s
root before the vote time of slot `s' + 1` is compatible with `W` with its `head_height_floor` at
most `W`'s height, and its root before the support cutoff of slot `s' + 2` is compatible with
`W`, then `StepFrameAt S Sched x C s' w` holds.

Why: a root compatible with `W` is compatible with `C` (both `W`'s ancestors are ordered, or `C` is
an ancestor of the root), and so is the finalized block, an ancestor of the root; when the root is
`C` or an ancestor of `C`, `W` is a viable head (held, on the root's chain and the finalized
block's, at least `head_height_floor`), in the voter tree of slot `s' + 1`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `C`, `W`: the blocks; `s'`: the slot;
  `w`: the validator; `th`: the time `w` holds `W` before. -/
theorem stepFrame_of_compat (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hDiv : TimeDiverges x.toTrace)
    (C W : Block V) (s' : ℕ) (w : V) (th : ℕ)
    (hCW : C.AncestorEq W) (hWT : W ∈ (stateBefore x th w).S.T)
    (hth : th ≤ viewFreeze S s') (hth' : th ≤ voteTime S (s' + 1))
    (hr1 : (get_fc_root (stateBefore x (voteTime S (s' + 1)) w).S).compatible W = true)
    (hf1 : head_height_floor (stateBefore x (voteTime S (s' + 1)) w).S ≤ (chainStateOf S.C W).h)
    (hr2 : (get_fc_root (stateBefore x (supportCutoff S (s' + 2)) w).S).compatible W = true) :
    StepFrameAt S Sched x C s' w := by
  have hcompatC : ∀ R : Block V, R.compatible W = true → R.compatible C = true := by
    intro R hR
    rcases (compatible_iff _ _).1 hR with hRW | hWR
    · exact (compatible_iff _ _).2 (ancestorEq_compatible hRW hCW)
    · exact (compatible_iff _ _).2 (Or.inr (ancestorEq_trans hCW hWR))
  refine ⟨by rw [fc_root_eq]; exact hcompatC _ hr1, ?_, ?_⟩
  · intro hRC tree htree
    have hRC' : (get_fc_root (stateBefore x (voteTime S (s' + 1)) w).S).AncestorEq C := by
      rw [← fc_root_eq]; exact hRC
    have hRW := ancestorEq_trans hRC' hCW
    have hFW := ancestorEq_trans (F_ancestorEq_fc_root_of_stateBefore S Sched x _ w) hRW
    have hWa : W ∈ (stateBefore x (voteTime S (s' + 1)) w).S.T :=
      (stateBefore_grows x hDiv w hth').1 hWT
    refine ⟨W, ?_, ?_, hCW⟩
    · exact mem_voter_tree_of_held S Sched x hDiv th (s' + 1) w W tree hWT
        (by rw [Nat.add_sub_cancel]; exact hth) hth' hFW htree
    · rw [mem_viable_heads_iff]
      refine ⟨hWa, hFW, by rw [fc_root_eq]; exact hRW, ?_⟩
      rw [σ_eq_of_stateBefore S Sched x _ w W hWa]
      exact hf1
  · exact GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible
      (F_ancestorEq_fc_root_of_stateBefore S Sched x _ w) (hcompatC _ hr2)

/-! ## The proposal's parent is a viable head of its proposer -/

/-- The fork-choice root is in the viable tree of the frame's tree: it is held (an ancestor of a
viable head, `frame_has_viable_head`), on the finalized block's chain, and an ancestor of that
viable head.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `p`: the validator. -/
theorem fc_root_mem_viable_tree (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (p : V) :
    (fg_to_ac (stateBefore x t p).S).fc_root ∈ viable_tree (fg_to_ac (stateBefore x t p).S)
      (fg_to_ac (stateBefore x t p).S).tree := by
  obtain ⟨W, hW⟩ := GoldilocksCorrectness.Statements.Executions.frame_has_viable_head S Sched x t p
  have hW' := (mem_viable_heads_iff _ _).1 hW
  have hrW : (get_fc_root (stateBefore x t p).S).AncestorEq W := by
    rw [← fc_root_eq]; exact hW'.2.2.1
  have hrT : get_fc_root (stateBefore x t p).S ∈ (stateBefore x t p).S.T :=
    ancestors_mem_T_of_exec S Sched x (stepBefore x t) p W _ hW'.1 hrW
  have hWtree : W ∈ (fg_to_ac (stateBefore x t p).S).tree :=
    (mem_fg_to_ac_tree _ _).2 ⟨hW'.1, hW'.2.1⟩
  have hrtree : get_fc_root (stateBefore x t p).S ∈ (fg_to_ac (stateBefore x t p).S).tree :=
    (mem_fg_to_ac_tree _ _).2 ⟨hrT, F_ancestorEq_fc_root_of_stateBefore S Sched x t p⟩
  rw [mem_viable_tree_iff, fc_root_eq]
  exact ⟨hrtree, ancestorEq_refl _, W, Finset.mem_inter.mpr ⟨hWtree, hW⟩, hrW⟩

/-- **An honest proposal's parent is a viable head of its proposer.** When `p` put `B` on the wire
at its tick at the start of slot `s + 1`, `B`'s parent is a viable head of `p`'s frame before that
start.

Why: the parent is the end of `p`'s walk (Lemma 19), which is in the viable tree, or the anchor,
which is the root or in the viable tree (`fc_root_mem_viable_tree`); a walk's end in the viable
tree is a viable head (Lemma 58).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
- `B`: the block proposed; `p`: its proposer. -/
theorem proposal_parent_viable_head (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (B : Block V) (p : V)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    B.parent ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads := by
  obtain ⟨i, hl, hsent⟩ := hPropose
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss' : slotStart S (s + 1 + 1) = slotStart S (s + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
  have hslot₁ : S.C.slot ((slotStart S (s + 1) : ℕ) : Int) = s + 1 :=
    slot_eq_of_mem S (le_refl _) (by omega)
  have hi : stepBefore x (slotStart S (s + 1)) = i := stepBefore_eq_of_lbl x hl
  obtain ⟨-, n₁', sent₁, hrun₁, hB₁⟩ := tick_send_of_honestSendAt hl hsent
  have hAp : (tickInputState x i (slotStart S (s + 1)) p).A =
      (stateBefore x (slotStart S (s + 1)) p).A := by
    rw [(tickInputState_frame x i _ p).2.1]
    unfold stateBefore
    rw [hi]
  have hSp : (tickInputState x i (slotStart S (s + 1)) p).S =
      (stateBefore x (slotStart S (s + 1)) p).S := by
    rw [(tickInputState_frame x i _ p).1]
    unfold stateBefore
    rw [hi]
  obtain ⟨-, -, -, Hp, votes_pl, support_pl, -, -, hWalkP, hBdef⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem19_tick_proposes S.C S.P S.X _ n₁' _ sent₁ B
      hrun₁ hB₁
  rw [hslot₁, Nat.add_sub_cancel, hAp, hSp] at hWalkP
  rw [hslot₁] at hBdef
  have hBpar : B.parent = Hp := by rw [hBdef]; rfl
  have hHead : get_head S.C (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) ((slotStart S (s + 1) : ℕ) : Int)
      votes_pl.toFinset support_pl.toFinset s = .ok B.parent := by
    rw [hBpar, get_head_eq]
    exact hWalkP
  have hBetween : ∀ X ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree,
      ∀ Y ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree, ∀ Z : Block V,
      X.AncestorEq Z → Z.AncestorEq Y →
        Z ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree :=
    fun X hX Y hY Z hXZ hZY => frame_path_of_exec S Sched x (stepBefore x (slotStart S (s + 1))) p
      Y Z hY (ancestorEq_trans (by rw [fg_to_ac_F]; exact ((mem_fg_to_ac_tree _ _).1 hX).2) hXZ)
      hZY
  have hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree := by
    obtain ⟨-, -, -, hor⟩ := proposal_parent_walk_end S Sched x s i B p hl hsent
    rcases hor with h | h
    · exact h
    · rw [h]
      rcases get_anchor_cases (stateBefore x (slotStart S (s + 1)) p).A
        (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
        ((slotStart S (s + 1) : ℕ) : Int) with ha | ha
      · rw [ha]
        exact fc_root_mem_viable_tree S Sched x _ p
      · exact ha
  exact GoldilocksCorrectness.Statements.Routines.lem58_walk_end_is_viable_head _ _ _ _ _ _
    _ _ (rootsNameBlocksIn_frame_of_exec_node S Sched x (stepBefore x (slotStart S (s + 1))) p)
    hBetween hHead hParentIn

/-! ## The anchor, with its lock -/

/-! ## The front's step to the slot before an opening -/

/-- **The chain at the slot before the opening, for the live locks and the confirmations before
it.** Under `FrontHyps` with `s' = m + 1 ≥ s_w + 2k − 1`: every block on the chain of a live lock a
member of `Hon m` holds before the vote time of slot `m + 1`, or of a confirmation of slot `m` a
member of `Hon (m + 1)` saved, satisfies `HonestChainExtends` at `Hon (m + 1)` at slot `m + 1`.

Why: `lem89fq_front`'s last step, kept before its conclusion: `front_locks_chain` at slot `m`,
then the phase step `lem89s_phase_step` from `m` to `m + 1`.

The variables:
- `H`: the bundle; `m`: the slot before `s'`. -/
theorem front_step_family {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST tGAT tAwakeEnd s_w s' : ℕ} {Hon : ℕ → Finset V}
    (H : FrontHyps S Sched x GST tGAT tAwakeEnd s_w s' Hon) (m : ℕ) (hm : s' = m + 1)
    (hs' : s_w + 2 * S.C.k - 1 ≤ s') :
    ∀ C : Block V, (liveLockAncestors S Sched x (Hon m) m C ∨ ∃ v ∈ Hon (m + 1), ∃ C' : Block V,
        (stateBefore x (supportCutoff S (m + 1) + 1) v).A.saved_confirmation m = some C' ∧
        C.AncestorEq C') →
      HonestChainExtends S Sched x (Hon (m + 1)) C (m + 1) := by
  subst hm
  have hk := S.C.k_ge_two
  have hb₀ : (s_w + 2 * S.C.k - 2) + 2 = s_w + 2 * S.C.k := by omega
  have hm := front_locks_chain H (s_w + 2 * S.C.k - 2) hb₀ (m - (s_w + 2 * S.C.k - 2)) (by omega)
  rw [show s_w + 2 * S.C.k - 2 + (m - (s_w + 2 * S.C.k - 2)) = m by omega] at hm
  exact (lem89s_phase_step S Sched x GST m (Hon m) (Hon (m + 1))
    (liveLockAncestors S Sched x (Hon m) m) H.hDiv H.hMono H.hSync H.hCatch
    (H.rootsAt (supportCutoff_mono S (by omega))) H.hParent H.hOwner (H.gst _ (by omega))
    (H.window m (by omega) (by omega))
    (H.window (m + 1) (by omega) le_rfl) (H.hHonMono m (by omega) (by omega))
    (H.hCommittees m (by omega) (by omega)) (H.hCommittees (m + 1) (by omega) le_rfl) hm
    (fun u hu => liveLocksOnFamilyAt_of_live S Sched x _ m u
      (fun e he hl => ⟨u, hu, e, he, hl, ancestorEq_refl e.B⟩))
    (front_step_frames H (s_w + 2 * S.C.k - 2) hb₀ m (by omega) (by omega))).1

/-! ## More of B6's context -/

namespace B6Ctx

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r s : ℕ}

/-- **A member's confirmation has a viable head of every honest frame on its chain.** At a slot
`σ` from `s − k − 1` with `σ + 2 ≤ s`, for a confirmation `X` of slot `σ` that a member `v` of slot
`σ` saved and a block `Y` that is `X` or an ancestor of `X`: every validator `p` honest at a time
`b` from one delay after the vote time of slot `σ` to the support cutoff of slot `s` has, before
`b`, a viable head of its frame that is `Y` or a descendant of `Y`.

Why: `X` has an honest committee supporter `u` (`supporter_saved`), whose vote's block `H_u` is
`X` or a descendant of `X` and an ancestor of a block `W` that `p` holds, with `p`'s root before
`b` compatible with `W` and its `head_height_floor` at most `W`'s height (`frame`). When the root
is an ancestor of `W`, `W` is a viable head; otherwise `W` is an ancestor of the root, which is an
ancestor of every viable head.

The variables:
- `C`: the context; `σ`: the slot; `v`: the member; `X`, `Y`: the blocks; `p`: the validator; `b`:
  the time. -/
theorem frameP_of_conf (C : B6Ctx S Sched x GST tGAT tAwakeEnd r s) {σ : ℕ}
    (hσ : s - S.C.k - 1 ≤ σ) (hσs : σ + 2 ≤ s) (v : V)
    (hv : v ∈ roundMembers S Sched (σ + 1)) (X Y : Block V)
    (hX : (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some X)
    (hYX : Y.AncestorEq X) (p : V) (b : ℕ) (hb1 : voteTime S σ + Δ S ≤ b)
    (hb2 : b ≤ supportCutoff S s) (hp : p ∉ Sched.adv (b : Int)) :
    ∃ W ∈ (fg_to_ac (stateBefore x b p).S).tree,
      W ∈ (fg_to_ac (stateBefore x b p).S).viable_heads ∧ Y.AncestorEq W := by
  obtain ⟨u, huA, vote, hsend, H_u, hHT, hvote, hXH⟩ := C.supporter_saved hσ hσs v hv X hX
  obtain ⟨H₁, hH₁T, hv₁, W₁, hHW₁, hW₁T, hfl₁, -, hr₁⟩ :=
    C.frame hσ hσs u huA vote hsend p b hb1 hb2 hp
  have hvs1 := voteTime_succ S σ
  have hsc1 := supportCutoff_eq S (σ + 1)
  have huvt : u ∉ Sched.adv ((voteTime S σ : ℕ) : Int) :=
    (honestActiveAt_window S Sched σ u C.hMono huA (voteTime S σ)
      (dutyWindowStart_le_voteTime S σ) (by omega)).2
  have hH : H₁ = H_u := by
    rw [hvote] at hv₁
    simp only [GoldfishVote.mk.injEq, true_and] at hv₁
    exact eq_of_root_eq_held S Sched x C.hMono C.hRoots _ u H₁ H_u huvt hH₁T hHT hv₁.symm
      (le_trans (by omega) (supportCutoff_mono S (show σ + 1 ≤ s by omega)))
  rw [hH] at hHW₁
  have hYW := ancestorEq_trans hYX (ancestorEq_trans hXH hHW₁)
  have hW₁b : W₁ ∈ (stateBefore x b p).S.T := (stateBefore_grows x C.hDiv p hb1).1 hW₁T
  rcases (compatible_iff _ _).1 hr₁ with hRW | hWR
  · have hFW := ancestorEq_trans (F_ancestorEq_fc_root_of_stateBefore S Sched x _ p) hRW
    refine ⟨W₁, (mem_fg_to_ac_tree _ _).2 ⟨hW₁b, hFW⟩, ?_, hYW⟩
    rw [mem_viable_heads_iff]
    refine ⟨hW₁b, hFW, by rw [fc_root_eq]; exact hRW, ?_⟩
    rw [σ_eq_of_stateBefore S Sched x _ p W₁ hW₁b]
    exact hfl₁
  · obtain ⟨W', hW'⟩ := GoldilocksCorrectness.Statements.Executions.frame_has_viable_head S Sched x
      b p
    have hW'' := (mem_viable_heads_iff _ _).1 hW'
    have hRW' := hW''.2.2.1
    rw [fc_root_eq] at hRW'
    exact ⟨W', (mem_fg_to_ac_tree _ _).2 ⟨hW''.1, hW''.2.1⟩, hW',
      ancestorEq_trans hYW (ancestorEq_trans hWR hRW')⟩

/-- **`rootChain` read at a time from the support cutoff of slot `σ + 1` to that of slot `σ + 2`.**
With `s = σ + 2`, every member `w` of slot `σ + 1` saved a confirmation `D` of slot `σ`, and its
root before every time `t` from the support cutoff of slot `σ + 1` to that of slot `σ + 2` is `D`
or an ancestor of `D`: every honest vote of slot `σ` extends that root (`vote_extends_root`), and
Lemma 78 at `w`. The proof is `rootChain`'s with `t` in place of the vote time of slot `σ + 2`.

The variables:
- `C`: the context; `σ`: the slot; `w`: the member; `t`: the time. -/
theorem rootChain_at (C : B6Ctx S Sched x GST tGAT tAwakeEnd r s) {σ : ℕ} (hs : s = σ + 2)
    (w : V) (hw : w ∈ Hon S Sched (σ + 1)) (t : ℕ) (ht1 : supportCutoff S (σ + 1) ≤ t)
    (ht2 : t ≤ supportCutoff S (σ + 2)) :
    ∃ D : Block V,
      (stateBefore x (supportCutoff S (σ + 1) + 1) w).A.saved_confirmation σ = some D ∧
      (get_fc_root (stateBefore x t w).S).AncestorEq D := by
  subst hs
  have hk2 := S.C.k_ge_two
  have hkk := C.hk
  have hΔ := one_le_Δ S
  have hσ : σ + 2 - S.C.k ≤ σ := by omega
  have hw' : w ∈ roundMembers S Sched (σ + 1) :=
    (roundMembers_mono S Sched (σ + 1) (σ + 2) tAwakeEnd C.hMono (Nat.le_succ _) C.tEnd).1 hw
  obtain ⟨D, hD⟩ := C.member_saves hσ le_rfl w hw'
  refine ⟨D, hD, ?_⟩
  obtain ⟨hsub, hMaj⟩ := C.members (σ := σ) (by omega) (by omega)
  have hwb : w ∉ Sched.adv ((supportCutoff S (σ + 2) : ℕ) : Int) := (Finset.mem_sdiff.1 hw).2
  have hwv : w ∉ Sched.adv ((t : ℕ) : Int) :=
    fun h => hwb (C.hMono _ _ (by exact_mod_cast ht2) h)
  have hvσ := voteTime_eq S σ
  have hsc1 := supportCutoff_eq S (σ + 1)
  have hv1 := voteTime_eq S (σ + 1)
  have hss1 : slotStart S (σ + 1) = slotStart S σ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hC1 : ∀ u ∈ S.P.committee σ ∩ roundMembers S Sched (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S σ) u).S.T,
        vote = GoldfishVote.mk u σ H_u.root ∧
        (get_fc_root (stateBefore x t w).S).AncestorEq H_u :=
    fun u hu vote hSend => C.vote_extends_root hσ le_rfl u (hsub (Finset.mem_inter.1 hu).2) vote
      hSend w t (by omega) ht2 hwv
  obtain ⟨H, hH⟩ := voters_of_votes_clause S Sched x σ
    (S.P.committee σ ∩ roundMembers S Sched (σ + 1)) _ C.hDiv C.hMono
    (fun u hu => ⟨hsub (Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hu).1⟩) hC1
  have hvA := honestActiveAt_window S Sched σ w C.hMono (hsub hw')
  have hFB : (stateBefore x (supportCutoff S (σ + 1)) w).S.F.compatible
      (get_fc_root (stateBefore x t w).S) = true :=
    (compatible_iff _ _).2 (Or.inl (ancestorEq_trans
      (stateBefore_grows x C.hDiv w ht1).2.1 (F_ancestorEq_fc_root_of_stateBefore S Sched x _ w)))
  have hGσ : GST ≤ voteTime S σ := by
    have := C.hGST
    have := C.tGAT_le
    have := slotStart_mono S (show σ + 2 - S.C.k - 1 ≤ σ by omega)
    omega
  exact lem78_update_confirmation_extends_voter_majority_chain S Sched x GST σ
    (S.P.committee σ ∩ roundMembers S Sched (σ + 1)) H _ w C.hDiv C.hMono C.hSync C.hCatch
    (C.hRoots.mono (supportCutoff_mono S (by omega))) C.hParent C.hOwner hGσ
    (fun u hu => ⟨(Finset.mem_inter.1 hu).1,
      (Finset.mem_sdiff.1 (Finset.mem_inter.1 hu).2).2, (hH u hu).1, (hH u hu).2.1,
      (hH u hu).2.2⟩)
    (counting_of_committee_majority S Sched x σ (supportCutoff S (σ + 1))
      (roundMembers S Sched (σ + 1)) w hMaj).2.1
    (fun t' h1 h2 => hvA t' (le_trans (dutyWindowStart_mono S (Nat.le_succ σ)) h1) h2) hFB D hD

end B6Ctx

/-! ## The window of an opening with no fork-choice change -/

/-- `WinCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀`: the hypotheses the window of the opening `i`
(first slot `s₀ + 1 = rs i * R ≤ r * R`) is read under: the execution assumptions and unforgeability,
every honest validator awake in the phase, fewer than a third in the adversary set, committee
sleepiness from `anchorCW S tGAT`, the honest round opening slots of the rounds `rs 0 < … < rs m` with `i ≤ m`, and no
validator outside the adversary set with a `ForkChoiceChangeAt` from the vote time of slot
`s₀ + 1 − k − 1` to before the support cutoff of slot `s₀ + 1`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `r`: the round of the action time the climb ends at; `m`: the index of the last honest round opening slot; `i`:
  the index of an honest round opening slot; `rs`: the rounds of the honest round opening slots; `s₀`: the slot before the honest round opening slot.

Roots name blocks until `supportCutoff S (s₀ + 1 + 1)`: the latest time a reader of the bundle
reads, the members' update at the action time of the opening's first slot (`base`). -/
structure WinCtx (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST tGAT tAwakeEnd r m i : ℕ) (rs : ℕ → ℕ) (s₀ : ℕ) : Prop where
  hDiv : TimeDiverges x.toTrace
  hMono : Sched.MonotoneCorruption
  hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject
  hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject
  hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s₀ + 1 + 1))
  hParent : ParentHeldAtDelivery S Sched x
  hOwner : VotesCastByOwner S Sched x
  hU : Unforgeability Vocab.goldilocks Sched x.toTrace
  hGST : GST ≤ tGAT
  hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int)
  hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
    ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int)
  hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT)
  hEnd : aR S r ≤ tAwakeEnd
  hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd
  hi : i ≤ m
  hs : rs i * S.C.R = s₀ + 1
  hrR : s₀ + 1 ≤ r * S.C.R
  hNo : ∀ (w : V) (t' : ℕ), voteTime S (s₀ + 1 - S.C.k - 1) ≤ t' →
    t' < supportCutoff S (s₀ + 1) → w ∉ Sched.adv (t' : Int) →
    ¬ ForkChoiceChangeAt S Sched x w t'

/-- `WinFam S Sched x s₀ C`: `C` is an ancestor of, or equal to, a block of the window's family at
slot `s₀`: a block on the chain of a live lock a member of `Hon S Sched (s₀ − 1)` holds before the
vote time of slot `s₀`, a member's confirmation of slot `s₀ − 1`, or a block of
`FrontFamily S Sched x (Hon S Sched s₀) s₀` (a member's live lock block or root before the vote
time of slot `s₀ + 1`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the slot; `C`: the block. -/
def WinFam (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) (s₀ : ℕ)
    (C : Block V) : Prop :=
  ∃ D : Block V, (liveLockAncestors S Sched x (Hon S Sched (s₀ - 1)) (s₀ - 1) D ∨
      (∃ v ∈ Hon S Sched (s₀ - 1 + 1), ∃ C' : Block V,
        (stateBefore x (supportCutoff S (s₀ - 1 + 1) + 1) v).A.saved_confirmation (s₀ - 1) =
          some C' ∧ D.AncestorEq C') ∨
      FrontFamily S Sched x (Hon S Sched s₀) s₀ D) ∧ C.AncestorEq D

namespace WinCtx

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r m i : ℕ} {rs : ℕ → ℕ} {s₀ : ℕ}

/-- The opening is at or after the first one. -/
theorem rs0 (C : WinCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀) :
    rs 0 * S.C.R ≤ s₀ + 1 := by
  rw [← C.hs]
  rcases Nat.eq_zero_or_pos i with h | h
  · rw [h]
  · exact Nat.mul_le_mul_right _ (r_lt_of_lt_of_mono rs m C.hSeq.mono 0 i h C.hi).le

/-- Every window from the opening on starts after the committee premise's anchor. -/
theorem win (C : WinCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀) {σ : ℕ}
    (h : s₀ + 1 ≤ σ) :
    2 * S.C.k ≤ σ ∧ anchorCW S tGAT ≤ slotStart S (σ - S.C.k - 1) := by
  have hw := window_after_anchor S Sched rs m tGAT tAwakeEnd σ C.hSeq (le_trans C.rs0 h)
  have h2 := hw.1
  have hk := S.C.k_ge_two
  exact ⟨h2, le_trans hw.2 (slotStart_mono S (by omega))⟩

/-- The support cutoff of the opening's first slot is at most `aR S r`. -/
theorem cut_le (C : WinCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀) :
    supportCutoff S (s₀ + 1) ≤ aR S r := by
  unfold aR
  have := C.hrR
  exact supportCutoff_mono S (by omega)

/-- No fork-choice change at `w` from `t₁` to before `b`, inside the window. -/
theorem noChange (C : WinCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀) (w : V) {t₁ b : ℕ}
    (h1 : voteTime S (s₀ + 1 - S.C.k - 1) ≤ t₁)
    (hb : b ≤ supportCutoff S (s₀ + 1)) (hw : w ∉ Sched.adv (b : Int)) :
    ∀ t : ℕ, t₁ ≤ t → t < b → ¬ ForkChoiceChangeAt S Sched x w t := fun t ht1 ht2 =>
  C.hNo w t (by omega) (by omega) (fun h => hw (C.hMono _ _ (by exact_mod_cast ht2.le) h))

/-- A validator honest at `b ≤ tAwakeEnd` is awake and honest at every time from `t₁ ≥ tGAT` to
`b`. -/
theorem awakeHonest (C : WinCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀) (w : V)
    {t₁ b : ℕ} (h1 : tGAT ≤ t₁) (hb : b ≤ tAwakeEnd) (hw : w ∉ Sched.adv (b : Int)) :
    ∀ t : ℕ, t₁ ≤ t → t ≤ b → w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int) := by
  intro t ht1 ht2
  have hw' : w ∉ Sched.adv (t : Int) := fun h => hw (C.hMono _ _ (by exact_mod_cast ht2) h)
  exact ⟨C.hAwake t (by omega) (by omega) w hw', hw'⟩

/-- B6's context at the window ending at the opening's first slot. -/
theorem b6 (C : WinCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀) :
    B6Ctx S Sched x GST tGAT tAwakeEnd r (s₀ + 1) := by
  have hw := C.win (le_refl (s₀ + 1))
  exact ⟨C.hDiv, C.hMono, C.hSync, C.hCatch,
    C.hRoots.mono (supportCutoff_mono S (Nat.le_succ _)), C.hParent, C.hOwner, C.hU,
    C.hGST, C.hThird, C.hAwake, C.hCommittees, C.hEnd, (by have := hw.1; omega), C.cut_le,
    le_trans hw.2 (slotStart_mono S (by omega)), C.hNo⟩

/-- The window before the opening is stable (B6, `stability_fact3`). -/
theorem stable (C : WinCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀) :
    FrontWindowStable S Sched x (Hon S Sched) (s₀ + 1 - 2 * S.C.k) (s₀ + 1 - 1) := by
  by_contra hF
  have hw := C.win (le_refl (s₀ + 1))
  obtain ⟨w, t', h1, h2, h3, h4⟩ := stability_fact3 S Sched x GST tGAT tAwakeEnd r (s₀ + 1)
    C.hDiv C.hMono C.hSync C.hCatch (C.hRoots.mono (supportCutoff_mono S (Nat.le_succ _)))
    C.hParent C.hOwner C.hU C.hGST C.hThird
    C.hAwake C.hCommittees C.hEnd (by have := hw.1; omega) C.cut_le
    (le_trans hw.2 (slotStart_mono S (by omega))) hF
  exact C.hNo w t' h1 h2 h3 h4

/-- The front's bundle for the window before the opening (`FrontHyps` with `s_w := s₀ + 1 − 2k`,
`s' := s₀`, the member sets `Hon S Sched`), with the end time the support cutoff of slot `s₀ + 1`.

Roots name blocks until `supportCutoff S s₀`: the bundle carries the premise at the support cutoff
of its slot `s' := s₀`. -/
theorem front (C : WinCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀) :
    FrontHyps S Sched x GST tGAT (supportCutoff S (s₀ + 1)) (s₀ + 1 - 2 * S.C.k) s₀
      (Hon S Sched) := by
  have hw := C.win (le_refl (s₀ + 1))
  have hk := S.C.k_ge_two
  have hEs : supportCutoff S (s₀ + 1) ≤ tAwakeEnd := le_trans C.cut_le C.hEnd
  have C6 := C.b6
  have hSt := C.stable
  rw [Nat.add_sub_cancel] at hSt
  refine ⟨C.hDiv, C.hMono, C.hSync, C.hCatch,
    C.hRoots.mono (supportCutoff_mono S (by omega)), C.hParent, C.hOwner, C.hGST,
    ?_, ?_, fun t h1 h2 => C.hAwake t h1 (le_trans h2 hEs), ?_, ?_, le_rfl, hSt.1⟩
  · intro s₁ h1 h2
    exact (roundMembers_mono S Sched (s₁ + 1) (s₁ + 1 + 1) tAwakeEnd C.hMono (Nat.le_succ _)
      (le_trans (supportCutoff_mono S (by omega)) hEs)).1
  · intro s₁ _ _ v hv
    exact (Finset.mem_sdiff.1 hv).2
  · intro s₁ h1 h2
    exact (C6.members (σ := s₁) (by omega) (by omega)).2
  · have := dutyWindowStart_of_anchor S tGAT (s₀ + 1 - 2 * S.C.k)
      (window_after_anchor S Sched rs m tGAT tAwakeEnd (s₀ + 1) C.hSeq C.rs0).2
    omega

/-- **The window's family.** For the opening's proposer `p` (honest at the support cutoff of its
slot, `HonestOpeningSeq`) and its state before the start of slot `s₀ + 1`: the chain invariant and
the lock invariant hold at slot `s₀` at `Hon S Sched s₀` for `WinFam S Sched x s₀`; the family holds
`p`'s anchor and every member's root before the vote time of slot `s₀ + 1`; and `p`'s frame has, for
every block of the family, a viable head that is that block or a descendant of it.

Why: the window is stable (B6). The front's chain step (`front_step_family`) gives the chain
invariant for the live locks of slot `s₀ − 1` and the confirmations of slot `s₀ − 1`, and
`front_of_frontWindowStable` for `FrontFamily`, with its lock invariant; ancestors inherit both.
The anchor is `p`'s root, an ancestor of `p`'s own confirmation of slot `s₀ − 1`
(`B6Ctx.rootChain_at`), or a locked block, on `p`'s confirmation of slot `s₀ − 1` or a live lock
before the vote time of slot `s₀` (`live_lock_entry_source`). A block of the family is on the chain
of a member's confirmation of a window slot (a lock is made on one, `lock_entry_confirmation`;
a member's root is on one, the window's second clause), whose honest supporter's vote gives `p` a
viable head on its chain (`B6Ctx.frameP_of_conf`).

The variables:
- `C`: the context. -/
theorem fam (C : WinCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀) :
    ChainInvFor S Sched x (Hon S Sched s₀) (WinFam S Sched x s₀) s₀ ∧
    (∀ w ∈ Hon S Sched s₀, LiveLocksOnFamilyAt S Sched x (WinFam S Sched x s₀) s₀ w) ∧
    WinFam S Sched x s₀ (get_anchor (stateBefore x (slotStart S (s₀ + 1)) (S.P.proposer (s₀ + 1))).A
      (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) (S.P.proposer (s₀ + 1))).S)
      ((slotStart S (s₀ + 1) : ℕ) : Int)) ∧
    (∀ w ∈ Hon S Sched s₀,
      WinFam S Sched x s₀ (get_fc_root (stateBefore x (voteTime S (s₀ + 1)) w).S)) ∧
    (∀ D : Block V, WinFam S Sched x s₀ D →
      ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) (S.P.proposer (s₀ + 1))).S).tree,
        W ∈ (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) (S.P.proposer (s₀ + 1))).S).viable_heads ∧
        D.AncestorEq W) := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hw0 := C.win (le_refl (s₀ + 1))
  have hEs : supportCutoff S (s₀ + 1) ≤ tAwakeEnd := le_trans C.cut_le C.hEnd
  have hss : slotStart S (s₀ + 1) = slotStart S s₀ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv0 := voteTime_eq S s₀
  have hv1 := voteTime_eq S (s₀ + 1)
  have hc1 := supportCutoff_eq S (s₀ + 1)
  have hc0 := supportCutoff_eq S s₀
  have hμ := voteTime_eq S (s₀ + 1 - S.C.k - 1)
  have hμs := slotStart_mono S (show s₀ + 1 - S.C.k - 1 ≤ s₀ - 1 by omega)
  have hss0 : slotStart S s₀ = slotStart S (s₀ - 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s₀ - 1), ← Nat.mul_add_one]
    congr 1
    omega
  have hanc := hw0.2
  rw [anchorCW_eq] at hanc
  have hGSTt := C.hGST
  set p := S.P.proposer (s₀ + 1) with hpdef
  have hpH : p ∉ Sched.adv ((supportCutoff S (s₀ + 1) : ℕ) : Int) := by
    have h := C.hSeq.honest i C.hi
    rw [C.hs] at h
    exact h
  have hpAH := C.awakeHonest p (t₁ := tGAT) le_rfl hEs hpH
  have hpb : p ∉ Sched.adv ((slotStart S (s₀ + 1) : ℕ) : Int) :=
    (hpAH _ (by omega) (by omega)).2
  have H := C.front
  have C6 := C.b6
  have hSt := C.stable
  rw [Nat.add_sub_cancel] at hSt
  have hstep := front_step_family H (s₀ - 1) (by omega) (by omega)
  have hext : ∀ D : Block V, (liveLockAncestors S Sched x (Hon S Sched (s₀ - 1)) (s₀ - 1) D ∨
      ∃ v ∈ Hon S Sched (s₀ - 1 + 1), ∃ C' : Block V,
        (stateBefore x (supportCutoff S (s₀ - 1 + 1) + 1) v).A.saved_confirmation (s₀ - 1) =
          some C' ∧ D.AncestorEq C') →
      HonestChainExtends S Sched x (Hon S Sched s₀) D s₀ := by
    intro D hD
    have h := hstep D hD
    rwa [show s₀ - 1 + 1 = s₀ by omega] at h
  obtain ⟨hFF, hFL⟩ := front_of_frontWindowStable S Sched x GST tGAT tAwakeEnd (s₀ + 1) (Hon S Sched)
    C.hDiv C.hMono C.hSync C.hCatch
    (C.hRoots.mono (supportCutoff_mono S (by omega))) C.hParent C.hOwner C.hGST hw0.1
    H.hHonMono H.hHon C.hAwake H.hCommittees H.hsw (by rw [Nat.add_sub_cancel]; exact hEs)
    (by rw [Nat.add_sub_cancel]; exact C.stable)
  rw [Nat.add_sub_cancel] at hFF hFL
  have hmem : ∀ a b : ℕ, a ≤ b → b ≤ s₀ + 1 → ∀ u ∈ roundMembers S Sched b,
      u ∈ roundMembers S Sched a := fun a b hab hb u hu =>
    (roundMembers_mono S Sched a b tAwakeEnd C.hMono hab
      (le_trans (supportCutoff_mono S hb) hEs)).1 hu
  have hpHon : ∀ a : ℕ, a ≤ s₀ + 1 → p ∈ roundMembers S Sched a := fun a ha =>
    Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun h => hpH (C.hMono _ _
      (by exact_mod_cast supportCutoff_mono S ha) h)⟩
  -- the frame of `p` on the chain of a member's confirmation
  have hFrameConf : ∀ (σ : ℕ) (v : V) (X Y : Block V), s₀ + 1 - S.C.k - 1 ≤ σ →
      σ + 2 ≤ s₀ + 1 → v ∈ roundMembers S Sched (σ + 1) →
      (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some X →
      Y.AncestorEq X →
      ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) p).S).tree,
        W ∈ (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) p).S).viable_heads ∧
          Y.AncestorEq W := by
    intro σ v X Y h1 h2 hv hX hYX
    have hvσ := voteTime_eq S σ
    have hsσ := slotStart_mono S (show σ + 2 ≤ s₀ + 1 from h2)
    have hss' : slotStart S (σ + 2) = slotStart S σ + 8 * Δ S := by
      rw [slotStart_eq, slotStart_eq S σ, Nat.mul_add]
      omega
    exact C6.frameP_of_conf (σ := σ) h1 h2 v hv X Y hX hYX p (slotStart S (s₀ + 1))
      (by omega) (by omega) hpb
  -- the frame of `p` on the chain of a live lock at a time `t` from the vote time of slot `s₀`
  -- to the start of slot `s₀ + 1`
  have hFrameLock : ∀ (t : ℕ) (u : V) (e : LockEntry V) (Y : Block V),
      voteTime S s₀ ≤ t → t ≤ slotStart S (s₀ + 1) → u ∈ roundMembers S Sched s₀ →
      e ∈ (stateBefore x t u).A.lock_entries → ((t : ℕ) : Int) < e.d → Y.AncestorEq e.B →
      ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) p).S).tree,
        W ∈ (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) p).S).viable_heads ∧
          Y.AncestorEq W := by
    intro t u e Y ht1 ht2 hu he hlive hYe
    obtain ⟨σ, hd, hcut, C', hsv, heC'⟩ := lock_entry_confirmation S Sched x t u e C.hDiv he
    have hσlo : s₀ - S.C.k ≤ σ :=
      GoldilocksCorrectness.Statements.Executions.lem41_slot_of_live_entry S
        (s₀ - S.C.k) σ t e hd hlive (le_trans (voteTime_mono S (by omega)) ht1)
    have hσhi : σ + 2 ≤ s₀ + 1 := by
      by_contra h
      have hm := slotStart_mono S (show s₀ + 1 ≤ σ + 1 by omega)
      have h2' := supportCutoff_eq S (σ + 1)
      have h3' := voteTime_eq S (σ + 1)
      omega
    have huσ : u ∈ roundMembers S Sched (σ + 1) :=
      hmem (σ + 1) s₀ (by omega) (by omega) u hu
    exact hFrameConf σ u C' Y (by omega) hσhi huσ hsv (ancestorEq_trans hYe heC')
  -- the frame of `p` on the chain of every block of the hstep family and of `FrontFamily`
  have hFrameDom : ∀ D : Block V, (liveLockAncestors S Sched x (Hon S Sched (s₀ - 1)) (s₀ - 1) D ∨
      (∃ v ∈ Hon S Sched (s₀ - 1 + 1), ∃ C' : Block V,
        (stateBefore x (supportCutoff S (s₀ - 1 + 1) + 1) v).A.saved_confirmation (s₀ - 1) =
          some C' ∧ D.AncestorEq C') ∨
      FrontFamily S Sched x (Hon S Sched s₀) s₀ D) →
      ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) p).S).tree,
        W ∈ (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) p).S).viable_heads ∧
          D.AncestorEq W := by
    intro D hD
    rcases hD with ⟨u, hu, e, he, hl, hDe⟩ | ⟨v, hv, C', hC', hDC'⟩ | hF
    · have hl' := hl
      rw [is_live_iff] at hl'
      rw [show s₀ - 1 + 1 = s₀ by omega] at he hl'
      have hu' : u ∈ roundMembers S Sched s₀ := by
        have h := hu
        simp only [Hon] at h
        rwa [show s₀ - 1 + 1 = s₀ by omega] at h
      exact hFrameLock (voteTime S s₀) u e D le_rfl (by omega) hu' he hl'.1 hDe
    · rw [show s₀ - 1 + 1 = s₀ by omega] at hv hC'
      exact hFrameConf (s₀ - 1) v C' D (by omega) (by omega)
        (by rw [show s₀ - 1 + 1 = s₀ by omega]; exact hmem s₀ (s₀ + 1) (by omega) le_rfl v hv)
        (by rw [show s₀ - 1 + 1 = s₀ by omega]; exact hC') hDC'
    · rcases hF with ⟨u, hu, e, he, hl, rfl⟩ | ⟨w', hw', rfl⟩
      · have hl' := hl
        rw [is_live_iff] at hl'
        obtain ⟨σ, hd, hcut, C', hsv, heC'⟩ := lock_entry_confirmation S Sched x _ u e C.hDiv he
        have hσlo : s₀ + 1 - S.C.k ≤ σ :=
          GoldilocksCorrectness.Statements.Executions.lem41_slot_of_live_entry S
            (s₀ + 1 - S.C.k) σ (voteTime S (s₀ + 1)) e hd hl'.1 (voteTime_mono S (by omega))
        have hσhi : σ + 2 ≤ s₀ + 1 := by
          by_contra h
          have hm := slotStart_mono S (show s₀ + 1 ≤ σ + 1 by omega)
          have h2' := supportCutoff_eq S (σ + 1)
          have h3' := voteTime_eq S (σ + 1)
          omega
        exact hFrameConf σ u C' e.B (by omega) hσhi (hmem (σ + 1) (s₀ + 1) (by omega) le_rfl u hu)
          hsv heC'
      · obtain ⟨D, hDc, hRD⟩ := hSt.2 w' hw'
        rcases hDc with ⟨u, hu, e, he, hl, rfl⟩ | ⟨v, hv, hconf⟩
        · have hl' := hl
          rw [is_live_iff] at hl'
          obtain ⟨σ, hd, hcut, C', hsv, heC'⟩ := lock_entry_confirmation S Sched x _ u e C.hDiv he
          have hσlo : s₀ + 1 - S.C.k ≤ σ :=
            GoldilocksCorrectness.Statements.Executions.lem41_slot_of_live_entry S
              (s₀ + 1 - S.C.k) σ (voteTime S (s₀ + 1)) e hd hl'.1 (voteTime_mono S (by omega))
          have hσhi : σ + 2 ≤ s₀ + 1 := by
            by_contra h
            have hm := slotStart_mono S (show s₀ + 1 ≤ σ + 1 by omega)
            have h2' := supportCutoff_eq S (σ + 1)
            have h3' := voteTime_eq S (σ + 1)
            omega
          exact hFrameConf σ u C' _ (by omega) hσhi
            (hmem (σ + 1) (s₀ + 1) (by omega) le_rfl u hu) hsv (ancestorEq_trans hRD heC')
        · exact hFrameConf (s₀ - 1) v D _ (by omega) (by omega)
            (by rw [show s₀ - 1 + 1 = s₀ by omega]; exact hmem s₀ (s₀ + 1) (by omega) le_rfl v hv)
            (by rw [show s₀ - 1 + 1 = s₀ by omega]; exact hconf) hRD
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the chain invariant
    rintro D ⟨D', hD', hDD'⟩
    refine honestChainExtends_of_ancestorEq S Sched x _ D' D s₀ hDD' ?_
    rcases hD' with h | h | h
    · exact hext D' (Or.inl h)
    · exact hext D' (Or.inr h)
    · exact hFF D' h
  · -- the lock invariant
    intro w hw A' hR e he hl
    obtain ⟨D, hD, heD⟩ := hFL w hw A' hR e he hl
    exact ⟨D, ⟨D, Or.inr (Or.inr hD), ancestorEq_refl D⟩, heD⟩
  · -- the anchor
    rcases get_anchor_cases_locked (stateBefore x (slotStart S (s₀ + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) p).S)
      ((slotStart S (s₀ + 1) : ℕ) : Int) with ha | ⟨hVT, e, he, hl, hAe⟩
    · rw [ha]
      have hp' : p ∈ Hon S Sched (s₀ - 1 + 1) := by
        rw [show s₀ - 1 + 1 = s₀ by omega]
        exact hpHon (s₀ + 1) le_rfl
      obtain ⟨D, hD, hRD⟩ := C6.rootChain_at (σ := s₀ - 1) (by omega) p hp'
        (slotStart S (s₀ + 1)) (by rw [show s₀ - 1 + 1 = s₀ by omega]; omega)
        (by rw [show s₀ - 1 + 2 = s₀ + 1 by omega]; omega)
      exact ⟨D, Or.inr (Or.inl ⟨p, hp', D, hD, ancestorEq_refl D⟩),
        by rw [fc_root_eq]; exact hRD⟩
    · have hl' := hl
      rw [is_live_iff] at hl'
      have hdw : tGAT ≤ dutyWindowStart S (s₀ - 1 + 1) := by
        rw [show s₀ - 1 + 1 = s₀ by omega]
        have := dutyWindowStart_of_anchor S tGAT s₀
          (le_trans hw0.2 (slotStart_mono S (by omega)))
        omega
      rcases live_lock_entry_source S Sched x (s₀ - 1) (slotStart S (s₀ + 1)) p C.hDiv
          (fun t h1' h2' => hpAH t (by have := dutyWindowStart_mono S (show (s₀ - 1) + 1 ≤ (s₀ - 1) + 2 by omega); omega) (by omega))
          (by rw [show s₀ - 1 + 1 = s₀ by omega]; omega)
          (by rw [show s₀ - 1 + 2 = s₀ + 1 by omega]; omega) e he hl'.1 with
        ⟨C', hC', heC'⟩ | ⟨A₃, hR₃, e', he', hl₃, hee'⟩
      · exact ⟨e.B, Or.inr (Or.inl ⟨p, hpHon _ (by omega), C', hC', heC'⟩), hAe⟩
      · obtain ⟨e₁, he₁, hl₁, -, he'₁, -⟩ :=
          GoldilocksCorrectness.Statements.Routines.lem38_revoke_locks_entries_moved S.P _ A₃ _ _
            (s₀ - 1 + 1) (Nat.le_add_left 1 _) hR₃ e' he'
        exact ⟨e₁.B, Or.inl ⟨p, hpHon _ (by omega), e₁, (Finset.mem_filter.1 he₁).1, hl₁,
          ancestorEq_refl _⟩, ancestorEq_trans hAe (ancestorEq_trans hee' he'₁)⟩
  · -- the members' roots
    intro w hw
    exact ⟨_, Or.inr (Or.inr (Or.inr ⟨w, hw, rfl⟩)), ancestorEq_refl _⟩
  · -- the proposer's frame
    rintro D ⟨D', hD', hDD'⟩
    obtain ⟨W, hWt, hWv, hD'W⟩ := hFrameDom D' hD'
    exact ⟨W, hWt, hWv, ancestorEq_trans hDD' hD'W⟩

/-- **The window's family is on the chain of the proposal's parent.** Every block of
`WinFam S Sched x s₀` is `B.parent` or an ancestor of it, for the opening's proposal `B`
(`family_ancestorEq_proposal_parent`, with the honest committee votes of slot `s₀` and `fam`).

The variables:
- `C`: the context; `B`: the proposal. -/
theorem fam_parent (C : WinCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀) (B : Block V)
    (hB : ProposalAt S Sched x (s₀ + 1) B) :
    ∀ D : Block V, WinFam S Sched x s₀ D → D.AncestorEq B.parent := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hw0 := C.win (le_refl (s₀ + 1))
  have hEs : supportCutoff S (s₀ + 1) ≤ tAwakeEnd := le_trans C.cut_le C.hEnd
  have hss : slotStart S (s₀ + 1) = slotStart S s₀ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv0 := voteTime_eq S s₀
  have hc1 := supportCutoff_eq S (s₀ + 1)
  have hc0 := supportCutoff_eq S s₀
  have hv1 := voteTime_eq S (s₀ + 1)
  have hμs := slotStart_mono S (show s₀ + 1 - S.C.k - 1 ≤ s₀ by omega)
  have hanc := hw0.2
  rw [anchorCW_eq] at hanc
  have hGSTt := C.hGST
  set p := S.P.proposer (s₀ + 1) with hpdef
  have hpH : p ∉ Sched.adv ((supportCutoff S (s₀ + 1) : ℕ) : Int) := by
    have h := C.hSeq.honest i C.hi
    rw [C.hs] at h
    exact h
  have hpAH := C.awakeHonest p (t₁ := tGAT) le_rfl hEs hpH
  have H := C.front
  have hVot := H.voters s₀ (by omega) le_rfl
  have hMaj := (C.b6.members (σ := s₀) (by omega) (by omega)).2
  obtain ⟨hChain, -, hAnchor, -, hFrameP⟩ := C.fam
  exact family_ancestorEq_proposal_parent S Sched x GST s₀ (S.P.committee s₀ ∩ Hon S Sched s₀)
    (WinFam S Sched x s₀) B p C.hDiv C.hMono C.hSync C.hCatch
    (C.hRoots.mono (supportCutoff_mono S (by omega))) C.hParent C.hOwner
    (by omega)
    (fun u hu => by
      obtain ⟨huH, hK, vote, -, -, i', hl', hs'⟩ := hVot u hu
      refine ⟨hK, ?_, vote, i', hl', hs'⟩
      have hb := (Finset.mem_sdiff.1 huH).2
      exact fun h => hb (C.hMono _ _ (by exact_mod_cast (show slotStart S (s₀ + 1) ≤
        supportCutoff S (s₀ + 1) by omega)) h))
    (fun D hD u hu vote hs => (hChain D hD).1 u (Finset.mem_inter.1 hu).2 vote hs)
    (counting_of_committee_majority S Sched x s₀ (slotStart S (s₀ + 1)) (Hon S Sched s₀) p
      hMaj).2.1
    (fun t h1 h2 => hpAH t (by omega) (by omega)) hB hFrameP hAnchor

/-- **The round's first clause, read on the window.** Before the vote time of the opening's first
slot `s₀ + 1`, every member `w` of `Hon S Sched (s₀ + 1)` has its root `B.parent` or an ancestor of
it (its root is in the window's family, `fam_parent`), and its `head_height_floor` at most
`B.parent`'s height (`B.parent` is a viable head of the proposer, `floor_le_of_viable`, and
`head_height_floor` (the least chain-state height a viable block may have) does not rise until the vote time).

The variables:
- `C`: the context; `B`: the proposal. -/
theorem clause1 (C : WinCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀) (B : Block V)
    (hB : ProposalAt S Sched x (s₀ + 1) B) :
    ∀ w ∈ Hon S Sched (s₀ + 1),
      (get_fc_root (stateBefore x (voteTime S (s₀ + 1)) w).S).AncestorEq B.parent ∧
      head_height_floor (stateBefore x (voteTime S (s₀ + 1)) w).S ≤
        (chainStateOf S.C B.parent).h := by
  intro w hw
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hw0 := C.win (le_refl (s₀ + 1))
  have hEs : supportCutoff S (s₀ + 1) ≤ tAwakeEnd := le_trans C.cut_le C.hEnd
  have hss : slotStart S (s₀ + 1) = slotStart S s₀ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv1 := voteTime_eq S (s₀ + 1)
  have hc1 := supportCutoff_eq S (s₀ + 1)
  have hμ := voteTime_eq S (s₀ + 1 - S.C.k - 1)
  have hμs := slotStart_mono S (show s₀ + 1 - S.C.k - 1 ≤ s₀ by omega)
  have hanc := hw0.2
  rw [anchorCW_eq] at hanc
  have hGSTt := C.hGST
  set p := S.P.proposer (s₀ + 1) with hpdef
  have hpH : p ∉ Sched.adv ((supportCutoff S (s₀ + 1) : ℕ) : Int) := by
    have h := C.hSeq.honest i C.hi
    rw [C.hs] at h
    exact h
  have hpAH := C.awakeHonest p (t₁ := tGAT) le_rfl hEs hpH
  have hEs2 : supportCutoff S (s₀ + 1 + 1) ≤ tAwakeEnd :=
    le_trans (by unfold aR; exact supportCutoff_mono S (by have := C.hrR; omega)) C.hEnd
  have hws₀ : w ∈ Hon S Sched s₀ :=
    (roundMembers_mono S Sched (s₀ + 1) (s₀ + 1 + 1) tAwakeEnd C.hMono (Nat.le_succ _) hEs2).1 hw
  obtain ⟨-, -, -, hRoot, -⟩ := C.fam
  refine ⟨C.fam_parent B hB _ (hRoot w hws₀), ?_⟩
  have hwb : w ∉ Sched.adv ((supportCutoff S (s₀ + 1 + 1) : ℕ) : Int) := (Finset.mem_sdiff.1 hw).2
  have hwv : w ∉ Sched.adv ((voteTime S (s₀ + 1) : ℕ) : Int) :=
    fun h => hwb (C.hMono _ _ (by exact_mod_cast (le_trans (show voteTime S (s₀ + 1) ≤
      supportCutoff S (s₀ + 1) by omega) (supportCutoff_mono S (Nat.le_succ _)))) h)
  have hPV := proposal_parent_viable_head S Sched x s₀ B p hB
  have e1 : slotStart S (s₀ + 1) - Δ S + Δ S = slotStart S (s₀ + 1) := by omega
  have hfl := floor_le_of_viable S Sched x GST C.hDiv C.hMono C.hSync C.hCatch C.hRoots
    C.hParent C.hU tAwakeEnd (slotStart S (s₀ + 1) - Δ S) w p B.parent C.hThird (by omega)
    (by omega) (fun h => hwv (C.hMono _ _ (by exact_mod_cast (show slotStart S (s₀ + 1) - Δ S ≤
      voteTime S (s₀ + 1) by omega)) h))
    (fun t' h1 h2 => hpAH t' (by omega) (by omega)) (by rw [e1]; exact hPV)
    (le_trans (by omega) (supportCutoff_mono S (Nat.le_succ _)))
  have hnf := floor_le_of_no_change S Sched x w (slotStart S (s₀ + 1) - Δ S) (voteTime S (s₀ + 1))
    (by omega) (C.noChange w (by omega) (by omega) hwv)
  exact le_trans hnf hfl

end WinCtx

/-! ## The round's base at the opening's first slot -/

namespace WinCtx

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r m i : ℕ} {rs : ℕ → ℕ} {s₀ : ℕ}

/-- **The round's base at the opening's first slot.** For the opening's proposal `B`, when no
opening's proposal collides with a block its proposer held and every member of
`Hon S Sched (s₀ + 1)` has its root before the action time `supportCutoff S (s₀ + 2)` on `B`'s
chain: every member holds `B` before the vote time of slot `s₀ + 1`, the chain invariant relative
to `B` holds at slot `s₀ + 1` at `Hon S Sched (s₀ + 1)`, and every member's update at the action
time saves `B` as its confirmation of slot `s₀ + 1` with `B` among its fast blocks
(`round_base_steps`, with the window's family, `fam` and `fam_parent`, the first clause and
`head_height_floor` at the proposer one delay before).

The variables:
- `C`: the context; `B`: the proposal. -/
theorem base (C : WinCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀)
    (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m) (B : Block V)
    (hB : ProposalAt S Sched x (s₀ + 1) B)
    (hRootAr : ∀ v ∈ Hon S Sched (s₀ + 1),
      (get_fc_root (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S).AncestorEq B) :
    (∀ u ∈ Hon S Sched (s₀ + 1), B ∈ (stateBefore x (voteTime S (s₀ + 1)) u).S.T) ∧
    HonestChainExtends S Sched x (Hon S Sched (s₀ + 1)) B (s₀ + 1) ∧
    ∀ v ∈ Hon S Sched (s₀ + 1), ∃ A' : ACState V,
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).A
          ((supportCutoff S (s₀ + 1 + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S)
        ((supportCutoff S (s₀ + 1 + 1) : ℕ) : Int) (s₀ + 1 + 1) = .ok A' ∧
      A'.saved_confirmation (s₀ + 1) = some B ∧ B ∈ A'.fast_blocks := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hw0 := C.win (le_refl (s₀ + 1))
  have hEs : supportCutoff S (s₀ + 1) ≤ tAwakeEnd := le_trans C.cut_le C.hEnd
  have hEs2 : supportCutoff S (s₀ + 1 + 1) ≤ tAwakeEnd :=
    le_trans (by unfold aR; exact supportCutoff_mono S (by have := C.hrR; omega)) C.hEnd
  have hss : slotStart S (s₀ + 1) = slotStart S s₀ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss1 : slotStart S (s₀ + 1 + 1) = slotStart S (s₀ + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s₀ + 1), Nat.mul_add, Nat.mul_one]
  have hv0 := voteTime_eq S s₀
  have hv1 := voteTime_eq S (s₀ + 1)
  have hv2 := voteTime_eq S (s₀ + 1 + 1)
  have hc1 := supportCutoff_eq S (s₀ + 1)
  have hc2 := supportCutoff_eq S (s₀ + 1 + 1)
  have hc0 := supportCutoff_eq S s₀
  have hdws0 := dutyWindowStart_succ_le_slotStart S s₀
  have hdws1 := dutyWindowStart_succ_le_slotStart S (s₀ + 1)
  have hdwm := dutyWindowStart_mono S (Nat.le_succ (s₀ + 1))
  have hA1 : anchorCW S tGAT ≤ slotStart S (s₀ + 1) :=
    le_trans hw0.2 (slotStart_mono S (by omega))
  have hA2 : anchorCW S tGAT ≤ slotStart S (s₀ + 1 + 1) :=
    le_trans hw0.2 (slotStart_mono S (by omega))
  have hdw0 := dutyWindowStart_of_anchor S tGAT s₀ hA1
  have hdw1 := dutyWindowStart_of_anchor S tGAT (s₀ + 1) hA2
  have hGSTt := C.hGST
  set p := S.P.proposer (s₀ + 1) with hpdef
  have hpH : p ∉ Sched.adv ((supportCutoff S (s₀ + 1) : ℕ) : Int) := by
    have h := C.hSeq.honest i C.hi
    rw [C.hs] at h
    exact h
  have hpAH := C.awakeHonest p (t₁ := tGAT) le_rfl hEs hpH
  have hpb : p ∉ Sched.adv ((slotStart S (s₀ + 1) : ℕ) : Int) :=
    (hpAH _ (by omega) (by omega)).2
  have hp' : ∀ t : ℕ, voteTime S s₀ ≤ t → t ≤ slotStart S (s₀ + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int) :=
    fun t h1 h2 => hpAH t (by omega) (by omega)
  have hpHon : HonestThroughTime Sched ((voteTime S (s₀ + 1) : ℕ) : Int) p := fun t' ht' h =>
    hpH (C.hMono _ _ (le_trans ht' (by exact_mod_cast (show voteTime S (s₀ + 1) ≤
      supportCutoff S (s₀ + 1) by omega))) h)
  -- the members' windows
  have hHonW : ∀ v ∈ Hon S Sched (s₀ + 1), ∀ t : ℕ, dutyWindowStart S (s₀ + 1) ≤ t →
      t ≤ supportCutoff S (s₀ + 1 + 1) → v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int) :=
    fun v hv t h1 h2 => C.awakeHonest v (t₁ := tGAT) le_rfl hEs2 (Finset.mem_sdiff.1 hv).2 t
      (by omega) h2
  -- the voters of the slots `s₀` and `s₀ + 1`
  have hMaj0 := committee_majority_of_committeeSleepiness S Sched _ s₀ C.hCommittees hA1
  have hMaj1 := committee_majority_of_committeeSleepiness S Sched _ (s₀ + 1) C.hCommittees hA2
  have H := C.front
  have hVot0 := H.voters s₀ (by omega) le_rfl
  have hVot1 : ∀ u ∈ S.P.committee (s₀ + 1) ∩ Hon S Sched (s₀ + 1), u ∈ Hon S Sched (s₀ + 1) ∧
      u ∈ S.P.committee (s₀ + 1) ∧ ∃ vote : GoldfishVote V, vote.val_index = u ∧
        vote.slot = s₀ + 1 ∧ ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s₀ + 1)) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent := by
    intro u hu
    obtain ⟨hK, huH⟩ := Finset.mem_inter.1 hu
    obtain ⟨i', vote, hl, hvi, hvs, hsent⟩ := honest_votes_of_window S Sched x (s₀ + 1) u C.hDiv
      C.hMono (fun t h1 h2 => (hHonW u huH t h1 (by omega)).1)
      (hHonW u huH _ (dutyWindowStart_le_voteTime S (s₀ + 1)) (by omega)).2 hK
    exact ⟨huH, hK, vote, hvi, hvs, i', hl, hsent⟩
  -- the family
  obtain ⟨hChain, hLocks, hAnchor, -, -⟩ := C.fam
  have hFamPar := C.fam_parent B hB
  have hcl1 := C.clause1 B hB
  set anchor := get_anchor (stateBefore x (slotStart S (s₀ + 1)) p).A
    (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) p).S) ((slotStart S (s₀ + 1) : ℕ) : Int)
    with hanchor
  set Hs0 : Finset V := S.P.committee s₀ ∩ Hon S Sched s₀ with hHs0
  have hex : ∀ u ∈ Hs0, ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s₀) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s₀ H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H_u ∈ (stateBefore x (voteTime S s₀) u).S.T ∧ anchor.AncestorEq H_u := by
    intro u hu
    obtain ⟨huH, -, vote, -, -, i', hl, hsent⟩ := hVot0 u hu
    obtain ⟨H_u, hT, hvt, hAH⟩ := (hChain anchor hAnchor).1 u huH vote ⟨i', hl, hsent⟩
    subst hvt
    exact ⟨H_u, ⟨i', hl, hsent⟩, hT, hAH⟩
  choose Hc hHc using hex
  let Hf : V → Block V := fun u => if h : u ∈ Hs0 then Hc u h else B
  have hHf : ∀ u (hu : u ∈ Hs0), Hf u = Hc u hu := fun u hu => dif_pos hu
  have hHsPrev : ∀ u ∈ Hs0, u ∈ S.P.committee (s₀ + 1 - 1) ∧
      u ∉ Sched.adv (voteTime S (s₀ + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s₀ + 1 - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s₀ + 1 - 1) (Hf u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      Hf u ∈ (stateBefore x (voteTime S (s₀ + 1 - 1)) u).S.T ∧ anchor.AncestorEq (Hf u) := by
    intro u hu
    rw [Nat.add_sub_cancel]
    obtain ⟨huH, hK, -⟩ := hVot0 u hu
    rw [hHf u hu]
    refine ⟨hK, ?_, (hHc u hu).1, (hHc u hu).2.1, (hHc u hu).2.2⟩
    have hb := (Finset.mem_sdiff.1 huH).2
    exact fun h => hb (C.hMono _ _ (by exact_mod_cast (show voteTime S (s₀ + 1) ≤
      supportCutoff S (s₀ + 1) by omega)) h)
  have hmem01 : ∀ w ∈ Hon S Sched (s₀ + 1), w ∈ Hon S Sched s₀ := fun w hw =>
    (roundMembers_mono S Sched (s₀ + 1) (s₀ + 1 + 1) tAwakeEnd C.hMono (Nat.le_succ _) hEs2).1 hw
  have hLocksW : ∀ w ∈ Hon S Sched (s₀ + 1), ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s₀ + 1)) w).A
        ((voteTime S (s₀ + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s₀ + 1)) w).S)
        ((voteTime S (s₀ + 1) : ℕ) : Int) (s₀ + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s₀ + 1)) w).S)
          ((voteTime S (s₀ + 1) : ℕ) : Int) e = true → e.B.AncestorEq B.parent := by
    intro w hw A' hR e he hl
    obtain ⟨D, hD, heD⟩ := hLocks w (hmem01 w hw) A' hR e he hl
    exact ancestorEq_trans heD (hFamPar D hD)
  have hOnly : ∀ w ∈ Hon S Sched (s₀ + 1), ∀ B₁ ∈ (stateBefore x (voteTime S (s₀ + 1)) w).S.T,
      B₁.slot = s₀ + 1 → B₁ = B :=
    fun w _ B₁ hB₁ hslot => only_block_of_unforgeability S Sched x C.hU (s₀ + 1)
      (voteTime S (s₀ + 1)) B B₁ p w hpHon rfl hB hB₁ hslot
  have hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S (s₀ + 1)) p).S.T, B₁.root ≠ B.root := by
    intro B₁ hB₁ heq
    apply hNoCol
    rw [GoldilocksCorrectness.Proofs.View.rootCollisionAtOpening_unfold]
    refine ⟨i, C.hi, B, ?_, ?_⟩
    · rw [C.hs]
      exact hB
    · rw [C.hs]
      exact ⟨B₁, hB₁, heq⟩
  have hFloorW : ∀ w ∈ Hon S Sched (s₀ + 1),
      head_height_floor (stateBefore x (slotStart S (s₀ + 1)) p).S ≤
        head_height_floor (stateBefore x (voteTime S (s₀ + 1)) w).S ∧
      head_height_floor (stateBefore x (voteTime S (s₀ + 1)) w).S ≤
        (chainStateOf S.C B.parent).h := by
    intro w hw
    refine ⟨?_, (hcl1 w hw).2⟩
    have hfl := floor_le_of_delivery_unordered S Sched x GST (slotStart S (s₀ + 1)) p w C.hDiv
      C.hMono C.hSync C.hCatch
      (C.hRoots.mono (le_trans (by omega) (supportCutoff_mono S (Nat.le_succ _)))) C.hParent C.hU
      (adversaryFewerThanThirdUntil_of_le (by exact_mod_cast (show slotStart S (s₀ + 1) + Δ S ≤
        tAwakeEnd by omega)) C.hThird) (by omega) hpb
      (fun t' h1' h2' => hHonW w hw t' (by omega) (by omega))
    rw [← hv1] at hfl
    exact hfl
  have hHeadP := anchor_has_viable_head S Sched x (slotStart S (s₀ + 1)) p
    (stateBefore x (slotStart S (s₀ + 1)) p).A ((slotStart S (s₀ + 1) : ℕ) : Int)
  exact round_base_steps S Sched x GST (s₀ + 1) (Hon S Sched (s₀ + 1))
    (S.P.committee (s₀ + 1) ∩ Hon S Sched (s₀ + 1)) Hs0 Hf anchor B p _
    (fun w => head_height_floor (stateBefore x (voteTime S (s₀ + 1)) w).S)
    (fun v => head_height_floor (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S)
    (get_fc_root (stateBefore x (slotStart S (s₀ + 1)) p).S)
    (fun w => get_fc_root (stateBefore x (voteTime S (s₀ + 1)) w).S)
    (fun v => get_fc_root (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S)
    C.hDiv C.hMono C.hSync C.hCatch C.hRoots C.hParent C.hOwner (by omega)
    (by rw [Nat.add_sub_cancel]; omega) hHonW (by rw [Nat.add_sub_cancel]; exact hp') hB
    hHsPrev (fun w _ => (counting_of_committee_majority S Sched x s₀ (voteTime S (s₀ + 1))
      (Hon S Sched s₀) w hMaj0).2.2) (ancestorEq_refl _) hLocksW hOnly hRootNew hVot1
    (fun v _ => (counting_of_committee_majority S Sched x (s₀ + 1) (supportCutoff S (s₀ + 1 + 1))
      (Hon S Sched (s₀ + 1)) v hMaj1).2.1)
    (counting_of_committee_majority S Sched x (s₀ + 1) 0 (Hon S Sched (s₀ + 1)) p hMaj1).1
    ⟨rfl, rfl⟩ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hFloorW
    (fun w hw => (hcl1 w hw).1) hRootAr hHeadP

end WinCtx

/-! ## The context of an opening with no fork-choice change -/

omit [RootOrder] in
/-- **Consecutive honest round opening slots are at least one round apart.** For `i < m`, the first
slot of honest round opening slot `i + 1` is at least `R` slots after that of `i`.

The variables: `S`, `Sched`: the setup and the schedule; `rs`, `m`, `tFirst`, `tLast`: the
sequence of honest round opening slots; `i`: an index.

Read aloud: the next honest round opening slot starts at least one round later. -/
theorem opening_round_step {S : Setup V} {Sched : Schedule V} {rs : ℕ → ℕ} {m tFirst tLast : ℕ}
    (hSeq : HonestOpeningSeq S Sched rs m tFirst tLast) {i : ℕ} (hi : i < m) :
    rs i * S.C.R + S.C.R ≤ rs (i + 1) * S.C.R := by
  have h' : (rs i + 1) * S.C.R ≤ rs (i + 1) * S.C.R := Nat.mul_le_mul_right _ (hSeq.mono i hi)
  rw [Nat.add_mul, Nat.one_mul] at h'
  exact h'

/-- `QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s''`: the hypotheses of
`spoiled_near_fork_choice_change_cutoff` its proof reads, with the negation of its conclusion, for
the honest round opening slot `i` whose first slot is `s₀ + 1 = rs i * R` and the end `s''` of the
range read, at least one round later (`s₀ + 1 + R ≤ s''`, the field `sR`) and at most `r * R`: the
next honest round opening slot's first slot `rs (i + 1) * R`, or `r * R` for the honest round
opening slot whose round holds `r * R`: the execution assumptions and unforgeability,
every honest validator awake in the phase, fewer than a third in the adversary set, committee
sleepiness from `anchorCW S tGAT`, the honest round opening slots `rs 0 < … < rs m` with `i < m`
and `s'' ≤ r * R`, no proposal of an honest round opening slot colliding with a block its proposer
held, and no validator outside the adversary set with a `ForkChoiceChangeAt` from the vote time of
slot `s₀ + 1 − k − 1` to before the support cutoff of slot `s''`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `r`: the round of the action time the climb ends at; `m`: the index of the last honest round opening slot; `i`:
  the index of an honest round opening slot; `rs`: the rounds of the honest round opening slots; `s₀`: the slot before the honest round opening slot; `s''`: the
  end of the range read.

Roots name blocks until `supportCutoff S s''`: the end of the range read; every reader of the
bundle compares blocks held before times at most it. -/
structure QuietCtx (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST tGAT tAwakeEnd r m i : ℕ) (rs : ℕ → ℕ) (s₀ s'' : ℕ) : Prop where
  hDiv : TimeDiverges x.toTrace
  hMono : Sched.MonotoneCorruption
  hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject
  hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject
  hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s'')
  hParent : ParentHeldAtDelivery S Sched x
  hOwner : VotesCastByOwner S Sched x
  hU : Unforgeability Vocab.goldilocks Sched x.toTrace
  hGST : GST ≤ tGAT
  hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int)
  hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
    ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int)
  hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT)
  hEnd : aR S r ≤ tAwakeEnd
  hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd
  hi : i < m
  hs : rs i * S.C.R = s₀ + 1
  sR : s₀ + 1 + S.C.R ≤ s''
  hir : s'' ≤ r * S.C.R
  hNoCol : ¬ RootCollisionAtOpening S Sched x rs m
  hNo : ∀ (w : V) (t' : ℕ), voteTime S (s₀ + 1 - S.C.k - 1) ≤ t' →
    t' < supportCutoff S s'' → w ∉ Sched.adv (t' : Int) →
    ¬ ForkChoiceChangeAt S Sched x w t'

namespace QuietCtx

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r m i : ℕ} {rs : ℕ → ℕ} {s₀ s'' : ℕ}

/-- The opening is at or after the first one. -/
theorem rs0 (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'') :
    rs 0 * S.C.R ≤ s₀ + 1 := by
  rw [← C.hs]
  rcases Nat.eq_zero_or_pos i with h | h
  · rw [h]
  · exact Nat.mul_le_mul_right _ (le_of_lt (r_lt_of_lt_of_mono rs m C.hSeq.mono 0 i h
      (le_of_lt C.hi)))

/-- Every window from the opening on starts after the committee premise's anchor. -/
theorem win (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'') {σ : ℕ}
    (h : s₀ + 1 ≤ σ) :
    2 * S.C.k ≤ σ ∧ anchorCW S tGAT ≤ slotStart S (σ - S.C.k - 1) := by
  have hw := window_after_anchor S Sched rs m tGAT tAwakeEnd σ C.hSeq (le_trans C.rs0 h)
  have h2 := hw.1
  have hk := S.C.k_ge_two
  exact ⟨h2, le_trans hw.2 (slotStart_mono S (by omega))⟩

/-- The support cutoff of the next opening's first slot is at most `aR S r`. -/
theorem cut_le (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'') :
    supportCutoff S s'' ≤ aR S r := by
  unfold aR
  have := C.hir
  exact supportCutoff_mono S (by omega)

/-- The support cutoff of the next opening's first slot is in the phase. -/
theorem cut_end (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'') :
    supportCutoff S s'' ≤ tAwakeEnd :=
  le_trans C.cut_le C.hEnd

/-- No fork-choice change at `w` from `t₁` to before `b`, inside the context's range. -/
theorem noChange (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'') (w : V) {t₁ b : ℕ}
    (h1 : voteTime S (s₀ + 1 - S.C.k - 1) ≤ t₁)
    (hb : b ≤ supportCutoff S s'') (hw : w ∉ Sched.adv (b : Int)) :
    ∀ t : ℕ, t₁ ≤ t → t < b → ¬ ForkChoiceChangeAt S Sched x w t := fun t ht1 ht2 =>
  C.hNo w t (by omega) (by omega) (fun h => hw (C.hMono _ _ (by exact_mod_cast ht2.le) h))

/-- A validator honest at `b ≤ tAwakeEnd` is awake and honest at every time from `t₁ ≥ tGAT` to
`b`. -/
theorem awakeHonest (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'') (w : V)
    {t₁ b : ℕ} (h1 : tGAT ≤ t₁) (hb : b ≤ tAwakeEnd) (hw : w ∉ Sched.adv (b : Int)) :
    ∀ t : ℕ, t₁ ≤ t → t ≤ b → w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int) := by
  intro t ht1 ht2
  have hw' : w ∉ Sched.adv (t : Int) := fun h => hw (C.hMono _ _ (by exact_mod_cast ht2) h)
  exact ⟨C.hAwake t (by omega) (by omega) w hw', hw'⟩

/-- B6's context at every window end from the opening to the next opening. -/
theorem b6 (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'') {σ : ℕ}
    (h1 : s₀ + 1 ≤ σ) (h2 : σ ≤ s'') :
    B6Ctx S Sched x GST tGAT tAwakeEnd r σ := by
  have hw := C.win h1
  have hw0 := C.win (le_refl (s₀ + 1))
  refine ⟨C.hDiv, C.hMono, C.hSync, C.hCatch, C.hRoots.mono (supportCutoff_mono S h2),
    C.hParent, C.hOwner, C.hU, C.hGST, C.hThird, C.hAwake, C.hCommittees, C.hEnd,
    (by have := hw.1; omega), le_trans (supportCutoff_mono S h2) C.cut_le,
    le_trans hw.2 (slotStart_mono S (by omega)), ?_⟩
  intro w t' h1' h2' h3
  exact C.hNo w t' (le_trans (voteTime_mono S (by omega)) h1')
    (lt_of_lt_of_le h2' (supportCutoff_mono S h2)) h3

/-- The window before the opening is stable (B6, `stability_fact3`). -/
theorem stable (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'') :
    FrontWindowStable S Sched x (Hon S Sched) (s₀ + 1 - 2 * S.C.k) (s₀ + 1 - 1) := by
  by_contra hF
  have hw := C.win (le_refl (s₀ + 1))
  have hsR := C.sR
  obtain ⟨w, t', h1, h2, h3, h4⟩ := stability_fact3 S Sched x GST tGAT tAwakeEnd r (s₀ + 1)
    C.hDiv C.hMono C.hSync C.hCatch (C.hRoots.mono (supportCutoff_mono S (by omega)))
    C.hParent C.hOwner C.hU C.hGST C.hThird
    C.hAwake C.hCommittees C.hEnd (by have := hw.1; omega)
    (le_trans (supportCutoff_mono S (by omega)) C.cut_le)
    (le_trans hw.2 (slotStart_mono S (by omega))) hF
  exact C.hNo w t' h1 (lt_of_lt_of_le h2 (supportCutoff_mono S (by omega))) h3 h4

/-- The front's bundle for the window before the opening (`FrontHyps` with `s_w := s₀ + 1 − 2k`,
`s' := s₀`, the member sets `Hon S Sched`), with the end time the support cutoff of slot `s₀ + 1`.

Roots name blocks until `supportCutoff S s₀`: the bundle carries the premise at the support cutoff
of its slot `s' := s₀`. -/
theorem front (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'') :
    FrontHyps S Sched x GST tGAT (supportCutoff S (s₀ + 1)) (s₀ + 1 - 2 * S.C.k) s₀
      (Hon S Sched) := by
  have hw := C.win (le_refl (s₀ + 1))
  have hk := S.C.k_ge_two
  have hsR := C.sR
  have hEs : supportCutoff S (s₀ + 1) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (by omega)) C.cut_end
  have C6 := C.b6 (le_refl (s₀ + 1)) (by omega)
  have hSt := C.stable
  rw [Nat.add_sub_cancel] at hSt
  refine ⟨C.hDiv, C.hMono, C.hSync, C.hCatch,
    C.hRoots.mono (supportCutoff_mono S (by omega)), C.hParent, C.hOwner, C.hGST,
    ?_, ?_, fun t h1 h2 => C.hAwake t h1 (le_trans h2 hEs), ?_, ?_, le_rfl, hSt.1⟩
  · intro s₁ h1 h2
    exact (roundMembers_mono S Sched (s₁ + 1) (s₁ + 1 + 1) tAwakeEnd C.hMono (Nat.le_succ _)
      (le_trans (supportCutoff_mono S (by omega)) hEs)).1
  · intro s₁ _ _ v hv
    exact (Finset.mem_sdiff.1 hv).2
  · intro s₁ h1 h2
    exact (C6.members (σ := s₁) (by omega) (by omega)).2
  · have := dutyWindowStart_of_anchor S tGAT (s₀ + 1 - 2 * S.C.k)
      (window_after_anchor S Sched rs m tGAT tAwakeEnd (s₀ + 1) C.hSeq C.rs0).2
    omega

end QuietCtx

/-! ## The round's first clause -/

namespace QuietCtx

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r m i : ℕ} {rs : ℕ → ℕ} {s₀ s'' : ℕ}

/-- The window's context of the opening. -/
theorem toWin (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'') :
    WinCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ := by
  have hsR := C.sR
  have hir := C.hir
  have hR := S.C.R_ge_two
  exact ⟨C.hDiv, C.hMono, C.hSync, C.hCatch,
    C.hRoots.mono (supportCutoff_mono S (by omega)), C.hParent, C.hOwner, C.hU,
    C.hGST, C.hThird, C.hAwake, C.hCommittees, C.hEnd, C.hSeq, le_of_lt C.hi, C.hs, by omega,
    fun w t' h1 h2 h3 => C.hNo w t' h1 (lt_of_lt_of_le h2 (supportCutoff_mono S (by omega))) h3⟩

/-- **The round's first clause** (`WinCtx.clause1`). -/
theorem clause1 (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'') (B : Block V)
    (hB : ProposalAt S Sched x (s₀ + 1) B) :
    ∀ w ∈ Hon S Sched (s₀ + 1),
      (get_fc_root (stateBefore x (voteTime S (s₀ + 1)) w).S).AncestorEq B.parent ∧
      head_height_floor (stateBefore x (voteTime S (s₀ + 1)) w).S ≤
        (chainStateOf S.C B.parent).h :=
  C.toWin.clause1 B hB

end QuietCtx

/-! ## The round's other clauses -/

namespace QuietCtx

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r m i : ℕ} {rs : ℕ → ℕ} {s₀ s'' : ℕ}

/-- **The proposal and its parent, at the proposer.** The opening's proposal `B` has a parent that
is a viable head of the proposer's frame before the start of slot `s₀ + 1`, held then; `B` is not
the genesis block, its parent is an ancestor of it, at a chain-state height at most `B`'s; and the
proposer holds `B` right after its tick (`lem22a_proposer_holds_own_proposal`, the root of `B` new to
it since no opening collides).

The variables:
- `C`: the context; `B`: the proposal. -/
theorem proposal_facts (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'') (B : Block V)
    (hB : ProposalAt S Sched x (s₀ + 1) B) :
    B.parent ∈ (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) (S.P.proposer (s₀ + 1))).S).viable_heads ∧
    B.parent ∈ (stateBefore x (slotStart S (s₀ + 1)) (S.P.proposer (s₀ + 1))).S.T ∧
    B.parent.AncestorEq B ∧ (chainStateOf S.C B.parent).h ≤ (chainStateOf S.C B).h ∧
    B ∈ (stateBefore x (slotStart S (s₀ + 1) + 1) (S.P.proposer (s₀ + 1))).S.T := by
  have hPV := proposal_parent_viable_head S Sched x s₀ B _ hB
  have hPV' := (mem_viable_heads_iff _ _).1 hPV
  obtain ⟨iB, hl, hsent⟩ := hB
  obtain ⟨-, hBne, hBpar?, -⟩ := proposal_parent_walk_end S Sched x s₀ iB B _ hl hsent
  have hPB : B.parent.AncestorEq B := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_parent? hBpar?
  have hh : (chainStateOf S.C B.parent).h ≤ (chainStateOf S.C B).h := by
    rcases (lem47_chain_state_heights S.C B B).2.1 hBne with h | h
    · rw [h]
    · rw [h]
      exact Nat.le_succ _
  refine ⟨hPV, hPV'.1, hPB, hh, ?_⟩
  have hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (s₀ + 1)) (S.P.proposer (s₀ + 1))).S.T,
      B'.root ≠ B.root := by
    intro B' hB' heq
    apply C.hNoCol
    rw [GoldilocksCorrectness.Proofs.View.rootCollisionAtOpening_unfold]
    refine ⟨i, le_of_lt C.hi, B, ?_, ?_⟩
    · rw [C.hs]
      exact ⟨iB, hl, hsent⟩
    · rw [C.hs]
      exact ⟨B', hB', heq⟩
  have hF : (stateBefore x (slotStart S (s₀ + 1)) (S.P.proposer (s₀ + 1))).S.F.compatible B =
      true := (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hPV'.2.1 hPB))
  have hBi := lem22a_proposer_holds_own_proposal S Sched x s₀ iB B _ C.hDiv C.hMono hl hsent
    hRootNew hPV'.1 hF
  have ht := (time_of_lbl_tickAllAwake x hl).2
  have hle : iB + 1 ≤ stepBefore x (slotStart S (s₀ + 1) + 1) :=
    (time_lt_iff_le_stepBefore x C.hDiv (by omega)).1 (by omega)
  exact mem_T_mono x _ hle hBi

/-- **A member's root stays on the proposal's parent's chain through the context's range.** For a
member `w` of `Hon S Sched (s₀ + 1)` and a time `t₂` from the vote time of slot `s₀ + 1` to the
support cutoff of slot `s''` at which `w` is honest: `w`'s root before `t₂` is `B.parent` or an
ancestor of it, with its `head_height_floor` at most `B.parent`'s height (`clause1`,
`root_below_kept`).

The variables:
- `C`: the context; `B`: the proposal; `w`: the member; `t₂`: the time. -/
theorem rootBelow (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'') (B : Block V)
    (hB : ProposalAt S Sched x (s₀ + 1) B) (w : V) (hw : w ∈ Hon S Sched (s₀ + 1)) (t₂ : ℕ)
    (h1 : voteTime S (s₀ + 1) ≤ t₂) (h2 : t₂ ≤ supportCutoff S s'')
    (hwt : w ∉ Sched.adv (t₂ : Int)) :
    (get_fc_root (stateBefore x t₂ w).S).AncestorEq B.parent ∧
      head_height_floor (stateBefore x t₂ w).S ≤ (chainStateOf S.C B.parent).h := by
  have hk := S.C.k_ge_two
  have hw0 := C.win (le_refl (s₀ + 1))
  have hEnd := C.cut_end
  have hsR := C.sR
  have hμ := voteTime_eq S (s₀ + 1 - S.C.k - 1)
  have hv1 := voteTime_eq S (s₀ + 1)
  have hμs := slotStart_mono S (show s₀ + 1 - S.C.k - 1 ≤ s₀ + 1 by omega)
  have hpH : S.P.proposer (s₀ + 1) ∉ Sched.adv ((supportCutoff S (s₀ + 1) : ℕ) : Int) := by
    have h := C.hSeq.honest i (le_of_lt C.hi)
    rw [C.hs] at h
    exact h
  have hc1 := supportCutoff_eq S (s₀ + 1)
  have hpb : S.P.proposer (s₀ + 1) ∉ Sched.adv ((slotStart S (s₀ + 1) : ℕ) : Int) :=
    fun h => hpH (C.hMono _ _ (by exact_mod_cast (show slotStart S (s₀ + 1) ≤
      supportCutoff S (s₀ + 1) by omega)) h)
  obtain ⟨-, hPT, -, -, -⟩ := C.proposal_facts B hB
  obtain ⟨hr, hf⟩ := C.clause1 B hB w hw
  exact root_below_kept S Sched x C.hMono C.hU C.hRoots (supportCutoff S s'')
    (voteTime S (s₀ + 1)) (slotStart S (s₀ + 1)) w _ B.parent
    (adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hEnd) C.hThird)
    (by have := supportCutoff_mono S (show s₀ + 1 ≤ s'' by omega); omega) hpb hPT
    hr hf le_rfl t₂ h1 h2 hwt (C.noChange w (by omega) h2 hwt)

/-- **The round's second clause.** Before the action time of slot `s₀ + 1`, every member has its
root `B` or an ancestor of `B` and its `head_height_floor` at most `B`'s height (`rootBelow`).

The variables:
- `C`: the context; `B`: the proposal. -/
theorem clause2 (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'') (B : Block V)
    (hB : ProposalAt S Sched x (s₀ + 1) B) :
    ∀ v ∈ Hon S Sched (s₀ + 1),
      (get_fc_root (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S).AncestorEq B ∧
      head_height_floor (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S ≤
        (chainStateOf S.C B).h := by
  intro v hv
  have hsR := C.sR
  have hR := S.C.R_ge_two
  obtain ⟨-, -, hPB, hh, -⟩ := C.proposal_facts B hB
  have hvb : v ∉ Sched.adv ((supportCutoff S (s₀ + 1 + 1) : ℕ) : Int) := (Finset.mem_sdiff.1 hv).2
  have hc2 := supportCutoff_eq S (s₀ + 1 + 1)
  have hv12 := voteTime_succ S (s₀ + 1)
  obtain ⟨hr, hf⟩ := C.rootBelow B hB v hv (supportCutoff S (s₀ + 1 + 1)) (by omega)
    (supportCutoff_mono S (by omega)) hvb
  exact ⟨ancestorEq_trans hr hPB, le_trans hf hh⟩

/-- **The round's third clause.** At every slot `s'` of the round with `s' + 2 ≤ s''`, every member
of `Hon S Sched (s' + 1)` satisfies `StepFrameAt` relative to the proposal `B`: `B` reaches it one
delay after its proposer's tick (`mem_T_before_add_delay_of_held`), and its root stays on `B`'s
parent's chain with its `head_height_floor` at most `B`'s height (`rootBelow`), at the two reading
points (`stepFrame_of_compat`).

The variables:
- `C`: the context; `B`: the proposal. -/
theorem clause3 (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'') (B : Block V)
    (hB : ProposalAt S Sched x (s₀ + 1) B) :
    ∀ s', s₀ + 1 ≤ s' → s' + 2 ≤ s'' → ∀ w ∈ Hon S Sched (s' + 1), StepFrameAt S Sched x B s' w := by
  intro s' h1 h2 w hw
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hEnd := C.cut_end
  have hsR := C.sR
  have hw0 := C.win (le_refl (s₀ + 1))
  have hanc := hw0.2
  rw [anchorCW_eq] at hanc
  have hμs := slotStart_mono S (show s₀ + 1 - S.C.k - 1 ≤ s₀ + 1 by omega)
  have hGSTt := C.hGST
  obtain ⟨-, -, hPB, hh, hBp⟩ := C.proposal_facts B hB
  have hmem : ∀ a b : ℕ, a ≤ b → b ≤ s'' → ∀ u ∈ roundMembers S Sched b,
      u ∈ roundMembers S Sched a := fun a b hab hb u hu =>
    (roundMembers_mono S Sched a b tAwakeEnd C.hMono hab
      (le_trans (supportCutoff_mono S hb) hEnd)).1 hu
  have hw1 : w ∈ Hon S Sched (s₀ + 1) := hmem (s₀ + 1 + 1) (s' + 1 + 1) (by omega) (by omega) w hw
  have hwb : w ∉ Sched.adv ((supportCutoff S (s' + 2) : ℕ) : Int) := (Finset.mem_sdiff.1 hw).2
  have hsc2 := supportCutoff_mono S (show s' + 2 ≤ s'' from h2)
  have hpH : S.P.proposer (s₀ + 1) ∉ Sched.adv ((supportCutoff S (s₀ + 1) : ℕ) : Int) := by
    have h := C.hSeq.honest i (le_of_lt C.hi)
    rw [C.hs] at h
    exact h
  have hc1 := supportCutoff_eq S (s₀ + 1)
  have hv1 := voteTime_eq S (s₀ + 1)
  have hvs := voteTime_mono S (show s₀ + 1 ≤ s' + 1 by omega)
  have hvc := supportCutoff_eq S (s' + 2)
  have hvt2 := voteTime_succ S (s' + 1)
  have hvt1 := voteTime_eq S (s' + 1)
  have hfz := viewFreeze_eq S s'
  have hss' := slotStart_mono S h1
  have hss1' : slotStart S (s' + 1) = slotStart S s' + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hvt2' : voteTime S (s' + 2) = voteTime S (s' + 1) + 4 * Δ S := voteTime_succ S (s' + 1)
  have hanc' : tGAT ≤ slotStart S (s₀ + 1 - S.C.k - 1) := le_trans
    (by rw [anchorCW_eq]; exact Nat.le_add_right _ _) hw0.2
  have hwt : ∀ t : ℕ, t ≤ supportCutoff S (s' + 2) → w ∉ Sched.adv (t : Int) :=
    fun t ht h => hwb (C.hMono _ _ (by exact_mod_cast ht) h)
  -- `B` reaches `w`
  have hBw : B ∈ (stateBefore x (slotStart S (s₀ + 1) + 1 + Δ S) w).S.T := by
    obtain ⟨hr0, -⟩ := C.rootBelow B hB w hw1 (slotStart S (s₀ + 1) + 1 + Δ S) (by omega)
      (by omega) (hwt _ (by omega))
    refine mem_T_before_add_delay_of_held C.hDiv C.hMono C.hSync C.hCatch
      (C.hRoots.mono (le_trans (by omega) (supportCutoff_mono S (show s₀ + 1 ≤ s'' by omega))))
      C.hParent (by omega) le_rfl (by omega)
      (fun h => hpH (C.hMono _ _ (by exact_mod_cast (show slotStart S (s₀ + 1) + 1 ≤
        supportCutoff S (s₀ + 1) by omega)) h)) hBp ?_ ?_
    · intro t' ht1 ht2
      have hw' := hwt t' (by omega)
      exact ⟨C.hAwake t' (by omega) (by omega) w hw', hw'⟩
    · exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans
        (F_ancestorEq_fc_root_of_stateBefore S Sched x _ w) (ancestorEq_trans hr0 hPB)))
  obtain ⟨hr1, hf1⟩ := C.rootBelow B hB w hw1 (voteTime S (s' + 1)) hvs (by omega)
    (hwt _ (by omega))
  obtain ⟨hr2, -⟩ := C.rootBelow B hB w hw1 (supportCutoff S (s' + 2)) (by omega) hsc2 hwb
  exact stepFrame_of_compat S Sched x C.hDiv B B s' w _ (ancestorEq_refl B) hBw
    (by omega) (by omega)
    ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hr1 hPB))) (le_trans hf1 hh)
    ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hr2 hPB)))

/-- **The round's fourth clause.** At every slot `s'` from `s₀` with `s' + 2 ≤ s''`, every member
of `Hon S Sched (s' + 1)` satisfies `StepFrameAt` relative to every confirmation `X` of a slot `σ`
from `s₀` to `s'` that a member of `Hon S Sched σ` saved: `X` has an honest committee supporter
whose vote's block is an ancestor of a block `W` that `w` holds one delay after the vote time of
slot `σ`, with `w`'s root compatible with `W` and its `head_height_floor` at most `W`'s height then
(B6's `frame` at the window ending at slot `σ + 2`); both stay so through the range
(`frame_compat_kept`), and `stepFrame_of_compat` at the two reading points.

The variables:
- `C`: the context. -/
theorem clause4 (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'') :
    ∀ s', s₀ + 1 - 1 ≤ s' → s' + 2 ≤ s'' → ∀ σ, s₀ + 1 - 1 ≤ σ → σ ≤ s' →
      ∀ v ∈ Hon S Sched σ, ∀ X : Block V,
        (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some X →
        ∀ w ∈ Hon S Sched (s' + 1), StepFrameAt S Sched x X s' w := by
  intro s' h1 h2 σ h3 h4 v hv X hX w hw
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hEnd := C.cut_end
  have hsR := C.sR
  have hw0 := C.win (le_refl (s₀ + 1))
  have C6 := C.b6 (σ := σ + 2) (by omega) (by omega)
  have hσ : σ + 2 - S.C.k - 1 ≤ σ := by omega
  obtain ⟨u, huA, vote, hsend, H_u, hHT, hvote, hXH⟩ := C6.supporter_saved hσ le_rfl v hv X hX
  have hwb : w ∉ Sched.adv ((supportCutoff S (s' + 2) : ℕ) : Int) := (Finset.mem_sdiff.1 hw).2
  have hsc2 := supportCutoff_mono S (show s' + 2 ≤ s'' from h2)
  have hvσ := voteTime_eq S σ
  have hvs := voteTime_mono S (show σ + 1 ≤ s' + 1 by omega)
  have hv1 := voteTime_eq S (σ + 1)
  have hss1 : slotStart S (σ + 1) = slotStart S σ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hvc := supportCutoff_eq S (s' + 2)
  have hvt2 := voteTime_succ S (s' + 1)
  have hsc22 := supportCutoff_eq S (σ + 2)
  have hv22 := voteTime_succ S (σ + 1)
  have hfz := viewFreeze_eq S s'
  have hss' := slotStart_mono S h4
  have hss1' : slotStart S (s' + 1) = slotStart S s' + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hvt2' : voteTime S (s' + 2) = voteTime S (s' + 1) + 4 * Δ S := voteTime_succ S (s' + 1)
  have hv22' : voteTime S (σ + 2) = voteTime S (σ + 1) + 4 * Δ S := voteTime_succ S (σ + 1)
  have hsσ1 := supportCutoff_eq S (σ + 1)
  have hwt : ∀ t : ℕ, t ≤ supportCutoff S (s' + 2) → w ∉ Sched.adv (t : Int) :=
    fun t ht h => hwb (C.hMono _ _ (by exact_mod_cast ht) h)
  have hvts : voteTime S (s' + 1) ≤ supportCutoff S (s' + 2) := by omega
  obtain ⟨H₁, hH₁T, hv₁, W, hHW, hWT, hfl, -, hr⟩ := C6.frame hσ le_rfl u huA vote hsend w
    (voteTime S σ + Δ S) le_rfl (by omega) (hwt _ (by omega))
  have huvt : u ∉ Sched.adv ((voteTime S σ : ℕ) : Int) :=
    (honestActiveAt_window S Sched σ u C.hMono huA (voteTime S σ)
      (dutyWindowStart_le_voteTime S σ) (by omega)).2
  have hH : H₁ = H_u := by
    rw [hvote] at hv₁
    simp only [GoldfishVote.mk.injEq, true_and] at hv₁
    exact eq_of_root_eq_held S Sched x C.hMono C.hRoots _ u H₁ H_u huvt hH₁T hHT hv₁.symm
      (by omega)
  rw [hH] at hHW
  have hXW := ancestorEq_trans hXH hHW
  have hw0 := C.win (le_refl (s₀ + 1))
  have hμ := voteTime_eq S (s₀ + 1 - S.C.k - 1)
  have hμs := slotStart_mono S (show s₀ + 1 - S.C.k - 1 ≤ σ by omega)
  have hkept := frame_compat_kept S Sched x C.hMono C.hU C.hRoots (supportCutoff S s'')
    (voteTime S σ + Δ S) (voteTime S σ + Δ S) w w W
    (adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hEnd) C.hThird) (by omega)
    (hwt _ (by omega)) hWT hr hfl le_rfl
  obtain ⟨hr1, hf1⟩ := hkept (voteTime S (s' + 1)) (by omega) (by omega) (hwt _ hvts)
    (C.noChange w (by omega) (by omega) (hwt _ hvts))
  obtain ⟨hr2, -⟩ := hkept (supportCutoff S (s' + 2)) (by omega) (by omega) hwb
    (C.noChange w (by omega) hsc2 hwb)
  exact stepFrame_of_compat S Sched x C.hDiv X W s' w _ hXW hWT (by omega) (by omega)
    hr1 hf1 hr2

/-- **The round's fifth clause.** The next opening's proposer `q` (honest at the support cutoff of
slot `s''`) saved a confirmation `D` of slot `s'' − 2`, its root before the start of slot `s''` is
`D` or an ancestor of `D` (`rootChain_at`), and its frame then has a viable head that is `D` or a
descendant of `D` (`frameP_of_conf`), B6's context at the window ending at slot `s''`.

The variables:
- `C`: the context; `hs''`: the end of the range read is the next honest round opening slot's
  first slot. -/
theorem clause5 (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'')
    (hs'' : rs (i + 1) * S.C.R = s'') :
    ∃ D : Block V,
      (∃ v ∈ Hon S Sched (s'' - 2),
        (stateBefore x (supportCutoff S (s'' - 1) + 1) v).A.saved_confirmation (s'' - 2) =
          some D) ∧
      (fg_to_ac (stateBefore x (slotStart S s'') (S.P.proposer s'')).S).fc_root.AncestorEq D ∧
      ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S s'') (S.P.proposer s'')).S).tree,
        W ∈ (fg_to_ac (stateBefore x (slotStart S s'') (S.P.proposer s'')).S).viable_heads ∧
        D.AncestorEq W := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hEnd := C.cut_end
  have hsR := C.sR
  have hR := S.C.R_ge_two
  have C6 := C.b6 (σ := s'') (by omega) le_rfl
  have hqH : S.P.proposer s'' ∉ Sched.adv ((supportCutoff S s'' : ℕ) : Int) := by
    have h := C.hSeq.honest (i + 1) C.hi
    rw [hs''] at h
    exact h
  have hw'' := C.win (σ := s'') (by omega)
  obtain ⟨σ, hσ⟩ : ∃ σ, s'' = σ + 2 := ⟨s'' - 2, by omega⟩
  subst hσ
  rw [show σ + 2 - 2 = σ by omega, show σ + 2 - 1 = σ + 1 by omega]
  have hq : S.P.proposer (σ + 2) ∈ Hon S Sched (σ + 1) :=
    Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hqH⟩
  have hq' : S.P.proposer (σ + 2) ∈ roundMembers S Sched (σ + 1) :=
    (roundMembers_mono S Sched (σ + 1) (σ + 2) tAwakeEnd C.hMono (Nat.le_succ _) hEnd).1 hq
  have hsc1 := supportCutoff_eq S (σ + 1)
  have hv1 := voteTime_eq S (σ + 1)
  have hvσ := voteTime_eq S σ
  have hss2 : slotStart S (σ + 2) = slotStart S (σ + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (σ + 1)]
    exact Nat.mul_succ _ _
  have hss1 : slotStart S (σ + 1) = slotStart S σ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hsc2 := supportCutoff_eq S (σ + 2)
  have hv2 := voteTime_eq S (σ + 2)
  have hqb : S.P.proposer (σ + 2) ∉ Sched.adv ((slotStart S (σ + 2) : ℕ) : Int) :=
    fun h => hqH (C.hMono _ _ (by exact_mod_cast (show slotStart S (σ + 2) ≤
      supportCutoff S (σ + 2) by omega)) h)
  obtain ⟨D, hD, hRD⟩ := C6.rootChain_at rfl (S.P.proposer (σ + 2)) hq (slotStart S (σ + 2))
    (by omega) (by omega)
  rw [← fc_root_eq] at hRD
  obtain ⟨W, hWt, hWv, hDW⟩ := C6.frameP_of_conf (σ := σ) (by omega) le_rfl _ hq' D D hD
    (ancestorEq_refl D) _ (slotStart S (σ + 2)) (by omega) (by omega) hqb
  exact ⟨D, ⟨_, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun h => hqH (C.hMono _ _
    (by exact_mod_cast supportCutoff_mono S (Nat.le_succ (σ + 1))) h)⟩, hD⟩, hRD, W, hWt, hWv,
    hDW⟩

/-- **The round is quiet relative to its own confirmations.** The five clauses, when the end of the
range read is the next honest round opening slot's first slot (`hs''`). -/
theorem quiet (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'')
    (hs'' : rs (i + 1) * S.C.R = s'') (B : Block V)
    (hB : ProposalAt S Sched x (s₀ + 1) B) :
    QuietRoundOnConfirmations S Sched x (Hon S Sched) B (s₀ + 1) s'' :=
  ⟨C.clause1 B hB, C.clause2 B hB, C.clause3 B hB, C.clause4, C.clause5 hs''⟩

end QuietCtx

/-! ## B10 restated, on the copy with the support cutoff of the next opening -/

/-- **B10 restated: a spoiled opening has a fork-choice change near it, with its time.**
The proof; the audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: by contradiction. With no validator outside the adversary set having a
`ForkChoiceChangeAt` from the vote time of slot `rs i * R − k − 1` to before the support cutoff of
slot `rs (i + 1) * R`, every proposal of the opening's first slot makes the round quiet relative to
its own confirmations (`QuietCtx.quiet`), against `Spoiled`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `r`: the round of the action time the climb ends at; `m`: the index of the last honest round opening slot; `i`:
  the index of an honest round opening slot; `rs`: the rounds of the honest round opening slots.

Roots name blocks until `supportCutoff S (rs (i + 1) * S.C.R)`: the end of the range the context
`QuietCtx` reads, the support cutoff of the next honest round opening slot's first slot. -/
theorem spoiled_near_fork_choice_change_cutoff (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r m i : ℕ) (rs : ℕ → ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (rs (i + 1) * S.C.R)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hEnd : aR S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hi : i < m) (hir : rs (i + 1) * S.C.R ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m)
    (hSp : Spoiled S Sched x rs i) :
    ∃ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' ∧
      t' < supportCutoff S (rs (i + 1) * S.C.R) ∧ w ∉ Sched.adv (t' : Int) ∧
      ForkChoiceChangeAt S Sched x w t' := by
  by_contra hcon
  have hNo : ∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
      t' < supportCutoff S (rs (i + 1) * S.C.R) → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t' :=
    fun w t' h1 h2 h3 h4 => hcon ⟨w, t', h1, h2, h3, h4⟩
  have hk := S.C.k_ge_two
  have h0 : rs 0 * S.C.R ≤ rs i * S.C.R := by
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h]
    · exact Nat.mul_le_mul_right _ (le_of_lt (r_lt_of_lt_of_mono rs m hSeq.mono 0 i h
        (le_of_lt hi)))
  have hw := window_after_anchor S Sched rs m tGAT tAwakeEnd (rs i * S.C.R) hSeq h0
  have hs1 : rs i * S.C.R = rs i * S.C.R - 1 + 1 := by omega
  have C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs (rs i * S.C.R - 1)
      (rs (i + 1) * S.C.R) :=
    ⟨hDiv, hMono, hSync, hCatch, hRoots, hParent, hOwner, hU, hGST, hThird, hAwake,
      hCommittees, hEnd, hSeq, hi, hs1, by rw [← hs1]; exact opening_round_step hSeq hi, hir,
      hNoCol, by rw [← hs1]; exact hNo⟩
  obtain ⟨B, hB, hNQ⟩ := hSp
  apply hNQ
  rw [hs1] at hB ⊢
  exact C.quiet rfl B hB

/-! ## The context from the hypotheses of the climb's steps -/

/-- The context `QuietCtx` of the honest round opening slot `i` with `s₀ := rs i * R − 1` and the
end `s''` of the range read, from the hypotheses the climb's steps state: `s''` at least one round
after `rs i * R` and at most `r * R`, no fork-choice change to before its support cutoff. The climb's
steps take `s'' := rs (i + 1) * R` (`opening_round_step` for `hsR`); the honest round opening slot
whose round holds `r * R` takes `s'' := r * R`.

The variables: as in `spoiled_near_fork_choice_change_cutoff`; `s''`: the end of the range read.

Roots name blocks until `supportCutoff S s''`: the end of the range the context carries. -/
theorem quietCtx_of (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r m i : ℕ) (rs : ℕ → ℕ) {s'' : ℕ}
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s''))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hEnd : aR S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hi : i < m) (hsR : rs i * S.C.R + S.C.R ≤ s'') (hir : s'' ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m)
    (hNo : ∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
      t' < supportCutoff S s'' → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t') :
    rs i * S.C.R = rs i * S.C.R - 1 + 1 ∧
    QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs (rs i * S.C.R - 1) s'' := by
  have hk := S.C.k_ge_two
  have h0 : rs 0 * S.C.R ≤ rs i * S.C.R := by
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h]
    · exact Nat.mul_le_mul_right _ (le_of_lt (r_lt_of_lt_of_mono rs m hSeq.mono 0 i h
        (le_of_lt hi)))
  have hw := window_after_anchor S Sched rs m tGAT tAwakeEnd (rs i * S.C.R) hSeq h0
  have hs1 : rs i * S.C.R = rs i * S.C.R - 1 + 1 := by omega
  refine ⟨hs1, hDiv, hMono, hSync, hCatch, hRoots, hParent, hOwner, hU, hGST, hThird,
    hAwake, hCommittees, hEnd, hSeq, hi, hs1, by rw [← hs1]; exact hsR, hir, hNoCol, ?_⟩
  rw [← hs1]
  exact hNo

namespace QuietCtx

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r m i : ℕ} {rs : ℕ → ℕ} {s₀ s'' : ℕ}

/-- **A quiet round's proposal is attested at its action time, or its height was attested
before.** With the round's base (`WinCtx.base`, the second clause giving the roots at the action
time), a member's update at the action time saves the proposal `B` with `B` among its fast blocks,
its live locks on `B`'s chain; so the member attests at `B`'s height at its tick then, or its record
already sent an attestation at that height, at an earlier tick (`lem61_honest_validator_attests_frame`,
`record_content_sent`).

The variables:
- `C`: the context; `B`: the proposal; `H₂`: a height below `B`'s. -/
theorem attests_above (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'') (B : Block V)
    (hB : ProposalAt S Sched x (s₀ + 1) B) (H₂ : ℕ) (hBh : H₂ < (chainStateOf S.C B).h) :
    ∃ (t₀ : ℕ) (v : V) (a : Attestation V), t₀ ≤ supportCutoff S (s₀ + 1 + 1) ∧
      HonestAttestationAt S Sched x t₀ v a ∧ H₂ < a.h := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hsR := C.sR
  have hR := S.C.R_ge_two
  have hw0 := C.win (le_refl (s₀ + 1))
  have hEnd := C.cut_end
  have hEs2 : supportCutoff S (s₀ + 1 + 1) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (by omega)) hEnd
  have hcl2 := C.clause2 B hB
  obtain ⟨hHeld, hBase, hUpd⟩ := C.toWin.base C.hNoCol B hB (fun v hv => (hcl2 v hv).1)
  have hA2 : anchorCW S tGAT ≤ slotStart S (s₀ + 1 + 1) :=
    le_trans hw0.2 (slotStart_mono S (by omega))
  have hMaj1 := committee_majority_of_committeeSleepiness S Sched _ (s₀ + 1) C.hCommittees hA2
  obtain ⟨v, hv⟩ : (S.P.committee (s₀ + 1) ∩ roundMembers S Sched (s₀ + 1 + 1)).Nonempty :=
    Finset.card_pos.1 (by omega)
  have hvH : v ∈ Hon S Sched (s₀ + 1) := (Finset.mem_inter.1 hv).2
  obtain ⟨A', hUp, hS, hF⟩ := hUpd v hvH
  obtain ⟨iB, hlB, hsentB⟩ := hB
  obtain ⟨hBslot, -, -, -⟩ := proposal_parent_walk_end S Sched x s₀ iB B _ hlB hsentB
  have hdw1 := dutyWindowStart_of_anchor S tGAT (s₀ + 1) hA2
  have hvwin : ∀ t : ℕ, dutyWindowStart S (s₀ + 1 + 1) ≤ t → t ≤ supportCutoff S (s₀ + 1 + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int) := by
    intro t h1 h2
    have hdm := dutyWindowStart_mono S (show s₀ + 1 ≤ s₀ + 1 + 1 by omega)
    exact C.awakeHonest v (t₁ := tGAT) le_rfl hEs2 (Finset.mem_sdiff.1 hvH).2 t (by omega) h2
  have hLk := update_lock_entries_ancestorEq S Sched x (s₀ + 1) B v A' C.hDiv C.hMono
    hvwin hUp hS hBslot (fun A'' hR e he hl => hBase.2.1 v hvH A'' hR e he hl)
  have hv1 := voteTime_eq S (s₀ + 1)
  have hc2 := supportCutoff_eq S (s₀ + 1 + 1)
  have hv2 := voteTime_succ S (s₀ + 1)
  have hBin : B ∈ (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S.T :=
    (stateBefore_grows x C.hDiv v (show voteTime S (s₀ + 1) ≤ supportCutoff S (s₀ + 1 + 1) by
      omega)).1 (hHeld v hvH)
  have hLockBox := lockBox_of_frame S Sched x C.hU _ v B
    (adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hEs2) C.hThird) (hcl2 v hvH).1
    (hcl2 v hvH).2
  rcases lem61_honest_validator_attests_frame S Sched x (rs i) (s₀ + 1) B v A' _ _ C.hDiv C.hMono
      C.hs.symm hvwin hUp hS hF hLk ⟨rfl, rfl⟩ (hcl2 v hvH).1 (hcl2 v hvH).2 hBin
      hLockBox with ⟨i', a, hl, hsent, -, hah, -⟩ | ⟨b, hb, hbh, -⟩
  · have hds := dutyWindowStart_succ_le_slotStart S (s₀ + 1)
    have hss1 : slotStart S (s₀ + 1 + 1) = slotStart S (s₀ + 1) + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq S (s₀ + 1), Nat.mul_add, Nat.mul_one]
    have hv12 := voteTime_eq S (s₀ + 1 + 1)
    have hvA := hvwin _ (by omega) le_rfl
    exact ⟨_, v, a, le_rfl, ⟨i', hl, hvA.1, hvA.2, hsent⟩, by rw [hah]; exact hBh⟩
  · obtain ⟨j, t', a, hl, ht', hawk, hadv, hsent, -, hac, -⟩ :=
      record_content_sent S Sched x _ v b C.hDiv hb
    have hah : a.h = b.h := by
      rw [← hac]
      rfl
    exact ⟨t', v, a, le_of_lt ht', ⟨j, hl, hawk, hadv, hsent⟩, by rw [hah, hbh]; exact hBh⟩

end QuietCtx

/-- **B11 restated, on a copy: a quiet opening above the threshold attests above it.** The proof;
the audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: `quietCtx_of`, then `QuietCtx.attests_above` at the action time `aR S (rs i)`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `r`: the round of the action time the climb ends at; `m`: the index of the last honest round opening slot; `i`:
  the index of an honest round opening slot; `H₂`: the threshold; `rs`: the rounds of the honest round opening slots; `B`: the proposal at the honest round opening slot.

Roots name blocks until `supportCutoff S s''`: the end of the range the context `QuietCtx` carries
(`quietCtx_of`). -/
theorem quiet_top_gives_attestation_cutoff (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r m i H₂ s'' : ℕ) (rs : ℕ → ℕ)
    (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s''))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hEnd : aR S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hi : i < m) (hsR : rs i * S.C.R + S.C.R ≤ s'') (hir : s'' ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m)
    (hNo : ∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
      t' < supportCutoff S s'' → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t')
    (hB : ProposalAt S Sched x (rs i * S.C.R) B) (hBh : H₂ < (chainStateOf S.C B).h) :
    ∃ (t₀ : ℕ) (v : V) (a : Attestation V), t₀ ≤ aR S (rs i) ∧
      HonestAttestationAt S Sched x t₀ v a ∧ H₂ < a.h := by
  obtain ⟨hs1, C⟩ := quietCtx_of S Sched x GST tGAT tAwakeEnd r m i rs hDiv hMono hSync hCatch
    hRoots hParent hOwner hU hGST hThird hAwake hCommittees hEnd hSeq hi hsR hir hNoCol hNo
  rw [hs1] at hB
  obtain ⟨t₀, v, a, ht₀, hA, ha⟩ := C.attests_above B hB H₂ hBh
  refine ⟨t₀, v, a, ?_, hA, ha⟩
  unfold aR
  rw [← hs1] at ht₀
  exact ht₀

/-! ## Lemma 89r at an opening with no fork-choice change -/

namespace QuietCtx

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r m i : ℕ} {rs : ℕ → ℕ} {s₀ s'' : ℕ}

/-- **Lemma 89r at an opening with no fork-choice change.** For the opening's proposal `B` and the next
opening's proposal `B'`: `B'` is on `B`'s chain and raises the height or carries the progress quorum
within `δt` of `B`'s entry, and the rest of `lem89r_quiet_round`'s conclusion, for the window's
family (`WinCtx.fam`); its collision case is excluded by `hNoCol`.

The variables:
- `C`: the context; `hs''`: the end of the range read is the next honest round opening slot's
  first slot; `B`, `B'`: the two proposals. -/
theorem round89r (C : QuietCtx S Sched x GST tGAT tAwakeEnd r m i rs s₀ s'')
    (hs'' : rs (i + 1) * S.C.R = s'') (B B' : Block V)
    (hB : ProposalAt S Sched x (s₀ + 1) B) (hB' : ProposalAt S Sched x s'' B')
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject) :
    B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt ∧
        ∃ Q : Finset V, quorum V ≤ Q.card ∧ Q ⊆ (chainStateOf S.C B').progress)) ∧
    (∀ v ∈ Hon S Sched (s₀ + 1),
      (stateBefore x (supportCutoff S (s₀ + 1 + 1) + 1) v).A.saved_confirmation (s₀ + 1) =
        some B) := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hsR := C.sR
  have hR := S.C.R_ge_two
  have hw0 := C.win (le_refl (s₀ + 1))
  have hEnd := C.cut_end
  have hEs2 : supportCutoff S (s₀ + 1 + 1) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (by omega)) hEnd
  have hss : slotStart S (s₀ + 1) = slotStart S s₀ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv0 := voteTime_eq S s₀
  have hv1 := voteTime_eq S (s₀ + 1)
  have hc1 := supportCutoff_eq S (s₀ + 1)
  have hanc := hw0.2
  rw [anchorCW_eq] at hanc
  have hμs := slotStart_mono S (show s₀ + 1 - S.C.k - 1 ≤ s₀ by omega)
  have hGSTt := C.hGST
  have hpH : S.P.proposer (s₀ + 1) ∉ Sched.adv ((supportCutoff S (s₀ + 1) : ℕ) : Int) := by
    have h := C.hSeq.honest i (le_of_lt C.hi)
    rw [C.hs] at h
    exact h
  have hpAH := C.awakeHonest _ (t₁ := tGAT) le_rfl
    (le_trans (supportCutoff_mono S (by omega)) hEnd) hpH
  have hqH : S.P.proposer s'' ∉ Sched.adv ((supportCutoff S s'' : ℕ) : Int) := by
    have h := C.hSeq.honest (i + 1) C.hi
    rw [hs''] at h
    exact h
  obtain ⟨hChain, hLocks, hAnchor, -, hFrameP⟩ := C.toWin.fam
  have hmemD : ∀ a b : ℕ, a ≤ b → b ≤ s'' → ∀ u ∈ roundMembers S Sched b,
      u ∈ roundMembers S Sched a := fun a b hab hb u hu =>
    (roundMembers_mono S Sched a b tAwakeEnd C.hMono hab
      (le_trans (supportCutoff_mono S hb) hEnd)).1 hu
  have h89 := lem89r_quiet_round S Sched x GST (rs i) (s₀ + 1) s'' (Hon S Sched)
    (WinFam S Sched x s₀) B B' (S.P.proposer (s₀ + 1)) (S.P.proposer s'') C.hDiv C.hMono C.hSync
    C.hCatch hSyncF hCatchF (C.hRoots.mono (supportCutoff_mono S (by omega))) C.hParent
    C.hOwner C.hU C.hs.symm (by omega)
    (delivery_of_round S C.sR)
    (by rw [Nat.add_sub_cancel]; omega)
    (adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hEs2) C.hThird)
    (fun s' h1 h2 => hmemD (s' + 1) (s' + 1 + 1) (Nat.le_succ _) (by omega))
    (by
      intro s' h1 h2 v hv t ht1 ht2
      have hA : anchorCW S tGAT ≤ slotStart S (s' + 1) :=
        le_trans hw0.2 (slotStart_mono S (by omega))
      have := dutyWindowStart_of_anchor S tGAT s' hA
      exact C.awakeHonest v (t₁ := tGAT) le_rfl
        (le_trans (supportCutoff_mono S (by omega)) hEnd) (Finset.mem_sdiff.1 hv).2 t (by omega)
        ht2)
    (quorum_le_of_phase_set Sched tAwakeEnd _ C.hThird
      (roundMembers_mono S Sched (s₀ + 1 + 1) (s₀ + 1 + 1) tAwakeEnd C.hMono le_rfl hEs2).2)
    (by
      intro s' h1 h2
      have hA : anchorCW S tGAT ≤ slotStart S (s' + 1) :=
        le_trans hw0.2 (slotStart_mono S (by omega))
      exact committee_majority_of_committeeSleepiness S Sched _ s' C.hCommittees hA)
    (fun t h1 h2 => (hpAH t (by rw [Nat.add_sub_cancel] at h1; omega) (by omega)).1)
    (fun t' ht' h => hpH (C.hMono _ _ (le_trans ht' (by exact_mod_cast (show voteTime S (s₀ + 1) ≤
      supportCutoff S (s₀ + 1) by omega))) h))
    (by
      show S.P.proposer s'' ∈ roundMembers S Sched (s'' - 1 + 1)
      rw [show s'' - 1 + 1 = s'' by omega]
      exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hqH⟩)
    rfl rfl hB hB' (C.quiet hs'' B hB) (by rw [Nat.add_sub_cancel]; exact hChain)
    (by rw [Nat.add_sub_cancel]; exact hLocks) hAnchor hFrameP
  rcases h89 with hcol | ⟨hBB', hrise, -, hsave, -, -⟩
  · exfalso
    apply C.hNoCol
    rw [GoldilocksCorrectness.Proofs.View.rootCollisionAtOpening_unfold]
    refine ⟨i, le_of_lt C.hi, B, ?_, ?_⟩
    · rw [C.hs]
      exact hB
    · rw [C.hs]
      exact hcol
  · exact ⟨hBB', hrise, hsave⟩

end QuietCtx

end GoldilocksCorrectness.Proofs.Executions
