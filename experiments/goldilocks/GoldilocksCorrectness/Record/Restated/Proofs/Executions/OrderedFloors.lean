module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Boxes
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ViableAgreement
public import GoldilocksCorrectness.Proofs.Executions.Boxes
public import GoldilocksCorrectness.Proofs.Executions.ViableAgreement

@[expose] public section

/-!
# OrderedFloors, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/OrderedFloors.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: the box instances of Lemma 59 with the two
greatest chain-state heights `hMax M S.C n` ordered in place of equal, and the viable heads along
the path with ordered least viable heights. The page's routine-level theorems are the facts' fields
or have their twins in phase A.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (slotStart voteTime)

open GoldilocksCorrectness.Proofs.Routines (parent_ancestorEq)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (BoxOne BoxThree BoxTwo FrameShape hMax)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans ancestorEq_refl)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- `lem59le_frame` with `p`'s and `w`'s states read before two times `t_p` and `t_w` in place of
the start and the vote time of slot `s + 1`. The proof; the audited statement is in
`Statements/Executions/OrderedFloorStatements.lean`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: on the path from `X` to `B`'s parent past `w`'s root, a block viable at `w` is viable at
`p`, when `w`'s least viable height is at least `p`'s. `lem59le_frame` is its instance at
`t_p := slotStart S (s + 1)`, `t_w := voteTime S (s + 1)`. -/
theorem lem59le_frame_at (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t_p t_w : ℕ) (X B : Block V) (p w : V)
    (ρ_p ρ_w : Block V) (φ φ_w : Height)
    -- `p`'s frame before `t_p` has the root `ρ_p` and `head_height_floor` (the least chain-state height a viable block may have) equal to `φ`
    (hShapeP : FrameShape M (x.stateBefore t_p p) ρ_p φ)
    -- `w`'s frame before `t_w` has the root `ρ_w` and `head_height_floor` equal to `φ_w`
    (hShapeW : FrameShape M (x.stateBefore t_w w) ρ_w φ_w)
    -- `head_height_floor` at `p` is at most the one at `w`
    (hFloorLe : φ ≤ φ_w)
    -- `p`'s tree before `t_p` holds `B`'s parent
    (hParentHeld : B.parent ∈ (x.stateBefore t_p p).tree)
    -- `ρ_p` is `X` or an ancestor of `X`
    (hRXp : ρ_p.AncestorEq X) :
    ∀ Y : Block V, X.AncestorEq Y → ρ_w.AncestorEq Y → Y.AncestorEq B.parent →
      Y ∈ (M.fg_to_ac (x.stateBefore t_w w)).viable_heads →
      Y ∈ (M.fg_to_ac (x.stateBefore t_p p)).viable_heads := by
  have hInvP := (lem11_node_invariantCore_of_run M F S x R (x.stepBefore t_p) p).1
  have hInvW := (lem11_node_invariantCore_of_run M F S x R (x.stepBefore t_w) w).1
  intro Y hXY _ hYP hYw
  obtain ⟨-, -, hHp⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.lem56_frame_of_shape_of_core M F) S.C S.P S.X
    (x.stateBefore t_p p) hInvP _ _ hShapeP
  obtain ⟨-, -, hHw⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.lem56_frame_of_shape_of_core M F) S.C S.P S.X
    (x.stateBefore t_w w) hInvW _ _ hShapeW
  obtain ⟨-, -, -, hflw⟩ := (hHw Y).1 hYw
  -- `p`'s tree holds `Y`
  have hYp : Y ∈ (x.stateBefore t_p p).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ p _ Y hParentHeld hYP
  -- `p`'s finalized block is `ρ_p` or an ancestor of it (Lemma 46)
  have hFρp : (x.stateBefore t_p p).finalized.AncestorEq ρ_p := by
    rw [← hShapeP.1]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_stateBefore M F) S A x R E _ p
  have hρY : ρ_p.AncestorEq Y := ancestorEq_trans hRXp hXY
  refine (hHp Y).2 ⟨hYp, ancestorEq_trans hFρp hρY, hρY, ?_⟩
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
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `s`: the slot of the votes;
- `X`: the block the slot-`s` majority extends; `B`: the block `p` proposed at `t₁`;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `ρ_p`, `ρ_w`: the roots of `p`'s and `w`'s fork choices; `φ`, `φ_w`: their `head_height_floor` values.

Read aloud: on the path from `X` to `B`'s parent past `w`'s root, a block viable at `w` is viable
at `p`, when `head_height_floor` at `w` is at least the one at `p`.



It is the instance of `lem59le_frame_at` at `t_p := M.slotStart S.C (s + 1)`,
`t_w := M.voteTime S.C (s + 1)`. -/
theorem lem59le_frame (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (X B : Block V) (p w : V)
    (ρ_p ρ_w : Block V) (φ φ_w : Height)
    -- `p`'s frame before `t₁` has the root `ρ_p` and `head_height_floor` equal to `φ`
    (hShapeP : FrameShape M (x.stateBefore (M.slotStart S.C (s + 1)) p) ρ_p φ)
    -- `w`'s frame before `t₃` has the root `ρ_w` and `head_height_floor` equal to `φ_w`
    (hShapeW : FrameShape M (x.stateBefore (M.voteTime S.C (s + 1)) w) ρ_w φ_w)
    -- `head_height_floor` at `p` is at most the one at `w`
    (hFloorLe : φ ≤ φ_w)
    -- `p`'s tree before `t₁` holds `B`'s parent
    (hParentHeld : B.parent ∈ (x.stateBefore (M.slotStart S.C (s + 1)) p).tree)
    -- `ρ_p` is `X` or an ancestor of `X`
    (hRXp : ρ_p.AncestorEq X) :
    ∀ Y : Block V, X.AncestorEq Y → ρ_w.AncestorEq Y → Y.AncestorEq B.parent →
      Y ∈ (M.fg_to_ac (x.stateBefore (M.voteTime S.C (s + 1)) w)).viable_heads →
      Y ∈ (M.fg_to_ac (x.stateBefore (M.slotStart S.C (s + 1)) p)).viable_heads :=
  (lem59le_frame_at M F) S A x R E (M.slotStart S.C (s + 1)) (M.voteTime S.C (s + 1)) X B p w ρ_p ρ_w φ φ_w
    hShapeP hShapeW hFloorLe hParentHeld hRXp

/-- `lem59le_boxOne` with `w`'s state read at its tick to a clock value `c` in place of its
tick to the vote time of slot `s + 1`. The proof; the audited statement is in
`Statements/Executions/OrderedFloorStatements.lean`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in box 1 the least viable heights are the greatest chain-state height minus one at both
states, ordered as the two greatest chain-state heights, and the honest proposal reaches `p`'s.
`lem59le_boxOne` is its instance at `c := voteTime S (s + 1)`. -/
theorem lem59le_boxOne_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s c : ℕ) (X B : Block V) (p w : V)
    -- `w` ticks to the clock value `c` at the step `kW`
    (kW : ℕ) (hkW : x.lbl kW = Event.tick w c)
    (hBoxP : BoxOne M S.C (x.tickInput p (M.slotStart S.C (s + 1))))
    (hBoxW : BoxOne M S.C (x.tickInput w c))
    (hHmaxLe : hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) ≤
      hMax M S.C (x.tickInput w c))
    (hFw : (x.tickInput w c).finalized.AncestorEq B)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree)
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq W ∧
        hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ (M.chainStateOf S.C W).h) :
    FrameShape M (x.tickInput p (M.slotStart S.C (s + 1)))
        (x.tickInput p (M.slotStart S.C (s + 1))).finalized
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1) ∧
      FrameShape M (x.tickInput w c)
        (x.tickInput w c).finalized
        (hMax M S.C (x.tickInput w c) - 1) ∧
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤
        hMax M S.C (x.tickInput w c) - 1 ∧
      (x.tickInput w c).finalized.AncestorEq B ∧
      (∃ W ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree,
        X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq W ∧
          hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ (M.chainStateOf S.C W).h) ∧
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ (M.chainStateOf S.C B).h := by
  have ⟨iP, hlP, _⟩ := hPropose
  have hInvP := (lem11_node_invariant M F S A x R E (x.tickStep p (M.slotStart S.C (s + 1))) p
    (by rw [(tickStep_eq_of_lbl M) x E hlP]; exact E.not_mem_corrupted_of_tick hlP)).1
  have hInvW := (lem11_node_invariant M F S A x R E (x.tickStep w c) w
    (by rw [(tickStep_eq_of_lbl M) x E hkW]; exact E.not_mem_corrupted_of_tick hkW)).1
  have hP := ((GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxOne M F) S.C S.P S.X (x.tickInput p (M.slotStart S.C (s + 1))) hInvP hBoxP).2
  have hW := ((GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxOne M F) S.C S.P S.X (x.tickInput w c) hInvW hBoxW).2
  have hfl := (proposal_viable M F U) S A x R E s B p hPropose hParentIn
  rw [hP.2] at hfl
  exact ⟨hP, hW, Nat.sub_le_sub_right hHmaxLe 1, hFw, hHeadP, hfl⟩

/-- Lemma 59 in box 1 with ordered `h_max`. The proof; the audited statement is in
`Statements/Executions/OrderedFloorStatements.lean`.

It is the instance of `lem59le_boxOne_at` at `c := M.voteTime S.C (s + 1)`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in box 1 the least viable heights are the greatest chain-state height minus one at both
states, ordered as the two greatest chain-state heights, and the honest proposal reaches `p`'s. -/
theorem lem59le_boxOne (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (X B : Block V) (p w : V)
    -- `w` ticks to the vote time of slot `s + 1` at the step `kW`
    (kW : ℕ) (hkW : x.lbl kW = Event.tick w (M.voteTime S.C (s + 1)))
    (hBoxP : BoxOne M S.C (x.tickInput p (M.slotStart S.C (s + 1))))
    (hBoxW : BoxOne M S.C (x.tickInput w (M.voteTime S.C (s + 1))))
    (hHmaxLe : hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) ≤
      hMax M S.C (x.tickInput w (M.voteTime S.C (s + 1))))
    (hFw : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq B)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree)
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq W ∧
        hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ (M.chainStateOf S.C W).h) :
    FrameShape M (x.tickInput p (M.slotStart S.C (s + 1)))
        (x.tickInput p (M.slotStart S.C (s + 1))).finalized
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1) ∧
      FrameShape M (x.tickInput w (M.voteTime S.C (s + 1)))
        (x.tickInput w (M.voteTime S.C (s + 1))).finalized
        (hMax M S.C (x.tickInput w (M.voteTime S.C (s + 1))) - 1) ∧
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤
        hMax M S.C (x.tickInput w (M.voteTime S.C (s + 1))) - 1 ∧
      (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq B ∧
      (∃ W ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree,
        X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq W ∧
          hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ (M.chainStateOf S.C W).h) ∧
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ (M.chainStateOf S.C B).h :=
  (lem59le_boxOne_at M F U) S A x R E s (M.voteTime S.C (s + 1)) X B p w kW hkW hBoxP hBoxW hHmaxLe hFw hPropose
    hParentIn hHeadP

/-- `lem59le_boxTwo` with `w`'s state read at its tick to a clock value `c` in place of its
tick to the vote time of slot `s + 1`. The proof; the audited statement is in
`Statements/Executions/OrderedFloorStatements.lean`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: with `p` in box 2, the voter's least viable height is `p`'s when it is in box 2 with the
same justified block, and one more when it is in box 3 with the same greatest chain-state height;
either way its root is on `B`'s chain. `lem59le_boxTwo` is its instance at
`c := voteTime S (s + 1)`. -/
theorem lem59le_boxTwo_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s c : ℕ) (B J₀ : Block V) (p w : V)
    -- `w` ticks to the clock value `c` at the step `kW`
    (kW : ℕ) (hkW : x.lbl kW = Event.tick w c)
    (hBoxP : BoxTwo M S.C (x.tickInput p (M.slotStart S.C (s + 1))) J₀)
    (hBoxW : (BoxTwo M S.C (x.tickInput w c) J₀ ∧ J₀ ≠ Block.genesis) ∨
      (BoxThree M (x.tickInput w c) ∧
        hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) =
          hMax M S.C (x.tickInput w c) ∧
        (x.tickInput w c).finalized.AncestorEq B))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree) :
    FrameShape M (x.tickInput p (M.slotStart S.C (s + 1))) J₀
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1) ∧
      (∃ ρ_w : Block V, ∃ φ_w : Height,
        FrameShape M (x.tickInput w c) ρ_w φ_w ∧
        hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ φ_w ∧ ρ_w.AncestorEq B) ∧
      J₀.AncestorEq B.parent ∧
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ (M.chainStateOf S.C B).h := by
  have ⟨iP, hlP, _⟩ := hPropose
  have hInvP := (lem11_node_invariant M F S A x R E (x.tickStep p (M.slotStart S.C (s + 1))) p
    (by rw [(tickStep_eq_of_lbl M) x E hlP]; exact E.not_mem_corrupted_of_tick hlP)).1
  have hInvW := (lem11_node_invariant M F S A x R E (x.tickStep w c) w
    (by rw [(tickStep_eq_of_lbl M) x E hkW]; exact E.not_mem_corrupted_of_tick hkW)).1
  have hP := (GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxTwo M F) S.C S.P S.X (x.tickInput p (M.slotStart S.C (s + 1))) hInvP _ hBoxP
  -- `B`'s parent is in `p`'s viable tree, so the root `J₀` is an ancestor of it
  have hJP : J₀.AncestorEq B.parent := by
    have hR := ((GoldilocksCorrectness.Record.Statements.Routines.lem56_frame_of_shape M F) S.C S.P S.X
        (x.tickInput p (M.slotStart S.C (s + 1))) hInvP _ _ hP).1
    simp only [(GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F)] at hParentIn
    obtain ⟨-, hRB, -⟩ := hParentIn
    rw [hR] at hRB
    exact hRB
  have hfl := (proposal_viable M F U) S A x R E s B p hPropose hParentIn
  rw [hP.2] at hfl
  refine ⟨hP, ?_, hJP, hfl⟩
  rcases hBoxW with ⟨hBoxW, hJ₀⟩ | ⟨hBoxW, hHmax, hFw⟩
  · -- `w` in box 2 with `J₀`: the root `J₀` and the height `p`'s greatest chain-state height minus one
    have hW := (GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxTwo M F) S.C S.P S.X (x.tickInput w c) hInvW _ hBoxW
    -- the justified height of a state in box 2 with `J₀` is `J₀`'s chain-state height
    have hJH : ∀ (u : V) (c' : ℕ), BoxTwo M S.C (x.tickInput u c') J₀ →
        (x.tickInput u c').justifiedHeight = (M.chainStateOf S.C J₀).h := fun u c' hBox => by
      obtain ⟨-, hJH, -, -, -⟩ := (GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E (x.tickStep u c') u
      have hJ : (x.tickInput u c').justified = J₀ := hBox.2.2
      have hJH' : GoldilocksCorrectness.Record.Statements.Routines.JustifiedHeight M S.C (x.tickInput u c') := hJH
      rcases hJH' with hg | hh
      · exact absurd (hJ.symm.trans hg) hJ₀
      · rw [hJ] at hh
        exact hh.symm

    have hmax : hMax M S.C (x.tickInput w c) = hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) := by
      rw [hBoxW.1, hBoxP.1, hJH w c hBoxW, hJH p _ hBoxP]
    rw [hmax] at hW
    exact ⟨J₀, _, hW, le_refl _, ancestorEq_trans hJP (parent_ancestorEq B)⟩
  · -- `w` in box 3 with `p`'s greatest chain-state height: the root `w`'s finalized block and that height
    have hW := ((GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxThree M F) S.C S.P S.X (x.tickInput w c) hInvW hBoxW).2
    refine ⟨_, _, hW, ?_, hFw⟩
    rw [← hHmax]
    exact Nat.sub_le _ 1

/-- Lemma 59 in box 2 with the voter in box 2 or contested. The proof; the audited statement is
in `Statements/Executions/OrderedFloorStatements.lean`.

It is the instance of `lem59le_boxTwo_at` at `c := M.voteTime S.C (s + 1)`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: with `p` in box 2, the voter's least viable height is `p`'s when it is in box 2 with the
same justified block, and one more when it is in box 3 with the same greatest chain-state height;
either way its root is on `B`'s chain. -/
theorem lem59le_boxTwo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (B J₀ : Block V) (p w : V)
    -- `w` ticks to the vote time of slot `s + 1` at the step `kW`
    (kW : ℕ) (hkW : x.lbl kW = Event.tick w (M.voteTime S.C (s + 1)))
    (hBoxP : BoxTwo M S.C (x.tickInput p (M.slotStart S.C (s + 1))) J₀)
    (hBoxW : (BoxTwo M S.C (x.tickInput w (M.voteTime S.C (s + 1))) J₀ ∧ J₀ ≠ Block.genesis) ∨
      (BoxThree M (x.tickInput w (M.voteTime S.C (s + 1))) ∧
        hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) =
          hMax M S.C (x.tickInput w (M.voteTime S.C (s + 1))) ∧
        (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq B))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree) :
    FrameShape M (x.tickInput p (M.slotStart S.C (s + 1))) J₀
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1) ∧
      (∃ ρ_w : Block V, ∃ φ_w : Height,
        FrameShape M (x.tickInput w (M.voteTime S.C (s + 1))) ρ_w φ_w ∧
        hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ φ_w ∧ ρ_w.AncestorEq B) ∧
      J₀.AncestorEq B.parent ∧
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ (M.chainStateOf S.C B).h :=
  (lem59le_boxTwo_at M F U) S A x R E s (M.voteTime S.C (s + 1)) B J₀ p w kW hkW hBoxP hBoxW hPropose hParentIn

/-- `lem59le_boxThree` with `w`'s state read at its tick to a clock value `c` in place of its
tick to the vote time of slot `s + 1`. The proof; the audited statement is in
`Statements/Executions/OrderedFloorStatements.lean`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in box 3 the least viable heights are the two greatest chain-state heights, ordered, and
the honest proposal reaches `p`'s. `lem59le_boxThree` is its instance at
`c := voteTime S (s + 1)`. -/
theorem lem59le_boxThree_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s c : ℕ) (B : Block V) (p w : V)
    -- `w` ticks to the clock value `c` at the step `kW`
    (kW : ℕ) (hkW : x.lbl kW = Event.tick w c)
    (hBoxP : BoxThree M (x.tickInput p (M.slotStart S.C (s + 1))))
    (hBoxW : BoxThree M (x.tickInput w c))
    (hHmaxLe : hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) ≤
      hMax M S.C (x.tickInput w c))
    (hFw : (x.tickInput w c).finalized.AncestorEq B)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree) :
    FrameShape M (x.tickInput p (M.slotStart S.C (s + 1)))
        (x.tickInput p (M.slotStart S.C (s + 1))).finalized
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1)))) ∧
      FrameShape M (x.tickInput w c)
        (x.tickInput w c).finalized
        (hMax M S.C (x.tickInput w c)) ∧
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) ≤
        hMax M S.C (x.tickInput w c) ∧
      (x.tickInput w c).finalized.AncestorEq B ∧
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) ≤ (M.chainStateOf S.C B).h := by
  have ⟨iP, hlP, _⟩ := hPropose
  have hInvP := (lem11_node_invariant M F S A x R E (x.tickStep p (M.slotStart S.C (s + 1))) p
    (by rw [(tickStep_eq_of_lbl M) x E hlP]; exact E.not_mem_corrupted_of_tick hlP)).1
  have hInvW := (lem11_node_invariant M F S A x R E (x.tickStep w c) w
    (by rw [(tickStep_eq_of_lbl M) x E hkW]; exact E.not_mem_corrupted_of_tick hkW)).1
  have hP := ((GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxThree M F) S.C S.P S.X (x.tickInput p (M.slotStart S.C (s + 1))) hInvP hBoxP).2
  have hW := ((GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxThree M F) S.C S.P S.X (x.tickInput w c) hInvW hBoxW).2
  have hfl := (proposal_viable M F U) S A x R E s B p hPropose hParentIn
  rw [hP.2] at hfl
  exact ⟨hP, hW, hHmaxLe, hFw, hfl⟩

/-- Lemma 59 in box 3 with ordered `h_max`. The proof; the audited statement is in
`Statements/Executions/OrderedFloorStatements.lean`.

It is the instance of `lem59le_boxThree_at` at `c := M.voteTime S.C (s + 1)`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in box 3 the least viable heights are the two greatest chain-state heights, ordered, and
the honest proposal reaches `p`'s. -/
theorem lem59le_boxThree (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (B : Block V) (p w : V)
    -- `w` ticks to the vote time of slot `s + 1` at the step `kW`
    (kW : ℕ) (hkW : x.lbl kW = Event.tick w (M.voteTime S.C (s + 1)))
    (hBoxP : BoxThree M (x.tickInput p (M.slotStart S.C (s + 1))))
    (hBoxW : BoxThree M (x.tickInput w (M.voteTime S.C (s + 1))))
    (hHmaxLe : hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) ≤
      hMax M S.C (x.tickInput w (M.voteTime S.C (s + 1))))
    (hFw : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq B)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree) :
    FrameShape M (x.tickInput p (M.slotStart S.C (s + 1)))
        (x.tickInput p (M.slotStart S.C (s + 1))).finalized
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1)))) ∧
      FrameShape M (x.tickInput w (M.voteTime S.C (s + 1)))
        (x.tickInput w (M.voteTime S.C (s + 1))).finalized
        (hMax M S.C (x.tickInput w (M.voteTime S.C (s + 1)))) ∧
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) ≤
        hMax M S.C (x.tickInput w (M.voteTime S.C (s + 1))) ∧
      (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq B ∧
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) ≤ (M.chainStateOf S.C B).h :=
  (lem59le_boxThree_at M F U) S A x R E s (M.voteTime S.C (s + 1)) B p w kW hkW hBoxP hBoxW hHmaxLe hFw hPropose
    hParentIn

end GoldilocksCorrectness.Record.Proofs.Executions

