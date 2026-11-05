module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.OrderedFloors
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.OrderedFloorVotes
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# OrderedFloorStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/OrderedFloorStatements.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the facts about two frames
where `head_height_floor` at the proposer is at most `head_height_floor` at the voter, and Lemmas
20, 24 and 59 in that case. Each is the theorem of the same name of
`Record/Restated/Proofs/Executions/OrderedFloors.lean` or `OrderedFloorVotes.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (BoxOne BoxThree BoxTwo FrameShape hMax)
open GoldilocksCorrectness.Record.Statements.Routines (AnchorAt AwakeFor CountedVotes FrameShape
  ProposalCountedVotes VoterTree)
open GoldilocksCorrectness.Statements.Executions (acObject)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **The viable heads along the path, with ordered `head_height_floor` values (the least chain-state height a viable block may have).** When `p`'s frame before the time
`t_p` has the root `ρ_p` and `head_height_floor` equal to `φ`, `w`'s frame before the time `t_w` has the root `ρ_w`
and `head_height_floor` equal to `φ_w`, `φ` is at most `φ_w`, `p`'s tree before `t_p` holds `B`'s parent, and `ρ_p` is
`X` or an ancestor of `X`: then every block that is `X` or a descendant of `X`, `ρ_w` or a
descendant of `ρ_w`, and `B`'s parent or an ancestor of it, and that is a viable head at `w`, is a
viable head at `p`.

This is the direction "a viable head at `w` is one at `p`" of `viable_heads_agree_of_floor_eq`,
with its equality of the two `head_height_floor` values replaced by `φ ≤ φ_w`. The other direction does not hold: a
block whose chain-state height is at least `φ` and less than `φ_w` is a viable head at `p` and not
at `w`.

Why: `p`'s tree holds the block, as an ancestor of `B`'s parent, or that parent; `w`'s holds it,
as a viable head; both hold for it its own chain state (Lemma 11); its height is at least `φ_w`,
so at least `φ`; `ρ_p` is an ancestor of it through `X`, and so is `p`'s finalized block
(Lemma 46); so it is a viable head at `p` (Lemma 56).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `t_p`, `t_w`: the times `p`'s and `w`'s states are read;
- `X`: the block the path starts from; `B`: the block whose parent `p` holds;
- `p`, `w`: the two validators;
- `ρ_p`, `ρ_w`: the roots of `p`'s and `w`'s fork choices; `φ`, `φ_w`: their `head_height_floor` values.

Read aloud: on the path from `X` to `B`'s parent past `w`'s root, a block viable at `w` is viable
at `p`, when `head_height_floor` at `w` is at least the one at `p`.

`lem59le_frame` is its instance at `t_p := M.slotStart S.C (s + 1)`,
`t_w := M.voteTime S.C (s + 1)`. -/
theorem lem59le_frame_at (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t_p t_w : ℕ) (X B : Block V) (p w : V)
    (ρ_p ρ_w : Block V) (φ φ_w : Height)
    -- `p`'s frame before `t_p` has the root `ρ_p` and `head_height_floor` equal to `φ`
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
      Y ∈ (M.fg_to_ac (x.stateBefore t_p p)).viable_heads :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem59le_frame_at M F) S A x R E t_p t_w X B p w
    ρ_p ρ_w φ φ_w hShapeP hShapeW hFloorLe hParentHeld hRXp

/-- **The viable heads along the path, with ordered `head_height_floor` values.** When `p`'s frame before the start
`t₁` of slot `s + 1` has the root `ρ_p` and `head_height_floor` equal to `φ`, `w`'s frame before the vote time `t₃`
of slot `s + 1` has the root `ρ_w` and `head_height_floor` equal to `φ_w`, `φ` is at most `φ_w`, `p`'s tree before
`t₁` holds `B`'s parent, and `ρ_p` is `X` or an ancestor of `X`: then every block that is `X` or a
descendant of `X`, `ρ_w` or a descendant of `ρ_w`, and `B`'s parent or an ancestor of it, and that
is a viable head at `w`, is a viable head at `p`.

This is the direction "a viable head at `w` is one at `p`" of `viable_heads_agree_of_floor_eq`,
with its equality of the two `head_height_floor` values replaced by `φ ≤ φ_w`. The other direction does not hold: a
block whose chain-state height is at least `φ` and less than `φ_w` is a viable head at `p` and not
at `w`.

Why: `p`'s tree holds the block, as an ancestor of `B`'s parent, or that parent; `w`'s holds it,
as a viable head; both hold for it its own chain state (Lemma 11); its height is at least `φ_w`,
so at least `φ`; `ρ_p` is an ancestor of it through `X`, and so is `p`'s finalized block
(Lemma 46); so it is a viable head at `p` (Lemma 56).

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
  (GoldilocksCorrectness.Record.Proofs.Executions.lem59le_frame M F) S A x R E s X B p w ρ_p ρ_w φ
    φ_w hShapeP hShapeW hFloorLe hParentHeld hRXp

/-- **Lemma 59 in box 1, with ordered `h_max`.** When `p`'s state before the start `t₁` of slot
`s + 1` and `w`'s at its tick to the clock value `c` are both in box 1, `p`'s `h_max` is at
most `w`'s, `w`'s finalized block is `B` or an ancestor of `B`, `p` put `B` on the wire at its
tick at `t₁` with `B`'s parent in `p`'s viable tree, and some block of `p`'s tree on `p`'s
finalized block's chain, `X` or a descendant of `X`, has a chain-state height at least `p`'s
`h_max − 1`: then `p`'s frame has the root `p`'s finalized block and `head_height_floor` equal to `p`'s `h_max − 1`,
`w`'s has the root `w`'s finalized block and `head_height_floor` equal to `w`'s `h_max − 1`, the first `head_height_floor` value is at
most the second, and `B`'s chain-state height is at least the first.

Why: box 1 has the finalized block as its root and `h_max − 1` as its `head_height_floor` (Lemma 56); the
ordered `h_max` give ordered `head_height_floor` values; the honest proposal reaches `head_height_floor` at its proposer
(`proposal_viable`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
- `X`: the block every honest slot-`s` vote extends; `B`: the block `p` proposed;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `c`: the clock value of `w`'s tick whose input state is read; `kW`: the step of that tick.

Read aloud: in box 1 the `head_height_floor` values are `h_max − 1` at both states, ordered as the two `h_max`, and the
honest proposal reaches `p`'s.

`lem59le_boxOne` is its instance at `c := M.voteTime S.C (s + 1)`. -/
theorem lem59le_boxOne_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s c : ℕ) (X B : Block V) (p w : V)
    -- `w` ticks to the clock value `c` at the step `kW`
    (kW : ℕ) (hkW : x.lbl kW = Event.tick w c)
    -- `p`'s state before `t₁` is in box 1
    (hBoxP : BoxOne M S.C (x.tickInput p (M.slotStart S.C (s + 1))))
    -- `w`'s state at its tick to `c` is in box 1
    (hBoxW : BoxOne M S.C (x.tickInput w c))
    -- `p`'s `h_max` before `t₁` is at most `w`'s at its tick to `c`
    (hHmaxLe : hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) ≤
      hMax M S.C (x.tickInput w c))
    -- `w`'s finalized block at its tick to `c` is `B` or an ancestor of `B`
    (hFw : (x.tickInput w c).finalized.AncestorEq B)
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `B`'s parent is in the viable tree of `p`'s frame before `t₁`
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree)
    -- some accepted block of `p` on its finalized block's chain, `X` or a descendant of `X`,
    -- has a chain-state height at least `p`'s greatest chain-state height minus one
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
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ (M.chainStateOf S.C B).h :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem59le_boxOne_at M F U) S A x R E s c X B p w kW hkW
    hBoxP hBoxW hHmaxLe hFw hPropose hParentIn hHeadP

/-- **Lemma 59 in box 1, with ordered `h_max`.** When `p`'s state before the start `t₁` of slot
`s + 1` and `w`'s at its tick to the vote time `t₃` of slot `s + 1` are both in box 1, `p`'s `h_max` is at
most `w`'s, `w`'s finalized block is `B` or an ancestor of `B`, `p` put `B` on the wire at its
tick at `t₁` with `B`'s parent in `p`'s viable tree, and some block of `p`'s tree on `p`'s
finalized block's chain, `X` or a descendant of `X`, has a chain-state height at least `p`'s
`h_max − 1`: then `p`'s frame has the root `p`'s finalized block and `head_height_floor` equal to `p`'s `h_max − 1`,
`w`'s has the root `w`'s finalized block and `head_height_floor` equal to `w`'s `h_max − 1`, the first `head_height_floor` value is at
most the second, and `B`'s chain-state height is at least the first.

This is `lem59_boxOne` with its hypothesis "the two states have the same `h_max`" replaced by
"`p`'s `h_max` is at most `w`'s".

Why: box 1 has the finalized block as its root and `h_max − 1` as its `head_height_floor` (Lemma 56); the
ordered `h_max` give ordered `head_height_floor` values; the honest proposal reaches `head_height_floor` at its proposer
(`proposal_viable`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
- `X`: the block every honest slot-`s` vote extends; `B`: the block `p` proposed;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`.

Read aloud: in box 1 the `head_height_floor` values are `h_max − 1` at both states, ordered as the two `h_max`, and the
honest proposal reaches `p`'s.



It is the instance of `lem59le_boxOne_at` at `c := M.voteTime S.C (s + 1)`. -/
theorem lem59le_boxOne (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (X B : Block V) (p w : V)
    -- `w` ticks to the vote time of slot `s + 1` at the step `kW`
    (kW : ℕ) (hkW : x.lbl kW = Event.tick w (M.voteTime S.C (s + 1)))
    -- `p`'s state before `t₁` is in box 1
    (hBoxP : BoxOne M S.C (x.tickInput p (M.slotStart S.C (s + 1))))
    -- `w`'s state at its tick to `t₃` is in box 1
    (hBoxW : BoxOne M S.C (x.tickInput w (M.voteTime S.C (s + 1))))
    -- `p`'s `h_max` before `t₁` is at most `w`'s at its tick to `t₃`
    (hHmaxLe : hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) ≤
      hMax M S.C (x.tickInput w (M.voteTime S.C (s + 1))))
    -- `w`'s finalized block at its tick to `t₃` is `B` or an ancestor of `B`
    (hFw : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq B)
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `B`'s parent is in the viable tree of `p`'s frame before `t₁`
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree)
    -- some accepted block of `p` on its finalized block's chain, `X` or a descendant of `X`,
    -- has a chain-state height at least `p`'s greatest chain-state height minus one
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
  (GoldilocksCorrectness.Record.Proofs.Executions.lem59le_boxOne M F U) S A x R E s X B p w kW hkW hBoxP
    hBoxW hHmaxLe hFw hPropose hParentIn hHeadP

/-- **Lemma 59 in box 2, with the voter in box 2 or contested.** When `p`'s state before the start
`t₁` of slot `s + 1` is in box 2 with the justified block `J₀`, and `w`'s at its tick to the clock value `c` is
in box 2 with `J₀`, other than the genesis block, or is contested with `p`'s `h_max` and its
finalized block `B` or an ancestor of `B`; and `p` put `B` on the wire at its tick at `t₁` with
`B`'s parent in `p`'s viable tree: then `p`'s frame has the root `J₀` and `head_height_floor` equal to `p`'s
`h_max − 1`, `w`'s frame has a root that is `B` or an ancestor of `B` and a `head_height_floor` value at least the one at `p`,
`J₀` is `B`'s parent or an ancestor of it, and `B`'s chain-state height is at least `head_height_floor` at `p`.

Why: box 2 has `J₀` as its root and `h_max − 1` as its `head_height_floor` (Lemma 56); when `w` is in box 2 with
`J₀`, the two `h_max` are `J₀`'s chain-state height plus one (Lemma 57), so the `head_height_floor` values are equal,
and `J₀` is an ancestor of `B` through `B`'s parent, which the viable tree places past the root;
when `w` is contested, its root is its finalized block and its `head_height_floor` its `h_max` (Lemma 56), which
is `p`'s; the honest proposal reaches `head_height_floor` at its proposer (`proposal_viable`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
- `B`: the block `p` proposed; `J₀`: the justified block;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `c`: the clock value of `w`'s tick whose input state is read; `kW`: the step of that tick.

Read aloud: with `p` in box 2, `head_height_floor` at the voter is the one at `p` when it is in box 2 with the same
justified block, and one more when it is contested with the same `h_max`; either way its root is
on `B`'s chain.

`lem59le_boxTwo` is its instance at `c := M.voteTime S.C (s + 1)`. -/
theorem lem59le_boxTwo_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s c : ℕ) (B J₀ : Block V) (p w : V)
    -- `w` ticks to the clock value `c` at the step `kW`
    (kW : ℕ) (hkW : x.lbl kW = Event.tick w c)
    -- `p`'s state before `t₁` is in box 2 with the justified block `J₀`
    (hBoxP : BoxTwo M S.C (x.tickInput p (M.slotStart S.C (s + 1))) J₀)
    -- `w`'s state at its tick to `c` is in box 2 with `J₀`, and `J₀` is not the genesis block; or it is
    -- contested, with `p`'s `h_max`, and its finalized block is `B` or an ancestor of `B`
    (hBoxW : (BoxTwo M S.C (x.tickInput w c) J₀ ∧ J₀ ≠ Block.genesis) ∨
      (BoxThree M (x.tickInput w c) ∧
        hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) =
          hMax M S.C (x.tickInput w c) ∧
        (x.tickInput w c).finalized.AncestorEq B))
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `B`'s parent is in the viable tree of `p`'s frame before `t₁`
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree) :
    FrameShape M (x.tickInput p (M.slotStart S.C (s + 1))) J₀
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1) ∧
      (∃ ρ_w : Block V, ∃ φ_w : Height,
        FrameShape M (x.tickInput w c) ρ_w φ_w ∧
        hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ φ_w ∧ ρ_w.AncestorEq B) ∧
      J₀.AncestorEq B.parent ∧
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ (M.chainStateOf S.C B).h :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem59le_boxTwo_at M F U) S A x R E s c B J₀ p w kW hkW
    hBoxP hBoxW hPropose hParentIn

/-- **Lemma 59 in box 2, with the voter in box 2 or contested.** When `p`'s state before the start
`t₁` of slot `s + 1` is in box 2 with the justified block `J₀`, and `w`'s at its tick to the vote time `t₃`
of slot `s + 1` is in box 2 with `J₀`, other than the genesis block, or is contested with `p`'s
`h_max` and its finalized block `B` or an ancestor of `B`; and `p` put `B` on the wire at its tick
at `t₁` with `B`'s parent in `p`'s viable tree: then `p`'s frame has the root `J₀` and `head_height_floor` equal to
`p`'s `h_max − 1`, `w`'s frame has a root that is `B` or an ancestor of `B` and a `head_height_floor` value at least
`p`'s, `J₀` is `B`'s parent or an ancestor of it, and `B`'s chain-state height is at least
`head_height_floor` at `p`.

This is `lem59_boxTwo` with `w`'s state allowed to be contested with `p`'s `h_max`, in which case
its `head_height_floor` is the one at `p` plus one.

Why: box 2 has `J₀` as its root and `h_max − 1` as its `head_height_floor` (Lemma 56); when `w` is in box 2 with
`J₀`, the two `h_max` are `J₀`'s chain-state height plus one (Lemma 57), so the `head_height_floor` values are equal,
and `J₀` is an ancestor of `B` through `B`'s parent, which the viable tree places past the root;
when `w` is contested, its root is its finalized block and its `head_height_floor` its `h_max` (Lemma 56), which
is `p`'s; the honest proposal reaches `head_height_floor` at its proposer (`proposal_viable`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
- `B`: the block `p` proposed; `J₀`: the justified block;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`.

Read aloud: with `p` in box 2, `head_height_floor` at the voter is the one at `p` when it is in box 2 with the same
justified block, and one more when it is contested with the same `h_max`; either way its root is
on `B`'s chain.



It is the instance of `lem59le_boxTwo_at` at `c := M.voteTime S.C (s + 1)`. -/
theorem lem59le_boxTwo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (B J₀ : Block V) (p w : V)
    -- `w` ticks to the vote time of slot `s + 1` at the step `kW`
    (kW : ℕ) (hkW : x.lbl kW = Event.tick w (M.voteTime S.C (s + 1)))
    -- `p`'s state before `t₁` is in box 2 with the justified block `J₀`
    (hBoxP : BoxTwo M S.C (x.tickInput p (M.slotStart S.C (s + 1))) J₀)
    -- `w`'s state at its tick to `t₃` is in box 2 with `J₀`, and `J₀` is not the genesis block; or it is
    -- contested, with `p`'s `h_max`, and its finalized block is `B` or an ancestor of `B`
    (hBoxW : (BoxTwo M S.C (x.tickInput w (M.voteTime S.C (s + 1))) J₀ ∧ J₀ ≠ Block.genesis) ∨
      (BoxThree M (x.tickInput w (M.voteTime S.C (s + 1))) ∧
        hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) =
          hMax M S.C (x.tickInput w (M.voteTime S.C (s + 1))) ∧
        (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq B))
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `B`'s parent is in the viable tree of `p`'s frame before `t₁`
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree) :
    FrameShape M (x.tickInput p (M.slotStart S.C (s + 1))) J₀
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1) ∧
      (∃ ρ_w : Block V, ∃ φ_w : Height,
        FrameShape M (x.tickInput w (M.voteTime S.C (s + 1))) ρ_w φ_w ∧
        hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ φ_w ∧ ρ_w.AncestorEq B) ∧
      J₀.AncestorEq B.parent ∧
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ (M.chainStateOf S.C B).h :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem59le_boxTwo M F U) S A x R E s B J₀ p w kW hkW hBoxP
    hBoxW hPropose hParentIn

/-- **Lemma 59 in box 3, with ordered `h_max`.** When `p`'s state before the start `t₁` of slot
`s + 1` and `w`'s at its tick to the clock value `c` are both contested, `p`'s `h_max` is at
most `w`'s, `w`'s finalized block is `B` or an ancestor of `B`, and `p` put `B` on the wire at its
tick at `t₁` with `B`'s parent in `p`'s viable tree: then `p`'s frame has the root `p`'s finalized
block and `head_height_floor` equal to `p`'s `h_max`, `w`'s has the root `w`'s finalized block and `head_height_floor` equal to `w`'s
`h_max`, the first `head_height_floor` value is at most the second, and `B`'s chain-state height is at least the
first.

Why: box 3 has the finalized block as its root and `h_max` as its `head_height_floor` (Lemma 56); the honest
proposal reaches `head_height_floor` at its proposer (`proposal_viable`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
- `B`: the block `p` proposed;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `c`: the clock value of `w`'s tick whose input state is read; `kW`: the step of that tick.

Read aloud: in box 3 the `head_height_floor` values are the two `h_max`, ordered, and the honest proposal reaches
`p`'s.

`lem59le_boxThree` is its instance at `c := M.voteTime S.C (s + 1)`. -/
theorem lem59le_boxThree_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s c : ℕ) (B : Block V) (p w : V)
    -- `w` ticks to the clock value `c` at the step `kW`
    (kW : ℕ) (hkW : x.lbl kW = Event.tick w c)
    -- `p`'s state before `t₁` is contested
    (hBoxP : BoxThree M (x.tickInput p (M.slotStart S.C (s + 1))))
    -- `w`'s state at its tick to `c` is contested
    (hBoxW : BoxThree M (x.tickInput w c))
    -- `p`'s `h_max` before `t₁` is at most `w`'s at its tick to `c`
    (hHmaxLe : hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) ≤
      hMax M S.C (x.tickInput w c))
    -- `w`'s finalized block at its tick to `c` is `B` or an ancestor of `B`
    (hFw : (x.tickInput w c).finalized.AncestorEq B)
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `B`'s parent is in the viable tree of `p`'s frame before `t₁`
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
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) ≤ (M.chainStateOf S.C B).h :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem59le_boxThree_at M F U) S A x R E s c B p w kW hkW
    hBoxP hBoxW hHmaxLe hFw hPropose hParentIn

/-- **Lemma 59 in box 3, with ordered `h_max`.** When `p`'s state before the start `t₁` of slot
`s + 1` and `w`'s at its tick to the vote time `t₃` of slot `s + 1` are both contested, `p`'s `h_max` is at
most `w`'s, `w`'s finalized block is `B` or an ancestor of `B`, and `p` put `B` on the wire at its
tick at `t₁` with `B`'s parent in `p`'s viable tree: then `p`'s frame has the root `p`'s finalized
block and `head_height_floor` equal to `p`'s `h_max`, `w`'s has the root `w`'s finalized block and `head_height_floor` equal to `w`'s
`h_max`, the first `head_height_floor` value is at most the second, and `B`'s chain-state height is at least the
first.

This is `lem59_boxThree` with its hypothesis "the two states have the same `h_max`" replaced by
"`p`'s `h_max` is at most `w`'s".

Why: box 3 has the finalized block as its root and `h_max` as its `head_height_floor` (Lemma 56); the honest
proposal reaches `head_height_floor` at its proposer (`proposal_viable`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
- `B`: the block `p` proposed;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`.

Read aloud: in box 3 the `head_height_floor` values are the two `h_max`, ordered, and the honest proposal reaches
`p`'s.



It is the instance of `lem59le_boxThree_at` at `c := M.voteTime S.C (s + 1)`. -/
theorem lem59le_boxThree (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (B : Block V) (p w : V)
    -- `w` ticks to the vote time of slot `s + 1` at the step `kW`
    (kW : ℕ) (hkW : x.lbl kW = Event.tick w (M.voteTime S.C (s + 1)))
    -- `p`'s state before `t₁` is contested
    (hBoxP : BoxThree M (x.tickInput p (M.slotStart S.C (s + 1))))
    -- `w`'s state at its tick to `t₃` is contested
    (hBoxW : BoxThree M (x.tickInput w (M.voteTime S.C (s + 1))))
    -- `p`'s `h_max` before `t₁` is at most `w`'s at its tick to `t₃`
    (hHmaxLe : hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) ≤
      hMax M S.C (x.tickInput w (M.voteTime S.C (s + 1))))
    -- `w`'s finalized block at its tick to `t₃` is `B` or an ancestor of `B`
    (hFw : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq B)
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `B`'s parent is in the viable tree of `p`'s frame before `t₁`
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
  (GoldilocksCorrectness.Record.Proofs.Executions.lem59le_boxThree M F U) S A x R E s B p w kW hkW hBoxP
    hBoxW hHmaxLe hFw hPropose hParentIn

/-! ## Lemmas 20, 24 and 59 with `head_height_floor` at `p` at most at `w`

The audited statements of Lemmas 20, 24 and 59 when `head_height_floor` at the proposer `p` (its FG
state before the start `t₁` of slot `s + 1`) is at most `head_height_floor` at the voter `w` (its
FG state before the vote time `t₃` of slot `s + 1`), each with a hypothesis on `B`'s parent in place
of the same hypothesis on `B`, proved in
`GoldilocksCorrectness/Proofs/Executions/OrderedFloorVotes.lean`:

- `lem20le_goldfish_vote_names_honest_proposal`: along the path, a viable head at `w` is one at
  `p`, and `B`'s parent is a viable head at `w` when it is one at `p`;
- `lem24le_goldfish_vote_names_honest_proposal_composed`: `B`'s parent passes `w`'s viability
  test;
- `lem59le_goldfish_vote_names_honest_proposal_frame`: `head_height_floor` at `w` is at most the
  chain-state height of `B`'s parent.


-/

open GoldilocksCorrectness.Statements.Routines (expireLocks)

/-- **Lemma 20 with `head_height_floor` at `p` at most at `w`.** Under the hypotheses of Lemma 20
(`lem20_goldfish_vote_names_honest_proposal`) other than its agreement of the viable heads, and:
along the path from `X` to `B`'s parent, on the blocks that have the root of `w`'s fork choice as
an ancestor (or are that root), a viable head at `w` is a viable head at `p`; and `B`'s parent,
when the root of `w`'s fork choice is an ancestor of it (or it), is a viable head at `w` when it is
one at `p` — then `w`'s vote names `B`.

Why: as Lemma 20. From the shared block on, the two walks see the same scores; on a child of a
path block that is a viable head at `w`, the two eligibility tests agree; on a child of a path
block that is not a viable head at `w`, `w`'s test accepts it; so `w`'s test accepts every block
`p`'s accepts, and Lemma 9 with ordered tests (`lem9le_walk_ends_at_proposal_of_shared_block`)
ends `w`'s walk at `B`. At `B`'s parent, a child `w` accepts and `p` refuses would need `B`'s
parent viable at `p` and not at `w`, which the last hypothesis excludes.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `X`: the block every vote of `Hs` extends; `B`: the block `p` proposed at the start of slot
  `s + 1`;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`.

Read aloud: Lemma 20 holds when, along the path from `X` to `B`'s parent past the root of `w`'s
fork choice, every viable head at `w` is one at `p`, and `B`'s parent, if a viable head at `p`, is
one at `w`.



Roots name blocks until the later of the real times of `p`'s and `w`'s own ticks to `M.supportCutoff S.C s`: the
bounds of the two Lemma 12 calls at slot `s` the proof passes the premise to, as Lemma 20's. -/
theorem lem20le_goldfish_vote_names_honest_proposal (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the later of the real times of `p`'s and `w`'s own ticks to the support cutoff of
    -- slot `s`
    (hRoots : RootsNameBlocksUntil M A x (max (x.time (x.tickStep p (M.supportCutoff S.C s)))
      (x.time (x.tickStep w (M.supportCutoff S.C s)))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- the slot-`s` votes of `Hs` for `X`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ X.AncestorEq (H u))
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes_w support_w →
      M.voters_count votes_w < 2 * Hs.card)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the proposer `p` and the voter `w` each tick to the support cutoff of slot `s` at a step `kR` and are active at
    -- every step from the sync fact's read time `supportCutoff s − max (2 * Δ S) Δs` up to `kR`
    (hp : ∃ kR : ℕ, x.lbl kR = Event.tick p (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → p ∈ A.active j)
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → w ∈ A.active j)
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `w`'s tick at `t₃` put `vote` on the wire
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    -- `w` holds `B` before its vote
    (hBw : B ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree)
    -- some block of `p`'s frame tree before `t₁` that is `X` or a descendant of `X` is a viable
    -- head
    (hF3p : ∃ W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree,
      W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads ∧ X.AncestorEq W)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (M.get_anchor (x.tickInput p (M.slotStart S.C (s + 1)))
      ((M.slotStart S.C (s + 1) : ℕ) : Int)).AncestorEq X)
    -- every live lock entry `w`'s revocation leaves is on `B` or an ancestor of `B`
    (hLocksW : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `B` is a viable head at `w`
    (hBViable : B ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads)
    -- along the path from `X` to `B`'s parent, on the blocks that have the root of `w`'s fork
    -- choice as an ancestor (or are that root), a viable head at `w` is one at `p`
    (hViableLe : ∀ Y : Block V, X.AncestorEq Y →
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq Y →
      Y.AncestorEq B.parent →
      Y ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads →
      Y ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads)
    -- `B`'s parent, when the root of `w`'s fork choice is an ancestor of it (or it), is a viable
    -- head at `w` when it is one at `p`
    (hViableEnd :
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq B.parent →
      B.parent ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads →
      B.parent ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads)
    -- the two validators count alike: the same score on every child of a block from `X` to
    -- `B`'s parent that has the root of `w`'s fork choice as an ancestor (or is that root), the
    -- same number of voters
    (hCount : ∀ votes_p support_p votes_w support_w : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput p (M.slotStart S.C (s + 1))) s votes_p support_p →
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes_w support_w →
      (∀ Y : Block V, X.AncestorEq Y →
        (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq Y →
        Y.AncestorEq B.parent →
        ∀ D : Block V, D.parent? = some Y → ∃ n : ℕ,
          goldfish_score (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))) votes_p
            support_p s D = .ok n ∧
          goldfish_score (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) votes_w
            support_w s D = .ok n) ∧
      M.voters_count votes_p = M.voters_count votes_w)
    -- every child in `w`'s viable tree of a block from `X` to `B`'s parent that has the root of
    -- `w`'s fork choice as an ancestor (or is that root), other than `B`, that `w`'s eligibility
    -- test accepts, is in `p`'s viable tree
    (hChild : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes_w support_w →
      ∀ Y : Block V, X.AncestorEq Y →
        (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq Y →
        Y.AncestorEq B.parent →
        ∀ D ∈ M.viable_tree (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1))))
            (VoterTree M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1)),
          D.parent? = some Y → D ≠ B →
          goldfish_eligible S.C (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1))))
            ((M.voteTime S.C (s + 1) : ℕ) : Int) votes_w support_w s D = .ok true →
          D ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
            (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree) :
    vote.head = B.root :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem20le_goldfish_vote_names_honest_proposal M F U) S A x R
    GST s Hs H X B p w vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs hVoters hHold hp hw hPropose hSend hBw hF3p
    hApX hLocksW hBViable hViableLe hViableEnd hCount hChild

/-- **Lemma 24 with `head_height_floor` at `p` at most at `w`.** Under the hypotheses of Lemma 24
(`lem24_goldfish_vote_names_honest_proposal_composed`) other than "`B` passes `w`'s viability
test" and "`head_height_floor` at `p` equals `head_height_floor` at `w`", and: `B`'s parent passes
`w`'s viability test (`is_viable`: its chain-state height is at least `head_height_floor` at `w`);
and `head_height_floor` at `p` is at most `head_height_floor` at `w` — then `vote`'s head is the
root of `B`.

Why: as Lemma 24, with Lemma 20 in the form `lem20le_goldfish_vote_names_honest_proposal`. `w`
holds `B` (Lemmas 22a and 22) and so `B`'s parent; both have their own chain states (Lemma 11),
and heights grow along ancestry (Lemma 47 (d)), so `B` passes `w`'s viability test too and is a
viable head at `w`. Along the path, a viable head at `w` reaches `head_height_floor` at `w`, so at
`p`, and is one at `p`; `B`'s parent is a viable head at `w` whenever the root of `w`'s fork choice
is an ancestor of it.

The proposer's window `hp` starts `max (Δ S) Δs` before the support cutoff of slot `s` and ends at the start of
slot `s + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `X`: the block every vote of `Hs` extends; `B`: the block `p` proposed at the start of slot
  `s + 1`;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`.

Read aloud: Lemma 24 holds when `head_height_floor` at the voter is at least at the proposer, and
the proposal's parent passes the voter's viability test.



Roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`: Lemma 22 and Lemma 23, which the proof calls, take
blocks as held up to `w`'s vote time of slot `s + 1`;
`lem20le_goldfish_vote_names_honest_proposal` and `child_mem_proposer_viable_tree` read earlier.

The activity rows: `p` and `w` are each active from a tick to
a clock value at most `tStart`, more than both clock bounds before the read time
`M.supportCutoff S.C s - max (2 * Δ S) Δs` at slot `s`, up to their own ticks to the start and to the
vote time of slot `s + 1`; each voter of `Hs` is active through the sync delay after that read time
(`hHold`), and `p` through the sync delay after `max (Δ S) Δs` before the start of slot `s + 1`
(`hHoldP`); the voters of `Hs` are outside the adversary set at `w`'s tick to the vote time of slot
`s + 1`. -/
theorem lem24le_goldfish_vote_names_honest_proposal_composed (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`
    --
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- the slot-`s` votes of `Hs` for `X`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ X.AncestorEq (H u))
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes_w support_w →
      M.voters_count votes_w < 2 * Hs.card)
    -- each voter of `Hs` is active through the sync delay after the read time at slot `s`
    --
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `p`'s and `w`'s windows start at `tStart`, more than `ΔClockAhead + ΔClockBehind` before the read
    -- time at slot `s`
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ))
    -- `p` is active from a tick to a clock value at most `tStart` up to its tick to the start of slot
    -- `s + 1`
    (hp : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C (s + 1)))
    -- `p` is active through the sync delay after `max (Δ S) Δs` before the start of slot `s + 1`
    --
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` is active from a tick to a clock value at most `tStart` up to its tick to the vote time of
    -- slot `s + 1`
    (hw : w ∈ A.activeThroughoutToTick x tStart (M.voteTime S.C (s + 1)))
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `w`'s tick at `t₃` put `vote` on the wire
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    -- `w`'s tree before `t₃` holds no slot-`(s + 1)` block other than `B`
    (hOnly : ∀ B' ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree, B'.slot = s + 1 → B' = B)
    -- no block of `p`'s tree before `t₁` has `B`'s root
    (hRootNew : ∀ B' ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree, B'.root ≠ B.root)
    -- some block of `p`'s frame tree before `t₁` that is `X` or a descendant of `X` is a viable
    -- head
    (hF3p : ∃ W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree,
      W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads ∧ X.AncestorEq W)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (M.get_anchor (x.tickInput p (M.slotStart S.C (s + 1)))
      ((M.slotStart S.C (s + 1) : ℕ) : Int)).AncestorEq X)
    -- the root of `w`'s fork choice is `B` or an ancestor of `B`
    (hF2w : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq B)
    -- every live lock entry `w`'s revocation leaves is on `B` or an ancestor of `B`
    (hLocksW : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `B`'s parent passes `w`'s viability test
    (hParentViable : M.is_viable (x.tickInput w (M.voteTime S.C (s + 1))) B.parent = true)
    -- `head_height_floor` at `p` is at most `head_height_floor` at `w`
    (hFloorLe : M.head_height_floor (x.tickInput p (M.slotStart S.C (s + 1))) ≤
      M.head_height_floor (x.tickInput w (M.voteTime S.C (s + 1)))) :
    vote.head = B.root :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem24le_goldfish_vote_names_honest_proposal_composed M F U)
    S A x R GST s Hs H X B p w vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs hVoters
    hHold tStart htStart hp hHoldP hw hPropose hSend hOnly hRootNew hF3p hApX hF2w hLocksW hParentViable hFloorLe

/-- **Lemma 59 with `head_height_floor` at `p` at most at `w`.** Under the hypotheses of Lemma 59
(`lem59_goldfish_vote_names_honest_proposal_frame`) with `w`'s frame shape at `φ_w` in place of
`φ`, and with "`B`'s chain-state height is at least `φ`" replaced by: `φ ≤ φ_w`, and `φ_w`
is at most the chain-state height of `B`'s parent — then `w`'s vote names `B`. Here `φ` is
`head_height_floor` at `p` and `φ_w` is `head_height_floor` at `w`, as the two frame shapes say.

Why: as Lemma 59, with Lemma 24 in the form `lem24le_goldfish_vote_names_honest_proposal_composed`.
`w` holds `B` (Lemmas 22a and 22) and so `B`'s parent, with its own chain state (Lemma 11), so
`B`'s parent passes `w`'s viability test (Lemma 56); the two frame shapes give the two
`head_height_floor` as `φ` and `φ_w`.

The proposer's window `hp` starts `max (Δ S) Δs` before the support cutoff of slot `s` and ends at the start of
slot `s + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `X`: the block every vote of `Hs` extends; `B`: the block `p` proposed at the start of slot
  `s + 1`;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`;
- `ρ_p`, `ρ_w`: the roots of `p`'s and `w`'s fork choices; `φ`, `φ_w`: `head_height_floor` at `p`
  and at `w`.

Read aloud: when `head_height_floor` at the voter is at least at the proposer and at most the
height of the proposal's parent, the voter's vote names the proposal.



Roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`: Lemma 22 and
`lem24le_goldfish_vote_names_honest_proposal_composed`, which the proof calls, take blocks as
held up to `w`'s vote time of slot `s + 1`.

The activity rows: `p` and `w` are each active from a tick to
a clock value at most `tStart`, more than both clock bounds before the read time
`M.supportCutoff S.C s - max (2 * Δ S) Δs` at slot `s`, up to their own ticks to the start and to the
vote time of slot `s + 1`; each voter of `Hs` is active through the sync delay after that read time
(`hHold`), and `p` through the sync delay after `max (Δ S) Δs` before the start of slot `s + 1`
(`hHoldP`); the voters of `Hs` are outside the adversary set at `w`'s tick to the vote time of slot
`s + 1`. -/
theorem lem59le_goldfish_vote_names_honest_proposal_frame (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V) (ρ_p ρ_w : Block V) (φ φ_w : Height)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`
    --
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- the slot-`s` votes of `Hs` for `X`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ X.AncestorEq (H u))
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes_w support_w →
      M.voters_count votes_w < 2 * Hs.card)
    -- each voter of `Hs` is active through the sync delay after the read time at slot `s`
    --
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `p`'s and `w`'s windows start at `tStart`, more than `ΔClockAhead + ΔClockBehind` before the read
    -- time at slot `s`
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ))
    -- `p` is active from a tick to a clock value at most `tStart` up to its tick to the start of slot
    -- `s + 1`
    (hp : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C (s + 1)))
    -- `p` is active through the sync delay after `max (Δ S) Δs` before the start of slot `s + 1`
    --
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` is active from a tick to a clock value at most `tStart` up to its tick to the vote time of
    -- slot `s + 1`
    (hw : w ∈ A.activeThroughoutToTick x tStart (M.voteTime S.C (s + 1)))
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `w`'s tick at `t₃` put `vote` on the wire
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    -- `w`'s tree before `t₃` holds no slot-`(s + 1)` block other than `B`
    (hOnly : ∀ B' ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree, B'.slot = s + 1 → B' = B)
    -- no block of `p`'s tree before `t₁` has `B`'s root
    (hRootNew : ∀ B' ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree, B'.root ≠ B.root)
    -- `p`'s frame before `t₁` has the root `ρ_p` and `head_height_floor` `φ`
    (hShapeP : FrameShape M (x.tickInput p (M.slotStart S.C (s + 1))) ρ_p φ)
    -- `w`'s frame before `t₃` has the root `ρ_w` and `head_height_floor` `φ_w`
    (hShapeW : FrameShape M (x.tickInput w (M.voteTime S.C (s + 1))) ρ_w φ_w)
    -- `φ` is at most `φ_w`
    (hFloorLe : φ ≤ φ_w)
    -- some block of `p`'s tree that is `X` or a descendant of `X`, and `ρ_p` or a descendant of
    -- `ρ_p`, has a chain-state height at least `φ`
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree,
      X.AncestorEq W ∧ ρ_p.AncestorEq W ∧ φ ≤ (M.chainStateOf S.C W).h)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (M.get_anchor (x.tickInput p (M.slotStart S.C (s + 1)))
      ((M.slotStart S.C (s + 1) : ℕ) : Int)).AncestorEq X)
    -- `ρ_w` is `B` or an ancestor of `B`
    (hRootW : ρ_w.AncestorEq B)
    -- every live lock entry `w`'s revocation leaves is on `B` or an ancestor of `B`
    (hLocksW : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `φ_w` is at most the chain-state height of `B`'s parent
    (hParentHeight : φ_w ≤ (M.chainStateOf S.C B.parent).h) :
    vote.head = B.root :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem59le_goldfish_vote_names_honest_proposal_frame M F U)
    S A x R GST s Hs H X B p w vote ρ_p ρ_w φ φ_w E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner
    hGST hHs hVoters hHold tStart htStart hp hHoldP hw hPropose hSend hOnly hRootNew hShapeP hShapeW hFloorLe hHeadP hApX hRootW
    hLocksW hParentHeight

end GoldilocksCorrectness.Record.Statements.Executions

