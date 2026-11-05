module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ProposalWalk
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ReadingPoints
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma12
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Relay
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Invariants
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFactsViableTree
public import GoldilocksCorrectness.Proofs.Routines.WalkEnd
public import GoldilocksCorrectness.Proofs.Executions.Invariants
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Executions.ProposalWalk
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Proofs.Executions.Relay
public import GoldilocksCorrectness.Proofs.Routines.Merge
public import GoldilocksCorrectness.Proofs.Routines.Blocks
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# ViableAgreement, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/ViableAgreement.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the proposer of slot `s + 1` and its
voter agree on the viable heads along the path from `X` to `B`'s parent, and every child in the
voter's viable tree of a block of that path, other than `B`, is in the proposer's viable tree. The
page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq viewFreeze_cast viewFreeze_eq
  voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (parent_ancestorEq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (ChainStatesComputed VoterTree)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_antisymm
  compatible_iff mem_voter_block_tree_iff ancestorEq_of_parent? ancestorEq_parent_of_ne
  depth_of_parent?)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- The proposer `p` of slot `s + 1` and its voter `w` agree on the viable heads along the path from
`X` to `B`'s parent, when their `head_height_floor` values (the least chain-state height a viable block may have) are equal. If `p`'s tree before the start `t₁` of slot
`s + 1` holds `B`'s parent, `w`'s tree before the vote time `t₃` of slot `s + 1` holds `B`, the
finalized block and the root of the fork choice of `p`'s node state are `X` or ancestors of `X`,
and the two node states
have the same least viable height (`head_height_floor`), then every block that is `X` or a
descendant of `X`, the root of `w`'s fork choice or a descendant of it, and `B`'s parent or an
ancestor of it, is a viable head at `p` exactly when it is one at `w`.





The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `s`: the slot of the votes;
- `X`: the block the slot-`s` majority extends; `B`: the block `p` proposed at `t₁`;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`; `hp`, `hw`: `p` and `w` are
  outside the adversary set in the configurations read.

Read aloud: on the path from `X` to `B`'s parent, past the root of the voter's fork choice, the
proposer and the voter see the same viable heads, when their least viable heights are equal. -/
theorem viable_heads_agree_of_floor_eq (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (X B : Block V) (p w : V)
    (hParentHeld : B.parent ∈ (x.stateBefore (M.slotStart S.C (s + 1)) p).tree)
    (hBw : B ∈ (x.stateBefore (M.voteTime S.C (s + 1)) w).tree)
    (hFXp : (x.stateBefore (M.slotStart S.C (s + 1)) p).finalized.AncestorEq X)
    (hRXp : (M.fg_to_ac (x.stateBefore (M.slotStart S.C (s + 1)) p)).fc_root.AncestorEq X)
    (hFloor : M.head_height_floor (x.stateBefore (M.slotStart S.C (s + 1)) p) =
      M.head_height_floor (x.stateBefore (M.voteTime S.C (s + 1)) w))
    -- `p` is outside the adversary set in the configuration in force at the start of slot `s + 1`
    (hp : p ∉ A.corrupted (x.stepBefore (M.slotStart S.C (s + 1))))
    -- `w` is outside the adversary set in the configuration in force at the vote time of slot `s + 1`
    (hw : w ∉ A.corrupted (x.stepBefore (M.voteTime S.C (s + 1)))) :
    ∀ Y : Block V, X.AncestorEq Y →
      (M.fg_to_ac (x.stateBefore (M.voteTime S.C (s + 1)) w)).fc_root.AncestorEq Y →
      Y.AncestorEq B.parent →
      (Y ∈ (M.fg_to_ac (x.stateBefore (M.slotStart S.C (s + 1)) p)).viable_heads ↔
        Y ∈ (M.fg_to_ac (x.stateBefore (M.voteTime S.C (s + 1)) w)).viable_heads) := by
  have hFRw : (x.stateBefore (M.voteTime S.C (s + 1)) w).finalized.AncestorEq
      (M.fg_to_ac (x.stateBefore (M.voteTime S.C (s + 1)) w)).fc_root := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_stateBefore M F) S A x R E
      (M.voteTime S.C (s + 1)) w
  intro Y hXY hRY hYP
  -- both trees hold `Y`
  have hYp : Y ∈ (x.stateBefore (M.slotStart S.C (s + 1)) p).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ p _ Y
      hParentHeld hYP
  have hYw : Y ∈ (x.stateBefore (M.voteTime S.C (s + 1)) w).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w _ Y hBw
      (ancestorEq_trans hYP (parent_ancestorEq B))
  -- both node states satisfy the node invariant, under which a block's chain state is the one
  -- computed from the block alone (`M.chainStateOf`), the same at both
  have hIp := (lem11_node_invariant M F S A x R E (x.stepBefore (M.slotStart S.C (s + 1))) p hp).1
  have hIw := (lem11_node_invariant M F S A x R E (x.stepBefore (M.voteTime S.C (s + 1))) w hw).1
  rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X
      (x.stateBefore (M.slotStart S.C (s + 1)) p) hIp,
    (GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X
      (x.stateBefore (M.voteTime S.C (s + 1)) w) hIw]
  constructor
  · rintro ⟨-, -, -, hfl⟩
    refine ⟨hYw, ancestorEq_trans hFRw hRY, hRY, ?_⟩
    rw [← hFloor]
    exact hfl
  · rintro ⟨-, -, -, hfl⟩
    refine ⟨hYp, ancestorEq_trans hFXp hXY, ancestorEq_trans hRXp hXY, ?_⟩
    rw [hFloor]
    exact hfl

/-- `viable_heads_agree_of_floor_eq` at two steps: the proposer `p`'s node state at the step `kp` and
the voter `w`'s at the step `kw` (in Lemma 24, the steps of `p`'s tick to the start of slot `s + 1`
and of `w`'s tick to the vote time of slot `s + 1`, rule R3). The proof is that of
`viable_heads_agree_of_floor_eq`, which reads no time.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `x`: the execution; `kp`, `kw`: the two steps;
- `X`: the block the slot-`s` majority extends; `B`: the block `p` proposed;
- `p`: the proposer; `w`: the voter; `hp`, `hw`: `p` and `w` are outside the adversary set at the two
  steps.

Read aloud: on the path from `X` to `B`'s parent, past the root of the voter's fork choice, the
proposer at step `kp` and the voter at step `kw` see the same viable heads, when their least viable
heights are equal. -/
theorem viable_heads_agree_of_floor_eq_at (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (kp kw : ℕ) (X B : Block V) (p w : V)
    (hParentHeld : B.parent ∈ (x.st kp p).tree)
    (hBw : B ∈ (x.st kw w).tree)
    (hFXp : (x.st kp p).finalized.AncestorEq X)
    (hRXp : (M.fg_to_ac (x.st kp p)).fc_root.AncestorEq X)
    (hFloor : M.head_height_floor (x.st kp p) = M.head_height_floor (x.st kw w))
    (hp : p ∉ A.corrupted kp) (hw : w ∉ A.corrupted kw) :
    ∀ Y : Block V, X.AncestorEq Y →
      (M.fg_to_ac (x.st kw w)).fc_root.AncestorEq Y →
      Y.AncestorEq B.parent →
      (Y ∈ (M.fg_to_ac (x.st kp p)).viable_heads ↔ Y ∈ (M.fg_to_ac (x.st kw w)).viable_heads) := by
  have hFRw : (x.st kw w).finalized.AncestorEq (M.fg_to_ac (x.st kw w)).fc_root := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E kw w
  intro Y hXY hRY hYP
  have hYp : Y ∈ (x.st kp p).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ p _ Y
      hParentHeld hYP
  have hYw : Y ∈ (x.st kw w).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w _ Y hBw
      (ancestorEq_trans hYP (parent_ancestorEq B))
  have hIp := (lem11_node_invariant M F S A x R E kp p hp).1
  have hIw := (lem11_node_invariant M F S A x R E kw w hw).1
  rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X (x.st kp p) hIp,
    (GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X (x.st kw w) hIw]
  constructor
  · rintro ⟨-, -, -, hfl⟩
    refine ⟨hYw, ancestorEq_trans hFRw hRY, hRY, ?_⟩
    rw [← hFloor]
    exact hfl
  · rintro ⟨-, -, -, hfl⟩
    refine ⟨hYp, ancestorEq_trans hFXp hXY, ancestorEq_trans hRXp hXY, ?_⟩
    rw [hFloor]
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
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `X`: the block the slot-`s` majority extends; `B`: the block `p` proposed at `t₁`;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`; `hp`, `hw`: `p` and `w` are
  outside the adversary set in the configurations read.

Read aloud: what the voter can step to from a block of the path, other than `B`, the proposer
could step to as well.

Roots name blocks until the real time of `p`'s tick to `M.slotStart S.C (s + 1)`: the proof takes a
block `w` stamped before the view freeze of slot `s` as held by `w` at its tick to the view freeze
(`mem_T_tick_of_blockStamp_lt`), and by `p` at its tick to the start of slot `s + 1`
(`block_at_tick_of_held_tick`, which reads roots up to that tick).

 each is active
at every step from the first one whose time is `ΔClockAhead` before `t₁ − max (Δ S) Δs` up to that tick, which
covers its tick to the view freeze of slot `s` (`hSkew`); `w` is active in every configuration in force at a real
time of `[t₁ − max (Δ S) Δs, t₁ − max (Δ S) Δs + Δs]` (the holder clause of the sync fact). -/
theorem child_mem_proposer_viable_tree (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (X B : Block V) (p w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    -- roots name blocks until the real time of `p`'s tick to the start of slot `s + 1`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.slotStart S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.slotStart S.C (s + 1))
    -- `p` ticks to the start of slot `s + 1` at a step `kP` and is active after every step from the first one
    -- whose time is `ΔClockAhead` before `M.slotStart S.C (s + 1) - max (Δ S) Δs` up to `kP`
    (hp : ∃ kP : ℕ, x.lbl kP = Event.tick p (M.slotStart S.C (s + 1)) ∧
      ∀ j : ℕ, ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kP →
        p ∈ A.active j)
    -- `w` ticks to the vote time of slot `s + 1` at a step `kW` and is active after every step from the same
    -- first one up to `kW`
    (hw : ∃ kW : ℕ, x.lbl kW = Event.tick w (M.voteTime S.C (s + 1)) ∧
      ∀ j : ℕ, ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kW →
        w ∈ A.active j)
    -- `w` is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the window's
    -- start `M.slotStart S.C (s + 1) - max (Δ S) Δs` (:'s holder clause)
    (hHold : w ∈ A.activeThroughout x ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hOnly : ∀ B' ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree, B'.slot = s + 1 → B' = B)
    -- `B`'s parent is the end of `p`'s walk: in `p`'s viable tree, or `p`'s anchor
    (hHp : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
        (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree ∨
      B.parent = M.get_anchor (x.tickInput p (M.slotStart S.C (s + 1)))
        ((M.slotStart S.C (s + 1) : ℕ) : Int))
    (hApX : (M.get_anchor (x.tickInput p (M.slotStart S.C (s + 1)))
      ((M.slotStart S.C (s + 1) : ℕ) : Int)).AncestorEq X)
    (hFloorLe : M.head_height_floor (x.tickInput p (M.slotStart S.C (s + 1))) ≤
      M.head_height_floor (x.tickInput w (M.voteTime S.C (s + 1)))) :
    ∀ Y : Block V, X.AncestorEq Y → Y.AncestorEq B.parent →
      ∀ D ∈ M.viable_tree (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1))))
          (VoterTree M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1)),
        D.parent? = some Y → D ≠ B →
        D ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
          (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree := by
  -- the delivery premises up to the start of slot `s + 1`, the deadline of the relay theorem
  have E' := E.upTo (M.slotStart S.C (s + 1))
  have Sy' := Sy.upTo (M.slotStart S.C (s + 1))
  obtain ⟨kP, hkP, hpwin⟩ := hp
  obtain ⟨kW, hkW, hwwin⟩ := hw
  -- the states read: `p`'s tick input at `kP`, `w`'s at `kW`
  have hPin : x.tickInput p (M.slotStart S.C (s + 1)) = x.st kP p := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E' hkP]
  have hWin : x.tickInput w (M.voteTime S.C (s + 1)) = x.st kW w := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E' hkW]
  rw [hPin] at hHp hApX hFloorLe ⊢
  rw [hWin] at hOnly hFloorLe ⊢
  rw [(tickStep_eq_of_lbl M) x E' hkP] at hRoots
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E'.ahead_nonneg
  have hB0 := E'.behind_nonneg
  have hΔ := one_le_Δ S
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  -- the times
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hv₃ : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hvf : M.viewFreeze S.C s = M.slotStart S.C s + 3 * Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hvfΔ : M.viewFreeze S.C s + Δ S = M.slotStart S.C (s + 1) := by omega
  -- the freeze `voter_block_tree` reads for slot `s + 1` is `viewFreeze S s`
  have hfz : ((S.C.t_ (s + 1 - 1) + 3 * S.C.Δ : Time) : Stamp) =
      (((M.viewFreeze S.C s : ℕ) : Int) : Stamp) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_cast M.toSlotLayout F.sched U), Nat.add_sub_cancel]
  -- the window's start `a`, one delay or one sync delay before the start of slot `s + 1`
  obtain ⟨a, hadef⟩ : ∃ a : ℕ, a = M.slotStart S.C (s + 1) - max (Δ S) Δs := ⟨_, rfl⟩
  rw [← hadef] at hpwin hwwin hHold
  have ha : a + max (Δ S) Δs = M.slotStart S.C (s + 1) := by omega
  have haf : a ≤ M.viewFreeze S.C s := by omega
  have hGSTa : GST ≤ a := by omega
  -- the real times of the two ticks
  have hssR : ((M.slotStart S.C (s + 1) : ℕ) : ℝ) = (M.viewFreeze S.C s : ℝ) + Δ S := by
    rw [← hvfΔ]; push_cast; ring
  have hvtR : ((M.voteTime S.C (s + 1) : ℕ) : ℝ) = (M.viewFreeze S.C s : ℝ) + 2 * Δ S := by
    rw [hv₃, ← hvfΔ]; push_cast; ring
  have hafR : (a : ℝ) ≤ M.viewFreeze S.C s := by exact_mod_cast haf
  have hkPt := (E'.tick_active kP p _ hkP).2.1
  have hkWt := (E'.tick_active kW w _ hkW).2.1
  rw [hssR] at hkPt
  rw [hvtR] at hkWt
  have hpkP : p ∉ A.corrupted kP := E'.not_mem_corrupted_of_tick hkP
  have hwkW : w ∉ A.corrupted kW := E'.not_mem_corrupted_of_tick hkW
  -- `w` and `p` tick to the view freeze of slot `s`, inside their windows
  have hvf1 : 1 ≤ M.viewFreeze S.C s := by omega
  obtain ⟨kU, hkU, hkU1, hkU2⟩ := E'.tick_of_active (M.viewFreeze S.C s) hvf1 w (fun i h1 h2 =>
    hwwin i (by linarith) ((lt_of_time_lt M) x R (by linarith)).le)
  obtain ⟨k₂, hk₂, hk₂1, hk₂2⟩ := E'.tick_of_active (M.viewFreeze S.C s) hvf1 p (fun i h1 h2 =>
    hpwin i (by linarith) ((lt_of_time_lt M) x R (by linarith)).le)
  have hkUW : kU < kW := (lt_of_time_lt M) x R (by linarith)
  have hwkU : w ∉ A.corrupted kU := E'.not_mem_corrupted_of_tick hkU
  -- `p`'s window from the real time `a`, as the relay theorem reads it
  have hpwin' : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kP → p ∈ A.active i :=
    fun i h1 h2 => hpwin i (by linarith) h2
  have hF2p : (x.st kP p).finalized.AncestorEq (M.fg_to_ac (x.st kP p)).fc_root := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E' kP p
  intro Y hXY hYP D hD hDpar hDB
  -- the ancestry facts at `p`
  have hRpA : (M.fg_to_ac (x.st kP p)).fc_root.AncestorEq
      (M.get_anchor (x.st kP p) ((M.slotStart S.C (s + 1) : ℕ) : Int)) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_get_anchor M F) _ _
  have hYD : Y.AncestorEq D := ancestorEq_of_parent? hDpar
  have hXD : X.AncestorEq D := ancestorEq_trans hXY hYD
  have hRpD : (M.fg_to_ac (x.st kP p)).fc_root.AncestorEq D :=
    ancestorEq_trans hRpA (ancestorEq_trans hApX hXD)
  have hFpD : (x.st kP p).finalized.AncestorEq D := ancestorEq_trans hF2p hRpD
  -- `w`'s viable tree over its voter's tree, unfolded at `D`
  rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F)] at hD ⊢
  obtain ⟨hDv, -, W, hWmem, hDW⟩ := hD
  obtain ⟨hWv, hWvh⟩ := Finset.mem_inter.1 hWmem
  by_cases hDP : D.AncestorEq B.parent
  · -- case A, `D` on the path: `D` is `B`'s parent or an ancestor of it
    rcases hHp with hBin | hBeq
    · -- `B`'s parent is in `p`'s viable tree, and so is `D`, with the same viable head
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F)] at hBin
      obtain ⟨hBΦ, -, W', hW'mem, hBW'⟩ := hBin
      have hBT := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hBΦ).1
      exact ⟨((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨(GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E' _ p _ D hBT hDP, hFpD⟩,
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
  · -- case B, `D` off the path: what `w`'s voter's tree holds of `D`'s descendants reached `p`
    -- by its tick to the start of slot `s + 1`
    have hReach : ∀ Z ∈ VoterTree M S.C (x.st kW w) (s + 1), D.AncestorEq Z →
        Z ∈ (x.st kP p).tree := by
      intro Z hZ hDZ
      simp only [VoterTree, Finset.mem_filter] at hZ
      obtain ⟨-, hZΦ, τ, hτ, hfr | ⟨B', hB'Φ, hB's, hZB'⟩⟩ := hZ
      · -- `Z` was stamped at `w` before the view freeze of slot `s`: `w` holds it at its tick to
        -- the view freeze, and the relay at ticks brings it to `p` by its tick to `t₁`
        have hZw : Z ∈ (x.st kW w).tree :=
          (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hZΦ).1
        rw [hfz] at hfr
        have hZU : Z ∈ (x.st kU w).tree :=
          (mem_T_tick_of_blockStamp_lt M F) x R E' hkU hwkW hZw hτ hfr
        by_cases hg : Z = Block.genesis
        · rw [hg]
          exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E' kP p
        -- `w`'s finalized block before the window's start is compatible with `Z`
        have hsbW : x.stepBefore a ≤ kW := by
          rcases Nat.eq_zero_or_pos a with h0 | h0
          · rw [h0, (stepBefore_zero M) x R]
            exact Nat.zero_le _
          · exact ((stepBefore_lt_of_le_time M) x R E' h0 (by linarith)).le
        have hFa : (x.st (x.stepBefore a) w).finalized.compatible Z = true :=
          (compatible_iff _ _).2 (Or.inl (ancestorEq_trans ((F_ancestorEq_of_le M F) x R E' w hsbW)
            (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hZΦ).2))
        -- `Z`'s slot starts no later than the view freeze of slot `s`: it entered `w`'s tree at a
        -- clock value less than the view freeze
        have hZs : M.slotStart S.C Z.slot ≤ M.viewFreeze S.C s := by
          obtain ⟨i, hi, -, -, hslot, -⟩ := (tree_block_relayed_entry M F) x R E' hZU hg
          rw [(clock_eq_clockValue M F) x R (i + 1) w] at hslot
          have hcv1 : x.clockValue (i + 1) w ≤ x.clockValue kU w :=
            E'.clockValue_mono (show i + 1 ≤ kU by omega) hwkU
          have hcv2 : x.clockValue kU w < M.viewFreeze S.C s :=
            (clockValue_lt_of_tick_of_active M F) E' hkU (by omega)
              (fun j h1 h2 => hwwin j (by linarith) (le_trans h2 hkUW.le))
          have hsl : M.slot S.C (x.clockValue (i + 1) w) =
              S.C.slot ((x.clockValue (i + 1) w : ℕ) : Int) := by
            rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
              GoldilocksCorrectness.Proofs.Routines.slot_natCast]
          have h1 : M.slotStart S.C Z.slot ≤ x.clockValue (i + 1) w :=
            (F.sched.slotStart_le_iff S _ _).2 (by rw [hsl]; exact hslot)
          omega
        have hZp := (block_at_tick_of_held_tick M F U) S A x R GST (M.slotStart S.C (s + 1))
          (M.viewFreeze S.C s) kU a (M.slotStart S.C (s + 1)) (M.viewFreeze S.C s) kP k₂ w p Z
          E' hNet hSkew hRedeliver Sy' hRoots hParent hGSTa (by omega) (by omega) le_rfl hHold hkU hZU
          hFa hg hkP hpwin' hk₂ (by omega) hZs
          ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFpD hDZ)))
        exact hZp
      · -- `Z` leads to a slot-`(s + 1)` block of `w`'s tree, which is `B`: then `D` is on the path
        exfalso
        have hB'B := hOnly B' (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hB'Φ).1 hB's
        rw [hB'B] at hZB'
        exact hDP (ancestorEq_parent_of_ne (ancestorEq_trans hDZ hZB') hDB)
    have hDp := hReach D hDv (ancestorEq_refl D)
    have hWp := hReach W hWv hDW
    -- `W` is a viable head at `p`: the chain state of a block is the one computed from the block
    -- alone at both node states (the node invariant, Lemma 11 at the two ticks), and
    -- `head_height_floor` at `p` is at most the one at `w`
    have hIp := (lem11_node_invariant M F S A x R E' kP p hpkP).1
    have hIw := (lem11_node_invariant M F S A x R E' kW w hwkW).1
    obtain ⟨hWw, -, -, hflw⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F)
      S.C S.P S.X (x.st kW w) hIw W).1 hWvh
    have hFpW := ancestorEq_trans hFpD hDW
    have hfl : M.head_height_floor (x.st kP p) ≤ (M.chainStateOf S.C W).h :=
      le_trans hFloorLe hflw
    exact ⟨((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hDp, hFpD⟩, hRpD, W,
      Finset.mem_inter.2 ⟨((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2
          ⟨hWp, hFpW⟩,
        ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X (x.st kP p)
          hIp W).2 ⟨hWp, hFpW, ancestorEq_trans hRpD hDW, hfl⟩⟩, hDW⟩

end GoldilocksCorrectness.Record.Proofs.Executions

