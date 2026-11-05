module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Provenance
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Network
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.NetworkUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.RootsStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Monotone
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Clock
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Node
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Proofs.Executions.Provenance
public import GoldilocksCorrectness.Proofs.Executions.Network
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.RootsStatements
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# BlockPropagation, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/BlockPropagation.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: what a delivery step leaves at its
receiver (the model's `receive`), a held block's slot is at most the slot of the time, and block
propagation: a block an honest validator holds reaches every awake honest validator whose finalized
block is compatible with it within the delay, the node accepting it by the field
`block_admissible_iff` of `F.ndAdded` under the model's node invariant (Lemma 11). The page's
routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ)
open GoldilocksCorrectness.Proofs.Routines (slot_mono slot_mono_int)

open GoldilocksCorrectness.Proofs.Routines (fun_getElem)

open GoldilocksCorrectness.Proofs.Routines (fg_on_block_eq)

open GoldilocksCorrectness.Proofs.Routines (block_admissible_of mem_T_receive_block)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open Goldilocks
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff)

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The times -/

section Times

open Goldilocks.Sts (Setup)

end Times

/-! ## The test of a block, and its receipt -/

section Admission

variable [RootOrder]

end Admission

/-! ## A delivery step -/

section Steps

open Framework.StsMultisetLog (SignedMsg applyNodeStepResult_getElem receive_getElem nodeStep_iff_exists)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks.Sts (Setup)

variable [RootOrder] {S : Setup V} {A : Activity V}

/-- A step that delivers the signed message `sm` to `v` finds `v` awake and outside the adversary
set at its time, and leaves `v` with the node state `receive` gives on `sm`'s object.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `d`: the step; `v`: the receiver; `sm`: the signed message.

Read aloud: a delivery to `v` finds `v` awake and honest, and leaves it with what the model's
`receive` gives on the delivered object. -/
theorem deliver_step_state (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {d : ℕ} {v : V}
    {sm : SignedMsg V (NamedObject V)}
    -- the step `d` delivers `sm` to `v`
    (hl : x.lbl d = Event.deliver v sm) :
    v ∈ A.active d ∧
      x.st (d + 1) v = M.receive S.C S.P S.X (x.st d v) sm.msg := by
  exact ⟨E.deliver_active d v sm hl, (R.deliver d v sm hl).2.1⟩

end Steps

/-! ## Along an execution -/

section Propagation

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks.Sts (Setup)

variable [RootOrder] {S : Setup V} {A : Activity V}

/-- A block a validator holds before the time `t` has a slot at most the slot of some clock value `c`
at most `t + ΔClockAhead` (or `0`, the initial clock, when `t + ΔClockAhead` is negative): it entered
the validator's tree at a step whose time is less than `t`, with the validator's clock value then in
a slot at least the block's (`tree_block_relayed_before`), and a clock value is at most the real time
plus `ΔClockAhead` (`clockValue_le_time_add_ahead`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `t`: the time; `v`: the validator; `B`: the block; `c`: the clock value.

Read aloud: a block a validator holds before `t` has a slot at most the slot of a clock value at most
`t + ΔClockAhead`. -/
theorem slot_le_of_mem_T_before {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- corruption is permanent
    {t : ℕ} {v : V} {B : Block V}
    -- `v`'s tree before `t` holds `B`
    (hB : B ∈ (x.stateBefore t v).tree) :
    ∃ c : ℕ, (c : ℝ) ≤ max 0 ((t : ℝ) + ΔClockAhead) ∧ B.slot ≤ S.C.slot (c : Int) := by
  by_cases hg : B = Block.genesis
  · subst hg
    exact ⟨0, by simp, Nat.zero_le _⟩
  obtain ⟨i, hi, -, -, hslot⟩ := (tree_block_relayed_before M F R) E hB hg
  have hlt : x.time (i + 1) < t := ((lt_stepBefore_iff M) x R E).1 hi
  refine ⟨x.clockValue (i + 1) v, ?_, ?_⟩
  · refine le_trans ((clockValue_le_time_add_ahead M F) x R E (i + 1) v) (max_le_max le_rfl ?_)
    linarith
  · rw [(clock_eq_clockValue M F) x R (i + 1) v] at hslot
    exact hslot

/-- **Kit theorem, a delivery that found the receiver reacted to a clock value is read by its clock.**
A validator outside the adversary set at a delivery step `d`, which by `d` has ticked to, or been
restarted at, a clock value at least `r`, has a clock value at least `r` at `d` (the tick or restart is
before `d`, which is a delivery; the clock value never goes back, `clockValue_mono`).

The variables:
- `x`: the execution; `E`: the environment's facts; `d`: the delivery step; `w`: the receiver;
  `sm`: the delivered message; `r`: the clock value.

Read aloud: a receiver that has reacted to `r` by a delivery has its clock value at least `r` there. -/
theorem le_clockValue_of_reactedAtLeast {x : Trace V (NamedObject V) M.N}
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {d : ℕ} {w : V} {sm : SignedMsg V (NamedObject V)} {r : ℕ}
    (hl : x.lbl d = Event.deliver w sm) (hw : w ∉ A.corrupted d) (hreact : x.ReactedAtLeast d w r) :
    r ≤ x.clockValue d w := by
  obtain ⟨i', hi', t', hrt, hset⟩ := hreact
  have hi'd : i' < d := by
    refine lt_of_le_of_ne hi' fun h => ?_
    subst h
    rcases hset with h | ⟨_, h⟩ <;> rw [hl] at h <;> cases h
  have hcv : x.clockValue (i' + 1) w = t' := by
    rcases hset with h | ⟨_, h⟩
    · exact x.clockValue_succ_of_tick h
    · exact x.clockValue_succ_of_restart h
  have := E.clockValue_mono (show i' + 1 ≤ d from hi'd) hw
  omega

/-- **Kit theorem, a block delivered to a receiver that has reacted to the start of its slot is held
from then on**. `u`, outside the adversary set at a step `iu`, holds a block
`B`; the step `d` delivers `u`'s signed block `B` to `w`, which by `d` has ticked to, or been restarted
at, a clock value at least the start of `B`'s slot (the admission clause of the delivery promise, with
`release := releaseOf M S.C`); at a later step `k`, `w` is outside the adversary set and its finalized
block is compatible with `B`. Then `w` holds `B` at `k`: the delivery finds `w` holding `B`'s parent
(`ParentHeldAtDelivery`), its clock in `B`'s slot or later, and no other block of `B`'s root held by an
honest validator (`hRoots`), so the model's `receive` admits `B` (`block_admissible_iff`), and the tree
only grows.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `T`: the time until which
  roots name blocks;
- `u`: the holder; `w`: the receiver; `B`: the block; `iu`: a step at which `u` holds `B`; `d`: the
  delivery; `k`: the later step.

Read aloud: a block an honest validator holds, delivered to `w` once `w`'s clock has reached the start of
the block's slot, is in `w`'s tree at every later step at which `w` is honest and its finalized block is
compatible with the block. -/
theorem mem_tree_of_admitted_delivery (U : UniformSchedule M.toSlotLayout)
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {T : ℝ}
    -- a root names one block among what honest validators hold by `T`
    (hRoots : RootsNameBlocksUntil M A x T)
    -- a block reaches a validator only once the validator holds its parent
    (hParent : ParentHeldAtDelivery M x)
    {u w : V} {B : Block V} {iu d k : ℕ}
    -- `u` is outside the adversary set at `iu`, by `T`, and holds `B` there
    (hu : u ∉ A.corrupted iu) (hTu : x.time iu ≤ T) (hB : B ∈ (x.st iu u).tree)
    -- the step `d`, by `T`, delivers `u`'s signed block `B` to `w`, which by `d` has reacted to the start
    -- of `B`'s slot
    (hl : x.lbl d = Event.deliver w ⟨u, NamedObject.block B⟩) (hTd : x.time d ≤ T)
    (hreact : x.ReactedAtLeast d w (M.slotStart S.C B.slot))
    -- `k` is after `d`; `w` is outside the adversary set at `k` and its finalized block there is
    -- compatible with `B`
    (hdk : d < k) (hwk : w ∉ A.corrupted k)
    (hcompat : (x.st k w).finalized.compatible B = true) :
    B ∈ (x.st k w).tree := by
  by_cases hg : B = Block.genesis
  · subst hg
    exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E _ w
  rcases (compatible_iff _ _).1 hcompat with hFB | hBF
  swap
  · exact (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w
      _ B (F.nd.nodeInv_finalized_mem_tree
        ((GoldilocksCorrectness.Record.Statements.Executions.lem11_node_invariant M F) S A x R E.noDelivery
          k w hwk).1) hBF
  obtain ⟨hwa, hstep⟩ := (deliver_step_state M F) x R E hl
  have hwh : w ∉ A.corrupted d := Activity.not_mem_corrupted_of_mem_active hwa
  suffices h : B ∈ (x.st (d + 1) w).tree from (mem_T_mono M F) x R E w hdk h
  by_cases hheld : B ∈ (x.st d w).tree
  · exact (mem_T_mono M F) x R E w (Nat.le_succ d) hheld
  rw [hstep]
  have hInvU := ((GoldilocksCorrectness.Record.Statements.Executions.lem11_node_invariant M F)
    S A x R E.noDelivery iu u hu).1
  obtain ⟨-, hwf, hprop, hps⟩ := (F.nd.nodeInv_treeClosed hInvU).2 B hB hg
  have hFd : (x.st d w).finalized.AncestorEq B :=
    ancestorEq_trans ((F_ancestorEq_of_le M F) x R E w (le_of_lt hdk)) hFB
  have hpar : B.parent ∈ (x.st d w).tree :=
    hParent d w _ B hl rfl hg ((compatible_iff _ _).2 (Or.inl hFd))
  have hInvW := (GoldilocksCorrectness.Record.Statements.Executions.lem11_node_invariant M F)
    S A x R E.noDelivery d w hwh
  -- the receiver's clock at the delivery is in `B`'s slot or later
  have hclk : B.slot ≤ S.C.slot (x.st d w).t := by
    have h1 := (le_clockValue_of_reactedAtLeast M F) E hl hwh hreact
    have h2 : B.slot ≤ M.slot S.C (x.clockValue d w) := (F.sched.slotStart_le_iff S _ _).1 h1
    have hsl : M.slot S.C (x.clockValue d w) = S.C.slot ((x.clockValue d w : ℕ) : Int) := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
        GoldilocksCorrectness.Proofs.Routines.slot_natCast]
    rw [hInvW.2.2, ← hsl]
    exact h2
  refine (F.rcvAdded.mem_tree_receive_block S.C S.P S.X _ B B).2 (Or.inr ⟨rfl,
    (F.ndAdded.block_admissible_iff B hInvW.1).2 ⟨hwf, ?_, ?_, hpar, hFd, hprop, hps, ?_⟩⟩)
  · exact hclk
  · intro B' hB' hr
    have hBB : B' = B := hRoots B' B ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := d) (v := w) hwh hTd hB') ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := iu) (v := u) hu hTu hB) hr
    exact hheld (hBB ▸ hB')
  · intro a ha
    exact (F.nd.nodeInv_attestationsValid hInvU) B hB hg a ha

omit F in
/-- The delivery promise up to `b'` gives the one up to every `b ≤ b'`.

The variables:
- `M`: the model; `x`: the execution; `Δ'`: the delay; `GST`: the time from which the network is
  synchronous; `ok`: the class of objects; `b`, `b'`: the two bounds; `hle`: `b ≤ b'`; `E`: the
  delivery promise up to `b'`.

Read aloud: a bound on the delivery promise's deadlines can be lowered. -/
theorem envFactsDeliveryUpTo_mono {x : Trace V (NamedObject V) M.N} {Δ' GST b b' : ℕ}
    {ok : NamedObject V → Prop} (hle : b ≤ b')
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind Δ' ΔRedeliver GST release ok
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b') :
    GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind Δ' ΔRedeliver GST release ok
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b := by
  exact EnvFactsBy.restrict E fun _ _ _ h => by
    obtain ⟨h1, rfl⟩ := GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.1 h
    exact GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.2 ⟨le_trans h1 (by exact_mod_cast hle), rfl⟩

omit F in
/-- The delivery promise up to `b'` gives the one up to every `b ≤ b'`, in the dot form `E.mono hle`
the proofs of the restated pages call (`envFactsDeliveryUpTo_mono` for any messages).

The variables:
- `A'`: the activity; `x`: the execution; `Δ'`: the delay; `GST`: the time from which the network
  is synchronous; `ok`: the class of objects; `W`: the vocabulary; `b`, `b'`: the two bounds;
  `hle`: `b ≤ b'`; `E`: the delivery promise up to `b'`.

Read aloud: a bound on the delivery promise's deadlines can be lowered. -/
theorem _root_.GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDeliveryUpTo.mono
    {V' Msg N : Type} [DecidableEq V'] [DecidableEq Msg] {A' : Activity V'} {x : Trace V' Msg N}
    {Δ' GST b b' : ℕ} {ok : Msg → Prop} {B : Type}
    {W : GoldilocksCorrectness.Statements.Network.ViewVocab V' B Msg} (hle : b ≤ b')
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDeliveryUpTo A' x ΔClockAhead ΔClockBehind Δ' ΔRedeliver GST release ok W b') :
    GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDeliveryUpTo A' x ΔClockAhead ΔClockBehind Δ' ΔRedeliver GST release ok W b := by
  exact GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy.restrict E fun _ _ _ h => by
    obtain ⟨h1, rfl⟩ := GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.1 h
    exact GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.2 ⟨le_trans h1 (by exact_mod_cast hle), rfl⟩

/-- A validator active after every step read as `t₀ ≥ 1` is active after `x.stepBefore t₀`, the
last step before `t₀` (`mem_active_of_mem_activeAtTime_of_last`). The holder clause of the sync fact
 from an activity at the time.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts, for any deadlines;
- `t₀`: the time; `u`: the validator.

Read aloud: a validator active at `t₀` was active just before `t₀`. -/
theorem mem_active_stepBefore_of_mem_activeAtTime {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x)
    {deadline : Framework.StsMultisetLog.SignedMsg V (NamedObject V) → ℝ → Option ℝ}
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {t₀ : ℕ} {u : V} (ht₀1 : 1 ≤ t₀) (hu : u ∈ A.activeAtTime x t₀) :
    u ∈ A.active (x.stepBefore t₀) := by
  -- the configuration after `x.stepBefore t₀` is in force at `t₀`
  obtain ⟨h1, h2⟩ := (stepBefore_time M) x R E ht₀1
  exact Activity.mem_activeAtTime.1 hu _ h1.le h2

/-- The sync fact up to a bound `b` read at a window's start `t₀ ≥ 1`, with the receiver read up to its
own tick `kR` to the window's end `d ≤ b`, at least one sync delay after `t₀`: what `u`, active after the last step before `t₀`, serves there at its own clock value,
and active at every step whose real time is in `[t₀, t₀ + Δs]`, reaches `w` before `kR`,
at or after a step at a time less than `t₀` after which `u` already serves it at its clock value then,
with `w` active from the delivery up to `kR`; or `w` already serves it after the last step before
`t₀`, at its own clock value; when `w` is active after every step from the first one whose time is
`t₀` up to `kR`.

Why: the sync fact's receiver clause reads `w`'s tick to any clock value at least the sync deadline
`t₀ + Δs ≤ d` (`delivered_before_of_held_upTo_tick`); no intermediate tick is read.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `Δ`: the delay; `Δs`: the
  sync delay; `GST`: the time from which the network is synchronous; `b`: the bound; `ok`: the class
  of objects; `serves`: the selection; `Sy`: the sync fact up to `b`;
- `t₀`: the window's start; `d`: the window's end; `u`: the holder; `w`: the receiver; `o`: the
  object; `kR`: the step of `w`'s tick to `d`.

Read aloud: what an honest validator active at a window's start, and for one sync delay after it,
would serve then reaches, before its tick to the window's end, every validator active from the
window's start up to that tick that does not already serve it; when a re-delivery after the receiver's
clock reaches the object's release clock value would come before that tick, the delivery found its
clock there. -/
theorem delivered_before_of_held_window_tick {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline : Framework.StsMultisetLog.SignedMsg V (NamedObject V) → ℝ → Option ℝ}
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {Δ Δs GST b : ℕ} {ok : NamedObject V → Prop}
    {serves : M.N → ℕ → NamedObject V → Prop}
    (Sy : GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinUpTo A x serves ok (releaseOf M S.C) ΔRedeliver Δs GST b)
    {t₀ d : ℕ} {u w : V} {o : NamedObject V}
    -- the window starts at a time at least `1`, from which the network is synchronous
    (ht₀1 : 1 ≤ t₀) (hGST : GST ≤ t₀)
    -- `u` is active after the last step before `t₀` and serves `o` from its state there, at its own
    -- clock value there
    (hu : u ∈ A.active (x.stepBefore t₀))
    (ho : serves (x.st (x.stepBefore t₀) u) (x.clockValue (x.stepBefore t₀) u) o) (hok : ok o)
    -- `u` is active at every step whose real time is in `[t₀, t₀ + Δs]`
    (hhold : ∀ i : ℕ, (t₀ : ℝ) ≤ x.time i → x.time i ≤ t₀ + Δs → u ∈ A.active i)
    -- `w` ticks to `d` at `kR`, and is active from the first step read as `t₀` up to `kR`
    {kR : ℕ} (hkR : x.lbl kR = Event.tick w d)
    (hwR : ∀ i : ℕ, t₀ ≤ x.time i → i ≤ kR → w ∈ A.active i)
    -- the window is at least one delay or one sync delay long, and ends by the bound
    (ht₀ : t₀ + max Δ Δs ≤ d) (hdb : d ≤ b)
    -- the re-delivery premise of the sync fact at `kR`
    (hprem : ∀ (r j₀ k₁ t₁ : ℕ), releaseOf M S.C o = some r →
      x.lbl j₀ = Event.deliver w ⟨u, o⟩ → ¬ x.ReactedAtLeast j₀ w r →
      j₀ < k₁ → k₁ ≤ kR → x.lbl k₁ = Event.tick w t₁ → r ≤ t₁ →
      (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick w t' → t' < r) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time kR) :
    serves (x.st (x.stepBefore t₀) w) (x.clockValue (x.stepBefore t₀) w) o ∨
    ∃ j k', k' ≤ j ∧ x.time k' < t₀ ∧ serves (x.st k' u) (x.clockValue k' u) o ∧
      x.lbl j = Event.deliver w ⟨u, o⟩ ∧ j < kR ∧
      (∀ r : ℕ, releaseOf M S.C o = some r → r ≤ d → x.ReactedAtLeast j w r) ∧
      (∀ l : ℕ, j ≤ l → l ≤ kR → w ∈ A.active l) := by
  obtain ⟨hkt, hkt1⟩ := (stepBefore_time M) x R E ht₀1
  have hmx := le_max_right Δ Δs
  have hD : t₀ + Δs ≤ d := le_trans (Nat.add_le_add_left hmx t₀) ht₀
  exact (delivered_before_of_held_upTo_tick M) x R E Sy (hD.trans hdb) hu hkt hkt1 ho hok hhold hGST
    hD hkR hwR hprem

/-- What a node serves at the clock value `c` it also serves at every clock value `c' ≤ c`: the
clock value is read only by the Goldfish-vote test `M.slot C c ≤ vote.slot + 1`, and the slot of a
clock value grows with it (`slot_mono`).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `n`: the node state; `c' ≤ c`: the two clock values; `o`: the object.

Read aloud: a node serves at an earlier clock value everything it serves at a later one. -/
theorem servesMin_of_le_clockValue (S : Setup V) {n : M.N} {c c' : ℕ} {o : NamedObject V}
    -- `c'` is at most `c`
    (hcc : c' ≤ c)
    -- `n` serves `o` at `c`
    (h : GoldilocksCorrectness.Record.Statements.AbstractTrace.servesMin M S.C n c o) :
    GoldilocksCorrectness.Record.Statements.AbstractTrace.servesMin M S.C n c' o := by
  cases o with
  | block B => exact h
  | gfVote vote =>
      exact ⟨h.1, le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.slot_mono M.toSlotLayout F.sched) S hcc) h.2⟩
  | attest a => exact h

/-- **Kit theorem, `servesMin` at the holder's clock value (H8).** A validator's node state after `k`
steps serves at its own clock value there everything it serves at a clock value `c` at least
`max 0 (x.time k + ΔClockAhead)`: its clock value there is at most that bound
(`clockValue_le_time_add_ahead`: the tick or restart that set it was at a real time at least the
clock value minus `ΔClockAhead`; the `0` is the initial clock), and a node serves at a smaller clock
value everything it serves at a larger one (`servesMin_of_le_clockValue`). A caller reading the
holder at `x.stepBefore t₀` has `x.time k < t₀` and takes for `c` any clock value at least
`max 0 (t₀ + ΔClockAhead)` at which its hypotheses give the Goldfish-vote test.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `k`: the step; `u`: the
  holder; `o`: the object; `c`: the clock value the object is known to be served at.

Read aloud: a holder serves at its own clock value what it serves at any clock value at least the
real time plus `ΔClockAhead`. -/
theorem servesMin_of_clockValue_near {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k : ℕ} {u : V} {o : NamedObject V} {c : ℕ}
    -- `c` is at least the real time of the configuration after `k` steps plus `ΔClockAhead`
    (hc : max 0 (x.time k + ΔClockAhead) ≤ c)
    -- `u`'s node state after `k` steps serves `o` at `c`
    (h : GoldilocksCorrectness.Record.Statements.AbstractTrace.servesMin M S.C (x.st k u) c o) :
    GoldilocksCorrectness.Record.Statements.AbstractTrace.servesMin M S.C (x.st k u)
      (x.clockValue k u) o :=
  (servesMin_of_le_clockValue M F) S
    (by exact_mod_cast le_trans ((clockValue_le_time_add_ahead M F) x R E k u) hc) h

end Propagation

end GoldilocksCorrectness.Record.Proofs.Executions

