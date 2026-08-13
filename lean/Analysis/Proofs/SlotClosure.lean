import Spec
import Analysis.Proofs.Weights

/-!
# Proofs: closing slots

The argument behind Lemma 3. `Analysis/Lemmas.lean` holds the statement of record and calls into
here in one line.

`BlockPostState` and Definition 20's `actionState` are declared here rather than in
`Analysis/Lemmas.lean`, because the statement there needs them and that file holds statements only.

## How the proof goes, and what is left

`process_slots` is a `while`, a least fixed point that does not reduce. It is traded once for a
structural recursion on the number of slots left to close (`closeSlots`), and everything after
inducts on a `Nat`. The count is right because of the cursor lemma `processSlot_s`: the body
advances `s` by exactly one.

**The paper's Lemma 3 is false over an arbitrary state**, and the missing hypothesis is an
invariant it argues only in prose: the height-event check cannot fire, because
`state_transition` already ran it at the block and left its conditions false. `Settled` is that
invariant — the negations of `process_height_events`' three branch conditions, **plus a fourth
conjunct the paper never states**: with no target stored, no target bit is set. Without the fourth,
`process_slot`'s `T_h ← L` write unblocks the second branch, and the invariant is not preserved.

`Settled` also needs a **positive threshold**. On an empty electorate `q = ⌈2W/3⌉` is `0`, every
set is a quorum, and nothing is ever blocked. The machinery below takes that as a plain `0 < q` so it
does not depend on where the electorate's weight comes from; the outward-facing statements carry
the `PositiveWeight` class instead and discharge it with `q_pos`. That class is **not** an extra
assumption — either of the paper's fault bounds gives it, via `PositiveWeight.ofFaultBound`.

**What is outstanding is one fact: every block post-state is `Settled`.** That is where
`process_block` and `process_height_events` have to be analysed, and the invariant does not survive
`process_block` — quorums are built there, by design — so it wants the split the
`lean-proof-idioms` skill describes, with `process_height_events` re-establishing `Settled` at the
end of the transition. Everything else below is proved.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

/-- `σ` is a **block post-state**: reachable from `ChainState.gen` by `stateTransition` along a
    chain of blocks. That is the paper's own term — Lemmas 4 and 10 say "every reachable block
    post-state".

    **Deliberately weaker than the paper's `σ[·]`.** Figure 3 (`alg:store`) admits a block only
    when the structural precheck passes and its claimed post-state root equals `root(σ')`, and
    neither the precheck nor a state-root function is modelled, so neither is required here. This
    predicate therefore holds of *more* states than `σ[·]` does, which makes a theorem carrying it
    as a hypothesis **stronger** than the paper's, and one that specialises to the paper's sentence
    when Figure 3 lands.

    It is not called `σ[·]`, and must not be: an earlier `replayChain` was withdrawn precisely for
    claiming to be that map while omitting both checks. -/
inductive BlockPostState {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] : ChainState Node Root → Prop
  /-- Genesis: the values Definition 13 (`def:chain-state`) lists, which Figure 1's **Genesis**
      block repeats. -/
  | gen : BlockPostState ChainState.gen
  /-- One accepted block later. -/
  | step {σ σ' : ChainState Node Root} {B : Blk Node Root} :
      BlockPostState σ → stateTransition σ B = .state σ' → BlockPostState σ'

/-- Definition 20 (`def:finality-action-state`): `σ_a[X] = process_slots(σ[X], slot(a))`, the state
    a signing action reads, got by closing exactly the slots before the action.

    The definition is that one application of `process_slots`, so this renders all of it. Written
    over a block post-state rather than over `σ[X]`, for the reason in `BlockPostState`.

    Definition 20's side condition `X.slot ≤ slot(a)` is `σ.L.slot ≤ t` here, and the lemmas that
    use this carry it rather than the definition, which is where the paper puts it. -/
def actionState {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] (σ : ChainState Node Root) (t : Time) : ChainState Node Root :=
  processSlots σ t

namespace Proofs

variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]

/-! ## The cursor, and trading the `while` for a recursion -/

theorem advanceHeight_s (σ : ChainState Node Root) (j : Option (Blk Node Root)) (st : Time) :
    (advanceHeight σ j st).s = σ.s := by
  simp only [advanceHeight]; repeat' split
  all_goals rfl

theorem processHeightEvents_s (σ : ChainState Node Root) (st : Time) :
    (processHeightEvents σ st).s = σ.s := by
  simp only [processHeightEvents, advanceHeight]; repeat' split
  all_goals rfl

/-- The cursor lemma. This is what makes the slot count in `closeSlots` right. -/
theorem processSlot_s (σ : ChainState Node Root) : (processSlot σ).s = σ.s + 1 := by
  simp only [processSlot]; repeat' split
  all_goals simp [processHeightEvents_s]

/-- The `rfl` bridge. `rw` with `Lean.Loop.forIn_eq_of_monadTail` reports "no match" against the
    goal as it stands, because the goal holds the `ForIn` class method at
    `Lean.instForInLoopUnitOfMonad` while the lemma is about `Lean.Loop.forIn` directly, and `rw`
    does not see through the instance projection. Restating the loop bare is definitional. -/
theorem processSlots_eq_loop (σ : ChainState Node Root) (t : Time) :
    processSlots σ t =
      Lean.Loop.forIn (m := Id) Lean.Loop.mk σ
        (fun _ s => if s.s < t then pure (.yield (processSlot s)) else pure (.done s)) := rfl

theorem processSlots_step (σ : ChainState Node Root) (t : Time) :
    processSlots σ t = if σ.s < t then processSlots (processSlot σ) t else σ := by
  rw [processSlots_eq_loop, Lean.Loop.forIn_eq_of_monadTail]
  by_cases h : σ.s < t
  · simp [h, processSlots_eq_loop]
  · simp [h]; rfl

/-- The `while` as a structural recursion on the number of slots left to close. Everything after
    this inducts on a `Nat` instead of unfolding a fixed point. -/
def closeSlots : Nat → ChainState Node Root → ChainState Node Root
  | 0, σ => σ
  | n + 1, σ => closeSlots n (processSlot σ)

theorem processSlots_eq_closeSlots (t : Time) (σ : ChainState Node Root) :
    processSlots σ t = closeSlots (t - σ.s) σ := by
  induction hn : t - σ.s generalizing σ with
  | zero => rw [processSlots_step, if_neg (by omega), closeSlots]
  | succ n ih =>
      rw [processSlots_step, if_pos (by omega), closeSlots,
          ih (processSlot σ) (by rw [processSlot_s]; omega)]

/-! ## The invariant -/

/-- The three branch conditions of `process_height_events`, all blocked, plus a fourth conjunct the
    paper never states: with no target stored, no target bit is set.

    The fourth is what makes the invariant survive `process_slot`. That routine writes
    `T_h ← L` when `T_h` is `⊥`, which flips the second branch's `T_h ≠ ⊥` from blocking to live;
    the fourth conjunct closes the hole through the quorum clause instead, the target quorum being
    empty exactly while `T_h` is. It is true for a reason visible only in Figure 2: the only writer
    of a target bit needs `T_h ≠ ⊥`. -/
structure Settled (σ : ChainState Node Root) : Prop where
  /-- The finality branch is blocked. -/
  fin : ¬ (σ.h_j > σ.h_F ∧ σ.F ⪯ σ.J ∧ w(σ.P)≥q)
  /-- The target branch is blocked. -/
  tgt : ¬ (¬ σ.nj ∧ σ.T_h ≠ ⊥ ∧ w(σ.Qtarget)≥q)
  /-- The progress branch is blocked. -/
  prog : ¬ (w(σ.Qprog)≥q)
  /-- Not in the paper. See the structure's docstring. -/
  emptyTarget : σ.T_h = ⊥ → σ.Qtarget = ∅

/-- Under `Settled` the height-event check does nothing, which is the paper's prose argument made
    into a lemma. -/
theorem processHeightEvents_of_settled {σ : ChainState Node Root} (hs : Settled σ) (st : Time) :
    processHeightEvents σ st = σ := by
  simp only [processHeightEvents]
  rw [if_neg hs.fin, if_neg hs.tgt, if_neg hs.prog]
  rfl

/-- Naming a target keeps every branch blocked, **given a positive threshold**: the target quorum
    is empty while `T_h` is, and this write does not touch it. `0 < q` is a real hypothesis — on an
    empty electorate `q = ⌈2W/3⌉` is `0` and every set is a quorum. -/
theorem settled_setTarget {σ : ChainState Node Root} (hs : Settled σ) (hq : 0 < q Node)
    (hT : σ.T_h = ⊥) : Settled { σ with T_h := some σ.L } := by
  have hQ : σ.Qtarget = ∅ := hs.emptyTarget hT
  refine ⟨hs.fin, ?_, hs.prog, ?_⟩
  · rintro ⟨-, -, hw⟩
    have hQe : ({ σ with T_h := some σ.L } : ChainState Node Root).Qtarget = σ.Qtarget := rfl
    rw [hQe, hQ] at hw
    exact not_quorum_empty hq hw
  · intro h; exact absurd h (by simp)

/-- `Settled` survives a move of the cursor: no branch condition mentions `s`. -/
theorem settled_bump {σ : ChainState Node Root} (hs : Settled σ) (n : Time) :
    Settled { σ with s := n } :=
  ⟨hs.fin, hs.tgt, hs.prog, hs.emptyTarget⟩

/-! ## Closing slots moves `s` and at most `T_h` -/

/-- One closed slot: the state moves only at `s` and possibly `T_h`, and stays `Settled`. -/
theorem processSlot_of_settled {σ : ChainState Node Root} (hs : Settled σ) (hq : 0 < q Node) :
    ∃ Th, (Th = σ.T_h ∨ Th = some σ.L) ∧
      processSlot σ = { σ with s := σ.s + 1, T_h := Th } ∧ Settled (processSlot σ) := by
  simp only [processSlot]
  by_cases h1 : σ.T_h = ⊥ ∧ σ.L.slot ≥ σ.s_h
  · have hset := settled_setTarget hs hq h1.1
    refine ⟨some σ.L, Or.inr rfl, ?_, ?_⟩
    · by_cases h2 : σ.L.slot < σ.s <;>
        simp [h1, h2, processHeightEvents_of_settled hset]
    · by_cases h2 : σ.L.slot < σ.s <;>
        simp only [h1, h2, if_true, if_false, processHeightEvents_of_settled hset] <;>
        exact settled_bump hset _
  · refine ⟨σ.T_h, Or.inl rfl, ?_, ?_⟩
    · by_cases h2 : σ.L.slot < σ.s <;>
        simp [h1, h2, processHeightEvents_of_settled hs]
    · by_cases h2 : σ.L.slot < σ.s <;>
        simp only [h1, h2, if_true, if_false, processHeightEvents_of_settled hs] <;>
        exact settled_bump hs _

/-- Any number of closed slots. The witness for `T_h` is carried through the induction, which is
    the small strengthening that lets the caller state a record equation rather than a list of
    fields that do not move. -/
theorem closeSlots_of_settled (n : Nat) {σ : ChainState Node Root} (hs : Settled σ)
    (hq : 0 < q Node) :
    ∃ Th, (Th = σ.T_h ∨ Th = some σ.L) ∧
      closeSlots n σ = { σ with s := σ.s + n, T_h := Th } ∧ Settled (closeSlots n σ) := by
  induction n generalizing σ with
  | zero => exact ⟨σ.T_h, Or.inl rfl, by simp [closeSlots], by simpa [closeSlots] using hs⟩
  | succ n ih =>
      obtain ⟨Th₁, hTh₁, heq₁, hs₁⟩ := processSlot_of_settled hs hq
      obtain ⟨Th₂, hTh₂, heq₂, hs₂⟩ := ih hs₁
      refine ⟨Th₂, ?_, ?_, by simpa [closeSlots] using hs₂⟩
      · rcases hTh₂ with h | h
        · rw [h, heq₁]; exact hTh₁
        · rw [h, heq₁]; exact Or.inr rfl
      · rw [closeSlots, heq₂, heq₁]
        simp [Nat.add_assoc, Nat.add_comm 1 n]

/-! ### Figure 2's routines, as far as `Settled` needs them

`process_block` cannot preserve `Settled`: it is where the target and progress tallies are built,
which is the routine doing its job. What it does preserve is `emptyTarget`, and the reason is
visible only in Figure 2 — line 778 is the only writer of a target bit, and it needs `T_h ≠ ⊥`.
-/

/-- `process_attestation` never touches `T_h`. -/
theorem processAttestation_T_h (σ : ChainState Node Root) (a : Attestation Node Root)
    (A : Blk Node Root) : (processAttestation σ a A).T_h = σ.T_h := by
  simp only [processAttestation]; repeat' split
  all_goals rfl

/-- …and it sets no target bit while no target is named. Figure 2, line 778.

    `hT` has to be restated as `σ.T_h = none` before it can be used: `⊥` is a `Bot (Option _)`
    instance rather than a constructor, so `simp only` with it leaves a `match …, ⊥ with` that
    `split` cannot reduce. The coercion is definitional, so `have` accepts it with no proof. -/
theorem processAttestation_target {σ : ChainState Node Root} (a : Attestation Node Root)
    (A : Blk Node Root) (hT : σ.T_h = ⊥) :
    (processAttestation σ a A).targetParticipation = σ.targetParticipation := by
  have hT' : σ.T_h = none := hT
  cases hp : a.heightPair <;>
    simp only [processAttestation, hT', hp] <;> (repeat' split) <;> rfl

theorem processAttestations_cons (σ : ChainState Node Root) (a : Attestation Node Root)
    (as : List (Attestation Node Root)) (A : Blk Node Root) :
    processAttestations σ (a :: as) A = processAttestations (processAttestation σ a A) as A := by
  simp [processAttestations]

/-- The fold, by induction on the list: while no target is named it sets no target bit and leaves
    `T_h` alone. -/
theorem processAttestations_target {σ : ChainState Node Root}
    (as : List (Attestation Node Root)) (A : Blk Node Root) (hT : σ.T_h = ⊥) :
    (processAttestations σ as A).targetParticipation = σ.targetParticipation ∧
      (processAttestations σ as A).T_h = σ.T_h := by
  induction as generalizing σ with
  | nil => exact ⟨rfl, rfl⟩
  | cons a as ih =>
      have hT1 : (processAttestation σ a A).T_h = ⊥ := by rw [processAttestation_T_h]; exact hT
      obtain ⟨h1, h2⟩ := ih (σ := processAttestation σ a A) hT1
      rw [processAttestations_cons]
      exact ⟨by rw [h1, processAttestation_target a A hT],
             by rw [h2, processAttestation_T_h]⟩

/-! ### `advance_height` resets both tallies and the target

Which is what re-establishes `Settled` after a height transition: with `T_h` back to `⊥` and both
arrays back to `false^V`, the target and progress branches are blocked again and `emptyTarget`
holds afresh.
-/

theorem advanceHeight_T_h (σ : ChainState Node Root) (j : Option (Blk Node Root)) (st : Time) :
    (advanceHeight σ j st).T_h = ⊥ := by
  simp only [advanceHeight]; repeat' split
  all_goals rfl

theorem advanceHeight_target (σ : ChainState Node Root) (j : Option (Blk Node Root)) (st : Time) :
    (advanceHeight σ j st).targetParticipation = fun _ => false := by
  simp only [advanceHeight]; repeat' split
  all_goals rfl

theorem advanceHeight_progress (σ : ChainState Node Root) (j : Option (Blk Node Root))
    (st : Time) : (advanceHeight σ j st).progress = fun _ => false := by
  simp only [advanceHeight]; repeat' split
  all_goals rfl

theorem advanceHeight_Qtarget (σ : ChainState Node Root) (j : Option (Blk Node Root))
    (st : Time) : (advanceHeight σ j st).Qtarget = ∅ := by
  simp [ChainState.Qtarget, advanceHeight_target]

theorem advanceHeight_Qprog (σ : ChainState Node Root) (j : Option (Blk Node Root))
    (st : Time) : (advanceHeight σ j st).Qprog = ∅ := by
  simp [ChainState.Qprog, advanceHeight_progress]

/-- `Settled` holds at genesis. Both tallies are `V.filter (fun _ => false)`, so the target and
    progress branches are blocked by `not_quorum_empty`; the finality branch fails on
    `h_j = h_F = 0`; and `emptyTarget` is vacuous, genesis being its own current-height target. -/
theorem settled_gen [PositiveWeight Node] :
    Settled (ChainState.gen (Node := Node) (Root := Root)) := by
  have hq : 0 < q Node := q_pos
  have hQt : (ChainState.gen (Node := Node) (Root := Root)).Qtarget = ∅ := by
    simp [ChainState.Qtarget, ChainState.gen]
  have hQp : (ChainState.gen (Node := Node) (Root := Root)).Qprog = ∅ := by
    simp [ChainState.Qprog, ChainState.gen]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨h1, -, -⟩; simp [ChainState.gen] at h1
  · rintro ⟨-, -, hw⟩; rw [hQt] at hw; exact not_quorum_empty hq hw
  · intro hw; rw [hQp] at hw; exact not_quorum_empty hq hw
  · intro h; simp [ChainState.gen] at h

/-! ## Lemma 3 -/

/-- Every block post-state is `Settled`.

    **Outstanding.** This is the one gap left in Lemma 3. It is where `process_block` and
    `process_height_events` have to be analysed, and the invariant does not survive
    `process_block` — target and progress quorums are built there, which is the routine doing its
    job — so it wants the split the `lean-proof-idioms` skill describes: a core that rides the whole
    transition, with `process_height_events` re-establishing the rest at the end.

    `0 < q` will come from the same place it does elsewhere: any electorate member gives it. -/
theorem settled_of_blockPostState [PositiveWeight Node] {σ : ChainState Node Root}
    (h : BlockPostState σ) : Settled σ := by
  sorry

/-- Lemma 3 (`lem:empty-slot-noop`), as a record equation: closing slots up to `t` moves `s` to
    `max σ.s t` and may fill `T_h` with `σ.L`, and moves nothing else.

    `T_h` is left open rather than pinned exactly. Pinning it needs the induction to split `n = 0`
    from `n ≥ 1`, and nothing yet needs to know *which* target was named. -/
theorem emptySlotNoop [PositiveWeight Node] {σ : ChainState Node Root} (t : Time)
    (h : BlockPostState σ) :
    ∃ Th, (Th = σ.T_h ∨ Th = some σ.L) ∧
      actionState σ t = { σ with s := max σ.s t, T_h := Th } := by
  obtain ⟨Th, hTh, heq, -⟩ :=
    closeSlots_of_settled (t - σ.s) (settled_of_blockPostState h) q_pos
  refine ⟨Th, hTh, ?_⟩
  rw [actionState, processSlots_eq_closeSlots, heq]
  by_cases hle : σ.s ≤ t
  · rw [Nat.max_eq_right hle, Nat.add_sub_cancel' hle]
  · rw [Nat.max_eq_left (by omega)]
    have h0 : t - σ.s = 0 := by omega
    rw [h0]; simp

end Proofs

end Decoupled
