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

/-- **The post-state of `B`**: replay `B`'s own chain and return where it ends, or `invalid` if any
    step of it fails. A function of the block alone.

    This is what the paper writes `σ[B]`. The paper never defines that notation: its meaning comes
    from Definition 19 (`def:valid-block`), where a block's replay starts "from the parent's
    post-state", and from Figure 3 (`alg:store`), which tabulates those values. So there is no
    numbered definition to cite, and this does not claim to render one.

    Structural recursion on the block — the recursive call is on `p`, a constructor argument — so
    there is no measure and no termination obligation, and it is computable.

    **Same value as `σ[B]`, on more blocks.** Figure 3's `σ` is a partial map whose domain is the
    accepted set `𝒜`, and a block enters it only when the structural precheck passes, the transition
    returns a state, the block's claimed post-state root equals `root(σ')`, and its slot has started
    by the store clock. Of those four, this replays the transition alone. So the checks sit in `σ`'s
    *domain*, not in its value: where both give a state it is the same state, and this gives one for
    blocks Figure 3 would have rejected — a block whose `claimedRoot` disagrees with its own
    post-state, for instance.

    A hypothesis of the form `postState B = .state σ` is therefore **weaker** than the paper's "for
    an accepted block `B`", which makes a theorem carrying it stronger. That is safe while an
    argument uses none of the three unmodelled checks; a proof needing the claimed root to tie a
    block to a state, or needing proposer equivocation to be the only source of two valid blocks in
    one slot, would want those modelled first.

    An earlier `replayChain` was withdrawn for calling itself `σ[B]` while dropping those checks
    silently. Naming the difference is the fix. -/
def postState {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] : Blk Node Root → TransitionResult Node Root
  | .genesis => .state ChainState.gen
  | .mk p s n as r =>
      match postState p with
      | .state σp => stateTransition σp (.mk p s n as r)
      | invalid => invalid

/-- `B`'s own chain replays without failing. A name for `postState B ≠ invalid`, so that a
    statement or a hypothesis can say what the condition means rather than how it is written. -/
def Replayable {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] (B : Blk Node Root) : Prop := postState B ≠ invalid

/-- The post-state at `B`, defined exactly on the blocks that replay. Its result type is
    `ChainState`, with no failure case: `invalid` has not been removed from the world but from the
    *domain*, since the function cannot be applied where the replay fails. Nothing is fabricated,
    which is what a total `postState` with a default value would have to do.

    A function "defined only where the replay succeeds" is a function that takes the proof. Writing
    it over a subtype, `{B // Replayable B} → ChainState …`, is the same thing with the pair packed:
    in Lean the restriction of the domain *is* the proof argument.

    The proof is an **autoparam**, filled by `assumption` from the local context, so `postState' T`
    can be written bare wherever `Replayable T` is already a hypothesis — including under a binder
    that introduces it, as in `∃ _ : Replayable T, (postState' T).h = σ.h`. It can still be passed
    explicitly. What this hides is the writing of the proof, not the proof: the elaborated term
    contains it, so rewriting `postState B` afterwards still meets "motive is not type correct". -/
def postState' {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] (B : Blk Node Root)
    (h : Replayable B := by assumption) : ChainState Node Root :=
  (postState B).get h

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
visible only in Figure 2 (`alg:attestation-processing`) — line 778 is the only writer
of a target bit, and it needs `T_h ≠ ⊥`.
-/

/-- `process_attestation` never touches `T_h`. -/
theorem processAttestation_T_h (σ : ChainState Node Root) (a : Attestation Node Root)
    (A : Blk Node Root) : (processAttestation σ a A).T_h = σ.T_h := by
  simp only [processAttestation]; repeat' split
  all_goals rfl

/-- …and it sets no target bit while no target is named. Figure 2
    (`alg:attestation-processing`), line 778.

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

/-- `T_h` survives the fold whatever the attestations say, which is what lets the block phase
    be analysed without knowing whether a target is named. -/
theorem processAttestations_T_h {σ : ChainState Node Root}
    (as : List (Attestation Node Root)) (A : Blk Node Root) :
    (processAttestations σ as A).T_h = σ.T_h := by
  induction as generalizing σ with
  | nil => rfl
  | cons a as ih => rw [processAttestations_cons, ih, processAttestation_T_h]

/-- The fold preserves `emptyTarget`. Read: if the fold left no target named, then it set no
    target bit either, so the target tally is still empty. -/
theorem processAttestations_emptyTarget {σ : ChainState Node Root}
    (as : List (Attestation Node Root)) (A : Blk Node Root)
    (hET : σ.T_h = ⊥ → σ.Qtarget = ∅) :
    (processAttestations σ as A).T_h = ⊥ → (processAttestations σ as A).Qtarget = ∅ := by
  intro h
  rw [processAttestations_T_h] at h
  obtain ⟨hp, -⟩ := processAttestations_target as A h
  simp only [ChainState.Qtarget, hp]
  exact hET h

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

/-! ### A height transition lands in a settled state -/

theorem advanceHeight_F (σ : ChainState Node Root) (j : Option (Blk Node Root)) (st : Time) :
    (advanceHeight σ j st).F = σ.F := by
  simp only [advanceHeight]; repeat' split
  all_goals rfl

theorem advanceHeight_h_F (σ : ChainState Node Root) (j : Option (Blk Node Root)) (st : Time) :
    (advanceHeight σ j st).h_F = σ.h_F := by
  simp only [advanceHeight]; repeat' split
  all_goals rfl

/-- A justifying transition clears `P`, which is what blocks the finality branch afterwards. -/
theorem advanceHeight_P_some (σ : ChainState Node Root) (T : Blk Node Root) (st : Time) :
    (advanceHeight σ (some T) st).P = ∅ := by
  simp only [advanceHeight]; repeat' split
  all_goals rfl

theorem advanceHeight_none_J (σ : ChainState Node Root) (st : Time) :
    (advanceHeight σ none st).J = σ.J := by
  simp only [advanceHeight]; repeat' split
  all_goals rfl

theorem advanceHeight_none_h_j (σ : ChainState Node Root) (st : Time) :
    (advanceHeight σ none st).h_j = σ.h_j := by
  simp only [advanceHeight]; repeat' split
  all_goals rfl

theorem advanceHeight_none_P (σ : ChainState Node Root) (st : Time) :
    (advanceHeight σ none st).P = σ.P := by
  simp only [advanceHeight]; repeat' split
  all_goals rfl

/-- **A height transition lands in a `Settled` state.** The target and both tallies are reset, which
    blocks the target and progress branches. The finality branch is blocked two different ways
    depending on the transition: a justifying one clears `P`, so no quorum of finality commitments
    remains; a progress one leaves the finality fields untouched, so whatever blocked that branch
    before still does — which is why `hfin` is a hypothesis rather than a consequence. -/
theorem settled_advanceHeight {σ : ChainState Node Root} (hq : 0 < q Node)
    (j : Option (Blk Node Root)) (st : Time)
    (hfin : ¬(σ.h_j > σ.h_F ∧ σ.F ⪯ σ.J ∧ w(σ.P)≥q)) : Settled (advanceHeight σ j st) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases j with
    | none =>
        rw [advanceHeight_none_h_j, advanceHeight_h_F, advanceHeight_F, advanceHeight_none_J,
            advanceHeight_none_P]
        exact hfin
    | some T =>
        rintro ⟨-, -, hw⟩
        rw [advanceHeight_P_some] at hw
        exact not_quorum_empty hq hw
  · rintro ⟨-, hT, -⟩; exact hT (advanceHeight_T_h σ j st)
  · intro hw; rw [advanceHeight_Qprog] at hw; exact not_quorum_empty hq hw
  · intro _; exact advanceHeight_Qtarget σ j st

/-- **The height-event check lands in a `Settled` state, whatever it does.** Read: after
    `process_height_events` all three of Definition 18's branches are blocked, and the target
    tally is empty if no target is named — and the only thing needed of the state beforehand is
    that last part.

    The three branches close three different ways. A target or progress transition is
    `settled_advanceHeight`. The fall-through is `Settled` by construction, taking the negations
    of the three conditions that did not fire. And whenever the finality sub-step *did* fire, the
    finality branch is blocked afterwards for a reason of its own: that step sets `h_F ← h_j`, so
    `h_j > h_F` is `h_j > h_j`.

    Two things make the tactic work, both measured. `Id.run` has to be in the `simp only` set or
    the goals keep a `pure (…).run` wrapper and `split_ifs` cannot see the `if`s underneath. And
    the six leaves are closed by `first | …` on hypotheses found by `assumption` rather than by
    name: `split_ifs` discharges the branches that contradict, so which name lands on which leaf
    is not stable. -/
theorem settled_processHeightEvents {σ : ChainState Node Root} (hq : 0 < q Node) (st : Time)
    (hET : σ.T_h = ⊥ → σ.Qtarget = ∅) : Settled (processHeightEvents σ st) := by
  simp only [processHeightEvents, Id.run]
  split_ifs <;>
    first
      | exact settled_advanceHeight hq _ _
          (by rintro ⟨hlt, -, -⟩; exact absurd hlt (Nat.lt_irrefl _))
      | exact settled_advanceHeight hq _ _ (by assumption)
      | exact ⟨by rintro ⟨hlt, -, -⟩; exact absurd hlt (Nat.lt_irrefl _),
               by assumption, by assumption, hET⟩
      | exact ⟨by assumption, by assumption, by assumption, hET⟩

/-! ### The two figures' `invalid` branches, inverted

Both `process_block` and `state_transition` return `invalid` on a failed check, so a hypothesis
`… = .state σ'` says which branch ran. `split_ifs at h` and `split at h` discharge the
contradictory branches themselves — `pure invalid = .state σ'` is closed by `injection` — so what
is left is the successful path, in the shape the invariant needs.
-/

/-- On the successful path `process_block` is the attestation fold, run on the state whose latest
    block is already `B`, against the parent as the ancestor argument. -/
theorem processBlock_state {σ σ' : ChainState Node Root} {B : Blk Node Root}
    (h : processBlock σ B = .state σ') :
    σ' = processAttestations { σ with L := B } B.attestations σ.L := by
  simp only [processBlock, Id.run] at h
  split_ifs at h
  injection h with h
  exact h.symm

/-- `process_block`'s first check, as a fact about the block: on the successful path the block's
    parent is the state's latest block. Three proofs now need it, so it is a lemma rather than four
    lines repeated. -/
theorem processBlock_parent {σ σ' : ChainState Node Root} {B : Blk Node Root}
    (he : processBlock σ B = .state σ') : B.parent = some σ.L := by
  simp only [processBlock, Id.run] at he
  split_ifs at he with hc
  simp only [not_or, ne_eq, not_not] at hc
  exact hc.1

/-- `process_block` preserves `emptyTarget`. The `L ← B` update is invisible to it: `T_h` and the
    target tally are read off the other fields, so the fold's own lemma is the whole proof. -/
theorem processBlock_emptyTarget {σ σ' : ChainState Node Root} {B : Blk Node Root}
    (h : processBlock σ B = .state σ') (hET : σ.T_h = ⊥ → σ.Qtarget = ∅) :
    σ'.T_h = ⊥ → σ'.Qtarget = ∅ := by
  rw [processBlock_state h]
  exact processAttestations_emptyTarget _ _ hET

/-- On the successful path `state_transition` closes the slots up to `B.slot`, processes the block,
    and ends in `process_height_events`. -/
theorem stateTransition_state {σ σ' : ChainState Node Root} {B : Blk Node Root}
    (h : stateTransition σ B = .state σ') :
    ∃ σ₂, processBlock (processSlots σ B.slot) B = .state σ₂ ∧
      σ' = processHeightEvents σ₂ B.slot := by
  simp only [stateTransition, Id.run] at h
  split_ifs at h
  split at h
  · injection h
  · rename_i σ₂ hb
    injection h with h
    exact ⟨σ₂, hb, h.symm⟩

/-! ### What a height transition does to the height, and which branch did it

Lemma 6 (`lem:height-progression`) needs more than "`Settled` is restored": it needs the height to
have moved by exactly one, and it needs to know *which* branch moved it, because that decides which
certificate the block carries.
-/

theorem advanceHeight_h (σ : ChainState Node Root) (j : Option (Blk Node Root)) (st : Time) :
    (advanceHeight σ j st).h = σ.h + 1 := by
  simp only [advanceHeight]; repeat' split
  all_goals rfl

theorem advanceHeight_L (σ : ChainState Node Root) (j : Option (Blk Node Root)) (st : Time) :
    (advanceHeight σ j st).L = σ.L := by
  simp only [advanceHeight]; repeat' split
  all_goals rfl

theorem advanceHeight_J_some (σ : ChainState Node Root) (T : Blk Node Root) (st : Time) :
    (advanceHeight σ (some T) st).J = T := by
  simp only [advanceHeight]; repeat' split
  all_goals rfl

theorem advanceHeight_h_j_some (σ : ChainState Node Root) (T : Blk Node Root) (st : Time) :
    (advanceHeight σ (some T) st).h_j = σ.h := by
  simp only [advanceHeight]; repeat' split
  all_goals rfl

/-- **If the height-event check moved the height, this says which branch did it and with what.**
    Read aloud: the height went up by one, the latest block did not change, and either the target
    tally held a quorum and the named target is what got justified at the old height, or the
    progress tally held a quorum and the justification did not move.

    Everything is phrased over `σ` rather than over the state the finality sub-step leaves, which
    differs from `σ` in `F` and `h_F` only — fields none of this mentions.

    Two measured points. `cases hT : σ.T_h` comes **before** `split_ifs`, and only `hne` needs the
    rewrite afterwards: `cases` has already replaced `σ.T_h` in the goal, and doing it first is what
    turns the target branch's `advance_height σ σ.T_h st` into `advance_height σ (some T) st`, which
    the field lemmas above can read. Second, the leaves are closed with `exact`, not `rw`: the goals
    carry a `pure` wrapper that `rw` will not see through, and `exact` unifies up to it. -/
theorem processHeightEvents_advance (σ : ChainState Node Root) (st : Time)
    (hne : (processHeightEvents σ st).h ≠ σ.h) :
    (processHeightEvents σ st).h = σ.h + 1 ∧ (processHeightEvents σ st).L = σ.L ∧
      ((w(σ.Qtarget)≥q ∧ σ.T_h = some (processHeightEvents σ st).J ∧
          (processHeightEvents σ st).h_j = σ.h)
        ∨ (w(σ.Qprog)≥q ∧ (processHeightEvents σ st).J = σ.J)) := by
  simp only [processHeightEvents, Id.run] at hne ⊢
  cases hT : σ.T_h with
  | none =>
      rw [hT] at hne
      split_ifs at hne ⊢ <;>
        first
          | exact absurd rfl hne
          | (rename_i hb; exact absurd rfl hb.2.1)
          | (rename_i hb
             exact ⟨advanceHeight_h _ _ _, advanceHeight_L _ _ _,
               Or.inr ⟨hb, advanceHeight_none_J _ _⟩⟩)
  | some T =>
      rw [hT] at hne
      split_ifs at hne ⊢ <;>
        first
          | exact absurd rfl hne
          | (rename_i hb
             exact ⟨advanceHeight_h _ _ _, advanceHeight_L _ _ _,
               Or.inl ⟨hb.2.2, congrArg some (advanceHeight_J_some _ _ _).symm,
                 advanceHeight_h_j_some _ _ _⟩⟩)
          | (rename_i hb
             exact ⟨advanceHeight_h _ _ _, advanceHeight_L _ _ _,
               Or.inr ⟨hb, advanceHeight_none_J _ _⟩⟩)

/-- **If the height-event check left a target named, it did nothing else either.** Read: a state
    whose `T_h` is still filled after the check has the same height, latest block and target as
    before it.

    The reason is one field: `advance_height` always writes `T_h ← ⊥`, so a filled `T_h` afterwards
    says no branch fired, and the remaining leaves change only `F` and `h_F`. This is the
    complement of `processHeightEvents_advance` and the two together cover the check. -/
theorem processHeightEvents_of_target (σ : ChainState Node Root) (st : Time)
    (hT : (processHeightEvents σ st).T_h ≠ ⊥) :
    (processHeightEvents σ st).h = σ.h ∧ (processHeightEvents σ st).L = σ.L ∧
      (processHeightEvents σ st).T_h = σ.T_h := by
  simp only [processHeightEvents, Id.run] at hT ⊢
  split_ifs at hT ⊢ <;>
    first
      | exact absurd (advanceHeight_T_h _ _ _) hT
      | exact ⟨rfl, rfl, rfl⟩

/-! ## Lemma 3 -/

/-- **A whole transition lands in a `Settled` state.** This is the split the invariant needs, and
    the three phases each play a different part:

    * `process_slots` preserves all of `Settled` (`closeSlots_of_settled`);
    * `process_block` preserves `emptyTarget` and nothing else, because building the target and
      progress tallies is what that routine is for;
    * `process_height_events` re-establishes the rest from `emptyTarget` alone
      (`settled_processHeightEvents`).

    So `Settled` is not preserved phase by phase. Only `emptyTarget` is threaded end to end, and
    the last phase rebuilds the other three conjuncts. -/
theorem settled_stateTransition {σ σ' : ChainState Node Root} (hs : Settled σ) (hq : 0 < q Node)
    {B : Blk Node Root} (h : stateTransition σ B = .state σ') : Settled σ' := by
  obtain ⟨σ₂, hb, rfl⟩ := stateTransition_state h
  obtain ⟨-, -, -, hs₁⟩ := closeSlots_of_settled (B.slot - σ.s) hs hq
  rw [← processSlots_eq_closeSlots] at hs₁
  exact settled_processHeightEvents hq _ (processBlock_emptyTarget hb hs₁.emptyTarget)

/-- **Every block post-state is `Settled`.** The induction over `BlockPostState`: `settled_gen` at
    genesis, `settled_stateTransition` at each accepted block.

    `0 < q` comes from `PositiveWeight` here, at the one place the assumption is needed; the
    machinery above takes it as a plain hypothesis so that it does not depend on where the
    assumption is defined. -/
theorem settled_of_blockPostState [PositiveWeight Node] {σ : ChainState Node Root}
    (h : BlockPostState σ) : Settled σ := by
  induction h with
  | gen => exact settled_gen
  | step _ hst ih => exact settled_stateTransition ih q_pos hst

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
