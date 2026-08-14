import Analysis.Proofs.Certificates
import Analysis.Proofs.Determinism

/-!
# Where a named target sits

Lemma 7 (`lem:height-target-freshness`, `height_filter_healing.tex:1002-1009`) says three things
about a counted target bit. The first is `Witnessed.target`, already proved in
`Analysis/Proofs/Witnessed.lean`: the vote behind the bit names the stored target. The other two are
about the stored target itself, and this file proves them:

* it strictly precedes the chain's latest block;
* its own post-state — *the* post-state, by `postState_unique` — is at the current height.

## The invariant is *not* preserved step by step, and that is the point

`process_slot` writes `T_h ← some σ.L`, so right after that write the target **is** the latest block
— strictness is false at that moment. It becomes true again because `process_block` moves `L` to the
child. So strictness holds of block post-states and of nothing smaller, and the induction here is
over `BlockPostState` with a whole transition as its step, the way `Chained` is proved rather than
the way `Settled` is.

## Two claims, split by where genesis sits

`Fresh` carries the two claims that hold **unconditionally**: the target is on the chain
(non-strictly), and it has a post-state at the current height. Strictness is separate, in
`prec_of_target`, because it is false at genesis — there `T_h = some genesis` and `L = genesis`. That
costs nothing: at genesis no bit is set, so Lemma 7's own hypothesis excludes it, and `prec_of_target`
takes `σ.Qtarget.Nonempty` for exactly that case and uses it nowhere else.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]

/-! ## The invariant -/

/-- What holds of a named target in every block post-state, genesis included. -/
structure Fresh (σ : ChainState Node Root) : Prop where
  /-- The named target is on this chain. Non-strict, so that genesis is included. -/
  onChain : ∀ T, σ.T_h = some T → T ⪯ σ.L
  /-- The named target has a post-state, and it sits at the current height. Stated as an
      existential inside the invariant, because that is what the step case produces; `anchorAll`
      below turns it into the paper's "*the* post-state at `T`" with `postState_unique`. -/
  anchor : ∀ T, σ.T_h = some T →
    ∃ σT : ChainState Node Root, BlockPostState σT ∧ σT.L = T ∧ σT.h = σ.h

theorem fresh_gen : Fresh (ChainState.gen (Node := Node) (Root := Root)) where
  onChain T hT := by
    simp only [ChainState.gen, Option.some.injEq] at hT
    subst hT; exact Preceq.refl _
  anchor T hT := by
    simp only [ChainState.gen, Option.some.injEq] at hT
    subst hT
    exact ⟨ChainState.gen, .gen, rfl, rfl⟩

/-- The post-block state's target is either the parent state's or the block's own parent — the two
    values Lemma 3 says slot closure can leave, carried through the block phase, which never writes
    `T_h`. -/
theorem postBlock_target [PositiveWeight Node] {σp σ₂ : ChainState Node Root} {B : Blk Node Root}
    (hp : BlockPostState σp) (hb : processBlock (processSlots σp B.slot) B = .state σ₂) :
    σ₂.T_h = σp.T_h ∨ σ₂.T_h = some σp.L := by
  obtain ⟨Th, hdisj, heq'⟩ := emptySlotNoop B.slot hp
  have heq : processSlots σp B.slot = { σp with s := max σp.s B.slot, T_h := Th } := heq'
  have h2 : σ₂.T_h = Th := by
    rw [processBlock_state hb, processAttestations_T_h]
    show (processSlots σp B.slot).T_h = Th
    rw [heq]
  rcases hdisj with h | h
  · exact Or.inl (by rw [h2, h])
  · exact Or.inr (by rw [h2, h])

/-- A transition keeps both claims. If the post-state still names a target then no height branch
    fired, so the check moved nothing; the target is then either inherited, and the induction
    hypothesis places it before the parent's latest block, or freshly named by slot closure, in which
    case it *is* the parent's latest block and the parent state is its own post-state. -/
theorem Fresh.stateTransition [PositiveWeight Node] {σp σ : ChainState Node Root}
    {B : Blk Node Root} (ih : Fresh σp) (hp : BlockPostState σp)
    (ht : stateTransition σp B = .state σ) : Fresh σ := by
  obtain ⟨σ₂, hb, rfl⟩ := stateTransition_state ht
  obtain ⟨hh₂, hL₂, -⟩ := postBlock_fields hp hb
  have hpar : B.parent = some σp.L := by
    rw [← processSlots_L σp B.slot]; exact processBlock_parent hb
  have hLB : σp.L ⪯ B := parent_preceq hpar
  refine ⟨?_, ?_⟩
  · intro T hT
    obtain ⟨-, hL, hTh⟩ := processHeightEvents_of_target σ₂ B.slot (by rw [hT]; simp)
    rw [hTh] at hT
    rw [hL, hL₂]
    rcases postBlock_target hp hb with h | h
    · exact Preceq.trans (ih.onChain T (by rw [← h]; exact hT)) hLB
    · rw [h, Option.some.injEq] at hT
      rw [← hT]; exact hLB
  · intro T hT
    obtain ⟨hh, -, hTh⟩ := processHeightEvents_of_target σ₂ B.slot (by rw [hT]; simp)
    rw [hTh] at hT
    rcases postBlock_target hp hb with h | h
    · obtain ⟨σT, h1, h2, h3⟩ := ih.anchor T (by rw [← h]; exact hT)
      exact ⟨σT, h1, h2, by rw [h3, ← hh₂, ← hh]⟩
    · rw [h, Option.some.injEq] at hT
      exact ⟨σp, hp, hT, by rw [← hh₂, ← hh]⟩

theorem fresh_of_blockPostState [PositiveWeight Node] {σ : ChainState Node Root}
    (h : BlockPostState σ) : Fresh σ := by
  induction h with
  | gen => exact fresh_gen
  | step hp hst ih => exact ih.stateTransition hp hst

/-! ## Strictness, which is false at genesis and nowhere else -/

/-- **The named target strictly precedes the latest block**, whenever any target bit is counted.

    `Qtarget.Nonempty` is used for the genesis case alone, where `T_h = some genesis` and
    `L = genesis` and no bit is set. Every other block post-state is the result of a transition, and
    there the block phase has already moved `L` past the target — so strictness needs no hypothesis
    and the case analysis is the same one `Fresh.stateTransition` runs. -/
theorem prec_of_target [PositiveWeight Node] {σ : ChainState Node Root} (h : BlockPostState σ)
    (hne : σ.Qtarget.Nonempty) (T : Blk Node Root) (hT : σ.T_h = some T) : T ≺ σ.L := by
  cases h with
  | gen =>
      obtain ⟨i, hi⟩ := hne
      simp [ChainState.Qtarget, ChainState.gen] at hi
  | step hp ht =>
      rename_i σp B
      obtain ⟨σ₂, hb, rfl⟩ := stateTransition_state ht
      obtain ⟨-, hL₂, -⟩ := postBlock_fields hp hb
      have hpar : B.parent = some σp.L := by
        rw [← processSlots_L σp B.slot]; exact processBlock_parent hb
      have hLB : σp.L ≺ B := parent_prec hpar
      obtain ⟨-, hL, hTh⟩ := processHeightEvents_of_target σ₂ B.slot (by rw [hT]; simp)
      rw [hTh] at hT
      rw [hL, hL₂]
      rcases postBlock_target hp hb with h | h
      · exact Preceq.trans_prec
          ((fresh_of_blockPostState hp).onChain T (by rw [← h]; exact hT)) hLB
      · rw [h, Option.some.injEq] at hT
        rw [← hT]; exact hLB

/-- **Every** post-state of the named target is at the current height, which is the paper's definite
    description. `Fresh.anchor` produces one such state; `postState_unique` says there is no other. -/
theorem Fresh.anchorAll [PositiveWeight Node] {σ : ChainState Node Root} (h : Fresh σ)
    (T : Blk Node Root) (hT : σ.T_h = some T) :
    (∃ σT : ChainState Node Root, BlockPostState σT ∧ σT.L = T) ∧
      ∀ σT : ChainState Node Root, BlockPostState σT → σT.L = T → σT.h = σ.h := by
  obtain ⟨σT, hbps, hLT, hh⟩ := h.anchor T hT
  refine ⟨⟨σT, hbps, hLT⟩, fun σT' hbps' hLT' => ?_⟩
  rw [postState_unique T hbps' hbps hLT' hLT]
  exact hh

/-! ## Lemma 7 -/

/-- **Lemma 7** (`lem:height-target-freshness`). Read aloud: for every validator whose target bit is
    counted, the vote behind it names the stored current-height target, that target is a strict
    ancestor of the chain's latest block, and the target's own post-state is at this height.

    Three sources, one per claim: `Witnessed.target` for the first four conjuncts, `prec_of_target`
    for strictness, `Fresh.anchor` for the post-state.

    The post-state claim is the paper's definite description, in two halves: `T` has a post-state,
    and every post-state of `T` is at this height. `postState_unique` is what makes the second half
    provable, so nothing here is weaker than the paper's sentence. -/
theorem heightTargetFreshness [PositiveWeight Node] {σ : ChainState Node Root}
    (hp : BlockPostState σ) :
    ∀ i ∈ σ.Qtarget, ∃ T a, σ.T_h = some T ∧ a.validator = i ∧
      a.heightPair = .target σ.h T ∧ IncludedOn a σ.L ∧ T ≺ σ.L ∧
      (∃ σT : ChainState Node Root, BlockPostState σT ∧ σT.L = T) ∧
      ∀ σT : ChainState Node Root, BlockPostState σT → σT.L = T → σT.h = σ.h := by
  intro i hi
  obtain ⟨T, a, hT, hv, hpair, hinc⟩ := (witnessed_of_blockPostState hp).target i hi
  obtain ⟨hex, hall⟩ := (fresh_of_blockPostState hp).anchorAll T hT
  exact ⟨T, a, hT, hv, hpair, hinc, prec_of_target hp ⟨i, hi⟩ T hT, hex, hall⟩

end Proofs

end Decoupled
