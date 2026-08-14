import Analysis.Proofs.Ancestry

/-!
# A block determines its post-state

    BlockPostState σ → BlockPostState σ' → σ.L = σ'.L → σ = σ'

This is what lets a statement say "**the** post-state of `B`" rather than "some post-state of `B`".
The paper says the first — `σ[B]` is a map — and this project has no such map, Figure 3
(`alg:store`) not being rendered. What it has is `BlockPostState`, a predicate, and an existential
over a predicate is a weaker claim than a definite description. This file closes that gap without
Figure 3.

## Why it holds, and why it needs no assumption

`state_transition` is a function, and `process_block` checks `B.parent = some σ.L`. So the post-state
of a block is determined by the post-state of its parent, which is determined by the post-state of
*its* parent, and so on down to genesis — where `ChainState.gen` is the only post-state, because
every step's block has a parent and genesis has none.

The recursion is on the **block**, not on the `BlockPostState` derivation: two derivations for the
same block may have different shapes, and it is the block that pins the state. Nothing here needs a
threshold or a fault bound, which is why the `L` lemmas below are proved without `PositiveWeight` —
Lemma 3's record equation would have supplied them, at the cost of an assumption this argument does
not otherwise want.

## The predicate and the function agree

`postState` (`Analysis/Proofs/SlotClosure.lean`) replays a block's own chain and returns a
`TransitionResult`. `BlockPostState` says the same thing as a predicate. The last section of this
file relates them in both directions, so a statement may use whichever shape reads better:

    postState B = .state σ  →  BlockPostState σ
    BlockPostState σ        →  postState σ.L = .state σ

Together they make `postState` a definite description where `BlockPostState` is an existential. That
is a second route to `postState_unique`, and the reason a statement about "the post-state of `T`"
need no longer be written in two halves.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]

/-! ## `L` through the routines, with no threshold hypothesis -/

theorem processHeightEvents_L (σ : ChainState Node Root) (st : Time) :
    (processHeightEvents σ st).L = σ.L := by
  simp only [processHeightEvents, Id.run]
  split_ifs <;> first | exact advanceHeight_L _ _ _ | rfl

theorem processSlot_L (σ : ChainState Node Root) : (processSlot σ).L = σ.L := by
  simp only [processSlot, Id.run]
  split_ifs <;> first | exact processHeightEvents_L _ _ | rfl

theorem closeSlots_L : ∀ (n : Nat) (σ : ChainState Node Root), (closeSlots n σ).L = σ.L
  | 0, _ => by rw [closeSlots]
  | n + 1, _ => by rw [closeSlots, closeSlots_L n, processSlot_L]

theorem processSlots_L (σ : ChainState Node Root) (t : Time) :
    (processSlots σ t).L = σ.L := by
  rw [processSlots_eq_closeSlots, closeSlots_L]

/-- A transition's post-state has the block as its latest block. -/
theorem stateTransition_L {σp σ : ChainState Node Root} {B : Blk Node Root}
    (ht : stateTransition σp B = .state σ) : σ.L = B := by
  obtain ⟨σ₂, hb, rfl⟩ := stateTransition_state ht
  have h1 : σ₂.L = B := by
    rw [processBlock_state hb, (processAttestations_chainFields B.attestations _).1]
  rw [processHeightEvents_L, h1]

/-! ## Determinism -/

/-- Genesis has exactly one post-state. Every step's block has a parent, and genesis has none. -/
theorem blockPostState_genesis {σ : ChainState Node Root} (h : BlockPostState σ)
    (hL : σ.L = Blk.genesis) : σ = ChainState.gen := by
  cases h with
  | gen => rfl
  | step hp hst =>
      rename_i σp B
      have hLB : σ.L = B := stateTransition_L hst
      obtain ⟨σ₂, hb, -⟩ := stateTransition_state hst
      have hpar := processBlock_parent hb
      rw [← hLB, hL] at hpar
      simp [Blk.parent] at hpar

/-- **A block determines its post-state.** Read aloud: two block post-states whose latest block is
    the same block are the same state.

    By structural recursion on the block. At genesis, `blockPostState_genesis`. At a child, both
    states came from a transition on that child, and `process_block`'s parent check puts both parent
    states' latest block at the parent — so the recursion identifies the parent states, and
    `state_transition` being a function identifies the two. -/
theorem postState_unique : ∀ (B : Blk Node Root) {σ σ' : ChainState Node Root},
    BlockPostState σ → BlockPostState σ' → σ.L = B → σ'.L = B → σ = σ'
  | .genesis, _, _, h, h', hL, hL' => by
      rw [blockPostState_genesis h hL, blockPostState_genesis h' hL']
  | .mk p s n as r, σ, σ', h, h', hL, hL' => by
      cases h with
      | gen => simp [ChainState.gen] at hL
      | step hp hst =>
          rename_i σp B
          have hB : B = Blk.mk p s n as r := by rw [← stateTransition_L hst, hL]
          subst hB
          cases h' with
          | gen => simp [ChainState.gen] at hL'
          | step hp' hst' =>
              rename_i σp' B'
              have hB' : B' = Blk.mk p s n as r := by rw [← stateTransition_L hst', hL']
              subst hB'
              obtain ⟨σ₂, hb, -⟩ := stateTransition_state hst
              obtain ⟨σ₂', hb', -⟩ := stateTransition_state hst'
              have hp1 : σp.L = p := by
                have := processBlock_parent hb
                rw [processSlots_L] at this
                simp only [Blk.parent, Option.some.injEq] at this
                exact this.symm
              have hp2 : σp'.L = p := by
                have := processBlock_parent hb'
                rw [processSlots_L] at this
                simp only [Blk.parent, Option.some.injEq] at this
                exact this.symm
              have : σp = σp' := postState_unique p hp hp' hp1 hp2
              subst this
              simpa using hst.symm.trans hst'

/-! ## The predicate and the function agree -/

/-- What `postState` returns is a block post-state. Structural recursion on the block: genesis is
    `BlockPostState.gen`, and a child's replay is its parent's replay followed by one transition,
    which is `BlockPostState.step`. -/
theorem blockPostState_of_postState : ∀ (B : Blk Node Root) {σ : ChainState Node Root},
    postState B = .state σ → BlockPostState σ
  | .genesis, σ, h => by
      simp only [postState, TransitionResult.state.injEq] at h
      exact h ▸ .gen
  | .mk p s n as r, σ, h => by
      rw [postState] at h
      rcases hp : postState p with ⟨σp⟩ | _
      · rw [hp] at h
        exact .step (blockPostState_of_postState p hp) h
      · rw [hp] at h
        simp at h

/-- The converse: a block post-state is what `postState` returns for its own latest block. So the
    replay never fails on a block that has a post-state, and the two agree on the state.

    Induction on the derivation, not on the block, because the step gives the parent's state
    directly. `process_block`'s parent check is what identifies the parent of `σ.L` with the block
    of the induction hypothesis. -/
theorem postState_of_blockPostState {σ : ChainState Node Root} (h : BlockPostState σ) :
    postState σ.L = .state σ := by
  induction h with
  | gen => rfl
  | @step σp σ' B hp hst ih =>
      have hLB : σ'.L = B := stateTransition_L hst
      obtain ⟨σ₂, hb, -⟩ := stateTransition_state hst
      have hpar : B.parent = some σp.L := by
        rw [← processSlots_L σp B.slot]; exact processBlock_parent hb
      cases B with
      | genesis => simp [Blk.parent] at hpar
      | mk p s n as r =>
          simp only [Blk.parent, Option.some.injEq] at hpar
          have hpp : postState p = .state σp := by rw [hpar]; exact ih
          rw [hLB, postState, hpp]
          exact hst

end Proofs

end Decoupled
