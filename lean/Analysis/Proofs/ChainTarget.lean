import Analysis.Proofs.Freshness

/-!
# Proofs: where a chain's target sits (Lemma 8)

The machinery behind `lem:chain-target-uniqueness`. `Analysis/Lemmas.lean` holds the five
statements of record and calls into here.

## The route: slots, not "first"

The paper argues Lemma 8 through "the chain's unique first block at that height". This file
reaches the same facts through one scalar equation instead: **a named target sits at the
height's start slot**,

    σ.T_h = some T  →  T.slot = σ.s_h

which is `Aligned`, the fifth invariant, after `Settled`, `Chained`, `Witnessed` and `Fresh`.
Definition 7 (`def:current-height-target`) makes `s_h` the slot of the block whose transition
entered the height, so the equation is the paper's "first block" said about one field.

What makes the scalar version sufficient is that **slots are strict along a chain**:
`state_transition` rejects `B.slot ≤ σ.s` (Figure 1, line 719), so one chain has at most one
block per slot, and two comparable blocks at one slot are equal. Uniqueness is then three
equalities: `T.slot = σ.s_h`, `s_h` agrees along one chain at one height, and `T'.slot = σ'.s_h`.

## The companion conjunct, and why the write always fires

`Aligned` carries a second field: while no target is named, the *latest block* sits at the
start slot,

    σ.T_h = ⊥  →  σ.L.slot = σ.s_h

This is what turns Figure 1's write condition `L.slot ≥ s_h` (line 739) into an equality at
the moment of recording, so the recorded target is at the start slot — and it also says the
condition *holds* whenever `T_h = ⊥`, so the first closed slot after a height transition
always records. That is Definition 7's "the following slot processing records `B` as `T_h`"
as an invariant. It survives `advance_height` because the advance writes `s_h ← start` with
the transition block as the latest block at exactly that slot, and it survives the block
phase vacuously: after one closed slot `T_h` is never `⊥` again until the next transition.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]

/-! ## Field lemmas the earlier files did not need -/

theorem advanceHeight_s_h (σ : ChainState Node Root) (j : Option (Blk Node Root)) (st : Time) :
    (advanceHeight σ j st).s_h = st := by
  simp only [advanceHeight]; repeat' split
  all_goals rfl

theorem processAttestation_s_h (σ : ChainState Node Root) (a : Attestation Node Root)
    (A : Blk Node Root) : (processAttestation σ a A).s_h = σ.s_h := by
  simp only [processAttestation]; repeat' split
  all_goals rfl

theorem processAttestations_s_h {σ : ChainState Node Root}
    (as : List (Attestation Node Root)) (A : Blk Node Root) :
    (processAttestations σ as A).s_h = σ.s_h := by
  induction as generalizing σ with
  | nil => rfl
  | cons a as ih => rw [processAttestations_cons, ih, processAttestation_s_h]

theorem processAttestation_s (σ : ChainState Node Root) (a : Attestation Node Root)
    (A : Blk Node Root) : (processAttestation σ a A).s = σ.s := by
  simp only [processAttestation]; repeat' split
  all_goals rfl

theorem processAttestations_s {σ : ChainState Node Root}
    (as : List (Attestation Node Root)) (A : Blk Node Root) :
    (processAttestations σ as A).s = σ.s := by
  induction as generalizing σ with
  | nil => rfl
  | cons a as ih => rw [processAttestations_cons, ih, processAttestation_s]

theorem closeSlots_s : ∀ (n : Nat) (σ : ChainState Node Root), (closeSlots n σ).s = σ.s + n
  | 0, _ => by rw [closeSlots]; rfl
  | n + 1, σ => by rw [closeSlots, closeSlots_s n, processSlot_s]; omega

theorem processSlots_s (σ : ChainState Node Root) (t : Time) :
    (processSlots σ t).s = max σ.s t := by
  rw [processSlots_eq_closeSlots, closeSlots_s]; omega

/-! ## The height-event check: two complements keyed on the target field

`processHeightEvents_of_target` (`SlotClosure.lean`) says a check that left `T_h` filled moved
neither `h` nor `L` nor `T_h`. These two are the pieces Lemma 8 needs beside it: the same
no-fire case moves `s_h` no more, and the case that *emptied* a filled `T_h` is an advance,
whose `s_h` is the start it was handed and whose height is up by one. -/

/-- If the height-event check left a target named, `s_h` did not move: only `advance_height`
    writes it, and the advance always clears `T_h`. -/
theorem processHeightEvents_s_h_of_target (σ : ChainState Node Root) (st : Time)
    (hT : (processHeightEvents σ st).T_h ≠ ⊥) :
    (processHeightEvents σ st).s_h = σ.s_h := by
  simp only [processHeightEvents, Id.run] at hT ⊢
  split_ifs at hT ⊢ <;>
    first
      | exact absurd (advanceHeight_T_h _ _ _) hT
      | rfl

/-- If the height-event check emptied a filled target, a branch advanced: the height is up by
    one, `s_h` is the start slot the check was handed, and the latest block is untouched. -/
theorem processHeightEvents_of_bot (σ : ChainState Node Root) (st : Time)
    (hpre : σ.T_h ≠ ⊥) (hT : (processHeightEvents σ st).T_h = ⊥) :
    (processHeightEvents σ st).h = σ.h + 1 ∧ (processHeightEvents σ st).s_h = st ∧
      (processHeightEvents σ st).L = σ.L := by
  simp only [processHeightEvents, Id.run] at hT ⊢
  split_ifs at hT ⊢ <;>
    first
      | exact absurd hT hpre
      | exact ⟨advanceHeight_h _ _ _, advanceHeight_s_h _ _ _, advanceHeight_L _ _ _⟩

/-! ## Figure 1's slot check, extracted -/

/-- On the successful path the block's slot is beyond the cursor: `state_transition`'s own
    first check (Figure 1, line 719). With `postState_s` below this is what makes slots
    strictly increase along a chain. -/
theorem stateTransition_slot_lt {σ σ' : ChainState Node Root} {B : Blk Node Root}
    (h : stateTransition σ B = .state σ') : σ.s < B.slot := by
  simp only [stateTransition, Id.run] at h
  split_ifs at h with hc
  simp only [not_or, not_le] at hc
  exact hc.2

/-- A block post-state's cursor sits at its own block's slot. -/
theorem postState_s : ∀ (B : Blk Node Root) {σ : ChainState Node Root},
    postState B = .state σ → σ.s = B.slot
  | .genesis, σ, h => by
      simp only [postState, TransitionResult.state.injEq] at h
      rw [← h]; rfl
  | .mk p s n as r, σ, h => by
      rw [postState] at h
      rcases hp : postState p with ⟨σp⟩ | _
      · rw [hp] at h
        have hslot := stateTransition_slot_lt h
        obtain ⟨σ₂, hb, rfl⟩ := stateTransition_state h
        have hs2 : σ₂.s = (processSlots σp (Blk.mk p s n as r).slot).s := by
          rw [processBlock_state hb]; exact processAttestations_s _ _
        rw [processHeightEvents_s, hs2, processSlots_s]
        omega
      · rw [hp] at h; simp at h

/-- An ancestor of a block that replays itself replays. This is the lemma
    `lemChainTargetFirstBlock`'s docstring names as unwritten; now it is. -/
theorem postState_ancestor : ∀ (B : Blk Node Root) {C : Blk Node Root}
    {σ : ChainState Node Root}, C ⪯ B → postState B = .state σ →
    ∃ σC, postState C = .state σC
  | .genesis, C, σ, hle, h => by
      simp only [Preceq, ancestors, List.mem_singleton] at hle
      subst hle; exact ⟨σ, h⟩
  | .mk p s n as r, C, σ, hle, h => by
      simp only [Preceq, ancestors, List.mem_cons] at hle
      rcases hle with rfl | hle
      · exact ⟨σ, h⟩
      · rw [postState] at h
        rcases hp : postState p with ⟨σp⟩ | _
        · exact postState_ancestor p hle hp
        · rw [hp] at h; simp at h

/-- Slots never decrease along a replayable chain. -/
theorem preceq_slot_le : ∀ (B : Blk Node Root) {C : Blk Node Root} {σ : ChainState Node Root},
    C ⪯ B → postState B = .state σ → C.slot ≤ B.slot
  | .genesis, C, _, hle, _ => by
      simp only [Preceq, ancestors, List.mem_singleton] at hle
      subst hle; exact Nat.le_refl _
  | .mk p s n as r, C, σ, hle, h => by
      simp only [Preceq, ancestors, List.mem_cons] at hle
      rcases hle with rfl | hle
      · exact Nat.le_refl _
      · rw [postState] at h
        rcases hp : postState p with ⟨σp⟩ | _
        · rw [hp] at h
          have h1 : C.slot ≤ p.slot := preceq_slot_le p hle hp
          have h2 : σp.s = p.slot := postState_s p hp
          have h3 := stateTransition_slot_lt h
          simp only [Blk.slot] at *
          omega
        · rw [hp] at h; simp at h

/-- **Slots are strict along a chain**: a strict ancestor of a replayable block sits at a
    strictly earlier slot. Contrapositively, one chain has at most one block per slot, which is
    what lets `s_h` pin a block. -/
theorem prec_slot_lt {C B : Blk Node Root} {σ : ChainState Node Root}
    (hlt : C ≺ B) (h : postState B = .state σ) : C.slot < B.slot := by
  obtain ⟨h1, h2⟩ := hlt
  cases B with
  | genesis =>
      simp only [Preceq, ancestors, List.mem_singleton] at h1
      exact absurd h1 h2
  | mk p s n as r =>
      simp only [Preceq, ancestors, List.mem_cons] at h1
      rcases h1 with rfl | h1
      · exact absurd rfl h2
      · rw [postState] at h
        rcases hp : postState p with ⟨σp⟩ | _
        · rw [hp] at h
          have hle : C.slot ≤ p.slot := preceq_slot_le p h1 hp
          have heq : σp.s = p.slot := postState_s p hp
          have hlt' := stateTransition_slot_lt h
          simp only [Blk.slot] at *
          omega
        · rw [hp] at h; simp at h

/-! ## The height never decreases, with no threshold hypothesis

Lemma 6 says a transition that moves the height moves it up by one, but it carries
`PositiveWeight` and names the branch that fired. These say only that nothing goes down, which
needs no assumption: `advance_height` is the one writer of `h`, and it increments. -/

theorem processHeightEvents_h_le (σ : ChainState Node Root) (st : Time) :
    σ.h ≤ (processHeightEvents σ st).h := by
  simp only [processHeightEvents, advanceHeight, Id.run]
  repeat' split
  all_goals first | exact Nat.le_refl _ | exact Nat.le_succ _

theorem processSlot_h_le (σ : ChainState Node Root) : σ.h ≤ (processSlot σ).h := by
  simp only [processSlot, Id.run]
  split_ifs <;>
    first
      | exact Nat.le_refl _
      | exact processHeightEvents_h_le _ _
      | exact processHeightEvents_h_le { σ with T_h := some σ.L } σ.s

theorem closeSlots_h_le : ∀ (n : Nat) (σ : ChainState Node Root), σ.h ≤ (closeSlots n σ).h
  | 0, _ => by rw [closeSlots]
  | n + 1, σ => by
      rw [closeSlots]
      exact Nat.le_trans (processSlot_h_le σ) (closeSlots_h_le n _)

theorem processSlots_h_le (σ : ChainState Node Root) (t : Time) :
    σ.h ≤ (processSlots σ t).h := by
  rw [processSlots_eq_closeSlots]; exact closeSlots_h_le _ _

/-- The block phase does not touch the height: it writes `L` and then the participation
    fields. -/
theorem processBlock_h {σ σ' : ChainState Node Root} {B : Blk Node Root}
    (h : processBlock σ B = .state σ') : σ'.h = σ.h := by
  rw [processBlock_state h]
  exact (processAttestations_chainFields B.attestations _).2.2

theorem stateTransition_h_le {σp σ' : ChainState Node Root} {B : Blk Node Root}
    (ht : stateTransition σp B = .state σ') : σp.h ≤ σ'.h := by
  obtain ⟨σ₂, hb, rfl⟩ := stateTransition_state ht
  refine Nat.le_trans ?_ (processHeightEvents_h_le σ₂ B.slot)
  rw [processBlock_h hb]
  exact processSlots_h_le σp B.slot

/-- **Height is monotone along a chain.** Read aloud: an ancestor's post-state is at no
    greater height than a descendant's. Structural recursion on the descendant. -/
theorem postState_h_le : ∀ (B' : Blk Node Root) {B : Blk Node Root}
    {σ σ' : ChainState Node Root}, B ⪯ B' → postState B = .state σ →
    postState B' = .state σ' → σ.h ≤ σ'.h
  | .genesis, B, σ, σ', hle, hx, hy => by
      simp only [Preceq, ancestors, List.mem_singleton] at hle
      subst hle
      rw [hx] at hy; injection hy with hy; rw [hy]
  | .mk p s n as r, B, σ, σ', hle, hx, hy => by
      simp only [Preceq, ancestors, List.mem_cons] at hle
      rcases hle with rfl | hle
      · rw [hx] at hy; injection hy with hy; rw [hy]
      · rw [postState] at hy
        rcases hp : postState p with ⟨σp⟩ | _
        · rw [hp] at hy
          exact Nat.le_trans (postState_h_le p hle hx hp) (stateTransition_h_le hy)
        · rw [hp] at hy; simp at hy

/-! ## The fifth invariant -/

/-- The named target sits at the height's start slot — the paper's "first block of the height"
    said about one field — and while no target is named, the *latest block* does. The second
    conjunct is what makes Figure 1's recording condition `L.slot ≥ s_h` an equality when it
    fires, and what shows it always fires at the first closed slot after a transition. -/
structure Aligned (σ : ChainState Node Root) : Prop where
  /-- A named target sits at the start slot. -/
  named : ∀ T, σ.T_h = some T → T.slot = σ.s_h
  /-- Until one is named, the latest block does: it is the transition block itself. -/
  empty : σ.T_h = ⊥ → σ.L.slot = σ.s_h

theorem aligned_gen : Aligned (ChainState.gen (Node := Node) (Root := Root)) where
  named T hT := by
    simp only [ChainState.gen, Option.some.injEq] at hT
    subst hT; rfl
  empty h := by simp [ChainState.gen] at h

/-- One closed slot keeps the invariant, and afterwards a target is always named: if none was,
    `empty` says the write condition held, so the write fired. -/
theorem processSlot_aligned {σ : ChainState Node Root} (hs : Settled σ) (hq : 0 < q Node)
    (ha : Aligned σ) : Aligned (processSlot σ) ∧ (processSlot σ).T_h ≠ ⊥ := by
  by_cases h1 : σ.T_h = ⊥ ∧ σ.L.slot ≥ σ.s_h
  · have hset := settled_setTarget hs hq h1.1
    have heq : processSlot σ = { σ with s := σ.s + 1, T_h := some σ.L } := by
      simp only [processSlot]
      by_cases h2 : σ.L.slot < σ.s <;> simp [h1, h2, processHeightEvents_of_settled hset]
    rw [heq]
    refine ⟨⟨fun T hT => ?_, fun hbot => absurd hbot (by simp)⟩, by simp⟩
    have hLT : σ.L = T := by injection hT
    rw [← hLT]
    exact ha.empty h1.1
  · have hTne : σ.T_h ≠ ⊥ := fun hbot => h1 ⟨hbot, (ha.empty hbot).ge⟩
    have heq : processSlot σ = { σ with s := σ.s + 1 } := by
      simp only [processSlot]
      by_cases h2 : σ.L.slot < σ.s <;> simp [h1, h2, processHeightEvents_of_settled hs]
    rw [heq]
    exact ⟨⟨fun T hT => ha.named T hT, fun hbot => ha.empty hbot⟩, hTne⟩

/-- Any number of closed slots; at least one, and a target is named. -/
theorem closeSlots_aligned : ∀ (n : Nat) {σ : ChainState Node Root}, Settled σ →
    0 < q Node → Aligned σ →
    Aligned (closeSlots n σ) ∧ (0 < n → (closeSlots n σ).T_h ≠ ⊥)
  | 0, σ, _, _, ha => by
      rw [closeSlots]
      exact ⟨ha, fun h => absurd h (Nat.lt_irrefl 0)⟩
  | n + 1, σ, hs, hq, ha => by
      rw [closeSlots]
      obtain ⟨-, -, -, hs'⟩ := processSlot_of_settled hs hq
      obtain ⟨ha', hne'⟩ := processSlot_aligned hs hq ha
      obtain ⟨hA, hN⟩ := closeSlots_aligned n hs' hq ha'
      refine ⟨hA, fun _ => ?_⟩
      cases n with
      | zero => rw [closeSlots]; exact hne'
      | succ m => exact hN (Nat.succ_pos m)

/-- A whole transition keeps the invariant. The closure keeps it and names a target; the block
    phase touches neither `T_h` nor `s_h`; and the final height-event check either fires no
    branch — every field the invariant reads unchanged — or advances, and then `empty` is the
    new height's own anchor: `s_h` becomes the block's slot and the block is the latest. -/
theorem aligned_stateTransition {σp σ' : ChainState Node Root} {B : Blk Node Root}
    (hs : Settled σp) (hq : 0 < q Node) (ha : Aligned σp)
    (ht : stateTransition σp B = .state σ') : Aligned σ' := by
  have hslot : σp.s < B.slot := stateTransition_slot_lt ht
  obtain ⟨σ₂, hb, rfl⟩ := stateTransition_state ht
  rw [processSlots_eq_closeSlots] at hb
  obtain ⟨haC, hneC⟩ := closeSlots_aligned (B.slot - σp.s) hs hq ha
  have hne : (closeSlots (B.slot - σp.s) σp).T_h ≠ ⊥ := hneC (by omega)
  have h2eq := processBlock_state hb
  have h2Th : σ₂.T_h = (closeSlots (B.slot - σp.s) σp).T_h := by
    rw [h2eq]; exact processAttestations_T_h _ _
  have h2sh : σ₂.s_h = (closeSlots (B.slot - σp.s) σp).s_h := by
    rw [h2eq]; exact processAttestations_s_h _ _
  have h2L : σ₂.L = B := by
    rw [h2eq]; exact (processAttestations_chainFields _ _).1
  cases hpost : (processHeightEvents σ₂ B.slot).T_h with
  | none =>
      obtain ⟨-, hsh, hL⟩ :=
        processHeightEvents_of_bot σ₂ B.slot (by rw [h2Th]; exact hne) hpost
      refine ⟨fun T hTx => ?_, fun _ => ?_⟩
      · rw [hpost] at hTx; exact absurd hTx (by simp)
      · rw [hL, h2L, hsh]
  | some T0 =>
      have hne' : (processHeightEvents σ₂ B.slot).T_h ≠ ⊥ := by rw [hpost]; simp
      obtain ⟨-, -, hTh⟩ := processHeightEvents_of_target σ₂ B.slot hne'
      have hsh := processHeightEvents_s_h_of_target σ₂ B.slot hne'
      refine ⟨fun T hTx => ?_, fun hbot => ?_⟩
      · rw [hTh, h2Th] at hTx
        rw [hsh, h2sh]
        exact haC.named T hTx
      · rw [hpost] at hbot; exact absurd hbot (by simp)

/-- Every block post-state is `Aligned`. `PositiveWeight` is here because `Settled` is, and
    `Settled` is here for the closure alone. -/
theorem aligned_of_blockPostState [PositiveWeight Node] {σ : ChainState Node Root}
    (h : BlockPostState σ) : Aligned σ := by
  induction h with
  | gen => exact aligned_gen
  | step hp hst ih => exact aligned_stateTransition (settled_of_blockPostState hp) q_pos ih hst

/-! ## `s_h` is pinned by the height, along one chain -/

/-- A transition that leaves the height alone leaves `s_h` alone: `advance_height` is the one
    writer of `s_h`, and it always increments `h`. -/
theorem stateTransition_s_h_eq {σp σ' : ChainState Node Root} {B : Blk Node Root}
    (hs : Settled σp) (hq : 0 < q Node) (ha : Aligned σp)
    (ht : stateTransition σp B = .state σ') (hh : σ'.h = σp.h) : σ'.s_h = σp.s_h := by
  have hslot : σp.s < B.slot := stateTransition_slot_lt ht
  obtain ⟨σ₂, hb, rfl⟩ := stateTransition_state ht
  rw [processSlots_eq_closeSlots] at hb
  obtain ⟨haC, hneC⟩ := closeSlots_aligned (B.slot - σp.s) hs hq ha
  have hne : (closeSlots (B.slot - σp.s) σp).T_h ≠ ⊥ := hneC (by omega)
  obtain ⟨Th, -, hCeq, -⟩ := closeSlots_of_settled (B.slot - σp.s) hs hq
  have hCsh : (closeSlots (B.slot - σp.s) σp).s_h = σp.s_h := by rw [hCeq]
  have hCh : (closeSlots (B.slot - σp.s) σp).h = σp.h := by rw [hCeq]
  have h2eq := processBlock_state hb
  have h2Th : σ₂.T_h = (closeSlots (B.slot - σp.s) σp).T_h := by
    rw [h2eq]; exact processAttestations_T_h _ _
  have h2sh : σ₂.s_h = σp.s_h := by
    rw [h2eq]; exact (processAttestations_s_h _ _).trans hCsh
  have h2h : σ₂.h = σp.h := by
    rw [h2eq]; exact ((processAttestations_chainFields _ _).2.2).trans hCh
  cases hpost : (processHeightEvents σ₂ B.slot).T_h with
  | some T0 =>
      have hne' : (processHeightEvents σ₂ B.slot).T_h ≠ ⊥ := by rw [hpost]; simp
      have hsh := processHeightEvents_s_h_of_target σ₂ B.slot hne'
      rw [hsh]; exact h2sh
  | none =>
      obtain ⟨hplus, -, -⟩ :=
        processHeightEvents_of_bot σ₂ B.slot (by rw [h2Th]; exact hne) hpost
      omega

/-- **`s_h` agrees along one chain at one height.** Read aloud: two block post-states on one
    chain at the same height have the same start slot. Height monotonicity puts every state in
    between at that height too, so no transition fired and `s_h` never moved. -/
theorem postState_s_h_eq [PositiveWeight Node] :
    ∀ (B' : Blk Node Root) {B : Blk Node Root} {σ σ' : ChainState Node Root},
      B ⪯ B' → postState B = .state σ → postState B' = .state σ' →
      σ.h = σ'.h → σ.s_h = σ'.s_h
  | .genesis, B, σ, σ', hle, hx, hy, _ => by
      simp only [Preceq, ancestors, List.mem_singleton] at hle
      subst hle
      rw [hx] at hy; injection hy with hy; rw [hy]
  | .mk p s n as r, B, σ, σ', hle, hx, hy, hh => by
      simp only [Preceq, ancestors, List.mem_cons] at hle
      rcases hle with rfl | hle
      · rw [hx] at hy; injection hy with hy; rw [hy]
      · rw [postState] at hy
        rcases hp : postState p with ⟨σp⟩ | _
        · rw [hp] at hy
          have hbp := blockPostState_of_postState p hp
          have h1 : σ.h ≤ σp.h := postState_h_le p hle hx hp
          have h2 : σp.h ≤ σ'.h := stateTransition_h_le hy
          have hsp : σ'.s_h = σp.s_h :=
            stateTransition_s_h_eq (settled_of_blockPostState hbp) q_pos
              (aligned_of_blockPostState hbp) hy (by omega)
          have ih : σ.s_h = σp.s_h := postState_s_h_eq p hle hx hp (by omega)
          rw [ih, hsp]
        · rw [hp] at hy; simp at hy

/-! ## Lemma 8, first sentence, first clause -/

/-- **A chain has at most one current-height target per height.** The named targets both sit
    at the height's start slot (`Aligned`), the start slots agree (`postState_s_h_eq`), both
    blocks are ancestors of `B'` (`Fresh.onChain`), ancestors of one block are comparable
    (`preceq_or_preceq`), and slots are strict along a chain (`prec_slot_lt`) — so distinct
    comparable blocks at one slot cannot be. -/
theorem chainTargetUniqueness [PositiveWeight Node] {B B' T T' : Blk Node Root}
    {σ σ' : ChainState Node Root} (hchain : B ⪯ B')
    (hB : postState B = .state σ) (hB' : postState B' = .state σ')
    (hheight : σ.h = σ'.h) (hT : σ.T_h = some T) (hT' : σ'.T_h = some T') : T = T' := by
  have hbp : BlockPostState σ := blockPostState_of_postState B hB
  have hbp' : BlockPostState σ' := blockPostState_of_postState B' hB'
  have hTs : T.slot = σ.s_h := (aligned_of_blockPostState hbp).named T hT
  have hTs' : T'.slot = σ'.s_h := (aligned_of_blockPostState hbp').named T' hT'
  have hsh : σ.s_h = σ'.s_h := postState_s_h_eq B' hchain hB hB' hheight
  have hTB : T ⪯ B := by
    have h := (fresh_of_blockPostState hbp).onChain T hT
    rwa [postState_L B hB] at h
  have hT'B' : T' ⪯ B' := by
    have h := (fresh_of_blockPostState hbp').onChain T' hT'
    rwa [postState_L B' hB'] at h
  have hTB' : T ⪯ B' := Preceq.trans hTB hchain
  by_contra hne
  rcases preceq_or_preceq B' hTB' hT'B' with hcmp | hcmp
  · obtain ⟨σT', hσT'⟩ := postState_ancestor B' hT'B' hB'
    have := prec_slot_lt ⟨hcmp, hne⟩ hσT'
    omega
  · obtain ⟨σT, hσT⟩ := postState_ancestor B' hTB' hB'
    have := prec_slot_lt ⟨hcmp, fun he => hne he.symm⟩ hσT
    omega

end Proofs

end Decoupled
