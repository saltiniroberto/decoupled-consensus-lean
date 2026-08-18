import Analysis.Vocabulary
import Analysis.Proofs.Ancestry

/-!
# Every set bit has an attestation behind it

The invariant Lemma 6 (`lem:height-progression`) needs for its second half. A height transition
fires on a quorum's worth of bits in one of the two participation arrays, and the certificate the
lemma has to produce is a claim about *attestations*. So something has to carry the bits back to the
attestations that set them, and that is `Witnessed`:

    target   : a set target bit means an included attestation for exactly the current height and
               the named target
    progress : a set progress bit means an included attestation at the current height

Both are stated against `σ.L`, the state's own latest block, so no endpoint parameter is needed;
`Witnessed.of_fields` moves the endpoint up the chain where a step needs it.

## Why the paper never states this

Definition 21's certificates are *about* included attestations, and the paper's proof of Lemma 6 is
two sentences that take for granted that a fired branch had the votes. In the state machine the
votes are gone by then — only bits remain — so the Lean proof needs the bits' provenance as an
invariant. Compare `Settled` (`Analysis/Proofs/SlotClosure.lean`) and `Chained`
(`Analysis/Proofs/Ancestry.lean`): this is the third invariant here whose statement the paper does
not write down.

## `Settled` is needed for one step only

`process_slot` can name a target while bits are already set, which would leave the old bits
witnessing the wrong target. It cannot really happen: naming a target requires `T_h = ⊥`, and
`Settled`'s fourth conjunct says the target tally is then empty. That is the only place `Settled`
enters this file, and it is why `witnessed_of_blockPostState` needs `PositiveWeight`.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]

/-- Inclusion survives moving the endpoint down the chain. -/
theorem IncludedOn.mono {a : Attestation Node Root} {B B' : Blk Node Root}
    (h : IncludedOn a B) (hB : B ⪯ B') : IncludedOn a B' := by
  obtain ⟨Y, hY, ha⟩ := h
  exact ⟨Y, Preceq.trans hY hB, ha⟩

namespace Proofs

/-! ## Figure 2's writers of the two bit arrays -/

/-- Line 779 is the only writer of a target bit, and this is what it wrote: either the bit was
    already set, or `a` is the attestation that set it, and its height pair is exactly the current
    height and the named target. -/
theorem processAttestation_target_bit (σ : ChainState Node Root) (a : Attestation Node Root)
    (A : Blk Node Root) (i : Node)
    (hb : (processAttestation σ a A).targetParticipation i = true) :
    σ.targetParticipation i = true ∨
      (a.validator = i ∧ ∃ T, σ.T_h = some T ∧ a.heightPair = .target σ.h T) := by
  simp only [processAttestation] at hb
  repeat' split at hb
  all_goals (simp_all [Function.update_apply]; try tauto)

/-- Figure 2 (`alg:attestation-processing`)'s lines 783 and 784 are the only writers of
    a progress bit: either the bit was already set, or
    `a` is the attestation that set it — a timeout at the current height (line 783), or an exact
    target at the current height whose target is on the including block's parent chain (line 784,
    where `A` is that parent). The `T ⪯ A` half is the piece Lemma 10's progress case needs: a
    counted vote with a *nonempty* target vouches for its target being on the chain. -/
theorem processAttestation_progress_bit (σ : ChainState Node Root) (a : Attestation Node Root)
    (A : Blk Node Root) (i : Node) (hb : (processAttestation σ a A).progress i = true) :
    σ.progress i = true ∨ (a.validator = i ∧
      (a.heightPair = .timeout σ.h ∨ ∃ T, a.heightPair = .target σ.h T ∧ T ⪯ A)) := by
  simp only [processAttestation] at hb
  repeat' split at hb
  all_goals (simp_all [Function.update_apply]; try tauto)

/-! ## The invariant -/

/-- Every set bit has an attestation on this chain behind it. See the module docstring. -/
structure Witnessed (σ : ChainState Node Root) : Prop where
  /-- A set target bit is backed by an included attestation for the named target at the current
      height. -/
  target : ∀ i ∈ σ.Qtarget, ∃ T a, σ.T_h = some T ∧ a.validator = i ∧
    a.heightPair = .target σ.h T ∧ IncludedOn a σ.L
  /-- A set progress bit is backed by an included attestation at the current height — a timeout,
      or an exact target whose target is itself on this chain. The ancestry half is
      Figure 2 (`alg:attestation-processing`)'s line 784 condition remembered; `progress_height` below recovers the weaker
      `a.height = some σ.h` reading. -/
  progress : ∀ i ∈ σ.Qprog, ∃ a : Attestation Node Root, a.validator = i ∧ IncludedOn a σ.L ∧
    (a.heightPair = .timeout σ.h ∨ ∃ T, a.heightPair = .target σ.h T ∧ T ⪯ σ.L)

/-- The congruence lemma: a state agreeing on the four fields the invariant reads is witnessed, and
    the endpoint may move down the chain. Every step that touches only `s`, `F`, `h_F`, `P` or `J`
    is one line with this. -/
theorem Witnessed.of_fields {σ τ : ChainState Node Root} (h : Witnessed σ)
    (hT : τ.T_h = σ.T_h) (hh : τ.h = σ.h) (hL : σ.L ⪯ τ.L)
    (htp : τ.targetParticipation = σ.targetParticipation) (hpp : τ.progress = σ.progress) :
    Witnessed τ where
  target i hi := by
    rw [ChainState.Qtarget, htp] at hi
    obtain ⟨T, a, h1, h2, h3, h4⟩ := h.target i (by rw [ChainState.Qtarget]; exact hi)
    exact ⟨T, a, by rw [hT]; exact h1, h2, by rw [hh]; exact h3, h4.mono hL⟩
  progress i hi := by
    rw [ChainState.Qprog, hpp] at hi
    obtain ⟨a, h1, h2, h3⟩ := h.progress i (by rw [ChainState.Qprog]; exact hi)
    refine ⟨a, h1, h2.mono hL, ?_⟩
    rcases h3 with h3 | ⟨T, h3, h4⟩
    · exact Or.inl (by rw [hh]; exact h3)
    · exact Or.inr ⟨T, by rw [hh]; exact h3, Preceq.trans h4 hL⟩

/-- Vacuously witnessed: no bits, nothing to witness. This is how every step that clears the two
    arrays is discharged. -/
theorem witnessed_of_empty {σ : ChainState Node Root} (ht : σ.Qtarget = ∅) (hp : σ.Qprog = ∅) :
    Witnessed σ where
  target i hi := absurd (ht ▸ hi) (by simp)
  progress i hi := absurd (hp ▸ hi) (by simp)

theorem witnessed_gen : Witnessed (ChainState.gen (Node := Node) (Root := Root)) where
  target i hi := by simp [ChainState.Qtarget, ChainState.gen] at hi
  progress i hi := by simp [ChainState.Qprog, ChainState.gen] at hi

/-- The old reading of the progress field: the vote sits at the current height, whichever arm it
    came from — `Attestation.height` reads a timeout and an exact target alike. -/
theorem Witnessed.progress_height {σ : ChainState Node Root} (h : Witnessed σ) :
    ∀ i ∈ σ.Qprog, ∃ a : Attestation Node Root,
      a.validator = i ∧ a.height = some σ.h ∧ IncludedOn a σ.L := by
  intro i hi
  obtain ⟨a, h1, h2, h3⟩ := h.progress i hi
  rcases h3 with h3 | ⟨T, h3, -⟩ <;> exact ⟨a, h1, by simp [Attestation.height, h3], h2⟩

/-! ## The attestation loop, where bits are set -/

/-- One attestation keeps the invariant. A bit that was already set keeps its old witness — the
    routine moves neither `T_h`, nor `h`, nor `L` — and a newly set bit is witnessed by `a` itself,
    whose height pair the writer's own condition pins. `hA` is what turns the progress writer's
    `T ⪯ A` into the invariant's `T ⪯ σ.L`: the parent the votes are judged against is on this
    chain. -/
theorem Witnessed.processAttestation {σ : ChainState Node Root} (h : Witnessed σ)
    (a : Attestation Node Root) (A : Blk Node Root) (hinc : IncludedOn a σ.L)
    (hA : A ⪯ σ.L) :
    Witnessed (_root_.Decoupled.processAttestation σ a A) where
  target i hi := by
    obtain ⟨hL, -, -, hh, -, -⟩ := processAttestation_chainFields σ a A
    have hT := processAttestation_T_h σ a A
    rw [ChainState.Qtarget, Finset.mem_filter] at hi
    rcases processAttestation_target_bit σ a A i hi.2 with hold | ⟨hv, T, hTh, hpair⟩
    · obtain ⟨T, b, h1, h2, h3, h4⟩ :=
        h.target i (by rw [ChainState.Qtarget, Finset.mem_filter]; exact ⟨hi.1, hold⟩)
      exact ⟨T, b, by rw [hT]; exact h1, h2, by rw [hh]; exact h3, by rw [hL]; exact h4⟩
    · exact ⟨T, a, by rw [hT]; exact hTh, hv, by rw [hh]; exact hpair, by rw [hL]; exact hinc⟩
  progress i hi := by
    obtain ⟨hL, -, -, hh, -, -⟩ := processAttestation_chainFields σ a A
    rw [ChainState.Qprog, Finset.mem_filter] at hi
    rcases processAttestation_progress_bit σ a A i hi.2 with hold | ⟨hv, harm⟩
    · obtain ⟨b, h1, h2, h3⟩ :=
        h.progress i (by rw [ChainState.Qprog, Finset.mem_filter]; exact ⟨hi.1, hold⟩)
      refine ⟨b, h1, by rw [hL]; exact h2, ?_⟩
      rcases h3 with h3 | ⟨T, h3, h4⟩
      · exact Or.inl (by rw [hh]; exact h3)
      · exact Or.inr ⟨T, by rw [hh]; exact h3, by rw [hL]; exact h4⟩
    · refine ⟨a, hv, by rw [hL]; exact hinc, ?_⟩
      rcases harm with harm | ⟨T, harm, hTA⟩
      · exact Or.inl (by rw [hh]; exact harm)
      · exact Or.inr ⟨T, by rw [hh]; exact harm, by rw [hL]; exact Preceq.trans hTA hA⟩

/-- The fold, by list induction. `hinc` is what says the attestations being processed are on this
    chain; at the call site they are the block's own, and the block is the state's `L` by then. -/
theorem Witnessed.processAttestations :
    ∀ (as : List (Attestation Node Root)) {σ : ChainState Node Root} (A : Blk Node Root),
      Witnessed σ → (∀ a ∈ as, IncludedOn a σ.L) → A ⪯ σ.L →
        Witnessed (_root_.Decoupled.processAttestations σ as A)
  | [], _, _, h, _, _ => h
  | a :: as, σ, A, h, hinc, hA => by
      rw [processAttestations_cons]
      obtain ⟨hL, -⟩ := processAttestation_chainFields σ a A
      refine Witnessed.processAttestations as A
        (h.processAttestation a A (hinc a (by simp)) hA) (fun b hb => ?_) (by rw [hL]; exact hA)
      rw [hL]
      exact hinc b (by simp [hb])

/-! ## The rest of the transition -/

/-- Naming a target keeps the invariant, and this is the one step that needs `Settled`: it only ever
    happens while no target is named, and then the fourth conjunct says there are no target bits to
    witness. -/
theorem Witnessed.setTarget {σ : ChainState Node Root} (h : Witnessed σ)
    (hET : σ.T_h = ⊥ → σ.Qtarget = ∅) (hTh : σ.T_h = ⊥) :
    Witnessed { σ with T_h := some σ.L } where
  target i hi := absurd ((hET hTh) ▸ hi) (by simp)
  progress i hi := h.progress i hi

/-- The height-event check keeps the invariant unconditionally: either it changes none of the fields
    the invariant reads, or it advances the height and clears both arrays. -/
theorem Witnessed.processHeightEvents {σ : ChainState Node Root} (h : Witnessed σ) (st : Time) :
    Witnessed (_root_.Decoupled.processHeightEvents σ st) := by
  simp only [_root_.Decoupled.processHeightEvents, Id.run]
  split_ifs <;>
    first
      | exact witnessed_of_empty (advanceHeight_Qtarget _ _ _) (advanceHeight_Qprog _ _ _)
      | exact h.of_fields rfl rfl (Preceq.refl _) rfl rfl

theorem Witnessed.processSlot {σ : ChainState Node Root} (h : Witnessed σ) (hs : Settled σ) :
    Witnessed (_root_.Decoupled.processSlot σ) := by
  simp only [_root_.Decoupled.processSlot, Id.run]
  split_ifs <;>
    first
      | exact ((h.setTarget hs.emptyTarget (by tauto)).processHeightEvents _).of_fields
          rfl rfl (Preceq.refl _) rfl rfl
      | exact (h.setTarget hs.emptyTarget (by tauto)).of_fields rfl rfl (Preceq.refl _) rfl rfl
      | exact (h.processHeightEvents _).of_fields rfl rfl (Preceq.refl _) rfl rfl
      | exact h.of_fields rfl rfl (Preceq.refl _) rfl rfl

/-- Closing slots keeps it, carrying `Settled` alongside because `process_slot` needs it. -/
theorem Witnessed.closeSlots (hq : 0 < q Node) :
    ∀ (n : Nat) {σ : ChainState Node Root}, Witnessed σ → Settled σ →
      Witnessed (_root_.Decoupled.Proofs.closeSlots n σ)
  | 0, _, h, _ => by rw [_root_.Decoupled.Proofs.closeSlots]; exact h
  | n + 1, σ, h, hs => by
      obtain ⟨-, -, -, hs'⟩ := processSlot_of_settled hs hq
      rw [_root_.Decoupled.Proofs.closeSlots]
      exact Witnessed.closeSlots hq n (h.processSlot hs) hs'

theorem Witnessed.processSlots {σ : ChainState Node Root} (h : Witnessed σ) (hs : Settled σ)
    (hq : 0 < q Node) (t : Time) : Witnessed (_root_.Decoupled.processSlots σ t) := by
  rw [processSlots_eq_closeSlots]
  exact Witnessed.closeSlots hq _ h hs

/-- The block phase keeps the invariant. Two things happen: `L` moves to `B`, which the parent check
    makes an ancestry step so every old witness is still included; and the block's own attestations
    are processed, each of which is included on `B` by sitting in `B` itself. -/
theorem Witnessed.processBlock {σ σ' : ChainState Node Root} {B : Blk Node Root}
    (h : Witnessed σ) (he : _root_.Decoupled.processBlock σ B = .state σ') : Witnessed σ' := by
  have hpar : B.parent = some σ.L := by
    simp only [_root_.Decoupled.processBlock, Id.run] at he
    split_ifs at he with hc
    simp only [not_or, ne_eq, not_not] at hc
    exact hc.1
  have hext : Witnessed { σ with L := B } := h.of_fields rfl rfl (parent_preceq hpar) rfl rfl
  rw [processBlock_state he]
  exact Witnessed.processAttestations _ _ hext (fun a ha => ⟨B, Preceq.refl B, ha⟩)
    (parent_preceq hpar)

theorem Witnessed.stateTransition {σ σ' : ChainState Node Root} {B : Blk Node Root}
    (h : Witnessed σ) (hs : Settled σ) (hq : 0 < q Node)
    (he : _root_.Decoupled.stateTransition σ B = .state σ') : Witnessed σ' := by
  obtain ⟨σ₂, hb, rfl⟩ := stateTransition_state he
  exact ((h.processSlots hs hq B.slot).processBlock hb).processHeightEvents _

/-- Every block post-state is `Witnessed`. `PositiveWeight` is here because `Settled` is, and
    `Settled` is here for `process_slot` alone. -/
theorem witnessed_of_blockPostState [PositiveWeight Node] {σ : ChainState Node Root}
    (h : BlockPostState σ) : Witnessed σ := by
  induction h with
  | gen => exact witnessed_gen
  | step hp hst ih => exact ih.stateTransition (settled_of_blockPostState hp) q_pos hst

end Proofs

end Decoupled
