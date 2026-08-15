import Analysis.Proofs.Freshness

/-!
# The recorded pairs have quorums behind them

Lemma 11 and Theorem 5 take finalization as a *recorded pair*: the chain's post-state has
`(F, h_F) = (C, h)`. Their proofs intersect quorums, so something must carry the recorded pair
back to the quorums that produced it — the machine wrote `(F, h_F)` only after counting a commit
quorum, and `(J, h_j)` only after counting a target quorum. That is `Certified`, the sixth
invariant, `Witnessed`'s idea applied to the finality fields:

    PsubV   : the finality tally is inside the electorate
    commits : every bit in `P` has an included commit to the current `(h_j, J)` behind it
    just    : a justified pair at `h_j ≥ 1` has an included target quorum behind it,
              and the justified block's own post-state sits at `h_j`
    fin     : a finalized pair at `h_F ≥ 1` has an included commit quorum *and* an included
              target quorum behind it, and the finalized block's post-state sits at `h_F`
    fin0    : a finalized height of `0` is genesis, finalized by stipulation

`fin` carries both quorums because the finality write copies `(J, h_j)`: at that moment `P` is
the commit quorum and `just` is the target quorum, and both are frozen into `fin` by the copy.
The anchors — `(postState σ.J).map ChainState.h = some σ.h_j` — come from `Fresh`: the justified
block was the current-height target when it was justified.

## Where each field moves, and what re-establishes it

* Slot closure moves `s` and `T_h` only (Lemma 3), which no field reads.
* The block phase moves `L` one step down the chain — inclusions follow by `IncludedOn.mono` —
  and grows `P`; the writer's own condition (Figure 2, lines 774–776) pins each new bit to an
  included commit to the current `(h_j, J)`, and `process_block`'s `ValidInclusion` check keeps
  the tally inside `V`.
* The height-event check either fires nothing, or copies `(J, h_j)` into `(F, h_F)` — `fin`
  rebuilt from `commits` and `just` — or advances with a justification — `just` rebuilt from the
  target quorum that fired, whose votes `Witnessed` carries and whose anchor `Fresh` carries —
  or advances by progress, which moves none of the five subjects. A justification advance clears
  `P`, so `commits` never witnesses a stale pair.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]

/-! ## The height-event check, keyed on the two recorded pairs

`processHeightEvents_advance` and `_of_target` (`SlotClosure.lean`) are keyed on the height and
the target. These two are keyed on the pairs `Certified` reads. Both are phrased over `σ`'s own
fields although the later branches read the state the finality sub-step leaves — that state
differs in `F` and `h_F` only, which none of the read fields mention. -/

/-- What the check does to `(J, h_j)` and `P`, together: either all three are untouched, or a
    justification advance fired — the new pair is the named target at the current height, backed
    by a target quorum, and `P` is cleared. Reporting `P` in the same disjunction is the point:
    `J` never changes while `P` survives. -/
theorem processHeightEvents_J_P (σ : ChainState Node Root) (st : Time) :
    ((processHeightEvents σ st).J = σ.J ∧ (processHeightEvents σ st).h_j = σ.h_j ∧
      (processHeightEvents σ st).P = σ.P) ∨
    ((processHeightEvents σ st).P = ∅ ∧ ∃ T, σ.T_h = some T ∧
      (processHeightEvents σ st).J = T ∧ (processHeightEvents σ st).h_j = σ.h ∧
      w(σ.Qtarget)≥q) := by
  simp only [processHeightEvents, Id.run]
  cases hT : σ.T_h with
  | none =>
      split_ifs <;>
        first
          | exact Or.inl ⟨rfl, rfl, rfl⟩
          | (rename_i hb; exact absurd rfl hb.2.1)
          | exact Or.inl ⟨advanceHeight_none_J _ _, advanceHeight_none_h_j _ _,
              advanceHeight_none_P _ _⟩
  | some T =>
      split_ifs <;>
        first
          | exact Or.inl ⟨rfl, rfl, rfl⟩
          | (rename_i hb; exact Or.inr ⟨advanceHeight_P_some _ _ _, T, rfl,
              advanceHeight_J_some _ _ _, advanceHeight_h_j_some _ _ _, hb.2.2⟩)
          | exact Or.inl ⟨advanceHeight_none_J _ _, advanceHeight_none_h_j _ _,
              advanceHeight_none_P _ _⟩

/-- What the check does to `(F, h_F)`: untouched, or the finality sub-step copied `(J, h_j)` in,
    on a commit quorum and a strict height gap. -/
theorem processHeightEvents_F_pair (σ : ChainState Node Root) (st : Time) :
    ((processHeightEvents σ st).F = σ.F ∧ (processHeightEvents σ st).h_F = σ.h_F) ∨
    ((processHeightEvents σ st).F = σ.J ∧ (processHeightEvents σ st).h_F = σ.h_j ∧
      σ.h_F < σ.h_j ∧ w(σ.P)≥q) := by
  by_cases hfin : σ.h_j > σ.h_F ∧ σ.F ⪯ σ.J ∧ w(σ.P)≥q
  · simp only [processHeightEvents, Id.run, if_pos hfin]
    split_ifs <;>
      first
        | exact Or.inr ⟨rfl, rfl, hfin.1, hfin.2.2⟩
        | exact Or.inr ⟨advanceHeight_F _ _ _, advanceHeight_h_F _ _ _, hfin.1, hfin.2.2⟩
  · simp only [processHeightEvents, Id.run, if_neg hfin]
    split_ifs <;>
      first
        | exact Or.inl ⟨rfl, rfl⟩
        | exact Or.inl ⟨advanceHeight_F _ _ _, advanceHeight_h_F _ _ _⟩

/-! ## Figure 2's writer of the finality tally -/

/-- Line 776 is the only writer of `P`, and this is what it wrote: either the bit was already
    set, or `a` set it and `a`'s finality pair is a commit to the current `(h_j, J)`. -/
theorem processAttestation_P_mem (σ : ChainState Node Root) (a : Attestation Node Root)
    (A : Blk Node Root) (i : Node) (hi : i ∈ (processAttestation σ a A).P) :
    i ∈ σ.P ∨ (a.validator = i ∧ a.finalityPair = .commit σ.h_j σ.J) := by
  simp only [processAttestation] at hi
  repeat' split at hi
  all_goals (simp_all [Finset.mem_insert]; try tauto)

/-- `process_attestation` leaves the three finality-side scalars alone. -/
theorem processAttestation_finFields (σ : ChainState Node Root) (a : Attestation Node Root)
    (A : Blk Node Root) :
    (processAttestation σ a A).h_j = σ.h_j ∧ (processAttestation σ a A).J = σ.J ∧
      (processAttestation σ a A).F = σ.F ∧ (processAttestation σ a A).h_F = σ.h_F := by
  simp only [processAttestation]; repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

/-- The fold: every bit of the finality tally was there at the start, or was set by one of the
    block's own attestations, a commit to the fold-initial `(h_j, J)` — which the fold never
    moves. -/
theorem processAttestations_P_mem :
    ∀ (as : List (Attestation Node Root)) {σ : ChainState Node Root} (A : Blk Node Root)
      (i : Node), i ∈ (processAttestations σ as A).P →
      i ∈ σ.P ∨ ∃ a ∈ as, a.validator = i ∧ a.finalityPair = .commit σ.h_j σ.J
  | [], _, _, _, hi => Or.inl hi
  | a :: as, σ, A, i, hi => by
      rw [processAttestations_cons] at hi
      obtain ⟨hhj, hJ, -, -⟩ := processAttestation_finFields σ a A
      rcases processAttestations_P_mem as A i hi with h1 | ⟨b, hb, hv, hpair⟩
      · rcases processAttestation_P_mem σ a A i h1 with h2 | ⟨hv, hpair⟩
        · exact Or.inl h2
        · exact Or.inr ⟨a, by simp, hv, hpair⟩
      · rw [hhj, hJ] at hpair
        exact Or.inr ⟨b, by simp [hb], hv, hpair⟩

theorem processAttestations_finFields :
    ∀ (as : List (Attestation Node Root)) {σ : ChainState Node Root} (A : Blk Node Root),
      (processAttestations σ as A).h_j = σ.h_j ∧ (processAttestations σ as A).J = σ.J ∧
        (processAttestations σ as A).F = σ.F ∧ (processAttestations σ as A).h_F = σ.h_F
  | [], _, _ => ⟨rfl, rfl, rfl, rfl⟩
  | a :: as, σ, A => by
      rw [processAttestations_cons]
      obtain ⟨h1, h2, h3, h4⟩ := processAttestation_finFields σ a A
      obtain ⟨g1, g2, g3, g4⟩ := processAttestations_finFields as (σ := processAttestation σ a A) A
      exact ⟨g1.trans h1, g2.trans h2, g3.trans h3, g4.trans h4⟩

/-- `process_block`'s inclusion check, as a fact about the block's own attestations. -/
theorem processBlock_validators {σ σ' : ChainState Node Root} {B : Blk Node Root}
    (he : processBlock σ B = .state σ') :
    ∀ a ∈ B.attestations, a.validator ∈ Electorate.V := by
  simp only [processBlock, Id.run] at he
  split_ifs at he with hc
  simp only [not_or, not_not] at hc
  intro a ha
  have := hc.2.2
  rw [List.all_eq_true] at this
  have := this a ha
  rwa [ValidInclusion, decide_eq_true_eq] at this

/-! ## The invariant -/

/-- The recorded pairs have quorums behind them. See the module docstring. -/
structure Certified (σ : ChainState Node Root) : Prop where
  /-- The finality tally is inside the electorate. -/
  PsubV : σ.P ⊆ Electorate.V
  /-- Every bit of the finality tally has an included commit to the current `(h_j, J)`. -/
  commits : ∀ i ∈ σ.P, ∃ a : Attestation Node Root, a.validator = i ∧
    a.finalityPair = .commit σ.h_j σ.J ∧ IncludedOn a σ.L
  /-- A justified pair at `h_j ≥ 1` has an included target quorum behind it, and the justified
      block's own post-state sits at `h_j`. -/
  just : 1 ≤ σ.h_j →
    (∃ Q : Finset Node, Q ⊆ Electorate.V ∧ w(Q)≥q ∧
      ∀ i ∈ Q, ∃ a : Attestation Node Root, a.validator = i ∧
        a.heightPair = .target σ.h_j σ.J ∧ IncludedOn a σ.L) ∧
    (postState σ.J).map ChainState.h = some σ.h_j
  /-- A finalized pair at `h_F ≥ 1` has an included commit quorum and an included target quorum
      behind it, and the finalized block's own post-state sits at `h_F`. -/
  fin : 1 ≤ σ.h_F →
    (∃ Q : Finset Node, Q ⊆ Electorate.V ∧ w(Q)≥q ∧
      ∀ i ∈ Q, ∃ a : Attestation Node Root, a.validator = i ∧
        a.finalityPair = .commit σ.h_F σ.F ∧ IncludedOn a σ.L) ∧
    (∃ Q : Finset Node, Q ⊆ Electorate.V ∧ w(Q)≥q ∧
      ∀ i ∈ Q, ∃ a : Attestation Node Root, a.validator = i ∧
        a.heightPair = .target σ.h_F σ.F ∧ IncludedOn a σ.L) ∧
    (postState σ.F).map ChainState.h = some σ.h_F
  /-- A finalized height of `0` is genesis, finalized by stipulation. -/
  fin0 : σ.h_F = 0 → σ.F = .genesis

/-- The congruence lemma: a state agreeing on the five fields the invariant reads is certified,
    and the endpoint may move down the chain. -/
theorem Certified.of_fields {σ τ : ChainState Node Root} (h : Certified σ)
    (hP : τ.P = σ.P) (hJ : τ.J = σ.J) (hhj : τ.h_j = σ.h_j)
    (hF : τ.F = σ.F) (hhF : τ.h_F = σ.h_F) (hL : σ.L ⪯ τ.L) : Certified τ where
  PsubV := hP ▸ h.PsubV
  commits i hi := by
    obtain ⟨a, h1, h2, h3⟩ := h.commits i (hP ▸ hi)
    exact ⟨a, h1, by rw [hhj, hJ]; exact h2, h3.mono hL⟩
  just h1 := by
    obtain ⟨⟨Q, hQV, hQw, hQa⟩, hanc⟩ := h.just (hhj ▸ h1)
    refine ⟨⟨Q, hQV, hQw, fun i hi => ?_⟩, by rw [hJ, hhj]; exact hanc⟩
    obtain ⟨a, g1, g2, g3⟩ := hQa i hi
    exact ⟨a, g1, by rw [hhj, hJ]; exact g2, g3.mono hL⟩
  fin h1 := by
    obtain ⟨⟨Q, hQV, hQw, hQa⟩, ⟨Q', hQ'V, hQ'w, hQ'a⟩, hanc⟩ := h.fin (hhF ▸ h1)
    refine ⟨⟨Q, hQV, hQw, fun i hi => ?_⟩, ⟨Q', hQ'V, hQ'w, fun i hi => ?_⟩,
        by rw [hF, hhF]; exact hanc⟩
    · obtain ⟨a, g1, g2, g3⟩ := hQa i hi
      exact ⟨a, g1, by rw [hhF, hF]; exact g2, g3.mono hL⟩
    · obtain ⟨a, g1, g2, g3⟩ := hQ'a i hi
      exact ⟨a, g1, by rw [hhF, hF]; exact g2, g3.mono hL⟩
  fin0 h0 := by rw [hF]; exact h.fin0 (hhF ▸ h0)

theorem certified_gen : Certified (ChainState.gen (Node := Node) (Root := Root)) where
  PsubV := by simp [ChainState.gen]
  commits i hi := by simp [ChainState.gen] at hi
  just h1 := by simp [ChainState.gen] at h1
  fin h1 := by simp [ChainState.gen] at h1
  fin0 _ := rfl

/-- A whole transition keeps the invariant. Slot closure moves nothing the invariant reads; the
    block phase moves `L` one ancestry step and grows the tally with commits its writer pins;
    and the height-event check is covered by the two pair lemmas — each disjunct either keeps a
    field or rebuilds its clause from `commits`, `just`, `Witnessed` and `Fresh`. -/
theorem Certified.stateTransition [PositiveWeight Node] {σp σ' : ChainState Node Root}
    {B : Blk Node Root} (hc : Certified σp) (hp : BlockPostState σp)
    (ht : stateTransition σp B = .state σ') : Certified σ' := by
  obtain ⟨σ₂, hb, rfl⟩ := stateTransition_state ht
  -- the closure's record equation: only `s` and `T_h` move
  obtain ⟨Th, -, heqC⟩ := emptySlotNoop B.slot hp
  rw [actionState] at heqC
  -- the block phase
  have h2eq := processBlock_state hb
  have hpar : B.parent = some σp.L := by
    have := processBlock_parent hb
    rwa [heqC] at this
  have hLB : σp.L ⪯ B := parent_preceq hpar
  obtain ⟨hhj₂, hJ₂, hF₂, hhF₂⟩ :=
    processAttestations_finFields B.attestations
      (σ := { processSlots σp B.slot with L := B }) (processSlots σp B.slot).L
  have hhj₂' : σ₂.h_j = σp.h_j := by rw [h2eq, hhj₂, heqC]
  have hJ₂' : σ₂.J = σp.J := by rw [h2eq, hJ₂, heqC]
  have hF₂' : σ₂.F = σp.F := by rw [h2eq, hF₂, heqC]
  have hhF₂' : σ₂.h_F = σp.h_F := by rw [h2eq, hhF₂, heqC]
  have hL₂ : σ₂.L = B := by
    rw [h2eq]
    exact (processAttestations_chainFields _ _).1
  have hh₂ : σ₂.h = σp.h := (postBlock_fields hp hb).1
  -- `Certified` after the block phase
  have hc₂ : Certified σ₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- PsubV
      intro i hi
      have hi' : i ∈ (processAttestations { processSlots σp B.slot with L := B }
          B.attestations (processSlots σp B.slot).L).P := by rw [← h2eq]; exact hi
      rcases processAttestations_P_mem B.attestations _ i hi' with h1 | ⟨a, ha, hv, -⟩
      · have : i ∈ σp.P := by
          have : ({ processSlots σp B.slot with L := B } : ChainState Node Root).P = σp.P := by
            rw [heqC]
          rwa [this] at h1
        exact hc.PsubV this
      · rw [← hv]; exact processBlock_validators hb a ha
    · -- commits
      intro i hi
      have hi' : i ∈ (processAttestations { processSlots σp B.slot with L := B }
          B.attestations (processSlots σp B.slot).L).P := by rw [← h2eq]; exact hi
      rcases processAttestations_P_mem B.attestations _ i hi' with h1 | ⟨a, ha, hv, hpair⟩
      · have h1' : i ∈ σp.P := by
          have : ({ processSlots σp B.slot with L := B } : ChainState Node Root).P = σp.P := by
            rw [heqC]
          rwa [this] at h1
        obtain ⟨a, g1, g2, g3⟩ := hc.commits i h1'
        exact ⟨a, g1, by rw [hhj₂', hJ₂']; exact g2, by rw [hL₂]; exact g3.mono hLB⟩
      · refine ⟨a, hv, ?_, by rw [hL₂]; exact ⟨B, Preceq.refl B, ha⟩⟩
        have : ({ processSlots σp B.slot with L := B } : ChainState Node Root).h_j = σp.h_j ∧
            ({ processSlots σp B.slot with L := B } : ChainState Node Root).J = σp.J := by
          constructor <;> rw [heqC]
        rw [hhj₂', hJ₂']
        rw [this.1, this.2] at hpair
        exact hpair
    · -- just
      intro h1
      obtain ⟨⟨Q, hQV, hQw, hQa⟩, hanc⟩ := hc.just (hhj₂' ▸ h1)
      refine ⟨⟨Q, hQV, hQw, fun i hi => ?_⟩, by rw [hJ₂', hhj₂']; exact hanc⟩
      obtain ⟨a, g1, g2, g3⟩ := hQa i hi
      exact ⟨a, g1, by rw [hhj₂', hJ₂']; exact g2, by rw [hL₂]; exact g3.mono hLB⟩
    · -- fin
      intro h1
      obtain ⟨⟨Q, hQV, hQw, hQa⟩, ⟨Q', hQ'V, hQ'w, hQ'a⟩, hanc⟩ := hc.fin (hhF₂' ▸ h1)
      refine ⟨⟨Q, hQV, hQw, fun i hi => ?_⟩, ⟨Q', hQ'V, hQ'w, fun i hi => ?_⟩,
          by rw [hF₂', hhF₂']; exact hanc⟩
      · obtain ⟨a, g1, g2, g3⟩ := hQa i hi
        exact ⟨a, g1, by rw [hhF₂', hF₂']; exact g2, by rw [hL₂]; exact g3.mono hLB⟩
      · obtain ⟨a, g1, g2, g3⟩ := hQ'a i hi
        exact ⟨a, g1, by rw [hhF₂', hF₂']; exact g2, by rw [hL₂]; exact g3.mono hLB⟩
    · -- fin0
      intro h0
      rw [hF₂']; exact hc.fin0 (hhF₂' ▸ h0)
  -- `Witnessed` after the block phase, for the justification rebuild
  have hw₂ : Witnessed σ₂ :=
    (((witnessed_of_blockPostState hp).processSlots (settled_of_blockPostState hp)
      q_pos B.slot).processBlock hb)
  -- the height-event check
  have hLpost := processHeightEvents_L σ₂ B.slot
  rcases processHeightEvents_J_P σ₂ B.slot with ⟨hJn, hhjn, hPn⟩ | ⟨hPn, T, hTn, hJn, hhjn, hQw⟩ <;>
    rcases processHeightEvents_F_pair σ₂ B.slot with ⟨hFn, hhFn⟩ | ⟨hFn, hhFn, hgap, hPq⟩
  · -- nothing fired
    exact hc₂.of_fields hPn hJn hhjn hFn hhFn (by rw [hLpost]; exact Preceq.refl _)
  · -- finality copy, no justification move
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hPn]; exact hc₂.PsubV
    · intro i hi
      obtain ⟨a, g1, g2, g3⟩ := hc₂.commits i (hPn ▸ hi)
      exact ⟨a, g1, by rw [hhjn, hJn]; exact g2, by rw [hLpost]; exact g3⟩
    · intro h1
      obtain ⟨⟨Q, hQV, hQw, hQa⟩, hanc⟩ := hc₂.just (hhjn ▸ h1)
      refine ⟨⟨Q, hQV, hQw, fun i hi => ?_⟩, by rw [hJn, hhjn]; exact hanc⟩
      obtain ⟨a, g1, g2, g3⟩ := hQa i hi
      exact ⟨a, g1, by rw [hhjn, hJn]; exact g2, by rw [hLpost]; exact g3⟩
    · intro _
      have h1j : 1 ≤ σ₂.h_j := by omega
      obtain ⟨⟨Q, hQV, hQw, hQa⟩, hanc⟩ := hc₂.just h1j
      refine ⟨⟨σ₂.P, hc₂.PsubV, hPq, fun i hi => ?_⟩, ⟨Q, hQV, hQw, fun i hi => ?_⟩,
          by rw [hFn, hhFn]; exact hanc⟩
      · obtain ⟨a, g1, g2, g3⟩ := hc₂.commits i hi
        exact ⟨a, g1, by rw [hhFn, hFn]; exact g2, by rw [hLpost]; exact g3⟩
      · obtain ⟨a, g1, g2, g3⟩ := hQa i hi
        exact ⟨a, g1, by rw [hhFn, hFn]; exact g2, by rw [hLpost]; exact g3⟩
    · intro h0
      rw [hhFn] at h0
      omega
  · -- justification advance, no finality copy
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hPn]; exact Finset.empty_subset _
    · intro i hi
      rw [hPn] at hi
      exact absurd hi (by simp)
    · intro _
      -- the target quorum that fired, witnessed vote by vote
      refine ⟨⟨σ₂.Qtarget, Finset.filter_subset _ _, hQw, fun i hi => ?_⟩, ?_⟩
      · obtain ⟨T', a, hT', g1, g2, g3⟩ := hw₂.target i hi
        rw [hTn] at hT'
        injection hT' with hT'
        exact ⟨a, g1, by rw [hhjn, hJn, hT']; exact g2, by rw [hLpost]; exact g3⟩
      · -- the anchor: the named target's post-state sits at the current height
        rw [hJn, hhjn]
        rcases postBlock_target hp hb with hcase | hcase
        · have hTp : σp.T_h = some T := by rw [← hcase]; exact hTn
          obtain ⟨σT, hbps, hLT, hhT⟩ := (fresh_of_blockPostState hp).anchor T hTp
          have : postState T = .state σT := by
            have := postState_of_blockPostState hbps
            rwa [hLT] at this
          rw [this, TransitionResult.map_state, hhT, hh₂]
        · have hTL : T = σp.L := by
            rw [hcase] at hTn
            injection hTn with h
            exact h.symm
          have : postState T = .state σp := by
            rw [hTL]
            exact postState_of_blockPostState hp
          rw [this, TransitionResult.map_state, hh₂]
    · intro h1
      obtain ⟨hcq, htq, hanc⟩ := hc₂.fin (hhFn ▸ h1)
      obtain ⟨Q, hQV, hQw, hQa⟩ := hcq
      obtain ⟨Q', hQ'V, hQ'w, hQ'a⟩ := htq
      refine ⟨⟨Q, hQV, hQw, fun i hi => ?_⟩, ⟨Q', hQ'V, hQ'w, fun i hi => ?_⟩,
          by rw [hFn, hhFn]; exact hanc⟩
      · obtain ⟨a, g1, g2, g3⟩ := hQa i hi
        exact ⟨a, g1, by rw [hhFn, hFn]; exact g2, by rw [hLpost]; exact g3⟩
      · obtain ⟨a, g1, g2, g3⟩ := hQ'a i hi
        exact ⟨a, g1, by rw [hhFn, hFn]; exact g2, by rw [hLpost]; exact g3⟩
    · intro h0
      rw [hhFn] at h0
      rw [hFn]
      exact hc₂.fin0 h0
  · -- finality copy and justification advance in one check
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hPn]; exact Finset.empty_subset _
    · intro i hi
      rw [hPn] at hi
      exact absurd hi (by simp)
    · intro _
      refine ⟨⟨σ₂.Qtarget, Finset.filter_subset _ _, hQw, fun i hi => ?_⟩, ?_⟩
      · obtain ⟨T', a, hT', g1, g2, g3⟩ := hw₂.target i hi
        rw [hTn] at hT'
        injection hT' with hT'
        exact ⟨a, g1, by rw [hhjn, hJn, hT']; exact g2, by rw [hLpost]; exact g3⟩
      · rw [hJn, hhjn]
        rcases postBlock_target hp hb with hcase | hcase
        · have hTp : σp.T_h = some T := by rw [← hcase]; exact hTn
          obtain ⟨σT, hbps, hLT, hhT⟩ := (fresh_of_blockPostState hp).anchor T hTp
          have : postState T = .state σT := by
            have := postState_of_blockPostState hbps
            rwa [hLT] at this
          rw [this, TransitionResult.map_state, hhT, hh₂]
        · have hTL : T = σp.L := by
            rw [hcase] at hTn
            injection hTn with h
            exact h.symm
          have : postState T = .state σp := by
            rw [hTL]
            exact postState_of_blockPostState hp
          rw [this, TransitionResult.map_state, hh₂]
    · intro _
      have h1j : 1 ≤ σ₂.h_j := by omega
      obtain ⟨⟨Q, hQV, hQw, hQa⟩, hanc⟩ := hc₂.just h1j
      refine ⟨⟨σ₂.P, hc₂.PsubV, hPq, fun i hi => ?_⟩, ⟨Q, hQV, hQw, fun i hi => ?_⟩,
          by rw [hFn, hhFn]; exact hanc⟩
      · obtain ⟨a, g1, g2, g3⟩ := hc₂.commits i hi
        exact ⟨a, g1, by rw [hhFn, hFn]; exact g2, by rw [hLpost]; exact g3⟩
      · obtain ⟨a, g1, g2, g3⟩ := hQa i hi
        exact ⟨a, g1, by rw [hhFn, hFn]; exact g2, by rw [hLpost]; exact g3⟩
    · intro h0
      rw [hhFn] at h0
      omega

/-- Every block post-state is `Certified`. -/
theorem certified_of_blockPostState [PositiveWeight Node] {σ : ChainState Node Root}
    (h : BlockPostState σ) : Certified σ := by
  induction h with
  | gen => exact certified_gen
  | step hp hst ih => exact ih.stateTransition hp hst

end Proofs

end Decoupled
