import Analysis.Proofs.Provenance
import Analysis.Proofs.ChainTarget

/-!
# Proofs: finalized blocks form a chain, and conflicting finalization pays (Lemmas 10, 11, Theorem 5)

Three results, one dependency line:

* **Lemma 10** (`lem:past-finalized`) is proved: `exists_first_advance` walks `B`'s chain to the
  transition that first stepped past `h` — from exactly `h` to `h + 1`, by Lemma 6 — and
  `pastFinalized_evidence` intersects `C`'s commit quorum (out of the recorded pair, by
  `Certified.fin`) with the quorum that fired there. A signer of both holds a commit to `(h, C)`
  and a height-`h` vote, and unless the vote targets `C` — which would put `C` on the chain, by
  the named target on the exact branch and by `Witnessed.progress`'s ancestry arm on the progress
  branch — the pair is E1, timeout case included.
* **Lemma 11** (`lem:finalized-chain`) is proved. `h = 0` is genesis by `Certified.fin0` and
  `genesis_preceq`. Equal heights intersect `C`'s commit quorum with `C'`'s target quorum — both
  recovered from the recorded pairs by `Certified.fin` — and every intersection signer is
  E1-slashable unless `C = C'`. Different heights go through Lemma 10: either its evidence, or
  `C` is on `C'`'s own chain, and then the two anchors (`Certified.fin`'s third conjunct), the
  comparability of two ancestors (`preceq_or_preceq`) and height monotonicity
  (`postState_h_le`) order `C` below `C'`.
* **Theorem 5** (`thm:accountable-safety`) is Lemma 11 plus a case split: order the two heights
  with `Nat.le_total`, and in each branch the lemma's first disjunct is one arm of `Compatible`,
  which `Conflicts` refuses — so the evidence disjunct is all that is left.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]

/-- **The first advance past `h`.** A chain whose post-state has moved beyond `h ≥ 1` contains a
    block whose own transition stepped from exactly `h` to `h + 1`: walk down the chain past the
    blocks still beyond `h`; the first one whose parent is not moved by exactly one, by Lemma 6.
    Genesis closes the walk, its post-state sitting at height `1 ≤ h` already. -/
theorem exists_first_advance [PositiveWeight Node] :
    ∀ (B : Blk Node Root) {σB : ChainState Node Root} {h : Nat},
      postState B = .state σB → 1 ≤ h → h < σB.h →
      ∃ (D : Blk Node Root) (σp σD : ChainState Node Root), D ⪯ B ∧ BlockPostState σp ∧
        stateTransition σp D = .state σD ∧ σp.h = h ∧ σD.h = h + 1
  | .genesis, σB, h, hB, h1, hlt => by
      simp only [postState, TransitionResult.state.injEq] at hB
      rw [← hB] at hlt
      have hg : (ChainState.gen : ChainState Node Root).h = 1 := rfl
      omega
  | .mk p s n as r, σB, h, hB, h1, hlt => by
      rw [postState] at hB
      rcases hp : postState p with ⟨σp⟩ | _
      · rw [hp] at hB
        by_cases hph : h < σp.h
        · obtain ⟨D, σq, σD, hDle, hbps, htr, hh1, hh2⟩ := exists_first_advance p hp h1 hph
          exact ⟨D, σq, σD, Preceq.trans hDle (parent_preceq rfl), hbps, htr, hh1, hh2⟩
        · have hbps := blockPostState_of_postState p hp
          have hne : σB.h ≠ σp.h := by omega
          obtain ⟨hstep, -⟩ := heightProgression (Blk.mk p s n as r) hbps hB hne
          exact ⟨.mk p s n as r, σp, σB, Preceq.refl _, hbps, hB, by omega, by omega⟩
      · rw [hp] at hB; simp at hB

/-- Lemma 10's evidence, at the first advance. `C`'s commit quorum (out of the recorded pair, by
    `Certified.fin`) is intersected with the quorum that advanced past `h`; a signer of both holds
    a commit to `(h, C)` on `B_F`'s chain and a height-`h` vote on `B`'s, and unless that vote
    targets `C` the pair is E1. A vote targeting `C` puts `C` on `B`'s chain — the exact-target
    branch through the named target, the progress branch through `Witnessed.progress`'s ancestry
    arm — against `hCB`. -/
theorem pastFinalized_evidence [PositiveWeight Node] {B_F C B : Blk Node Root} {h : Nat}
    (hBF : postState B_F ≠ invalid)
    (hC : (postState' B_F).F = C) (hhF : (postState' B_F).h_F = h)
    {σB : ChainState Node Root} (hB : postState B = .state σB)
    (h1 : 1 ≤ h) (hlt : h < σB.h) (hCB : ¬ C ⪯ B) :
    ∃ S : Finset Node, w(S) ≥ 2 * q Node - W Node ∧
      ∀ i ∈ S, ∃ x y : Attestation Node Root, x.validator = i ∧ y.validator = i ∧
        IncludedOn x B_F ∧ IncludedOn y B ∧ E1 x y := by
  -- the commit quorum behind the recorded pair
  have hσF : postState B_F = .state (postState' B_F) := TransitionResult.state_get _ hBF
  have hbpF : BlockPostState (postState' B_F) := blockPostState_of_postState B_F hσF
  have hLF : (postState' B_F).L = B_F := postState_L B_F hσF
  obtain ⟨⟨Qc, hQcV, hQcw, hQca⟩, -, -⟩ :=
    (certified_of_blockPostState hbpF).fin (by rw [hhF]; exact h1)
  -- the first advance past h on B's chain
  obtain ⟨D, σp, σD, hDB, hbps, htr, hph, hDh⟩ := exists_first_advance B hB h1 hlt
  obtain ⟨σ₂, hb, hσDeq⟩ := stateTransition_state htr
  have hh₂ : σ₂.h = σp.h := (postBlock_fields hbps hb).1
  have hL₂ : σ₂.L = D := (postBlock_fields hbps hb).2.1
  have hw₂ : Witnessed σ₂ :=
    ((witnessed_of_blockPostState hbps).processSlots (settled_of_blockPostState hbps)
      q_pos D.slot).processBlock hb
  have hpar : σp.L ⪯ D := by
    have hpp := processBlock_parent hb
    rw [processSlots_L] at hpp
    exact parent_preceq hpp
  have hne₂ : (processHeightEvents σ₂ D.slot).h ≠ σ₂.h := by
    rw [← hσDeq]
    omega
  obtain ⟨-, -, hbranch⟩ := processHeightEvents_advance σ₂ D.slot hne₂
  rcases hbranch with ⟨hQw, -, -⟩ | ⟨hQw, -⟩
  · -- the exact-target branch advanced
    refine ⟨Qc ∩ σ₂.Qtarget,
      quorumIntersection hQcV (Finset.filter_subset _ _) hQcw hQw, fun i hi => ?_⟩
    obtain ⟨x, hxv, hxp, hxi⟩ := hQca i (Finset.mem_inter.1 hi).1
    obtain ⟨T, y, hTh₂, hyv, hyp, hyi⟩ := hw₂.target i (Finset.mem_inter.1 hi).2
    rw [hhF, hC] at hxp
    rw [hh₂, hph] at hyp
    rw [hL₂] at hyi
    refine ⟨x, y, hxv, hyv, by rwa [hLF] at hxi, hyi.mono hDB, ?_⟩
    by_cases hTC : T = C
    · exfalso
      rcases postBlock_target hbps hb with hcase | hcase
      · have hTp : σp.T_h = some T := by rw [← hcase]; exact hTh₂
        exact hCB (hTC ▸ Preceq.trans
          (Preceq.trans ((fresh_of_blockPostState hbps).onChain T hTp) hpar) hDB)
      · have hTeq : σp.L = T := by
          rw [hcase] at hTh₂
          exact Option.some.inj hTh₂
        exact hCB (hTC ▸ Preceq.trans (hTeq ▸ hpar) hDB)
    · exact ⟨h, C, hxp, Or.inl ⟨T, hyp, hTC⟩⟩
  · -- the progress branch advanced
    refine ⟨Qc ∩ σ₂.Qprog,
      quorumIntersection hQcV (Finset.filter_subset _ _) hQcw hQw, fun i hi => ?_⟩
    obtain ⟨x, hxv, hxp, hxi⟩ := hQca i (Finset.mem_inter.1 hi).1
    obtain ⟨y, hyv, hyi, harm⟩ := hw₂.progress i (Finset.mem_inter.1 hi).2
    rw [hhF, hC] at hxp
    rw [hL₂] at hyi
    refine ⟨x, y, hxv, hyv, by rwa [hLF] at hxi, hyi.mono hDB, ?_⟩
    rcases harm with hyp | ⟨T, hyp, hTL⟩
    · rw [hh₂, hph] at hyp
      exact ⟨h, C, hxp, Or.inr hyp⟩
    · rw [hh₂, hph] at hyp
      by_cases hTC : T = C
      · exfalso
        rw [hL₂] at hTL
        exact hCB (hTC ▸ Preceq.trans hTL hDB)
      · exact ⟨h, C, hxp, Or.inl ⟨T, hyp, hTC⟩⟩

/-- Lemma 10's content; `lemPastFinalized` in `Analysis/Lemmas.lean` is the statement of
    record and is this, verbatim. `h = 0` is genesis by stipulation; at `h ≥ 1` each subject
    either contains `C` or `pastFinalized_evidence` produces the slashable set — the two
    subjects are one argument, because slot closure moves neither the height nor anything else
    the evidence reads (Lemma 3). -/
theorem pastFinalized [PositiveWeight Node] {B_F C B : Blk Node Root} {h : Nat}
    (hBF : postState B_F ≠ invalid)
    (hC : (postState' B_F).F = C) (hhF : (postState' B_F).h_F = h)
    (hB : postState B ≠ invalid) (t : Time) :
    (h < (postState' B).h → C ⪯ B ∨
      (1 ≤ h ∧ ∃ S : Finset Node, w(S) ≥ 2 * q Node - W Node ∧
        ∀ i ∈ S, ∃ x y : Attestation Node Root, x.validator = i ∧ y.validator = i ∧
          IncludedOn x B_F ∧ IncludedOn y B ∧ E1 x y)) ∧
    (h < (actionState (postState' B) t).h → C ⪯ B ∨
      (1 ≤ h ∧ ∃ S : Finset Node, w(S) ≥ 2 * q Node - W Node ∧
        ∀ i ∈ S, ∃ x y : Attestation Node Root, x.validator = i ∧ y.validator = i ∧
          IncludedOn x B_F ∧ IncludedOn y B ∧ E1 x y)) := by
  have hσF : postState B_F = .state (postState' B_F) := TransitionResult.state_get _ hBF
  have hbpF : BlockPostState (postState' B_F) := blockPostState_of_postState B_F hσF
  by_cases h0 : h = 0
  · have hCg : C ⪯ B := by
      rw [← hC, (certified_of_blockPostState hbpF).fin0 (by rw [hhF, h0])]
      exact genesis_preceq B
    exact ⟨fun _ => Or.inl hCg, fun _ => Or.inl hCg⟩
  · have h1 : 1 ≤ h := Nat.one_le_iff_ne_zero.mpr h0
    have hσB : postState B = .state (postState' B) := TransitionResult.state_get _ hB
    have hbpB : BlockPostState (postState' B) := blockPostState_of_postState B hσB
    have hact : (actionState (postState' B) t).h = (postState' B).h := by
      obtain ⟨Th, -, heq⟩ := emptySlotNoop t hbpB
      rw [heq]
    constructor <;> intro hlt
    · by_cases hCB : C ⪯ B
      · exact Or.inl hCB
      · exact Or.inr ⟨h1, pastFinalized_evidence hBF hC hhF hσB h1 hlt hCB⟩
    · rw [hact] at hlt
      by_cases hCB : C ⪯ B
      · exact Or.inl hCB
      · exact Or.inr ⟨h1, pastFinalized_evidence hBF hC hhF hσB h1 hlt hCB⟩

/-- Lemma 11's content; `lemFinalizedChain` in `Analysis/Lemmas.lean` is the statement of
    record and is this, verbatim. The module docstring gives the three cases. -/
theorem finalizedChain [PositiveWeight Node] {B_F B_F' C C' : Blk Node Root} {h h' : Nat}
    (hBF : postState B_F ≠ invalid)
    (hC : (postState' B_F).F = C) (hhF : (postState' B_F).h_F = h)
    (hBF' : postState B_F' ≠ invalid)
    (hC' : (postState' B_F').F = C') (hhF' : (postState' B_F').h_F = h')
    (hle : h ≤ h') :
    C ⪯ C' ∨
      ∃ S : Finset Node, w(S) ≥ 2 * q Node - W Node ∧
        ∀ i ∈ S, ∃ x y : Attestation Node Root, x.validator = i ∧ y.validator = i ∧
          IncludedOn x B_F ∧ IncludedOn y B_F' ∧ (E1 x y ∨ E2 x y) := by
  have hσeq := TransitionResult.state_get _ hBF
  have hσeq' := TransitionResult.state_get _ hBF'
  have hbp : BlockPostState (postState' B_F) := blockPostState_of_postState B_F hσeq
  have hbp' : BlockPostState (postState' B_F') := blockPostState_of_postState B_F' hσeq'
  have hcert := certified_of_blockPostState hbp
  have hcert' := certified_of_blockPostState hbp'
  have hL : (postState' B_F).L = B_F := postState_L B_F hσeq
  have hL' : (postState' B_F').L = B_F' := postState_L B_F' hσeq'
  by_cases h0 : h = 0
  · -- height 0 is genesis, an ancestor of everything
    left
    have hFg : (postState' B_F).F = .genesis := hcert.fin0 (by rw [hhF, h0])
    rw [← hC, hFg]
    exact genesis_preceq C'
  · have h1 : 1 ≤ h := Nat.one_le_iff_ne_zero.mpr h0
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · -- equal heights: C's commit quorum against C''s target quorum
      by_cases hCC : C = C'
      · exact Or.inl (hCC ▸ Preceq.refl C)
      · obtain ⟨⟨Qc, hQcV, hQcw, hQca⟩, -, -⟩ := hcert.fin (by rw [hhF]; exact h1)
        obtain ⟨-, ⟨Qt, hQtV, hQtw, hQta⟩, -⟩ := hcert'.fin (by rw [hhF']; omega)
        right
        refine ⟨Qc ∩ Qt, quorumIntersection hQcV hQtV hQcw hQtw, fun i hi => ?_⟩
        obtain ⟨x, hxv, hxp, hxi⟩ := hQca i (Finset.mem_inter.1 hi).1
        obtain ⟨y, hyv, hyp, hyi⟩ := hQta i (Finset.mem_inter.1 hi).2
        refine ⟨x, y, hxv, hyv, by rwa [hL] at hxi, by rwa [hL'] at hyi, Or.inl ?_⟩
        rw [hhF, hC] at hxp
        rw [hhF', hC', ← heq] at hyp
        exact ⟨h, C, hxp, Or.inl ⟨C', hyp, fun he => hCC he.symm⟩⟩
    · -- different heights: through Lemma 10
      have hch' := chained_of_blockPostState hbp'
      have hadv : h < (postState' B_F').h := by
        have g1 := hch'.hF_le_hj
        have g2 := hch'.hj_lt_h
        rw [hhF'] at g1
        omega
      rcases (pastFinalized hBF hC hhF hBF' 0).1 hadv with hCB | ⟨-, S, hw, hev⟩
      · -- C is on C''s own chain: order the two by their post-state heights
        have hC'B : C' ⪯ B_F' := by
          have hj := Preceq.trans hch'.finJust hch'.justLatest
          rwa [hC', hL'] at hj
        obtain ⟨-, -, hanc⟩ := hcert.fin (by rw [hhF]; exact h1)
        obtain ⟨-, -, hanc'⟩ := hcert'.fin (by rw [hhF']; omega)
        rw [hC, hhF] at hanc
        rw [hC', hhF'] at hanc'
        obtain ⟨σC, hpC, hhC⟩ := TransitionResult.map_eq_some hanc
        obtain ⟨σC', hpC', hhC'⟩ := TransitionResult.map_eq_some hanc'
        rcases preceq_or_preceq B_F' hCB hC'B with hcc | hcc
        · exact Or.inl hcc
        · -- C' ⪯ C would put h' at or below h
          have := postState_h_le C hcc hpC' hpC
          omega
      · right
        refine ⟨S, hw, fun i hi => ?_⟩
        obtain ⟨x, y, hxv, hyv, hxi, hyi, he⟩ := hev i hi
        exact ⟨x, y, hxv, hyv, hxi, hyi, Or.inl he⟩

/-- Theorem 5's content: order the heights, apply `finalizedChain` in that order, and refuse its
    first disjunct with the conflict — `Conflicts` is `¬ (C ⪯ C' ∨ C' ⪯ C)`, and each branch's
    ancestry lands in one arm. The evidence's inclusions come out in the order the lemma was
    applied, which is the theorem's either-order disjunction. -/
theorem accountableSafety [PositiveWeight Node] {B_F B_F' C C' : Blk Node Root} {h h' : Nat}
    (hBF : postState B_F ≠ invalid)
    (hC : (postState' B_F).F = C) (hhF : (postState' B_F).h_F = h)
    (hBF' : postState B_F' ≠ invalid)
    (hC' : (postState' B_F').F = C') (hhF' : (postState' B_F').h_F = h')
    (hconf : Conflicts C C') :
    ∃ S : Finset Node, w(S) ≥ 2 * q Node - W Node ∧
      ∀ i ∈ S, ∃ x y : Attestation Node Root, x.validator = i ∧ y.validator = i ∧
        ((IncludedOn x B_F ∧ IncludedOn y B_F') ∨ (IncludedOn x B_F' ∧ IncludedOn y B_F)) ∧
        (E1 x y ∨ E2 x y) := by
  rcases Nat.le_total h h' with hle | hle
  · rcases finalizedChain hBF hC hhF hBF' hC' hhF' hle with hpre | ⟨S, hw, hev⟩
    · exact absurd (Or.inl hpre) hconf
    · refine ⟨S, hw, fun i hi => ?_⟩
      obtain ⟨x, y, hx, hy, hix, hiy, he⟩ := hev i hi
      exact ⟨x, y, hx, hy, Or.inl ⟨hix, hiy⟩, he⟩
  · rcases finalizedChain hBF' hC' hhF' hBF hC hhF hle with hpre | ⟨S, hw, hev⟩
    · exact absurd (Or.inr hpre) hconf
    · refine ⟨S, hw, fun i hi => ?_⟩
      obtain ⟨x, y, hx, hy, hix, hiy, he⟩ := hev i hi
      exact ⟨x, y, hx, hy, Or.inr ⟨hix, hiy⟩, he⟩

end Proofs

end Decoupled
