import Mathlib.Data.Finset.Max
-- `Finset.exists_max_image` — the maximum of a finite image, which `exists_leaf` picks the
-- leaf with. Nothing already imported carries it: `Spec` stops at `Finset.Defs`, and
-- `Analysis/Proofs/Weights.lean` adds only the big-operators files a weight sum needs.
import Analysis.Proofs.Upgrade

/-!
# Leaves, and Lemma 10 (`hft:lem:viable-finalized`)

Definition 11 (`hft:def:viable`) reads viability off a **leaf**: `B ∈ T'(Σ)` when some leaf
`L ⪰ B` of the accepted tree has `σ[L].h ≥ Σ.hmax − 1`. So a viability proof owes a leaf, and
this file's first job is to produce one.

**`exists_leaf`.** Every accepted block has a leaf above it. The witness is the maximum-slot
element of the accepted blocks descending from it: a proper descendant of that inside the tree
would sit at a strictly later slot — one chain holds at most one block per slot
(`prec_slot_lt`, whose replayability comes from `domT` and the recorded-replay bridge) — and
would still descend from the block we started at, contradicting maximality. This is where the
paper's "any leaf descendant preserves the maximum by state-height monotonicity" gets its
leaf; the paper says "pick any leaf" and does not say why one exists.

**`viable_of_height_lt`.** The content of Lemma 10 (`hft:lem:viable-finalized`), stated over
what the argument actually uses rather than over the paper's hypotheses: a block finalized at
a height strictly below the store's maximum, and already accepted, is viable — or a slashable
set is exhibited. The paper reaches `Σ.hmax ≥ h_f + 1` from the processing of `B`, then picks a
maximum-height leaf and calls its Lemma 4 (`hft:lem:mainsafety`, healing's Lemma 10
`lem:past-finalized`) to put `F` below it. Splitting the height bound out as a hypothesis is
what lets both Theorem 8 and Theorem 9 use this: they establish `h_f < Σ.hmax` from different
records — Theorem 8 from the accepted block's own `h_F ≤ h_j < h`, Theorem 9 from the
justifying record's `h_j = h_f < h`.

Membership of `F` in the tree is a hypothesis for the same reason: `viableTree` is a filter of
`Σ.T`, so viability presupposes acceptance, and each caller has its own short route to it —
`mem_T_of_preceq`, the tree's downward closure along `⪯`, applied to a record whose chain runs
through `F`.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

section Store
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-- **The accepted tree is closed downward along `⪯`.** `StoreInv`'s `parentT` field is one
    step of this; the walk to genesis is the structural recursion on the descendant. Every
    quorum argument that finds a block *inside* a record's chain and then needs it in `S.T` —
    to place evidence, or to claim viability — goes through this. -/
theorem mem_T_of_preceq {S : Store Node Root} (hinv : StoreInv S) :
    ∀ (B : Blk Node Root), B ∈ S.T → ∀ (C : Blk Node Root), C ⪯ B → C ∈ S.T
  | .genesis, hB, C, hC => by
      simp only [Preceq, ancestors, List.mem_singleton] at hC
      subst hC; exact hB
  | .mk p s n as r, hB, C, hC => by
      simp only [Preceq, ancestors, List.mem_cons] at hC
      rcases hC with rfl | hC
      · exact hB
      · exact mem_T_of_preceq hinv p (hinv.parentT _ hB p rfl) C hC

/-- **Every accepted block has a leaf above it.** See the module docstring for the argument. -/
theorem exists_leaf {S : Store Node Root} (hinv : StoreInv S) {B₀ : Blk Node Root}
    (hB₀ : B₀ ∈ S.T) : ∃ L ∈ S.T, B₀ ⪯ L ∧ ∀ C ∈ S.T, ¬ L ≺ C := by
  have hne : (S.T.filter (fun B => B₀ ⪯ B)).Nonempty :=
    ⟨B₀, Finset.mem_filter.2 ⟨hB₀, Preceq.refl _⟩⟩
  obtain ⟨L, hL, hmax⟩ :=
    Finset.exists_max_image (S.T.filter (fun B => B₀ ⪯ B)) Blk.slot hne
  rw [Finset.mem_filter] at hL
  refine ⟨L, hL.1, hL.2, fun C hC hlt => ?_⟩
  have hCf : C ∈ S.T.filter (fun B => B₀ ⪯ B) :=
    Finset.mem_filter.2 ⟨hC, Preceq.trans hL.2 hlt.1⟩
  have hslot : C.slot ≤ L.slot := hmax C hCf
  obtain ⟨σC, hσC⟩ : ∃ σC, S.σ C = some σC := Option.isSome_iff_exists.1 ((hinv.domT C).1 hC)
  have := prec_slot_lt hlt (record_postState hinv hσC)
  omega

omit [Electorate Node] [Params] [BlockHash Node Root] in
/-- Definition 11 (`hft:def:viable`)'s closed form, assembled from its parts: the accepted
    block, the leaf above it, and that leaf's height read through the map. -/
theorem mem_viableTree {S : Store Node Root} {B L : Blk Node Root} {σL : ChainState Node Root}
    (hB : B ∈ S.T) (hLT : L ∈ S.T) (hleaf : ∀ C ∈ S.T, ¬ L ≺ C) (hBL : B ⪯ L)
    (hσL : S.σ L = some σL) (hh : σL.h ≥ S.hmax - 1) : B ∈ viableTree S := by
  refine Finset.mem_filter.2 ⟨hB, L, hLT, hleaf, hBL, ?_⟩
  rw [hσL]
  simpa using hh

/-- Lemma 10 (`hft:lem:viable-finalized`)'s content. Read aloud: a block that some chain
    finalized at a height strictly below the store's maximum state-height, and that the store
    has accepted, is viable — or a slashable set of weight `2q − W` is exhibited.

    The maximum-height record is a chain past `h_f`, so healing's Lemma 10 puts `F` on it or
    produces the evidence; a leaf above that record has the same height, since heights only
    grow along `⪯` and `hmax` bounds them; and that leaf is the viability witness. At `h_f = 0`
    the finalized block is genesis (`Certified.fin0`), which is on every chain, so the
    evidence branch is never reached there — which is why `1 ≤ h_f` is derived inside rather
    than assumed. -/
theorem viable_of_height_lt [PositiveWeight Node] {S : Store Node Root} (hinv : StoreInv S)
    {B_F F : Blk Node Root} {h_f : Nat}
    (hBF : postState B_F ≠ invalid)
    (hF : (postState' B_F).F = F) (hhF : (postState' B_F).h_F = h_f)
    (hFT : F ∈ S.T) (hlt : h_f < S.hmax) :
    F ∈ viableTree S ∨ SlashableSet S B_F := by
  have hσF : postState B_F = .state (postState' B_F hBF) := TransitionResult.state_get _ hBF
  have hcertF := certified_of_blockPostState (blockPostState_of_postState B_F hσF)
  obtain ⟨B₂, σ₂, hB₂, hh₂⟩ := hinv.hmaxEx
  have hpost₂ : postState B₂ = .state σ₂ := record_postState hinv hB₂
  have hT₂ : B₂ ∈ S.T := record_mem_T hinv hB₂
  have hlt₂ : h_f < σ₂.h := by rw [hh₂]; exact hlt
  by_cases hFB₂ : F ⪯ B₂
  · -- the maximum-height block descends from `F`; a leaf above it keeps the maximum
    left
    obtain ⟨L, hLT, hB₂L, hleaf⟩ := exists_leaf hinv hT₂
    obtain ⟨σL, hσL⟩ : ∃ σL, S.σ L = some σL := Option.isSome_iff_exists.1 ((hinv.domT L).1 hLT)
    have hpostL : postState L = .state σL := record_postState hinv hσL
    have hge : σ₂.h ≤ σL.h := postState_h_le L hB₂L hpost₂ hpostL
    have hle : σL.h ≤ S.hmax := hinv.hmaxLe L σL hσL
    exact mem_viableTree hFT hLT hleaf (Preceq.trans hFB₂ hB₂L) hσL (by omega)
  · -- otherwise the maximum-height chain has passed `h_f` without containing `F`
    right
    have h1 : 1 ≤ h_f := by
      by_contra h0
      have hg : (postState' B_F hBF).F = .genesis := hcertF.fin0 (by rw [hhF]; omega)
      rw [hF] at hg
      exact hFB₂ (by rw [hg]; exact genesis_preceq _)
    obtain ⟨A, hw, hev⟩ := pastFinalized_evidence hBF hF hhF hpost₂ h1 hlt₂ hFB₂
    refine ⟨A, hw, fun v hv => ?_⟩
    obtain ⟨a, b, hav, hbv, hai, hbi, he⟩ := hev v hv
    exact ⟨a, b, hav, hbv, Or.inl hai, RetainedOn.ofChain hT₂ hbi, he⟩

end Store

end Proofs

end Decoupled
