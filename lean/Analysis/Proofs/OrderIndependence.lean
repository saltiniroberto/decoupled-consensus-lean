import Analysis.Proofs.Fold

/-!
# Theorem 10 (`hft:thm:orderindep`): order independence

Two validators that received the same blocks, each in some parent-respecting order, agree on
everything the fork choice reads. The proof runs at the fold — `onBlocks Store.gen Bs` — and the
execution statement follows because a validator's store *is* that fold (`storeAt_eq_fold`,
`Analysis/Proofs/Fold.lean`).

## The shape of the argument

Everything turns on which blocks each order accepts, and `onBlocks_accept`
(`Analysis/Proofs/Fold.lean`) is what settles that: in a parent-first fold whose store-finalized
block never passes a given `Fmax`, every block of the list that is **comparable with `Fmax`** and
replays is accepted. So the two orders agree on the whole `⪯`-comparability class of `Fmax`, and
may differ only on blocks that conflict with it — which is the paper's own caveat, its third
sentence.

That lemma needs both directions of comparability, not just `Fmax ⪯ C`. A block *below* `Fmax`
has to be accepted too, or the parent chain of a block above it would be broken. It is: at the
moment such a block is offered, either the store's finalized block is at or below it — the
assert passes — or the store has already passed it, and then it is already accepted, because
`StoreInv`'s `fProv` plus the tree's downward closure put every ancestor of `Σ.F` in the tree
(`F_mem_T`). The paper does not make this step; it says "the `on_block` finality-ancestor
assertion accepts such a maximum-height block" and moves on.

The four claims then come out in order.

* **`F`.** The two finalized blocks are comparable (`fold_F_comparable`: two recorded finalized
  pairs, ordered by `finalizedChainE1`). Whichever is larger is carried by a record whose block
  is in the shared list and descends from it, so the acceptance lemma puts that block in the
  other fold too, and the fold-level Theorem 8 (`fold_record_F`) puts the other fold's `F` at or
  above it. Antisymmetry closes it. The paper argues through a maximum over the whole input set;
  taking the two stores' own `F`s avoids constructing that maximum.
* **`hmax`.** The maximum-height record either descends from `F` — then it is accepted on both
  sides and bounds both maxima — or it has passed `F`'s finalized height without containing it,
  which is healing's Lemma 10, or `F` itself attains the maximum by its own post-state anchor.
* **`J` and `h_j`.** No new work: `jProv` names a record carrying the store's justified pair, the
  record descends from `F` (Theorem 4 gives `F ⪯ J ⪯ L`), so it is accepted on both sides, and
  `keyDom` at each store bounds each key by the other. The keys are therefore equal.
* **`get_confirmed`.** Both branches of the cascade start at or above `F`, so a confirmed block
  is in the shared subtree; its viability witness is a leaf above it, hence also shared, and
  leafhood transfers because a proper descendant of a block above `F` is itself above `F`.

## The one assumption this theorem needs and the others do not

`[HashInjective Node Root]` — the paper's collision-freedom idealization, `Spec/Defs/Store.lean`.
It is used in exactly one place: turning `hash(Σ.J) = hash(Σ'.J)` into `Σ.J = Σ'.J`. Without it
the claim is false, and not by a slashable event: two distinct blocks justified at one height
with equal hashes leave `update_justified`'s tiebreak deciding by arrival order, and Definition 9
(`hft:def:slashing`) has no rule against two targets at one height — it is E1 and nothing else.
The paper identifies a block with its hash, so in its model the assumption is free.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

section Store
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

omit [DecidableEq Node] [DecidableEq Root] [Params] [BlockHash Node Root] in
theorem SlashableThirdAcross.symm {T T' : Finset (Blk Node Root)} (h : SlashableThirdAcross T T') :
    SlashableThirdAcross T' T := by
  obtain ⟨A, hw, hev⟩ := h
  refine ⟨A, hw, fun v hv => ?_⟩
  obtain ⟨a, b, ha, hb, hia, hib, he⟩ := hev v hv
  exact ⟨a, b, ha, hb, hia.symm, hib.symm, he⟩

/-! ## `hmax` -/

theorem hmax_le_of_agree [PositiveWeight Node] {S S' : Store Node Root}
    (hinv : StoreInv S) (hinv' : StoreInv S') (hgS : (Blk.genesis : Blk Node Root) ∈ S.T)
    (hsub : ∀ C, S.F ⪯ C → C ∈ S.T → C ∈ S'.T) :
    S.hmax ≤ S'.hmax ∨ SlashableThirdAcross S.T S'.T := by
  obtain ⟨Bm, σm, hBm, hhm⟩ := hinv.hmaxEx
  have hTm : Bm ∈ S.T := record_mem_T hinv hBm
  have hpm : postState Bm = .state σm := record_postState hinv hBm
  by_cases hFBm : S.F ⪯ Bm
  · left
    have hBm' : Bm ∈ S'.T := hsub Bm hFBm hTm
    obtain ⟨σm', hσm'⟩ := record_of_mem hinv' hBm'
    have hmm : σm = σm' := record_agree hinv hinv' hBm hσm'
    subst hmm
    rw [← hhm]
    exact hinv'.hmaxLe Bm σm hσm'
  rcases hinv.fProv with hg | ⟨E, σE, hE, hFE⟩
  · exact absurd (by rw [hg]; exact genesis_preceq _) hFBm
  have hne : postState E ≠ invalid := record_ne_invalid hinv hE
  have hps : postState' E hne = σE := record_postState' hinv hE hne
  have hTE : E ∈ S.T := record_mem_T hinv hE
  by_cases h1 : 1 ≤ σE.h_F
  · obtain ⟨-, -, hanc⟩ := (record_certified hinv hE).fin h1
    rw [hFE] at hanc
    obtain ⟨σF, hpF, hhF⟩ := TransitionResult.map_eq_some hanc
    by_cases hlt : σE.h_F < σm.h
    · right
      obtain ⟨A, hw, hev⟩ :=
        pastFinalized_evidence hne (by rw [hps]; exact hFE) (by rw [hps]) hpm h1 hlt hFBm
      refine ⟨A, hw, fun v hv => ?_⟩
      obtain ⟨a, b, hav, hbv, hai, hbi, he⟩ := hev v hv
      exact ⟨a, b, hav, hbv, Or.inl ⟨E, hTE, hai⟩, Or.inl ⟨Bm, hTm, hbi⟩, he⟩
    · left
      have hFT : S.F ∈ S.T := F_mem_T hinv hgS
      obtain ⟨σF2, hσF2⟩ := record_of_mem hinv hFT
      have e1 : σF2.h = σE.h_F := by
        have g1 := record_postState hinv hσF2
        rw [hpF] at g1
        injection g1 with g2
        rw [← g2]; exact hhF
      have hFT' : S.F ∈ S'.T := hsub S.F (Preceq.refl _) hFT
      obtain ⟨σF3, hσF3⟩ := record_of_mem hinv' hFT'
      have e2 : σF2 = σF3 := record_agree hinv hinv' hσF2 hσF3
      have hle2 : σF3.h ≤ S'.hmax := hinv'.hmaxLe _ _ hσF3
      rw [e2] at e1
      have hlt' : σm.h ≤ σE.h_F := Nat.le_of_not_lt hlt
      omega
  · exfalso
    have hFg : S.F = Blk.genesis := by
      rw [← hFE]; exact (record_certified hinv hE).fin0 (by omega)
    exact hFBm (by rw [hFg]; exact genesis_preceq _)

/-! ## The justification key -/

theorem key_le_of_agree {S S' : Store Node Root}
    (hinv : StoreInv S) (hinv' : StoreInv S') (hFJ : S.F ⪯ S.J) (hFeq : S.F = S'.F)
    (hsub : ∀ C, S.F ⪯ C → C ∈ S.T → C ∈ S'.T) :
    S.h_j < S'.h_j ∨ (S.h_j = S'.h_j ∧ hash(S.J) ≤ hash(S'.J)) := by
  obtain ⟨B₁, σ₁, hB₁, hJ₁, hh₁⟩ := hinv.jProv
  have hch₁ : Chained σ₁ := record_chained hinv hB₁
  have hL₁ : σ₁.L = B₁ := record_L hinv hB₁
  have hT₁ : B₁ ∈ S.T := record_mem_T hinv hB₁
  have hFB₁ : S.F ⪯ B₁ := by
    have g1 : S.F ⪯ σ₁.J := by rw [hJ₁]; exact hFJ
    have g2 : σ₁.J ⪯ B₁ := by rw [← hL₁]; exact hch₁.justLatest
    exact Preceq.trans g1 g2
  have hT₁' : B₁ ∈ S'.T := hsub B₁ hFB₁ hT₁
  obtain ⟨σ₁', hσ₁'⟩ := record_of_mem hinv' hT₁'
  have heq : σ₁ = σ₁' := record_agree hinv hinv' hB₁ hσ₁'
  subst heq
  have hcond : S'.F ⪯ σ₁.J := by rw [← hFeq, hJ₁]; exact hFJ
  have hkey := hinv'.keyDom B₁ σ₁ hσ₁' hcond
  rw [hJ₁, hh₁] at hkey
  exact hkey

/-! ## `get_confirmed` -/

theorem getConfirmed_sub {S S' : Store Node Root} (hinv : StoreInv S) (hinv' : StoreInv S')
    (hFeq : S.F = S'.F) (hJeq : S.J = S'.J) (hhj : S.h_j = S'.h_j) (hhmax : S.hmax = S'.hmax)
    (hFJ : S.F ⪯ S.J)
    (hsub : ∀ C, S.F ⪯ C → C ∈ S.T → C ∈ S'.T)
    (hsub' : ∀ C, S.F ⪯ C → C ∈ S'.T → C ∈ S.T)
    {C : Blk Node Root}
    (hC : (C ∈ viableTree S ∧ S.walkStart ⪯ C ∧ (get st from S.σ C; st.h ≥ S.hmax - 1))) :
    (C ∈ viableTree S' ∧ S'.walkStart ⪯ C ∧ (get st from S'.σ C; st.h ≥ S'.hmax - 1)) := by
  have hR : S.walkStart = S'.walkStart := by unfold Store.walkStart; rw [hFeq, hJeq, hhj, hhmax]
  have hFC : S.F ⪯ C := Preceq.trans (F_preceq_walkStart hFJ) hC.2.1
  obtain ⟨hCT, L, σL, hLT, hleaf, hCL, hσL, hh⟩ := viableTree_witness hC.1
  have hCT' : C ∈ S'.T := hsub C hFC hCT
  have hFL : S.F ⪯ L := Preceq.trans hFC hCL
  have hLT' : L ∈ S'.T := hsub L hFL hLT
  obtain ⟨σL', hσL'⟩ := record_of_mem hinv' hLT'
  have heqL : σL = σL' := record_agree hinv hinv' hσL hσL'
  subst heqL
  have hleaf' : ∀ D ∈ S'.T, ¬ L ≺ D := by
    intro D hD hlt
    exact hleaf D (hsub' D (Preceq.trans hFL hlt.1) hD) hlt
  refine ⟨mem_viableTree hCT' hLT' hleaf' hCL hσL' (by rw [← hhmax]; exact hh), ?_, ?_⟩
  · rw [← hR]; exact hC.2.1
  · obtain ⟨σC, hσC, hhC⟩ := hC.2.2
    have hσC' : S.σ C = some σC := hσC
    obtain ⟨σC2, hσC2⟩ := record_of_mem hinv' hCT'
    have hcc : σC = σC2 := record_agree hinv hinv' hσC' hσC2
    subst hcc
    exact ⟨σC, hσC2, by rw [← hhmax]; exact hhC⟩

theorem onBlocks_accept_all {Bs : List (Blk Node Root)} (hpf : ParentFirst Bs)
    {Fmax : Blk Node Root} (hFle : ∀ k : Nat, (onBlocks Store.gen (Bs.take k)).F ⪯ Fmax)
    {C : Blk Node Root} (hC : C ∈ Bs) (hval : postState C ≠ invalid)
    (hcomp : C ⪯ Fmax ∨ Fmax ⪯ C) : C ∈ (onBlocks Store.gen Bs).T := by
  have h := onBlocks_accept hpf hFle Bs.length C (by rw [List.take_length]; exact hC) hval hcomp
  rwa [List.take_length] at h

/-! ## The two finalized blocks are comparable -/

theorem fold_F_comparable [PositiveWeight Node] (Bs Bs' : List (Blk Node Root)) :
    (onBlocks Store.gen Bs).F ⪯ (onBlocks Store.gen Bs').F ∨
      (onBlocks Store.gen Bs').F ⪯ (onBlocks Store.gen Bs).F ∨
      SlashableThirdAcross (onBlocks Store.gen Bs).T (onBlocks Store.gen Bs').T := by
  have hinv : StoreInv (onBlocks Store.gen Bs) := storeInv_onBlocks storeInv_gen _
  have hinv' : StoreInv (onBlocks Store.gen Bs') := storeInv_onBlocks storeInv_gen _
  rcases hinv.fProv with hg | ⟨E, σE, hE, hFE⟩
  · exact Or.inl (by rw [hg]; exact genesis_preceq _)
  rcases hinv'.fProv with hg' | ⟨E', σE', hE', hFE'⟩
  · exact Or.inr (Or.inl (by rw [hg']; exact genesis_preceq _))
  have hne : postState E ≠ invalid := record_ne_invalid hinv hE
  have hne' : postState E' ≠ invalid := record_ne_invalid hinv' hE'
  have hps : postState' E hne = σE := record_postState' hinv hE hne
  have hps' : postState' E' hne' = σE' := record_postState' hinv' hE' hne'
  have hT : E ∈ (onBlocks Store.gen Bs).T := record_mem_T hinv hE
  have hT' : E' ∈ (onBlocks Store.gen Bs').T := record_mem_T hinv' hE'
  rcases Nat.le_total σE.h_F σE'.h_F with hle | hle
  · rcases finalizedChainE1 (C := σE.F) (h := σE.h_F) (C' := σE'.F) (h' := σE'.h_F)
        hne (by rw [hps]) (by rw [hps]) hne' (by rw [hps']) (by rw [hps']) hle with
      hpre | ⟨A, hw, hev⟩
    · exact Or.inl (by rw [← hFE, ← hFE']; exact hpre)
    · refine Or.inr (Or.inr ⟨A, hw, fun v hv => ?_⟩)
      obtain ⟨a, b, hav, hbv, hai, hbi, he⟩ := hev v hv
      exact ⟨a, b, hav, hbv, Or.inl ⟨E, hT, hai⟩, Or.inr ⟨E', hT', hbi⟩, he⟩
  · rcases finalizedChainE1 (C := σE'.F) (h := σE'.h_F) (C' := σE.F) (h' := σE.h_F)
        hne' (by rw [hps']) (by rw [hps']) hne (by rw [hps]) (by rw [hps]) hle with
      hpre | ⟨A, hw, hev⟩
    · exact Or.inr (Or.inl (by rw [← hFE, ← hFE']; exact hpre))
    · refine Or.inr (Or.inr ⟨A, hw, fun v hv => ?_⟩)
      obtain ⟨a, b, hav, hbv, hai, hbi, he⟩ := hev v hv
      exact ⟨a, b, hav, hbv, Or.inr ⟨E', hT', hai⟩, Or.inl ⟨E, hT, hbi⟩, he⟩

/-! ## The larger finalized block is reached in the other order too -/

theorem fold_F_ge [PositiveWeight Node] {Bs Bs' : List (Blk Node Root)}
    (hmem : ∀ C, C ∈ Bs' → C ∈ Bs) (hp : ParentFirst Bs)
    (hle : (onBlocks Store.gen Bs).F ⪯ (onBlocks Store.gen Bs').F) :
    (onBlocks Store.gen Bs').F ⪯ (onBlocks Store.gen Bs).F ∨
      SlashableThirdAcross (onBlocks Store.gen Bs).T (onBlocks Store.gen Bs').T := by
  have hinv : StoreInv (onBlocks Store.gen Bs) := storeInv_onBlocks storeInv_gen _
  have hinv' : StoreInv (onBlocks Store.gen Bs') := storeInv_onBlocks storeInv_gen _
  rcases hinv'.fProv with hg | ⟨E, σE, hE, hFE⟩
  · exact Or.inl (by rw [hg]; exact genesis_preceq _)
  have hET' : E ∈ (onBlocks Store.gen Bs').T := record_mem_T hinv' hE
  have hEval : postState E ≠ invalid := record_ne_invalid hinv' hE
  have hchE : Chained σE := record_chained hinv' hE
  have hLE : σE.L = E := record_L hinv' hE
  have hFmaxE : (onBlocks Store.gen Bs').F ⪯ E := by
    rw [← hFE, ← hLE]; exact Preceq.trans hchE.finJust hchE.justLatest
  by_cases hEg : E = Blk.genesis
  · left
    have h1 : postState (Blk.genesis : Blk Node Root) = .state σE := by
      rw [← hEg]; exact record_postState hinv' hE
    have h2 : (TransitionResult.state (ChainState.gen : ChainState Node Root)) = .state σE := h1
    injection h2 with h3
    rw [← hFE, ← h3]
    exact genesis_preceq _
  have hEBs : E ∈ Bs := by
    rcases onBlocks_T_sub Store.gen Bs' E hET' with hgen | hmem'
    · exact absurd (Finset.mem_singleton.1 hgen) hEg
    · exact hmem E hmem'
  have hFle : ∀ k : Nat,
      (onBlocks Store.gen (Bs.take k)).F ⪯ (onBlocks Store.gen Bs').F :=
    fun k => Preceq.trans (onBlocks_prefix_F Store.gen Bs k) hle
  have hacc : E ∈ (onBlocks Store.gen Bs).T :=
    onBlocks_accept_all hp hFle hEBs hEval (Or.inr hFmaxE)
  obtain ⟨σE2, hE2⟩ := record_of_mem hinv hacc
  have hσ : σE2 = σE := record_agree hinv hinv' hE2 hE
  subst hσ
  rcases fold_record_F Bs hE2 with hpre | hev
  · exact Or.inl (by rw [← hFE]; exact hpre)
  · exact Or.inr (SlashableThirdOn.toAcrossLeft (Or.inl hacc) hev)

theorem fold_F_eq [PositiveWeight Node] {Bs Bs' : List (Blk Node Root)} (hperm : Bs.Perm Bs')
    (hp : ParentFirst Bs) (hp' : ParentFirst Bs') :
    (onBlocks Store.gen Bs).F = (onBlocks Store.gen Bs').F ∨
      SlashableThirdAcross (onBlocks Store.gen Bs).T (onBlocks Store.gen Bs').T := by
  rcases fold_F_comparable Bs Bs' with h1 | h1 | hev
  · rcases fold_F_ge (fun C hC => hperm.mem_iff.2 hC) hp h1 with h2 | hev
    · exact Or.inl (Preceq.antisymm h1 h2)
    · exact Or.inr hev
  · rcases fold_F_ge (Bs := Bs') (Bs' := Bs) (fun C hC => hperm.mem_iff.1 hC) hp' h1 with h2 | hev
    · exact Or.inl (Preceq.antisymm h2 h1)
    · exact Or.inr hev.symm
  · exact Or.inr hev

/-! ## Order independence, at the fold -/

theorem foldOrderIndependence [PositiveWeight Node] [HashInjective Node Root]
    {Bs Bs' : List (Blk Node Root)} (hperm : Bs.Perm Bs')
    (hp : ParentFirst Bs) (hp' : ParentFirst Bs') :
    ((onBlocks Store.gen Bs).F = (onBlocks Store.gen Bs').F ∧
     (onBlocks Store.gen Bs).J = (onBlocks Store.gen Bs').J ∧
     (onBlocks Store.gen Bs).h_j = (onBlocks Store.gen Bs').h_j ∧
     (onBlocks Store.gen Bs).hmax = (onBlocks Store.gen Bs').hmax ∧
     (∀ C, (onBlocks Store.gen Bs).F ⪯ C →
        (C ∈ (onBlocks Store.gen Bs).T ↔ C ∈ (onBlocks Store.gen Bs').T)) ∧
     (∀ C, (C ∈ viableTree (onBlocks Store.gen Bs) ∧ (onBlocks Store.gen Bs).walkStart ⪯ C ∧
         (get st from (onBlocks Store.gen Bs).σ C;
           st.h ≥ (onBlocks Store.gen Bs).hmax - 1)) ↔
       (C ∈ viableTree (onBlocks Store.gen Bs') ∧ (onBlocks Store.gen Bs').walkStart ⪯ C ∧
         (get st from (onBlocks Store.gen Bs').σ C;
           st.h ≥ (onBlocks Store.gen Bs').hmax - 1)))) ∨
      SlashableThirdAcross (onBlocks Store.gen Bs).T (onBlocks Store.gen Bs').T := by
  rcases fold_F_eq hperm hp hp' with hFeq | hev
  case inr => exact Or.inr hev
  have hinv : StoreInv (onBlocks Store.gen Bs) := storeInv_onBlocks storeInv_gen _
  have hinv' : StoreInv (onBlocks Store.gen Bs') := storeInv_onBlocks storeInv_gen _
  have hFJ : (onBlocks Store.gen Bs).F ⪯ (onBlocks Store.gen Bs).J :=
    onBlocks_FJ Bs (Preceq.refl _)
  have hFJ' : (onBlocks Store.gen Bs').F ⪯ (onBlocks Store.gen Bs').J :=
    onBlocks_FJ Bs' (Preceq.refl _)
  have hgS : (Blk.genesis : Blk Node Root) ∈ (onBlocks Store.gen Bs).T := genesis_mem_onBlocks _
  have hgS' : (Blk.genesis : Blk Node Root) ∈ (onBlocks Store.gen Bs').T := genesis_mem_onBlocks _
  have hacc' : ∀ C ∈ Bs', postState C ≠ invalid →
      (C ⪯ (onBlocks Store.gen Bs).F ∨ (onBlocks Store.gen Bs).F ⪯ C) →
      C ∈ (onBlocks Store.gen Bs').T := by
    intro C hC hval hcomp
    refine onBlocks_accept_all hp' (fun k => onBlocks_prefix_F Store.gen Bs' k) hC hval ?_
    rw [← hFeq]; exact hcomp
  have hacc : ∀ C ∈ Bs, postState C ≠ invalid →
      (C ⪯ (onBlocks Store.gen Bs).F ∨ (onBlocks Store.gen Bs).F ⪯ C) →
      C ∈ (onBlocks Store.gen Bs).T := fun C hC hval hcomp =>
    onBlocks_accept_all hp (fun k => onBlocks_prefix_F Store.gen Bs k) hC hval hcomp
  have hsub : ∀ C, (onBlocks Store.gen Bs).F ⪯ C → C ∈ (onBlocks Store.gen Bs).T →
      C ∈ (onBlocks Store.gen Bs').T := by
    intro C hFC hCT
    rcases onBlocks_T_sub Store.gen Bs C hCT with hg | hb
    · have hCg : C = Blk.genesis := Finset.mem_singleton.1 hg
      rw [hCg]; exact hgS'
    · obtain ⟨σC, hσC⟩ := record_of_mem hinv hCT
      exact hacc' C (hperm.mem_iff.1 hb) (record_ne_invalid hinv hσC) (Or.inr hFC)
  have hsub' : ∀ C, (onBlocks Store.gen Bs).F ⪯ C → C ∈ (onBlocks Store.gen Bs').T →
      C ∈ (onBlocks Store.gen Bs).T := by
    intro C hFC hCT
    rcases onBlocks_T_sub Store.gen Bs' C hCT with hg | hb
    · have hCg : C = Blk.genesis := Finset.mem_singleton.1 hg
      rw [hCg]; exact hgS
    · obtain ⟨σC, hσC⟩ := record_of_mem hinv' hCT
      exact hacc C (hperm.mem_iff.2 hb) (record_ne_invalid hinv' hσC) (Or.inr hFC)
  have hsub'F : ∀ C, (onBlocks Store.gen Bs').F ⪯ C → C ∈ (onBlocks Store.gen Bs').T →
      C ∈ (onBlocks Store.gen Bs).T := by
    intro C hFC hCT
    exact hsub' C (by rw [hFeq]; exact hFC) hCT
  rcases hmax_le_of_agree hinv hinv' hgS hsub with hle | hev
  case inr => exact Or.inr hev
  rcases hmax_le_of_agree hinv' hinv hgS' hsub'F with hle' | hev
  case inr => exact Or.inr hev.symm
  have hhmax : (onBlocks Store.gen Bs).hmax = (onBlocks Store.gen Bs').hmax := by omega
  have hk1 := key_le_of_agree hinv hinv' hFJ hFeq hsub
  have hk2 := key_le_of_agree hinv' hinv hFJ' hFeq.symm hsub'F
  have hhj : (onBlocks Store.gen Bs).h_j = (onBlocks Store.gen Bs').h_j := by
    rcases hk1 with a | ⟨a, -⟩ <;> rcases hk2 with b | ⟨b, -⟩ <;> omega
  have hJeq : (onBlocks Store.gen Bs).J = (onBlocks Store.gen Bs').J := by
    refine HashInjective.inj _ _ (Nat.le_antisymm ?_ ?_)
    · rcases hk1 with a | ⟨-, a⟩
      · omega
      · exact a
    · rcases hk2 with b | ⟨-, b⟩
      · omega
      · exact b
  refine Or.inl ⟨hFeq, hJeq, hhj, hhmax, fun C hFC => ⟨hsub C hFC, hsub' C hFC⟩,
    fun C => ⟨?_, ?_⟩⟩
  · exact getConfirmed_sub hinv hinv' hFeq hJeq hhj hhmax hFJ hsub hsub'
  · exact getConfirmed_sub hinv' hinv hFeq.symm hJeq.symm hhj.symm hhmax.symm hFJ' hsub'F
      (fun C hFC hCT => hsub C (by rw [hFeq]; exact hFC) hCT)

end Store

/-! ## The execution layer -/

section Exec
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-- **Theorem 10 (`hft:thm:orderindep`)'s content.** The fold-level theorem, read at two
    validators of one execution through `storeAt_eq_fold`. -/
theorem orderIndependence [PositiveWeight Node] [HashInjective Node Root]
    [Omega Node Root]
    {sched : Schedule Node} {x : Exec (protocol (Node := Node) (Root := Root)) sched}
    {p p' : Node} {i j : Nat}
    (hperm : (deliveredBlocks x p i).Perm (deliveredBlocks x p' j))
    (hp : ParentFirst (deliveredBlocks x p i))
    (hp' : ParentFirst (deliveredBlocks x p' j)) :
    ((storeAt x p i).F = (storeAt x p' j).F ∧
     (storeAt x p i).J = (storeAt x p' j).J ∧
     (storeAt x p i).h_j = (storeAt x p' j).h_j ∧
     (storeAt x p i).hmax = (storeAt x p' j).hmax ∧
     (∀ C, (storeAt x p i).F ⪯ C → (C ∈ (storeAt x p i).T ↔ C ∈ (storeAt x p' j).T)) ∧
     getConfirmed (storeAt x p i) = getConfirmed (storeAt x p' j)) ∨
      SlashableThird (fun a =>
        IncludedOnSome a (storeAt x p i).T ∨ IncludedOnSome a (storeAt x p' j).T) := by
  rw [storeAt_eq_fold x p i, storeAt_eq_fold x p' j]
  refine (foldOrderIndependence hperm hp hp').imp (fun hc => ?_) id
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
  have hR : (onBlocks Store.gen (deliveredBlocks x p i)).walkStart
      = (onBlocks Store.gen (deliveredBlocks x p' j)).walkStart := by
    unfold Store.walkStart
    rw [h1, h2, h3, h4]
  exact ⟨h1, h2, h3, h4, h5, getConfirmed_congr hR h6⟩

end Exec

end Proofs

end Decoupled
