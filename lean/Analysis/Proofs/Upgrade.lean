import Analysis.Proofs.StoreRecords

/-!
# The accountable disjunct at a store, and the upgrade argument

Two things live here.

**The disjunct, at a store.** `Slashable` (`Analysis/Vocabulary.lean`) is the accountable
disjunct itself, parameterized by where each of a signer's two messages may sit.
`IncludedInOrOn` is the inclusion predicate the store-level results want — in the accepted
tree, or on the chain that finalized the block in question — and `SlashableSet` is `Slashable`
at that predicate, so the proofs have one name for the shape they build over and over.
Definition 9 (`hft:def:slashing`) is the single rule E1 and has no E2, which is why
`Slashable` names E1 alone; `finalizedChainE1` (`Analysis/Proofs/Finality.lean`) is the
healing result restated to match.

**The upgrade argument.** Lemma 9 (`hft:lem:upgrade`): a block whose recorded state justifies a
finalized `F` at that block's finalized height puts the store root at or below `F`'s chain, or
exposes a slashable set. Its own dependency, Lemma 8 (`hft:lem:certchain`), is `certChain` here.

## What replaces the paper's history

The paper's proof names `F⁰ ≔ Σ.F` **at the moment `on_block(B)` offered `(F, h_f)` to
`update_justified`** and then carries the key forward by Lemma 6 (`hft:lem:Rs-key-monotone`).
This proof names no moment: `StoreInv`'s `keyDom` field is that conclusion made a state
invariant — every recorded justified pair on the *current* `F`'s chain has key at most the
store's — which is sound because `F` only ascends, so the condition only narrows. So the case
split is on the current store's `F`, not on a historical one:

* `S.F ⪯ F`: `keyDom` at the record gives `h_f ≤ S.h_j`, and `certChain` at the record `jProv`
  names does the rest.
* `¬ S.F ⪯ F`: `fProv` makes `S.F` genesis — impossible, genesis precedes everything — or some
  recorded state's finalized block, and then `finalizedChainE1` orders the two finalized pairs
  or produces the evidence.

`certChain` itself is the paper's Lemma 8 with the record standing in for "a justification
`(C, h)` has fired on any chain processed by the node": a recorded state *is* a fired
justification, since the justification branch is the only writer of `(J, h_j)`. Its three cases
are the paper's — height `0` is genesis by stipulation, a strictly higher store key is settled
by the two post-state anchors and height monotonicity, and equal heights by intersecting the
finalized block's commit quorum with the justified block's target quorum. It concludes `F ⪯ C`
where the paper concludes compatibility plus `F ≺ C` at `h > h_f`; the strict half is not
needed and is not proved.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

section Store
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-! ## The disjunct -/

/-- Where the companion paper's theorems allow an attestation to sit: on some chain in the
    accepted tree `T`, or on the chain `B_F` whose replay finalized the block in question —
    hence the name, "included in `T` or on `B_F`". Both arms are things a statement about one
    store can name, which is the point: an attestation the proof can only place "somewhere in
    the past" would make the disjunct unusable.

    Over a `Finset` rather than a `Store` because the tree is all these lemmas read of a store,
    and because the intermediate stores inside `on_block`'s accept branch are record literals
    whose `T` is `S.T ∪ {B}`: naming the set keeps those out of the statements. -/
def IncludedInOrOn (T : Finset (Blk Node Root)) (B_F : Blk Node Root)
    (a : Attestation Node Root) : Prop :=
  IncludedOn a B_F ∨ IncludedIn T a

/-- `Slashable` at the store-level retention predicate: the shape every conditional result
    under `Analysis/Proofs/` concludes with. -/
def SlashableSet (T : Finset (Blk Node Root)) (B_F : Blk Node Root) : Prop :=
  Slashable (IncludedInOrOn T B_F)

omit [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params] [BlockHash Node Root] in
/-- Inclusion survives a growing tree, so it survives `ReachesFrom` (`reachesFrom_T`). -/
theorem IncludedInOrOn.mono {T T' : Finset (Blk Node Root)} {B_F : Blk Node Root}
    {a : Attestation Node Root} (hT : T ⊆ T') (h : IncludedInOrOn T B_F a) :
    IncludedInOrOn T' B_F a := by
  rcases h with h | ⟨C, hC, ha⟩
  · exact Or.inl h
  · exact Or.inr ⟨C, hT hC, ha⟩

omit [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params] [BlockHash Node Root] in
/-- The usual way one is built: the attestation sits on an accepted chain. -/
theorem IncludedInOrOn.ofChain {T : Finset (Blk Node Root)} {B_F C : Blk Node Root}
    {a : Attestation Node Root} (hC : C ∈ T) (ha : IncludedOn a C) : IncludedInOrOn T B_F a :=
  Or.inr ⟨C, hC, ha⟩

omit [Electorate Node] [Params] [BlockHash Node Root] in
/-- The named chain adds nothing to the tree: retention against a tree with the named block
    thrown in is retention against the tree. This is what brings evidence found inside
    `on_block`'s accept branch, where the tree is already `S.T ∪ {B}`, back to the store the
    call started from. -/
theorem IncludedInOrOn.ofUnion {T : Finset (Blk Node Root)} {B_F : Blk Node Root}
    {a : Attestation Node Root} (h : IncludedInOrOn (T ∪ {B_F}) B_F a) : IncludedInOrOn T B_F a := by
  rcases h with h | ⟨C, hC, ha⟩
  · exact Or.inl h
  · rw [Finset.mem_union, Finset.mem_singleton] at hC
    rcases hC with hC | rfl
    · exact Or.inr ⟨C, hC, ha⟩
    · exact Or.inl ha

omit [DecidableEq Node] [DecidableEq Root] [Params] [BlockHash Node Root] in
/-- The set survives a growing tree. -/
theorem SlashableSet.mono {T T' : Finset (Blk Node Root)} {B_F : Blk Node Root}
    (hT : T ⊆ T') (h : SlashableSet T B_F) : SlashableSet T' B_F := by
  obtain ⟨A, hw, hev⟩ := h
  refine ⟨A, hw, fun v hv => ?_⟩
  obtain ⟨a, b, ha, hb, hra, hrb, he⟩ := hev v hv
  exact ⟨a, b, ha, hb, hra.mono hT, hrb.mono hT, he⟩

omit [Params] [BlockHash Node Root] in
/-- `IncludedInOrOn.ofUnion`, for a whole set. -/
theorem SlashableSet.ofUnion {T : Finset (Blk Node Root)} {B_F : Blk Node Root}
    (h : SlashableSet (T ∪ {B_F}) B_F) : SlashableSet T B_F := by
  obtain ⟨A, hw, hev⟩ := h
  refine ⟨A, hw, fun v hv => ?_⟩
  obtain ⟨a, b, ha, hb, hra, hrb, he⟩ := hev v hv
  exact ⟨a, b, ha, hb, hra.ofUnion, hrb.ofUnion, he⟩

omit [DecidableEq Node] [DecidableEq Root] [Params] [BlockHash Node Root] in
/-- When the finalizing chain is itself a block the store accepted, the two arms of every
    `IncludedInOrOn` collapse into one. This is the shape Theorem 8 (`hft:thm:finlive`) states,
    where the finalized pair comes from a record and so has no chain of its own to name. -/
theorem SlashableSet.onTree {T : Finset (Blk Node Root)} {B_F : Blk Node Root} (hBF : B_F ∈ T)
    (h : SlashableSet T B_F) : Slashable (IncludedIn T) := by
  obtain ⟨A, hw, hev⟩ := h
  refine ⟨A, hw, fun v hv => ?_⟩
  obtain ⟨a, b, ha, hb, hra, hrb, he⟩ := hev v hv
  refine ⟨a, b, ha, hb, ?_, ?_, he⟩
  · rcases hra with h1 | h1
    · exact ⟨B_F, hBF, h1⟩
    · exact h1
  · rcases hrb with h1 | h1
    · exact ⟨B_F, hBF, h1⟩
    · exact h1

/-! ## Lemma 8 (`hft:lem:certchain`), over a record -/

/-- Lemma 8 (`hft:lem:certchain`)'s content, over a record. Read aloud: if a block the store
    accepted has a replayed state whose justified pair sits at or above the height at which
    some chain finalized `F`, then `F` is an ancestor of that justified block — or a slashable
    set of weight `2q − W` is exhibited.

    The paper's "a justification `(C, h)` has fired on any chain processed by the node" is the
    record: the justification branch of the height-event check is the only writer of
    `(J, h_j)`, so a recorded state carrying `(C, h)` *is* that firing, and the store's own map
    is what says the chain was processed. The paper concludes compatibility, strengthened to
    `F ≺ C` when `h > h_f`; this concludes `F ⪯ C` in every case, which is what Lemma 9 and
    Theorem 8 read from it.

    Three cases, the paper's. At `h_f = 0` the finalized block is genesis by stipulation
    (`Certified.fin0`) and precedes everything. Otherwise healing's Lemma 10
    (`lem:past-finalized`, the companion paper's Lemma 4, `hft:lem:mainsafety`) puts `F` on the
    record's own chain or produces the evidence; the justified block is on that chain too
    (`Chained.justLatest`), so the two are comparable, and the wrong order is refused by the
    two post-state anchors plus height monotonicity when the heights differ, and by
    intersecting the commit quorum for `(h_f, F)` with the target quorum for the record's pair
    when they agree. -/
theorem certChain [PositiveWeight Node] {S : Store Node Root} (hinv : StoreInv S)
    {B_F F : Blk Node Root} {h_f : Nat}
    (hBF : postState B_F ≠ invalid)
    (hF : (postState' B_F).F = F) (hhF : (postState' B_F).h_F = h_f)
    {B₁ : Blk Node Root} {σ₁ : ChainState Node Root} (hB₁ : S.σ B₁ = some σ₁)
    (hle : h_f ≤ σ₁.h_j) :
    F ⪯ σ₁.J ∨ SlashableSet S.T B_F := by
  -- the finalizing chain
  have hσF : postState B_F = .state (postState' B_F) := TransitionResult.state_get _ hBF
  have hbpF : BlockPostState (postState' B_F) := blockPostState_of_postState B_F hσF
  have hLF : (postState' B_F).L = B_F := postState_L B_F hσF
  have hcertF := certified_of_blockPostState hbpF
  -- the record
  have hpost₁ : postState B₁ = .state σ₁ := record_postState hinv hB₁
  have hL₁ : σ₁.L = B₁ := record_L hinv hB₁
  have hch₁ : Chained σ₁ := record_chained hinv hB₁
  have hcert₁ : Certified σ₁ := record_certified hinv hB₁
  have hT₁ : B₁ ∈ S.T := record_mem_T hinv hB₁
  by_cases h0 : h_f = 0
  · left
    have hg : (postState' B_F).F = .genesis := hcertF.fin0 (by rw [hhF, h0])
    rw [← hF, hg]
    exact genesis_preceq _
  have h1 : 1 ≤ h_f := Nat.one_le_iff_ne_zero.mpr h0
  have h1j : 1 ≤ σ₁.h_j := le_trans h1 hle
  have hlt : h_f < σ₁.h := lt_of_le_of_lt hle hch₁.hj_lt_h
  by_cases hFB₁ : F ⪯ B₁
  · have hJB₁ : σ₁.J ⪯ B₁ := by rw [← hL₁]; exact hch₁.justLatest
    rcases preceq_or_preceq B₁ hFB₁ hJB₁ with hFJ | hJF
    · exact Or.inl hFJ
    · -- the justified block at or below `F`
      rcases Nat.lt_or_ge h_f σ₁.h_j with hlt' | hge
      · -- a strictly higher justified height cannot sit below the finalized block
        exfalso
        obtain ⟨-, -, hancF⟩ := hcertF.fin (by rw [hhF]; exact h1)
        rw [hF, hhF] at hancF
        obtain ⟨-, hanc₁⟩ := hcert₁.just h1j
        obtain ⟨σF, hpF, hhF'⟩ := TransitionResult.map_eq_some hancF
        obtain ⟨σJ, hpJ, hhJ⟩ := TransitionResult.map_eq_some hanc₁
        have := postState_h_le F hJF hpJ hpF
        omega
      · -- equal heights: the two quorums intersect, and every signer is E1 unless they agree
        have heq : σ₁.h_j = h_f := le_antisymm hge hle
        by_cases hJFeq : σ₁.J = F
        · exact Or.inl (by rw [hJFeq]; exact Preceq.refl _)
        · right
          obtain ⟨⟨Qc, hQcV, hQcw, hQca⟩, -, -⟩ := hcertF.fin (by rw [hhF]; exact h1)
          obtain ⟨⟨Qt, hQtV, hQtw, hQta⟩, -⟩ := hcert₁.just h1j
          refine ⟨Qc ∩ Qt, quorumIntersection hQcV hQtV hQcw hQtw, fun v hv => ?_⟩
          obtain ⟨a, hav, hap, hai⟩ := hQca v (Finset.mem_inter.1 hv).1
          obtain ⟨b, hbv, hbp, hbi⟩ := hQta v (Finset.mem_inter.1 hv).2
          rw [hhF, hF] at hap
          rw [hL₁] at hbi
          rw [heq] at hbp
          refine ⟨a, b, hav, hbv, Or.inl (by rwa [hLF] at hai),
            IncludedInOrOn.ofChain hT₁ hbi, ?_⟩
          exact ⟨h_f, F, hap, Or.inl ⟨σ₁.J, hbp, hJFeq⟩⟩
  · -- `F` off the record's chain, past its finalized height, is the evidence
    right
    obtain ⟨A, hw, hev⟩ := pastFinalized_evidence hBF hF hhF hpost₁ h1 hlt hFB₁
    refine ⟨A, hw, fun v hv => ?_⟩
    obtain ⟨a, b, hav, hbv, hai, hbi, he⟩ := hev v hv
    exact ⟨a, b, hav, hbv, Or.inl hai, IncludedInOrOn.ofChain hT₁ hbi, he⟩

/-! ## Lemma 9 (`hft:lem:upgrade`), at one store -/

/-- Lemma 9 (`hft:lem:upgrade`)'s content, at one store. Read aloud: if some chain finalized
    `F` at height `h_f` and the store holds a recorded state whose justified pair is exactly
    `(F, h_f)`, then the store root is `F` or a descendant of it — or a slashable set of weight
    `2q − W` is exhibited.

    The paper's "at all future times" is not here: this is the claim at *one* store, and the
    future is reached by re-applying it at the later store, where the record still exists by
    `reachesFrom_record`. Chasing `S.J` across steps instead would not work — `J` is not
    `⪯`-monotone, since `update_justified` compares keys and not ancestry.

    See the module docstring for the two cases and for what `keyDom` replaces. -/
theorem upgrade [PositiveWeight Node] {S : Store Node Root} (hinv : StoreInv S)
    (hFJ : S.F ⪯ S.J) {B_F F : Blk Node Root} {h_f : Nat}
    (hBF : postState B_F ≠ invalid)
    (hF : (postState' B_F).F = F) (hhF : (postState' B_F).h_F = h_f)
    {B : Blk Node Root} {σB : ChainState Node Root} (hB : S.σ B = some σB)
    (hJ : σB.J = F) (hhj : σB.h_j = h_f) :
    F ⪯ S.J ∨ SlashableSet S.T B_F := by
  by_cases hSF : S.F ⪯ F
  · -- the `F`-filter passes, so `keyDom` bounds `h_f` by the store's key height
    have hkey := hinv.keyDom B σB hB (by rw [hJ]; exact hSF)
    have hle : h_f ≤ S.h_j := by
      rcases hkey with h | ⟨h, -⟩ <;> omega
    obtain ⟨B₁, σ₁, hB₁, hJ₁, hh₁⟩ := hinv.jProv
    rcases certChain hinv hBF hF hhF hB₁ (by rw [hh₁]; exact hle) with hpre | hev
    · exact Or.inl (by rwa [hJ₁] at hpre)
    · exact Or.inr hev
  · -- `S.F` is genesis, which precedes everything, or finalized on a chain the store recorded
    rcases hinv.fProv with hgen | ⟨B₀, σ₀, hB₀, hF₀⟩
    · exact absurd (by rw [hgen]; exact genesis_preceq F) hSF
    have hne₀ : postState B₀ ≠ invalid := record_ne_invalid hinv hB₀
    have hps₀ : postState' B₀ hne₀ = σ₀ := record_postState' hinv hB₀ hne₀
    have hF₀' : (postState' B₀ hne₀).F = S.F := by rw [hps₀]; exact hF₀
    have hhF₀' : (postState' B₀ hne₀).h_F = σ₀.h_F := by rw [hps₀]
    have hT₀ : B₀ ∈ S.T := record_mem_T hinv hB₀
    rcases Nat.le_total h_f σ₀.h_F with hle | hle
    · rcases finalizedChainE1 hBF hF hhF hne₀ hF₀' hhF₀' hle with hpre | ⟨A, hw, hev⟩
      · exact Or.inl (Preceq.trans hpre hFJ)
      · refine Or.inr ⟨A, hw, fun v hv => ?_⟩
        obtain ⟨a, b, hav, hbv, hai, hbi, he⟩ := hev v hv
        exact ⟨a, b, hav, hbv, Or.inl hai, IncludedInOrOn.ofChain hT₀ hbi, he⟩
    · rcases finalizedChainE1 hne₀ hF₀' hhF₀' hBF hF hhF hle with hpre | ⟨A, hw, hev⟩
      · exact absurd hpre hSF
      · refine Or.inr ⟨A, hw, fun v hv => ?_⟩
        obtain ⟨a, b, hav, hbv, hai, hbi, he⟩ := hev v hv
        exact ⟨a, b, hav, hbv, IncludedInOrOn.ofChain hT₀ hai, Or.inl hbi, he⟩

end Store

end Proofs

end Decoupled
