import Analysis.Proofs.StoreRecords

/-!
# The accountable disjunct at a store, and the upgrade argument

Two things live here.

**The disjunct, named.** `RetainedOn` and `SlashableSet` are the shape the companion paper's
conditional results all conclude with: a set of validators of weight at least `2q − W`, each
with two signed attestations forming an E1 pair, and each attestation retained somewhere the
theorem can name — on the chain that finalized the block the theorem is about, or on a chain
the store accepted. Definition 9 (`hft:def:slashing`) is the single rule E1 and has no E2,
which is why `SlashableSet` names E1 alone; `finalizedChainE1`
(`Analysis/Proofs/Finality.lean`) is the healing result restated to match.

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

/-- Where the companion paper's theorems allow a retained attestation to sit: on the chain
    whose replay finalized the block in question, or on a chain the store accepted. Both arms
    are things a statement about one store can name, which is the point — an attestation the
    proof can only place "somewhere in the past" would make the disjunct unusable. -/
def RetainedOn (S : Store Node Root) (B_F : Blk Node Root) (a : Attestation Node Root) : Prop :=
  IncludedOn a B_F ∨ ∃ C ∈ S.T, IncludedOn a C

/-- "Unless `≥ n/3` validators are slashable", at one store: a set of weight at least `2q − W`
    — the weight two `q`-quorums must share (Lemma 2, `lem:quorum-intersection`), the count
    analogue of `n/3` — each of whose members signed an E1 pair, both messages retained.
    Definition 9 (`hft:def:slashing`) is E1 and nothing else. -/
def SlashableSet (S : Store Node Root) (B_F : Blk Node Root) : Prop :=
  ∃ A : Finset Node, w(A) ≥ 2 * q Node - W Node ∧
    ∀ v ∈ A, ∃ a b : Attestation Node Root, a.validator = v ∧ b.validator = v ∧
      RetainedOn S B_F a ∧ RetainedOn S B_F b ∧ E1 a b

omit [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params] [BlockHash Node Root] in
/-- Retention survives a growing tree, so it survives `ReachesFrom` (`reachesFrom_T`). -/
theorem RetainedOn.mono {S S' : Store Node Root} {B_F : Blk Node Root}
    {a : Attestation Node Root} (hT : S.T ⊆ S'.T) (h : RetainedOn S B_F a) :
    RetainedOn S' B_F a := by
  rcases h with h | ⟨C, hC, ha⟩
  · exact Or.inl h
  · exact Or.inr ⟨C, hT hC, ha⟩

omit [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params] [BlockHash Node Root] in
/-- The usual way one is built: the attestation sits on an accepted chain. -/
theorem RetainedOn.ofChain {S : Store Node Root} {B_F C : Blk Node Root}
    {a : Attestation Node Root} (hC : C ∈ S.T) (ha : IncludedOn a C) : RetainedOn S B_F a :=
  Or.inr ⟨C, hC, ha⟩

omit [DecidableEq Node] [DecidableEq Root] [Params] [BlockHash Node Root] in
/-- The set survives a growing tree. -/
theorem SlashableSet.mono {S S' : Store Node Root} {B_F : Blk Node Root}
    (hT : S.T ⊆ S'.T) (h : SlashableSet S B_F) : SlashableSet S' B_F := by
  obtain ⟨A, hw, hev⟩ := h
  refine ⟨A, hw, fun v hv => ?_⟩
  obtain ⟨a, b, ha, hb, hra, hrb, he⟩ := hev v hv
  exact ⟨a, b, ha, hb, hra.mono hT, hrb.mono hT, he⟩

omit [DecidableEq Node] [DecidableEq Root] [Params] [BlockHash Node Root] in
/-- When the finalizing chain is itself a block the store accepted, the two arms of every
    `RetainedOn` collapse into one. This is the shape Theorem 8 (`hft:thm:finlive`) states,
    where the finalized pair comes from a record and so has no chain of its own to name. -/
theorem SlashableSet.onTree {S : Store Node Root} {B_F : Blk Node Root} (hBF : B_F ∈ S.T)
    (h : SlashableSet S B_F) :
    ∃ A : Finset Node, w(A) ≥ 2 * q Node - W Node ∧
      ∀ v ∈ A, ∃ a b : Attestation Node Root, a.validator = v ∧ b.validator = v ∧
        (∃ Ca ∈ S.T, IncludedOn a Ca) ∧ (∃ Cb ∈ S.T, IncludedOn b Cb) ∧ E1 a b := by
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
    F ⪯ σ₁.J ∨ SlashableSet S B_F := by
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
            RetainedOn.ofChain hT₁ hbi, ?_⟩
          exact ⟨h_f, F, hap, Or.inl ⟨σ₁.J, hbp, hJFeq⟩⟩
  · -- `F` off the record's chain, past its finalized height, is the evidence
    right
    obtain ⟨A, hw, hev⟩ := pastFinalized_evidence hBF hF hhF hpost₁ h1 hlt hFB₁
    refine ⟨A, hw, fun v hv => ?_⟩
    obtain ⟨a, b, hav, hbv, hai, hbi, he⟩ := hev v hv
    exact ⟨a, b, hav, hbv, Or.inl hai, RetainedOn.ofChain hT₁ hbi, he⟩

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
    F ⪯ S.J ∨ SlashableSet S B_F := by
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
        exact ⟨a, b, hav, hbv, Or.inl hai, RetainedOn.ofChain hT₀ hbi, he⟩
    · rcases finalizedChainE1 hne₀ hF₀' hhF₀' hBF hF hhF hle with hpre | ⟨A, hw, hev⟩
      · exact absurd hpre hSF
      · refine Or.inr ⟨A, hw, fun v hv => ?_⟩
        obtain ⟨a, b, hav, hbv, hai, hbi, he⟩ := hev v hv
        exact ⟨a, b, hav, hbv, RetainedOn.ofChain hT₀ hai, Or.inl hbi, he⟩

end Store

end Proofs

end Decoupled
