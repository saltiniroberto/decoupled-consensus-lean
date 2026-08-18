import Analysis.Proofs.Determinism
import Analysis.Proofs.StoreInvariants

/-!
# `StoreInv`: every store field traces to a recorded replay

The invariant bundle Theorems 8–10 stand on, preserved as one structure so a single
walker application carries all of it. The fields, and which paper fact each renders:

* `recorded` — every recorded state is its block's replay (`postState`). The bridge of
  `StoreInvariants.lean`, carried here as a field because the other fields' preservation
  needs it mid-proof: an overwrite writes the same value (`update_keeps`), and the newly
  recorded state is a `BlockPostState`, so the healing paper's `Chained` applies to it.
* `domT`, `parentT` — the tree is exactly the map's domain, and is parent-closed. The
  companion paper's Definition 10 (`hft:def:store`) says both in prose.
* `jProv` — some recorded state carries `(S.J, S.h_j)` as its justified pair: the store
  root is never invented. With `recorded`, this is what hands the healing certificate
  machinery the store's justification.
* `fProv` — `S.F` is genesis or some recorded state's `F`: the first sentence of the
  companion paper's Remark 5 (`hft:rem:fs-invariant`).
* `keyDom` — the remark's second half, made a state invariant instead of a history fact:
  every recorded justified pair **on the current `F`'s chain** has key at most the
  store's. The paper phrases this as "was offered to `update_justified` once
  `J* ⪰ Σ.F` at the moment of offering"; quantifying over recorded states whose `J`
  descends from the *current* `F` avoids the history because `F` only ascends, so the
  condition only ever narrows.
* `hmaxLe`/`hmaxEx` — `hmax` is exactly the maximum recorded state-height, Definition 10's
  own description of the field.

Preservation routes each of `on_block`'s two updates through a `spec` lemma — the record
equation stating exactly what fired and what the store became (the positive shape the
`lean-proof-idioms` skill recommends) — and the four resulting cases differ only in the
three provenance fields. The one interesting case is `keyDom` when finalization fired and
justification did not: the new `F` sits under the new record's own `J` by the healing
paper's `Chained`, so the justification's condition can only have failed on the key
comparison, which is what the conclusion needs.
-/

set_option autoImplicit false


namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

section Store
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-- Every store field traces to a recorded replay. -/
structure StoreInv (S : Store Node Root) : Prop where
  recorded : ∀ B σB, S.σ B = some σB → postState B = .state σB
  domT : ∀ B, B ∈ S.T ↔ (S.σ B).isSome
  parentT : ∀ B ∈ S.T, ∀ P, B.parent = some P → P ∈ S.T
  jProv : ∃ B σB, S.σ B = some σB ∧ σB.J = S.J ∧ σB.h_j = S.h_j
  fProv : S.F = .genesis ∨ ∃ B σB, S.σ B = some σB ∧ σB.F = S.F
  keyDom : ∀ B σB, S.σ B = some σB → S.F ⪯ σB.J →
    σB.h_j < S.h_j ∨ (σB.h_j = S.h_j ∧ hash(σB.J) ≤ hash(S.J))
  hmaxLe : ∀ B σB, S.σ B = some σB → σB.h ≤ S.hmax
  hmaxEx : ∃ B σB, S.σ B = some σB ∧ σB.h = S.hmax

omit [Electorate Node] [Params] in
theorem updateJustified_spec (S : Store Node Root) (J' : Blk Node Root) (h' : Nat) :
    (S.F ⪯ J' ∧ (S.h_j < h' ∨ (h' = S.h_j ∧ hash(S.J) < hash(J'))) ∧
      updateJustified S J' h' = { S with J := J', h_j := h' }) ∨
    (¬(S.F ⪯ J' ∧ (S.h_j < h' ∨ (h' = S.h_j ∧ hash(S.J) < hash(J')))) ∧
      updateJustified S J' h' = S) := by
  simp only [updateJustified, Id.run]
  split_ifs with hc
  · exact Or.inl ⟨hc.1, hc.2, rfl⟩
  · exact Or.inr ⟨hc, rfl⟩

omit [Electorate Node] [Params] [BlockHash Node Root] in
theorem updateFinalized_spec (S : Store Node Root) (F' : Blk Node Root) :
    (S.F ≺ F' ∧ F' ⪯ S.J ∧ F' ∈ viableTree S ∧
      updateFinalized S F' = { S with F := F' }) ∨
    (¬(S.F ≺ F' ∧ F' ⪯ S.J ∧ F' ∈ viableTree S) ∧ updateFinalized S F' = S) := by
  simp only [updateFinalized, Id.run]
  split_ifs with hc
  · exact Or.inl ⟨hc.1, hc.2.1, hc.2.2, rfl⟩
  · exact Or.inr ⟨hc, rfl⟩

omit [BlockHash Node Root] in
/-- The core of the recorded-replay bridge, factored: a successful `Store.replay` on a
    store whose records are replays is itself the block's replay. -/
theorem replay_postState {S : Store Node Root}
    (h : ∀ B σB, S.σ B = some σB → postState B = .state σB)
    {B' : Blk Node Root} {σ' : ChainState Node Root}
    (hrep : S.replay B' = .state σ') : postState B' = .state σ' := by
  simp only [Store.replay] at hrep
  split at hrep
  · rename_i σP hbind
    cases hOpt : B'.parent with
    | none => rw [hOpt] at hbind; exact absurd hbind (by simp)
    | some P =>
        rw [hOpt] at hbind
        have hσP : S.σ P = some σP := hbind
        cases B' with
        | genesis => exact absurd hOpt (by simp [Blk.parent])
        | mk P₀ s n a r =>
            have hPP : P₀ = P := by
              have h3 : some P₀ = some P := hOpt
              injection h3
            subst hPP
            simp only [postState]
            rw [h P₀ σP hσP]
            exact hrep
  · exact absurd hrep (by simp)

omit [BlockHash Node Root] in
/-- Overwriting a record with the same block's replay keeps every entry: the replay is
    deterministic, so the new value equals the old one. -/
theorem update_keeps {S : Store Node Root}
    (h : ∀ B σB, S.σ B = some σB → postState B = .state σB)
    {B' : Blk Node Root} {σ' : ChainState Node Root} (hpost : postState B' = .state σ')
    {B₀ : Blk Node Root} {σ₀ : ChainState Node Root} (h₀ : S.σ B₀ = some σ₀) :
    Function.update S.σ B' (some σ') B₀ = some σ₀ := by
  rw [Function.update_apply]
  split_ifs with hb
  · subst hb
    have h2 := h B₀ σ₀ h₀
    rw [hpost] at h2
    injection h2 with h3
    rw [h3]
  · exact h₀

/-- The one entry the accept branch writes, read back through `update_justified`. Named
    because `storeInv_accept` needs it as `update_finalized`'s provenance witness, and the
    record literal makes it awkward to inline. -/
theorem writes_self {S : Store Node Root} {B' : Blk Node Root} {σ' : ChainState Node Root} :
    (updateJustified
      { S with σ := Function.update S.σ B' (some σ'), T := S.T ∪ {B'},
               hmax := max S.hmax σ'.h } σ'.J σ'.h_j).σ B' = some σ' := by
  have h1 : Function.update S.σ B' (some σ') B' = some σ' := by
    rw [Function.update_apply]; exact if_pos rfl
  rw [updateJustified_σ]
  exact h1

/-- **Everything the accept branch does before the finality update preserves the invariant**:
    the three writes, then `update_justified`. Two cases, differing only in the three
    provenance fields, and the interesting one is `keyDom` when the justification did not
    fire — the new record's own pair then lost the key comparison, which is what that field
    claims.

    Split from `update_finalized` (below) because Theorem 8 (`hft:thm:finlive`) reads the
    invariant at exactly this point: its proof asks whether the finality update's three
    conditions hold, and answering each is an argument about a store whose records the
    healing machinery has to apply to. -/
theorem storeInv_writes_justified {S : Store Node Root} (hinv : StoreInv S)
    {B' P : Blk Node Root} {σ' : ChainState Node Root}
    (hP : B'.parent = some P) (hPT : P ∈ S.T)
    (hpost : postState B' = .state σ') :
    StoreInv (updateJustified
      { S with σ := Function.update S.σ B' (some σ'), T := S.T ∪ {B'},
               hmax := max S.hmax σ'.h } σ'.J σ'.h_j) := by
  set u : Blk Node Root → Option (ChainState Node Root) :=
    Function.update S.σ B' (some σ') with hu
  have hself : u B' = some σ' := by
    rw [hu, Function.update_apply]
    exact if_pos rfl
  -- Facts at the intermediate store, shared by both cases.
  have hrec₁ : ∀ B σB, u B = some σB → postState B = .state σB := by
    intro B σB hB
    rw [hu, Function.update_apply] at hB
    split_ifs at hB with hb
    · subst hb; injection hB with h2; rw [← h2]; exact hpost
    · exact hinv.recorded B σB hB
  have hdom₁ : ∀ B, B ∈ S.T ∪ {B'} ↔ (u B).isSome := by
    intro B
    rw [hu, Function.update_apply, Finset.mem_union, Finset.mem_singleton]
    split_ifs with hb
    · simp [hb]
    · simp only [Option.isSome]
      rw [hinv.domT B]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd h hb
      · exact Or.inl
  have hpar₁ : ∀ B ∈ S.T ∪ {B'}, ∀ Q, B.parent = some Q → Q ∈ S.T ∪ {B'} := by
    intro B hB Q hQ
    rw [Finset.mem_union, Finset.mem_singleton] at hB
    rcases hB with hB | rfl
    · exact Finset.mem_union_left _ (hinv.parentT B hB Q hQ)
    · have hQP : Q = P := by
        rw [hP] at hQ
        injection hQ with h2
        exact h2.symm
      subst hQP
      exact Finset.mem_union_left _ hPT
  have hle₁ : ∀ B σB, u B = some σB → σB.h ≤ max S.hmax σ'.h := by
    intro B σB hB
    rw [hu, Function.update_apply] at hB
    split_ifs at hB with hb
    · injection hB with h2; rw [← h2]; exact le_max_right _ _
    · exact le_trans (hinv.hmaxLe B σB hB) (le_max_left _ _)
  have hex₁ : ∃ B σB, u B = some σB ∧ σB.h = max S.hmax σ'.h := by
    rcases max_choice S.hmax σ'.h with hm | hm
    · obtain ⟨B₀, σ₀, h₀, hh₀⟩ := hinv.hmaxEx
      exact ⟨B₀, σ₀, update_keeps hinv.recorded hpost h₀, by rw [hm, hh₀]⟩
    · exact ⟨B', σ', hself, by rw [hm]⟩
  have hfp : ∀ (σ₀ : ChainState Node Root) (B₀ : Blk Node Root),
      S.σ B₀ = some σ₀ → u B₀ = some σ₀ :=
    fun σ₀ B₀ h₀ => update_keeps hinv.recorded hpost h₀
  -- `update_justified`, as a record equation.
  rcases updateJustified_spec
      { S with σ := u, T := S.T ∪ {B'}, hmax := max S.hmax σ'.h } σ'.J σ'.h_j with
    ⟨hcJ, hlex, hJeq⟩ | ⟨hcJ, hJeq⟩ <;>
    rw [hJeq] <;>
    refine ⟨hrec₁, hdom₁, hpar₁, ?_, ?_, ?_, hle₁, hex₁⟩
  -- The justification fired: the new record carries the store's pair.
  · exact ⟨B', σ', hself, rfl, rfl⟩
  · rcases hinv.fProv with hgen | ⟨B₀, σ₀, h₀, hF₀⟩
    · exact Or.inl hgen
    · exact Or.inr ⟨B₀, σ₀, hfp σ₀ B₀ h₀, hF₀⟩
  · intro B σB hB hcond
    dsimp only at hcond ⊢
    (try dsimp only at hcJ)
    have hB' : Function.update S.σ B' (some σ') B = some σB := hB
    rw [Function.update_apply] at hB'
    split_ifs at hB' with hb
    · injection hB' with h2
      subst hb
      rw [← h2]
      exact Or.inr ⟨rfl, le_refl _⟩
    · dsimp only at hlex
      have hold := hinv.keyDom B σB hB' hcond
      rcases hold with h3 | ⟨h3, h4⟩ <;> rcases hlex with h1 | ⟨h1, h2⟩ <;> omega
  -- The justification did not fire: the store keeps its own pair, and the new record's pair
  -- is what lost the key comparison.
  · obtain ⟨B₀, σ₀, h₀, hJ₀, hh₀⟩ := hinv.jProv
    exact ⟨B₀, σ₀, hfp σ₀ B₀ h₀, hJ₀, hh₀⟩
  · rcases hinv.fProv with hgen | ⟨B₀, σ₀, h₀, hF₀⟩
    · exact Or.inl hgen
    · exact Or.inr ⟨B₀, σ₀, hfp σ₀ B₀ h₀, hF₀⟩
  · intro B σB hB hcond
    dsimp only at hcond ⊢
    (try dsimp only at hcJ)
    have hB' : Function.update S.σ B' (some σ') B = some σB := hB
    rw [Function.update_apply] at hB'
    split_ifs at hB' with hb
    · injection hB' with h2
      subst hb
      rw [← h2] at hcond ⊢
      have h5 : ¬ S.h_j < σ'.h_j := fun h => hcJ ⟨hcond, Or.inl h⟩
      rcases Nat.lt_or_ge σ'.h_j S.h_j with h7 | h7
      · exact Or.inl h7
      · have h8 : σ'.h_j = S.h_j := by omega
        refine Or.inr ⟨h8, ?_⟩
        by_contra h9
        exact hcJ ⟨hcond, Or.inr ⟨h8, by omega⟩⟩
    · exact hinv.keyDom B σB hB' hcond

/-- **`update_finalized` preserves the invariant**, given that the block it installs comes
    from a record — which is the first half of Remark 5 (`hft:rem:fs-invariant`), and is what
    `fProv` then reports. `keyDom` survives because the update's own condition `Σ.F ≺ F'` puts
    the new `F` at or above the old one, so that field's hypothesis only narrows; every other
    field reads a component the update does not touch. -/
theorem storeInv_updateFinalized {S : Store Node Root} (hinv : StoreInv S) {F' : Blk Node Root}
    (hprov : ∃ B σB, S.σ B = some σB ∧ σB.F = F') :
    StoreInv (updateFinalized S F') := by
  rcases updateFinalized_spec S F' with ⟨hc1, hc2, hc3, heq⟩ | ⟨hc, heq⟩ <;> rw [heq]
  · refine ⟨hinv.recorded, hinv.domT, hinv.parentT, hinv.jProv, Or.inr hprov, ?_,
      hinv.hmaxLe, hinv.hmaxEx⟩
    intro B σB hB hcond
    dsimp only at hB hcond ⊢
    exact hinv.keyDom B σB hB (Preceq.trans hc1.1 hcond)
  · exact hinv

/-- The accept branch of `on_block` preserves the invariant: the two halves above composed,
    with the newly written record as `update_finalized`'s provenance witness. -/
theorem storeInv_accept {S : Store Node Root} (hinv : StoreInv S)
    {B' P : Blk Node Root} {σ' : ChainState Node Root}
    (hP : B'.parent = some P) (hPT : P ∈ S.T)
    (hpost : postState B' = .state σ') :
    StoreInv (updateFinalized (updateJustified
      { S with σ := Function.update S.σ B' (some σ'), T := S.T ∪ {B'},
               hmax := max S.hmax σ'.h } σ'.J σ'.h_j) σ'.F) :=
  storeInv_updateFinalized (storeInv_writes_justified hinv hP hPT hpost)
    ⟨B', σ', writes_self, rfl⟩

/-- `on_block` preserves the invariant. -/
theorem storeInv_onBlock {S : Store Node Root} (hinv : StoreInv S) (B' : Blk Node Root) :
    StoreInv (onBlock S B') := by
  simp only [onBlock, Id.run]
  split
  · rename_i P hP
    split_ifs with hadm
    · split
      · rename_i σ' hrep
        have hpost : postState B' = .state σ' := replay_postState hinv.recorded hrep
        exact storeInv_accept hinv hP hadm.1 hpost
      · exact hinv
    · exact hinv
  · exact hinv

/-- Receipt preserves the invariant. -/
theorem storeInv_receive {S : Store Node Root} (hinv : StoreInv S) (m : StoreMsg Node Root) :
    StoreInv (Decoupled.receive S m) := by
  cases m with
  | block B' => exact storeInv_onBlock hinv B'

/-- The genesis store satisfies the invariant. -/
theorem storeInv_gen : StoreInv (Store.gen : Store Node Root) := by
  refine ⟨gen_recorded, ?_, ?_, ?_, Or.inl rfl, ?_, ?_, ?_⟩
  · intro B
    by_cases hb : B = Blk.genesis
    · subst hb; simp [Store.gen]
    · simp [Store.gen, hb]
  · intro B hB Q hQ
    have hB' : B ∈ ({Blk.genesis} : Finset (Blk Node Root)) := hB
    rw [Finset.mem_singleton] at hB'
    subst hB'
    exact absurd hQ (by simp [Blk.parent])
  · exact ⟨.genesis, .gen, if_pos rfl, rfl, rfl⟩
  · intro B σB hB _
    have hB' : (if B = Blk.genesis then some (ChainState.gen : ChainState Node Root)
        else none) = some σB := hB
    split_ifs at hB' with hb
    injection hB' with h2
    rw [← h2]
    exact Or.inr ⟨rfl, le_refl _⟩
  · intro B σB hB
    have hB' : (if B = Blk.genesis then some (ChainState.gen : ChainState Node Root)
        else none) = some σB := hB
    split_ifs at hB' with hb
    injection hB' with h2
    rw [← h2]
    exact le_refl _
  · exact ⟨.genesis, .gen, if_pos rfl, rfl⟩

end Store

section Exec
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-- Every store a validator holds satisfies the invariant. -/
theorem reaches_storeInv {sched : Schedule Node}
    {x : Exec (protocol (Node := Node) (Root := Root)) sched} {p : Node}
    {S : Store Node Root} (hS : Reaches x p S) : StoreInv S := by
  obtain ⟨i, rfl⟩ := hS
  exact exec_node_invariant (P := StoreInv)
    (fun S m h => storeInv_receive h m) storeInv_gen x p i

end Exec

end Proofs

end Decoupled
