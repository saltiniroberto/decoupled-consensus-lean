import Analysis.Proofs.Viability

/-!
# Theorem 8 (`hft:thm:finlive`): the store accepts the finality update

The claim is that `on_block` does not *miss* a finality update: when the store accepts a block
whose replayed state records `F'` as finalized, the store's own finalized block ends at or
below `F'` on its chain. Since `Σ.F` moves only inside `update_finalized`, that means the three
conditions on line 552 of Figure 2 (`hft:alg:store`) must all pass, or the store already sat at
or above `F'`. So the proof is one case per condition, and each case is a small lemma here:

* `accept_notPrec` — the first condition, `Σ.F ≺ F'`, fails. Then either the two are equal, or
  they are not comparable at all, and `fProv` plus `finalizedChainE1` orders the two finalized
  pairs or produces the evidence.
* `accept_underJ` — the second, `F' ⪯ Σ.J`. If `update_justified` fired, `F' ⪯ σ'.J` is
  `Chained` and there is nothing to prove; otherwise the offered key lost the comparison, which
  bounds `σ'.h_j` — hence `σ'.h_F` — by the store's own `h_j`, and `certChain` at the record
  `jProv` names finishes.
* `accept_viable` — the third. The block just accepted is itself a record at the intermediate
  store, its own finalized block is on its chain and so accepted, and its height sits below the
  new `hmax`; `viable_of_height_lt` does the rest.

The paper's proof runs differently at the second condition: it names an ancestor `B'` of `B`
whose post-state *justified* `F'`, argues that `B'` was processed first because the order is
parent-first, and calls its Lemma 9 (`hft:lem:upgrade`). No such ancestor is needed here.
`Chained` already gives `σ'.h_F ≤ σ'.h_j` on the accepted block's own state, so `certChain`
applies to the store's justified record directly, with the accepted block as the finalizing
chain. That is one fewer object to produce and it drops the parent-first hypothesis from this
theorem entirely.

## Finding the accepting step

`exec_step_shape` says a step either leaves the validator's store alone or folds one message
into it. With it, `exists_first_change` — the first index at which a property of `Nat` turns on
— locates the step `k` where `B` entered the tree: `B ∉ S.T` at the earlier store, `B ∈ S'.T`
at the later one (by `domT`), so some step in between admitted it, and by the shape lemma that
step is an `on_block` call. Inside `on_block`, the tree is written in one place, so the block
the call was given is `B` and the state written is `B`'s replay.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

/-- The first index at which a property of `Nat` turns on. Nothing protocol-specific: the
    induction is `Nat.le_induction` and the two cases are "it was already on at `j`" and "`j`
    is the index". -/
theorem exists_first_change {P : Nat → Prop} {i j : Nat} (hij : i ≤ j)
    (hi : ¬ P i) (hj : P j) : ∃ k, i ≤ k ∧ k < j ∧ ¬ P k ∧ P (k + 1) := by
  induction j, hij using Nat.le_induction with
  | base => exact absurd hj hi
  | succ j hij ih =>
      by_cases h : P j
      · obtain ⟨k, h1, h2, h3, h4⟩ := ih h
        exact ⟨k, h1, by omega, h3, h4⟩
      · exact ⟨j, hij, by omega, h, hj⟩

/-! ## One case per condition of the finality update -/

section Store
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-- The first condition fails: the store's finalized block is not a *strict* ancestor of the
    offered one. Then the offered one is at or below it — or the two are incomparable, which
    two finalized pairs cannot be (`finalizedChainE1`) without a slashable set. -/
theorem accept_notPrec [PositiveWeight Node] {S : Store Node Root} (hinv : StoreInv S)
    {B : Blk Node Root} {σ' : ChainState Node Root} (hpost : postState B = .state σ')
    (hc : ¬ (S.F ≺ σ'.F)) : σ'.F ⪯ S.F ∨ SlashableSet S.T B := by
  have hne : postState B ≠ invalid := replayable_of_state hpost
  have hps : postState' B hne = σ' := postState'_of_state hpost hne
  by_cases heq : S.F = σ'.F
  · exact Or.inl (by rw [heq]; exact Preceq.refl _)
  have hnp : ¬ (S.F ⪯ σ'.F) := fun h => hc ⟨h, heq⟩
  rcases hinv.fProv with hgen | ⟨B₀, σ₀, hB₀, hF₀⟩
  · exact absurd (by rw [hgen]; exact genesis_preceq _) hnp
  have hne₀ : postState B₀ ≠ invalid := record_ne_invalid hinv hB₀
  have hps₀ : postState' B₀ hne₀ = σ₀ := record_postState' hinv hB₀ hne₀
  have hT₀ : B₀ ∈ S.T := record_mem_T hinv hB₀
  rcases Nat.le_total σ'.h_F σ₀.h_F with hle | hle
  · rcases finalizedChainE1 (C := σ'.F) (h := σ'.h_F) (C' := S.F) (h' := σ₀.h_F)
        hne (by rw [hps]) (by rw [hps]) hne₀ (by rw [hps₀]; exact hF₀) (by rw [hps₀]) hle with
      hpre | ⟨A, hw, hev⟩
    · exact Or.inl hpre
    · refine Or.inr ⟨A, hw, fun v hv => ?_⟩
      obtain ⟨a, b, hav, hbv, hai, hbi, he⟩ := hev v hv
      exact ⟨a, b, hav, hbv, Or.inl hai, IncludedOnEither.ofChain hT₀ hbi, he⟩
  · rcases finalizedChainE1 (C := S.F) (h := σ₀.h_F) (C' := σ'.F) (h' := σ'.h_F)
        hne₀ (by rw [hps₀]; exact hF₀) (by rw [hps₀]) hne (by rw [hps]) (by rw [hps]) hle with
      hpre | ⟨A, hw, hev⟩
    · exact absurd hpre hnp
    · refine Or.inr ⟨A, hw, fun v hv => ?_⟩
      obtain ⟨a, b, hav, hbv, hai, hbi, he⟩ := hev v hv
      exact ⟨a, b, hav, hbv, IncludedOnEither.ofChain hT₀ hai, Or.inl hbi, he⟩

/-- The second condition, in the case where `update_justified` did not fire. Its hypothesis is
    what the failed key comparison leaves: the offered justified height is at or below the
    store's. `Chained` carries that down to the offered *finalized* height, and `certChain` at
    the record `jProv` names concludes. -/
theorem accept_underJ [PositiveWeight Node] {S : Store Node Root} (hinv : StoreInv S)
    {B : Blk Node Root} {σ' : ChainState Node Root} (hpost : postState B = .state σ')
    (hle : σ'.h_j ≤ S.h_j) : σ'.F ⪯ S.J ∨ SlashableSet S.T B := by
  have hne : postState B ≠ invalid := replayable_of_state hpost
  have hps : postState' B hne = σ' := postState'_of_state hpost hne
  have hch' : Chained σ' := chained_of_blockPostState (blockPostState_of_postState B hpost)
  obtain ⟨B₁, σ₁, hB₁, hJ₁, hh₁⟩ := hinv.jProv
  have hle' : σ'.h_F ≤ σ₁.h_j := by rw [hh₁]; exact le_trans hch'.hF_le_hj hle
  rcases certChain hinv (F := σ'.F) (h_f := σ'.h_F) hne (by rw [hps]) (by rw [hps]) hB₁ hle'
    with hpre | hev
  · exact Or.inl (by rwa [hJ₁] at hpre)
  · exact Or.inr hev

/-- The third condition, at the store the finality update actually sees — after the three
    writes and after `update_justified`, which is why `storeInv_writes_justified` had to be
    split out of `storeInv_accept`. The accepted block is a record there, its own finalized
    block lies on its chain and so is accepted, and its finalized height is below the new
    `hmax`, since `h_F ≤ h_j < h ≤ max`. -/
theorem accept_viable [PositiveWeight Node] {S : Store Node Root} (hinv : StoreInv S)
    {B P : Blk Node Root} {σ' : ChainState Node Root}
    (hP : B.parent = some P) (hPT : P ∈ S.T) (hpost : postState B = .state σ') :
    σ'.F ∈ viableTree (updateJustified
      { S with σ := Function.update S.σ B (some σ'), T := S.T ∪ {B},
               hmax := max S.hmax σ'.h } σ'.J σ'.h_j) ∨ SlashableSet S.T B := by
  obtain ⟨S₂, hS₂⟩ : ∃ V : Store Node Root, V = updateJustified
      { S with σ := Function.update S.σ B (some σ'), T := S.T ∪ {B},
               hmax := max S.hmax σ'.h } σ'.J σ'.h_j := ⟨_, rfl⟩
  rw [← hS₂]
  have hinv₂ : StoreInv S₂ := by rw [hS₂]; exact storeInv_writes_justified hinv hP hPT hpost
  have hT₂ : S₂.T = S.T ∪ {B} := by rw [hS₂, updateJustified_T]
  have hmax₂ : S₂.hmax = max S.hmax σ'.h := by rw [hS₂, updateJustified_hmax]
  have hch' : Chained σ' := chained_of_blockPostState (blockPostState_of_postState B hpost)
  have hLB : σ'.L = B := postState_L B hpost
  have hne : postState B ≠ invalid := replayable_of_state hpost
  have hps : postState' B hne = σ' := postState'_of_state hpost hne
  have hBT₂ : B ∈ S₂.T := by
    rw [hT₂]; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have hFB : σ'.F ⪯ B := by
    rw [← hLB]; exact Preceq.trans hch'.finJust hch'.justLatest
  have hFT₂ : σ'.F ∈ S₂.T := mem_T_of_preceq hinv₂ B hBT₂ σ'.F hFB
  have hlt : σ'.h_F < S₂.hmax := by
    rw [hmax₂]
    have g1 := hch'.hF_le_hj
    have g2 := hch'.hj_lt_h
    have g3 : σ'.h ≤ max S.hmax σ'.h := le_max_right _ _
    omega
  rcases viable_of_height_lt hinv₂ (F := σ'.F) (h_f := σ'.h_F) hne (by rw [hps]) (by rw [hps])
      hFT₂ hlt with h | h
  · exact Or.inl h
  · right
    rw [hT₂] at h
    exact SlashableSet.ofUnion h

/-! ## The store-side core -/

/-- **Theorem 8's store-side core**, on `on_block`'s accept branch: after the call, the store's
    finalized block is at or above the accepted block's own — or a slashable set is exhibited.

    Either the finality update fired, and the two are equal, or it did not, and one of its three
    conditions failed. The three lemmas above answer the three cases; if none of them failed the
    update would have fired, which is the contradiction that closes the last branch.

    No `S.F ⪯ S.J` hypothesis: unlike the paper's argument, nothing here goes through Theorem 4.
    The second condition is settled by `certChain` at the store's own justified record, which
    reads `keyDom` and not the `F ⪯ J` invariant. -/
theorem accept_F [PositiveWeight Node] {S : Store Node Root} (hinv : StoreInv S)
    {B P : Blk Node Root} {σ' : ChainState Node Root}
    (hP : B.parent = some P) (hPT : P ∈ S.T) (hpost : postState B = .state σ') :
    σ'.F ⪯ (updateFinalized (updateJustified
      { S with σ := Function.update S.σ B (some σ'), T := S.T ∪ {B},
               hmax := max S.hmax σ'.h } σ'.J σ'.h_j) σ'.F).F
      ∨ SlashableSet S.T B := by
  have hch' : Chained σ' := chained_of_blockPostState (blockPostState_of_postState B hpost)
  obtain ⟨S₂, hS₂⟩ : ∃ V : Store Node Root, V = updateJustified
      { S with σ := Function.update S.σ B (some σ'), T := S.T ∪ {B},
               hmax := max S.hmax σ'.h } σ'.J σ'.h_j := ⟨_, rfl⟩
  rw [← hS₂]
  have hF₂ : S₂.F = S.F := by rw [hS₂, updateJustified_F]
  have hJ₂ : S₂.J = σ'.J ∨ (S₂.J = S.J ∧ (S.F ⪯ σ'.J → σ'.h_j ≤ S.h_j)) := by
    rw [hS₂]
    rcases updateJustified_spec
        { S with σ := Function.update S.σ B (some σ'), T := S.T ∪ {B},
                 hmax := max S.hmax σ'.h } σ'.J σ'.h_j with
      ⟨hcJ, hlex, heq⟩ | ⟨hcJ, heq⟩
    · exact Or.inl (by rw [heq])
    · refine Or.inr ⟨by rw [heq], fun hSF => ?_⟩
      by_contra hlt
      have hlt' : S.h_j < σ'.h_j := by omega
      exact hcJ ⟨hSF, Or.inl hlt'⟩
  have hviab : σ'.F ∈ viableTree S₂ ∨ SlashableSet S.T B := by
    rw [hS₂]; exact accept_viable hinv hP hPT hpost
  rcases updateFinalized_spec S₂ σ'.F with ⟨-, -, -, hFeq⟩ | ⟨hcF, hFeq⟩
  · rw [hFeq]; exact Or.inl (Preceq.refl _)
  · rw [hFeq, hF₂]
    by_cases h1 : S.F ≺ σ'.F
    · have hc1 : S₂.F ≺ σ'.F := by rw [hF₂]; exact h1
      have hSFJ : S.F ⪯ σ'.J := Preceq.trans h1.1 hch'.finJust
      have hc2 : σ'.F ⪯ S₂.J ∨ SlashableSet S.T B := by
        rcases hJ₂ with hj | ⟨hj, hkey⟩
        · exact Or.inl (by rw [hj]; exact hch'.finJust)
        · rcases accept_underJ hinv hpost (hkey hSFJ) with g | g
          · exact Or.inl (by rw [hj]; exact g)
          · exact Or.inr g
      rcases hc2 with hc2 | hev
      · rcases hviab with hc3 | hev
        · exact absurd ⟨hc1, hc2, hc3⟩ hcF
        · exact Or.inr hev
      · exact Or.inr hev
    · exact accept_notPrec hinv hpost h1

/-- The accept leaf, keyed on the record read after the call rather than on the block the call
    was given: the map is written in one place, so a record for a block the store did not have
    is the new entry, which identifies the block and the state at once. -/
theorem accept_new_F [PositiveWeight Node] {S : Store Node Root} (hinv : StoreInv S)
    {B' P B : Blk Node Root} {σ' σB : ChainState Node Root}
    (hP : B'.parent = some P) (hPT : P ∈ S.T) (hpost : postState B' = .state σ')
    (hnew : B ∉ S.T)
    (hrec : (updateFinalized (updateJustified
      { S with σ := Function.update S.σ B' (some σ'), T := S.T ∪ {B'},
               hmax := max S.hmax σ'.h } σ'.J σ'.h_j) σ'.F).σ B = some σB) :
    σB.F ⪯ (updateFinalized (updateJustified
      { S with σ := Function.update S.σ B' (some σ'), T := S.T ∪ {B'},
               hmax := max S.hmax σ'.h } σ'.J σ'.h_j) σ'.F).F
      ∨ SlashableSet S.T B := by
  have hmap : Function.update S.σ B' (some σ') B = some σB := by
    rw [updateFinalized_σ, updateJustified_σ] at hrec; exact hrec
  rw [Function.update_apply] at hmap
  split_ifs at hmap with hb
  · injection hmap with h2
    subst h2
    subst hb
    exact accept_F hinv hP hPT hpost
  · exact absurd (record_mem_T hinv hmap) hnew

/-- **`on_block` recording a block the store did not have** puts the store's finalized block at
    or above that block's own. Every rejection leaf leaves the map alone, so a record for a
    block absent from the tree contradicts `domT`; the accept leaf is `accept_new_F`. -/
theorem onBlock_new_F [PositiveWeight Node] {S : Store Node Root} (hinv : StoreInv S)
    (B' : Blk Node Root) {B : Blk Node Root} {σB : ChainState Node Root}
    (hnew : B ∉ S.T) :
    (onBlock S B').σ B = some σB → σB.F ⪯ (onBlock S B').F ∨ SlashableSet S.T B := by
  simp only [onBlock, Id.run]
  split
  · rename_i P hP
    split_ifs with hadm
    · split
      · rename_i σ' hrep
        exact fun hrec => accept_new_F hinv hP hadm.1
          (replay_postState hinv.recorded hrep) hnew hrec
      · exact fun hrec => absurd (record_mem_T hinv hrec) hnew
    · exact fun hrec => absurd (record_mem_T hinv hrec) hnew
  · exact fun hrec => absurd (record_mem_T hinv hrec) hnew

end Store

/-! ## The execution layer -/

section Exec
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-- **One step either leaves the validator's store alone or folds one message into it.** The
    `Step.elim` walk of `exec_step_F`, with the conclusion an equation instead of an
    inequality: `advance`/`adversarial` touch no node, `custom` is `Empty`, `tick`/`wake`
    reactions keep the state, and a delivery to the observed validator is the one case that
    calls `receive`. -/
theorem exec_step_shape {sched : Schedule Node}
    (x : Exec (protocol (Node := Node) (Root := Root)) sched) (p : Node) (i : Nat) :
    x[i + 1][p].st = x[i][p].st ∨
      ∃ m : StoreMsg Node Root, x[i + 1][p].st = Decoupled.receive (x[i][p].st) m := by
  refine Step.elim (motive := fun _ c c' => c'[p].st = c[p].st ∨
      ∃ m : StoreMsg Node Root, c'[p].st = Decoupled.receive (c[p].st) m)
    (x.step i) (fun d t => Or.inl rfl) ?tick ?deliver ?wake
    (fun d q ev res he hp => ev.elim) (fun d q m he => Or.inl rfl)
  case tick =>
    intro d q t res he hp
    have hres : res = reaction ((setClock q t d)[q].st) .tick := hp
    by_cases hqp : q = p
    · subst hqp
      rw [applyNodeStepResult_st_self, hres, setClock_st]
      exact Or.inl rfl
    · rw [applyNodeStepResult_st_other hqp, setClock_st]
      exact Or.inl rfl
  case deliver =>
    intro d q m res he hp
    have hres : res = reaction ((Framework.StsMultisetLog.receive q m d)[q].st) (.recv m) := hp
    by_cases hqp : q = p
    · subst hqp
      rw [applyNodeStepResult_st_self, hres, receive_st]
      exact Or.inr ⟨m.msg, rfl⟩
    · rw [applyNodeStepResult_st_other hqp, receive_st]
      exact Or.inl rfl
  case wake =>
    intro d q res he hp
    have hres : res = reaction (d[q].st) .wake := hp
    by_cases hqp : q = p
    · subst hqp
      rw [applyNodeStepResult_st_self, hres]
      exact Or.inl rfl
    · rw [applyNodeStepResult_st_other hqp]
      exact Or.inl rfl

/-- **Theorem 8 (`hft:thm:finlive`)'s content.** Read aloud: when a validator's store records a
    block it did not have before, the state that record carries has its finalized block at or
    below the store's own by then — or a set of validators of weight `2q − W` each signed an E1
    pair, both messages on chains the store accepted.

    The step that recorded `B` is found by `exists_first_change` on membership of the tree, and
    `exec_step_shape` makes it an `on_block` call; `onBlock_new_F` is the whole argument there.
    The record at that step is the same state as the one the statement names, because both are
    `B`'s replay (the bridge). Then Theorem 3 carries the finalized block forward to the later
    store, and `reachesFrom_T` carries the evidence — which sits on chains the earlier store
    accepted, `B_F` being `B` itself, hence `SlashableSet.onTree`. -/
theorem finalityAcceptance [PositiveWeight Node] {sched : Schedule Node}
    {x : Exec (protocol (Node := Node) (Root := Root)) sched} {p : Node}
    {S S' : Store Node Root} (h : ReachesFrom x p S S')
    {B F' : Blk Node Root} (hnew : B ∉ S.T)
    (hB : get σB from S'.σ B; σB.F = F') :
    F' ⪯ S'.F ∨ Slashable (fun a => IncludedOnSome a S'.T) := by
  obtain ⟨i, j, hij, rfl, rfl⟩ := h
  obtain ⟨σB, hσB, hF'⟩ := hB
  have hσB' : (storeAt x p j).σ B = some σB := hσB
  have hinvj : StoreInv (storeAt x p j) := reaches_storeInv ⟨j, rfl⟩
  have hBj : B ∈ (storeAt x p j).T := record_mem_T hinvj hσB'
  obtain ⟨k, hik, hkj, hnk, hnk1⟩ :=
    exists_first_change (P := fun n => B ∈ (storeAt x p n).T) hij hnew hBj
  have hinvk : StoreInv (storeAt x p k) := reaches_storeInv ⟨k, rfl⟩
  have hinvk1 : StoreInv (storeAt x p (k + 1)) := reaches_storeInv ⟨k + 1, rfl⟩
  -- the record at `k + 1` is `B`'s replay, hence the one the statement names
  obtain ⟨σk, hσk⟩ : ∃ σk, (storeAt x p (k + 1)).σ B = some σk :=
    Option.isSome_iff_exists.1 ((hinvk1.domT B).1 hnk1)
  have hσeq : σk = σB := by
    have g1 := record_postState hinvk1 hσk
    have g2 := record_postState hinvj hσB'
    rw [g1] at g2
    injection g2
  subst hσeq
  -- the step that recorded it is an `on_block` call
  rcases exec_step_shape x p k with hid | ⟨m, hm⟩
  · have hid' : storeAt x p (k + 1) = storeAt x p k := hid
    rw [hid'] at hnk1
    exact absurd hnk1 hnk
  cases m with
  | block B' =>
    have hstep : storeAt x p (k + 1) = onBlock (storeAt x p k) B' := hm
    have hrec : (onBlock (storeAt x p k) B').σ B = some σk := by rw [← hstep]; exact hσk
    rcases onBlock_new_F hinvk B' hnk hrec with hpre | hev
    · left
      rw [← hF']
      have hstep' : σk.F ⪯ (storeAt x p (k + 1)).F := by rw [hstep]; exact hpre
      exact Preceq.trans hstep' (localIrreversibility x p hkj)
    · right
      refine SlashableSet.onTree hBj (SlashableSet.mono ?_ hev)
      exact reachesFrom_T (x := x) (p := p) ⟨k, j, Nat.le_of_lt hkj, rfl, rfl⟩

end Exec

end Proofs

end Decoupled
