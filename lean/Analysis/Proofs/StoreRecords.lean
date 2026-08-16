import Analysis.Proofs.Finality
import Analysis.Proofs.StoreProvenance

/-!
# Records persist, the tree grows, and what a record hands the healing machinery

The small machinery Theorems 8–10 consume constantly, in three parts.

**Monotonicity.** `on_block` never forgets: a recorded state stays recorded (`onBlock_record_mono`,
which needs the recorded-replay bridge because an overwrite writes the same value — that is
`update_keeps`), and a block once accepted stays accepted (`onBlock_T_mono`). Both lift to
`ReachesFrom` through `reachesFrom_mono`.

**`reachesFrom_mono`**, the walker's companion. `exec_node_invariant`
(`Analysis/Proofs/StoreInvariants.lean`) carries a store *predicate* from `Store.gen` forward;
this carries a store *relation* between two stores one validator holds in order, given that
`receive` establishes it at every store satisfying `StoreInv` — which is every held store, by
`reaches_storeInv`. So the relation's hypotheses may use the invariant, which is what
`onBlock_record_mono` needs. `reachesFrom_F` (Theorem 3) is the same shape written out by hand,
before this existed; it is not rewritten through this, because it needs no invariant and its
own walk is what `exec_step_mono` was modelled on.

**`record_…`.** A store's record is a replayed post-state, so everything the healing paper
proves about `BlockPostState` applies to it: `Chained` (`F ⪯ J ⪯ L`, `h_F ≤ h_j < h`),
`Certified` (the quorums and anchors behind the two recorded pairs), the block itself as the
state's own endpoint (`σB.L = B`, so `IncludedOn a σB.L` is `IncludedOn a B`), and membership
of `T`. Each is one line over `StoreInv.recorded` plus a healing result; they are named because
every quorum argument below opens with two or three of them.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

/-! ## `on_block` forgets nothing -/

section Store
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

omit [Electorate Node] [Params] in
/-- `update_justified` never writes the tree. -/
theorem updateJustified_T (S : Store Node Root) (J' : Blk Node Root) (h' : Nat) :
    (updateJustified S J' h').T = S.T := by
  simp only [updateJustified, Id.run]; split_ifs <;> rfl

omit [Electorate Node] [Params] [BlockHash Node Root] in
/-- `update_finalized` never writes the tree. -/
theorem updateFinalized_T (S : Store Node Root) (F' : Blk Node Root) :
    (updateFinalized S F').T = S.T := by
  simp only [updateFinalized, Id.run]; split_ifs <;> rfl

omit [Electorate Node] [Params] in
/-- `update_justified` never writes the maximum height. -/
theorem updateJustified_hmax (S : Store Node Root) (J' : Blk Node Root) (h' : Nat) :
    (updateJustified S J' h').hmax = S.hmax := by
  simp only [updateJustified, Id.run]; split_ifs <;> rfl

omit [Electorate Node] [Params] [BlockHash Node Root] in
/-- `update_finalized` never writes the maximum height. -/
theorem updateFinalized_hmax (S : Store Node Root) (F' : Blk Node Root) :
    (updateFinalized S F').hmax = S.hmax := by
  simp only [updateFinalized, Id.run]; split_ifs <;> rfl

omit [Electorate Node] [Params] in
/-- The two updates in `on_block`'s order keep the map: what the intermediate store records,
    the store after both updates records.

    Stated for *application* at `on_block`'s accept leaf, where the intermediate store is a
    record literal `rw` cannot reach through the leaf's `pure` wrapper — the same shape as
    `updates_F` in `Analysis/Proofs/Irreversibility.lean`, and the reason both exist. -/
theorem updates_record {S : Store Node Root} {J' F' : Blk Node Root} {h' : Nat}
    {B : Blk Node Root} {σB : ChainState Node Root} (hB : S.σ B = some σB) :
    (updateFinalized (updateJustified S J' h') F').σ B = some σB := by
  rw [updateFinalized_σ, updateJustified_σ]; exact hB

omit [Electorate Node] [Params] in
/-- The same for the tree, applied the same way. -/
theorem updates_T_sub {T₀ : Finset (Blk Node Root)} {S : Store Node Root}
    {J' F' : Blk Node Root} {h' : Nat} (h : T₀ ⊆ S.T) :
    T₀ ⊆ (updateFinalized (updateJustified S J' h') F').T := by
  rw [updateFinalized_T, updateJustified_T]; exact h

/-- **A recorded state stays recorded.** The only write to the map is the accepted block's own
    entry, and it writes the block's replay — which, on a store whose records are replays, is
    the value already there (`update_keeps`). So the hypothesis is the bridge, not a whole
    `StoreInv`. -/
theorem onBlock_record_mono {S : Store Node Root}
    (hrec : ∀ B σB, S.σ B = some σB → postState B = .state σB)
    (B' : Blk Node Root) {B : Blk Node Root} {σB : ChainState Node Root}
    (hB : S.σ B = some σB) : (onBlock S B').σ B = some σB := by
  simp only [onBlock, Id.run]
  split
  · rename_i P hP
    split_ifs with hadm
    · split
      · rename_i σ' hrep
        have hpost : postState B' = .state σ' := replay_postState hrec hrep
        exact updates_record (update_keeps hrec hpost hB)
      · exact hB
    · exact hB
  · exact hB

/-- **An accepted block stays accepted.** The tree is written in one place, a union. -/
theorem onBlock_T_mono (S : Store Node Root) (B' : Blk Node Root) : S.T ⊆ (onBlock S B').T := by
  simp only [onBlock, Id.run]
  repeat' split
  all_goals first
    | exact Finset.Subset.refl _
    | exact updates_T_sub Finset.subset_union_left

/-- Receipt keeps a record — today, by `onBlock_record_mono`. -/
theorem receiveMsg_record_mono {S : Store Node Root}
    (hrec : ∀ B σB, S.σ B = some σB → postState B = .state σB)
    (m : StoreMsg Node Root) {B : Blk Node Root} {σB : ChainState Node Root}
    (hB : S.σ B = some σB) : (Decoupled.receive S m).σ B = some σB := by
  cases m with
  | block B' => exact onBlock_record_mono hrec B' hB

/-- Receipt keeps the tree — today, by `onBlock_T_mono`. -/
theorem receiveMsg_T_mono (S : Store Node Root) (m : StoreMsg Node Root) :
    S.T ⊆ (Decoupled.receive S m).T := by
  cases m with
  | block B' => exact onBlock_T_mono S B'

end Store

/-! ## The walker's companion: a relation carried between two held stores -/

section Exec
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-- One step. The motive carries `StoreInv (c[p].st)` as a hypothesis rather than deriving it
    inside a case, because `Step.elim` hands each case an arbitrary configuration `d` and only
    instantiates it at the end; the invariant is discharged once, at the application, from
    `exec_node_invariant`. Everything else is `exec_step_F`'s walk: `advance`/`adversarial`
    touch no node, `custom` is `Empty`, `tick`/`wake` reactions keep the state, and `recv` is
    the `hrecv` hypothesis. -/
theorem exec_step_mono {R : Store Node Root → Store Node Root → Prop}
    (hrefl : ∀ S, R S S)
    (hrecv : ∀ (S : Store Node Root) (m : StoreMsg Node Root), StoreInv S →
      R S (Decoupled.receive S m))
    {sched : Schedule Node} (x : Exec (protocol (Node := Node) (Root := Root)) sched)
    (p : Node) (i : Nat) : R (x[i][p].st) (x[i + 1][p].st) := by
  refine Step.elim (motive := fun _ c c' => StoreInv (c[p].st) → R (c[p].st) (c'[p].st))
    (x.step i) (fun d t _ => hrefl _) ?tick ?deliver ?wake
    (fun d q ev res he hp _ => ev.elim) (fun d q m he _ => hrefl _)
    (exec_node_invariant (P := StoreInv) (fun S m h => storeInv_receive h m) storeInv_gen x p i)
  case tick =>
    intro d q t res he hp _
    have hres : res = reaction ((setClock q t d)[q].st) .tick := hp
    by_cases hqp : q = p
    · subst hqp
      rw [applyNodeStepResult_st_self, hres, setClock_st]
      exact hrefl _
    · rw [applyNodeStepResult_st_other hqp, setClock_st]
      exact hrefl _
  case deliver =>
    intro d q m res he hp hinv
    have hres : res = reaction ((Framework.StsMultisetLog.receive q m d)[q].st) (.recv m) := hp
    by_cases hqp : q = p
    · subst hqp
      rw [applyNodeStepResult_st_self, hres, receive_st]
      exact hrecv (d[q].st) m.msg hinv
    · rw [applyNodeStepResult_st_other hqp, receive_st]
      exact hrefl _
  case wake =>
    intro d q res he hp _
    have hres : res = reaction (d[q].st) .wake := hp
    by_cases hqp : q = p
    · subst hqp
      rw [applyNodeStepResult_st_self, hres]
      exact hrefl _
    · rw [applyNodeStepResult_st_other hqp]
      exact hrefl _

/-- The walk across steps, `Nat.le_induction` over `exec_step_mono`. -/
theorem exec_mono {R : Store Node Root → Store Node Root → Prop}
    (hrefl : ∀ S, R S S)
    (htrans : ∀ S₁ S₂ S₃ : Store Node Root, R S₁ S₂ → R S₂ S₃ → R S₁ S₃)
    (hrecv : ∀ (S : Store Node Root) (m : StoreMsg Node Root), StoreInv S →
      R S (Decoupled.receive S m))
    {sched : Schedule Node} (x : Exec (protocol (Node := Node) (Root := Root)) sched)
    (p : Node) {i j : Nat} (hij : i ≤ j) : R (x[i][p].st) (x[j][p].st) := by
  induction j, hij using Nat.le_induction with
  | base => exact hrefl _
  | succ j hij ih => exact htrans _ _ _ ih (exec_step_mono hrefl hrecv x p j)

/-- **A reflexive, transitive store relation that `receive` establishes at every invariant
    store holds between any two stores one validator holds in order.** The relational
    counterpart of `exec_node_invariant`, and what lifts the two monotonicity facts above to
    the reachability vocabulary. -/
theorem reachesFrom_mono {R : Store Node Root → Store Node Root → Prop}
    (hrefl : ∀ S, R S S)
    (htrans : ∀ S₁ S₂ S₃ : Store Node Root, R S₁ S₂ → R S₂ S₃ → R S₁ S₃)
    (hrecv : ∀ (S : Store Node Root) (m : StoreMsg Node Root), StoreInv S →
      R S (Decoupled.receive S m))
    {sched : Schedule Node} {x : Exec (protocol (Node := Node) (Root := Root)) sched}
    {p : Node} {S S' : Store Node Root} (h : ReachesFrom x p S S') : R S S' := by
  obtain ⟨i, j, hij, rfl, rfl⟩ := h
  exact exec_mono hrefl htrans hrecv x p hij

/-- **A record persists at all future times.** -/
theorem reachesFrom_record {sched : Schedule Node}
    {x : Exec (protocol (Node := Node) (Root := Root)) sched} {p : Node}
    {S S' : Store Node Root} (h : ReachesFrom x p S S')
    {B : Blk Node Root} {σB : ChainState Node Root} (hB : S.σ B = some σB) :
    S'.σ B = some σB :=
  reachesFrom_mono
    (R := fun S S' => ∀ B σB, S.σ B = some σB → S'.σ B = some σB)
    (fun _ _ _ h => h) (fun _ _ _ h1 h2 B σB hB => h2 B σB (h1 B σB hB))
    (fun _ m hinv _ _ hB => receiveMsg_record_mono hinv.recorded m hB) h B σB hB

/-- **The tree only grows, at all future times.** So evidence pinned to a block the store
    accepted stays pinned there, which is what the theorems' disjuncts need. -/
theorem reachesFrom_T {sched : Schedule Node}
    {x : Exec (protocol (Node := Node) (Root := Root)) sched} {p : Node}
    {S S' : Store Node Root} (h : ReachesFrom x p S S') : S.T ⊆ S'.T :=
  reachesFrom_mono (R := fun S S' => S.T ⊆ S'.T)
    (fun _ => Finset.Subset.refl _) (fun _ _ _ h1 h2 => Finset.Subset.trans h1 h2)
    (fun S m _ => receiveMsg_T_mono S m) h

end Exec

/-! ## `postState'`, from a replay equation

The healing statements name a chain's replayed state as `postState' B`, a definite description
behind a `Replayable B` proof; the store's records arrive as `postState B = .state σB`. These
two cross between the spellings, and are what every application of `lemPastFinalized`,
`finalizedChainE1` or `Certified` to a store record opens with. -/

section PostState
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  {B : Blk Node Root} {σ : ChainState Node Root}

/-- A block that replays to a state replays. -/
theorem replayable_of_state (h : postState B = .state σ) : postState B ≠ invalid := by
  rw [h]; simp

/-- …and the state it replays to is `postState' B`. -/
theorem postState'_of_state (h : postState B = .state σ) (hne : postState B ≠ invalid) :
    postState' B hne = σ := by
  have h2 : postState B = .state (postState' B hne) := TransitionResult.state_get _ hne
  have h4 : (TransitionResult.state (postState' B hne) : TransitionResult Node Root)
      = .state σ := h2.symm.trans h
  injection h4

end PostState

/-! ## What a record hands the healing machinery -/

section Record
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root] {S : Store Node Root} {B : Blk Node Root}
  {σB : ChainState Node Root}

/-- The bridge, read off the invariant. -/
theorem record_postState (hinv : StoreInv S) (hB : S.σ B = some σB) :
    postState B = .state σB := hinv.recorded B σB hB

/-- A recorded state is a block post-state, so every healing invariant applies to it. -/
theorem record_blockPostState (hinv : StoreInv S) (hB : S.σ B = some σB) :
    BlockPostState σB := blockPostState_of_postState B (record_postState hinv hB)

/-- The recorded state's own endpoint is the block it is recorded under. So `IncludedOn a σB.L`
    is `IncludedOn a B`, which is how a quorum found inside `Certified` reaches a chain the
    statements can name. -/
theorem record_L (hinv : StoreInv S) (hB : S.σ B = some σB) : σB.L = B :=
  postState_L B (record_postState hinv hB)

/-- Lemma 4's ancestry and height inequalities, at a record. -/
theorem record_chained (hinv : StoreInv S) (hB : S.σ B = some σB) : Chained σB :=
  chained_of_blockPostState (record_blockPostState hinv hB)

/-- The quorums and anchors behind a record's two pairs. -/
theorem record_certified [PositiveWeight Node] (hinv : StoreInv S) (hB : S.σ B = some σB) :
    Certified σB := certified_of_blockPostState (record_blockPostState hinv hB)

/-- A recorded block is an accepted block: `domT` read in the direction the theorems' disjuncts
    want. -/
theorem record_mem_T (hinv : StoreInv S) (hB : S.σ B = some σB) : B ∈ S.T :=
  (hinv.domT B).2 (by rw [hB]; rfl)

/-- A recorded block replays: `Replayable B`, spelled as the healing lemmas' hypothesis. -/
theorem record_ne_invalid (hinv : StoreInv S) (hB : S.σ B = some σB) :
    postState B ≠ invalid := replayable_of_state (record_postState hinv hB)

/-- The record *is* `postState'`, so a hypothesis of a healing lemma phrased over
    `(postState' B).F` can be discharged from `σB.F`. -/
theorem record_postState' (hinv : StoreInv S) (hB : S.σ B = some σB) (h : Replayable B) :
    postState' B h = σB := postState'_of_state (record_postState hinv hB) h

end Record

end Proofs

end Decoupled
