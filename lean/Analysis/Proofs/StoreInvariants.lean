import Analysis.Proofs.Irreversibility

/-!
# Theorems 4 and 7, the invariant walker, and the recorded-replay bridge

Four things live here. First, `exec_node_invariant`: a store predicate that holds at the
genesis store and is preserved by `receive` holds at every validator's store at every step
of every execution. This is the reusable half — Theorem 4 consumes it below, and the
map-domain coherence invariant will consume it next. Its proof is the walk
`Analysis/Proofs/Irreversibility.lean` demonstrates, with the relational motive replaced
by preservation of `P`: `advance`/`adversarial` touch no node, `custom` is `Empty`,
`tick`/`wake` reactions keep the state, and `recv` is the `hrecv` hypothesis.

Second, Theorem 4's chain (`hft:thm:fleqr`): `F ⪯ J` holds at the genesis store — both
fields are genesis — and each mutator preserves it by its own condition. `update_justified`
moves `J` only past the `F`-filter `Σ.F ⪯ J'`, and `update_finalized` moves `F` only under
`F' ⪯ Σ.J`; each fired branch's condition is exactly the conclusion it must re-establish,
which is the paper's own two-line proof. `reachable_FJ` is the store-level core the
statement of record used to be.

Third, Theorem 7 (`hft:thm:fcconsistency`), which rides Theorems 3 and 4: `get_confirmed`'s
own second conjunct is `R ⪯ C`, the walk-from block `R` is `J` or `F` — either at or above
`F` once `F ⪯ J` is in hand — and Theorem 3 carries the earlier store's `F` up to the
later one's.

Fourth, the **recorded-replay bridge**: every state a held store records is its block's
replay, `postState B = .state σB`. The store writes its map in exactly one place, from
`Store.replay`, which reads the parent's recorded state, so the fact is the walker at that
predicate. This is the bridge to the healing paper's analysis — a pair recorded in a store
IS a pair recorded on a replayed post-state, so `lemPastFinalized`, `lemFinalizedChain`
and the certificate machinery apply to store contents. Theorems 8–10 stand on it.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

/-! ## `F ⪯ J` through each mutator -/

section Store
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

omit [Electorate Node] [Params] in
/-- `update_justified` preserves `F ⪯ J`: when it fires, its own `F`-filter `Σ.F ⪯ J'` is
    the conclusion. -/
theorem updateJustified_FJ {S : Store Node Root} {J' : Blk Node Root} {h' : Nat}
    (h : S.F ⪯ S.J) :
    (updateJustified S J' h').F ⪯ (updateJustified S J' h').J := by
  simp only [updateJustified, Id.run]
  split_ifs with hc
  · exact hc.1
  · exact h

omit [Electorate Node] [Params] [BlockHash Node Root] in
/-- `update_finalized` preserves `F ⪯ J`: when it fires, its own condition `F' ⪯ Σ.J` is
    the conclusion. -/
theorem updateFinalized_FJ {S : Store Node Root} {F' : Blk Node Root}
    (h : S.F ⪯ S.J) :
    (updateFinalized S F').F ⪯ (updateFinalized S F').J := by
  simp only [updateFinalized, Id.run]
  split_ifs with hc
  · exact hc.2.1
  · exact h

/-- `on_block` preserves `F ⪯ J`: rejection leaves the store unchanged, and acceptance
    routes the pair through the two updates. -/
theorem onBlock_FJ {S : Store Node Root} (B : Blk Node Root) (h : S.F ⪯ S.J) :
    (onBlock S B).F ⪯ (onBlock S B).J := by
  simp only [onBlock, Id.run]
  repeat' split
  all_goals first
    | exact h
    | exact updateFinalized_FJ (updateJustified_FJ h)

/-- Receipt of any store message preserves `F ⪯ J` — today, by `onBlock_FJ`. -/
theorem receiveMsg_FJ {S : Store Node Root} (m : StoreMsg Node Root) (h : S.F ⪯ S.J) :
    (Decoupled.receive S m).F ⪯ (Decoupled.receive S m).J := by
  cases m with
  | block B => exact onBlock_FJ B h

/-- The fold preserves `F ⪯ J`. -/
theorem onBlocks_FJ {S : Store Node Root} (Bs : List (Blk Node Root)) (h : S.F ⪯ S.J) :
    (onBlocks S Bs).F ⪯ (onBlocks S Bs).J := by
  induction Bs generalizing S with
  | nil => exact h
  | cons B Bs ih => exact ih (onBlock_FJ B h)

/-- The store-level core: every store the node can hold has `F ⪯ J`. This was Theorem 4's
    statement of record before it moved to executions; the store-level Theorems 7–10 will
    want it in this form. -/
theorem reachable_FJ {S : Store Node Root} (hS : S.Reachable) : S.F ⪯ S.J := by
  obtain ⟨Bs, rfl⟩ := hS
  exact onBlocks_FJ Bs (Preceq.refl _)


/-! ## Theorem 7's store layer -/

omit [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params] [BlockHash Node Root] in
/-- The walk-from block sits at or above the store-finalized block, given `F ⪯ J`. -/
theorem F_preceq_R {S : Store Node Root} (h : S.F ⪯ S.J) : S.F ⪯ S.R := by
  unfold Store.R
  split_ifs with hc
  · exact h
  · exact Preceq.refl _

omit [Electorate Node] [Params] [BlockHash Node Root] in
/-- Every block `get_confirmed` may return descends from the store-finalized block,
    given `F ⪯ J`. -/
theorem getConfirmed_F {S : Store Node Root} {C : Blk Node Root}
    (hFJ : S.F ⪯ S.J) (hC : GetConfirmed S C) : S.F ⪯ C :=
  Preceq.trans (F_preceq_R hFJ) hC.2.1

omit [Electorate Node] [Params] [BlockHash Node Root] in
/-- The candidate set is the relation: a statement over `GetConfirmed` and one over
    membership in `getConfirmedSet` say the same thing, so the function view in
    `Spec/HftFig2Store.lean` and the relation cannot drift apart. -/
theorem mem_getConfirmedSet {S : Store Node Root} {B : Blk Node Root} :
    B ∈ getConfirmedSet S ↔ GetConfirmed S B := by
  unfold getConfirmedSet GetConfirmed
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    cases hσ : S.σ B with
    | none => rw [hσ] at h3; exact absurd h3 (by simp)
    | some st =>
        rw [hσ] at h3
        exact ⟨st, rfl, by simpa using h3⟩
  · rintro ⟨h1, h2, st, hst, h3⟩
    have hst' : S.σ B = some st := hst
    refine ⟨h1, h2, ?_⟩
    rw [hst']
    simp
    omega

omit [Electorate Node] [Params] [BlockHash Node Root] in
/-- Whatever `getConfirmed` returns, the relation admits: every statement over
    `GetConfirmed` applies to the function's output unchanged. -/
theorem getConfirmed_spec [Omega Node Root] (S : Store Node Root)
    (h : (getConfirmedSet S).Nonempty) :
    GetConfirmed S (getConfirmed S h) :=
  mem_getConfirmedSet.mp (Omega.choose (getConfirmedSet S) h).property

omit [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params] [BlockHash Node Root] in
/-- Equal candidate sets, equal choice: the `Nonempty` witnesses are proofs, hence
    irrelevant. -/
theorem Omega.choose_congr [Omega Node Root] {s t : Finset (Blk Node Root)} (hst : s = t)
    (h₁ : s.Nonempty) (h₂ : t.Nonempty) :
    (Omega.choose s h₁).val = (Omega.choose t h₂).val := by
  subst hst
  rfl

omit [Electorate Node] [Params] [BlockHash Node Root] in
/-- Two stores with the same candidates confirm the same block, whatever the ambient
    `Ω`. -/
theorem getConfirmed_congr [Omega Node Root] {S S' : Store Node Root}
    (hset : getConfirmedSet S = getConfirmedSet S')
    (h₁ : (getConfirmedSet S).Nonempty) (h₂ : (getConfirmedSet S').Nonempty) :
    getConfirmed S h₁ = getConfirmed S' h₂ :=
  Omega.choose_congr hset h₁ h₂

/-! ## The recorded-replay bridge, through each writer -/

omit [Electorate Node] [Params] in
theorem updateJustified_σ (S : Store Node Root) (J' : Blk Node Root) (h' : Nat) :
    (updateJustified S J' h').σ = S.σ := by
  simp only [updateJustified, Id.run]
  split_ifs <;> rfl

omit [Electorate Node] [Params] [BlockHash Node Root] in
theorem updateFinalized_σ (S : Store Node Root) (F' : Blk Node Root) :
    (updateFinalized S F').σ = S.σ := by
  simp only [updateFinalized, Id.run]
  split_ifs <;> rfl

theorem onBlock_recorded {S : Store Node Root} {B' : Blk Node Root}
    (h : ∀ B σB, S.σ B = some σB → postState B = .state σB)
    (B : Blk Node Root) (σB : ChainState Node Root)
    (hB : (onBlock S B').σ B = some σB) : postState B = .state σB := by
  simp only [onBlock, Id.run] at hB
  split at hB
  · rename_i P hP
    split_ifs at hB with hadm
    · split at hB
      · rename_i σ' hrep
        have hB' : Function.update S.σ B' (some σ') B = some σB := by
          have h2 : (updateFinalized (updateJustified _ _ _) _).σ B = some σB := hB
          rwa [updateFinalized_σ, updateJustified_σ] at h2
        rw [Function.update_apply] at hB'
        split_ifs at hB' with hBB
        · subst hBB
          injection hB' with hσ
          subst hσ
          simp only [Store.replay] at hrep
          split at hrep
          · rename_i σP hbind
            rw [hP] at hbind
            have hσP : S.σ P = some σP := hbind
            cases B with
            | genesis => exact absurd hP (by simp [Blk.parent])
            | mk P₀ s n a r =>
                have hPP : P₀ = P := by
                  have h3 : some P₀ = some P := hP
                  injection h3
                subst hPP
                simp only [postState]
                rw [h P₀ σP hσP]
                exact hrep
          · exact absurd hrep (by simp)
        · exact h B σB hB'
      · exact h B σB hB
    · exact h B σB hB
  · exact h B σB hB

theorem receiveMsg_recorded {S : Store Node Root} (m : StoreMsg Node Root)
    (h : ∀ B σB, S.σ B = some σB → postState B = .state σB)
    (B : Blk Node Root) (σB : ChainState Node Root)
    (hB : (Decoupled.receive S m).σ B = some σB) : postState B = .state σB := by
  cases m with
  | block B' => exact onBlock_recorded h B σB hB

omit [BlockHash Node Root] in
theorem gen_recorded (B : Blk Node Root) (σB : ChainState Node Root)
    (hB : (Store.gen : Store Node Root).σ B = some σB) : postState B = .state σB := by
  have hB' : (if B = .genesis then some (ChainState.gen : ChainState Node Root) else none)
      = some σB := hB
  split_ifs at hB' with hg
  subst hg
  injection hB' with hσ
  subst hσ
  rfl

end Store

/-! ## The walker, and Theorem 4 -/

section Exec
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-- A store predicate that holds at the genesis store and is preserved by `receive` holds
    at every validator's store, at every step of every execution: the induction is the one
    `Irreversibility.lean`'s walk demonstrates, `Empty` killing the `custom` case and the
    `st` read-backs reducing every other action to either the identity or `hrecv`. -/
theorem exec_node_invariant {P : Store Node Root → Prop}
    (hrecv : ∀ (S : Store Node Root) (m : StoreMsg Node Root), P S → P (Decoupled.receive S m))
    (hgen : P (Store.gen : Store Node Root)) {sched : Schedule Node}
    (x : Exec (protocol (Node := Node) (Root := Root)) sched) (p : Node) (i : Nat) :
    P (x[i][p].st) := by
  induction i with
  | zero =>
      have hn : x[0][p] = { clock := 0, st := protocol.init p, view := ∅ } := x.init.2.1 p
      rw [hn]
      exact hgen
  | succ i ih =>
      refine Step.elim (motive := fun _ c c' => P (c[p].st) → P (c'[p].st)) (x.step i)
        (fun d t h => h) ?tick ?deliver ?wake
        (fun d q ev res he hp => ev.elim) (fun d q m he h => h) ih
      case tick =>
        intro d q t res he hp h
        have hres : res = reaction ((setClock q t d)[q].st) .tick := hp
        by_cases hqp : q = p
        · subst hqp
          rw [applyNodeStepResult_st_self, hres, setClock_st]
          exact h
        · rw [applyNodeStepResult_st_other hqp, setClock_st]
          exact h
      case deliver =>
        intro d q m res he hp h
        have hres : res = reaction ((Framework.StsMultisetLog.receive q m d)[q].st) (.recv m) := hp
        by_cases hqp : q = p
        · subst hqp
          rw [applyNodeStepResult_st_self, hres, receive_st]
          exact hrecv (d[q].st) m.msg h
        · rw [applyNodeStepResult_st_other hqp, receive_st]
          exact h
      case wake =>
        intro d q res he hp h
        have hres : res = reaction (d[q].st) .wake := hp
        by_cases hqp : q = p
        · subst hqp
          rw [applyNodeStepResult_st_self, hres]
          exact h
        · rw [applyNodeStepResult_st_other hqp]
          exact h

/-- Theorem 4 (`hft:thm:fleqr`): the walker at `P S := S.F ⪯ S.J`, with the genesis store
    supplying reflexivity. -/
theorem fPreceqJ {sched : Schedule Node}
    (x : Exec (protocol (Node := Node) (Root := Root)) sched) (p : Node) (i : Nat) :
    (x[i][p].st).F ⪯ (x[i][p].st).J :=
  exec_node_invariant (P := fun S => S.F ⪯ S.J)
    (fun _ m h => receiveMsg_FJ m h) (Preceq.refl _) x p i

/-- Theorem 4 in the reachability vocabulary: obtain the step and read the invariant. -/
theorem reaches_FJ {sched : Schedule Node}
    {x : Exec (protocol (Node := Node) (Root := Root)) sched} {p : Node}
    {S : Store Node Root} (h : Reaches x p S) : S.F ⪯ S.J := by
  obtain ⟨i, rfl⟩ := h
  exact fPreceqJ x p i


/-- `ReachesFrom` reaches its later store. -/
theorem reaches_of_reachesFrom {sched : Schedule Node}
    {x : Exec (protocol (Node := Node) (Root := Root)) sched} {p : Node}
    {S S' : Store Node Root} (h : ReachesFrom x p S S') : Reaches x p S' := by
  obtain ⟨i, j, hij, hS, hS'⟩ := h
  exact ⟨j, hS'⟩

/-- Theorem 7 (`hft:thm:fcconsistency`): `S.F ⪯ S'.F ⪯ S'.J`, and both branches of the
    walk-from cascade start at or above `S'.F`. -/
theorem forkChoiceConsistency {sched : Schedule Node}
    {x : Exec (protocol (Node := Node) (Root := Root)) sched} {p : Node}
    {S S' : Store Node Root} (h : ReachesFrom x p S S')
    {C : Blk Node Root} (hC : GetConfirmed S' C) :
    S.F ⪯ C :=
  Preceq.trans (reachesFrom_F h) (getConfirmed_F (reaches_FJ (reaches_of_reachesFrom h)) hC)

/-- The bridge over executions: whatever a held store records is the block's replay. -/
theorem reaches_recorded {sched : Schedule Node}
    {x : Exec (protocol (Node := Node) (Root := Root)) sched} {p : Node}
    {S : Store Node Root} (hS : Reaches x p S)
    {B : Blk Node Root} {σB : ChainState Node Root} (hB : S.σ B = some σB) :
    postState B = .state σB := by
  obtain ⟨i, rfl⟩ := hS
  exact exec_node_invariant
    (P := fun S => ∀ B σB, S.σ B = some σB → postState B = .state σB)
    (fun S m h => receiveMsg_recorded m h) gen_recorded x p i B σB hB

end Exec

end Proofs

end Decoupled
