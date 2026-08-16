import Analysis.Proofs.Irreversibility

/-!
# Theorem 4, and the walker every store invariant will use

Two things live here. First, `exec_node_invariant`: a store predicate that holds at the
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
statement of record used to be, kept because the store-level Theorems 7–10 will want it.
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

end Exec

end Proofs

end Decoupled
