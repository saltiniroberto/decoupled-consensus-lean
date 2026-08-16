import StsMultisetLog.Analysis.Lemmas
import StsMultisetLog.Spec.Execution
import Spec.Protocol
import Analysis.Vocabulary
import Analysis.Proofs.Ancestry

/-!
# Theorem 3: the store-finalized block only ever descends

The proof of `thmLocalIrreversibility` (Theorem 3, `hft:thm:finperm`), in three layers:

* **Configuration read-backs** — what each framework write does to a node's `st`, one
  lemma per writer (`applyNodeStepResult`, `setClock`, the framework's `receive`). Each is
  the framework's own `_getElem` read-back with the `if` discharged; the framework states
  `clock`/`view` projections but not `st`, so these live here.
* **Store layer** — `F` moves only inside `update_finalized`, whose condition
  `F' ≻ Σ.F` hands the proof exactly the `⪯` it needs; every other branch of `on_block`
  leaves `F` untouched, so `onBlock_F` falls to `repeat' split` with two closers. The fold
  (`onBlocks_F`) is the store-level core Theorem 3's docstring names — an arbitrary store,
  no reachability.
* **Execution layer** — `Step.elim` hands each action a concrete successor. The reacting
  cases re-ascribe `protocol.step` to its definition (`res = reaction … e`, a defeq
  re-ascription per the `lean-proof-idioms` skill), split on whether the reacting
  validator is the observed one, and reduce: `tick`/`wake` reactions keep the state,
  `recv` folds the message through `Decoupled.receive`, `custom` is `Empty`, and
  `advance`/`adversarial` never touch a node. The walk from `i` to `j` is
  `Nat.le_induction` over the per-step fact.

One shape worth naming: `updates_F` takes `S₀.F = S.F` as a hypothesis discharged by
`rfl` at the use site, because inside `on_block`'s accept branch the store is a record
update whose `.F` is definitionally the original's — passing the equality avoids the
unifier picking the wrong store for the motive (the metavariable trap the skill records).
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

/-! ## What each framework write does to a node's `st` -/

section Config
variable {N M NS : Type} [DecidableEq N]

/-- The reacting node's state afterwards is the reaction's. -/
theorem applyNodeStepResult_st_self (q : N) (res : NodeStepResult NS M)
    (d : Config N M NS) : (applyNodeStepResult q res d)[q].st = res.state := by
  rw [applyNodeStepResult_getElem, if_pos rfl]

/-- Any other node's state is untouched. -/
theorem applyNodeStepResult_st_other {q p : N} (h : q ≠ p) (res : NodeStepResult NS M)
    (d : Config N M NS) : (applyNodeStepResult q res d)[p].st = d[p].st := by
  rw [applyNodeStepResult_getElem, if_neg h]

/-- A clock write touches no node's state. -/
theorem setClock_st (q p : N) (t : Time) (d : Config N M NS) :
    (setClock q t d)[p].st = d[p].st := by
  rw [setClock_getElem]; split_ifs with h
  · subst h; rfl
  · rfl

/-- Filing a message into a view touches no node's state. -/
theorem receive_st [DecidableEq M] (q p : N) (m : SignedMsg N M) (d : Config N M NS) :
    (Framework.StsMultisetLog.receive q m d)[p].st = d[p].st := by
  rw [receive_getElem]; split_ifs with h
  · subst h; rfl
  · rfl

end Config

/-! ## The store layer: `F` only ever descends -/

section Store
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

omit [Electorate Node] [Params] in
/-- `update_justified` never writes `F`. -/
theorem updateJustified_F (S : Store Node Root) (J' : Blk Node Root) (h' : Nat) :
    (updateJustified S J' h').F = S.F := by
  simp only [updateJustified, Id.run]
  split_ifs <;> rfl

omit [Electorate Node] [Params] [BlockHash Node Root] in
/-- `update_finalized` moves `F` only to a strict descendant — its own condition
    `F' ≻ Σ.F` is the `⪯` the conclusion needs. -/
theorem updateFinalized_F (S : Store Node Root) (F' : Blk Node Root) :
    S.F ⪯ (updateFinalized S F').F := by
  simp only [updateFinalized, Id.run]
  split_ifs with h
  · exact h.1.1
  · exact Preceq.refl _

omit [Electorate Node] [Params] in
/-- The two updates in `on_block`'s order, from any store whose `F` agrees with `S₀`'s.
    The hypothesis is discharged by `rfl` at the use site — see the module header. -/
theorem updates_F {S₀ S : Store Node Root} (hF : S₀.F = S.F)
    {J' F' : Blk Node Root} {h' : Nat} :
    S₀.F ⪯ (updateFinalized (updateJustified S J' h') F').F := by
  rw [hF]
  have h := updateFinalized_F (updateJustified S J' h') F'
  rwa [updateJustified_F] at h

/-- `on_block` only ever extends `F`: a rejected block leaves the store unchanged, and an
    accepted one routes `F` through the two updates. -/
theorem onBlock_F (S : Store Node Root) (B : Blk Node Root) :
    S.F ⪯ (onBlock S B).F := by
  simp only [onBlock, Id.run]
  repeat' split
  all_goals first
    | exact Preceq.refl _
    | exact updates_F rfl

/-- The fold: Theorem 3's store-level core, over an arbitrary store. -/
theorem onBlocks_F (S : Store Node Root) (Bs : List (Blk Node Root)) :
    S.F ⪯ (onBlocks S Bs).F := by
  induction Bs generalizing S with
  | nil => exact Preceq.refl _
  | cons B Bs ih => exact Preceq.trans (onBlock_F S B) (ih (onBlock S B))

/-- Receipt of any store message only ever extends `F` — today, by `onBlock_F`. -/
theorem receiveMsg_F (S : Store Node Root) (m : StoreMsg Node Root) :
    S.F ⪯ (Decoupled.receive S m).F := by
  cases m with
  | block B => exact onBlock_F S B

end Store

/-! ## The execution layer -/

section Exec
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-- One step of any execution: a validator's store-finalized block only ever descends. -/
theorem exec_step_F {sched : Schedule Node}
    (x : Exec (protocol (Node := Node) (Root := Root)) sched) (p : Node) (i : Nat) :
    (x[i][p].st).F ⪯ (x[i + 1][p].st).F := by
  refine Step.elim (motive := fun _ c c' => (c[p].st).F ⪯ (c'[p].st).F) (x.step i)
    (fun d t => Preceq.refl _) ?tick ?deliver ?wake
    (fun d q ev res he hp => ev.elim) (fun d q m he => Preceq.refl _)
  case tick =>
    intro d q t res he hp
    have hres : res = reaction ((setClock q t d)[q].st) .tick := hp
    by_cases hqp : q = p
    · subst hqp
      rw [applyNodeStepResult_st_self, hres, setClock_st]
      exact Preceq.refl _
    · rw [applyNodeStepResult_st_other hqp, setClock_st]
      exact Preceq.refl _
  case deliver =>
    intro d q m res he hp
    have hres : res = reaction ((Framework.StsMultisetLog.receive q m d)[q].st) (.recv m) := hp
    by_cases hqp : q = p
    · subst hqp
      rw [applyNodeStepResult_st_self, hres, receive_st]
      exact receiveMsg_F (d[q].st) m.msg
    · rw [applyNodeStepResult_st_other hqp, receive_st]
      exact Preceq.refl _
  case wake =>
    intro d q res he hp
    have hres : res = reaction (d[q].st) .wake := hp
    by_cases hqp : q = p
    · subst hqp
      rw [applyNodeStepResult_st_self, hres]
      exact Preceq.refl _
    · rw [applyNodeStepResult_st_other hqp]
      exact Preceq.refl _

/-- Theorem 3 (`hft:thm:finperm`): the walk from `i` to `j`, `Nat.le_induction` over
    `exec_step_F`. -/
theorem localIrreversibility {sched : Schedule Node}
    (x : Exec (protocol (Node := Node) (Root := Root)) sched)
    (p : Node) {i j : Nat} (hij : i ≤ j) :
    (x[i][p].st).F ⪯ (x[j][p].st).F := by
  induction j, hij using Nat.le_induction with
  | base => exact Preceq.refl _
  | succ j hij ih => exact Preceq.trans ih (exec_step_F x p j)

end Exec

end Proofs

end Decoupled
