import Proofs.Instance.Model
import Proofs.Instance.Facts.GradesRun

/-!
# The run invariant along the steps, at `Model.spec`

Proofs of the fields of the record that say which node states, stores and caches a run reaches, at
`Model.spec`. There a node state is reached when its store has the run invariant `Inv`:
`RunStoreInv`, `ConfirmedInTree`, and the saved grades holding tree blocks only.
-/

set_option autoImplicit false

namespace SpecRecord.Reached

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open SpecRecord.NoRaise
open SpecRecord.GradesRunFacts
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- `Inv st`: the run invariant of the spec's store `st`: its justified block and chain states name
    tree blocks and nothing is held off the tree, its three confirmation records are tree blocks,
    and its saved grades hold tree blocks. -/
def Inv (st : Spec.Store V) : Prop :=
  SubtypeEqualities.RunStoreInv st ∧ HandlersRunFacts.ConfirmedInTree st ∧
    Spec.Store.ContractInTree st.T st.saved_grades

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- Saved grades whose blocks are blocks of `T` satisfy the claim that every computed result's block
    is a block of `T`. -/
theorem claim_of_contractInTree {T : Finset (Spec.Block V)}
    {c : Spec.SavedGrades V} (h : Spec.Store.ContractInTree T c) :
    CacheClaim c (fun _ _ G => ∀ g, G = some g → g ∈ T) := by
  have key : ∀ (r : Round) (f : Spec.RoundGrades V), f ∈ [c.current, c.next] →
      FrameClaim r f (fun _ _ G => ∀ g, G = some g → g ∈ T) := by
    intro r f hf p G hG g hg
    subst hg
    have hmem : res f p ∈ [f.g0, f.g1, f.g2] := by
      cases p <;> simp [res, Spec.Protocol.phaseResult,
        Spec.Protocol.Phase.toSpec]
    exact h f hf (res f p) hmem g hG
  exact ⟨key _ _ (by simp), key _ _ (by simp)⟩

/-- Every store that a sequence of steps leads to, from a store of the store type with the run
    invariant and its three confirmation records in its tree, has them too when its tree has
    distinct roots. -/
theorem inv_reach {C : Spec.Config} {P : Spec.Provisional V} {τ : Time}
    {st st' : Spec.Store V} (h : StoreSteps.StoreReach C P τ st st')
    (hd : DistinctRoots st'.T)
    (hq : StoreOk st ∧ SubtypeEqualities.RunStoreInv st ∧ HandlersRunFacts.ConfirmedInTree st) :
    StoreOk st' ∧ SubtypeEqualities.RunStoreInv st' ∧ HandlersRunFacts.ConfirmedInTree st' :=
  HandlersRunFacts.reach_induction_ok
    (fun st => StoreOk st ∧ SubtypeEqualities.RunStoreInv st ∧ HandlersRunFacts.ConfirmedInTree st)
    (fun a b hs hd' q => by
    obtain ⟨hb1, hb2⟩ := HandlersRunFacts.base_step hs hd' ⟨q.1, q.2.1⟩
    exact ⟨hb1, hb2, HandlersRunFacts.confirmedInTree_step hs q.1 q.2.1 q.2.2⟩) h hd hq

/-- After a tick of `Model.spec`, the saved grades hold blocks of the tree, when they did
    before. -/
theorem contractInTree_tick (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
    (out : (Model.spec (V := V)).N × List (NamedObject V))
    (hout : (Model.spec (V := V)).tick S v n t ⇢ out)
    (h : Spec.Store.ContractInTree n.val.st.T n.val.st.saved_grades) :
    Spec.Store.ContractInTree out.1.val.st.T out.1.val.st.saved_grades := by
  obtain ⟨st0, hupd, hsg⟩ := tick_saved (v := v) (out := (out.1.val, out.2)) hout
  have hmem := memClaim_update_grades n.property hupd (claim_of_contractInTree h)
  have hT : n.val.st.T ⊆ out.1.val.st.T :=
    reach_T_subset (HandlersRunFacts.spec_tick_reach S v n t out hout)
  apply contractInTree_of_claim
  rw [hsg]
  refine cacheClaim_clip _ _ _ _ hmem (fun r p G hG g hg => ?_)
  cases G with
  | none => cases hg
  | some g₀ =>
    cases hg
    exact dca_mem _ out.1.property.2.2.1 _ _ (hT (hG g₀ rfl))

/-- After a receipt of `Model.spec`, the saved grades hold blocks of the tree, when they did
    before. -/
theorem contractInTree_process (S : Setup V) (n : (Model.spec (V := V)).N)
    (o : NamedObject V) (n' : (Model.spec (V := V)).N)
    (hn' : (Model.spec (V := V)).process S n o ⇢ n')
    (h : Spec.Store.ContractInTree n.val.st.T n.val.st.saved_grades) :
    Spec.Store.ContractInTree n'.val.st.T n'.val.st.saved_grades := by
  have he : n'.val = receiveNamedObject S n.val o :=
    (NodeFacts.process_returns_iff S n.val n'.val o).mp hn'
  have hk := NodeFacts.keeps_receipt_process S n.val.st o
  have hst : n'.val.st = Spec.make_grades_compatible_with_finalized
      (Member.receipt_process S n.val.st o) := by
    rw [he, NodeFacts.receiveNamedObject_eq]
  have hsg : n'.val.st.saved_grades = Spec.Protocol.make_saved_grades_compatible_with
      n'.val.st.F n.val.st.saved_grades := by
    rw [hst, ← hk.2.2.2.2.1]
    rfl
  have hT : n.val.st.T ⊆ n'.val.st.T := by
    rw [hst]
    exact hk.2.2.1
  apply contractInTree_of_claim
  rw [hsg]
  refine cacheClaim_clip _ _ _ _ (claim_of_contractInTree h) (fun r p G hG g hg => ?_)
  cases G with
  | none => cases hg
  | some g₀ =>
    cases hg
    exact dca_mem _ n'.property.2.2.1 _ _ (hT (hG g₀ rfl))

/-- A tick of `Model.spec` keeps the run invariant `Inv` of the node's store. -/
theorem inv_tick (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
    (out : (Model.spec (V := V)).N × List (NamedObject V))
    (hout : (Model.spec (V := V)).tick S v n t ⇢ out) (h : Inv n.val.st) :
    Inv out.1.val.st := by
  obtain ⟨-, h1, h2⟩ := inv_reach (HandlersRunFacts.spec_tick_reach S v n t out hout)
    out.1.property.2.1 ⟨n.property, h.1, h.2.1⟩
  exact ⟨h1, h2, contractInTree_tick S v n t out hout h.2.2⟩

/-- A receipt of `Model.spec` keeps the run invariant `Inv` of the node's store. -/
theorem inv_process (S : Setup V) (n : (Model.spec (V := V)).N) (o : NamedObject V)
    (n' : (Model.spec (V := V)).N) (hn' : (Model.spec (V := V)).process S n o ⇢ n')
    (h : Inv n.val.st) : Inv n'.val.st := by
  obtain ⟨-, h1, h2⟩ := inv_reach (HandlersRunFacts.spec_process_reach S n n' o hn' 0)
    n'.property.2.1 ⟨n.property, h.1, h.2.1⟩
  exact ⟨h1, h2, contractInTree_process S n o n' hn' h.2.2⟩

omit [Fintype V] [Inhabited V] in
/-- The spec's initial store has the run invariant `Inv`. -/
theorem inv_init : Inv (Spec.Store.init : Spec.Store V) := by
  refine ⟨SubtypeEqualities.runStoreInv_init, HandlersRunFacts.confirmedInTree_init, ?_⟩
  intro fr hfr g hg G hG
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfr hg
  rcases hfr with rfl | rfl <;> rcases hg with rfl | rfl | rfl <;>
    simp [Spec.Store.init, Spec.Protocol.initial_saved_grades,
      Spec.Protocol.empty_round_grades,
      Spec.Protocol.pending_round_grades] at hG

end SpecRecord.Reached

namespace DecoupledConsensusModel.Sts.Record

open SpecRecord

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

section NodeFacts

open DecoupledConsensusModel.Execution
open scoped DC

/-- The field `stateBeforeOf_reachedNode` of `NodeRunFacts` at `Model.spec`: for every world
    `w` the run `rho` holds before its `i`-th event, `v`'s node state `w v` is one a run reaches. -/
theorem _root_.SpecRecord.NodeRunFacts.spec_stateBeforeOf_reachedNode :
    ∀ (S : Setup V) (rho : Record.Run V) (i : Nat) (w : V → (Model.spec (V := V)).N)
      (hw : w ∈ stateBeforeOf (Model.spec (V := V)) S rho i) (v : V), (Model.spec (V := V)).reachedNode (w v) := by
  intro S rho i w hw v
  exact (HandlersRunFacts.fold_relation_sub S Reached.Inv (fun _ _ => True) (fun _ => trivial)
    (fun _ _ _ _ _ => trivial) (rho.events.take i)
    (fun p t _ n out hout hq => ⟨Reached.inv_tick S p n t out hout hq, trivial⟩)
    (fun n o n' h hq => ⟨Reached.inv_process S n o n' h hq, trivial⟩)
    (fun u => (Model.spec (V := V)).initial S u) (fun _ => Reached.inv_init) w hw v).1

/-- The field `reachedNode_initial` of `NodeFacts` at `Model.spec`: every initial node state is
    one a run reaches. -/
theorem _root_.SpecRecord.NodeFacts.spec_reachedNode_initial :
    ∀ (S : Setup V) (v : V), (Model.spec (V := V)).reachedNode ((Model.spec (V := V)).initial S v) := by
  intro S v
  exact Reached.inv_init

/-- The field `reachedNode_wake` of `NodeFacts` at `Model.spec`: if a run reaches `n`, it
    reaches `n`'s wake. -/
theorem _root_.SpecRecord.NodeFacts.spec_reachedNode_wake :
    ∀ (n : (Model.spec (V := V)).N), (Model.spec (V := V)).reachedNode n → (Model.spec (V := V)).reachedNode ((Model.spec (V := V)).wake n) := by
  intro n h₁
  show Reached.Inv ((Model.spec (V := V)).wake n).val.st
  rw [HandlersRunFacts.spec_wake_st]
  exact h₁

/-- The field `reachedNode_tick` of `NodeFacts` at `Model.spec`: if a run reaches `n`, it
    reaches the node state of every outcome of `v`'s tick at `t` from `n`. -/
theorem _root_.SpecRecord.NodeFacts.spec_reachedNode_tick :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time) (out : (Model.spec (V := V)).N × List (NamedObject V)),
      (Model.spec (V := V)).tick S v n t ⇢ out → (Model.spec (V := V)).reachedNode n → (Model.spec (V := V)).reachedNode out.1 := by
  intro S v n t out h₁ h₂
  exact Reached.inv_tick S v n t out h₁ h₂

/-- The field `reachedNode_process` of `NodeFacts` at `Model.spec`: if a run reaches `n`, it
    reaches every node state `n`'s receipt of `o` can return. -/
theorem _root_.SpecRecord.NodeFacts.spec_reachedNode_process :
    ∀ (S : Setup V) (n : (Model.spec (V := V)).N) (o : NamedObject V) (n' : (Model.spec (V := V)).N),
      (Model.spec (V := V)).process S n o ⇢ n' → (Model.spec (V := V)).reachedNode n → (Model.spec (V := V)).reachedNode n' := by
  intro S n o n' h₁ h₂
  exact Reached.inv_process S n o n' h₁ h₂

/-- The field `reachedStore_of_node` of `NodeFacts` at `Model.spec`: the named store of a
    reached node state is reached. -/
theorem _root_.SpecRecord.NodeFacts.spec_reachedStore_of_node :
    ∀ (n : (Model.spec (V := V)).N), (Model.spec (V := V)).reachedNode n → (Model.spec (V := V)).reachedStore n.st := by
  intro n h₁
  exact h₁

/-- The field `reachedCore_of_store` of `NodeFacts` at `Model.spec`: the core store of a
    reached named store is reached. -/
theorem _root_.SpecRecord.NodeFacts.spec_reachedCore_of_store :
    ∀ (st : (Model.spec (V := V)).NS), (Model.spec (V := V)).reachedStore st → (Model.spec (V := V)).reachedCore st.core := by
  intro st h₁
  exact h₁

/-- The field `reachedRead_of_node` of `NodeFacts` at `Model.spec`: the store of a reached node
    state, read as a healing store, with its grade cache, is a pair a run reaches. -/
theorem _root_.SpecRecord.NodeFacts.spec_reachedRead_of_node :
    ∀ (n : (Model.spec (V := V)).N), (Model.spec (V := V)).reachedNode n → (Model.spec (V := V)).reachedRead n.st.core.toHealing n.cache := by
  intro n h₁
  exact h₁

end NodeFacts

section StoreFacts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- The field `reachedStore_setClock` of `StoreFacts` at `Model.spec`: setting the clock of a
    reached named store gives a reached named store. -/
theorem _root_.SpecRecord.StoreFacts.spec_reachedStore_setClock :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Time),
      (Model.spec (V := V)).reachedStore st → (Model.spec (V := V)).reachedStore ((Model.spec (V := V)).ns_setClock E st t) := by
  intro E st t h₁
  exact h₁

end StoreFacts

end DecoupledConsensusModel.Sts.Record
