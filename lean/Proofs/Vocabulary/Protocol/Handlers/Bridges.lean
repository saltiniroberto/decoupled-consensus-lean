module
public import Proofs.Vocabulary.Execution.NamedAncestry
public import Proofs.Vocabulary.Internal.Definitions.Evidence
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Admissible
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run
import Proofs.Vocabulary.Execution.Wire
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

/-!
# Run-level facts for the store invariants

Root collision freedom restricted to the bodies held by honest nodes, the agreement between reads by
time and reads by event prefix, and the deliveries behind the run's object list.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace Bridges

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Run-wide root collision freedom -/

/-- A named body an honest node holds at a state of the run is a block of the run. -/
theorem runBlock_of_stateBefore_mem (S : Setup V) {ρ : Run V} {v : V}
    (hv : v ∈ ρ.honest) {i : Nat} {C : NamedBlock V}
    (hC : C ∈ (ρ.stateBefore S i v).st.bodies) : RunBlock S ρ C :=
  ⟨C, Or.inr ⟨v, hv, i, hC⟩, Proofs.NamedAncestry.named_self C⟩

/-- Under `RootCollisionFree`, the erasures of a finite set of named blocks of the run satisfy
    `RootInjectiveBelow`. -/
theorem rootInjectiveBelow_of_runBlocks (S : Setup V) {ρ : Run V}
    (hcf : RootCollisionFree S ρ) {T : Finset (NamedBlock V)}
    (hRun : ∀ C ∈ T, RunBlock S ρ C) :
    RootInjectiveBelow (T.image NamedBlock.erase) := by
  intro A C hA hC hr
  obtain ⟨B, hBT, hAB⟩ := hA
  obtain ⟨D, hDT, hCD⟩ := hC
  obtain ⟨B', hB'T, rfl⟩ := Finset.mem_image.mp hBT
  obtain ⟨D', hD'T, rfl⟩ := Finset.mem_image.mp hDT
  obtain ⟨A', hA'B, rfl⟩ := Proofs.NamedAncestry.erased_ancestor_lift B' hAB
  obtain ⟨C', hC'D, rfl⟩ := Proofs.NamedAncestry.erased_ancestor_lift D' hCD
  have hroots : A'.root = C'.root := by
    rwa [Proofs.NamedWire.erase_root, Proofs.NamedWire.erase_root] at hr
  rw [RootCollisionFree.root_injective hcf B' D' (hRun B' hB'T) (hRun D' hD'T) A' C'
    (Or.inl hA'B) (Or.inr hC'D) hroots]


/-- Under `RootCollisionFree`, the erasures of the bodies held by two honest nodes satisfy
    `RootInjectiveBelow`. -/
theorem rootInjectiveBelow_stateBefore_union (S : Setup V) {ρ : Run V}
    (hcf : RootCollisionFree S ρ) {u v : V}
    (hu : u ∈ ρ.honest) (hv : v ∈ ρ.honest) (i j : Nat) :
    RootInjectiveBelow
      (((ρ.stateBefore S i u).st.bodies ∪
        (ρ.stateBefore S j v).st.bodies).image NamedBlock.erase) :=
  rootInjectiveBelow_of_runBlocks S hcf (by
    intro C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · exact runBlock_of_stateBefore_mem S hu hC
    · exact runBlock_of_stateBefore_mem S hv hC)

/-! ## Reads by time and by event prefix -/

/-- Filtering a sorted list by a predicate inherited backwards along the order gives the list's
    `takeWhile`. -/
theorem filter_eq_takeWhile_of_pairwise {α : Type} {R : α → α → Prop} {p : α → Bool}
    (hdc : ∀ a b : α, R a b → p b = true → p a = true) :
    ∀ l : List α, l.Pairwise R → l.filter p = l.takeWhile p := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
      intro hp
      rw [List.pairwise_cons] at hp
      by_cases ha : p a = true
      · rw [List.filter_cons_of_pos ha, List.takeWhile_cons_of_pos ha, ih hp.2]
      · rw [List.filter_cons_of_neg ha, List.takeWhile_cons_of_neg ha]
        refine List.filter_eq_nil_iff.mpr ?_
        intro b hb hpb
        exact ha (hdc a b (hp.1 b hb) hpb)

/-- Folding the events that pass a filter inherited backwards along the key order gives the state
    after a prefix of the events, all of which pass the filter. -/
theorem filtered_fold_eq_stateBefore (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) {p : Event V → Bool}
    (hdc : ∀ e f : Event V, NamedEvent.key e ≤ NamedEvent.key f → p f = true → p e = true) :
    ∃ n : Nat, (ρ.events.filter p).foldl (World.step S) World.init = ρ.stateBefore S n ∧
      ∀ (j : Nat) (e : Event V), j < n → ρ.events[j]? = some e → p e = true := by
  have hpref : ρ.events.filter p <+: ρ.events := by
    rw [filter_eq_takeWhile_of_pairwise hdc _ sch.sorted]
    exact List.takeWhile_prefix p
  have hpre : ρ.events.filter p = ρ.events.take (ρ.events.filter p).length :=
    List.prefix_iff_eq_take.mp hpref
  refine ⟨(ρ.events.filter p).length, ?_, ?_⟩
  · conv_lhs => rw [hpre]
    rfl
  · intro j e hj hget
    have hmem : e ∈ ρ.events.filter p := by
      rw [hpre]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact hget)
    exact (List.mem_filter.mp hmem).2

/-- `filtered_fold_eq_stateBefore`, assuming only that the events are sorted by key. -/
theorem filtered_fold_eq_stateBefore_of_sorted (S : Setup V) {ρ : Run V}
    (sorted : ρ.events.Pairwise (fun e f => NamedEvent.key e ≤ NamedEvent.key f))
    {p : Event V → Bool}
    (hdc : ∀ e f : Event V, NamedEvent.key e ≤ NamedEvent.key f → p f = true → p e = true) :
    ∃ n : Nat, (ρ.events.filter p).foldl (World.step S) World.init = ρ.stateBefore S n ∧
      ∀ (j : Nat) (e : Event V), j < n → ρ.events[j]? = some e → p e = true := by
  have hpref : ρ.events.filter p <+: ρ.events := by
    rw [filter_eq_takeWhile_of_pairwise hdc _ sorted]
    exact List.takeWhile_prefix p
  have hpre : ρ.events.filter p = ρ.events.take (ρ.events.filter p).length :=
    List.prefix_iff_eq_take.mp hpref
  refine ⟨(ρ.events.filter p).length, ?_, ?_⟩
  · conv_lhs => rw [hpre]
    rfl
  · intro j e hj hget
    have hmem : e ∈ ρ.events.filter p := by
      rw [hpre]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact hget)
    exact (List.mem_filter.mp hmem).2

omit [DecidableEq V] [Fintype V] in
/-- The key order refines the time order. -/
theorem time_le_of_key_le {e f : Event V}
    (h : NamedEvent.key e ≤ NamedEvent.key f) : e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with h' | ⟨h', _⟩
  · exact le_of_lt h'
  · exact le_of_eq h'

/-- The read before `t` is the state after a prefix of the events, all of which are before `t`. -/
theorem stateBeforeTime_eq_stateBefore (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) (t : Time) :
    ∃ n : Nat, ρ.stateBeforeTime S t = ρ.stateBefore S n ∧
      ∀ (j : Nat) (e : Event V), j < n → ρ.events[j]? = some e → e.time < t :=
  (filtered_fold_eq_stateBefore S sch
    (p := fun e => decide (e.time < t))
    (fun e f hk hf => by
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (time_le_of_key_le hk) hf)).imp fun _ h =>
    ⟨h.1, fun j e hj hget => by simpa using h.2 j e hj hget⟩


/-! ## Blocks of the run's object list -/

omit [DecidableEq V] [Fintype V] in
/-- A block in the run's object list is carried by some delivery. -/
theorem exists_deliver_of_mem_objects (ρ : Run V) {B : NamedBlock V}
    (h : Object.block B ∈ NamedRun.objects ρ) :
    ∃ (i : Nat) (u : V) (t : Time),
      ρ.events[i]? = some (Event.deliver u (Object.block B) t) := by
  obtain ⟨e, hmem, he⟩ := List.mem_filterMap.mp h
  cases e with
  | tick u t => simp only [NamedEvent.object?, reduceCtorEq] at he
  | deliver u o t =>
      simp only [NamedEvent.object?, Option.some.injEq] at he
      subst he
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hmem
      exact ⟨i, u, t, hi⟩

end Bridges
end Proofs


end DecoupledConsensusModel

end
