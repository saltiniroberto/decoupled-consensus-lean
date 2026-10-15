import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Projection
import Model.Record.Wiring
import Proofs.Claims.SynchronyH

/-!
# Views and exclusion along the sts execution

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: a message enters
a validator's view only by a delivery to it, and a store whose finalized block is compatible with a
block was so at every earlier step.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If a message is in `p`'s view after a step and was not there before, that step delivered exactly
    that message to `p`. -/
theorem mem_view_step (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    {a : AtomicAction V (NamedObject V) Empty}
    {cfg cfg' : Config V (NamedObject V) (M.N)}
    (hs : AtomicStep (Record.protocolOf M S) Sched a cfg cfg') {p : V}
    {sm : SignedMsg V (NamedObject V)} (h : sm ∈ cfg'[p].view) :
    sm ∈ cfg[p].view ∨ a = AtomicAction.deliver p sm := by
  classical
  refine AtomicStep.elim
    (motive := fun a d d' =>
      sm ∈ d'[p].view → sm ∈ d[p].view ∨ a = AtomicAction.deliver p sm)
    hs ?_ ?_ ?_ ?_ ?_ h
  · intro d t w tk _ _ _ hh
    rw [tickAllAwakeUpdate_getElem_view] at hh
    exact Or.inl hh
  · intro d q m res _ _ hh
    rw [applyNodeStepResult_view] at hh
    by_cases hq : q = p
    · subst hq
      rw [receive_view_self] at hh
      rcases Finset.mem_insert.1 hh with rfl | hh
      · exact Or.inr rfl
      · exact Or.inl hh
    · rw [show (receive q m d)[p] = d[p] from by rw [receive_getElem, if_neg hq]] at hh
      exact Or.inl hh
  · intro d q ev res _ _ hh
    rw [applyNodeStepResult_view] at hh
    exact Or.inl hh
  · intro d q m _ hh
    exact Or.inl hh
  · intro d q m _ hh
    exact Or.inl hh

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A message in `p`'s view after `i` steps was delivered to `p` at some step `k < i`. -/
theorem deliver_of_mem_view (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {p : V} {sm : SignedMsg V (NamedObject V)} :
    ∀ i : Nat, sm ∈ x[i][p].view → ∃ k < i, x.lbl k = AtomicAction.deliver p sm
  | 0, h => by
      have h0 := x.init.2.1 p
      rw [show (x[0] : Config V (NamedObject V) (M.N)) = x.cfg 0 from rfl] at h
      rw [h0] at h
      exact absurd h (by simp)
  | i + 1, h => by
      rcases Restated.mem_view_step facts S Sched (x.step i) h with h' | h'
      · obtain ⟨k, hk, hlbl⟩ := deliver_of_mem_view facts S Sched x i h'
        exact ⟨k, Nat.lt_succ_of_lt hk, hlbl⟩
      · exact ⟨i, Nat.lt_succ_self i, h'⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the finalized block of `v`'s store after `j` steps is compatible with the erasure of `B`, so
    is the finalized block of `v`'s store after any `i ≤ j` steps. -/
theorem excludes_mono_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) {i j : Nat} (hij : i ≤ j)
    {B : NamedBlock V} (h : Block.compatible (x[j][v].st).st.core.F B.erase = true) :
    Block.compatible (x[i][v].st).st.core.F B.erase = true :=
  compatible_of_preceq_left (Restated.F_mono facts S Sched x v hij) h

end

end DecoupledConsensusModel.Sts.Restated
