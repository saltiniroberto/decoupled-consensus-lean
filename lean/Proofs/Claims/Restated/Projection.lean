import Proofs.Claims.Projection
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_FinalizationBridge
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Ticks, finalized blocks and bodies along the sts execution

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: the tick
reactions of the wiring, the finalized block of a validator moving to descendants along the
execution, the named block that carries it, the erased tree as the image of the bodies, and root
injectivity for the blocks in play.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- At an instant that is a whole multiple of `S.E.Δ`, the tick reactions of the wiring are exactly
    those that pass on the state and the sent objects of an outcome of the model's tick. -/
theorem reaction_tick_of_emod (facts : Record.Facts M) (S : Setup V) (p : V) (n : M.N) {t : Int}
    (ht : t % S.E.Δ = 0) :
    Record.reactionsOf M S p n t Event.tick
      = { res | ∃ out₁, M.tick (Setup.alwaysAwake S) p n t ⇢ out₁ ∧
          res = { state := out₁.1,
                  send := (out₁.2 : Multiset (NamedObject V)) } } := by
  simp only [Record.reactionsOf, if_pos ht]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- At an instant that is not a whole multiple of `S.E.Δ`, the one tick reaction of the wiring keeps
    the state and sends nothing. -/
theorem reaction_tick_of_not_emod (facts : Record.Facts M) (S : Setup V) (p : V) (n : M.N) {t : Int}
    (ht : ¬ t % S.E.Δ = 0) :
    Record.reactionsOf M S p n t Event.tick = { { state := n, send := 0 } } := by
  simp only [Record.reactionsOf, if_neg ht]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The finalized block `v` holds after `i` steps is an ancestor of the one it holds after `i + 1`
    steps. -/
theorem F_mono_succ (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (i : Nat) :
    Block.Preceq (x[i][v].st).st.core.F (x[i + 1][v].st).st.core.F := by
  rcases Record.st_succ_cases M S Sched x v i with h | h | ⟨t, out, hres | hres, h⟩ | ⟨o, h⟩
  · rw [h]
    exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)
  · rw [h, (facts.nd.wake_st_record _).1]
    exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)
  · rw [h]
    exact facts.nd.node_tick_F (Setup.alwaysAwake S) v _ t out hres
  · rw [h]
    have hF := facts.nd.node_tick_F (Setup.alwaysAwake S) v _ t out hres
    rw [(facts.nd.wake_st_record _).1] at hF
    exact hF
  · exact facts.nd.node_process_F (Setup.alwaysAwake S) _ o _ h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For `i ≤ j`, the finalized block `v` holds after `i` steps is an ancestor of the one it holds
    after `j` steps. -/
theorem F_mono (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) {i j : Nat} (hij : i ≤ j) :
    Block.Preceq (x[i][v].st).st.core.F (x[j][v].st).st.core.F := by
  induction j, hij using Nat.le_induction with
  | base => exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)
  | succ j hij ih => exact preceq_trans_Preceq ih (Restated.F_mono_succ facts S Sched x v j)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After `n` steps, `v`'s store holds among its bodies a named block whose replay finalizes exactly
    the store's finalized block, at a height less than the store's maximum height. -/
theorem finalization_carrier_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (n : Nat) (v : V) :
    ∃ D : NamedBlock V, D ∈ (x[n][v].st).st.bodies ∧
      (M.derive_named S.E S.cfg D).F = (x[n][v].st).st.core.F ∧
      (M.derive_named S.E S.cfg D).h_F < (x[n][v].st).st.core.h_max := by
  obtain ⟨w, hw, hwv⟩ := Record.stateBeforeOf_runOfM M S Sched x facts.nd.wake_events_or_id v n
  have h := Restated.Vocabulary.Proofs.NamedFinalizationBridge.finalization_carrier_stateBefore facts
    (Setup.alwaysAwake S) (Record.runOfM M S Sched x v n) (Record.veventsOf M S Sched x v n).length v
    w hw
  rw [hwv] at h
  exact h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After `n` steps, the erased tree of `v`'s store is the image of its bodies under erasure. -/
theorem bodies_image_eq_T (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (n : Nat) (v : V) :
    (x[n][v].st).st.core.T = (x[n][v].st).st.bodies.image NamedBlock.erase := by
  have h := Record.inv_sts M S Sched x
    (fun m => Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M
        (Setup.alwaysAwake S).E (Setup.alwaysAwake S).cfg m.st ∧
      Restated.Vocabulary.Proofs.NamedTickRecord.Invariant M m.record)
    (fun u => facts.nd.initial_invariants (Setup.alwaysAwake S) u)
    (fun m hm => by
      rw [(facts.nd.wake_st_record m).1, (facts.nd.wake_st_record m).2]
      exact hm)
    (fun u m t out hout hm =>
      ⟨facts.nd.confirmation_invariant_tick (Setup.alwaysAwake S) u m t hm.1 out hout,
        facts.nd.record_invariant_tick (Setup.alwaysAwake S) u m t hm.2 out hout⟩)
    (fun m o m' hm' hm => facts.nd.invariants_process (Setup.alwaysAwake S) m o hm.1 hm.2 m' hm')
    n v
  exact h.1.1.1.1

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A named block that a validator honest through step `n` holds among its bodies after `n` steps is
    a block in play in the execution. -/
theorem blockInLog_of_mem_bodies (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    {x : AtomicExec (Record.protocolOf M S) Sched} {n : Nat} {v : V} (hv : Restated.HonestThrough M Sched x n v)
    {D : NamedBlock V} (hD : D ∈ (x[n][v].st).st.bodies) :
    Restated.blockInLog M S Sched x D :=
  ⟨D, Or.inr ⟨n, v, hv, hD⟩, namedBlock_Preceq_self D⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- When the blocks in play have no root collision, if `A` and `B` are in play and two erased blocks
    are each an ancestor of the erasure of one of them, equal roots force the two erased blocks to
    be equal. -/
theorem rootInjectiveOnAncestors_of_collisionFreeInLog (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (hroot : Restated.RootCollisionFreeInLog M S Sched x)
    (A B : NamedBlock V) (hA : Restated.blockInLog M S Sched x A) (hB : Restated.blockInLog M S Sched x B) :
    RootInjectiveOnAncestors A.erase B.erase := by
  refine rootInjectiveOnAncestors_intro ?_
  intro X Y Z W hZmem hXZ hWmem hYW hroots
  simp only [Finset.mem_insert, Finset.mem_singleton] at hZmem hWmem
  rcases hZmem with hZmem | hZmem <;> subst hZmem <;>
      rcases hWmem with hWmem | hWmem <;> subst hWmem
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hYW
    have hXr : X'.root = X.root := by rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y' (Or.inl hX'anc) (Or.inl hY'anc)
      (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hYW
    have hXr : X'.root = X.root := by rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y' (Or.inl hX'anc) (Or.inr hY'anc)
      (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hYW
    have hXr : X'.root = X.root := by rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y' (Or.inr hX'anc) (Or.inl hY'anc)
      (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hYW
    have hXr : X'.root = X.root := by rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y' (Or.inr hX'anc) (Or.inr hY'anc)
      (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]

end

end DecoupledConsensusModel.Sts.Restated
