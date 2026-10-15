import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf
import Proofs.Claims.ModelIrreducible

/-!
# The justified height across one chain-state transition

A block's justified height is at least its parent's.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.NamedBlock.attestations
  DecoupledConsensusModel.NamedBlock.parent DecoupledConsensusModel.Protocol.ChainState.initial
  DecoupledConsensusModel.Protocol.process_height_events
  DecoupledConsensusModel.Protocol.targetReady

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Protocol (ChainState HeightConfig derive_named fold_rows TimeoutBinding)

variable {V : Type} [DecidableEq V] [Fintype V]

section ChainStateBodies

attribute [local semireducible] Protocol.derive_named Protocol.named_transition
  Protocol.transition_rows Protocol.fold_rows

/-- For every named block `B`, the justified height of the chain state of `B`'s parent is at most
    the justified height of the chain state of `B`. -/
theorem derive_named_h_j_parent_le (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    (derive_named E cfg B.parent).h_j ≤ (derive_named E cfg B).h_j := by
  cases B with
  | genesis => exact le_refl _
  | node p s root gv gsv ats proposer =>
      set tau := fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
        (NamedBlock.node p s root gv gsv ats proposer).erase
        (NamedBlock.node p s root gv gsv ats proposer).attestations with htau
      have hderive : derive_named E cfg (.node p s root gv gsv ats proposer) =
          Protocol.process_height_events E cfg tau := rfl
      have hfields := Proofs.NamedDerivationGeometry.fold_context_fields
        (TimeoutBinding.targeted V)
        (NamedBlock.node p s root gv gsv ats proposer).attestations
        { derive_named E cfg p with
          s := (NamedBlock.node p s root gv gsv ats proposer).erase.slot }
      have htauH : tau.h = (derive_named E cfg p).h := hfields.2.1
      have htauHj : tau.h_j = (derive_named E cfg p).h_j := hfields.2.2.2.2.1
      have hpar : (NamedBlock.node p s root gv gsv ats proposer).parent = p := rfl
      have hlt : (derive_named E cfg p).h_j < (derive_named E cfg p).h :=
        (Proofs.NamedDerivationGeometry.chainOrder_derive_named E cfg p).justified_below_height
      rw [hpar, hderive, Protocol.process_height_events_eq]
      split_ifs
      · rw [Protocol.advance_height_h_j, Protocol.afterFin_h, htauH]
        exact Nat.le_of_lt hlt
      · rw [Protocol.advance_height_h_j, Protocol.afterFin_h_j, htauHj]
      · rw [Protocol.afterFin_h_j, htauHj]

end ChainStateBodies

end DecoupledConsensusModel.Sts
