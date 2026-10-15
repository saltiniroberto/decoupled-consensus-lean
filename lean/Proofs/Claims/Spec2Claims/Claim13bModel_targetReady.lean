import Proofs.Claims.Spec2Claims.Claim13bModel_derive_named

/-!
# Facts about `Protocol.targetReady`

Across one named block, the justified height either stays the parent's, or becomes the parent's
height, and then the parent's `nj` bit is clear.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.derive_named

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Protocol (ChainState HeightConfig derive_named fold_rows TimeoutBinding)

variable {V : Type} [DecidableEq V] [Fintype V]

section ChainStateBodies

attribute [local semireducible] Protocol.fold_rows Protocol.targetReady

/-- For a named block with parent `p`, either its justified height equals that of `p`, or it equals
    the height of `p` and the `nj` bit of `p`'s chain state is clear. -/
theorem derive_named_h_j_step_cases (E : Env V) (cfg : HeightConfig) (p : NamedBlock V)
    (s : Slot) (root : BlockId) (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V) :
    (derive_named E cfg (.node p s root votes support rows proposer)).h_j =
        (derive_named E cfg p).h_j ∨
      ((derive_named E cfg (.node p s root votes support rows proposer)).h_j =
          (derive_named E cfg p).h ∧ (derive_named E cfg p).nj = false) := by
  obtain ⟨hfh, -, hfnj⟩ := fold_rows_fields_l85 (derive_named E cfg p)
    (NamedBlock.node p s root votes support rows proposer).erase rows
  have hfields := Proofs.NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows
    { derive_named E cfg p with
      s := (NamedBlock.node p s root votes support rows proposer).erase.slot }
  have hfhj : (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
      (NamedBlock.node p s root votes support rows proposer).erase rows).h_j =
      (derive_named E cfg p).h_j := hfields.2.2.2.2.1
  rw [derive_node_l85]
  set tau := fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
    (NamedBlock.node p s root votes support rows proposer).erase rows with htau
  rw [Protocol.process_height_events_eq]
  by_cases ht : Protocol.targetReady E (Protocol.afterFin E tau) = true
  · right
    rw [if_pos ht]
    refine ⟨?_, ?_⟩
    · rw [Protocol.advance_height_h_j]
      change (Protocol.afterFin E tau).h = _
      rw [Protocol.afterFin_h, hfh]
    · have hnj : (Protocol.afterFin E tau).nj = false := by
        unfold Protocol.targetReady at ht
        cases hn : (Protocol.afterFin E tau).nj
        · rfl
        · rw [hn] at ht
          simp at ht
      rw [Protocol.afterFin_nj, hfnj] at hnj
      exact hnj
  · left
    rw [if_neg ht]
    split_ifs
    · rw [Protocol.advance_height_h_j, Protocol.afterFin_h_j, hfhj]
    · rw [Protocol.afterFin_h_j, hfhj]

end ChainStateBodies

end DecoupledConsensusModel.Sts
