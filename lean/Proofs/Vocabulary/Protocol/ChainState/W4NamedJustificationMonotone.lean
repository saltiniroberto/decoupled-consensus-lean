module
public import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry

@[expose] public section

/-!
# Monotone justification along named ancestry

Along named ancestry the derived justification height strictly increases, or the justification
height and the justified block are both unchanged.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol Internal Execution

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem nfold_h (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).h = st.h := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { st with s := geometry.slot }).2.1

omit [Fintype V] in
private theorem nfold_J (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).J = st.J := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { st with s := geometry.slot }).2.2.2.1

omit [Fintype V] in
private theorem nfold_h_j (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).h_j = st.h_j := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { st with s := geometry.slot }).2.2.2.2.1

/-- From a named parent to its child, the derived `h_j` strictly increases, or both `h_j` and `J`
    are unchanged. -/
theorem namedJustification_strict_or_eq_of_parent
    (E : Env V) (cfg : HeightConfig)
    (parent : NamedBlock V) (slot : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V) :
    (derive_named E cfg parent).h_j <
        (derive_named E cfg
          (.node parent slot root votes support rows proposer)).h_j ∨
      ((derive_named E cfg parent).h_j =
          (derive_named E cfg
            (.node parent slot root votes support rows proposer)).h_j ∧
        (derive_named E cfg parent).J =
          (derive_named E cfg
            (.node parent slot root votes support rows proposer)).J) := by
  let B := NamedBlock.node parent slot root votes support rows proposer
  let folded := fold_rows (TimeoutBinding.targeted V)
    (derive_named E cfg parent) B.erase rows
  rw [show derive_named E cfg B = process_height_events E cfg folded by rfl,
    Protocol.process_height_events_eq]
  split_ifs
  · left
    rw [Protocol.advance_height_h_j, Protocol.afterFin_h, nfold_h]
    exact (NamedDerivationGeometry.chainOrder_derive_named E cfg
      parent).justified_below_height
  · right
    constructor
    · rw [Protocol.advance_height_h_j, Protocol.afterFin_h_j, nfold_h_j]
    · rw [Protocol.advance_height_J, Protocol.afterFin_J, nfold_J]
  · right
    constructor
    · rw [Protocol.afterFin_h_j, nfold_h_j]
    · rw [Protocol.afterFin_J, nfold_J]

/-- If `A` is a named ancestor of `B`, then `A`'s derived `h_j` is less than `B`'s, or both `h_j`
    and `J` are equal. -/
theorem namedJustification_strict_or_eq_of_preceq
    (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) :
    (derive_named E cfg A).h_j < (derive_named E cfg B).h_j ∨
      ((derive_named E cfg A).h_j = (derive_named E cfg B).h_j ∧
        (derive_named E cfg A).J = (derive_named E cfg B).J) := by
  induction B with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      subst A
      exact Or.inr ⟨rfl, rfl⟩
  | node p s r gv support ats i ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hAp
      · exact Or.inr ⟨rfl, rfl⟩
      · have hprefix := ih hAp
        have hedge := namedJustification_strict_or_eq_of_parent E cfg p s r gv
          support ats i
        rcases hprefix with hprefix | ⟨hhPrefix, hJPrefix⟩
        · rcases hedge with hedge | ⟨hhEdge, -⟩
          · exact Or.inl (hprefix.trans hedge)
          · exact Or.inl (hprefix.trans_eq hhEdge)
        · rcases hedge with hedge | ⟨hhEdge, hJEdge⟩
          · exact Or.inl (hhPrefix.trans_lt hedge)
          · exact Or.inr ⟨hhPrefix.trans hhEdge, hJPrefix.trans hJEdge⟩

/-- If `A` is a named ancestor of `B`, then `A`'s derived `h_j` is at most `B`'s. -/
theorem namedJustification_le_of_preceq
    (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) :
    (derive_named E cfg A).h_j ≤ (derive_named E cfg B).h_j := by
  rcases namedJustification_strict_or_eq_of_preceq E cfg hAB with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

#print axioms namedJustification_strict_or_eq_of_parent
#print axioms namedJustification_strict_or_eq_of_preceq
#print axioms namedJustification_le_of_preceq


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
