module
public import Proofs.Vocabulary.Protocol.ChainState.W4FKChainJustification
import Proofs.Vocabulary.Protocol.ChainState.NjGap
import Mathlib.Data.Rat.Floor

@[expose] public section

/-!
# The named justification witness

The justified block of a named block's derived state is the erasure of a named ancestor that is its
own height target, has `nj` false, and has the justified height.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Protocol (ChainState HeightConfig derive_named fold_rows
  process_attestation_with TimeoutBinding)

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem w4caFold_nj
    (rows : List (NamedAttestation V)) (sigma : ChainState V) :
    (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
      sigma).nj = sigma.nj := by
  induction rows generalizing sigma with
  | nil => rfl
  | cons row rows ih =>
      rw [List.foldl_cons, ih]
      exact NjGap.process_attestation_nj sigma _

omit [Fintype V] in
private theorem w4caRows_nj (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).nj = sigma.nj := by
  unfold fold_rows
  exact w4caFold_nj rows { sigma with s := geometry.slot }

omit [Fintype V] in
private theorem w4caRows_h (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).h = sigma.h := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.1

omit [Fintype V] in
private theorem w4caRows_T_h (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).T_h = sigma.T_h := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.2.1

omit [Fintype V] in
private theorem w4caRows_J (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).J = sigma.J := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.2.2.1

omit [Fintype V] in
private theorem w4caRows_h_j (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).h_j = sigma.h_j := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.2.2.2.1

/-- The justified block of `B` is the erasure of a named ancestor `J` of `B` that is its own height
    target, has `nj` false, and, unless `B`'s `h_j` is 0, has derived height `B`'s `h_j`. -/
theorem namedJustificationWitness (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    ∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
      J.erase = (derive_named E cfg B).J ∧
      (derive_named E cfg J).T_h = J.erase ∧
      (derive_named E cfg J).nj = false ∧
      ((derive_named E cfg B).h_j = 0 ∨
        (derive_named E cfg J).h = (derive_named E cfg B).h_j) := by
  induction B with
  | genesis =>
      exact ⟨.genesis, Proofs.NamedAncestry.named_self _, rfl, rfl, rfl, Or.inl rfl⟩
  | node p s root gv gsv ats proposer ih =>
      obtain ⟨JP, hJPle, hJPerase, hJPself, hJPnj, hJPheight⟩ := ih
      set tau := fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
        (NamedBlock.node p s root gv gsv ats proposer).erase
        (NamedBlock.node p s root gv gsv ats proposer).attestations with htau
      have hderive : derive_named E cfg (.node p s root gv gsv ats proposer) =
          Protocol.process_height_events E cfg tau := rfl
      by_cases htarget : Protocol.targetReady E (Protocol.afterFin E tau) = true
      · obtain ⟨entry, hentryLe, hentryErase, hentryHeight⟩ :=
          Proofs.NamedEntryHeight.entry_ancestor_same_height E cfg p
        have hnjParent : (derive_named E cfg p).nj = false := by
          have hready := htarget
          simp only [Protocol.targetReady, Bool.and_eq_true] at hready
          have hnjAfter : (Protocol.afterFin E tau).nj = false := by
            simpa only [Bool.not_eq_true'] using hready.1
          rw [Protocol.afterFin_nj, w4caRows_nj] at hnjAfter
          exact hnjAfter
        refine ⟨entry, Proofs.NamedAncestry.named_extend s root gv gsv ats proposer hentryLe,
          ?_, ?_, ?_, ?_⟩
        · rw [hderive, Protocol.process_height_events_eq, if_pos htarget,
            Protocol.advance_height_J, Protocol.afterFin_T_h, w4caRows_T_h, hentryErase]
        · rw [Proofs.NamedEntryHeight.entry_eq_on_plateau E cfg hentryLe hentryHeight,
            hentryErase]
        · rw [namedNj_eq_of_preceq_same_height E cfg hentryLe hentryHeight.symm] at hnjParent
          exact hnjParent
        · right
          rw [hderive, Protocol.process_height_events_eq, if_pos htarget,
            Protocol.advance_height_h_j, Protocol.afterFin_h, w4caRows_h, hentryHeight]
      · have hJout : (derive_named E cfg (.node p s root gv gsv ats proposer)).J =
            (derive_named E cfg p).J := by
          rw [hderive, Protocol.process_height_events_eq, if_neg htarget]
          split_ifs
          · rw [Protocol.advance_height_J, Protocol.afterFin_J, w4caRows_J]
          · rw [Protocol.afterFin_J, w4caRows_J]
        have hHjout : (derive_named E cfg (.node p s root gv gsv ats proposer)).h_j =
            (derive_named E cfg p).h_j := by
          rw [hderive, Protocol.process_height_events_eq, if_neg htarget]
          split_ifs
          · rw [Protocol.advance_height_h_j, Protocol.afterFin_h_j, w4caRows_h_j]
          · rw [Protocol.afterFin_h_j, w4caRows_h_j]
        exact ⟨JP, Proofs.NamedAncestry.named_extend s root gv gsv ats proposer hJPle,
          by rw [hJPerase, hJout], hJPself, hJPnj, by rw [hHjout]; exact hJPheight⟩


#print axioms namedJustificationWitness

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
