module
public import Proofs.Vocabulary.Protocol.ChainState.HeightRegimeNamedBase
public import Proofs.Vocabulary.Execution.HeightRegimeNamedClosed
public import Proofs.Vocabulary.Protocol.ValidatorClient.HeightProgressFixedRoot
public import Proofs.Vocabulary.Execution.SeedSourceCapClosure
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FixedRootSourceCap
public import Proofs.Vocabulary.Protocol.ChainState.CheckpointAlgebra
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

@[expose] public section

/-!
# Named ancestry and finalization helpers

Helpers on named ancestry, on the fields the attestation fold keeps, and on the checkpoint of a
positive named finalization.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic
open Proofs.HealingLemmas Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

omit [Fintype V] in
private theorem named_preceq_self_deadline (B : NamedBlock V) :
    NamedBlock.Preceq B B := by
  cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

omit [Fintype V] in
private theorem named_preceq_extend_deadline {A P : NamedBlock V}
    (s : Slot) (root : BlockId) (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V)
    (h : NamedBlock.Preceq A P) :
    NamedBlock.Preceq A (.node P s root votes support rows proposer) := by
  simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
  exact Or.inr h

omit [Fintype V] in
private theorem named_genesis_preceq_deadline (B : NamedBlock V) :
    NamedBlock.Preceq .genesis B := by
  induction B with
  | genesis => exact named_preceq_self_deadline _
  | node parent slot root votes support rows proposer ih =>
      exact named_preceq_extend_deadline slot root votes support rows proposer ih

omit [Fintype V] in
private theorem named_preceq_or_preceq_common_deadline
    {A B C : NamedBlock V} (hA : NamedBlock.Preceq A C)
    (hB : NamedBlock.Preceq B C) :
    NamedBlock.Preceq A B ∨ NamedBlock.Preceq B A := by
  induction C with
  | genesis =>
      have hAg : A = .genesis := by
        simpa only [NamedBlock.Preceq, NamedBlock.preceq,
          decide_eq_true_eq] using hA
      have hBg : B = .genesis := by
        simpa only [NamedBlock.Preceq, NamedBlock.preceq,
          decide_eq_true_eq] using hB
      subst A
      subst B
      exact Or.inl (named_preceq_self_deadline _)
  | node parent slot root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hA hB
      rcases hA with rfl | hA
      · rcases hB with rfl | hB
        · exact Or.inl (named_preceq_self_deadline _)
        · exact Or.inr
            (named_preceq_extend_deadline slot root votes support rows proposer hB)
      · rcases hB with rfl | hB
        · exact Or.inl
            (named_preceq_extend_deadline slot root votes support rows proposer hA)
        · exact ih hA hB

omit [Fintype V] in
private theorem fold_F_deadline (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).F = st.F :=
  (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { st with s := geometry.slot }).2.2.2.2.2.1

omit [Fintype V] in
private theorem fold_h_F_deadline (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).h_F = st.h_F :=
  (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { st with s := geometry.slot }).2.2.2.2.2.2

omit [Fintype V] in
private theorem fold_J_deadline (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).J = st.J :=
  (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { st with s := geometry.slot }).2.2.2.1

omit [Fintype V] in
private theorem fold_h_j_deadline (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).h_j = st.h_j :=
  (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { st with s := geometry.slot }).2.2.2.2.1

private theorem namedFinalization_selfTarget_deadline
    (E : Env V) (cfg : Protocol.HeightConfig) (B : NamedBlock V)
    (hpos : 0 < (derive_named E cfg B).h_F) :
    ∃ F : NamedBlock V, NamedBlock.Preceq F B ∧
      F.erase = (derive_named E cfg B).F ∧
      (derive_named E cfg F).h = (derive_named E cfg B).h_F ∧
      (derive_named E cfg F).T_h = F.erase := by
  induction B with
  | genesis => simp [derive_named, ChainState.initial] at hpos
  | node parent slot root votes support rows proposer ih =>
      let B := NamedBlock.node parent slot root votes support rows proposer
      let folded := fold_rows (TimeoutBinding.targeted V)
        (derive_named E cfg parent) B.erase rows
      have hstate : derive_named E cfg B = process_height_events E cfg folded := rfl
      have hafterF : (Protocol.afterFin E folded).F =
          (derive_named E cfg B).F := by
        rw [hstate, Protocol.process_height_events_eq]
        split_ifs <;> rfl
      have hafterH : (Protocol.afterFin E folded).h_F =
          (derive_named E cfg B).h_F := by
        rw [hstate, Protocol.process_height_events_eq]
        split_ifs <;> rfl
      by_cases hfinal : finalityReady E folded = true
      · simp only [Protocol.afterFin_F, Protocol.afterFin_h_F,
          if_pos hfinal] at hafterF hafterH
        have hparentPos : 0 < (derive_named E cfg parent).h_j := by
          rw [← fold_h_j_deadline]
          rw [hafterH]
          exact hpos
        obtain ⟨J, hJ, hJerase, hJheight, hJtarget⟩ :=
          NamedCheckpointAlgebra.namedJustification_selfTarget
            E cfg parent hparentPos
        refine ⟨J,
          named_preceq_extend_deadline slot root votes support rows proposer hJ,
          ?_, ?_, hJtarget⟩
        · calc
            J.erase = (derive_named E cfg parent).J := hJerase
            _ = folded.J :=
              (fold_J_deadline (derive_named E cfg parent) B.erase rows).symm
            _ = (derive_named E cfg B).F := hafterF
            _ = (derive_named E cfg
                (.node parent slot root votes support rows proposer)).F := rfl
        · calc
            (derive_named E cfg J).h =
                (derive_named E cfg parent).h_j := hJheight
            _ = folded.h_j :=
              (fold_h_j_deadline (derive_named E cfg parent) B.erase rows).symm
            _ = (derive_named E cfg B).h_F := hafterH
            _ = (derive_named E cfg
                (.node parent slot root votes support rows proposer)).h_F := rfl
      · simp only [Protocol.afterFin_F, Protocol.afterFin_h_F,
          if_neg hfinal] at hafterF hafterH
        have hparentPos : 0 < (derive_named E cfg parent).h_F := by
          rw [← fold_h_F_deadline]
          rw [hafterH]
          exact hpos
        obtain ⟨F, hF, hFerase, hFheight, hFtarget⟩ := ih hparentPos
        refine ⟨F,
          named_preceq_extend_deadline slot root votes support rows proposer hF,
          ?_, ?_, hFtarget⟩
        · calc
            F.erase = (derive_named E cfg parent).F := hFerase
            _ = folded.F :=
              (fold_F_deadline (derive_named E cfg parent) B.erase rows).symm
            _ = (derive_named E cfg B).F := hafterF
            _ = (derive_named E cfg
                (.node parent slot root votes support rows proposer)).F := rfl
        · calc
            (derive_named E cfg F).h =
                (derive_named E cfg parent).h_F := hFheight
            _ = folded.h_F :=
              (fold_h_F_deadline (derive_named E cfg parent) B.erase rows).symm
            _ = (derive_named E cfg B).h_F := hafterH
            _ = (derive_named E cfg
                (.node parent slot root votes support rows proposer)).h_F := rfl


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
