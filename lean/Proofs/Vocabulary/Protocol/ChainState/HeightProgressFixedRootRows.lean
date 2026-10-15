module
public import Proofs.Vocabulary.Objects.FixedHeightRootCore
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# The justification as its own height entry

A helper: the justified block of a named block's derived state is a named ancestor that is its own
height entry.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]


open Protocol (HeightConfig derive_named fold_rows TimeoutBinding)

private theorem namedJustification_entry_ancestor
    (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    ∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
      J.erase = (derive_named E cfg B).J ∧
      (derive_named E cfg J).T_h = J.erase := by
  induction B with
  | genesis => exact ⟨.genesis, Proofs.NamedAncestry.named_self _, rfl, rfl⟩
  | node parent s root votes support rows proposer ih =>
      let B := NamedBlock.node parent s root votes support rows proposer
      have hfields := Proofs.NamedStoreRoots.fold_context_fields (TimeoutBinding.targeted V)
        rows { derive_named E cfg parent with s := B.erase.slot }
      have hcases : (derive_named E cfg B).J = (derive_named E cfg parent).T_h ∨
          (derive_named E cfg B).J = (derive_named E cfg parent).J := by
        let folded := fold_rows (TimeoutBinding.targeted V)
          (derive_named E cfg parent) B.erase rows
        change (Protocol.process_height_events E cfg folded).J = _ ∨
          (Protocol.process_height_events E cfg folded).J = _
        simp only [Protocol.process_height_events_eq]
        split_ifs
        · left
          rw [Protocol.advance_height_J, Protocol.afterFin_T_h]
          exact hfields.2.2.1
        · right
          rw [Protocol.advance_height_J, Protocol.afterFin_J]
          exact hfields.2.2.2.1
        · right
          rw [Protocol.afterFin_J]
          exact hfields.2.2.2.1
      rcases hcases with hnew | hstay
      · obtain ⟨entry, hentry, herase, hheight⟩ :=
          Proofs.NamedEntryHeight.entry_ancestor_same_height E cfg parent
        refine ⟨entry, Proofs.NamedAncestry.named_extend s root votes support rows proposer hentry,
          herase.trans hnew.symm, ?_⟩
        exact (Proofs.NamedEntryHeight.entry_eq_on_plateau E cfg hentry hheight).trans herase.symm
      · obtain ⟨J, hJ, herase, hself⟩ := ih
        exact ⟨J, Proofs.NamedAncestry.named_extend s root votes support rows proposer hJ,
          herase.trans hstay.symm, hself⟩

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
