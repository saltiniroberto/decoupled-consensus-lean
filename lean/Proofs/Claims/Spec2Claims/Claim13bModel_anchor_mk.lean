import Model.Vocabulary.Execution.Setup
import Proofs.Claims.ModelIrreducible
import Proofs.Vocabulary.Objects.AttestationCanonicality
import Proofs.Claims.Spec2Claims.Claim13bModel_activePrefix

/-!
# `Protocol.anchor` against a fixed block

When the block a grade frame anchors a round at is compatible with a given block.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.anchor

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If every completed grade-1 root of `g1` is compatible with `T`, and so is the store's
    `get_fg_root`, then the anchor of round `r₁` is compatible with `T`. -/
theorem anchor_compatible (S : Setup V) {stH : Protocol.HealingStore V} {T : Block V}
    {r₁ : Round} {g1 : Option (Option (Block V))}
    (hg1 : ∀ root : Block V, g1 = some (some root) → Block.compatible root T = true)
    (hfg : Block.compatible (Protocol.get_fg_root stH.toFG) T = true) :
    Block.compatible (Protocol.anchor S.E S.hc stH r₁ g1) T = true := by
  unfold Protocol.anchor
  match hg : g1 with
  | none => exact hfg
  | some none => exact hfg
  | some (some root) =>
      simp only [Option.getD]
      cases hactive : Protocol.activePrefix (Protocol.get_filtered_block_tree stH.toFG) root with
      | none => exact hfg
      | some B =>
          exact Protocol.compatible_of_preceq_of_compatible
            (preceq_of_activePrefix_eq_some hactive) (hg1 root rfl)

end DecoupledConsensusModel.Sts
