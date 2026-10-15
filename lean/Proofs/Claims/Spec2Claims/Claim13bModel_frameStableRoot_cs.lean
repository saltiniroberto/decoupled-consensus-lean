import Proofs.Vocabulary.Protocol.Grades.VoteBelowSource
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records
import Mathlib.Data.Rat.Floor
import Proofs.Claims.ModelIrreducible

/-!
# `Protocol.frameStableRoot` against the ancestors of the grade-2 root

`Protocol.frameStableRoot` is the active prefix, in the filtered tree, of the frame's grade-2 root
when that is a block, and `get_fg_root` otherwise.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Block.deepest? DecoupledConsensusModel.Protocol.activePrefix
  DecoupledConsensusModel.Protocol.frameStableRoot
  DecoupledConsensusModel.Protocol.get_filtered_block_tree
  DecoupledConsensusModel.Protocol.get_filtered_block_tree_from

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the frame `Protocol.readFrame c st r` holds the grade-2 root `e`, `X ⪯ e`, and `X` is in the
    store's filtered tree or is an ancestor of its `get_fg_root`, then `X` is an ancestor of every
    stable root `G` of `c` at `st` for round `r`. -/
theorem preceq_frameStableRoot (c : Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) {X e G : Block V}
    (he : (Protocol.readFrame c st r).g2 = some (some e)) (hXe : Block.Preceq X e)
    (hX : X ∈ Protocol.get_filtered_block_tree st.toFG ∨
      Block.Preceq X (Protocol.get_fg_root st.toFG))
    (hG : Protocol.frameStableRoot c E hc st r = some G) :
    Block.Preceq X G := by
  unfold Protocol.frameStableRoot at hG
  simp only [he, Option.bind_some, id_eq] at hG
  have hXm : X ∈ Protocol.get_filtered_block_tree st.toFG →
      X ∈ (Protocol.get_filtered_block_tree st.toFG).filter (fun B => Block.preceq B e = true) :=
    fun h => Finset.mem_filter.2 ⟨h, hXe⟩
  have hchain : ∀ Y ∈ (Protocol.get_filtered_block_tree st.toFG).filter
      (fun B => Block.preceq B e = true), Block.preceq Y e = true :=
    fun Y hY => (Finset.mem_filter.1 hY).2
  cases hp : Protocol.activePrefix (Protocol.get_filtered_block_tree st.toFG) e with
  | none =>
      rw [hp] at hG
      simp only [Option.some.injEq] at hG
      rcases hX with hXt | hXr
      · exfalso
        unfold Protocol.activePrefix at hp
        have hs := Proofs.HealingSurface.deepest?_isSome_of_chain hchain ⟨X, hXm hXt⟩
        rw [hp] at hs
        exact Bool.false_ne_true hs
      · rw [← hG]; exact hXr
  | some G' =>
      rw [hp] at hG
      simp only [Option.some.injEq] at hG
      subst hG
      unfold Protocol.activePrefix at hp
      have hGm := Finset.mem_filter.1 (Proofs.Engine.deepest?_mem hp)
      rcases hX with hXt | hXr
      · exact Proofs.HealingLemmas.deepest?_dominates hp (hXm hXt)
          (Block.compatible_of_preceq_common hXe hGm.2)
      · exact Block.preceq_trans hXr
          (Proofs.Records.preceq_get_fg_root_of_mem_filtered hGm.1)

end DecoupledConsensusModel.Sts
