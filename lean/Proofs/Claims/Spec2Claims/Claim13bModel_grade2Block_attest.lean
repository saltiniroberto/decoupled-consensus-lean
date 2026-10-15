import Proofs.Vocabulary.Protocol.Grades.VoteBelowSource
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.grade2Block` against the filtered tree

Lemmas that unfold `Protocol.grade2Block`, `Protocol.allClosed` and `Protocol.activePrefix`. When
the frame's three phase results are present, the grade-2 block is the active prefix, in the store's
filtered tree, of the frame's grade-2 root.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Block.deepest? DecoupledConsensusModel.Protocol.activePrefix
  DecoupledConsensusModel.Protocol.allClosed
  DecoupledConsensusModel.Protocol.get_filtered_block_tree
  DecoupledConsensusModel.Protocol.grade2Block

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the frame's grade-2 block at the store `st` is `q`, then `Protocol.get_fg_root st.toFG ⪯ q`. -/
theorem fgRoot_preceq_grade2Block {st : Protocol.HealingStore V} {frame : Protocol.Frame V}
    {q : Block V} (h : Protocol.grade2Block st frame = some q) :
    Block.Preceq (Protocol.get_fg_root st.toFG) q := by
  unfold Protocol.grade2Block at h
  split_ifs at h
  cases hg : frame.g2.bind id with
  | none => rw [hg] at h; exact absurd h (by simp)
  | some e =>
      rw [hg] at h
      simp only [Option.bind_some] at h
      unfold Protocol.activePrefix at h
      have hGm := Finset.mem_filter.1 (Proofs.Engine.deepest?_mem h)
      exact Proofs.Records.preceq_get_fg_root_of_mem_filtered hGm.1

/-- If the frame holds all three phase results with grade-2 root `e`, and `P` is in the store's
    filtered tree with `P ⪯ e`, then the frame's grade-2 block at `st` is some `q` with `P ⪯ q`. -/
theorem preceq_grade2Block_of_g2 {st : Protocol.HealingStore V} {frame : Protocol.Frame V}
    {o₀ o₁ : Option (Block V)} {P e : Block V}
    (h₀ : frame.g0 = some o₀) (h₁ : frame.g1 = some o₁) (h₂ : frame.g2 = some (some e))
    (hPt : P ∈ Protocol.get_filtered_block_tree st.toFG) (hPe : Block.Preceq P e) :
    ∃ q : Block V, Protocol.grade2Block st frame = some q ∧ Block.Preceq P q := by
  have hcl : Protocol.allClosed frame = true := by
    unfold Protocol.allClosed
    rw [h₀, h₁, h₂]
    rfl
  have hPm : P ∈ (Protocol.get_filtered_block_tree st.toFG).filter
      (fun B => Block.preceq B e = true) := Finset.mem_filter.2 ⟨hPt, hPe⟩
  have hchain : ∀ Y ∈ (Protocol.get_filtered_block_tree st.toFG).filter
      (fun B => Block.preceq B e = true), Block.preceq Y e = true :=
    fun Y hY => (Finset.mem_filter.1 hY).2
  unfold Protocol.grade2Block
  rw [if_pos hcl, h₂]
  simp only [Option.bind_some, id_eq]
  cases hp : Protocol.activePrefix (Protocol.get_filtered_block_tree st.toFG) e with
  | none =>
      exfalso
      unfold Protocol.activePrefix at hp
      have hs := Proofs.HealingSurface.deepest?_isSome_of_chain hchain ⟨P, hPm⟩
      rw [hp] at hs
      exact Bool.false_ne_true hs
  | some G =>
      refine ⟨G, rfl, ?_⟩
      unfold Protocol.activePrefix at hp
      have hGm := Finset.mem_filter.1 (Proofs.Engine.deepest?_mem hp)
      exact Proofs.HealingLemmas.deepest?_dominates hp hPm
        (Block.compatible_of_preceq_common hPe hGm.2)

end DecoupledConsensusModel.Sts
