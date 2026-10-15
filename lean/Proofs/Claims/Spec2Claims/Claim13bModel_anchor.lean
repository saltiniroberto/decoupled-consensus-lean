import Proofs.Vocabulary.Protocol.Grades.VoteBelowSource
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records
import Proofs.Claims.ModelIrreducible
import Proofs.Claims.Spec2Claims.Claim13bModel_activePrefix

/-!
# Facts about `Protocol.anchor`

The start of the SG walk of a round: when the frame's grade-1 result is a block `e`, the active
prefix of `e` in the store's filtered tree if it exists; otherwise `Protocol.get_fg_root`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Block.deepest? DecoupledConsensusModel.Protocol.activePrefix
  DecoupledConsensusModel.Protocol.anchor DecoupledConsensusModel.Protocol.get_fg_root
  DecoupledConsensusModel.Protocol.get_filtered_block_tree

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If `P ⪯ get_fg_root`, then `P` is an ancestor of the anchor of round `r` or the anchor itself,
    whatever the frame's grade-1 result. -/
theorem preceq_anchor_of_fgRoot (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (g1 : Option (Option (Block V))) {P : Block V}
    (hP : Block.Preceq P (Protocol.get_fg_root st.toFG)) :
    Block.Preceq P (Protocol.anchor E hc st r g1) := by
  unfold Protocol.anchor
  split
  · rename_i e
    cases hp : Protocol.activePrefix (Protocol.get_filtered_block_tree st.toFG) e with
    | none => exact hP
    | some G =>
        simp only [Option.getD_some]
        unfold Protocol.activePrefix at hp
        have hGm := Finset.mem_filter.1 (Proofs.Engine.deepest?_mem hp)
        exact Block.preceq_trans hP (Proofs.Records.preceq_get_fg_root_of_mem_filtered hGm.1)
  · exact hP

/-- If `P` is in the store's filtered tree and `P ⪯ e`, then `P` is an ancestor of the anchor of
    round `r` at the grade-1 result `e`, or the anchor itself. -/
theorem preceq_anchor_of_g1 (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) {P e : Block V}
    (hPt : P ∈ Protocol.get_filtered_block_tree st.toFG) (hPe : Block.Preceq P e) :
    Block.Preceq P (Protocol.anchor E hc st r (some (some e))) := by
  unfold Protocol.anchor
  simp only
  have hPm : P ∈ (Protocol.get_filtered_block_tree st.toFG).filter
      (fun B => Block.preceq B e = true) := Finset.mem_filter.2 ⟨hPt, hPe⟩
  have hchain : ∀ Y ∈ (Protocol.get_filtered_block_tree st.toFG).filter
      (fun B => Block.preceq B e = true), Block.preceq Y e = true :=
    fun Y hY => (Finset.mem_filter.1 hY).2
  cases hp : Protocol.activePrefix (Protocol.get_filtered_block_tree st.toFG) e with
  | none =>
      exfalso
      unfold Protocol.activePrefix at hp
      have hs := Proofs.HealingSurface.deepest?_isSome_of_chain hchain ⟨P, hPm⟩
      rw [hp] at hs
      exact Bool.false_ne_true hs
  | some G =>
      simp only [Option.getD_some]
      unfold Protocol.activePrefix at hp
      have hGm := Finset.mem_filter.1 (Proofs.Engine.deepest?_mem hp)
      exact Proofs.HealingLemmas.deepest?_dominates hp hPm
        (Block.compatible_of_preceq_common hPe hGm.2)

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the grade-1 result is the completed root `root` and the active prefix of `root` in the
    store's filtered block tree is `A`, then the anchor is `A`. -/
theorem anchor_of_activePrefix (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) {root A : Block V}
    (h : Protocol.activePrefix (Protocol.get_filtered_block_tree st.toFG) root = some A) :
    Protocol.anchor E hc st r (some (some root)) = A := by
  unfold Protocol.anchor
  simp only [h, Option.getD_some]

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `Protocol.anchor` at the grade-1 result `g1` is the store's `get_fg_root`, or `g1` is a
    completed grade-1 root and the anchor is an ancestor of it. -/
theorem anchor_cases (S : Setup V) (stH : Protocol.HealingStore V) (r₁ : Round)
    (g1 : Option (Option (Block V))) :
    Protocol.anchor S.E S.hc stH r₁ g1 = Protocol.get_fg_root stH.toFG ∨
      ∃ root : Block V, g1 = some (some root) ∧
        Block.Preceq (Protocol.anchor S.E S.hc stH r₁ g1) root := by
  unfold Protocol.anchor
  match hg : g1 with
  | none => exact Or.inl rfl
  | some none => exact Or.inl rfl
  | some (some root) =>
      simp only [Option.getD]
      cases hactive : Protocol.activePrefix (Protocol.get_filtered_block_tree stH.toFG) root with
      | none => exact Or.inl rfl
      | some B => exact Or.inr ⟨root, rfl, preceq_of_activePrefix_eq_some hactive⟩

end DecoupledConsensusModel.Sts
