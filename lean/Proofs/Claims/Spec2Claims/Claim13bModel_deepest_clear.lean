import Proofs.Vocabulary.Protocol.Grades.VoteBelowSource
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.deepest_clear`

The deepest member of the chain of a block `C` that is a descendant of a floor and passes a test.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Block.depth DecoupledConsensusModel.Block.parent?
  DecoupledConsensusModel.Block.preceq DecoupledConsensusModel.Protocol.chain_of
  DecoupledConsensusModel.Protocol.chain_up DecoupledConsensusModel.Protocol.deepest_clear

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If `X ⪯ C`, then `X` is a member of `Protocol.chain_of C`. -/
theorem mem_chain_of_of_preceq {C X : Block V} (h : Block.Preceq X C) :
    X ∈ Protocol.chain_of C := by
  induction C generalizing X with
  | genesis =>
      simp only [Block.Preceq, Block.preceq, decide_eq_true_eq] at h
      subst X
      simp [Protocol.chain_of, Protocol.chain_up, Block.depth]
  | node p s root votes support attestations proposer ih =>
      simp only [Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · subst X
        simp [Protocol.chain_of, Protocol.chain_up, Block.depth, Block.parent?]
      · have hmem : X ∈ Protocol.chain_of p := ih h
        have htail : X = Block.node p s root votes support attestations proposer ∨
            X ∈ Protocol.chain_up p.depth p := Or.inr hmem
        simpa [Protocol.chain_of, Protocol.chain_up, Block.depth, Block.parent?] using htail

/-- If `B ⪯ C`, `floor ⪯ B` and `B` passes `test`, then `deepest_clear` with that floor, `C` and
    `test` returns a block `D` with `B ⪯ D`. -/
theorem preceq_deepest_clear {floor C B : Block V} {test : Block V → Bool}
    (hBC : Block.Preceq B C) (hfloor : Block.Preceq floor B) (htest : test B = true) :
    ∃ D : Block V, Protocol.deepest_clear (some floor) C test = some D ∧ Block.Preceq B D := by
  have hmem : B ∈ Protocol.chain_of C := mem_chain_of_of_preceq hBC
  have hsome : (Protocol.deepest_clear (some floor) C test).isSome = true :=
    Proofs.HealingSurface.deepest_clear_isSome_of_mem (floor := some floor) hfloor hmem htest
  obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨D, hD, ?_⟩
  have hDC : Block.preceq D C = true := Proofs.Engine.deepest_clear_preceq hD
  have hBmem : B ∈ ((Protocol.chain_of C).toFinset.filter (fun B' =>
      (some floor).elim true (fun anchor => Block.preceq anchor B') = true ∧
        test B' = true)) :=
    Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hmem, hfloor, htest⟩
  have hcmp : Block.compatible B D = true := Block.compatible_of_preceq_common hBC hDC
  exact Proofs.HealingLemmas.deepest?_dominates hD hBmem hcmp

end DecoupledConsensusModel.Sts
