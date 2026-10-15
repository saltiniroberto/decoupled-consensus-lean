module
public import Proofs.Vocabulary.Internal.Invariants
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Filtered-tree membership of a cone segment

When the FG root is an ancestor of `P`, every block `D` with `P ⪯ D ⪯ W`, for a processed block `W`
at height at least `h_max - 1`, is in the filtered block tree.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V]


/-- In a parent-closed store with `Σ.F ⪯ Σ.J`, if the FG root is an ancestor of `P` and `W` is a
    processed block with `h_max - 1 ≤ σ(W).h`, then every block `D` with `P ⪯ D ⪯ W` is in the
    filtered block tree. -/
theorem canonicalConeSegment_mem_filtered_of_root_preceq
    {st : Protocol.Store V} (hpc : ParentClosed st)
    (hFJ : Block.Preceq st.F st.J)
    {P W D : Block V}
    (hrootP : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) P)
    (hWT : W ∈ st.T)
    (hheight : st.h_max - 1 ≤ (st.σ W).h)
    (hPD : Block.Preceq P D) (hDW : Block.Preceq D W) :
    D ∈ Protocol.get_filtered_block_tree st.toHealing.toFG := by
  have hDT : D ∈ st.T :=
    Proofs.Records.mem_of_preceq ((parentClosed_iff st).mp hpc).2 D W hWT hDW
  have hFD : Block.Preceq st.F D :=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F (st := st.toHealing.toFG) hFJ)
      (Block.preceq_trans hrootP hPD)
  have hrootD : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) D :=
    Block.preceq_trans hrootP hPD
  have hV : D ∈ Protocol.V_tree st.toHealing.toFG := by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq, Protocol.Store.toHealing]
    exact ⟨⟨hDT, hFD⟩, W, hWT, hDW, hheight⟩
  exact Proofs.Records.mem_filtered_of_mem_V_tree hV hrootD

variable [Fintype V]


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
