module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Walk
public import Proofs.Vocabulary.Protocol.Grades.LegacyVocabulary
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records

@[expose] public section

/-!
# The finalized block and the FG root

The finalized block is an ancestor of the FG root when it is an ancestor of the justified block.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace StoreFinality

open Protocol (HealConfig)
open Internal

variable {V : Type} [DecidableEq V] [Fintype V]

theorem finalized_preceq_fgRoot {st : Protocol.Store V}
    (hFJ : Block.preceq st.F st.J = true) :
    Block.Preceq st.F (Protocol.get_fg_root st.toHealing.toFG) :=
  Proofs.Records.preceq_get_fg_root_of_F (st := st.toHealing.toFG) hFJ

end StoreFinality
end Proofs
end DecoupledConsensusModel

end
