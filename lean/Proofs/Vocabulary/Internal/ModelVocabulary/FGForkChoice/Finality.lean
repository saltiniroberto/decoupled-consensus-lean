module
public import Model.Vocabulary.Protocol.ForkChoice.Goldfish

@[expose] public section

/-!
# The viable tree of a store

`V_tree`, the viable tree read off a finality-gadget store.
-/


namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState)

namespace FGStore

variable {V : Type} [DecidableEq V]

end FGStore

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The viable tree read off the store, named `V_tree` because `V` is the validator type. -/
def V_tree (st : FGStore V) : Finset (Block V) :=
  viable_tree st.σ st.F st.h_max st.T

end Protocol
end DecoupledConsensusModel

end
