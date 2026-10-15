module
public import Model.Vocabulary.Execution.Run

@[expose] public section

/-!
# Nesting of the three user-facing chains

The statement `NestedOutputs`.
-/


namespace DecoupledConsensusModel
namespace Internal

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-- At every read of every node, the finalized block is an ancestor of the stable output, which is
    an ancestor of the confirmed output. -/
def NestedOutputs (S : Setup V) : Prop :=
  ∀ (rho : NamedRun V) (v : V) (t : Time),
    let st := (NamedRun.readAt S rho t v).st.core
    Block.Preceq st.F (Protocol.get_stable st) ∧
      Block.Preceq (Protocol.get_stable st) (Protocol.get_confirmed st)

end Internal
end DecoupledConsensusModel

end
