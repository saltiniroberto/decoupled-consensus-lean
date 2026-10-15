module
public import Proofs.Vocabulary.Internal.Definitions.NamedStableChainOutage
public import Proofs.Vocabulary.Internal.Definitions.OutageEntryRevision

@[expose] public section

/-!
# Round checkpoint and the SG-need test

`RoundIncluded`, the round `checkpoint` read, and `NeedsSG`, which holds when a block is not an
ancestor of a validator's finalized block at round `r`'s G1 read.
-/


namespace DecoupledConsensusModel.Internal.NamedJointOutage
open Execution NamedOutageEntry NamedStableChainOutage DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

def RoundIncluded (S : Setup V) (rho : NamedRun V) (b0 : Time) (r : Round) : Prop :=
  0 < r ∧ b0 ≤ S.a r ∧ S.a r ≤ rho.horizon


/-- `v`'s node state at round `r`'s confirmation read, used for both the SG and the FG fields. -/
def checkpoint (S : Setup V) (rho : NamedRun V) (v : V) (r : Round) : NamedNodeState V :=
  roundConfirmationRead S rho v r


/-- The block `P` is not an ancestor of `v`'s finalized block at the G1 read of round `r`. -/
def NeedsSG (S : Setup V) (rho : NamedRun V) (P : NamedBlock V) (r : Round) (v : V) : Prop :=
  ¬ Block.Preceq P.erase (NamedRun.readAt S rho (domain S.E S.hc r .g1) v).st.core.F

local instance (S : Setup V) (rho : NamedRun V) (P : NamedBlock V) (r : Round) (v : V) :
    Decidable (NeedsSG S rho P r v) :=
  inferInstanceAs (Decidable (¬ Block.Preceq P.erase
    (NamedRun.readAt S rho (domain S.E S.hc r .g1) v).st.core.F))


end DecoupledConsensusModel.Internal.NamedJointOutage

end
