module

public import Proofs.Vocabulary.Protocol.ValidatorClient.FinalityPairCore
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedHeadReads
public import Proofs.Vocabulary.Internal.Internal.GradeReads
public import Proofs.Claims.ModelIrreducible
public import Proofs.Vocabulary.ModelProperties.NamedDuties_update_confirmation_with
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
public import Proofs.Vocabulary.ModelProperties.NamedStore_setClock
public import Proofs.Vocabulary.ModelProperties.NamedDuties_attest_with
public import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
public import Proofs.Claims.Spec2Claims.Claim13bModel_actionReadFrom

@[expose] public section

/-!
# Facts about `actionStoreAt`

The round-`r` action store `actionStoreAt`, with the action head `actionHeadAt` and the action
attestation `actionAttestationAt` read off it.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.preceq
  DecoupledConsensusModel.Execution.NamedActionReads.confirmationReadFrom
  DecoupledConsensusModel.Protocol.NamedDuties.update_confirmation_with
  DecoupledConsensusModel.Protocol.NamedStore.setClock
  DecoupledConsensusModel.Protocol.Store.toHealing
  DecoupledConsensusModel.Protocol.finalized_descendants
  DecoupledConsensusModel.Protocol.get_fg_root
  DecoupledConsensusModel.Protocol.get_filtered_block_tree
  DecoupledConsensusModel.Protocol.get_filtered_block_tree_from
  DecoupledConsensusModel.Protocol.update_confirmation_with
  DecoupledConsensusModel.Protocol.viable_tree

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The bodies of `v`'s round-`r` action store are the bodies `v` holds strictly before `S.a r`. -/
theorem actionStoreAt_st_bodies (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    (actionStoreAt S rho v r).st.bodies =
      (NamedRun.stateBeforeTime S rho (S.a r) v).st.bodies := by
  unfold actionStoreAt actionReadAt NamedActionReads.actionReadAt NamedActionReads.actionReadFrom
  rw [Proofs.ModelProperties.named_update_confirmation_with_bodies,
    Proofs.ModelProperties.confirmationReadFrom_st, Proofs.ModelProperties.setClock_bodies]

/-- The chain-state map `σ` of `v`'s round-`r` action store is the chain-state map of `v`'s store
    strictly before `S.a r`. -/
theorem actionStoreAt_st_core_σ (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    (actionStoreAt S rho v r).st.core.σ = (NamedRun.stateBeforeTime S rho (S.a r) v).st.core.σ :=
  rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]


end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]


end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]


end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]


end DecoupledConsensusModel.Sts
