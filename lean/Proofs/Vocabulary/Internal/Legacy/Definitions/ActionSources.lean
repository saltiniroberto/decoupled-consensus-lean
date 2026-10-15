module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.NamedActionReads

@[expose] public section

/-!
# Action reads and selectors

A validator's action read at a round, and the attestation, SG block, FG source and FG confirmation
witness the action computes from it.
-/
namespace DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- `v`'s node state at round `r`'s action, after the same-tick confirmation duty. -/
def actionReadAt (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    NamedNodeState V :=
  NamedActionReads.actionReadAt S rho v r

/-- `v`'s action read at round `r`, cache, store and record included. -/
def actionStoreAt (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    NamedNodeState V :=
  actionReadAt S rho v r

/-- The attestation `v`'s attest duty computes at round `r`'s action read. -/
def actionAttestationAt (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    NamedAttestation V :=
  let n := actionReadAt S rho v r
  (Protocol.NamedDuties.attest_with (NamedProfile.gradeContract n.cache)
    S.E S.hc (S.node v) n.st n.record).2.2

/-- The SG block `v`'s action at round `r` selects, under the contract of the action read's cache. -/
def actionSGBlockAt (S : Setup V) (rho : Run V) (v : V) (r : Round) : Block V :=
  let n := actionReadAt S rho v r
  let gc := NamedProfile.gradeContract n.cache
  let st := n.st.core.toHealing
  let k := S.hc.round_of st.s
  Protocol.get_sg_vote_with gc S.E S.hc st k
    (Protocol.grade2_block_with gc S.E S.hc st k)

/-- The FG source of a node state, under the contract of its cache. -/
def actionFGSource (S : Setup V) (n : NamedNodeState V) : Option (Block V) :=
  let gc := NamedProfile.gradeContract n.cache
  let st := n.st.core.toHealing
  let r := S.hc.round_of st.s
  Protocol.fg_source_with gc S.E S.hc st r
    (Protocol.grade2_block_with gc S.E S.hc st r)

/-- The checkpoint of the FG source's stored chain state. -/
def fgConfirmationWitness (S : Setup V) (n : NamedNodeState V) : Option (Block V) :=
  (actionFGSource S n).map (fun Cfg => (n.st.core.σ Cfg).T_h)

end DecoupledConsensusModel.Proofs.HealingSurface

end
