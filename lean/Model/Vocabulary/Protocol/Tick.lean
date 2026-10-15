module
public import Model.Vocabulary.Protocol.Handlers
public import Model.Vocabulary.Protocol.Duties.Proposals
public import Model.Vocabulary.Execution.Objects

@[expose] public section

/-!
# The node's tick

The named duties bound to the tick timetable, and the named tick.
-/

namespace DecoupledConsensusModel.Protocol.NamedTick
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

def namedOps (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) :
    TickScheduler.TickOps (NamedStore V) Protocol.NamedRecord
      (NamedBlock V) (GoldfishVote V) (NamedAttestation V) where
  clock := fun st t s => { st with core := { st.core with t := t, s := s } }
  slot := fun st => st.core.s
  proposal := NamedDuties.propose_block_with gc E hc cfg nd
  vote := NamedDuties.goldfish_vote_with gc E hc nd
  confirmation := NamedDuties.update_confirmation_with gc E hc
  attestation := NamedDuties.attest_with gc E hc nd

def tick (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) :
    NamedStore V × Protocol.NamedRecord × List (NamedObject V) :=
  TickScheduler.runWith E hc nd (namedOps gc E hc cfg nd)
    NamedObject.block NamedObject.gfVote NamedObject.attest
    (fun st record emitted => (st, record, emitted)) st record t

end DecoupledConsensusModel.Protocol.NamedTick

end
