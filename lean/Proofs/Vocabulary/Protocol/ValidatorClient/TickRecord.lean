module
public import Proofs.Vocabulary.Protocol.Schedule.NamedTick
public import Proofs.Vocabulary.Protocol.ValidatorClient.Record
import Proofs.Vocabulary.Protocol.Duties.Proposals.Actions
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Record invariant at the named tick

`Invariant`, `HistoryConsistent` together with `LockCompatible`, holds initially and is preserved by
the attestation duty and by the named tick, whose attestation duty is the only record writer.
-/
namespace DecoupledConsensusModel.Proofs.NamedTickRecord
variable {V : Type} [DecidableEq V] [Fintype V]

def Invariant (record : Protocol.NamedRecord) : Prop :=
  NamedRecord.HistoryConsistent record ∧ Proofs.Records.LockCompatible record.legacy

omit [DecidableEq V] [Fintype V] in
theorem invariant_initial : Invariant Protocol.NamedRecord.initial :=
  ⟨NamedRecord.history_consistent_initial, Proofs.Records.lockCompatible_initial⟩

/-- The attestation duty preserves `Invariant`. -/
theorem invariant_attest (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (h : Invariant record) :
    Invariant (Protocol.NamedDuties.attest_with gc E hc nd st record).2.1 := by
  change Invariant (Protocol.NamedActions.round_action_with gc E hc nd st.core.toHealing record).1
  rw [Proofs.NamedActions.round_action_shared_read]
  exact ⟨NamedRecord.history_consistent_create record _ h.1,
    NamedRecord.lock_compatible_create record _ h.2⟩

/-- The named tick preserves `Invariant`. -/
theorem invariant_tick (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (h : Invariant record) :
    Invariant (Protocol.NamedTick.tick gc E hc cfg nd st record t).2.1 := by
  rw [NamedTick.tick_computed_duties]
  dsimp only
  split_ifs <;> first
    | exact h
    | exact invariant_attest gc E hc nd _ record h


#print axioms invariant_initial
end DecoupledConsensusModel.Proofs.NamedTickRecord

end
