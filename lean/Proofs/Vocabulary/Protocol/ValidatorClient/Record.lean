module
public import Proofs.Vocabulary.Protocol.ValidatorClient.SlashableBound
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Named records

Facts about the named record and its signing call `create`: the encoded height pair erases to the
record's height pair, and `HistoryConsistent` holds initially and is preserved by `create`.
-/
namespace DecoupledConsensusModel.Proofs.NamedRecord
open Protocol
open Protocol.NamedRecord
open Proofs.HealingSurface
open Proofs.Records (LockCompatible)
variable {V : Type}

/-- Erasing the encoded height pair gives `height_pair` of the record. -/
theorem encode_height_erase (record : Record)
    (fields : Option (Height × BlockId × Bool)) (fp : Option FinalityPair) :
    (encodeHeight fields (height_pair record fields fp)).erase =
      height_pair record fields fp := by
  rcases Proofs.Engine.height_pair_cases (Λ := record) fields fp with he | ⟨h, entry, nu, hf, hp⟩
  · simp [encodeHeight, he, NamedHeightPair.erase]
  · rcases hp with ht | ht <;> rw [ht, hf] <;> rfl

/-- The erasure of the row `create` emits is the attestation `legacyCreate` emits on the erased
    record. -/
theorem create_erases (record : Protocol.NamedRecord) (input : Input V) :
    (create record input).2.erase = (legacyCreate record.legacy input).2 := by
  simp only [create, legacyCreate, create_attestation, encodeRow, NamedAttestation.erase,
    encode_height_erase]


/-- The record `create` returns, erased, is `record_attestation` of the old record at the erased row
    just emitted. -/
theorem create_legacy_records_erasure (record : Protocol.NamedRecord) (input : Input V) :
    (create record input).1.legacy =
      record_attestation record.legacy (create record input).2.erase := by
  rw [create_erases]
  rfl

/-- A nonempty height pair `create` emits names the height and entry of the input's height fields. -/
theorem create_names_source (record : Protocol.NamedRecord) (input : Input V)
    {h : Height} {entry : BlockId} {timeout : Bool}
    (hp : (create record input).2.height_pair = .vote h entry timeout) :
    ∃ nu, input.fields = some (h, entry, nu) := by
  cases hf : input.fields with
  | none => simp [create, legacyCreate, create_attestation, encodeRow, encodeHeight,
      height_pair, hf] at hp
  | some fields =>
    obtain ⟨k, target, nu⟩ := fields
    cases hpair : (legacyCreate record.legacy input).2.height_pair <;>
      simp [create, encodeRow, encodeHeight, hf, hpair] at hp
    all_goals
      obtain ⟨rfl, rfl, _⟩ := hp
      exact ⟨nu, rfl⟩

/-- A timeout entry after `record_attestation` was already set or comes from the row's timeout
    height pair. -/
private theorem timeout_update_iff (record : Record) (row : CombinedAttestation V) (h : Height) :
    (record_attestation record row).timeout h = true ↔
      record.timeout h = true ∨ row.height_pair = .timeout h := by
  constructor
  · intro hpost
    by_cases hpre : record.timeout h = true
    · exact Or.inl hpre
    · exact Or.inr (record_attestation_timeout_introduced
        (Bool.eq_false_of_not_eq_true hpre) hpost)
  · rintro (hpre | hp)
    · exact record_attestation_timeout_mono row hpre
    · exact record_attestation_timeout_true record row hp

/-- After `rememberTimeout`, the history has an entry at `h` exactly when it had one before or the
    pair is a timeout at `h`. -/
theorem remember_timeout_height_iff (history : Finset (Height × BlockId))
    (pair : NamedHeightPair) (h : Height) :
    (∃ entry, (h, entry) ∈ rememberTimeout history pair) ↔
      (∃ entry, (h, entry) ∈ history) ∨ pair.erase = .timeout h := by
  cases pair with
  | empty => simp [rememberTimeout, NamedHeightPair.erase]
  | vote k entry timeout =>
    cases timeout <;>
      simp [rememberTimeout, NamedHeightPair.erase, Prod.mk.injEq, exists_or, eq_comm, or_comm]

/-- The record's timeout bit at `h` is set exactly when its timeout history has an entry at `h`. -/
def HistoryConsistent (record : Protocol.NamedRecord) : Prop :=
  ∀ h, record.legacy.timeout h = true ↔ ∃ entry, (h, entry) ∈ record.timeoutHistory

/-- The initial named record satisfies `HistoryConsistent`. -/
theorem history_consistent_initial : HistoryConsistent Protocol.NamedRecord.initial := by
  simp [HistoryConsistent, Protocol.NamedRecord.initial, Record.initial]

/-- `create` preserves `HistoryConsistent`. -/
theorem history_consistent_create (record : Protocol.NamedRecord) (input : Input V)
    (hconsistent : HistoryConsistent record) : HistoryConsistent (create record input).1 := by
  intro h
  change (create record input).1.legacy.timeout h = true ↔
    ∃ entry, (h, entry) ∈ rememberTimeout record.timeoutHistory (create record input).2.height_pair
  rw [create_legacy_records_erasure, timeout_update_iff, remember_timeout_height_iff]
  change (record.legacy.timeout h = true ∨
    (create record input).2.height_pair.erase = .timeout h) ↔ _
  exact or_congr (hconsistent h) Iff.rfl

/-- `create` preserves `LockCompatible` of the erased record. -/
theorem lock_compatible_create (record : Protocol.NamedRecord) (input : Input V)
    (hlock : LockCompatible record.legacy) : LockCompatible (create record input).1.legacy := by
  exact lockCompatible_create_attestation hlock input.val_index input.round input.confirmed
    input.fields input.h_j input.J input.h_F


#print axioms encode_height_erase
#print axioms create_erases
#print axioms create_legacy_records_erasure
#print axioms create_names_source
#print axioms remember_timeout_height_iff
#print axioms history_consistent_initial
#print axioms history_consistent_create
#print axioms lock_compatible_create
end DecoupledConsensusModel.Proofs.NamedRecord

end
