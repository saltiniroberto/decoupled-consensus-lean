module
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.WithBot
public import Model.Vocabulary.Objects.Identifiers

@[expose] public section

/-!
# Time and timestamps

Time, stamps with `−∞` for genesis, occurrences with `+∞` for events that never happen, timestamp
maps, the strict cutoff tests and views, and slot arithmetic.
-/

namespace DecoupledConsensusModel

/-- The time domain. -/
abbrev Time := Int

/-- A processing time: a time, or `⊥ = −∞` for genesis. -/
abbrev Stamp := WithBot Time

/-- An event time: a stamp, or `+∞` (`none`) when the event never occurs. -/
abbrev Occurrence := Option Stamp

/-- The genesis stamp, `−∞`. -/
def genesisStamp : Stamp := ⊥

/-- A timestamp map: the insertion time of each processed object; `none` when the object was never
    processed. -/
abbrev TimestampMap (α : Type) := α → Option Stamp

variable {α : Type}

/-- The strict cutoff test `timestamp(x) < Γ`; an unstamped object fails it. -/
def stampedBefore (ts : TimestampMap α) (Γ : Time) (x : α) : Bool :=
  match ts x with
  | none => false
  | some u => decide (u < (Γ : Stamp))

/-- The strict cutoff view `{x ∈ S : timestamp(x) < Γ}`. -/
def beforeCutoff [DecidableEq α] (ts : TimestampMap α) (Γ : Time)
    (S : Finset α) : Finset α :=
  S.filter (fun x => stampedBefore ts Γ x = true)

/-- The strict cutoff test `x < Γ` on an occurrence; `+∞` fails it and `−∞` passes it. -/
def occurrenceBefore (x : Occurrence) (Γ : Time) : Bool :=
  match x with
  | none => false
  | some u => decide (u < (Γ : Stamp))

/-- The maximum of two occurrences, `+∞` absorbing. -/
def occurrenceMax (x y : Occurrence) : Occurrence :=
  match x, y with
  | some a, some b => some (max a b)
  | _, _ => none

/-- `t_s = 4Δs`, the start of slot `s`. -/
def slotStart (Δ : Time) (s : Slot) : Time :=
  4 * Δ * (s : Time)

/-- `s = ⌊t / 4Δ⌋`, the slot containing `t`; negative times give slot `0`. -/
def slotOfTime (Δ : Time) (t : Time) : Slot :=
  (Int.fdiv t (4 * Δ)).toNat

end DecoupledConsensusModel

end
