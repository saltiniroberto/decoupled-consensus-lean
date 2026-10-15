module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Model.Vocabulary.Objects.Identifiers

@[expose] public section

/-!
# Electorate and committees

The weighted electorate with its total weight, set weights and finality threshold, and the slot
committees, which carry membership only.
-/

open scoped BigOperators

namespace DecoupledConsensusModel

/-- A finite electorate with fixed positive weights. -/
structure Electorate (V : Type) [Fintype V] where
  /-- `w(v)`, the weight of each validator. -/
  weight : V → Nat
  /-- Weights are positive. -/
  weight_pos : ∀ i, 0 < weight i

namespace Electorate

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `W = w(V)`, the total weight. -/
def totalWeight (E : Electorate V) : Nat :=
  ∑ i, E.weight i

/-- `w(S)`, the total weight of the validators in `S`. -/
def weightOf (E : Electorate V) (S : Finset V) : Nat :=
  ∑ i ∈ S, E.weight i

/-- `q = ⌈2W/3⌉`, computed as `(2W+2)/3`. -/
def finalityThreshold (E : Electorate V) : Nat :=
  (2 * E.totalWeight + 2) / 3

/-- Whether the weight of `S` reaches the finality threshold `q`. -/
def quorumCheck (E : Electorate V) (S : Finset V) : Bool :=
  decide (E.finalityThreshold ≤ E.weightOf S)

end Electorate

/-- The fixed slot committees `K_s ⊆ V`; membership only, with no weight attached. -/
structure Committees (V : Type) where
  /-- `K_s`, the committee of slot `s`. -/
  members : Slot → Finset V

end DecoupledConsensusModel

end
