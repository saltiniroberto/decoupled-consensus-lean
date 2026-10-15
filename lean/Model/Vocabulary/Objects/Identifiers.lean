module
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Basic

@[expose] public section

/-!
# Identifiers

Slots, heights, rounds, and block roots with their fixed total order.
-/

namespace DecoupledConsensusModel

/-- A slot number. -/
abbrev Slot := Nat

/-- A height: the finality counter, separate from the slot. -/
abbrev Height := Nat

/-- A round index; round `r` is slots `rR … rR+R−1`. -/
abbrev Round := Nat

/-- A block root: the identity of a block. -/
@[ext]
structure BlockId where
  /-- The underlying value; only equality and the order on roots are used. -/
  value : Nat
deriving DecidableEq, Repr

private theorem BlockId.value_injective : Function.Injective BlockId.value := by
  intro left right equal
  exact BlockId.ext equal

/-- The fixed total order on roots, used to break ties. -/
instance : LinearOrder BlockId :=
  LinearOrder.lift' BlockId.value (by exact BlockId.value_injective)

/-- The root of the genesis block, the least root. -/
def genesisRoot : BlockId := ⟨0⟩

end DecoupledConsensusModel

end
