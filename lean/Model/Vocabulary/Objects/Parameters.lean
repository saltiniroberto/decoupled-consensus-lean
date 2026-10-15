module
public import Model.Vocabulary.Objects.Blocks
public import Model.Vocabulary.Objects.Time
public import Model.Vocabulary.Objects.Weights

@[expose] public section

/-!
# Protocol environment

The fixed environment of the protocol: the schedule unit `Δ`, `t_GST`, the proposer and committee of
each slot, and the weighted electorate, with the slot and weight reads derived from it.
-/

namespace DecoupledConsensusModel

/-- The fixed protocol environment. -/
structure Env (V : Type) [DecidableEq V] [Fintype V] where
  /-- `Δ`: the schedule unit, and a strict delivery bound after `t_GST`. -/
  Δ : Time
  /-- `Δ` is positive, so `t_s = 4Δs` is strictly increasing. -/
  Δ_pos : 0 < Δ
  /-- `t_GST`: after it, `Δ` bounds delivery and honest nodes relay every object they process. -/
  t_GST : Time
  /-- `t_GST` is not negative. -/
  t_GST_nonneg : 0 ≤ t_GST
  /-- The assigned proposer of each slot. -/
  proposer : Slot → V
  /-- The committee `K_s ⊆ V` of each slot. -/
  committees : Committees V
  /-- The weighted electorate `w(·)`. -/
  electorate : Electorate V

namespace Env

variable {V : Type} [DecidableEq V] [Fintype V] (E : Env V)

/-- `K_s`, the committee of slot `s`. -/
def committee (s : Slot) : Finset V :=
  E.committees.members s

/-- `t_s = 4Δs`, the start of slot `s`. -/
def t (s : Slot) : Time :=
  slotStart E.Δ s

/-- The slot containing time `u`, `⌊u / 4Δ⌋`. -/
def slotOf (u : Time) : Slot :=
  slotOfTime E.Δ u

/-- `W = w(V)`, the total weight. -/
def W : Nat :=
  E.electorate.totalWeight

/-- `q = ⌈2W/3⌉`, the finality threshold. -/
def q : Nat :=
  E.electorate.finalityThreshold

end Env

end DecoupledConsensusModel

end
