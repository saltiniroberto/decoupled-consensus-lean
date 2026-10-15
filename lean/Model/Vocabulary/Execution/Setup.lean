module
public import Model.Vocabulary.Objects.Blocks
public import Model.Vocabulary.Objects.Parameters
public import Model.Vocabulary.Protocol.Schedule
public import Model.Vocabulary.Protocol.Grades
public import Model.Vocabulary.Protocol.ChainState

@[expose] public section

/-!
# The fixed data of a run

Root collision freedom on the ancestors of a set of blocks, and `Setup`, the environment and
parameters every handler takes, with the round action time.
-/

section
/-! ## Root collision freedom -/

namespace DecoupledConsensusModel
namespace Execution

variable {V : Type} [DecidableEq V]

/-- Roots identify blocks among the ancestors of the blocks in `S`: two such ancestors with the same
    root are equal. -/
def RootInjectiveBelow (S : Finset (Block V)) : Prop :=
  ∀ A C : Block V, (∃ B ∈ S, A ⪯ B) → (∃ B ∈ S, C ⪯ B) → A.root = C.root → A = C

/-- Root collision freedom across the ancestors of two chain tips. -/
def RootInjectiveOnAncestors (tip₁ tip₂ : Block V) : Prop :=
  RootInjectiveBelow {tip₁, tip₂}

end Execution
end DecoupledConsensusModel
end

section
/-! ## The fixed data of a run -/

namespace DecoupledConsensusModel
namespace Execution

open Protocol (HeightConfig)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The fixed data of a run: the protocol environment, the healing schedule, the height
    configuration and the node each validator runs, with the conditions they satisfy. -/
structure Setup (V : Type) [DecidableEq V] [Fintype V] where
  /-- The protocol environment and electorate. -/
  E : Env V
  /-- The healing round schedule. -/
  hc : Protocol.HealConfig
  /-- The finality-gadget height parameters. -/
  cfg : HeightConfig
  /-- The named node each validator runs. -/
  node : V → Protocol.Node V
  /-- The node's validator identity, equal to the validator running it. -/
  node_val_index : ∀ v, (node v).val_index = v
  /-- The timeout is a whole number of rounds and at least two rounds. -/
  timeout_rounds : hc.R ∣ cfg.timeoutDelay ∧ 2 * hc.R ≤ cfg.timeoutDelay
  /-- Every committee is nonempty. -/
  committee_nonempty : ∀ s, (E.committee s).Nonempty
  /-- The healing parameters satisfy `4 ≤ R · η_SG`. -/
  outage_window : 4 ≤ hc.R * hc.η_SG

namespace Setup

variable (S : Setup V)

/-- `a_r = t_{rR} + 6Δ`, the action time of round `r`. -/
abbrev a (r : Round) : Time := S.hc.a S.E.Δ r

end Setup

end Execution
end DecoupledConsensusModel
end

end
