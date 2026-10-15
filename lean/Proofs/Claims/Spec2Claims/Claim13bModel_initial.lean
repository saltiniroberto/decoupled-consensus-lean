module
public import Model.Vocabulary.Execution.Node
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `NamedNode.initial`

Lemmas that unfold the initial node state: its cache, clock and signing record.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedNode.initial
  DecoupledConsensusModel.Protocol.ChainState.initial
  DecoupledConsensusModel.Protocol.NamedRecord.initial
  DecoupledConsensusModel.Protocol.NamedStore.initial
  DecoupledConsensusModel.Protocol.Record.initial DecoupledConsensusModel.Protocol.Store.init
  DecoupledConsensusModel.Protocol.cacheAtRound DecoupledConsensusModel.Protocol.emptyFrame
  DecoupledConsensusModel.Protocol.initialCache DecoupledConsensusModel.Protocol.pendingFrame
  DecoupledConsensusModel.Protocol.phaseResult

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V]

/-- For every round and every phase, the frame the initial node state's cache holds for that round
    has no phase result of the form `some (some root)`. -/
theorem initial_cache_phaseResult_ne (r₁ : Round) (p : Protocol.Phase) (root : Block V) :
    Protocol.phaseResult
      (Protocol.cacheAtRound (NamedNode.initial : NamedNodeState V).cache r₁) p
      ≠ some (some root) := by
  intro hr
  simp only [NamedNode.initial, Protocol.initialCache, Protocol.cacheAtRound] at hr
  split_ifs at hr <;> cases p <;>
    simp [Protocol.phaseResult, Protocol.emptyFrame, Protocol.pendingFrame] at hr

/-- The clock of the initial node state's store is `0`. -/
theorem initial_clock_eq_zero : (NamedNode.initial : NamedNodeState V).st.core.t = 0 := rfl

/-- The signing record of the initial node state has no lock at any height `h`. -/
theorem initial_record_lock (h : Height) :
    (NamedNode.initial : NamedNodeState V).record.legacy.lock h = none := rfl

/-- The signing record of the initial node state has no target at any height `h`. -/
theorem initial_record_target (h : Height) :
    (NamedNode.initial : NamedNodeState V).record.legacy.target h = none := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V]

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V]

end DecoupledConsensusModel.Sts
