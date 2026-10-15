module
public import Proofs.Vocabulary.Protocol.ValidatorClient.RecordClean
public import Proofs.Vocabulary.Protocol.ChainState.NamedNjGap
public import Proofs.Vocabulary.Protocol.Handlers.StoreBridge
public import Proofs.Vocabulary.Internal.Definitions.NamedDerived
public import Proofs.Vocabulary.Internal.Internal.GradeReads
import Proofs.Vocabulary.Execution.Wire
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Protocol (ChainState HeightConfig derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- When the record at `h` has an empty or `J` target, a clear timeout bit and an empty or `J` lock,
    and the action head's chain state has justification height `h`, justified root `J` and finalized
    height less than `h`, the named round action emits the finality pair `⟨h, J⟩`. -/
theorem namedRoundAction_finality_pair_of_record_guard
    (contract : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.HealingStore V) (record : Protocol.NamedRecord)
    {h : Height} {J : BlockId}
    (htarget : record.legacy.target h = none ∨ record.legacy.target h = some J)
    (htimeout : record.legacy.timeout h = false)
    (hlock : record.legacy.lock h = none ∨ record.legacy.lock h = some J)
    (hhj : (st.σ (actionHeadWith contract E hc st)).h_j = h)
    (hJ : (st.σ (actionHeadWith contract E hc st)).J.root = J)
    (hF : (st.σ (actionHeadWith contract E hc st)).h_F < h) :
    (Protocol.NamedActions.round_action_with contract E hc nd st record).2.finality_pair =
      some ⟨h, J⟩ := by
  obtain ⟨Hd, hHd, heq⟩ :=
    _root_.DecoupledConsensusModel.Proofs.round_action_finality_pair
      contract E hc nd st record
  have hHdEq : Hd = actionHeadWith contract E hc st := hHd
  subst hHdEq
  rw [heq, hhj, hJ]
  have hguard :
      (record.legacy.target h = none ∨ record.legacy.target h = some J) ∧
        record.legacy.timeout h = false ∧
        (record.legacy.lock h = none ∨ record.legacy.lock h = some J) :=
    ⟨htarget, htimeout, hlock⟩
  simp only [Protocol.finality_pair, if_pos hF, if_pos hguard]

#print axioms namedRoundAction_finality_pair_of_record_guard

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
