module
public import Proofs.Vocabulary.Protocol.Schedule.StableRootSuffixOrigin
import Proofs.Vocabulary.Protocol.Handlers.TickBridges
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Origins of the confirmation record

A stored confirmation value is genesis, a block selected by a confirmation tick, or the stable root
written by a confirmation tick.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace ConfirmationOrigin

open Internal Execution Internal.NamedRecoveryRead Protocol Proofs.Optimistic
open StableRecord NamedOutageClosure

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A tick at a time other than a positive slot's support cutoff leaves `latest_confirmed`
    unchanged. -/
theorem on_tick_emit_latest_of_ne
    (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time)
    (h : ¬ (0 < S.E.slotOf t ∧
      t = Protocol.support_cutoff S.E (S.E.slotOf t))) :
    (on_tick_emit S v n t).1.st.latest_confirmed = n.st.latest_confirmed := by
  show (Protocol.NamedTick.tick
      (NamedProfile.gradeContract
        (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
      S.E S.hc S.cfg (S.node v) n.st n.record t).1.latest_confirmed =
      n.st.latest_confirmed
  simp only [Protocol.NamedTick.tick, Protocol.TickScheduler.runWith,
    Protocol.NamedTick.namedOps, if_neg h]
  split_ifs <;>
    simp only [Protocol.attest_with_latest,
      Protocol.propose_block_with_latest,
      Protocol.named_goldfish_vote_with_latest]

namespace StableRecord

end StableRecord

end ConfirmationOrigin

namespace StableRecord

open Internal Execution

variable {V : Type} [DecidableEq V] [Fintype V]

end StableRecord
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.ConfirmationOrigin
end DecoupledConsensusModel.Proofs.ConfirmationOrigin

namespace DecoupledConsensusModel.Proofs.StableRecord
end DecoupledConsensusModel.Proofs.StableRecord

end
