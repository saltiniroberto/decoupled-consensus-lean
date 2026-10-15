module
public import Proofs.Vocabulary.Protocol.Handlers.RetentionNamed
import Proofs.Vocabulary.Protocol.Handlers.TickBridges
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.RingTheory.WittVector.IsPoly

@[expose] public section

/-!
# The stable record at ticks

A tick other than a confirmation tick leaves the stable record unchanged.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace StableRecord

open Internal Execution Internal.NamedRecoveryRead Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A non-confirmation tick leaves the stable record unchanged. -/
theorem on_tick_emit_stable_of_ne
    (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time)
    (h : ¬ (0 < S.E.slotOf t ∧
      t = Protocol.support_cutoff S.E (S.E.slotOf t))) :
    (on_tick_emit S v n t).1.st.latest_stable = n.st.latest_stable := by
  show (Protocol.NamedTick.tick
      (NamedProfile.gradeContract
        (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
      S.E S.hc S.cfg (S.node v) n.st n.record t).1.latest_stable =
      n.st.latest_stable
  simp only [Protocol.NamedTick.tick, Protocol.TickScheduler.runWith,
    Protocol.NamedTick.namedOps, if_neg h]
  split_ifs <;>
    simp only [NamedOutageClosure.attest_with_stable,
      NamedOutageClosure.propose_block_with_stable,
      NamedOutageClosure.named_goldfish_vote_with_stable]


end StableRecord
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.StableRecord
end DecoupledConsensusModel.Proofs.StableRecord

end
