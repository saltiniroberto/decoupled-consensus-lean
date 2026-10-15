module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalSnapshotBridge
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
public import Proofs.Vocabulary.Protocol.Handlers.GoldfishVotePool
import Proofs.Vocabulary.Generic.Sync
import Proofs.Vocabulary.Protocol.ChainState.ProposalBridge
import Proofs.Vocabulary.Protocol.Handlers.AcceptanceTiming
import Proofs.Vocabulary.Protocol.Handlers.Proposer
import Proofs.Vocabulary.Protocol.Schedule.CanonicalSuffixPostGSTCore
import Proofs.Vocabulary.Protocol.Schedule.ProposalCanonicality
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]


private theorem slotOf_of_proposal_before_next_proposal
    (E : Env V) (s : Slot) {p : Time}
    (hlo : Protocol.proposal_time E s ≤ p)
    (hhi : p < Protocol.proposal_time E (s + 1)) :
    E.slotOf p = s := by
  have hbounds : ∀ a d q : Int, 0 < d → a ≤ q → q < a + 4 * d →
      0 ≤ q - a ∧ q - a < 4 * d := by
    intro a d q hd h1 h2
    omega
  have hnext : Protocol.proposal_time E (s + 1) = E.t s + 4 * E.Δ := by
    unfold Protocol.proposal_time Env.t slotStart
    push_cast
    ring
  have hhi' : p < E.t s + 4 * E.Δ := by rwa [← hnext]
  obtain ⟨h0, h1⟩ := hbounds (E.t s) E.Δ p E.Δ_pos hlo hhi'
  have hrw : p = 4 * E.Δ * (s : Time) + (p - E.t s) := by
    unfold Env.t slotStart
    ring
  rw [Env.slotOf, hrw]
  exact Proofs.Optimistic.slotOfTime_add E.Δ E.Δ_pos s _ h0 h1


end HealingSurface
end Proofs
end DecoupledConsensusModel

end


