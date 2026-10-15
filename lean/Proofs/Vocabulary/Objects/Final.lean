module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Agreement

@[expose] public section


namespace DecoupledConsensusModel
namespace Protocol

open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## The slot times are ordered -/

theorem proposal_time_le_confirmation_time (E : Env V) (s : Slot) :
    Protocol.proposal_time E s ≤ Protocol.confirmation_time E s := by
  have h : ∀ a d : Int, 0 < d → a ≤ a + 6 * d := by intro a d hd; omega
  exact h (E.t s) E.Δ E.Δ_pos

theorem vote_time_le_confirmation_time (E : Env V) (s : Slot) :
    Protocol.vote_time E s ≤ Protocol.confirmation_time E s := by
  have h : ∀ a d : Int, 0 < d → a + d ≤ a + 6 * d := by intro a d hd; omega
  exact h (E.t s) E.Δ E.Δ_pos


end Protocol
end DecoupledConsensusModel

end
