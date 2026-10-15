module
public import Model.Vocabulary.Protocol.Schedule

@[expose] public section

/-!
# The confirmation time and the next slot's support cutoff

The slot-`s` confirmation evaluation happens at the support cutoff of slot `s + 1`.
-/

namespace DecoupledConsensusModel
namespace Protocol

section Vocabulary

variable {V : Type} [DecidableEq V]

end Vocabulary

section Schedule

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The slot-`s` confirmation time `t_s + 6Δ` equals the support cutoff of slot `s + 1`,
    `t_{s+1} + 2Δ`. -/
theorem confirmation_time_eq_support_cutoff_succ (E : Env V) (s : Slot) :
    confirmation_time E s = support_cutoff E (s + 1) := by
  unfold confirmation_time support_cutoff Env.t slotStart
  push_cast
  ring

end Schedule

end Protocol
end DecoupledConsensusModel

end
