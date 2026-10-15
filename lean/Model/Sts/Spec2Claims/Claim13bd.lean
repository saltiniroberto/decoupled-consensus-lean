module
public import Model.Sts.Conditions
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-!
# Recurring honest proposers from `tGAT`

The premise `strongOpeningsRecurFrom`, on the proposers of the rounds that open between `tGAT` and
`tAwakeEnd`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- From `tGAT` to `tAwakeEnd`, every window of `gap` periods starting at `t` contains, at least two
    periods after `t`, a slot `s` satisfying `MultiProposerAt`, and every slot that opens a period
    in the two periods before `s` has a proposer honest through its own confirmation instant. -/
def strongOpeningsRecurFrom (S : Setup V) (Sched : Schedule V) (tGAT tAwakeEnd : Int)
    (gap : Nat) : Prop :=
  ∀ t : Int, tGAT ≤ t → t + (gap : Int) * (constants S).period ≤ tAwakeEnd →
    ∃ s : Slot, t + 2 * (constants S).period ≤ (interface S Sched).proposalTime s ∧
      (interface S Sched).proposalTime s ≤ t + (gap : Int) * (constants S).period ∧
      MultiProposerAt S Sched (interface S Sched) (constants S) s ∧
      ∀ s' : Slot, (interface S Sched).opening s' →
        (interface S Sched).proposalTime s - 2 * (constants S).period ≤
          (interface S Sched).proposalTime s' →
        (interface S Sched).proposalTime s' < (interface S Sched).proposalTime s →
        HonestThroughTime Sched (Protocol.confirmation_time S.E s')
          ((interface S Sched).proposer s')

end DecoupledConsensusModel.Sts
