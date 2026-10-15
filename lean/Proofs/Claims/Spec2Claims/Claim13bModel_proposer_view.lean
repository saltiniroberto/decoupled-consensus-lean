import Model.Vocabulary.Protocol.ForkChoice.Views
import Model.Vocabulary.Protocol.Store
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.proposer_view` and `Protocol.proposer_support_view`

Lemmas that unfold the proposer's views of a Goldfish store.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.GoldfishStore.pool
  DecoupledConsensusModel.Protocol.Store.toHealing
  DecoupledConsensusModel.Protocol.proposer_support_view
  DecoupledConsensusModel.Protocol.proposer_view

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- The slot-`s` proposer view of `gs` is the list of `gs`'s slot-`(s − 1)` Goldfish votes. -/
theorem proposer_view_eq (gs : Protocol.GoldfishStore V) (s : Slot) :
    Protocol.proposer_view gs s = gs.gf_votes (s - 1) := rfl

omit [Fintype V] in
/-- The votes of the slot-`s` proposer view of `gs` are the votes `gs` pools for slot `s − 1`. -/
theorem proposer_view_toFinset (gs : Protocol.GoldfishStore V) (s : Slot) :
    (Protocol.proposer_view gs s).toFinset = gs.pool (s - 1) := rfl

omit [Fintype V] in
/-- A vote is in the slot-`s` proposer support view of `gs` exactly when it is among `gs`'s
    slot-`(s − 1)` Goldfish votes and resolves in `gs`'s tree. -/
theorem mem_proposer_support_view_iff (gs : Protocol.GoldfishStore V) (s : Slot)
    (u : GoldfishVote V) :
    u ∈ Protocol.proposer_support_view gs s ↔
      u ∈ gs.gf_votes (s - 1) ∧ Protocol.resolved gs.T u = true := by
  simp only [Protocol.proposer_support_view, List.mem_filter, decide_eq_true_eq]

omit [Fintype V] in
/-- The slot-`k` proposer view of the store `st` with its clock set to `t` and its slot set to `s`
    is the slot-`k` proposer view of `st`. -/
theorem proposer_view_set_clock_slot (st : Protocol.Store V) (t : Int) (s k : Slot) :
    Protocol.proposer_view
        ({ st with t := t, s := s } : Protocol.Store V).toHealing.toFG.toSG.toGoldfishStore k
      = Protocol.proposer_view st.toHealing.toFG.toSG.toGoldfishStore k := rfl

end DecoupledConsensusModel.Sts
