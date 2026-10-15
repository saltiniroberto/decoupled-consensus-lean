import Proofs.Vocabulary.Protocol.Grades.Main
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.update_confirmation_with`: an eligible walk result

The confirmation update's write of `latest_confirmed` when the walk result passes the eligibility
test.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.update_confirmation_with

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the store passes the slot's eligibility test for the confirmation walk's result `W`, then the
    `latest_confirmed` that `update_confirmation_with` writes is `floor_on_stable` of the
    `latest_stable` it writes, `advance_confirmed` of the store's `latest_confirmed` with `W`, and
    the store's `latest_confirmed`. -/
theorem update_confirmation_with_latest_confirmed_of_eligible
    (contract : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (s : Slot)
    (hel : Protocol.confEligible E st s (Protocol.confWalkWith contract E hc st s) = true) :
    (Protocol.update_confirmation_with contract E hc st s).latest_confirmed
      = Protocol.floor_on_stable
          (Protocol.update_confirmation_with contract E hc st s).latest_stable
          (Protocol.advance_confirmed st.latest_confirmed
            (Protocol.confWalkWith contract E hc st s))
          st.latest_confirmed := by
  obtain ⟨select, hmode⟩ : ∃ select, contract.confirmationSG =
      Protocol.ConfirmationSGCandidate.optional select := by
    cases h : contract.confirmationSG with
    | optional select => exact ⟨select, rfl⟩
  show Protocol.floor_on_stable _ (match contract.confirmationSG with
      | .optional select =>
        if Protocol.confEligible E st s (Protocol.confWalkWith contract E hc st s) then
          Protocol.advance_confirmed st.latest_confirmed
            (Protocol.confWalkWith contract E hc st s)
        else match select E hc st.toHealing s with
          | some candidate => Protocol.advance_confirmed st.latest_confirmed candidate
          | none => st.latest_confirmed) st.latest_confirmed = _
  rw [hmode]
  dsimp only
  rw [if_pos hel]
  rfl

end DecoupledConsensusModel.Sts
