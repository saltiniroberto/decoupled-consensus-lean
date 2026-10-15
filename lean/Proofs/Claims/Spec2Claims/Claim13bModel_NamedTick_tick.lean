import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Proofs.Vocabulary.Protocol.Handlers.Admission
import Proofs.Claims.Spec2Claims.Claim13bModel_on_sg_vote

/-!
# Fields `Protocol.NamedTick.tick` does not write

At a time that is neither its slot's proposal time nor its slot's Goldfish vote time, the named tick
writes none of `F`, `J`, `h_j`, `h_max`, the block tree `T` and the named bodies.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Env.slotOf
  DecoupledConsensusModel.Protocol.NamedAdmission.admit_row
  DecoupledConsensusModel.Protocol.NamedDuties.attest_with
  DecoupledConsensusModel.Protocol.NamedDuties.update_confirmation_with
  DecoupledConsensusModel.Protocol.NamedStore.setClock
  DecoupledConsensusModel.Protocol.NamedTick.tick DecoupledConsensusModel.Protocol.proposal_time
  DecoupledConsensusModel.Protocol.update_confirmation_with
  DecoupledConsensusModel.Protocol.vote_time

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If `t` is neither the proposal time nor the Goldfish vote time of its slot, the named store the
    tick returns at `t` has the finalized block, the justified block, the justified height, the
    largest height, the block tree and the bodies of the store it was given. -/
theorem namedTick_tree_fields_of_not_proposal_vote
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Int)
    (hnp : t ≠ Protocol.proposal_time E (E.slotOf t))
    (hnv : t ≠ Protocol.vote_time E (E.slotOf t)) :
    (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core.F = st.core.F ∧
      (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core.J = st.core.J ∧
      (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core.h_j = st.core.h_j ∧
      (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core.h_max = st.core.h_max ∧
      (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core.T = st.core.T ∧
      (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.bodies = st.bodies := by
  let s := E.slotOf t
  let st0 := Protocol.NamedStore.setClock E st t
  let proposed := Protocol.NamedDuties.propose_block_with gc E hc cfg nd st0
  let proposalDue := 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index
  let st1 := if proposalDue then proposed.1 else st0
  let emitted1 : List (NamedObject V) := if proposalDue then
    match proposed.2 with | none => [] | some C => [.block C]
    else []
  let voted := Protocol.NamedDuties.goldfish_vote_with gc E hc nd st1
  let voteDue := 0 < s ∧ t = Protocol.vote_time E s
  let st2 := if voteDue then voted.1 else st1
  let emitted2 : List (NamedObject V) :=
    if voteDue then voted.2.toList.map NamedObject.gfVote else []
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff E s then
    Protocol.NamedDuties.update_confirmation_with gc E hc st2 (s - 1) else st2
  have hpdue : ¬ proposalDue := fun h => hnp h.2.1
  have hvdue : ¬ voteDue := fun h => hnv h.2
  have h1 : st1 = st0 := by dsimp only [st1]; rw [if_neg hpdue]
  have h2 : st2 = st0 := by dsimp only [st2]; rw [if_neg hvdue]; exact h1
  have h3 : st3.core.F = st.core.F ∧ st3.core.J = st.core.J ∧ st3.core.h_j = st.core.h_j ∧
      st3.core.h_max = st.core.h_max ∧ st3.core.T = st.core.T ∧ st3.bodies = st.bodies := by
    dsimp only [st3]
    rw [h2]
    split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hout := Proofs.NamedTick.tick_computed_duties gc E hc cfg nd st record t
  change Protocol.NamedTick.tick gc E hc cfg nd st record t =
    (if t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true then
      let a := Protocol.NamedDuties.attest_with gc E hc nd st3 record
      (a.1, a.2.1, emitted1 ++ emitted2 ++ [NamedObject.attest a.2.2])
    else (st3, record, emitted1 ++ emitted2)) at hout
  rw [hout]
  split_ifs
  · show (Protocol.NamedAdmission.admit_row hc st3 _).core.F = _ ∧
      (Protocol.NamedAdmission.admit_row hc st3 _).core.J = _ ∧
      (Protocol.NamedAdmission.admit_row hc st3 _).core.h_j = _ ∧
      (Protocol.NamedAdmission.admit_row hc st3 _).core.h_max = _ ∧
      (Protocol.NamedAdmission.admit_row hc st3 _).core.T = _ ∧
      (Protocol.NamedAdmission.admit_row hc st3 _).bodies = _
    rw [Proofs.NamedAdmission.admit_row_core, Proofs.NamedAdmission.admit_row_bodies]
    obtain ⟨aF, aJ, ahj, ahm, aT⟩ := on_sg_vote_tree_fields hc st3.core
      (Protocol.NamedActions.round_action_with gc E hc nd st3.core.toHealing record).2.erase
    obtain ⟨bF, bJ, bhj, bhm, bT, bB⟩ := h3
    exact ⟨aF.trans bF, aJ.trans bJ, ahj.trans bhj, ahm.trans bhm, aT.trans bT, bB⟩
  · exact h3

end DecoupledConsensusModel.Sts
