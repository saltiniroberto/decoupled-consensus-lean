import Proofs.Claims.Spec2Claims.Claim13bK_PrevHeadsStep
import Proofs.Claims.Spec2Claims.Claim13bModel_advance_confirmed_phase
import Proofs.Claims.Spec2Claims.Claim13bModel_advance_confirmed
import Proofs.Claims.Spec2Claims.Claim13bModel_floor_on_stable_phase
import Proofs.Claims.Spec2Claims.Claim13bModel_get_stable
import Proofs.Claims.Spec2Claims.Claim13bModel_get_confirmed
import Proofs.Claims.Spec2Claims.Claim13bModel_frameStableRoot
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeContract
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedNode_tick
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclX
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmation_time
import Proofs.Claims.Spec2Claims.Claim13bModel_slotStart
import Proofs.Claims.Spec2Claims.Claim13bModel_support_cutoff
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock
import Proofs.Claims.Spec2Claims.Claim13bModel_floor_on_stable
import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with
import Proofs.Claims.Spec2Claims.Claim13bModel_on_sg_vote
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_attest_with
import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with_phase
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Vocabulary.ModelProperties.Block_compatible

/-!
# The two records after a confirmation tick

`namedTick_records_at_confirmation` gives the `latest_stable` and `latest_confirmed` a tick writes
at a slot's support cutoff. The namespace `ConfirmedSettleScenario` holds a concrete tree and a
store holding a block of an abandoned branch as both records.
-/

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

section Protocol

end Protocol

/-! ### A concrete tree and store -/

namespace ConfirmedSettleScenario

/-- A child of genesis, the last block the two branches of the scenario share. -/
def X : Block Unit := .node .genesis 1 ⟨1⟩ [] [] [] ()

/-- A child of `X`, on the branch the healing abandons. -/
def A₁ : Block Unit := .node X 2 ⟨2⟩ [] [] [] ()

/-- A store before the tick: the initial store with `A₁` as both records. -/
def before : Protocol.Store Unit :=
  { Protocol.Store.init with latest_stable := A₁, latest_confirmed := A₁ }

end ConfirmedSettleScenario

/-! ## The two records after a confirmation tick -/

/-- A tick at an instant that is its own slot's support cutoff and no slot's proposal or Goldfish
    vote instant returns a store whose `latest_stable` and `latest_confirmed` are those the
    confirmation update of the clock-stamped store wrote, at the slot before the instant's own. -/
theorem namedTick_records_at_confirmation
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Int)
    (hspos : 0 < E.slotOf t)
    (hnp : t ≠ Protocol.proposal_time E (E.slotOf t))
    (hnv : t ≠ Protocol.vote_time E (E.slotOf t))
    (hsc : t = Protocol.support_cutoff E (E.slotOf t)) :
    (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core.latest_stable
        = (Protocol.update_confirmation_with gc E hc
            (Protocol.NamedStore.setClock E st t).core (E.slotOf t - 1)).latest_stable ∧
      (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core.latest_confirmed
        = (Protocol.update_confirmation_with gc E hc
            (Protocol.NamedStore.setClock E st t).core (E.slotOf t - 1)).latest_confirmed := by
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
  have h3 : st3 = Protocol.NamedDuties.update_confirmation_with gc E hc st0 (s - 1) := by
    dsimp only [st3]
    rw [if_pos (show 0 < s ∧ t = Protocol.support_cutoff E s from ⟨hspos, hsc⟩), h2]
  have hout := Proofs.NamedTick.tick_computed_duties gc E hc cfg nd st record t
  change Protocol.NamedTick.tick gc E hc cfg nd st record t =
    (if t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true then
      let a := Protocol.NamedDuties.attest_with gc E hc nd st3 record
      (a.1, a.2.1, emitted1 ++ emitted2 ++ [NamedObject.attest a.2.2])
    else (st3, record, emitted1 ++ emitted2)) at hout
  rw [hout]
  split_ifs
  · obtain ⟨ha, hb⟩ := attest_with_records gc E hc nd st3 record
    show (Protocol.NamedDuties.attest_with gc E hc nd st3 record).1.core.latest_stable = _ ∧
      (Protocol.NamedDuties.attest_with gc E hc nd st3 record).1.core.latest_confirmed = _
    rw [ha, hb, h3, namedDuties_update_confirmation_with_core]
    exact ⟨rfl, rfl⟩
  · show st3.core.latest_stable = _ ∧ st3.core.latest_confirmed = _
    rw [h3, namedDuties_update_confirmation_with_core]
    exact ⟨rfl, rfl⟩

end DecoupledConsensusModel.Sts
