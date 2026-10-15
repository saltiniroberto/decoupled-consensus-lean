module
public import Proofs.Vocabulary.Protocol.Handlers.TickBridges

@[expose] public section


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingLemmas

open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## The SG pool only grows -/

omit [Fintype V] in
/-- `on_sg_vote` keeps every attestation of the SG pool. -/
theorem sg_pool_subset_on_sg_vote (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (a : CombinedAttestation V) (r : Round) :
    st.sg_pool r ⊆ (Protocol.on_sg_vote hc st a).sg_pool r := by
  intro b hb
  simp only [Protocol.Store.sg_pool] at hb ⊢
  simp only [Protocol.on_sg_vote]
  split_ifs with h1
  · exact hb
  · dsimp only
    split_ifs with hr
    · rw [List.toFinset_append]
      exact Finset.mem_union_left _ hb
    · exact hb

omit [Fintype V] in
private theorem admit_row_core (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st row).core =
      Protocol.on_sg_vote hc st.core row.erase := by
  simp only [Protocol.NamedAdmission.admit_row]
  split_ifs <;> rfl

omit [Fintype V] in
/-- `admit_row` keeps every attestation of the SG pool. -/
private theorem admit_row_sg_pool_subset (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (row : NamedAttestation V) (r : Round) :
    st.core.sg_pool r ⊆ (Protocol.NamedAdmission.admit_row hc st row).core.sg_pool r := by
  rw [admit_row_core]
  exact sg_pool_subset_on_sg_vote hc st.core row.erase r

omit [Fintype V] in

/-- `admit_rows` keeps every attestation of the SG pool. -/
private theorem admit_rows_sg_pool_subset (hc : Protocol.HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : Protocol.NamedStore V) (r : Round),
      st.core.sg_pool r ⊆ (Protocol.NamedAdmission.admit_rows hc st rows).core.sg_pool r := by
  intro rows
  induction rows with
  | nil => intro st r; exact Finset.Subset.refl _
  | cons a l ih =>
      intro st r
      have h : Protocol.NamedAdmission.admit_rows hc st (a :: l) =
          Protocol.NamedAdmission.admit_rows hc
            (Protocol.NamedAdmission.admit_row hc st a) l := rfl
      rw [h]
      exact (admit_row_sg_pool_subset hc st a r).trans (ih _ r)

/-- The named block handler keeps every attestation of the SG pool. -/
private theorem on_block_with_sg_pool_subset (adm : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (r : Round) :
    st.core.sg_pool r ⊆
      (Protocol.NamedAdmission.on_block_with adm E hc cfg st B).core.sg_pool r := by
  have hcore : (Protocol.NamedStore.process_block_core E hc cfg st B).core.sg_pool r =
      st.core.sg_pool r := by
    simp only [Protocol.Store.sg_pool, Proofs.Optimistic.process_block_core_sg_votes]
  cases adm with
  | alsoCarried =>
      rw [show Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st B =
          (if B ∉ st.bodies ∧
              B ∈ (Protocol.NamedStore.process_block_core E hc cfg st B).bodies then
            Protocol.NamedAdmission.admit_rows hc
              (Protocol.NamedStore.process_block_core E hc cfg st B) B.attestations
          else Protocol.NamedStore.process_block_core E hc cfg st B) from rfl]
      split_ifs
      · exact hcore ▸ admit_rows_sg_pool_subset hc B.attestations _ r
      · exact hcore ▸ Finset.Subset.refl _

private theorem propose_block_with_sg_pool_subset (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (r : Round) :
    st.core.sg_pool r ⊆
      (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).1.core.sg_pool r := by
  simp only [Protocol.NamedDuties.propose_block_with]
  split
  · exact Finset.Subset.refl _
  · exact on_block_with_sg_pool_subset .alsoCarried E hc cfg st _ r

private theorem attest_with_sg_pool_subset (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (r : Round) :
    st.core.sg_pool r ⊆
      (Protocol.NamedDuties.attest_with contract E hc nd st record).1.core.sg_pool r :=
  admit_row_sg_pool_subset hc st _ r

/-- The tick scheduler keeps every attestation of the SG pool. -/
private theorem runWith_sg_pool_subset
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (ops : Protocol.TickScheduler.TickOps (Protocol.NamedStore V) Protocol.NamedRecord
      (NamedBlock V) (GoldfishVote V) (NamedAttestation V))
    (hclock : ∀ (st0 : Protocol.NamedStore V) (t' : Time) (s' : Slot) (r : Round),
      (ops.clock st0 t' s').core.sg_pool r = st0.core.sg_pool r)
    (hprop : ∀ (st0 : Protocol.NamedStore V) (r : Round),
      st0.core.sg_pool r ⊆ (ops.proposal st0).1.core.sg_pool r)
    (hvote : ∀ (st0 : Protocol.NamedStore V) (r : Round),
      (ops.vote st0).1.core.sg_pool r = st0.core.sg_pool r)
    (hconf : ∀ (st0 : Protocol.NamedStore V) (s' : Slot) (r : Round),
      (ops.confirmation st0 s').core.sg_pool r = st0.core.sg_pool r)
    (hatt : ∀ (st0 : Protocol.NamedStore V) (record0 : Protocol.NamedRecord) (r : Round),
      st0.core.sg_pool r ⊆ (ops.attestation st0 record0).1.core.sg_pool r)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time) (r : Round) :
    st.core.sg_pool r ⊆ (Protocol.TickScheduler.runWith E hc nd ops
        NamedObject.block NamedObject.gfVote NamedObject.attest
        (fun st record emitted => (st, record, emitted)) st record t).1.core.sg_pool r := by
  simp only [Protocol.TickScheduler.runWith,
    apply_ite (fun p : Protocol.NamedStore V × Protocol.NamedRecord × List (NamedObject V) =>
      p.1.core.sg_pool r)]
  set st1 := (if 0 < E.slotOf t ∧ t = Protocol.proposal_time E (E.slotOf t) ∧
      E.proposer (E.slotOf t) = nd.val_index then
        (ops.proposal (ops.clock st t (E.slotOf t))).1
      else ops.clock st t (E.slotOf t)) with hst1
  set st2 := (if 0 < E.slotOf t ∧ t = Protocol.vote_time E (E.slotOf t) then
      (ops.vote st1).1 else st1) with hst2
  set st3 := (if 0 < E.slotOf t ∧ t = Protocol.support_cutoff E (E.slotOf t) then
      ops.confirmation st2 (E.slotOf t - 1) else st2) with hst3
  have hstep1 : st.core.sg_pool r ⊆ st1.core.sg_pool r := by
    rw [hst1]
    split_ifs with hP1
    · have heq := hclock st t (E.slotOf t) r
      rw [← heq]
      exact hprop (ops.clock st t (E.slotOf t)) r
    · rw [hclock st t (E.slotOf t) r]
  have hstep2 : st1.core.sg_pool r ⊆ st2.core.sg_pool r := by
    rw [hst2]
    split_ifs with hP2
    · rw [hvote st1 r]
    · exact Finset.Subset.refl _
  have hstep3 : st2.core.sg_pool r ⊆ st3.core.sg_pool r := by
    rw [hst3]
    split_ifs with hP3
    · rw [hconf st2 (E.slotOf t - 1) r]
    · exact Finset.Subset.refl _
  have hchain : st.core.sg_pool r ⊆ st3.core.sg_pool r :=
    hstep1.trans (hstep2.trans hstep3)
  by_cases hP4 : t = hc.a E.Δ (hc.round_of (ops.slot st3)) ∧
      nd.awake (hc.round_of (ops.slot st3)) = true
  · rw [if_pos hP4]
    exact hchain.trans (hatt st3 record r)
  · rw [if_neg hP4]
    exact hchain


/-- A tick keeps every attestation of the SG pool. -/
private theorem on_tick_emit_sg_pool_subset (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    (r : Round) : n.st.core.sg_pool r ⊆ (on_tick_emit S v n t).1.st.core.sg_pool r := by
  simp only [NamedNode.tick, NamedProfile.tick, Protocol.NamedTick.tick]
  exact runWith_sg_pool_subset S.E S.hc (S.node v)
    (Protocol.NamedTick.namedOps
      (NamedProfile.gradeContract
        (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
      S.E S.hc S.cfg (S.node v))
    (fun st0 t' s' _r => rfl)
    (fun st0 r =>
      propose_block_with_sg_pool_subset
        (NamedProfile.gradeContract
          (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
        S.E S.hc S.cfg (S.node v) st0 r)
    (fun st0 r => by
      simp only [Protocol.NamedTick.namedOps, Protocol.Store.sg_pool,
        Proofs.Optimistic.goldfish_vote_with_sg_votes])
    (fun st0 s' r => by
      simp only [Protocol.NamedTick.namedOps, Protocol.Store.sg_pool,
        Proofs.Optimistic.update_confirmation_with_sg_votes])
    (fun st0 record0 r =>
      attest_with_sg_pool_subset
        (NamedProfile.gradeContract
          (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
        S.E S.hc (S.node v) st0 record0 r)
    n.st n.record t r

theorem sg_pool_subset_on_tick_emit (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    (r : Round) : n.st.sg_pool r ⊆ (on_tick_emit S v n t).1.st.sg_pool r :=
  on_tick_emit_sg_pool_subset S v n t r

/-- Processing an object keeps every attestation of the SG pool. -/
theorem sg_pool_subset_process (S : Setup V) (n : NodeState V) (o : Object V)
    (r : Round) : n.st.sg_pool r ⊆ (n.process S o).st.sg_pool r := by
  cases o with
  | block B => exact on_block_with_sg_pool_subset .alsoCarried S.E S.hc S.cfg n.st B r
  | gfVote g =>
      simp only [NodeState.process, NamedNode.process, NamedReceipt.process,
        Protocol.Store.sg_pool, Proofs.Optimistic.on_goldfish_vote_checked_sg_votes]
      exact Finset.Subset.refl _
  | attest a => exact admit_row_sg_pool_subset S.hc n.st a r


end HealingLemmas

end Proofs
end DecoupledConsensusModel

end
