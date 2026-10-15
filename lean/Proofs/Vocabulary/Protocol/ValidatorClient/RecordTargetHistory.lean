module
public import Proofs.Vocabulary.Protocol.ValidatorClient.Bridge
public import Proofs.Vocabulary.ModelProperties.NamedNode_initial
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Origin of record targets and locks

A new target or lock entry in a validator's record was written by an attestation that validator's
own tick emitted.
-/


namespace DecoupledConsensusModel
namespace Protocol

open Protocol (Record create_attestation finality_pair record_attestation)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
/-- If `record_attestation` sets a target `T` at a height `h` that had none, the attestation's
    height pair is `target h T`. -/
theorem record_attestation_target_introduced {Λ : Record}
    {a : CombinedAttestation V} {h : Height} {T : BlockId}
    (hpre : Λ.target h = none)
    (hpost : (record_attestation Λ a).target h = some T) :
    a.height_pair = HeightPair.target h T := by
  simp only [record_attestation] at hpost
  cases hfp : a.finality_pair <;> cases hhp : a.height_pair <;>
    simp_all [Record.with_lock, Record.with_timeout]
  all_goals
    split at hpost
    · rename_i hfresh
      simp only [Record.with_target] at hpost
      split at hpost
      · rename_i heq
        exact ⟨heq.symm, Option.some.inj hpost⟩
      · rw [hpre] at hpost
        contradiction
    · rw [hpre] at hpost
      contradiction

omit [DecidableEq V] [Fintype V] in
/-- If `record_attestation` sets a lock `T` at a height `h` that had none, the attestation's
    finality pair is `⟨h, T⟩`. -/
theorem record_attestation_lock_introduced {Λ : Record}
    {a : CombinedAttestation V} {h : Height} {T : BlockId}
    (hpre : Λ.lock h = none)
    (hpost : (record_attestation Λ a).lock h = some T) :
    a.finality_pair = some ⟨h, T⟩ := by
  cases hfp : a.finality_pair with
  | none =>
      have hunchanged : (record_attestation Λ a).lock h = Λ.lock h := by
        simp only [record_attestation, hfp]
        split <;> first | rfl | (split <;> rfl)
      rw [hunchanged, hpre] at hpost
      exact absurd hpost (by simp)
  | some p =>
      have hlock : (record_attestation Λ a).lock h =
          (Λ.with_lock p.height p.target).lock h := by
        simp only [record_attestation, hfp]
        split <;> first | rfl | (split <;> rfl)
      rw [hlock] at hpost
      by_cases hne : h = p.height
      · subst hne
        rw [Proofs.Records.with_lock_self] at hpost
        have hT : p.target = T := Option.some.inj hpost
        subst hT
        cases p
        rfl
      · rw [Proofs.Records.with_lock_ne hne, hpre] at hpost
        exact absurd hpost (by simp)


omit [DecidableEq V] [Fintype V] in
private theorem erase_finality_pair (a : NamedAttestation V) :
    a.erase.finality_pair = a.finality_pair := rfl

omit [DecidableEq V] [Fintype V] in
private theorem encodeHeight_erase_of (record : Record)
    (fields : Option (Height × BlockId × Bool)) (fp : Option FinalityPair) :
    (Protocol.NamedRecord.encodeHeight fields
      (Protocol.height_pair record fields fp)).erase =
      Protocol.height_pair record fields fp := by
  rcases Proofs.Engine.height_pair_cases (Λ := record) fields fp with he | ⟨h, entry, nu, hf, hp⟩
  · simp [Protocol.NamedRecord.encodeHeight, he, NamedHeightPair.erase]
  · rcases hp with ht | ht <;> rw [ht, hf] <;> rfl

private theorem round_action_shape (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.HealingStore V)
    (record : Protocol.NamedRecord) :
    ∃ (r : Round) (c : Option BlockId) (f : Option (Height × BlockId × Bool))
      (h_j : Height) (J : BlockId) (h_F : Height),
      (Protocol.NamedActions.round_action_with contract E hc nd st record).1.legacy =
        (create_attestation record.legacy nd.val_index r c f h_j J h_F).1 ∧
      (Protocol.NamedActions.round_action_with contract E hc nd st record).2.erase =
        (create_attestation record.legacy nd.val_index r c f h_j J h_F).2 := by
  refine ⟨_, _, _, _, _, _, rfl, ?_⟩
  simp only [Protocol.NamedActions.round_action_with, Protocol.with_attestation_input,
    Protocol.NamedRecord.create, Protocol.NamedRecord.legacyCreate,
    Protocol.NamedActions.creatorInput, Protocol.NamedRecord.encodeRow,
    NamedAttestation.erase, create_attestation, encodeHeight_erase_of]

private theorem on_tick_emit_record_eq (S : Setup V) (v : V) (n : NodeState V) (t : Time) :
    (on_tick_emit S v n t).1.record =
      (Protocol.NamedTick.tick
        (NamedProfile.gradeContract
          (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
        S.E S.hc S.cfg (S.node v) n.st n.record t).2.1 := rfl

private theorem on_tick_emit_snd_eq (S : Setup V) (v : V) (n : NodeState V) (t : Time) :
    (on_tick_emit S v n t).2 =
      (Protocol.NamedTick.tick
        (NamedProfile.gradeContract
          (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
        S.E S.hc S.cfg (S.node v) n.st n.record t).2.2 := rfl

private theorem named_tick_computed_duties (gc : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time) :
    Protocol.NamedTick.tick gc E hc cfg nd st record t =
      let s := E.slotOf t
      let st0 := Protocol.NamedStore.setClock E st t
      let proposed := Protocol.NamedDuties.propose_block_with gc E hc cfg nd st0
      let proposalDue := 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index
      let st1 := if proposalDue then proposed.1 else st0
      let emitted1 := if proposalDue then
        match proposed.2 with
        | none => []
        | some B => [Object.block B]
      else []
      let voted := Protocol.NamedDuties.goldfish_vote_with gc E hc nd st1
      let voteDue := 0 < s ∧ t = Protocol.vote_time E s
      let st2 := if voteDue then voted.1 else st1
      let emitted2 := if voteDue then voted.2.toList.map Object.gfVote else []
      let st3 := if 0 < s ∧ t = Protocol.support_cutoff E s then
        Protocol.NamedDuties.update_confirmation_with gc E hc st2 (s - 1) else st2
      if t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true then
        let attested := Protocol.NamedDuties.attest_with gc E hc nd st3 record
        (attested.1, attested.2.1, emitted1 ++ emitted2 ++ [Object.attest attested.2.2])
      else (st3, record, emitted1 ++ emitted2) := by
  simp only [Protocol.NamedTick.tick, Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps,
    Protocol.NamedStore.setClock]
  unfold Protocol.TickScheduler.runWith.match_1 named_tick_computed_duties.match_1
  rfl

/-- A tick's emissions are a list `pre` with no attestation, followed either by nothing, with the
    record unchanged, or by the row of one named round action, with the record that action returns. -/
private theorem on_tick_emit_attest_shape (S : Setup V) (v : V) (n : NodeState V) (t : Time) :
    ∃ (st3 : Protocol.NamedStore V) (gc : Protocol.GradeContract V) (pre : List (Object V)),
      (∀ o ∈ pre, ∀ a : NamedAttestation V, o ≠ Object.attest a) ∧
      (((on_tick_emit S v n t).1.record = n.Λ ∧ (on_tick_emit S v n t).2 = pre) ∨
       ((on_tick_emit S v n t).1.record =
          (Protocol.NamedActions.round_action_with gc S.E S.hc (S.node v)
            st3.core.toHealing n.Λ).1 ∧
        (on_tick_emit S v n t).2 = pre ++
          [Object.attest (Protocol.NamedActions.round_action_with gc S.E S.hc (S.node v)
            st3.core.toHealing n.Λ).2])) := by
  have hrec := on_tick_emit_record_eq S v n t
  have hsnd := on_tick_emit_snd_eq S v n t
  rw [named_tick_computed_duties] at hrec hsnd
  set gc := NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache) with hgcdef
  set s := S.E.slotOf t with hsdef
  set st0 := Protocol.NamedStore.setClock S.E n.st t with hst0def
  set proposed := Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node v) st0
    with hproposeddef
  set proposalDue := 0 < s ∧ t = Protocol.proposal_time S.E s ∧
    S.E.proposer s = (S.node v).val_index with hproposalDuedef
  set st1 := if proposalDue then proposed.1 else st0 with hst1def
  set emitted1 : List (Object V) := if proposalDue then
    (match proposed.2 with | none => [] | some B => [Object.block B]) else [] with hemitted1def
  set voted := Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc (S.node v) st1 with hvoteddef
  set voteDue := 0 < s ∧ t = Protocol.vote_time S.E s with hvoteDuedef
  set st2 := if voteDue then voted.1 else st1 with hst2def
  set emitted2 : List (Object V) := if voteDue then voted.2.toList.map Object.gfVote else []
    with hemitted2def
  set st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
    with hst3def
  have hpre : ∀ o ∈ emitted1 ++ emitted2, ∀ a : NamedAttestation V,
      o ≠ Object.attest a := by
    intro o ho a
    rcases List.mem_append.mp ho with h1 | h1
    · rw [hemitted1def] at h1
      split_ifs at h1 with hpd
      · rcases hpm : proposed.2 with _ | B
        · simp [hpm] at h1
        · simp only [hpm, List.mem_singleton] at h1
          simp [h1]
      · simp at h1
    · rw [hemitted2def] at h1
      split_ifs at h1 with hvd
      · obtain ⟨w, -, hw⟩ := List.mem_map.mp h1
        simp [← hw]
      · simp at h1
  by_cases hcond : t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
      (S.node v).awake (S.hc.round_of st3.core.s) = true
  · rw [if_pos hcond] at hrec hsnd
    exact ⟨st3, gc, emitted1 ++ emitted2, hpre, Or.inr ⟨hrec, hsnd⟩⟩
  · rw [if_neg hcond] at hrec hsnd
    exact ⟨st3, gc, emitted1 ++ emitted2, hpre, Or.inl ⟨hrec, hsnd⟩⟩

/-- If a tick sets a target `T` at a height `h` that had none, the tick emits an attestation whose
    height pair is `target h T`. -/
theorem on_tick_emit_target_introduced (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {h : Height} {T : BlockId}
    (hpre : n.Λ.legacy.target h = none)
    (hpost : (on_tick_emit S v n t).1.record.legacy.target h = some T) :
    ∃ a : NamedAttestation V,
      Object.attest a ∈ (on_tick_emit S v n t).2 ∧
        a.erase.height_pair = HeightPair.target h T := by
  obtain ⟨st3, gc, pre, -, hcase⟩ := on_tick_emit_attest_shape S v n t
  rcases hcase with ⟨hrec, -⟩ | ⟨hrec, hsnd⟩
  · rw [hrec] at hpost
    exact absurd hpost (by rw [hpre]; simp)
  · obtain ⟨r, c, f, h_j, J, h_F, hleg, herase⟩ :=
      round_action_shape gc S.E S.hc (S.node v) st3.core.toHealing n.Λ
    refine ⟨(Protocol.NamedActions.round_action_with gc S.E S.hc (S.node v)
        st3.core.toHealing n.Λ).2, ?_, ?_⟩
    · rw [hsnd]
      exact List.mem_append_right pre (List.mem_singleton_self _)
    · rw [herase]
      have hcreated :
          (create_attestation n.Λ.legacy (S.node v).val_index r c f h_j J h_F).1.target h =
            some T := by
        rw [← hleg, ← hrec]
        exact hpost
      have hfold :
          (record_attestation n.Λ.legacy
              (create_attestation n.Λ.legacy (S.node v).val_index r c f h_j J h_F).2).target h =
            some T := by
        simpa only [create_attestation] using hcreated
      exact record_attestation_target_introduced hpre hfold

/-- If a tick sets a lock `T` at a height `h` that had none, the tick emits an attestation whose
    finality pair is `⟨h, T⟩`. -/
theorem on_tick_emit_lock_introduced (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {h : Height} {T : BlockId}
    (hpre : n.Λ.legacy.lock h = none)
    (hpost : (on_tick_emit S v n t).1.record.legacy.lock h = some T) :
    ∃ a : NamedAttestation V,
      Object.attest a ∈ (on_tick_emit S v n t).2 ∧
        a.finality_pair = some ⟨h, T⟩ := by
  obtain ⟨st3, gc, pre, -, hcase⟩ := on_tick_emit_attest_shape S v n t
  rcases hcase with ⟨hrec, -⟩ | ⟨hrec, hsnd⟩
  · rw [hrec] at hpost
    exact absurd hpost (by rw [hpre]; simp)
  · obtain ⟨r, c, f, h_j, J, h_F, hleg, herase⟩ :=
      round_action_shape gc S.E S.hc (S.node v) st3.core.toHealing n.Λ
    refine ⟨(Protocol.NamedActions.round_action_with gc S.E S.hc (S.node v)
        st3.core.toHealing n.Λ).2, ?_, ?_⟩
    · rw [hsnd]
      exact List.mem_append_right pre (List.mem_singleton_self _)
    · rw [← erase_finality_pair, herase]
      have hcreated :
          (create_attestation n.Λ.legacy (S.node v).val_index r c f h_j J h_F).1.lock h =
            some T := by
        rw [← hleg, ← hrec]
        exact hpost
      have hfold :
          (record_attestation n.Λ.legacy
              (create_attestation n.Λ.legacy (S.node v).val_index r c f h_j J h_F).2).lock h =
            some T := by
        simpa only [create_attestation] using hcreated
      exact record_attestation_lock_introduced hpre hfold

end Protocol
end DecoupledConsensusModel

end
