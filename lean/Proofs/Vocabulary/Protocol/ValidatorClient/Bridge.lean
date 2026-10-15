module
public import Proofs.Vocabulary.Objects.PerHeight
public import Proofs.Vocabulary.Protocol.ValidatorClient.RecordCore
public import Proofs.Vocabulary.Internal.Legacy.Definitions.Confirmation
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Admissible
import Proofs.Vocabulary.Protocol.ValidatorClient.Divergence
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Proofs.Vocabulary.ModelProperties.create_attestation
import Proofs.Vocabulary.ModelProperties.own_lock
public import Proofs.Vocabulary.ModelProperties.NamedNode_initial

@[expose] public section

/-!
# Records evolve only by their own round actions

A validator's record changes only at its own ticks, by one named round action. So `LockCompatible`
holds along every run, recorded targets and locks keep their values, and `honestNoDoubleTarget`
proves that no honest validator emits two different nonempty targets at one height.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (Record create_attestation finality_pair record_attestation)
open Protocol (HealConfig)
open Internal
open Execution
open Proofs.Records (LockCompatible)

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
private theorem erase_finality_pair (a : NamedAttestation V) :
    a.erase.finality_pair = a.finality_pair := rfl

private theorem encodeHeight_erase_of (record : Record)
    (fields : Option (Height × BlockId × Bool)) (fp : Option FinalityPair) :
    (Protocol.NamedRecord.encodeHeight fields
      (Protocol.height_pair record fields fp)).erase =
      Protocol.height_pair record fields fp := by
  rcases Proofs.Engine.height_pair_cases (Λ := record) fields fp with he | ⟨h, entry, nu, hf, hp⟩
  · simp [Protocol.NamedRecord.encodeHeight, he, NamedHeightPair.erase]
  · rcases hp with ht | ht <;> rw [ht, hf] <;> rfl

/-- The named round action's record and attestation are those of `create_attestation` at the
    emitter's own record. -/
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

/-! ## One tick -/

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

/-- A tick preserves `LockCompatible`. -/
theorem lockCompatible_on_tick_emit (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    (hla : LockCompatible n.Λ.legacy) :
    LockCompatible (on_tick_emit S v n t).1.record.legacy := by
  obtain ⟨st3, gc, pre, -, hcase⟩ := on_tick_emit_attest_shape S v n t
  rcases hcase with ⟨hrec, -⟩ | ⟨hrec, -⟩
  · rw [hrec]; exact hla
  · rw [hrec]
    obtain ⟨r, c, f, h_j, J, h_F, hleg, -⟩ :=
      round_action_shape gc S.E S.hc (S.node v) st3.core.toHealing n.Λ
    rw [hleg]
    exact lockCompatible_create_attestation hla _ r c f h_j J h_F

/-- A tick keeps every recorded target. -/
theorem target_mono_on_tick_emit (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {h : Height} {T : BlockId} (hs : n.Λ.legacy.target h = some T) :
    (on_tick_emit S v n t).1.record.legacy.target h = some T := by
  obtain ⟨st3, gc, pre, -, hcase⟩ := on_tick_emit_attest_shape S v n t
  rcases hcase with ⟨hrec, -⟩ | ⟨hrec, -⟩
  · rw [hrec]; exact hs
  · rw [hrec]
    obtain ⟨r, c, f, h_j, J, h_F, hleg, -⟩ :=
      round_action_shape gc S.E S.hc (S.node v) st3.core.toHealing n.Λ
    rw [hleg]
    simp only [create_attestation]
    exact record_attestation_target_mono _ _ hs

/-- A tick keeps every recorded lock. -/
theorem lock_mono_on_tick_emit (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {h : Height} {T : BlockId} (hs : n.Λ.legacy.lock h = some T) :
    (on_tick_emit S v n t).1.record.legacy.lock h = some T := by
  obtain ⟨st3, gc, pre, -, hcase⟩ := on_tick_emit_attest_shape S v n t
  rcases hcase with ⟨hrec, -⟩ | ⟨hrec, -⟩
  · rw [hrec]; exact hs
  · rw [hrec]
    obtain ⟨r, c, f, h_j, J, h_F, hleg, -⟩ :=
      round_action_shape gc S.E S.hc (S.node v) st3.core.toHealing n.Λ
    rw [hleg]
    exact create_attestation_lock_mono hs _ r c f h_j J h_F

/-- Processing an object leaves the record unchanged. -/
theorem process_record (S : Setup V) (n : NodeState V) (o : Object V) :
    (NamedNode.process S n o).Λ = n.Λ := by
  cases o <;> rfl

/-! ## Along the run -/

/-- `LockCompatible` holds for every validator's record in every prefix state. -/
theorem stateBefore_lockCompatible (S : Setup V) (ρ : Run V) (v : V) :
    ∀ i : Nat, LockCompatible (ρ.stateBefore S i v).Λ.legacy := by
  intro i
  induction i with
  | zero =>
    intro h T hl
    have h0 : (ρ.stateBefore S 0 v).Λ.legacy.lock h = none := by
      show (NamedNode.initial : NamedNodeState V).record.legacy.lock h = none
      exact ModelProperties.initial_record_legacy_lock h
    rw [h0] at hl
    exact absurd hl (Option.some_ne_none T).symm
  | succ i ih =>
    have hstep : ρ.stateBefore S (i + 1) =
        (ρ.events[i]?.toList).foldl (World.step S) (ρ.stateBefore S i) := by
      unfold Run.stateBefore NamedRun.stateBefore
      rw [List.take_add_one, List.foldl_append]
    rw [hstep]
    rcases hev : ρ.events[i]? with _ | e
    · exact ih
    · cases e with
      | tick u t =>
        by_cases hu : u = v
        · subst hu
          simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
            Function.update_self]
          exact lockCompatible_on_tick_emit S u _ t ih
        · simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
            Function.update_of_ne (Ne.symm hu)]
          exact ih
      | deliver u o t =>
        by_cases hu : u = v
        · subst hu
          simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
            Function.update_self]
          rw [process_record]
          exact ih
        · simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
            Function.update_of_ne (Ne.symm hu)]
          exact ih

/-- A recorded target is kept in every later prefix state. -/
theorem stateBefore_target_mono (S : Setup V) (ρ : Run V) (v : V) {h : Height}
    {T : BlockId} {i : Nat} :
    ∀ j : Nat, i ≤ j → (ρ.stateBefore S i v).Λ.legacy.target h = some T →
      (ρ.stateBefore S j v).Λ.legacy.target h = some T := by
  intro j
  induction j with
  | zero => intro hj; rw [Nat.le_zero.mp hj]; exact id
  | succ j ih =>
    intro hj hs
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · have hprev := ih (Nat.lt_succ_iff.mp hlt) hs
      have hstep : ρ.stateBefore S (j + 1) =
          (ρ.events[j]?.toList).foldl (World.step S) (ρ.stateBefore S j) := by
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
      rw [hstep]
      rcases hev : ρ.events[j]? with _ | e
      · exact hprev
      · cases e with
        | tick u t =>
          by_cases hu : u = v
          · subst hu
            simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
              Function.update_self]
            exact target_mono_on_tick_emit S u _ t hprev
          · simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
              Function.update_of_ne (Ne.symm hu)]
            exact hprev
        | deliver u o t =>
          by_cases hu : u = v
          · subst hu
            simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
              Function.update_self]
            rw [process_record]
            exact hprev
          · simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
              Function.update_of_ne (Ne.symm hu)]
            exact hprev
    · exact (Nat.le_antisymm hj hge) ▸ hs

/-- A recorded lock is kept in every later prefix state. -/
theorem stateBefore_lock_mono (S : Setup V) (ρ : Run V) (v : V) {h : Height}
    {T : BlockId} {i : Nat} :
    ∀ j : Nat, i ≤ j → (ρ.stateBefore S i v).Λ.legacy.lock h = some T →
      (ρ.stateBefore S j v).Λ.legacy.lock h = some T := by
  intro j
  induction j with
  | zero => intro hj; rw [Nat.le_zero.mp hj]; exact id
  | succ j ih =>
    intro hj hs
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · have hprev := ih (Nat.lt_succ_iff.mp hlt) hs
      have hstep : ρ.stateBefore S (j + 1) =
          (ρ.events[j]?.toList).foldl (World.step S) (ρ.stateBefore S j) := by
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
      rw [hstep]
      rcases hev : ρ.events[j]? with _ | e
      · exact hprev
      · cases e with
        | tick u t =>
          by_cases hu : u = v
          · subst hu
            simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
              Function.update_self]
            exact lock_mono_on_tick_emit S u _ t hprev
          · simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
              Function.update_of_ne (Ne.symm hu)]
            exact hprev
        | deliver u o t =>
          by_cases hu : u = v
          · subst hu
            simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
              Function.update_self]
            rw [process_record]
            exact hprev
          · simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
              Function.update_of_ne (Ne.symm hu)]
            exact hprev
    · exact (Nat.le_antisymm hj hge) ▸ hs

/-! ## What an emission leaves behind -/

/-- The record after the tick at index `i` is the tick's own output. -/
theorem stateBefore_succ_record (S : Setup V) (ρ : Run V) {v : V} {t : Time}
    {i : Nat} (hi : ρ.events[i]? = some (Event.tick v t)) :
    (ρ.stateBefore S (i + 1) v).Λ =
      (on_tick_emit S v (ρ.stateBefore S i v) t).1.record := by
  have hval : ρ.stateBefore S (i + 1) v =
      (on_tick_emit S v (ρ.stateBefore S i v) t).1 := by
    have hfold : ρ.stateBefore S (i + 1) =
        (ρ.events[i]?.toList).foldl (World.step S) (ρ.stateBefore S i) := by
      unfold Run.stateBefore NamedRun.stateBefore
      rw [List.take_add_one, List.foldl_append]
    rw [hfold, hi]
    simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
      Function.update_self]
  rw [hval]

/-- The target of an emitted height pair is recorded as the target at its height in the record the
    tick leaves. -/
theorem emits_height_target_recorded (S : Setup V) (ρ : Run V)
    {v : V} {t : Time} {i : Nat}
    {a : NamedAttestation V} (hi : ρ.events[i]? = some (Event.tick v t))
    (ha : Object.attest a ∈ (on_tick_emit S v (ρ.stateBefore S i v) t).2)
    {h : Height} {T : BlockId} (hT : a.erase.height_pair = HeightPair.target h T) :
    (ρ.stateBefore S (i + 1) v).Λ.legacy.target h = some T := by
  obtain ⟨st3, gc, pre, hpre, hcase⟩ := on_tick_emit_attest_shape S v (ρ.stateBefore S i v) t
  rw [stateBefore_succ_record S ρ hi]
  rcases hcase with ⟨-, hsnd⟩ | ⟨hrec, hsnd⟩
  · rw [hsnd] at ha
    exact absurd rfl (hpre (Object.attest a) ha a)
  · rw [hrec]
    rw [hsnd] at ha
    obtain ⟨r, c, f, h_j, J, h_F, hleg, herase⟩ :=
      round_action_shape gc S.E S.hc (S.node v) st3.core.toHealing (ρ.stateBefore S i v).Λ
    have h'' : a = (Protocol.NamedActions.round_action_with gc S.E S.hc (S.node v)
        st3.core.toHealing (ρ.stateBefore S i v).Λ).2 := by
      rcases List.mem_append.mp ha with h' | h'
      · exact absurd rfl (hpre (Object.attest a) h' a)
      · rw [List.mem_singleton] at h'
        injection h'
    rw [hleg]
    exact create_attestation_saves (ρ.stateBefore S i v).Λ.legacy
      (stateBefore_lockCompatible S ρ v i) (S.node v).val_index r c f h_j J h_F
      (by rw [← herase, ← h'']; exact hT)

/-- The target of an emitted nonempty finality pair is recorded as the lock at its height in the
    record the tick leaves. -/
theorem emits_finality_locked (S : Setup V) (ρ : Run V)
    {v : V} {t : Time} {i : Nat}
    {a : NamedAttestation V} (hi : ρ.events[i]? = some (Event.tick v t))
    (ha : Object.attest a ∈ (on_tick_emit S v (ρ.stateBefore S i v) t).2)
    {h : Height} {J : BlockId} (hfp : a.finality_pair = some ⟨h, J⟩) :
    (ρ.stateBefore S (i + 1) v).Λ.legacy.lock h = some J := by
  obtain ⟨st3, gc, pre, hpre, hcase⟩ := on_tick_emit_attest_shape S v (ρ.stateBefore S i v) t
  rw [stateBefore_succ_record S ρ hi]
  rcases hcase with ⟨-, hsnd⟩ | ⟨hrec, hsnd⟩
  · rw [hsnd] at ha
    exact absurd rfl (hpre (Object.attest a) ha a)
  · rw [hrec]
    rw [hsnd] at ha
    obtain ⟨r, c, f, h_j, T, h_F, hleg, herase⟩ :=
      round_action_shape gc S.E S.hc (S.node v) st3.core.toHealing (ρ.stateBefore S i v).Λ
    have h'' : a = (Protocol.NamedActions.round_action_with gc S.E S.hc (S.node v)
        st3.core.toHealing (ρ.stateBefore S i v).Λ).2 := by
      rcases List.mem_append.mp ha with h' | h'
      · exact absurd rfl (hpre (Object.attest a) h' a)
      · rw [List.mem_singleton] at h'
        injection h'
    rw [hleg, Proofs.ModelProperties.create_attestation_fst, record_attestation_lock_eq_own_lock,
      Proofs.ModelProperties.create_attestation_snd_finality_pair]
    have hfp' : Protocol.finality_pair (ρ.stateBefore S i v).Λ.legacy h_j T h_F =
        some ⟨h, J⟩ := by
      have hstep1 : a.erase = (create_attestation (ρ.stateBefore S i v).Λ.legacy
          (S.node v).val_index r c f h_j T h_F).2 := by rw [h'']; exact herase
      have hstep2 : a.finality_pair =
          Protocol.finality_pair (ρ.stateBefore S i v).Λ.legacy h_j T h_F := by
        rw [← erase_finality_pair a, hstep1,
          Proofs.ModelProperties.create_attestation_snd_finality_pair]
      rw [← hstep2]
      exact hfp
    rw [hfp', Proofs.ModelProperties.own_lock_some_self]

/-- For every target an emitted attestation names at height `h`, the record the tick leaves has no
    target at `h` or has that target. -/
theorem emits_target_compatible (S : Setup V) (ρ : Run V)
    {v : V} {t : Time} {i : Nat}
    {a : NamedAttestation V} (hi : ρ.events[i]? = some (Event.tick v t))
    (ha : Object.attest a ∈ (on_tick_emit S v (ρ.stateBefore S i v) t).2)
    {h : Height} {T : BlockId} (hT : T ∈ targetsAt a.erase h) :
    (ρ.stateBefore S (i + 1) v).Λ.legacy.target h = none ∨
      (ρ.stateBefore S (i + 1) v).Λ.legacy.target h = some T := by
  rcases hT with hheight | hfinality
  · exact Or.inr (emits_height_target_recorded S ρ hi ha hheight)
  · have hlock := emits_finality_locked S ρ hi ha
      ((erase_finality_pair a).symm.trans hfinality)
    exact (stateBefore_lockCompatible S ρ v (i + 1) h T hlock).2

/-! ## No honest double target -/

/-- A target an emitted attestation names at height `h` equals the target the record already holds
    at `h`. -/
theorem emits_target_eq_of_record (S : Setup V) (ρ : Run V) {v : V} {t : Time}
    {i : Nat} {a : NamedAttestation V} (hi : ρ.events[i]? = some (Event.tick v t))
    (ha : Object.attest a ∈ (on_tick_emit S v (ρ.stateBefore S i v) t).2)
    {h : Height} {T X : BlockId} (hs : (ρ.stateBefore S i v).Λ.legacy.target h = some X)
    (hT : T ∈ targetsAt a.erase h) : T = X := by
  have hsucc := emits_target_compatible S ρ hi ha hT
  have hmono : (ρ.stateBefore S (i + 1) v).Λ.legacy.target h = some X :=
    stateBefore_target_mono S ρ v (i + 1) (Nat.le_succ i) hs
  rcases hsucc with hnone | hsame
  · rw [hmono] at hnone
    contradiction
  · rw [hsame] at hmono
    exact Option.some_inj.mp hmono

/-- A target an emitted attestation names at height `h` equals the lock the record already holds at
    `h`. -/
theorem emits_target_eq_of_lock (S : Setup V) (ρ : Run V) {v : V} {t : Time}
    {i : Nat} {a : NamedAttestation V} (hi : ρ.events[i]? = some (Event.tick v t))
    (ha : Object.attest a ∈ (on_tick_emit S v (ρ.stateBefore S i v) t).2)
    {h : Height} {T X : BlockId} (hs : (ρ.stateBefore S i v).Λ.legacy.lock h = some X)
    (hT : T ∈ targetsAt a.erase h) : T = X := by
  have hlock : (ρ.stateBefore S (i + 1) v).Λ.legacy.lock h = some X := by
    rw [stateBefore_succ_record S ρ hi]
    exact lock_mono_on_tick_emit S v _ t hs
  rcases hT with hheight | hfinality
  · have htarget := emits_height_target_recorded S ρ hi ha hheight
    have hcompat := (stateBefore_lockCompatible S ρ v (i + 1) h X hlock).2
    rcases hcompat with hnone | hsame
    · rw [htarget] at hnone
      contradiction
    · rw [htarget] at hsame
      exact Option.some_inj.mp hsame
  · have hnewLock := emits_finality_locked S ρ hi ha
      ((erase_finality_pair a).symm.trans hfinality)
    rw [hlock] at hnewLock
    exact (Option.some_inj.mp hnewLock).symm

/-- No honest validator emits two different nonempty targets at one height. -/
theorem honestNoDoubleTarget (S : Setup V) (ρ : Run V) :
    Internal.HealingSurface.HonestNoDoubleTarget S ρ := by
  rintro v - a a' t t' ⟨i, hi, ha⟩ ⟨j, hj, ha'⟩ h T T' hT hT'
  rcases Nat.lt_trichotomy i j with hlt | rfl | hgt
  · rcases hT with hheight | hfinality
    · exact (emits_target_eq_of_record S ρ hj ha'
        (stateBefore_target_mono S ρ v j hlt
          (emits_height_target_recorded S ρ hi ha hheight)) hT').symm
    · exact (emits_target_eq_of_lock S ρ hj ha'
        (stateBefore_lock_mono S ρ v j hlt
          (emits_finality_locked S ρ hi ha
            ((erase_finality_pair a).symm.trans hfinality))) hT').symm
  · rw [hj, Option.some_inj, NamedEvent.tick.injEq] at hi
    obtain ⟨-, ht⟩ := hi
    subst ht
    have ha : Object.attest a ∈ (on_tick_emit S v (ρ.stateBefore S i v) t').2 := ha
    have ha' : Object.attest a' ∈ (on_tick_emit S v (ρ.stateBefore S i v) t').2 := ha'
    obtain ⟨st3, gc, pre, hpre, hcase⟩ :=
      on_tick_emit_attest_shape S v (ρ.stateBefore S i v) t'
    rcases hcase with ⟨-, hsnd⟩ | ⟨-, hsnd⟩
    · rw [hsnd] at ha
      exact absurd rfl (hpre (Object.attest a) ha a)
    · rw [hsnd] at ha ha'
      have hmem : ∀ b : NamedAttestation V, Object.attest b ∈ pre ++
          [Object.attest (Protocol.NamedActions.round_action_with gc S.E S.hc (S.node v)
            st3.core.toHealing (ρ.stateBefore S i v).Λ).2] →
          b = (Protocol.NamedActions.round_action_with gc S.E S.hc (S.node v)
            st3.core.toHealing (ρ.stateBefore S i v).Λ).2 := by
        intro b hb
        rcases List.mem_append.mp hb with h' | h'
        · exact absurd rfl (hpre (Object.attest b) h' b)
        · rw [List.mem_singleton] at h'
          injection h'
      have hA := hmem a ha
      have hA' := hmem a' ha'
      subst hA
      subst hA'
      obtain ⟨r, c, f, h_j, J, h_F, -, herase⟩ :=
        round_action_shape gc S.E S.hc (S.node v) st3.core.toHealing (ρ.stateBefore S i v).Λ
      rw [herase] at hT hT'
      rcases hT with hT | hT <;> rcases hT' with hT' | hT'
      · rw [hT] at hT'
        simp only [HeightPair.target.injEq, true_and] at hT'
        exact hT'
      · exact create_attestation_no_self_E1 _ _ _ _ _ _ _ _ hT hT'
      · exact (create_attestation_no_self_E1 _ _ _ _ _ _ _ _ hT' hT).symm
      · rw [hT] at hT'
        exact congrArg FinalityPair.target (Option.some_inj.mp hT')
  · rcases hT' with hheight | hfinality
    · exact emits_target_eq_of_record S ρ hi ha
        (stateBefore_target_mono S ρ v i hgt
          (emits_height_target_recorded S ρ hj ha' hheight)) hT
    · exact emits_target_eq_of_lock S ρ hi ha
        (stateBefore_lock_mono S ρ v i hgt
          (emits_finality_locked S ρ hj ha'
            ((erase_finality_pair a').symm.trans hfinality))) hT

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
