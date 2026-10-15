import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRecord
import Proofs.Claims.Restated.Claim13bSyncView
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Redelivery
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Proposals_Actions
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_BlockEmission
import Model.Conditions.Claim13beRoute3_23
import Model.Conditions.ProcessedFlip
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Healing_Action
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_23

/-!
# Recorded attestations are delivered

Every step keeps the four clauses of `SgMono`, every attestation a held body includes is recorded or
refused for good, a validator's own proposal records none of its attestations anew, and an
attestation an honest store records inside the phase is delivered to every validator not held at the
deadline. Stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- The slot of the time a tick step names is at or after the slot of every validator's store when
    the step starts. -/
theorem slot_le_slotOf_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {i τ : Nat} (v : V)
    (hl : x.lbl i = AtomicAction.tickAllAwake τ) :
    (x[i][v].st).st.core.s ≤ S.E.slotOf (τ : Int) := by
  rw [Restated.slotOfClock_sts facts S Sched x i v]
  apply slotOf_mono_sts S
  have h1 := Restated.clock_le_time_sts facts S Sched x i v
  have h2 := (Restated.tickAllAwake_time facts S Sched x hl).1
  refine le_trans h1 ?_
  rw [← h2]; push_cast; omega

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- Going from a store to itself, the four clauses of `SgMono` hold. -/
theorem SgMono.refl (hc : HealConfig) (st : M.NS) : Restated.SgMono M hc st st :=
  ⟨fun _ h => h, fun _ h => h, fun _ h _ => h, id⟩

/-- If the four clauses of `SgMono` hold going from `st` to `st'`, they hold going from `st` to
    `st'` with its saved grades made compatible with its finalized block. -/
private theorem sgMono_make_grades_compatible (facts : Record.Facts M) (hc : HealConfig)
    {st st' : M.NS} (h : Restated.SgMono M hc st st') :
    Restated.SgMono M hc st (M.make_grades_compatible_with_finalized st') := by
  have hR : ∀ b : CombinedAttestation V,
      Restated.SgRefused M hc (M.make_grades_compatible_with_finalized st').core b ↔
        Restated.SgRefused M hc st'.core b := by
    intro b
    simp only [Restated.SgRefused, facts.nd.make_grades_compatible_with_finalized_core_s,
      facts.nd.make_grades_compatible_with_finalized_core_round_votes]
  have hS : Restated.IncludedAttestationsSettled M hc (M.make_grades_compatible_with_finalized st') ↔
      Restated.IncludedAttestationsSettled M hc st' := by
    simp only [Restated.IncludedAttestationsSettled,
      facts.nd.make_grades_compatible_with_finalized_bodies,
      facts.nd.make_grades_compatible_with_finalized_sg_rows, hR]
  refine ⟨fun b hb => (hR b).2 (h.refused b hb), fun a ha => ?_, fun a h0 hr => ?_,
    fun hs => hS.2 (h.settled hs)⟩
  · rw [facts.nd.make_grades_compatible_with_finalized_sg_rows]; exact h.rows a ha
  · rw [facts.nd.make_grades_compatible_with_finalized_sg_rows]; exact h.excluded a h0 hr

/-- If step `k` is the tick at `t`, then either the step took an outcome `out` of `v`'s tick from a
    node state whose store is `v`'s store after `k` steps, and `v`'s node state after `k + 1` steps
    is `out`'s, or `v`'s store after `k + 1` steps is its store after `k` steps. -/
private theorem tick_step_st_cases (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k t : Nat} (v : V)
    (hl : x.lbl k = AtomicAction.tickAllAwake t) :
    (∃ (n₀ : M.N) (out : M.N × List (NamedObject V)), n₀.st = (x[k][v].st).st ∧
        (M.reachedNode n₀ ∧ M.runs_as n₀ v) ∧
        M.tick (Setup.alwaysAwake S) v n₀ (t : Int) ⇢ out ∧ x[k + 1][v].st = out.1) ∨
      (x[k + 1][v].st).st = (x[k][v].st).st := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, w, tk, hwake, htick, hc⟩ := hs
  have hwst : ((w v).state).st = (x[k][v].st).st := by
    have hww := hwake v
    unfold TickAllAwakeWake at hww
    by_cases he : v ∈ entrants Sched t
    · rw [if_pos he] at hww
      rw [Record.protocolOf_step_wake M S hww]
      exact (facts.nd.wake_st_record _).1
    · rw [if_neg he] at hww
      rw [hww]
  by_cases haw : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int)
  · have hx1 : x[k + 1][v].st = (tk v).state := by
      have h2 : x[k + 1][v] = (tickAllAwakeUpdate Sched t x[k] w tk)[v] := by rw [hc]
      rw [h2, tickAllAwakeUpdate_getElem_react haw]
    rcases Record.protocolOf_step_tick M S (htick v haw) with ⟨out, hout, hres⟩ | ⟨-, hres⟩
    · have hwS : (w v).state = Record.wakeStage M Sched (t : Int) x[k] v :=
        Record.wakeStage_of_TickAllAwakeWake M S Sched (hwake v)
      exact Or.inl ⟨(w v).state, out, hwst,
        ⟨by rw [hwS]; exact Record.reachedNode_wakeStage facts S Sched x k v t,
          by rw [hwS]; exact Record.runs_as_wakeStage facts S Sched x k v t⟩, hout, by rw [hx1, hres]⟩
    · exact Or.inr (by rw [hx1, hres, hwst])
  · refine Or.inr ?_
    have h2 : x[k + 1][v] = (tickAllAwakeUpdate Sched t x[k] w tk)[v] := by rw [hc]
    rw [h2, tickAllAwakeUpdate_getElem_st_of_not_react haw]

/-- From the store a validator holds after `i` steps to the one it holds after `i + 1` steps, the
    four clauses of `SgMono` hold. -/
theorem sgMono_sts_step (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (i : Nat) (v : V) : Restated.SgMono M S.hc (x[i][v].st).st (x[i + 1][v].st).st := by
  cases hl : x.lbl i with
  | custom _ ev => exact ev.elim
  | adversarial p m =>
      rw [Restated.getElem_succ_of_adversarial facts S Sched x hl]; exact Restated.SgMono.refl _ _
  | forward p m =>
      rw [Restated.getElem_succ_of_forward facts S Sched x hl]; exact Restated.SgMono.refl _ _
  | tickAllAwake τ =>
      rcases tick_step_st_cases facts S Sched x v hl with ⟨n₀, out₁, hn₀, ⟨_hr₀, _hv₀⟩, hout, hst⟩ | hst
      · rw [hst, ← hn₀]
        refine facts.nd.sgMono_node_tick (Setup.alwaysAwake S) v n₀ (τ : Int) ?_ out₁ hout
        rw [hn₀]
        exact Restated.slot_le_slotOf_tick facts S Sched x v hl
      · rw [hst]; exact Restated.SgMono.refl _ _
  | deliver p m =>
      by_cases hp : p = v
      · subst hp
        rcases Restated.st_succ_of_deliver facts S Sched x hl with hpr | ⟨-, hst⟩
        · rw [facts.nd.process_st (Setup.alwaysAwake S) _ m.msg _ hpr]
          exact sgMono_make_grades_compatible facts _
            (facts.nd.sgMono_process (Setup.alwaysAwake S) _ m.msg)
        · rw [hst]; exact Restated.SgMono.refl _ _
      · rw [Restated.getElem_succ_of_deliver_ne facts S Sched x hl hp]; exact Restated.SgMono.refl _ _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- At every step, every attestation included in a block whose body a validator's store holds is
    among that store's rows of its round, or the admission test refuses it for good at that store. -/
theorem includedAttestationsSettled_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (v : V) :
    Restated.IncludedAttestationsSettled M S.hc (x[i][v].st).st := by
  induction i with
  | zero =>
      rw [Record.st_zero M S Sched x v]
      intro B hB a ha
      have hB' : B = NamedBlock.genesis := facts.nd.initial_body_eq_genesis _ _ hB
      subst hB'
      rw [named_genesis_attestations] at ha
      exact absurd ha List.not_mem_nil
  | succ i ih => exact (Restated.sgMono_sts_step facts S Sched x i v).settled ih

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- Every attestation in the rows of round `r` of `v`'s store after `i` steps is of round `r`. -/
theorem round_of_mem_sg_rows_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat)
    (v : V) {r : Round}
    {a : NamedAttestation V} (h : a ∈ (x[i][v].st).st.sg_rows r) : a.round = r := by
  obtain ⟨w₁, hw₁, heq⟩ := Record.stateBeforeOf_runOfM M S Sched x facts.nd.wake_events_or_id v i
  have hr := Restated.Vocabulary.Proofs.NamedStoreBridge.sgRowRounds_stateBefore facts (Setup.alwaysAwake S)
    (Record.runOfM M S Sched x v i) (Record.veventsOf M S Sched x v i).length v w₁ hw₁
  rw [heq] at hr
  exact hr r a h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- If the store's slot is at or before the slot of `τ`, and an attestation `a` that block `B`
    includes is not among `v`'s rows of `a`'s round after `i` steps, then for every outcome of `v`'s
    tick at `τ` from its node state after `i` steps that sends `B`, `a` is not among the rows of
    `a`'s round of that outcome's store. -/
theorem not_mem_rows_of_tick_block (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat)
    (v : V) (τ : Int) {B : NamedBlock V}
    {a : NamedAttestation V}
    (hs : (x[i][v].st).st.core.s ≤ S.E.slotOf τ)
    (ha : a ∈ B.attestations) (h0 : a ∉ (x[i][v].st).st.sg_rows a.round) :
    ∀ out₁, M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched τ x[i] v) τ ⇢ out₁ →
      NamedObject.block B ∈ out₁.2 → a ∉ out₁.1.st.sg_rows a.round := by
  have _hr_0 : M.reachedNode (x[i][v].st) := Record.reachedNode_sts facts S Sched x i v
  have _hv_0 : M.runs_as (x[i][v].st) v := Record.runs_as_sts facts S Sched x i v
  have _hr_1 : M.reachedNode (Record.wakeStage M Sched τ x[i] v) := Record.reachedNode_wakeStage facts S Sched x i v τ
  have _hv_1 : M.runs_as (Record.wakeStage M Sched τ x[i] v) v := Record.runs_as_wakeStage facts S Sched x i v τ
  intro out₁ hout hem
  have hnst : (Record.wakeStage M Sched τ x[i] v).st = (x[i][v].st).st :=
    Record.wakeStage_st facts Sched τ x[i] v
  have hnc : (Record.wakeStage M Sched τ x[i] v).cache = (x[i][v].st).cache :=
    Record.wakeStage_cache facts Sched τ x[i] v
  obtain ⟨-, hprop⟩ :=
    facts.nd.block_mem_on_tick_emit (Setup.alwaysAwake S) v _ τ out₁ hout hem
  rw [hnst, hnc] at hprop
  set st0 := M.ns_setClock (Setup.alwaysAwake S).E (x[i][v].st).st τ with hst0
  have _hrs0 : M.reachedStore st0 := by
    rw [hst0]; exact facts.sto.reachedStore_setClock _ _ _ (facts.nd.reachedStore_of_node _ _hr_0)
  have hrows0 : st0.sg_rows = (x[i][v].st).st.sg_rows := by
    rw [hst0, facts.hd.setClock_sg_rows]
  have hbod0 : st0.bodies = (x[i][v].st).st.bodies := by
    rw [hst0, facts.hd.Sts_setClock_bodies]
  obtain ⟨c, hcph⟩ := facts.gr.onPhaseTick_nonempty (Setup.alwaysAwake S).E
    (Setup.alwaysAwake S).hc (x[i][v].st).st.core.toHealing τ (x[i][v].st).cache
  obtain ⟨D, hD⟩ : ∃ D, M.duties_propose_block_with (M.frameContract c) (Setup.alwaysAwake S).E
      (Setup.alwaysAwake S).hc (Setup.alwaysAwake S).cfg ((Setup.alwaysAwake S).node v) st0 ⇢ D := by
    have hbm := facts.nd.block_mem_on_tick_emit (Setup.alwaysAwake S) v _ τ out₁ hout hem
    obtain ⟨D, hD⟩ := facts.dt.propose_block_with_nonempty (Setup.alwaysAwake S) v _ τ out₁ hout
      hbm.1.1 hbm.1.2.1 hbm.1.2.2
      (facts.nd.block_mem_on_tick_emit_awake (Setup.alwaysAwake S) v _ τ out₁ hout hem) c
      (by rw [hnst, hnc]; exact hcph)
    rw [hnst] at hD
    exact ⟨D, hD⟩
  have hDB := hprop c hcph D hD
  obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.frameContract c) .poolAndCarried
    (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node v) st0
  have hoB := facts.dt.proposal_with_eq_of_propose_block_with_snd _ _ _ _ _ _ D hD hDB o ho
  rw [hoB] at ho
  obtain ⟨P, hP⟩ := facts.dt.with_proposal_input_nonempty (M.frameContract c)
    (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node v)
    (M.toHealing st0.core)
  obtain ⟨L, hL⟩ := facts.dt.select_nonempty .poolAndCarried (Setup.alwaysAwake S).hc st0
  have hBatt : B.attestations = M.proposalRows B.parent L :=
    (Restated.Vocabulary.Proofs.NamedActions.proposal_payload facts _ _ _ _ _ _ B ho P hP L
      hL).2.2.2.2.2.2.1
  rw [hBatt] at ha
  have hsel := (facts.dt.mem_proposalRows _ _ _ ha).1
  have hsettled := Restated.includedAttestationsSettled_sts facts S Sched x i v
  obtain ⟨C, hC⟩ := facts.dt.carriedRows_nonempty (Setup.alwaysAwake S).hc st0
  have hrefused : Restated.SgRefused M S.hc (x[i][v].st).st.core a.erase := by
    rcases facts.dt.mem_select_poolAndCarried _ st0 L hL hsel C hC with hpool | hcarried
    · exfalso
      obtain ⟨r, hr⟩ := facts.dt.exists_sg_rows_of_mem_processedRows _ _
        (facts.dt.mem_processedRows_of_mem_poolRows _ _ hpool)
      rw [hrows0] at hr
      have hround := Restated.round_of_mem_sg_rows_sts facts S Sched x i v hr
      rw [← hround] at hr
      exact h0 hr
    · obtain ⟨O, hO⟩ := facts.dt.orderedBodies_nonempty st0
      obtain ⟨B', hB', -, ha', -⟩ :=
        (facts.dt.mem_carried_rows _ _ _ C hC O hO).1 hcarried
      have hB'mem : B' ∈ (x[i][v].st).st.bodies := by
        rw [← hbod0]; exact facts.dt.ordered_bodies_mem O hO hB'
      rcases hsettled B' hB'mem a ha' with h | h
      · exact absurd h h0
      · exact h
  have hmono := facts.nd.sgMono_node_tick (Setup.alwaysAwake S) v _ τ (by rw [hnst]; exact hs)
    out₁ hout
  rw [hnst] at hmono
  exact hmono.excluded a h0 hrefused

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- If `out` is an outcome of `v`'s tick at the tick step `k` whose node state is the one `v` holds
    after the step, outcomes of that tick with one node state send the same objects, and `o` is in
    `out`'s list, then `⟨v, o⟩` is in `x[k + 1].sent - x[k].sent`. -/
theorem mem_sent_diff_of_tick_of_state (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {k t : Nat} {v : V}
    {o : NamedObject V} (hl : x.lbl k = AtomicAction.tickAllAwake t)
    (haw : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int))
    (hsend : ∀ out out' : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) x[k] v) (t : Int) ⇢ out →
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) x[k] v) (t : Int) ⇢ out' →
      out.1 = out'.1 → out.2 = out'.2)
    {out : M.N × List (NamedObject V)}
    (hout : M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) x[k] v) (t : Int) ⇢ out)
    (hst : x[k + 1][v].st = out.1) (ho : o ∈ out.2) :
    (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent - x[k].sent := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, w, tk, hwake, htick, hc⟩ := hs
  have hwst : (w v).state = Record.wakeStage M Sched (t : Int) x[k] v :=
    Record.wakeStage_of_TickAllAwakeWake M S Sched (hwake v)
  have hmem : tk v ∈ Record.reactionsOf M S v ((w v).state) (t : Int) .tick := by
    rcases htick v haw with h | ⟨hempty, -⟩
    · exact h
    · exfalso
      have h' : ({ state := out.1, send := (out.2 : Multiset (NamedObject V)) } :
          NodeStepResult M.N (NamedObject V)) ∈
          Record.reactionsOf M S v ((w v).state) (t : Int) .tick := by
        simp only [Record.reactionsOf, Set.mem_setOf_eq]
        exact ⟨out, by rw [hwst]; exact hout, rfl⟩
      rw [hempty] at h'
      exact h'
  simp only [Record.reactionsOf, Set.mem_setOf_eq] at hmem
  obtain ⟨out', hout', htkv⟩ := hmem
  rw [hwst] at hout'
  have hx1 : x[k + 1][v].st = (tk v).state := by
    have h2 : x[k + 1][v] = (tickAllAwakeUpdate Sched t x[k] w tk)[v] := by rw [hc]
    rw [h2, tickAllAwakeUpdate_getElem_awake (Finset.mem_sdiff.1 haw).1 (Finset.mem_sdiff.1 haw).2]
  rw [htkv] at hx1
  have h2 : out'.2 = out.2 := hsend out' out hout' hout (hx1.symm.trans hst)
  have hsent : x[k + 1].sent = x[k].sent
      + (Sched.awake (t : Int) \ Sched.adv (t : Int)).sum
          (fun q => ((w q).send + (tk q).send).map (SignedMsg.mk q)) := by
    rw [hc]; rfl
  rw [hsent, add_tsub_cancel_left]
  refine Multiset.mem_sum.2 ⟨v, haw, ?_⟩
  refine Multiset.mem_map.2 ⟨o, Multiset.mem_add.2 (Or.inr ?_), rfl⟩
  rw [htkv]
  exact Multiset.mem_coe.2 (h2 ▸ ho)

/-- Under `SynchronyFromWake`: if `a` enters `v`'s rows of `a`'s round at step `i`, `v` is honest
    through that step, the step starts inside the phase, the deadline (one delay after the later of
    `x[i + 1].time` and `t_GST`) is inside the phase, and the adversary does not hold `w` at the
    deadline, then some step at or after `x[i + 1].time` and strictly before the deadline delivers
    to `w` the message `⟨v, a⟩`. -/
theorem attest_delivered_of_recorded_phase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hsync : Restated.SynchronyFromWake M S x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE : Int}
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    {i : Nat} {v w : V} {a : NamedAttestation V}
    (h0 : a ∉ (x[i][v].st).st.sg_rows a.round)
    (h1 : a ∈ (x[i + 1][v].st).st.sg_rows a.round)
    (hvh : Restated.HonestThrough M Sched x i v) (hi : tGAT ≤ (x[i].time : Int))
    (hdead : max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ ≤ tE)
    (hw : w ∉ Sched.adv (max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ)) :
    ∃ d : Nat, (x[i + 1].time : Int) ≤ (x[d].time : Int) ∧
      (x[d].time : Int) < max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ ∧
      x.lbl d = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ := by
  have hf0 : Restated.Vocabulary.Execution.Object.processed M (x[i][v].st).st
      (NamedObject.attest a) = false :=
    decide_eq_false h0
  have hf1 : Restated.Vocabulary.Execution.Object.processed M (x[i + 1][v].st).st
      (NamedObject.attest a) = true :=
    decide_eq_true h1
  have hti : (x[i].time : Int) ≤ (x[i + 1].time : Int) := by
    exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_succ i)
  have hmax : max (x[i].time : Int) S.E.t_GST ≤ max (x[i + 1].time : Int) S.E.t_GST :=
    max_le_max hti (le_refl _)
  have hwin : w ∈ Sched.awakeThroughout (x[i].time : Int)
      (max (x[i].time : Int) S.E.t_GST + S.E.Δ) :=
    awakeThroughout_shrink Sched (awakeThroughout_phase Sched hawake hmono hi hdead hw)
      (by linarith)
  have hsend : Restated.HonestSendAt M S x i
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) := by
    rcases Restated.flip_step_cases facts S Sched x hf0 hf1 with
      ⟨m, hl, hm0, hm1, hcase⟩ | ⟨τ, hl, haw, out₁, hout, hst, hcase⟩
    · have ho : NamedObject.attest a ∈ relayedObjects m.msg := by
        rw [mem_relayedObjects_iff]
        rcases hcase with heq | ⟨B, hB, hcc⟩
        · exact Or.inl heq.symm
        · rw [hB]; exact Or.inr (Restated.carries_of_carriedCall facts _ _ B hcc)
      have hne : ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[i][v].st) m.msg ⇢ n' := by
        rcases Restated.st_succ_of_deliver facts S Sched x hl with hpr | ⟨-, hst⟩
        · exact ⟨_, hpr⟩
        · rw [hst, hm0] at hm1
          exact absurd hm1 (by simp)
      exact Restated.honestSendAt_of_deliver_relay facts S Sched x hl ho hne
    · rcases hcase with hmem | ⟨B, hem, hcc⟩
      · exact ⟨Restated.mem_sent_diff_of_tick_of_state facts S Sched x hl haw
          (fun o₁ o₂ h₁ h₂ h12 =>
            facts.nd.tick_send_eq_of_state (Setup.alwaysAwake S) v _ _ o₁ o₂ h₁ h₂ h12)
          hout hst hmem,
          hvh (x[i].time : Int) (le_refl _)⟩
      · exfalso
        obtain ⟨⟨j, hj⟩, -, -⟩ := hcc
        rw [hst] at h1
        exact Restated.not_mem_rows_of_tick_block facts S Sched x i v (τ : Int)
          (Restated.slot_le_slotOf_tick facts S Sched x v hl) (List.mem_of_getElem? hj) h0
          out₁ hout hem h1
  obtain ⟨d, hid, hlbl, -, hlt⟩ := Restated.synchronyFromWake_from_step facts S hsync hsend hwin
  refine ⟨d, ?_, by linarith, hlbl⟩
  exact_mod_cast Restated.time_mono facts S Sched x (show i + 1 ≤ d by omega)

end

end DecoupledConsensusModel.Sts.Restated
