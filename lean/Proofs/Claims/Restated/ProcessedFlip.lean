import Proofs.Claims.ProcessedFlip
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Redelivery
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Alignment
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_BlockEmission
import Model.Conditions.ProcessedFlip
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Recorded objects and where they come from

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: an object a
validator's store has recorded stays recorded, and an object newly recorded at a step was delivered
at that step or emitted by the validator's tick there, itself or inside a block. Also what a tick
step does to one node state, and that an emitted object names its emitter as author.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-! ## Helpers on the test whether a store has recorded an object -/

section
open DecoupledConsensusModel.Execution

/-- Setting the clock of a store changes none of the objects it has recorded. -/
private theorem processed_setClock' (facts : Record.Facts M) (E : Env V) (st : M.NS) (t : Int)
    (o : NamedObject V) :
    Restated.Vocabulary.Execution.Object.processed M (M.ns_setClock E st t) o =
      Restated.Vocabulary.Execution.Object.processed M st o := by
  cases o with
  | block B =>
      simp only [Restated.Vocabulary.Execution.Object.processed, facts.hd.Sts_setClock_bodies]
  | gfVote u =>
      simp only [Restated.Vocabulary.Execution.Object.processed, facts.hd.setClock_core_gf_votes]
  | attest a =>
      simp only [Restated.Vocabulary.Execution.Object.processed, facts.hd.setClock_sg_rows]

/-- Making a store's saved grades compatible with its finalized block changes none of the objects it
    has recorded. -/
private theorem processed_mgcwf' (facts : Record.Facts M) (ns : M.NS) (o : NamedObject V) :
    Restated.Vocabulary.Execution.Object.processed M (M.make_grades_compatible_with_finalized ns) o =
      Restated.Vocabulary.Execution.Object.processed M ns o := by
  cases o with
  | block B =>
      simp only [Restated.Vocabulary.Execution.Object.processed,
        facts.nd.make_grades_compatible_with_finalized_bodies]
  | gfVote u =>
      simp only [Restated.Vocabulary.Execution.Object.processed,
        facts.nd.make_grades_compatible_with_finalized_core_gf_votes]
  | attest a =>
      simp only [Restated.Vocabulary.Execution.Object.processed,
        facts.nd.make_grades_compatible_with_finalized_sg_rows]

/-- Whatever a receipt delivers, an object the store had already recorded is still recorded
    afterwards. -/
private theorem processed_mono_receipt' (facts : Record.Facts M) (S : Setup V) (st : M.NS)
    (o o' : NamedObject V) (h : Restated.Vocabulary.Execution.Object.processed M st o = true) :
    Restated.Vocabulary.Execution.Object.processed M (M.receipt_process S st o') o = true := by
  have hm := facts.nd.processed_mono_receipt S st o'
  cases o with
  | block B => exact decide_eq_true (hm.1 B (of_decide_eq_true h))
  | gfVote u => exact decide_eq_true (hm.2.1 u (of_decide_eq_true h))
  | attest a => exact decide_eq_true (hm.2.2 a (of_decide_eq_true h))

/-- If a store records an object after a receipt that it did not record before, that object is the
    receipt's own payload, or the payload is a block that carries it and entered the store there
    (`Restated.CarriedCall`). -/
private theorem flip_of_process' (facts : Record.Facts M) (S : Setup V) (st : M.NS)
    (o' o : NamedObject V) (h0 : Restated.Vocabulary.Execution.Object.processed M st o = false)
    (h1 : Restated.Vocabulary.Execution.Object.processed M (M.receipt_process S st o') o = true) :
    o = o' ∨ ∃ B : NamedBlock V, o' = NamedObject.block B ∧ Restated.CarriedCall M S st B o := by
  have hf := facts.nd.flip_of_process S st o'
  cases o with
  | block B => exact Or.inl (hf.1 B (of_decide_eq_false h0) (of_decide_eq_true h1))
  | gfVote u => exact hf.2.1 u (of_decide_eq_false h0) (of_decide_eq_true h1)
  | attest a => exact hf.2.2 a (of_decide_eq_false h0) (of_decide_eq_true h1)

/-- A receipt either gives the store back unchanged, or the store records the receipt's own payload
    afterwards. -/
private theorem receipt_noop_or_processed' (facts : Record.Facts M) (S : Setup V) (st : M.NS)
    (o' : NamedObject V) :
    M.receipt_process S st o' = st ∨
      Restated.Vocabulary.Execution.Object.processed M (M.receipt_process S st o') o' = true := by
  have hn := facts.nd.receipt_noop_or_processed S st
  cases o' with
  | block B => exact (hn.1 B).imp id decide_eq_true
  | gfVote u => exact (hn.2.1 u).imp id decide_eq_true
  | attest a => exact (hn.2.2 a).imp id decide_eq_true

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- If `Restated.CarriedCall M S before B o` holds, the block `B` carries `o`. -/
theorem carries_of_carriedCall (facts : Record.Facts M) (S : Setup V) (before : M.NS) (B : NamedBlock V)
    {o : NamedObject V} (h : Restated.CarriedCall M S before B o) : carries (.block B) o := by
  cases o with
  | block _ => exact h.elim
  | gfVote u =>
      obtain ⟨⟨j, hj⟩, -, -⟩ := h
      exact Or.inl ⟨u, List.mem_of_getElem? hj, rfl⟩
  | attest a =>
      obtain ⟨⟨j, hj⟩, -, -⟩ := h
      exact Or.inr ⟨a, List.mem_of_getElem? hj, rfl⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- For every outcome `out` of `v`'s tick at `t` from the node state `n`, the store of `out` records
    nothing that `n`'s store with its clock set to `t` did not record, except the objects `out`
    sends and what a block among them carries. -/
theorem addsOnlyCarried_named_tick (facts : Record.Facts M) (S : Setup V) (v : V) (n : M.N)
    (t : Int) (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out) :
    Restated.AddsOnlyCarried M S (M.ns_setClock S.E n.st t) out.1.st out.2 := by
  obtain ⟨⟨hmB, hmU, hmA⟩, hfB, hfU, hfA⟩ := facts.nd.addsOnlyCarried_node_tick S v n t out hout
  refine ⟨fun o h => ?_, fun o h0 h1 => ?_⟩
  · cases o with
    | block B => exact decide_eq_true (hmB B (of_decide_eq_true h))
    | gfVote u => exact decide_eq_true (hmU u (of_decide_eq_true h))
    | attest a => exact decide_eq_true (hmA a (of_decide_eq_true h))
  · cases o with
    | block B => exact Or.inl (hfB B (of_decide_eq_false h0) (of_decide_eq_true h1))
    | gfVote u => exact hfU u (of_decide_eq_false h0) (of_decide_eq_true h1)
    | attest a => exact hfA a (of_decide_eq_false h0) (of_decide_eq_true h1)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- For every outcome `out₁` of `v`'s tick at `t` from the node state `n`, the store of `out₁`
    records nothing that `n`'s store with its clock set to `t` did not record, except the objects
    `out₁.2` sends and what a block among them carries. -/
theorem addsOnlyCarried_node_tick (facts : Record.Facts M) (S : Setup V) (v : V) (n : M.N) (t : Int) :
    ∀ out₁, M.tick S v n t ⇢ out₁ →
      Restated.AddsOnlyCarried M S (M.ns_setClock S.E n.st t) out₁.1.st out₁.2 := by
  intro out₁ hout
  exact Restated.addsOnlyCarried_named_tick facts S v n t out₁ hout

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- After a `tickAllAwake τ` step, either `v` is awake and not adversarial at `τ`, and `v`'s next
    node state is that of some outcome of the tick from
    `Record.wakeStage M Sched τ x[k] v`, `v`'s node state after its wake; or `v`'s next node state
    is that node state unchanged. -/
theorem st_succ_of_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k τ : Nat} (v : V)
    (hl : x.lbl k = AtomicAction.tickAllAwake τ) :
    (v ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) ∧
        ∃ out₁, M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (τ : Int) x[k] v) (τ : Int) ⇢ out₁ ∧
          x[k + 1][v].st = out₁.1) ∨
      x[k + 1][v].st = Record.wakeStage M Sched (τ : Int) x[k] v := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, w', tk, hwake, htick, hc⟩ := hs
  by_cases hv : v ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int)
  · have hwst : (w' v).state = Record.wakeStage M Sched (τ : Int) x[k] v :=
      Record.wakeStage_of_TickAllAwakeWake M S Sched (hwake v)
    have hx1 : x[k + 1][v].st = (tk v).state := by
      have h2 : x[k + 1][v] = (tickAllAwakeUpdate Sched τ x[k] w' tk)[v] := by rw [hc]
      rw [h2, tickAllAwakeUpdate_getElem_react hv]
    have htk := htick v hv
    rcases htk with htk | ⟨-, htk⟩
    · rw [Restated.reaction_tick facts S v ((w' v).state)] at htk
      obtain ⟨out₁, hout, hres⟩ := htk
      refine Or.inl ⟨hv, out₁, ?_, ?_⟩
      · rw [← hwst]; exact hout
      · rw [hx1, hres]
    · refine Or.inr ?_
      rw [hx1, htk, hwst]
  · refine Or.inr ?_
    have h2 : x[k + 1][v] = (tickAllAwakeUpdate Sched τ x[k] w' tk)[v] := by rw [hc]
    rw [h2, tickAllAwakeUpdate_getElem_st_of_not_react hv]
    unfold Record.wakeStage
    rw [if_neg (fun h => hv (Finset.mem_sdiff.mp h).1)]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- An object a validator's store has recorded is still recorded after one more step. -/
theorem processed_mono_step (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (w : V) (o : NamedObject V) (i : Nat)
    (h : Restated.Vocabulary.Execution.Object.processed M (x[i][w].st).st o = true) :
    Restated.Vocabulary.Execution.Object.processed M (x[i + 1][w].st).st o = true := by
  rcases Record.st_succ_cases M S Sched x w i with hst | hst | ⟨t, out, hout, hst⟩ | ⟨o', hproc⟩
  · rw [hst]; exact h
  · rw [hst, (facts.nd.wake_st_record _).1]; exact h
  · rw [hst]
    rcases hout with hout | hout
    · have hkey := (Restated.addsOnlyCarried_named_tick facts (Setup.alwaysAwake S) w _ t out hout).1 o
      rw [processed_setClock' facts] at hkey
      exact hkey h
    · have hkey := (Restated.addsOnlyCarried_named_tick facts (Setup.alwaysAwake S) w _ t out hout).1 o
      rw [processed_setClock' facts, (facts.nd.wake_st_record _).1] at hkey
      exact hkey h
  · rw [facts.nd.process_st (Setup.alwaysAwake S) _ o' _ hproc, processed_mgcwf' facts]
    exact processed_mono_receipt' facts (Setup.alwaysAwake S) (x[i][w].st).st o o' h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- An object a validator's store has recorded after `i` steps is still recorded after `j` steps,
    for `i ≤ j`. -/
theorem processed_mono (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (w : V) (o : NamedObject V) {i j : Nat}
    (hij : i ≤ j) (h : Restated.Vocabulary.Execution.Object.processed M (x[i][w].st).st o = true) :
    Restated.Vocabulary.Execution.Object.processed M (x[j][w].st).st o = true := by
  induction j, hij using Nat.le_induction with
  | base => exact h
  | succ m hm ih => exact Restated.processed_mono_step facts S Sched x w o m ih

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- If a validator's store records an object after one step that it did not record before, then
    either that step delivered to it a message whose payload is that object or a block carrying it,
    the payload not recorded before the step and recorded after, or that step is a tick of that
    validator whose outcome sent the object or a block carrying it. -/
theorem flip_step_cases (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {i : Nat}
    {w : V} {o : NamedObject V}
    (h0 : Restated.Vocabulary.Execution.Object.processed M (x[i][w].st).st o = false)
    (h1 : Restated.Vocabulary.Execution.Object.processed M (x[i + 1][w].st).st o = true) :
    (∃ m : SignedMsg V (NamedObject V), x.lbl i = AtomicAction.deliver w m ∧
        Restated.Vocabulary.Execution.Object.processed M (x[i][w].st).st m.msg = false ∧
        Restated.Vocabulary.Execution.Object.processed M (x[i + 1][w].st).st m.msg = true ∧
        (m.msg = o ∨ ∃ B : NamedBlock V, m.msg = NamedObject.block B ∧
          Restated.CarriedCall M (Setup.alwaysAwake S) (x[i][w].st).st B o)) ∨
      (∃ τ : Nat, x.lbl i = AtomicAction.tickAllAwake τ ∧
        w ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) ∧
        ∃ out₁, M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (τ : Int) x[i] w) (τ : Int) ⇢ out₁ ∧
          x[i + 1][w].st = out₁.1 ∧
          (o ∈ out₁.2 ∨
            ∃ B : NamedBlock V, NamedObject.block B ∈ out₁.2 ∧
              Restated.CarriedCall M (Setup.alwaysAwake S)
                (M.ns_setClock (Setup.alwaysAwake S).E (x[i][w].st).st (τ : Int))
                B o)) := by
  cases hl : x.lbl i with
  | custom _ ev => exact ev.elim
  | adversarial p m =>
      rw [Restated.getElem_succ_of_adversarial facts S Sched x hl, h0] at h1
      exact absurd h1 (by simp)
  | forward p m =>
      rw [Restated.getElem_succ_of_forward facts S Sched x hl, h0] at h1
      exact absurd h1 (by simp)
  | tickAllAwake τ =>
      rcases Restated.st_succ_of_tick facts S Sched x w hl with ⟨haw, out₁, hout, hst⟩ | hst
      · have hkey :=
          (Restated.addsOnlyCarried_node_tick facts (Setup.alwaysAwake S) w
            (Record.wakeStage M Sched (τ : Int) x[i] w) (τ : Int) out₁ hout).2 o
        rw [processed_setClock' facts, Record.wakeStage_st facts] at hkey
        rw [hst] at h1
        exact Or.inr ⟨τ, rfl, haw, out₁, hout, hst, hkey h0 h1⟩
      · rw [hst, Record.wakeStage_st facts, h0] at h1
        exact absurd h1 (by simp)
  | deliver p m =>
      by_cases hp : p = w
      · subst hp
        rcases Restated.st_succ_of_deliver facts S Sched x hl with hproc | ⟨-, hst⟩
        · have hpst := facts.nd.process_st (Setup.alwaysAwake S) _ m.msg _ hproc
          have hpre : Restated.Vocabulary.Execution.Object.processed M (x[i][p].st).st m.msg = false := by
            by_contra hcon
            rw [Bool.not_eq_false] at hcon
            have hnoop := Restated.process_of_processed_sts facts S Sched x i p m.msg hcon _ hproc
            rw [hnoop, h0] at h1
            exact absurd h1 (by simp)
          have hflip : Restated.Vocabulary.Execution.Object.processed M
              (M.receipt_process (Setup.alwaysAwake S) (x[i][p].st).st m.msg) o = true := by
            rw [← processed_mgcwf' facts, ← hpst]; exact h1
          have hpost : Restated.Vocabulary.Execution.Object.processed M (x[i + 1][p].st).st m.msg = true := by
            rcases receipt_noop_or_processed' facts (Setup.alwaysAwake S) (x[i][p].st).st m.msg
              with hnoop | hyes
            · exfalso
              rw [hnoop, h0] at hflip
              exact absurd hflip (by simp)
            · rw [hpst, processed_mgcwf' facts]; exact hyes
          refine Or.inl ⟨m, rfl, hpre, hpost, ?_⟩
          rcases flip_of_process' facts (Setup.alwaysAwake S) (x[i][p].st).st m.msg o h0 hflip
            with h | ⟨B, hB, hc⟩
          · exact Or.inl h.symm
          · exact Or.inr ⟨B, hB, hc⟩
        · rw [hst, h0] at h1
          exact absurd h1 (by simp)
      · rw [Restated.getElem_succ_of_deliver_ne facts S Sched x hl hp, h0] at h1
        exact absurd h1 (by simp)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- An object that a validator's store records after `n` steps, and that its initial store does not
    record, was first recorded at some step `k < n`: not recorded after `k` steps, recorded after
    `k + 1`. -/
theorem exists_first_flip (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (w : V) (o : NamedObject V) :
    ∀ n : Nat, Restated.Vocabulary.Execution.Object.processed M (x[0][w].st).st o = false →
      Restated.Vocabulary.Execution.Object.processed M (x[n][w].st).st o = true →
      ∃ k < n, Restated.Vocabulary.Execution.Object.processed M (x[k][w].st).st o = false ∧
        Restated.Vocabulary.Execution.Object.processed M (x[k + 1][w].st).st o = true
  | 0, h0, hn => by rw [h0] at hn; exact absurd hn (by simp)
  | n + 1, h0, hn => by
      by_cases hb : Restated.Vocabulary.Execution.Object.processed M (x[n][w].st).st o = true
      · obtain ⟨k, hk, hk0, hk1⟩ := exists_first_flip facts S Sched x w o n h0 hb
        exact ⟨k, Nat.lt_succ_of_lt hk, hk0, hk1⟩
      · exact ⟨n, Nat.lt_succ_self n, by simpa using hb, hn⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- For every path `W` of `rho`, an object a validator emits along `W` names that validator as its
    author. -/
theorem author_of_emits (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) {v : V} {o : NamedObject V}
    {t : Int} (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (h : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v o t) : NamedObject.author o = some v := by
  cases o with
  | gfVote u =>
      rw [author_gfVote]
      rw [(Restated.Vocabulary.Proofs.Optimistic.emits_gfVote_shape facts S W h
        (fun i => facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hW i).1 v)
        (fun i => facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hW i).1 v)).2.2.1]
  | attest a =>
      rw [author_attest]
      rw [(Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hW h).1]
  | block B =>
      obtain ⟨i, -, out, hout, -, hmem⟩ := h
      have _hr : M.reachedNode (W i v) := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hW i).1 v
      have _hv : M.runs_as (W i v) v := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hW i).1 v
      have hprop := (Restated.Vocabulary.Proofs.HealingSurface.block_mem_on_tick_emit facts S v
        (W i v) t out hout hmem).2
      obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W i v).st.core.toHealing t
        (W i v).cache
      obtain ⟨D, hD⟩ := facts.dt.propose_block_with_nonempty S v (W i v) t out hout
        (facts.nd.block_mem_on_tick_emit S v (W i v) t out hout hmem).1.1 (facts.nd.block_mem_on_tick_emit S v (W i v) t out hout hmem).1.2.1
        (facts.nd.block_mem_on_tick_emit S v (W i v) t out hout hmem).1.2.2
        (facts.nd.block_mem_on_tick_emit_awake S v (W i v) t out hout hmem) c hc
      rw [author_block]
      rw [facts.dt.proposer_of_propose_block_with _ S.E S.hc S.cfg (S.node v) _ B D hD
          (hprop c hc D hD),
        S.node_val_index v]

end

end DecoupledConsensusModel.Sts.Restated
