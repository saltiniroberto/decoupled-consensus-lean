import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bRelay
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRecord
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Redelivery
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.VocabularyAssumptionsLemmas
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Pool
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_BlockEmission
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepKitRelay
import Model.Conditions.ProcessedFlip
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_VocabularyAssumptions
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bStepKitRelay

/-!
# Recording and relaying Goldfish votes

When a delivery records a Goldfish vote in the receiver's pool, the step at which a store first
records an object, the pool-and-stamp invariant of every store, and the relay obligation that
synchrony from wake gives, stated over a model `M : Record.Model V` and its facts
`facts : Record.Facts M`.
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

/-- A vote of the store's slot or the one before, signed by a member of its slot's committee, not
    already held, and from a signer the store does not see equivocating, is in the pool of its slot
    after `M.on_goldfish_vote_checked`, stamped with the store's clock. -/
theorem on_goldfish_vote_records (facts : Record.Facts M) (E : Env V) (st : M.S) (u : GoldfishVote V)
    (hwin : ¬ (u.slot < st.s - 1 ∨ st.s < u.slot))
    (hcomm : u.val_index ∈ E.committee u.slot) (hnew : u ∉ (M.store_pool st u.slot))
    (hne : M.equivocates ((M.store_pool st u.slot)) u.val_index = false) :
    u ∈ (M.store_pool (M.on_goldfish_vote_checked E st u) u.slot) ∧
      (M.on_goldfish_vote_checked E st u).timestamp_vote u = some (st.t : Stamp) := by
  have hmem : u ∉ st.gf_votes u.slot := fun hm => hnew ((facts.sto.mem_store_pool_iff st u.slot u).mpr hm)
  have h1 : ¬ (u.slot < st.s - 1 ∨ st.s < u.slot ∨ u ∈ st.gf_votes u.slot) := by
    rintro (h | h | h)
    · exact hwin (Or.inl h)
    · exact hwin (Or.inr h)
    · exact hmem h
  have h2 : ¬ M.equivocates ((M.store_pool st u.slot)) u.val_index = true := by
    rw [hne]; simp
  have hchecked : M.on_goldfish_vote_checked E st u = M.on_goldfish_vote st u :=
    facts.hd.on_goldfish_vote_checked_of_mem_committee E st u hcomm
  obtain ⟨hgf, hts, -⟩ := Restated.Vocabulary.Protocol.on_goldfish_vote_insert facts st u h1 h2
  rw [hchecked]
  refine ⟨?_, ?_⟩
  · rw [facts.sto.mem_store_pool_iff, hgf]
    simp

  · rw [hts]
    simp

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After any number of steps, every validator's store clock is at least `0`. -/
theorem clock_nonneg_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (m : Nat) (w : V) : 0 ≤ (x[m][w].st).st.core.t := by
  have h0 : (x[0][w].st).st.core.t = 0 := by
    rw [Record.st_zero M S Sched x w, facts.nd.initial_clock_eq_zero]
  have hmono := Restated.clock_mono_sts facts S Sched x w (Nat.zero_le m)
  rw [h0] at hmono
  exact hmono

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A delivery of `⟨q, .gfVote u⟩` to `w` at step `k`, whose store finds `u` neither stale nor of a
    future slot, with `u`'s signer in its slot's committee and a receipt that has an outcome
    (`hneRecv`), either finds `u` already in `w`'s pool, or finds its signer already equivocating
    there, or records `u` after the step, stamped with `w`'s store clock at step `k`. -/
theorem gfVote_recorded_of_deliver (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {k : Nat} {q w : V} {u : GoldfishVote V}
    (hl : x.lbl k = AtomicAction.deliver w ⟨q, NamedObject.gfVote u⟩)
    (hwin : ¬ (u.slot < (x[k][w].st).st.core.s - 1 ∨ (x[k][w].st).st.core.s < u.slot))
    (hcomm : u.val_index ∈ S.E.committee u.slot)
    (hneRecv : ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[k][w].st) (NamedObject.gfVote u) ⇢ n') :
    u ∈ (M.store_pool (x[k][w].st).st.core u.slot) ∨
      M.equivocates ((M.store_pool (x[k][w].st).st.core u.slot)) u.val_index = true ∨
      (u ∈ (M.store_pool (x[k + 1][w].st).st.core u.slot) ∧
        (x[k + 1][w].st).st.core.timestamp_vote u
          = some ((x[k][w].st).st.core.t : Stamp)) := by
  by_cases hmem : u ∈ (M.store_pool (x[k][w].st).st.core u.slot)
  · exact Or.inl hmem
  by_cases heq : M.equivocates ((M.store_pool (x[k][w].st).st.core u.slot)) u.val_index = true
  · exact Or.inr (Or.inl heq)
  refine Or.inr (Or.inr ?_)
  have hne : M.equivocates ((M.store_pool (x[k][w].st).st.core u.slot)) u.val_index = false := by
    simpa using heq
  obtain ⟨n', hn'⟩ := hneRecv
  rcases Restated.st_succ_of_deliver facts S Sched x hl with hproc | ⟨hno, -⟩
  · have hst := facts.nd.process_st (Setup.alwaysAwake S) _ _ _ hproc
    have hcore : (M.receipt_process (Setup.alwaysAwake S) (x[k][w].st).st
        (NamedObject.gfVote u)).core = M.on_goldfish_vote_checked S.E (x[k][w].st).st.core u := by
      rw [facts.nd.process_gfVote, facts.hd.ns_with_core_core]
      rfl
    obtain ⟨hrec, hts⟩ :=
      Restated.on_goldfish_vote_records facts S.E (x[k][w].st).st.core u hwin hcomm hmem hne
    refine ⟨?_, ?_⟩
    · rw [facts.sto.mem_store_pool_iff] at hrec ⊢
      rw [hst, facts.nd.make_grades_compatible_with_finalized_core_gf_votes]
      show u ∈ (M.receipt_process (Setup.alwaysAwake S) (x[k][w].st).st
        (NamedObject.gfVote u)).core.gf_votes u.slot
      rw [hcore]
      exact hrec
    · rw [hst, facts.nd.make_grades_compatible_with_finalized_core_timestamp_vote]
      show (M.receipt_process (Setup.alwaysAwake S) (x[k][w].st).st
        (NamedObject.gfVote u)).core.timestamp_vote u = _
      rw [hcore]
      exact hts
  · exact absurd hn' (hno n')

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A store whose clock is at or after the start of `u`'s slot, read at a step whose time is
    strictly before the start of slot `u.slot + 2`, finds `u` neither stale nor of a future slot. -/
theorem gf_window_of_clock (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (k : Nat) (w : V) (u : GoldfishVote V)
    (hlo : slotStart S.E.Δ u.slot ≤ (x[k][w].st).st.core.t)
    (hhi : (x[k].time : Int) < slotStart S.E.Δ (u.slot + 2)) :
    ¬ (u.slot < (x[k][w].st).st.core.s - 1 ∨ (x[k][w].st).st.core.s < u.slot) := by
  have hs : (x[k][w].st).st.core.s = S.E.slotOf (x[k][w].st).st.core.t :=
    Restated.slotOfClock_sts facts S Sched x k w
  have hct : (x[k][w].st).st.core.t ≤ (x[k].time : Int) := Restated.clock_le_time_sts facts S Sched x k w
  have hge : u.slot ≤ (x[k][w].st).st.core.s := by
    rw [hs]
    have hm := slotOf_mono_sts S hlo
    rw [slotOf_slotStart S u.slot] at hm
    exact hm
  have hle : (x[k][w].st).st.core.s ≤ u.slot + 1 := by
    rw [hs]
    exact Nat.le_of_lt_succ (Nat.lt_of_le_of_lt (slotOf_mono_sts S hct)
      (slotOf_lt_of_lt_slotStart S (Int.natCast_nonneg _) hhi))
  have hsub : (x[k][w].st).st.core.s - 1 ≤ u.slot := Nat.sub_le_iff_le_add.mpr hle
  rintro (h | h)
  · exact absurd h (Nat.not_lt.mpr hsub)
  · exact absurd h (Nat.not_lt.mpr hge)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A receiver awake from the start of `u`'s slot to the time of step `k`, not held by the adversary
    at that start, at a step whose time is at or after that start and strictly before the start of
    slot `u.slot + 2`, finds `u` neither stale nor of a future slot. The hypothesis `hneTick` says
    that `w`'s tick at the start of `u`'s slot has an outcome. -/
theorem gf_window_of_awakeThroughout (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) (k : Nat) (w : V)
    (u : GoldfishVote V)
    (hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ u.slot) (x[k].time : Int))
    (hwh : w ∉ Sched.adv (slotStart S.E.Δ u.slot))
    (hlo : slotStart S.E.Δ u.slot ≤ (x[k].time : Int)) (hpos : 0 < u.slot)
    (hhi : (x[k].time : Int) < slotStart S.E.Δ (u.slot + 2))
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (slotStart S.E.Δ u.slot) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (slotStart S.E.Δ u.slot) x[n] w) (slotStart S.E.Δ u.slot) ⇢ out) :
    ¬ (u.slot < (x[k][w].st).st.core.s - 1 ∨ (x[k][w].st).st.core.s < u.slot) := by
  obtain ⟨n, htick⟩ := Restated.exists_tickStepAt facts x htd (slotStart_pos S hpos)
  have haw : w ∈ Sched.awake (slotStart S.E.Δ u.slot) :=
    mem_awake_of_awakeThroughout Sched hawT (le_refl _) hlo
  obtain ⟨h1, h0⟩ := Restated.tickStepAt_time facts x htick
  have hnk : n + 1 ≤ k := by
    by_contra hcon
    have hkn : k ≤ n := by omega
    have hmt : (x[k].time : Int) ≤ (x[n].time : Int) := Restated.time_mono_int facts S Sched x hkn
    linarith
  exact Restated.gf_window_of_clock facts S Sched x k w u
    (Restated.clock_ge_of_tickStepAt_awake_sts facts S Sched x htick (Finset.mem_sdiff.2 ⟨haw, hwh⟩)
      (slotStart_emod_delta S u.slot) (hneTick n htick) hnk)
    hhi

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `w`'s store does not record `o` initially and does after `m` steps, then some step `i < m` is
    the one at which it first records `o`. -/
theorem exists_flip_of_processed (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (w : V) (o : NamedObject V) {m : Nat}
    (h0 : Restated.Vocabulary.Execution.Object.processed M (x[0][w].st).st o = false)
    (hm : Restated.Vocabulary.Execution.Object.processed M (x[m][w].st).st o = true) :
    ∃ i : Nat, i < m ∧ Restated.Vocabulary.Execution.Object.processed M (x[i][w].st).st o = false ∧
      Restated.Vocabulary.Execution.Object.processed M (x[i + 1][w].st).st o = true :=
  Restated.exists_first_flip facts S Sched x w o m h0 hm

/-- If `w`'s store does not record `o` after `i` steps and does after `i + 1` steps, then `w`
    accepts `o` at step `i` (`AcceptsAtStep`). -/
theorem acceptsAtStep_of_flip (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {i : Nat}
    {w : V} {o : NamedObject V}
    (h0 : Restated.Vocabulary.Execution.Object.processed M (x[i][w].st).st o = false)
    (h1 : Restated.Vocabulary.Execution.Object.processed M (x[i + 1][w].st).st o = true) :
    Restated.AcceptsAtStep M S x i w o := by
  rcases Restated.flip_step_cases facts S Sched x h0 h1 with
    ⟨m, hlbl, -, -, hpay⟩ | ⟨τ, hlbl, haw, -, out₁, hout₁, hst, hem⟩
  · refine Or.inl ⟨m, hlbl, ?_⟩
    rcases hpay with h | ⟨B, hB, hcc⟩
    · exact Or.inl h
    · rw [hB]
      exact Or.inr
        (Restated.carries_of_carriedCall facts (Setup.alwaysAwake S) (x[i][w].st).st B hcc)
  · have hstep : w ∉ Sched.adv (τ : Int) → (τ : Int) % S.E.Δ = 0 →
        x[i + 1][w].st = out₁.1 := fun _ _ => hst
    rcases hem with h | ⟨B, hmem, hcc⟩
    · exact Or.inr ⟨τ, o, hlbl, (Finset.mem_sdiff.1 haw).1, ⟨out₁, hout₁, h, hstep⟩,
        Or.inl rfl⟩
    · exact Or.inr ⟨τ, NamedObject.block B, hlbl, (Finset.mem_sdiff.1 haw).1,
        ⟨out₁, hout₁, hmem, hstep⟩,
        Or.inr (Restated.carries_of_carriedCall facts (Setup.alwaysAwake S) _ B hcc)⟩

/-- If `u` is in `w`'s pool for its slot after `m` steps, then some step `i < m` is an acceptance of
    `u` by `w` at which `u` enters that pool. -/
theorem accepts_of_mem_pool (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {m : Nat}
    {w : V} {u : GoldfishVote V}
    (hu : u ∈ (M.store_pool (x[m][w].st).st.core u.slot)) :
    ∃ i : Nat, i < m ∧ Restated.AcceptsAtStep M S x i w (NamedObject.gfVote u) ∧
      u ∉ (M.store_pool (x[i][w].st).st.core u.slot) ∧
      u ∈ (M.store_pool (x[i + 1][w].st).st.core u.slot) := by
  have h0 : Restated.Vocabulary.Execution.Object.processed M (x[0][w].st).st
      (NamedObject.gfVote u) = false := by
    rw [Record.st_zero M S Sched x w, facts.nd.initial_st]
    exact decide_eq_false (fun h =>
      facts.hd.initial_core_not_mem_pool _ _ ((facts.sto.mem_store_pool_iff _ _ _).2 h))
  have hm : Restated.Vocabulary.Execution.Object.processed M (x[m][w].st).st
      (NamedObject.gfVote u) = true :=
    decide_eq_true ((facts.sto.mem_store_pool_iff _ _ _).1 hu)
  obtain ⟨i, him, hf0, hf1⟩ :=
    Restated.exists_first_flip facts S Sched x w (NamedObject.gfVote u) m h0 hm
  exact ⟨i, him, acceptsAtStep_of_flip facts S Sched x hf0 hf1,
    fun h => absurd ((facts.sto.mem_store_pool_iff _ _ _).1 h) (of_decide_eq_false hf0),
    (facts.sto.mem_store_pool_iff _ _ _).2 (of_decide_eq_true hf1)⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `PoolStamps` of a node state's store holds for the node state of every outcome of the receipt of
    any object. -/
theorem poolStamps_node_process (facts : Record.Facts M) (S' : Setup V) (n : M.N) (o : NamedObject V)
    (h : Restated.Vocabulary.Protocol.PoolStamps M n.st.core) : ∀ n₁, M.process S' n o ⇢ n₁ → 
    Restated.Vocabulary.Protocol.PoolStamps M n₁.st.core :=
  fun n₁ hn₁ => (facts.ndRun.poolStep_process S' n o n₁ hn₁ h).2

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `k` is the tick at `t`, either `v` is awake and not held by the adversary at `t`, `t` is
    a multiple of `Δ`, and the step took an outcome `out` of `v`'s tick from a node state `n₀` with
    `v`'s store after `k` steps, which a run reaches and which runs as `v`, `v`'s node state after
    the step is `out`'s, and every object `out` sends is signed by `v` in
    `x[k + 1].sent - x[k].sent`; or `v`'s store after `k + 1` steps is its store after `k` steps. -/
private theorem tick_step_cases_sent (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k t : Nat} (v : V)
    (hl : x.lbl k = AtomicAction.tickAllAwake t) :
    (v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧ (t : Int) % S.E.Δ = 0 ∧
      ∃ (n₀ : M.N) (out : M.N × List (NamedObject V)), n₀.st = (x[k][v].st).st ∧
        (M.reachedNode n₀ ∧ M.runs_as n₀ v) ∧
        M.tick (Setup.alwaysAwake S) v n₀ (t : Int) ⇢ out ∧ x[k + 1][v].st = out.1 ∧
        ∀ o ∈ out.2, (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent - x[k].sent) ∨
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
    by_cases hdvd : (t : Int) % S.E.Δ = 0
    · rcases htick v haw with hmem | hrest
      · simp only [Record.reactionsOf, if_pos hdvd, Set.mem_setOf_eq] at hmem
        obtain ⟨out, hout, htkv⟩ := hmem
        have hwS : (w v).state = Record.wakeStage M Sched (t : Int) x[k] v :=
          Record.wakeStage_of_TickAllAwakeWake M S Sched (hwake v)
        refine Or.inl ⟨haw, hdvd, (w v).state, out, hwst,
          ⟨by rw [hwS]; exact Record.reachedNode_wakeStage facts S Sched x k v t,
            by rw [hwS]; exact Record.runs_as_wakeStage facts S Sched x k v t⟩, hout, ?_, ?_⟩
        · rw [hx1, htkv]
        · intro o ho
          have hsent : x[k + 1].sent = x[k].sent
              + (Sched.awake (t : Int) \ Sched.adv (t : Int)).sum
                  (fun q => ((w q).send + (tk q).send).map (SignedMsg.mk q)) := by
            rw [hc]; rfl
          rw [hsent, add_tsub_cancel_left]
          refine Multiset.mem_sum.2 ⟨v, haw, ?_⟩
          refine Multiset.mem_map.2 ⟨o, Multiset.mem_add.2 (Or.inr ?_), rfl⟩
          rw [htkv]
          exact Multiset.mem_coe.2 ho
      · refine Or.inr ?_
        obtain ⟨-, hres⟩ := hrest
        rw [hx1, hres, hwst]
    · refine Or.inr ?_
      rcases Record.protocolOf_step_tick M S (htick v haw) with ⟨hd, -⟩ | ⟨-, hres⟩
      · exact absurd hd hdvd
      · rw [hx1, hres, hwst]
  · refine Or.inr ?_
    have h2 : x[k + 1][v] = (tickAllAwakeUpdate Sched t x[k] w tk)[v] := by rw [hc]
    rw [h2, tickAllAwakeUpdate_getElem_st_of_not_react haw]

/-- After any number of steps, every validator's store satisfies `PoolStamps`: its Goldfish buckets
    hold votes of their own slot, it stamps exactly the votes it pools, and no stamp is later than
    its clock. -/
theorem poolStamps_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (m : Nat) (w : V) :
    Restated.Vocabulary.Protocol.PoolStamps M (x[m][w].st).st.core := by
  induction m with
  | zero =>
      rw [Record.st_zero M S Sched x w, facts.nd.initial_st]
      exact facts.hd.poolStamps_initial
  | succ i ih =>
      cases hl : x.lbl i with
      | tickAllAwake τ =>
          rcases tick_step_cases_sent facts S Sched x w hl with
            ⟨-, -, n₀, out₁, hn₀, -, hout, hst, -⟩ | hst
          · obtain ⟨hten, -⟩ := Restated.tickAllAwake_time facts S Sched x hl
            have hle : n₀.st.core.t ≤ (τ : Int) := by
              rw [hn₀]
              have h1 := Restated.clock_le_time_sts facts S Sched x i w
              have h2 : (x[i].time : Int) + 1 = (τ : Int) := by exact_mod_cast hten
              linarith
            have ih' : Restated.Vocabulary.Protocol.PoolStamps M n₀.st.core := by
              rw [hn₀]; exact ih
            rw [hst]
            exact ((facts.ndRun.voteInsertStep_onTickEmit (Setup.alwaysAwake S) w n₀ (τ : Int)
              out₁ hout hle).poolStep ih').2
          · rw [hst]; exact ih
      | deliver p sm =>
          by_cases hp : p = w
          · subst hp
            rcases Restated.st_succ_of_deliver facts S Sched x hl with hproc | ⟨-, hst⟩
            · exact Restated.poolStamps_node_process facts (Setup.alwaysAwake S) (x[i][p].st) sm.msg ih
                _ hproc
            · rw [hst]; exact ih
          · rw [Restated.getElem_succ_of_deliver_ne facts S Sched x hl hp]; exact ih
      | custom p ev => exact ev.elim
      | adversarial p mm =>
          rw [Restated.getElem_succ_of_adversarial facts S Sched x hl]; exact ih
      | forward p mm =>
          rw [Restated.getElem_succ_of_forward facts S Sched x hl]; exact ih

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `w`'s store after `m` steps holds `u` in the pool of `u`'s slot, its stamp for `u` is some
    `τ` at or before `w`'s store clock there. -/
theorem stamp_le_clock_gfVote (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (m : Nat) (w : V) {u : GoldfishVote V}
    (hu : u ∈ (M.store_pool (x[m][w].st).st.core u.slot)) :
    ∃ τ : Stamp, (x[m][w].st).st.core.timestamp_vote u = some τ ∧
      τ ≤ ((x[m][w].st).st.core.t : Stamp) := by
  have hps := Restated.poolStamps_sts facts S Sched x m w
  have hmem : u ∈ (x[m][w].st).st.core.gf_votes u.slot := (facts.sto.mem_store_pool_iff _ _ _).mp hu
  have hs := hps.stamped u.slot u hmem
  cases hcase : (x[m][w].st).st.core.timestamp_vote u with
  | none => rw [hcase] at hs; simp at hs
  | some c => exact ⟨c, rfl, hps.bounded u c hcase⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `n`'s store is `v`'s store after `i` steps and an outcome of `v`'s tick at `τ` from `n` sends
    a block `B`, then every Goldfish vote `B` includes is in `v`'s pool of its slot after `i` steps.
    The hypotheses `hreach` and `hruns` say that `n` is a node state a run reaches and that it runs
    as `v`. -/
private theorem mem_pool_of_mem_node_tick_block (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (v : V)
    (n : M.N) (hn : n.st = (x[i][v].st).st) (τ : Int) {B : NamedBlock V} {u : GoldfishVote V}
    (out : M.N × List (NamedObject V))
    (hout : M.tick (Setup.alwaysAwake S) v n τ ⇢ out)
    (hem : NamedObject.block B ∈ out.2)
    (hu : u ∈ B.gf_votes) (hreach : M.reachedNode n := by trivial)
    (hruns : M.runs_as n v := by trivial) :
    u ∈ (M.store_pool (x[i][v].st).st.core u.slot) := by
  obtain ⟨-, hprop⟩ := facts.nd.block_mem_on_tick_emit (Setup.alwaysAwake S) v n τ out hout hem
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
    n.st.core.toHealing τ n.cache
  obtain ⟨D, hD⟩ := facts.dt.propose_block_with_nonempty (Setup.alwaysAwake S) v n τ out hout
    (facts.nd.block_mem_on_tick_emit (Setup.alwaysAwake S) v n τ out hout hem).1.1 (facts.nd.block_mem_on_tick_emit (Setup.alwaysAwake S) v n τ out hout hem).1.2.1
    (facts.nd.block_mem_on_tick_emit (Setup.alwaysAwake S) v n τ out hout hem).1.2.2
    (facts.nd.block_mem_on_tick_emit_awake (Setup.alwaysAwake S) v n τ out hout hem) c hc
  have hDB := hprop c hc D hD
  obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.frameContract c) .poolAndCarried
    (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node v)
    (M.ns_setClock (Setup.alwaysAwake S).E n.st τ)
  have hoB := facts.dt.proposal_with_eq_of_propose_block_with_snd _ _ _ _ _ _ D hD hDB o ho
  have hgf := facts.dt.proposal_with_gf_votes _ .poolAndCarried _ _ _ _ o ho hoB
  rw [hgf] at hu
  have hpool := (facts.sto.mem_store_pool_iff _ _ _).2 hu
  rw [facts.hd.ModelProperties_setClock_core_pool, hn] at hpool
  have hslot := (Restated.poolStamps_sts facts S Sched x i v).slot _ u
    ((facts.sto.mem_store_pool_iff _ _ _).1 hpool)
  rw [← hslot] at hpool
  exact hpool

/-- If an outcome of `v`'s tick at `τ` from its wake-stage node state after `i` steps sends a block
    `B`, then every Goldfish vote `B` includes is in `v`'s pool of its slot after `i` steps. -/
theorem mem_pool_of_mem_tick_block (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (v : V) (τ : Int) {B : NamedBlock V}
    {u : GoldfishVote V} (out : M.N × List (NamedObject V))
    (hout : M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched τ x[i] v) τ ⇢ out)
    (hem : NamedObject.block B ∈ out.2)
    (hu : u ∈ B.gf_votes) :
    u ∈ (M.store_pool (x[i][v].st).st.core u.slot) :=
  mem_pool_of_mem_node_tick_block facts S Sched x i v (Record.wakeStage M Sched τ x[i] v)
    (Record.wakeStage_st facts Sched τ x[i] v) τ out hout hem hu
    (Record.reachedNode_wakeStage facts S Sched x i v τ) (Record.runs_as_wakeStage facts S Sched x i v τ)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `SynchronyFromWake` gives `GfVoteRelayAtAccept`: whenever an honest validator's store records a
    Goldfish vote, every validator awake from that step through the deadline is delivered the vote
    before the deadline. -/
theorem gfVoteRelayAtAccept_of_sync (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (hsync : Restated.SynchronyFromWake M S x) :
    Restated.GfVoteRelayAtAccept M S x := by
  intro i v w u h0 h1 hvh _hawi hwaw
  have h0' : u ∉ (x[i][v].st).st.core.gf_votes u.slot :=
    fun h => h0 ((facts.sto.mem_store_pool_iff _ _ _).2 h)
  have h1' : u ∈ (x[i + 1][v].st).st.core.gf_votes u.slot :=
    (facts.sto.mem_store_pool_iff _ _ _).1 h1
  have hti : (x[i].time : Int) ≤ (x[i + 1].time : Int) := by
    exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_succ i)
  have hwin : w ∈ Sched.awakeThroughout (x[i].time : Int)
      (max (x[i].time : Int) S.E.t_GST + S.E.Δ) :=
    awakeThroughout_shrink Sched hwaw
      (by have := max_le_max hti (le_refl S.E.t_GST); linarith)
  have hsend : Restated.HonestSendAt M S x i
      (⟨v, NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V)) := by
    cases hl : x.lbl i with
    | custom _ ev => exact ev.elim
    | adversarial p mm =>
        rw [Restated.getElem_succ_of_adversarial facts S Sched x hl] at h1'
        exact absurd h1' h0'
    | forward p mm =>
        rw [Restated.getElem_succ_of_forward facts S Sched x hl] at h1'
        exact absurd h1' h0'
    | deliver p m =>
        by_cases hp : p = v
        · subst hp
          rcases Restated.st_succ_of_deliver facts S Sched x hl with hproc | ⟨-, hst⟩
          ·
            have hpst := facts.nd.process_st (Setup.alwaysAwake S) _ m.msg _ hproc
            have h1r : u ∈ (M.receipt_process (Setup.alwaysAwake S) (x[i][p].st).st
                m.msg).core.gf_votes u.slot := by
              rw [hpst, facts.nd.make_grades_compatible_with_finalized_core_gf_votes] at h1'
              exact h1'
            have ho : NamedObject.gfVote u ∈ relayedObjects m.msg := by
              rw [mem_relayedObjects_iff]
              rcases (facts.nd.flip_of_process (Setup.alwaysAwake S) (x[i][p].st).st m.msg).2.1
                  u h0' h1r with heq | ⟨B, hB, hcc⟩
              · exact Or.inl heq
              · rw [hB]; exact Or.inr (Restated.carries_of_carriedCall facts _ _ B hcc)
            exact Restated.honestSendAt_of_deliver_relay facts S Sched x hl ho ⟨_, hproc⟩
          · rw [hst] at h1'
            exact absurd h1' h0'
        · rw [Restated.getElem_succ_of_deliver_ne facts S Sched x hl hp] at h1'
          exact absurd h1' h0'
    | tickAllAwake τ =>
        rcases tick_step_cases_sent facts S Sched x v hl with
          ⟨-, -, n₀, out, hn₀, ⟨hr₀, hv₀⟩, hout, hst, hsent⟩ | hst
        · have hkey := (facts.nd.addsOnlyCarried_node_tick (Setup.alwaysAwake S) v n₀ (τ : Int)
            out hout).2.2.1 u
          have hpre : u ∉ (M.ns_setClock (Setup.alwaysAwake S).E n₀.st (τ : Int)).core.gf_votes
              u.slot := by
            rw [facts.hd.setClock_core_gf_votes, hn₀]; exact h0'
          rw [hst] at h1'
          rcases hkey hpre h1' with hmem | ⟨B, hem, ⟨j, hj⟩, -, -⟩
          · exact ⟨hsent _ hmem, hvh (x[i].time : Int) (le_refl _)⟩
          · exfalso
            exact h0 (mem_pool_of_mem_node_tick_block facts S Sched x i v n₀ hn₀ (τ : Int) out
              hout hem (List.mem_of_getElem? hj) hr₀ hv₀)
        · rw [hst] at h1'
          exact absurd h1' h0'
  exact Restated.relay_of_honestSendAt_from facts S Sched x hsync (le_refl i) hti hsend rfl hwin

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The time after `i + 1` steps is at most one more than the time after `i` steps. -/
theorem time_succ_le (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) : (x[i + 1].time : Int) ≤ (x[i].time : Int) + 1 := by
  cases hl : x.lbl i with
  | tickAllAwake τ =>
      obtain ⟨hten, httime⟩ := Restated.tickAllAwake_time facts S Sched x hl
      have h : x[i + 1].time = x[i].time + 1 := by rw [httime, ← hten]
      omega
  | deliver p sm =>
      have h : x[i + 1].time = x[i].time := Restated.deliver_time facts S Sched x hl
      omega
  | custom p ev => exact ev.elim
  | adversarial p mm =>
      have h : x[i + 1].time = x[i].time := Restated.adversarial_time facts S Sched x hl
      omega
  | forward p mm =>
      have h : x[i + 1].time = x[i].time := Restated.forward_time facts S Sched x hl
      omega

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If a Goldfish vote `u` signed by a member of its slot's committee enters `v`'s pool at step `i`,
    `v` is honest through step `i`, and `w` is awake at step `i` and from one before the start of
    `u`'s slot through the deadline `max x[i + 1].time t_GST + Δ`, with the recording at or after
    the slot's start and the deadline at or before the start of slot `u.slot + 2`, then at some step
    `k` from the recording time to strictly before the deadline, `w` holds `u` in its pool after
    step `k` with a stamp at or before `x[k].time`, or already sees `u`'s signer equivocating at
    step `k`. The hypotheses `hneTick` and `hne` say that the ticks and receipts the proof reads
    have an outcome. -/
theorem gfVote_in_pool_of_accepts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (hrelay : Restated.GfVoteRelayAtAccept M S x) (htd : Restated.TimeDiverges M x)
    {i : Nat} {v w : V} {u : GoldfishVote V}
    (h0 : u ∉ (M.store_pool (x[i][v].st).st.core u.slot))
    (h1 : u ∈ (M.store_pool (x[i + 1][v].st).st.core u.slot))
    (hvh : Restated.HonestThrough M Sched x i v)
    (hawi : AtomicAwake x i w) (hcomm : u.val_index ∈ S.E.committee u.slot)
    (hpos : 0 < u.slot)
    (hlo : slotStart S.E.Δ u.slot ≤ (x[i + 1].time : Int))
    (hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ u.slot - 1)
      (max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ))
    (hwh : w ∉ Sched.adv (slotStart S.E.Δ u.slot))
    (hhi : max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ ≤ slotStart S.E.Δ (u.slot + 2))
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (slotStart S.E.Δ u.slot) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (slotStart S.E.Δ u.slot) x[n] w) (slotStart S.E.Δ u.slot) ⇢ out)
    (hne : ∀ (k : Nat) (q : V), x.lbl k = AtomicAction.deliver w ⟨q, NamedObject.gfVote u⟩ →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[k][w].st) (NamedObject.gfVote u) ⇢ n') :
    ∃ k : Nat, (x[i + 1].time : Int) ≤ (x[k].time : Int) ∧
      (x[k].time : Int) < max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ ∧
      ((u ∈ (M.store_pool (x[k + 1][w].st).st.core u.slot) ∧
          ∃ τ : Stamp, (x[k + 1][w].st).st.core.timestamp_vote u = some τ ∧
            τ ≤ ((x[k].time : Int) : Stamp)) ∨
        M.equivocates ((M.store_pool (x[k][w].st).st.core u.slot)) u.val_index = true) := by
  have hloi : slotStart S.E.Δ u.slot - 1 ≤ (x[i].time : Int) := by
    have := Restated.time_succ_le facts S Sched x i
    linarith
  obtain ⟨k, m, hk0, hk1, hlbl, hmsg⟩ :=
    hrelay i v w u h0 h1 hvh hawi
      (awakeThroughout_shrink_left Sched hawT hloi)
  refine ⟨k, hk0, hk1, ?_⟩
  have hm_eq : (⟨m.sender, NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V)) = m := by
    rw [← hmsg]
  have hlbl' : x.lbl k = AtomicAction.deliver w ⟨m.sender, NamedObject.gfVote u⟩ := by
    rw [hlbl, hm_eq]
  have hlok : slotStart S.E.Δ u.slot ≤ (x[k].time : Int) := le_trans hlo hk0
  have hhik : (x[k].time : Int) < slotStart S.E.Δ (u.slot + 2) := lt_of_lt_of_le hk1 hhi
  have hawTk : w ∈ Sched.awakeThroughout (slotStart S.E.Δ u.slot) (x[k].time : Int) :=
    awakeThroughout_shrink Sched (awakeThroughout_shrink_left Sched hawT (by linarith))
      (le_of_lt hk1)
  have hwin := Restated.gf_window_of_awakeThroughout facts S Sched x htd k w u hawTk hwh hlok hpos hhik
    hneTick
  have hstamp : ∀ _hmem : u ∈ (M.store_pool (x[k + 1][w].st).st.core u.slot),
      ∃ τ : Stamp, (x[k + 1][w].st).st.core.timestamp_vote u = some τ ∧
        τ ≤ ((x[k].time : Int) : Stamp) := by
    intro hmem
    obtain ⟨τ, hτ, hb⟩ := Restated.stamp_le_clock_gfVote facts S Sched x (k + 1) w hmem
    refine ⟨τ, hτ, le_trans hb ?_⟩
    have h1 : (x[k + 1][w].st).st.core.t ≤ (x[k + 1].time : Int) :=
      Restated.clock_le_time_sts facts S Sched x (k + 1) w
    have h2 : x[k + 1].time = x[k].time := Restated.deliver_time facts S Sched x hlbl'
    have h3 : (x[k + 1][w].st).st.core.t ≤ (x[k].time : Int) := by
      rw [← h2]; exact h1
    exact WithBot.coe_le_coe.mpr h3
  rcases Restated.gfVote_recorded_of_deliver facts S Sched x hlbl' hwin hcomm
      (hne k m.sender hlbl') with hmk | heq | ⟨hm1, -⟩
  · refine Or.inl ?_
    have hpk : Restated.Vocabulary.Execution.Object.processed M (x[k][w].st).st
        (NamedObject.gfVote u) = true :=
      decide_eq_true ((facts.sto.mem_store_pool_iff _ _ _).1 hmk)
    have hk1mem : u ∈ (M.store_pool (x[k + 1][w].st).st.core u.slot) :=
      (facts.sto.mem_store_pool_iff _ _ _).2 (of_decide_eq_true
        (Restated.processed_mono_step facts S Sched x w (NamedObject.gfVote u) k hpk))
    exact ⟨hk1mem, hstamp hk1mem⟩
  · exact Or.inr heq
  · exact Or.inl ⟨hm1, hstamp hm1⟩

end

end DecoupledConsensusModel.Sts.Restated
