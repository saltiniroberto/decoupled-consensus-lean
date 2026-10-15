import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRecord
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Redelivery
import Proofs.Claims.Restated.RunAll
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepKitConfirm
import Model.Conditions.Claim13bStepKitRelay
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_VocabularyAssumptions
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Confirmation
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bStepKitConfirm

/-!
# Goldfish vote pools and agreement of confirmations

How a store's Goldfish vote pool and stamps evolve along an execution, when a counted vote was
accepted, and the agreement of the blocks two honest validators find eligible at one slot's
confirmation, stated over a model `M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC in
/-- An outcome of `f <$> m` is `f a` for an outcome `a` of `m`. -/
private theorem returns_map_elim {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

open scoped DC in
/-- If `m >>= k` can return `b`, then `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_elim {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β)
    (h : (m >>= k) ⇢ b) : ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_bind, Set.bind_def] at h
  obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.mp h
  cases e with
  | ok a => exact ⟨a, he, hb⟩
  | error err => simp at hb

open scoped DC in
/-- An outcome of the lift of a set `s` is a member of `s`. -/
private theorem returns_lift_elim {α : Type} (s : Set α) (a : α)
    (h : (ExceptT.lift s : DC.NDRE α) ⇢ a) : a ∈ s := by
  unfold Record.Returns at h
  simp only [ExceptT.run_lift, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨a', ha', he⟩ := h
  cases he
  exact ha'

section
open DecoupledConsensusModel.Sts.InsertsAt
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `InsertsAt` is reflexive. -/
theorem InsertsAt.refl' (facts : Record.Facts M) (E : Env V) (c : Int) (st : M.S) :
    Restated.InsertsAt M E c st st := by
  intro hps hc
  exact ⟨⟨fun _ _ hu => hu, fun _ _ h => h⟩, hps, hc, rfl, fun _ h0 h1 => absurd h1 h0⟩

end

section
open DecoupledConsensusModel.Sts.InsertsAt
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `InsertsAt` at one clock reading `c` is transitive. -/
theorem InsertsAt.trans' (facts : Record.Facts M) {E : Env V} {c : Int} {st st' st'' : M.S} (h₁ : Restated.InsertsAt M E c st st') (h₂ : Restated.InsertsAt M E c st' st'') :
    Restated.InsertsAt M E c st st'' := by
  intro hps hc
  obtain ⟨c₁, s₁, k₁, l₁, n₁⟩ := h₁ hps hc
  obtain ⟨c₂, s₂, k₂, l₂, n₂⟩ := h₂ s₁ k₁
  refine ⟨⟨fun k u hu => c₂.mem k u (c₁.mem k u hu),
    fun u τ hτ => c₂.stamp u τ (c₁.stamp u τ hτ)⟩, s₂, k₂, l₂.trans l₁, ?_⟩
  intro u h0 h1
  by_cases hm : u ∈ st'.gf_votes u.slot
  · obtain ⟨hst, hsl, hcm⟩ := n₁ u h0 hm
    exact ⟨c₂.stamp u _ hst, hsl, hcm⟩
  · obtain ⟨hst, hsl, hcm⟩ := n₂ u hm h1
    exact ⟨hst, l₁ ▸ hsl, hcm⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A write that keeps the store's Goldfish votes, their stamps, its clock and its slot field is an
    `InsertsAt` at every time `c`. -/
private theorem insertsAt_of_pool_eq (E : Env V) (c : Int) {st st' : M.S}
    (hg : st'.gf_votes = st.gf_votes) (hts : st'.timestamp_vote = st.timestamp_vote)
    (ht : st'.t = st.t) (hs : st'.s = st.s) : Restated.InsertsAt M E c st st' := by
  intro hps hc
  refine ⟨⟨fun k u hu => by rw [hg]; exact hu, fun u τ hτ => by rw [hts]; exact hτ⟩,
    ⟨fun k u hu => hps.slot k u (by rw [hg] at hu; exact hu),
      fun k u hu => by rw [hts]; exact hps.stamped k u (by rw [hg] at hu; exact hu),
      fun u hu => by rw [hg]; exact hps.pooled u (by rw [hts] at hu; exact hu),
      fun u c' hu => by rw [ht]; exact hps.bounded u c' (by rw [hts] at hu; exact hu)⟩,
    by rw [ht]; exact hc, hs, fun u h0 h1 => absurd (by rw [hg] at h1; exact h1) h0⟩

/-- For every outcome `out` of `v`'s tick at `t` from the node state `n`, `InsertsAt` at `t` runs
    from the clock-stamped store of `n` to `out`'s store: `out`'s store reads `t` on its clock, has
    the stamped store's slot field, and stamps every vote that entered with `t`. The hypothesis `hn`
    says that `n` is a node state a run reaches, and `hv` that `n` runs as `v`. -/
theorem insertsAt_named_tick (facts : Record.Facts M) (S : Setup V) (v : V) (n : M.N)
    (t : Int) :
    ∀ out : M.N × List (NamedObject V), M.tick S v n t ⇢ out →
    ∀ (hn : M.reachedNode n := by trivial) (hv : M.runs_as n v := by trivial),
    Restated.InsertsAt M S.E t (M.ns_setClock S.E n.st t).core out.1.st.core :=
  fun out hc1 _hn _hv => (facts.nd.named_tick_preserves
    (fun st' => Restated.InsertsAt M S.E t (M.ns_setClock S.E n.st t).core st'.core) S v n t
    (fun c _ st' h D hD => Restated.InsertsAt.trans' facts h
      (facts.dt.insertsAt_named_propose S.E t _ S.hc S.cfg (S.node v) st' D hD))
    (fun c _ st' h D hD => Restated.InsertsAt.trans' facts h
      (facts.dt.insertsAt_named_vote S.E t _ S.hc (S.node v) st' D hD))
    (fun c _ st' s h D hD => Restated.InsertsAt.trans' facts h
      (facts.dt.insertsAt_named_confirmation S.E t _ S.hc st' s D hD))
    (fun c _ st' record' h D hD => Restated.InsertsAt.trans' facts h
      (facts.dt.insertsAt_named_attest S.E t _ S.hc (S.node v) st' record' D hD))
    (fun st' c h => Restated.InsertsAt.trans' facts h
      (insertsAt_of_pool_eq S.E t (facts.nd.store_with_cache_core_gf_votes st' c)
        (facts.nd.store_with_cache_core_timestamp_vote st' c) (facts.nd.store_with_cache_core_t st' c)
        (facts.nd.store_with_cache_core_s st' c)))
    (fun st' h => Restated.InsertsAt.trans' facts h
      (insertsAt_of_pool_eq S.E t (facts.nd.make_grades_compatible_with_finalized_core_gf_votes st')
        (facts.nd.make_grades_compatible_with_finalized_core_timestamp_vote st')
        (facts.nd.make_grades_compatible_with_finalized_core_t st')
        (facts.nd.make_grades_compatible_with_finalized_core_s st')))
    (Restated.InsertsAt.refl' facts S.E t _)) out hc1

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every outcome of `v`'s tick at `t` from `n`, `InsertsAt` at `t` runs from the clock-stamped
    store of `n` to the outcome's store. The hypothesis `hn` says that `n` is a node state a run
    reaches, and `hv` that `n` runs as `v`. -/
theorem insertsAt_tick (facts : Record.Facts M) (S' : Setup V) (v : V) (n : M.N) (t : Int) :
    ∀ out₁, M.tick S' v n t ⇢ out₁ →
    ∀ (hn : M.reachedNode n := by trivial) (hv : M.runs_as n v := by trivial),
    Restated.InsertsAt M S'.E t (M.ns_setClock S'.E n.st t).core
      out₁.1.st.core :=
  fun out₁ hc1 _hn _hv => Restated.insertsAt_named_tick facts S' v n t out₁ hc1

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `k` is the tick at `t`, either the step took an outcome `out` of `v`'s tick from a node
    state `n₀` with `v`'s store after `k` steps, which a run reaches and which runs as `v`, and
    `v`'s node state after `k + 1` steps is `out`'s, or `v`'s store after `k + 1` steps is its store
    after `k` steps. -/
private theorem tick_step_st_cases_confirm (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {k t : Nat} (v : V)
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

/-- Each step keeps every vote and every stamp a validator's store already held. -/
theorem poolCarry_step (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (w : V) :
    Restated.Vocabulary.Protocol.PoolCarry M (x[i][w].st).st.core (x[i + 1][w].st).st.core := by
  have hps := Restated.poolStamps_sts facts S Sched x i w
  cases hl : x.lbl i with
  | tickAllAwake τ =>
      rcases tick_step_st_cases_confirm facts S Sched x w hl with
        ⟨n₀, out₁, hn₀, -, hout, hst⟩ | hst
      · obtain ⟨hten, -⟩ := Restated.tickAllAwake_time facts S Sched x hl
        have hle : n₀.st.core.t ≤ (τ : Int) := by
          rw [hn₀]
          have h1 := Restated.clock_le_time_sts facts S Sched x i w
          have h2 : (x[i].time : Int) + 1 = (τ : Int) := by exact_mod_cast hten
          linarith
        have hps₀ : Restated.Vocabulary.Protocol.PoolStamps M n₀.st.core := by rw [hn₀]; exact hps
        rw [hst, ← hn₀]
        exact ((facts.ndRun.voteInsertStep_onTickEmit (Setup.alwaysAwake S) w n₀ (τ : Int)
          out₁ hout hle).poolStep hps₀).1
      · rw [hst]; exact ⟨fun _ _ h => h, fun _ _ h => h⟩
  | deliver p sm =>
      by_cases hp : p = w
      · subst hp
        rcases Restated.st_succ_of_deliver facts S Sched x hl with hproc | ⟨-, hst⟩
        · exact (facts.ndRun.poolStep_process (Setup.alwaysAwake S) (x[i][p].st) sm.msg _ hproc
            hps).1
        · rw [hst]; exact ⟨fun _ _ h => h, fun _ _ h => h⟩
      · rw [Restated.getElem_succ_of_deliver_ne facts S Sched x hl hp]
        exact ⟨fun _ _ h => h, fun _ _ h => h⟩
  | custom p ev => exact ev.elim
  | adversarial p mm =>
      rw [Restated.getElem_succ_of_adversarial facts S Sched x hl]
      exact ⟨fun _ _ h => h, fun _ _ h => h⟩
  | forward p mm =>
      rw [Restated.getElem_succ_of_forward facts S Sched x hl]
      exact ⟨fun _ _ h => h, fun _ _ h => h⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A stamp a validator's store writes for a vote is kept at every later step. -/
theorem stamp_mono_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (w : V) {m m' : Nat} (hmm : m ≤ m') {u : GoldfishVote V} {τ : Stamp}
    (h : (x[m][w].st).st.core.timestamp_vote u = some τ) :
    (x[m'][w].st).st.core.timestamp_vote u = some τ := by
  induction m', hmm using Nat.le_induction with
  | base => exact h
  | succ k hk ih => exact (Restated.poolCarry_step facts S Sched x k w).stamp u τ ih

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A vote a store holds in its slot-`s` pool has slot `s`. -/
theorem slot_of_mem_pool_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (m : Nat) (w : V) {s : Slot} {u : GoldfishVote V}
    (hu : u ∈ (M.store_pool (x[m][w].st).st.core s)) : u.slot = s :=
  (Restated.poolStamps_sts facts S Sched x m w).slot s u ((facts.sto.mem_store_pool_iff _ _ _).mp hu)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A vote a validator's store holds in the pool of its own slot stays there at every later step. -/
theorem mem_pool_mono_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (w : V) {k m : Nat} (hkm : k ≤ m) {u : GoldfishVote V}
    (hu : u ∈ (M.store_pool (x[k][w].st).st.core u.slot)) :
    u ∈ (M.store_pool (x[m][w].st).st.core u.slot) := by
  have h := Restated.processed_mono facts S Sched x w (NamedObject.gfVote u) hkm
    (by
      simp only [Restated.Vocabulary.Execution.Object.processed]
      exact decide_eq_true ((facts.sto.mem_store_pool_iff _ _ _).mp hu))
  simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] at h
  exact (facts.sto.mem_store_pool_iff _ _ _).mpr h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `u` enters `v`'s pool for its slot at step `i`, then `v`'s store after step `i` stamps `u`
    with its own clock, that clock is at or after the start of `u`'s slot, and `u`'s signer is in
    that slot's committee. -/
theorem stamp_eq_clock_of_flip_gfVote (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {i : Nat} {v : V} {u : GoldfishVote V}
    (h0 : u ∉ (M.store_pool (x[i][v].st).st.core u.slot))
    (h1 : u ∈ (M.store_pool (x[i + 1][v].st).st.core u.slot)) :
    (x[i + 1][v].st).st.core.timestamp_vote u
        = some ((x[i + 1][v].st).st.core.t : Stamp) ∧
      slotStart S.E.Δ u.slot ≤ (x[i + 1][v].st).st.core.t ∧
      u.val_index ∈ S.E.committee u.slot := by
  have _hr_0 : M.reachedNode (x[i][v].st) := Record.reachedNode_sts facts S Sched x i v
  have _hr_1 : M.reachedNode (x[i + 1][v].st) := Record.reachedNode_sts facts S Sched x (i + 1) v
  have hg0 : u ∉ (x[i][v].st).st.core.gf_votes u.slot :=
    fun hm => h0 ((facts.sto.mem_store_pool_iff _ _ _).mpr hm)
  have hg1 : u ∈ (x[i + 1][v].st).st.core.gf_votes u.slot := (facts.sto.mem_store_pool_iff _ _ _).mp h1
  have hps := Restated.poolStamps_sts facts S Sched x i v
  cases hl : x.lbl i with
  | tickAllAwake τ =>
      rcases tick_step_st_cases_confirm facts S Sched x v hl with
        ⟨n₀, out₁, hn₀, ⟨hr₀, hv₀⟩, hout, hst⟩ | hst
      · obtain ⟨hten, -⟩ := Restated.tickAllAwake_time facts S Sched x hl
        have hle : n₀.st.core.t ≤ (τ : Int) := by
          rw [hn₀]
          have ha := Restated.clock_le_time_sts facts S Sched x i v
          have hb : (x[i].time : Int) + 1 = (τ : Int) := by exact_mod_cast hten
          linarith
        rw [← hn₀] at hg0 hps
        have hbase : Restated.Vocabulary.Protocol.PoolStamps M
            (M.ns_setClock S.E n₀.st (τ : Int)).core := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro k u' hu'
            rw [facts.hd.setClock_core_gf_votes] at hu'
            exact hps.slot k u' hu'
          · intro k u' hu'
            rw [facts.hd.setClock_core_gf_votes] at hu'
            rw [facts.hd.setClock_core_timestamp_vote]
            exact hps.stamped k u' hu'
          · intro u' hu'
            rw [facts.hd.setClock_core_timestamp_vote] at hu'
            rw [facts.hd.setClock_core_gf_votes]
            exact hps.pooled u' hu'
          · intro u' c hc
            rw [facts.hd.setClock_core_timestamp_vote] at hc
            rw [facts.hd.Sts_setClock_core_t]
            exact le_trans (hps.bounded u' c hc) (WithBot.coe_le_coe.mpr hle)
        obtain ⟨-, -, hclk, hsl, hnew⟩ :=
          Restated.insertsAt_tick facts (Setup.alwaysAwake S) v n₀ (τ : Int) out₁ hout hr₀ hv₀
            hbase (facts.hd.Sts_setClock_core_t _ _ _)
        rw [hst] at hg1 ⊢
        obtain ⟨hstamp, hslot, hcomm⟩ :=
          hnew u (by rw [facts.hd.setClock_core_gf_votes]; exact hg0) hg1
        refine ⟨?_, ?_, hcomm⟩
        · rw [hstamp, hclk]
        · rw [hclk]
          refine slotStart_le_of_le_slotOf S (Int.natCast_nonneg _) ?_
          exact hslot.trans_eq (facts.hd.Sts_setClock_core_s _ _ _)
      · rw [hst] at hg1; exact absurd hg1 hg0
  | deliver p sm =>
      by_cases hp : p = v
      · subst hp
        rcases Restated.st_succ_of_deliver facts S Sched x hl with hproc | ⟨-, hst⟩
        · obtain ⟨-, -, hclk, hsl, hnew⟩ :=
            facts.ndRun.insertsAt_process (Setup.alwaysAwake S) (x[i][p].st) sm.msg _ hproc hps rfl
          obtain ⟨hstamp, hslot, hcomm⟩ := hnew u hg0 hg1
          refine ⟨?_, ?_, hcomm⟩
          · rw [hstamp, hclk]
          · rw [hclk]
            refine slotStart_le_of_le_slotOf S (Restated.clock_nonneg_sts facts S Sched x i p) ?_
            rw [← Restated.slotOfClock_sts facts S Sched x i p]
            exact hslot
        · rw [hst] at hg1; exact absurd hg1 hg0
      · rw [Restated.getElem_succ_of_deliver_ne facts S Sched x hl hp] at hg1
        exact absurd hg1 hg0
  | custom p ev => exact ev.elim
  | adversarial p mm =>
      rw [Restated.getElem_succ_of_adversarial facts S Sched x hl] at hg1
      exact absurd hg1 hg0
  | forward p mm =>
      rw [Restated.getElem_succ_of_forward facts S Sched x hl] at hg1
      exact absurd hg1 hg0

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `u` enters `v`'s pool for its slot at step `i`, the start of `u`'s slot is at or before the
    time of the configuration after that step. -/
theorem slotStart_le_time_of_flip_gfVote (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {i : Nat} {v : V} {u : GoldfishVote V}
    (h0 : u ∉ (M.store_pool (x[i][v].st).st.core u.slot))
    (h1 : u ∈ (M.store_pool (x[i + 1][v].st).st.core u.slot)) :
    slotStart S.E.Δ u.slot ≤ (x[i + 1].time : Int) :=
  le_trans (Restated.stamp_eq_clock_of_flip_gfVote facts S Sched x h0 h1).2.1
    (Restated.clock_le_time_sts facts S Sched x (i + 1) v)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A validator honest through step `m` and awake from the start of slot `s` to the time of step
    `m`, at or after that start, holds a store clock strictly within one delay of that time. The
    hypothesis `hneTick` says that `v`'s tick has an outcome at every tick step in that interval at
    a multiple of `Δ` at which `v` is awake and not held by the adversary. -/
theorem clock_ge_delta_floor (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) {m : Nat} {v : V} {s : Slot}
    (hpos : 0 < s) (hlo : slotStart S.E.Δ s ≤ (x[m].time : Int))
    (hawv : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (x[m].time : Int))
    (hvh : Restated.HonestThrough M Sched x m v)
    (hneTick : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → v ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ (x[m].time : Int) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t x[n'] v) t ⇢ out) :
    (x[m].time : Int) < (x[m][v].st).st.core.t + S.E.Δ := by
  have hΔpos : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hdm : S.E.Δ * ((x[m].time : Int) / S.E.Δ) + (x[m].time : Int) % S.E.Δ
      = (x[m].time : Int) := Int.mul_ediv_add_emod (x[m].time : Int) S.E.Δ
  have hmod0 : 0 ≤ (x[m].time : Int) % S.E.Δ := Int.emod_nonneg _ (ne_of_gt hΔpos)
  have hmod1 : (x[m].time : Int) % S.E.Δ < S.E.Δ := Int.emod_lt_of_pos _ hΔpos
  have h0le : S.E.Δ * ((x[m].time : Int) / S.E.Δ) ≤ (x[m].time : Int) := by linarith
  have hlt : (x[m].time : Int) < S.E.Δ * ((x[m].time : Int) / S.E.Δ) + S.E.Δ := by linarith
  have hdvd : (S.E.Δ * ((x[m].time : Int) / S.E.Δ)) % S.E.Δ = 0 := Int.mul_emod_right _ _
  have hstart : slotStart S.E.Δ s = S.E.Δ * (slotStart S.E.Δ s / S.E.Δ) :=
    (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero (slotStart_emod_delta S s))).symm
  have hk : S.E.Δ * (slotStart S.E.Δ s / S.E.Δ) ≤ (x[m].time : Int) := by rw [← hstart]; exact hlo
  have hdiv : (slotStart S.E.Δ s / S.E.Δ) ≤ (x[m].time : Int) / S.E.Δ := by
    by_contra hcon
    have hlt2 : (x[m].time : Int) / S.E.Δ < slotStart S.E.Δ s / S.E.Δ := not_le.mp hcon
    have h1 : (x[m].time : Int) / S.E.Δ + 1 ≤ slotStart S.E.Δ s / S.E.Δ :=
      Int.add_one_le_iff.mpr hlt2
    have h2 : S.E.Δ * ((x[m].time : Int) / S.E.Δ + 1) ≤ S.E.Δ * (slotStart S.E.Δ s / S.E.Δ) :=
      Int.mul_le_mul_of_nonneg_left h1 (le_of_lt hΔpos)
    have h3 : S.E.Δ * ((x[m].time : Int) / S.E.Δ + 1)
        = S.E.Δ * ((x[m].time : Int) / S.E.Δ) + S.E.Δ := by ring
    linarith
  have hss : slotStart S.E.Δ s ≤ S.E.Δ * ((x[m].time : Int) / S.E.Δ) := by
    rw [hstart]
    exact Int.mul_le_mul_of_nonneg_left hdiv (le_of_lt hΔpos)
  obtain ⟨n_0, htick⟩ :=
    Restated.exists_tickStepAt facts x htd (lt_of_lt_of_le (slotStart_pos S hpos) hss)
  have haw : v ∈ Sched.awake (S.E.Δ * ((x[m].time : Int) / S.E.Δ)) :=
    mem_awake_of_awakeThroughout Sched hawv hss h0le
  obtain ⟨h1t, h0t⟩ := Restated.tickStepAt_time facts x htick
  have hnm : n_0 + 1 ≤ m := by
    by_contra hcon
    have hmn : m ≤ n_0 := by omega
    have hmt : (x[m].time : Int) ≤ (x[n_0].time : Int) := Restated.time_mono_int facts S Sched x hmn
    linarith
  have hclk := Restated.clock_ge_of_tickStepAt_awake_sts facts S Sched x htick
    (Finset.mem_sdiff.2 ⟨haw, hvh _ h0le⟩)
    (hneTick n_0 _ htick hdvd (Finset.mem_sdiff.2 ⟨haw, hvh _ h0le⟩) hss h0le) hnm
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- At the tick step of slot `s`'s confirmation instant, the late set of `v`'s store is its slot-`s`
    pool. -/
theorem confLate_eq_pool_at_confirmation (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {n : Nat} {s : Slot}
    (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s)) (v : V) :
    Restated.Vocabulary.Protocol.confLate M S.E (x[n][v].st).st.core s = (M.store_pool (x[n][v].st).st.core s) := by
  obtain ⟨h1t, h0t⟩ := Restated.tickStepAt_time facts x hn
  refine Finset.Subset.antisymm ?_ ?_
  · intro u hu
    rw [Restated.Vocabulary.Protocol.confLate, mem_beforeCutoff_iff] at hu
    exact hu.1
  · intro u hu
    have hslot : u.slot = s := Restated.slot_of_mem_pool_sts facts S Sched x n v hu
    have hpool : u ∈ (M.store_pool (x[n][v].st).st.core u.slot) := by rw [hslot]; exact hu
    obtain ⟨τ, hτ, hb⟩ := Restated.stamp_le_clock_gfVote facts S Sched x n v hpool
    rw [Restated.Vocabulary.Protocol.confLate, mem_beforeCutoff_iff]
    refine ⟨hu, stampedBefore_of_lt hτ ?_⟩
    refine lt_of_le_of_lt hb ?_
    refine WithBot.coe_lt_coe.mpr ?_
    have hct := Restated.clock_le_time_sts facts S Sched x n v
    linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `v` is awake from one delay before slot `s`'s start to its confirmation instant, honest
    through the tick step `n` there, and `u` is in an outcome of the votes its store counts at that
    confirmation, then `u` has slot `s`, and at some step `i` with `i + 1 ≤ n` `v` accepts `u`, `u`
    enters `v`'s pool, `u`'s signer is in slot `s`'s committee, and the time after step `i` is at or
    after the slot's start and strictly before three delays into the slot. The hypothesis `hneTick`
    says that `v`'s tick has an outcome at the tick steps it reads. -/
theorem accept_step_of_mem_confVotes (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x)
    {n : Nat} {s : Slot} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s))
    (hpos : 0 < s) {v : V}
    (hawv : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hvh : Restated.HonestThrough M Sched x n v)
    {votes : Finset (GoldfishVote V)}
    (hvotes : Restated.Vocabulary.Protocol.confVotes M S.E (x[n][v].st).st.core s ⇢ votes)
    {u : GoldfishVote V} (hu : u ∈ votes)
    (hneTick : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → v ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t x[n'] v) t ⇢ out) :
    u.slot = s ∧ ∃ i : Nat, i + 1 ≤ n ∧
      Restated.AcceptsAtStep M S x i v (NamedObject.gfVote u) ∧
      u ∉ (M.store_pool (x[i][v].st).st.core u.slot) ∧ u ∈ (M.store_pool (x[i + 1][v].st).st.core u.slot) ∧
      u.val_index ∈ S.E.committee u.slot ∧
      slotStart S.E.Δ s ≤ (x[i + 1].time : Int) ∧
      (x[i + 1].time : Int) < slotStart S.E.Δ s + 3 * S.E.Δ := by
  have hΔpos : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hconf : M.confirmation_time S.E s = slotStart S.E.Δ s + 6 * S.E.Δ :=
    (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s).symm
  have hsup : M.support_cutoff S.E s = slotStart S.E.Δ s + 2 * S.E.Δ := by
    obtain ⟨s', rfl⟩ : ∃ s' : Slot, s = s' + 1 :=
      ⟨Nat.pred s, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [← facts.sch.confirmation_time_eq_support_cutoff_succ,
      ← facts.sch.slotStart_add_six_delta_eq_confirmation_time, slotStart_succ]
    ring
  obtain ⟨h1t, h0t⟩ := Restated.tickStepAt_time facts x hn
  obtain ⟨e, he, rfl⟩ := returns_map_elim _ _ _ hvotes
  obtain ⟨tm, htm, rfl⟩ := returns_map_elim _ _ _ he
  have hearly := (mem_beforeCutoff_iff _ _ _ _).mp (Finset.mem_filter.mp hu).1
  have hpool : u ∈ (M.store_pool (x[n][v].st).st.core s) := hearly.1
  have hslot : u.slot = s := Restated.slot_of_mem_pool_sts facts S Sched x n v hpool
  have hpool' : u ∈ (M.store_pool (x[n][v].st).st.core u.slot) := by rw [hslot]; exact hpool
  obtain ⟨i, hin, hacc, h0, h1⟩ := Restated.accepts_of_mem_pool facts S Sched x hpool'
  obtain ⟨hstamp, hlo0, hcomm⟩ := Restated.stamp_eq_clock_of_flip_gfVote facts S Sched x h0 h1
  have hi1n : i + 1 ≤ n := hin
  have hstampn : (x[n][v].st).st.core.timestamp_vote u
      = some ((x[i + 1][v].st).st.core.t : Stamp) :=
    Restated.stamp_mono_sts facts S Sched x v hi1n hstamp
  obtain ⟨τ, hτ, hτlt⟩ :=
    exists_stamp_of_stampedBefore (facts.sto.stampedBefore_vote_of_tau _ tm htm hearly.2)
  have hτeq : τ = ((x[i + 1][v].st).st.core.t : Stamp) :=
    Option.some_inj.mp (hτ.symm.trans hstampn)
  have hclt : (x[i + 1][v].st).st.core.t < M.support_cutoff S.E s := by
    rw [hτeq] at hτlt
    exact WithBot.coe_lt_coe.mp hτlt
  have hlotime : slotStart S.E.Δ s ≤ (x[i + 1].time : Int) := by
    have hlt := Restated.slotStart_le_time_of_flip_gfVote facts S Sched x h0 h1
    rw [hslot] at hlt
    exact hlt
  have hi1conf : (x[i + 1].time : Int) ≤ M.confirmation_time S.E s := by
    have hmt : (x[i + 1].time : Int) ≤ (x[n].time : Int) := Restated.time_mono_int facts S Sched x hi1n
    linarith
  have hawv' : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (x[i + 1].time : Int) :=
    awakeThroughout_mono Sched hawv (by linarith) hi1conf
  have hslack : (x[i + 1].time : Int) < (x[i + 1][v].st).st.core.t + S.E.Δ :=
    Restated.clock_ge_delta_floor facts S Sched x htd hpos hlotime hawv'
      (fun t ht => hvh t (le_trans ht (Restated.time_mono_int facts S Sched x hi1n)))
      (fun n' t ht hΔ hq h1 h2 => hneTick n' t ht hΔ hq h1 (le_trans h2 hi1conf))
  refine ⟨hslot, i, hi1n, hacc, h0, h1, hcomm, hlotime, ?_⟩
  rw [hsup] at hclt
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `v` and `w` are honest through the tick step `n` at slot `s`'s confirmation instant and awake
    from one delay before the slot's start to that instant, and GST is at or before the slot's
    start, then every vote `u` in an outcome of the votes `v`'s store counts there is in `w`'s late
    set, or `w`'s late set already shows `u`'s signer equivocating. The hypotheses `hneTickv` and
    `hneTickw` say that the ticks of `v` and `w` the proof reads have an outcome. -/
theorem confVotes_transfer (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (hrelay : Restated.GfVoteRelayAtAccept M S x) (htd : Restated.TimeDiverges M x)
    {n : Nat} {s : Slot} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s))
    (hpos : 0 < s) (hgst : S.E.t_GST ≤ slotStart S.E.Δ s) {v w : V}
    (hvh : Restated.HonestThrough M Sched x n v)
    (hawv : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (haww : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hwh : Restated.HonestThrough M Sched x n w)
    {votes : Finset (GoldfishVote V)}
    (hvotes : Restated.Vocabulary.Protocol.confVotes M S.E (x[n][v].st).st.core s ⇢ votes)
    {u : GoldfishVote V} (hu : u ∈ votes)
    (hneTickv : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → v ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t x[n'] v) t ⇢ out)
    (hneTickw : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → w ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t x[n'] w) t ⇢ out) :
    u ∈ Restated.Vocabulary.Protocol.confLate M S.E (x[n][w].st).st.core s ∨
      M.equivocates (Restated.Vocabulary.Protocol.confLate M S.E (x[n][w].st).st.core s)
        u.val_index = true := by
  have hΔpos : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hconf : M.confirmation_time S.E s = slotStart S.E.Δ s + 6 * S.E.Δ :=
    (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s).symm
  obtain ⟨h1t, h0t⟩ := Restated.tickStepAt_time facts x hn
  obtain ⟨hslot, i, hi1n, -, h0, h1, hcomm, hlotime, htimebound⟩ :=
    Restated.accept_step_of_mem_confVotes facts S Sched x htd hn hpos hawv hvh hvotes hu
      hneTickv
  have hi1conf : (x[i + 1].time : Int) ≤ M.confirmation_time S.E s := by
    have hmt : (x[i + 1].time : Int) ≤ (x[n].time : Int) := Restated.time_mono_int facts S Sched x hi1n
    linarith
  have hdead : max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ
      ≤ slotStart S.E.Δ s + 4 * S.E.Δ - 1 := by
    have ha : (x[i + 1].time : Int) ≤ slotStart S.E.Δ s + 3 * S.E.Δ - 1 := by linarith
    have hb : S.E.t_GST ≤ slotStart S.E.Δ s + 3 * S.E.Δ - 1 := by linarith
    have hm := max_le ha hb
    linarith
  have hA : slotStart S.E.Δ s - S.E.Δ ≤ (x[i].time : Int) := by
    have hsucc := Restated.time_succ_le facts S Sched x i
    linarith
  have hB : (x[i].time : Int) ≤ M.confirmation_time S.E s :=
    le_trans (Restated.time_mono_int facts S Sched x (Nat.le_succ i)) hi1conf
  have hawi : AtomicAwake x i w := mem_awake_of_awakeThroughout Sched haww hA hB
  have hvhi : Restated.HonestThrough M Sched x i v := fun t ht =>
    hvh t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_of_succ_le hi1n)))
  have hawTw : w ∈ Sched.awakeThroughout (slotStart S.E.Δ u.slot - 1)
      (max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ) := by
    rw [hslot]
    refine awakeThroughout_mono Sched haww (by omega) ?_
    rw [hconf]; linarith
  have hhi : max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ ≤ slotStart S.E.Δ (u.slot + 2) := by
    rw [hslot]
    have hr : slotStart S.E.Δ (s + 2) = slotStart S.E.Δ s + 8 * S.E.Δ := by
      rw [show s + 2 = s + 1 + 1 from rfl, slotStart_succ, slotStart_succ]
      ring
    rw [hr]; linarith
  obtain ⟨k, hk0, hk1, hres⟩ :=
    Restated.gfVote_in_pool_of_accepts facts S Sched x hrelay htd h0 h1 hvhi hawi hcomm
      (by rw [hslot]; exact hpos) (by rw [hslot]; exact hlotime) hawTw
      (by rw [hslot]; exact hwh _ (by linarith)) hhi
      (by
        rw [hslot]
        exact fun n' ht => hneTickw n' _ ht (slotStart_emod_delta S s)
          (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched haww (by linarith)
            (by rw [hconf]; linarith), hwh _ (by linarith)⟩)
          le_rfl (by rw [hconf]; linarith))
      (fun k _ _ => facts.nd.process_nonempty (Setup.alwaysAwake S) (x[k][w].st)
        (NamedObject.gfVote u) (fun _ h => by cases h))
  have hkn : k + 1 ≤ n := by
    have hxk : (x[k].time : Int) < (x[n].time : Int) := by
      rw [hconf] at h0t
      linarith
    by_contra hcon
    have hnk : n ≤ k := by omega
    have hmt := Restated.time_mono_int facts S Sched x hnk
    linarith
  rcases hres with ⟨hmem, -⟩ | heq
  · left
    have hpooln : u ∈ (M.store_pool (x[n][w].st).st.core u.slot) :=
      Restated.mem_pool_mono_sts facts S Sched x w hkn hmem
    rw [Restated.confLate_eq_pool_at_confirmation facts S Sched x hn w, ← hslot]
    exact hpooln
  · right
    have hsub : (M.store_pool (x[k][w].st).st.core u.slot)
        ⊆ Restated.Vocabulary.Protocol.confLate M S.E (x[n][w].st).st.core s := by
      rw [Restated.confLate_eq_pool_at_confirmation facts S Sched x hn w, ← hslot]
      intro z hz
      have hzs : z.slot = u.slot := Restated.slot_of_mem_pool_sts facts S Sched x k w hz
      have hz' : z ∈ (M.store_pool (x[k][w].st).st.core z.slot) := by rw [hzs]; exact hz
      have hzn : z ∈ (M.store_pool (x[n][w].st).st.core z.slot) :=
        Restated.mem_pool_mono_sts facts S Sched x w (Nat.le_of_succ_le hkn) hz'
      rw [← hzs]; exact hzn
    exact facts.sch.equivocates_mono_of_subset hsub heq

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If two validators honest through step `n` each resolve the root `r` in their own tree, they
    resolve it to the same block. -/
theorem find?_eq_of_bodies (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {n : Nat} {v w : V} (hv : Restated.HonestThrough M Sched x n v) (hw : Restated.HonestThrough M Sched x n w)
    {r : BlockId} {B C : Block V}
    (hB : Block.find? (x[n][v].st).st.core.T r = some B)
    (hC : Block.find? (x[n][w].st).st.core.T r = some C) : B = C := by
  have htv : (x[n][v].st).st.core.T = (x[n][v].st).st.bodies.image NamedBlock.erase :=
    (Restated.nodeInvariant_sts facts S Sched x n v).1.1.1.1
  have htw : (x[n][w].st).st.core.T = (x[n][w].st).st.bodies.image NamedBlock.erase :=
    (Restated.nodeInvariant_sts facts S Sched x n w).1.1.1.1
  have hBmem : B ∈ (x[n][v].st).st.core.T := Proofs.HealingLemmas.find?_mem hB
  have hCmem : C ∈ (x[n][w].st).st.core.T := Proofs.HealingLemmas.find?_mem hC
  rw [htv, Finset.mem_image] at hBmem
  obtain ⟨D, hDmem, hDer⟩ := hBmem
  rw [htw, Finset.mem_image] at hCmem
  obtain ⟨D', hD'mem, hD'er⟩ := hCmem
  have hBlog : Restated.blockInLog M S Sched x D := Restated.blockInLog_of_mem_bodies facts S Sched hv hDmem
  have hClog : Restated.blockInLog M S Sched x D' := Restated.blockInLog_of_mem_bodies facts S Sched hw hD'mem
  have hinj := Restated.rootInjectiveOnAncestors_of_collisionFreeInLog facts S Sched x hexec.idealization
    D D' hBlog hClog
  refine RootInjectiveOnAncestors.eq_of_root_eq hinj (A := B) (C := C) ?_ ?_ ?_
  · rw [hDer]; exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self B)
  · rw [hD'er]; exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self C)
  · rw [Proofs.HealingLemmas.find?_root hB, Proofs.HealingLemmas.find?_root hC]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under the hypotheses of `confVotes_transfer`, an outcome `votes` of the votes `v`'s store counts
    at slot `s`'s confirmation and `w`'s late set satisfy `CrossView`: every counted vote reaches
    `w`'s late set or shows `w` an equivocation, and the two trees resolve a counted vote's head to
    the same block. -/
theorem crossView_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hrelay : Restated.GfVoteRelayAtAccept M S x) (htd : Restated.TimeDiverges M x)
    {n : Nat} {s : Slot} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s))
    (hpos : 0 < s) (hgst : S.E.t_GST ≤ slotStart S.E.Δ s) {v w : V}
    (hv : Restated.HonestThrough M Sched x n v) (hw : Restated.HonestThrough M Sched x n w)
    (hawv : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (haww : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    {votes : Finset (GoldfishVote V)}
    (hvotes : Restated.Vocabulary.Protocol.confVotes M S.E (x[n][v].st).st.core s ⇢ votes)
    (hneTickv : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → v ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t x[n'] v) t ⇢ out)
    (hneTickw : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → w ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t x[n'] w) t ⇢ out) :
    Restated.Vocabulary.Protocol.CrossView M (x[n][v].st).st.core.T (x[n][w].st).st.core.T
      votes
      (Restated.Vocabulary.Protocol.confLate M S.E (x[n][w].st).st.core s) where
  transfer := fun _ hu =>
    Restated.confVotes_transfer facts S Sched x hrelay htd hn hpos hgst hv hawv haww hw
      hvotes hu hneTickv hneTickw
  resolve := fun _ _ _ _ hB hC => Restated.find?_eq_of_bodies facts S Sched x hexec hv hw hB hC

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `v` and `w` are honest through the tick step at slot `s`'s confirmation instant and awake
    from one delay before the slot's start to that instant, GST is at or before the slot's start,
    and an outcome of each store's confirmation test passes `B` and `C` respectively, then `B` and
    `C` lie on one chain. The hypotheses `hneTickv` and `hneTickw` say that the ticks the proof
    reads have an outcome. -/
theorem confirmed_compatible_sts_of_gfVoteRelay (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hrelay : Restated.GfVoteRelayAtAccept M S x) (htd : Restated.TimeDiverges M x)
    {n : Nat} {s : Slot} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s))
    (hpos : 0 < s) (hgst : S.E.t_GST ≤ slotStart S.E.Δ s) {v w : V}
    (hv : Restated.HonestThrough M Sched x n v) (hw : Restated.HonestThrough M Sched x n w)
    (hawv : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (haww : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    {B C : Block V}
    {elv elw : Block V → Bool}
    (helv : Restated.Vocabulary.Protocol.confEligible M S.E (x[n][v].st).st.core s ⇢ elv)
    (hB : elv B = true)
    (helw : Restated.Vocabulary.Protocol.confEligible M S.E (x[n][w].st).st.core s ⇢ elw)
    (hC : elw C = true)
    (hneTickv : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → v ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t x[n'] v) t ⇢ out)
    (hneTickw : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → w ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t x[n'] w) t ⇢ out) :
    Block.compatible B C = true := by
  obtain ⟨votesv, hvv, hrv⟩ := returns_bind_elim _ _ _ helv
  obtain ⟨scv, hscv, hpv⟩ := returns_bind_elim _ _ _ hrv
  have hscv' := returns_lift_elim _ _ hscv
  rw [Record.returns_pure] at hpv
  subst hpv
  obtain ⟨votesw, hvw', hrw⟩ := returns_bind_elim _ _ _ helw
  obtain ⟨scw, hscw, hpw⟩ := returns_bind_elim _ _ _ hrw
  have hscw' := returns_lift_elim _ _ hscw
  rw [Record.returns_pure] at hpw
  subst hpw
  simp only [Restated.Vocabulary.Protocol.confCount, decide_eq_true_eq] at hB hC
  have hel : ∀ (st : M.S) (tm : TimestampMap (GoldfishVote V)), st.tau ⇢ tm →
      ∀ u ∈ beforeCutoff tm (M.support_cutoff S.E s) (M.store_pool st s),
        u ∈ Restated.Vocabulary.Protocol.confLate M S.E st s := by
    intro st tm htm u hu
    have h := (mem_beforeCutoff_iff _ _ _ _).mp hu
    refine (mem_beforeCutoff_iff _ _ _ _).mpr ⟨h.1, ?_⟩
    obtain ⟨σ, hσ, hlt⟩ :=
      exists_stamp_of_stampedBefore (facts.sto.stampedBefore_vote_of_tau st tm htm h.2)
    exact stampedBefore_of_lt hσ (lt_of_lt_of_le hlt
      (WithBot.coe_le_coe.mpr (facts.sch.Protocol_support_cutoff_le_confirmation_time S.E s)))
  have hvw := Restated.crossView_sts facts S Sched x hexec hrelay htd hn hpos hgst hv hw hawv
    haww hvv hneTickv hneTickw
  have hwv := Restated.crossView_sts facts S Sched x hexec hrelay htd hn hpos hgst hw hv haww
    hawv hvw' hneTickw hneTickv
  obtain ⟨ev, hev, rfl⟩ := returns_map_elim _ _ _ hvv
  obtain ⟨tmv, htmv, rfl⟩ := returns_map_elim _ _ _ hev
  obtain ⟨ew, hew, rfl⟩ := returns_map_elim _ _ _ hvw'
  obtain ⟨tmw, htmw, rfl⟩ := returns_map_elim _ _ _ hew
  exact facts.fc.eligible_compatible
    (fun u hu => hel _ tmv htmv u hu) rfl (fun u hu => hel _ tmw htmw u hu) rfl
    hvw.transfer hvw.resolve hwv.transfer hwv.resolve
    _ (hscv' B) hB _ (hscw' C) hC

end

end DecoupledConsensusModel.Sts.Restated
