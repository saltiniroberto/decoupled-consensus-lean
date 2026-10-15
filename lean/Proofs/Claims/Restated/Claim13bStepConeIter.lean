import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitTick
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bStepConeIter

/-!
# The confirmed block a round's action reads

The store a round's action read produces, the fields it keeps from the reader's store, and the
theorem that its confirmed block lies on one chain with the previous round's anchor, stated over a
model `M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-! ## Helpers on outcome sets -/

section
open DecoupledConsensusModel.Execution

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro_iter {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_iter {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
    (m >>= k) ⇢ b ↔ ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns
  simp only [ExceptT.run_bind, Set.bind_def]
  constructor
  · intro h
    obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.mp h
    cases e with
    | ok a => exact ⟨a, he, hb⟩
    | error err => simp at hb
  · rintro ⟨a, ha, hb⟩
    exact Set.mem_iUnion₂.mpr ⟨_, ha, hb⟩

/-- `gfHeadWith` has an outcome at every store. -/
private theorem gfHeadWith_nonempty_iter (facts : Record.Facts M) (contract : M.Contract)
    (E : Env V) (hc : Protocol.HealConfig) (st : M.S) :
    ∃ H, Restated.gfHeadWith M contract E hc st ⇢ H := by
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty E st st.s
  obtain ⟨W, hW⟩ := facts.fc.voter_view_nonempty E (M.toHealing st).toFG.toSG.toGoldfishStore st.s
  obtain ⟨U, hU⟩ :=
    facts.fc.voter_support_view_nonempty E (M.toHealing st).toFG.toSG.toGoldfishStore st.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_in_tree_with_layer_nonempty contract E hc (M.toHealing st)
    T W U (st.s - 1)
  refine ⟨H, ?_⟩
  unfold Restated.gfHeadWith
  exact (returns_bind_iff_iter _ _ _).2 ⟨T, hT, (returns_bind_iff_iter _ _ _).2
    ⟨W, hW, (returns_bind_iff_iter _ _ _).2 ⟨U, hU,
      (facts.hd.get_head_in_tree_with_eq_layer _ _ _ _ _ _ _ _ _).2 hH⟩⟩⟩

/-- `gfHeadFrom` at slot `s` has an outcome from every node state. -/
private theorem gfHeadFrom_nonempty_iter (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (s : Slot) : ∃ H, Restated.gfHeadFrom M S before s ⇢ H := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (M.vote_time S.E s) before.cache
  have hn : Restated.voteReadOf M S before s ⇢
      M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c :=
    returns_map_intro_iter _ _ _ hc
  obtain ⟨H, hH⟩ := gfHeadWith_nonempty_iter facts (M.gradeContract
    (M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c).cache) S.E S.hc
    (M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c).st.core
  refine ⟨H, ?_⟩
  unfold Restated.gfHeadFrom
  exact (returns_bind_iff_iter _ _ _).2 ⟨_, hn, hH⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A round's action instant is the confirmation instant of the round's opening slot. -/
theorem confirmation_time_opening_slot (facts : Record.Facts M) (S : Setup V) (r : Round) :
    M.confirmation_time S.E ((M.opening_slot S.hc r)) = (Restated.Vocabulary.Execution.Setup.a M S r) := by
  rw [Restated.action_eq_support_cutoff facts S r, facts.sch.confirmation_time_eq_support_cutoff_succ]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- One slot before the slot that round `r`'s action instant falls in is the round's opening slot. -/
theorem slotOf_a_sub_one (facts : Record.Facts M) (S : Setup V) (r : Round) :
    S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S r)) - 1 = (M.opening_slot S.hc r) := by
  have h : S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S r)) = (M.opening_slot S.hc r) + 1 := by
    rw [← Restated.confirmation_time_opening_slot facts S r]
    exact facts.sch.Optimistic_slotOf_confirmation_time S.E ((M.opening_slot S.hc r))
  rw [h, Nat.add_sub_cancel]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If every head each member of `HonSlot S Sched s` can select at slot `s` is a descendant of `B`
    (`hprev`), those heads resolve in `v`'s tree (`hres`), that tree idealizes roots (`hid`), and
    each such head is the erasure of a named block in the sent log (`hinlog`), then for every such
    head `G` there is a block `X` with `G`'s root, a descendant of `B` of slot at most `s`,
    resolving in `v`'s tree at step `mr` and stamped there before slot `s`'s support cutoff. -/
theorem coneHeads_of_headsBelow (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {B : Block V} {s : Slot} {v : V} {m mr : Nat}
    (hprev : Restated.HeadsBelow M S Sched x B s) (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    (hres : Restated.HeadsResolve M S Sched x v m mr s) (hid : Restated.TreeIdealizes M S Sched x v mr B)
    (hinlog : ∀ v' ∈ Restated.HonSlot M S Sched s, ∀ G : Block V,
      Restated.gfHeadFrom M S (x[m][v'].st) s ⇢ G →
      ∃ H : NamedBlock V, Restated.blockInLog M S Sched x H ∧ H.erase = G) :
    ∀ v' ∈ Restated.HonSlot M S Sched s, ∀ G : Block V,
      Restated.gfHeadFrom M S (x[m][v'].st) s ⇢ G → ∃ X : Block V,
      X.root = G.root ∧ Block.Preceq B X ∧ X.slot ≤ s ∧
        Block.find? (x[mr][v].st).st.core.T X.root = some X ∧
        ∃ σ : Stamp, (x[mr][v].st).st.core.timestamp_block X = some σ ∧
          σ < ((M.support_cutoff S.E s : Int) : Stamp) := by
  intro v' hv' G hG
  obtain ⟨X, hXroot, hXs, hfind, σ, hσ, hσlt⟩ := hres v' hv' G hG
  obtain ⟨H, hH, hHe⟩ := hinlog v' hv' G hG
  have hHroot : H.erase.root = H.root := Proofs.NamedWire.erase_root H
  refine ⟨X, hXroot, hid X H hfind hH ?_ ?_, hXs, hfind, σ, hσ, hσlt⟩
  · rw [hXroot, ← hHe]; exact hHroot
  · rw [hHe]; exact hprev v' m hv' hm G hG

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every healing store round `r`'s action can read from `before` is the healing view of a store
    `st` with an outcome `c` of the phase tick at the action instant written in, where `st`'s core
    store is an outcome of the confirmation update of slot `S.E.slotOf (S.a r) - 1`, run under `c`'s
    grade contract on `before`'s store with its clock set to the action instant. -/
theorem actionHealingStore_eq (facts : Record.Facts M) (S : Setup V) (before : M.N) (r : Round) :
    ∀ hs ∈ Restated.actionHealingStore M S before r,
      ∃ c, M.onPhaseTick S.E S.hc (M.toHealing before.st.core)
          ((Restated.Vocabulary.Execution.Setup.a M S r)) before.cache ⇢ c ∧
        ∃ X, M.update_confirmation_with (M.gradeContract c)
            S.E S.hc (M.ns_setClock S.E before.st ((Restated.Vocabulary.Execution.Setup.a M S r))).core
            (S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S r)) - 1) ⇢ X ∧
          ∃ st : M.NS, st.core = X ∧ hs = M.toHealing (M.store_with_cache st c).core := by
  rintro hs ⟨nd, ⟨c, hc, D, hD, rfl⟩, rfl⟩
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st ((Restated.Vocabulary.Execution.Setup.a M S r))).core
    (S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S r)) - 1)
  refine ⟨c, hc, X, hX, D, facts.dt.named_update_confirmation_with_core _ _ _ _ _ D hD X hX, ?_⟩
  show M.toHealing (M.mkNode D before.record c).st.core = _
  rw [facts.nd.mkNode_st]

/-- If `st`'s core store is `X`, the healing view of `st` with the cache `c` written in has the
    finalized block, justified block, justified height, running height maximum, live confirmed
    block, tree, slot and chain-state map of the healing view of `X`. -/
theorem HS_fields_store_with_cache (facts : Record.Facts M) {st : M.NS} {X : M.S} (c : M.Cache)
    (h : st.core = X) :
    (M.toHealing (M.store_with_cache st c).core).F = (M.toHealing X).F ∧
    (M.toHealing (M.store_with_cache st c).core).J = (M.toHealing X).J ∧
    (M.toHealing (M.store_with_cache st c).core).h_j = (M.toHealing X).h_j ∧
    (M.toHealing (M.store_with_cache st c).core).h_max = (M.toHealing X).h_max ∧
    (M.toHealing (M.store_with_cache st c).core).live_confirmed = (M.toHealing X).live_confirmed ∧
    (M.toHealing (M.store_with_cache st c).core).T = (M.toHealing X).T ∧
    (M.toHealing (M.store_with_cache st c).core).s = (M.toHealing X).s ∧
    (M.toHealing (M.store_with_cache st c).core).σ = (M.toHealing X).σ := by
  subst h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Record.Model.HS.F, facts.sto.Sts_toHealing_F, facts.nd.store_with_cache_core_F]
  · simp only [Record.Model.HS.J, facts.sto.Sts_toHealing_J, facts.nd.store_with_cache_core_J]
  · simp only [Record.Model.HS.h_j, facts.sto.toHealing_h_j, facts.nd.store_with_cache_core_h_j]
  · simp only [Record.Model.HS.h_max, facts.sto.Sts_toHealing_h_max,
      facts.nd.store_with_cache_core_h_max]
  · simp only [Record.Model.HS.live_confirmed, facts.sto.toHealing_live_confirmed,
      facts.nd.store_with_cache_core_live_confirmed]
  · simp only [Record.Model.HS.T, facts.sto.toHealing_gs_T, facts.nd.store_with_cache_core_T]
  · simp only [Record.Model.HS.s, facts.sto.toHealing_gs_s, facts.nd.store_with_cache_core_s]
  · simp only [Record.Model.HS.σ, facts.sto.Sts_toHealing_σ, facts.nd.store_with_cache_core_σ]
end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every store round `r₁`'s action can read from `before` has the running height maximum of
    `before`'s store. -/
theorem actionHealingStore_h_max (facts : Record.Facts M) (S : Setup V) (before : M.N) (r₁ : Round) :
    ∀ hs ∈ Restated.actionHealingStore M S before r₁, hs.h_max = before.st.core.h_max := by
  intro hs hhs
  obtain ⟨c, hc, X, hX, st₀, hst₀, rfl⟩ := Restated.actionHealingStore_eq facts S before r₁ hs hhs
  obtain ⟨hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀⟩ :=
    Restated.HS_fields_store_with_cache facts c hst₀
  simp only [hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀] at *
  rw [Record.Model.HS.h_max, facts.dt.update_confirmation_with_toHealing_h_max _ _ _ _ _ X hX,
    facts.hd.setClock_toHealing_h_max]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every store round `r₁`'s action can read from `before` has the justified height of `before`'s
    store. -/
theorem actionHealingStore_h_j (facts : Record.Facts M) (S : Setup V) (before : M.N) (r₁ : Round) :
    ∀ hs ∈ Restated.actionHealingStore M S before r₁, hs.h_j = before.st.core.h_j := by
  intro hs hhs
  obtain ⟨c, hc, X, hX, st₀, hst₀, rfl⟩ := Restated.actionHealingStore_eq facts S before r₁ hs hhs
  obtain ⟨hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀⟩ :=
    Restated.HS_fields_store_with_cache facts c hst₀
  simp only [hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀] at *
  rw [Record.Model.HS.h_j, facts.dt.update_confirmation_with_toHealing_h_j _ _ _ _ _ X hX,
    facts.hd.setClock_toHealing_h_j]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- When round `r`'s action instant is slot `s`'s confirmation instant and step `n` is the tick
    there, at which `v` is awake and not held by the adversary, every store round `r`'s action can
    read from `v`'s node state at step `n` has as its `live_confirmed` the `live_confirmed` of `v`'s
    store right after step `n`. The hypothesis `hneTickConf` says that `v`'s tick at step `n` has an
    outcome, and `hrun` that the node state it reads passes the grade-2 awake test of slot `s + 1`'s
    round. -/
theorem actionHealingStore_live_confirmed (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {s : Slot} {r : Round} {n : Nat} {v : V}
    (hr : M.confirmation_time S.E s = (Restated.Vocabulary.Execution.Setup.a M S r))
    (hslot : S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S r)) - 1 = s)
    (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s))
    (haw : v ∈ Sched.awake (M.confirmation_time S.E s) \
      Sched.adv (M.confirmation_time S.E s))
    (hneTickConf : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] v) (M.confirmation_time S.E s) ⇢ out)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] v) (M.round_of S.hc (s + 1))) :
    ∀ hs ∈ Restated.actionHealingStore M S (x[n][v].st) r,
      hs.live_confirmed = (x[n + 1][v].st).st.core.live_confirmed := by
  have _hr_0 : M.reachedNode (x[n][v].st) := Record.reachedNode_sts facts S Sched x n v
  have _hr_1 : M.reachedNode (Record.wakeStage M Sched (M.support_cutoff S.E (s + 1)) x[n] v) := Record.reachedNode_wakeStage facts S Sched x n v (M.support_cutoff S.E (s + 1))
  rintro hs ⟨nd, ⟨c, hc, D, hD, rfl⟩, rfl⟩
  obtain ⟨t', hlbl, ht'⟩ := id hn
  have hct := facts.sch.confirmation_time_eq_support_cutoff_succ S.E s
  have hdvd : (t' : Int) % S.E.Δ = 0 := by
    rw [ht', hct]
    exact facts.sch.support_cutoff_emod_delta S (s + 1)
  have haw' : v ∈ Sched.awake (t' : Int) \ Sched.adv (t' : Int) := by rw [ht']; exact haw
  rcases Restated.st_succ_of_tick_awake facts S Sched x v hlbl haw' hdvd with
    ⟨out₁, hout, hst⟩ | ⟨hno, -⟩
  · rw [hst]
    rw [ht', hct] at hout
    have hc' : M.onPhaseTick S.E S.hc (x[n][v].st).st.core.toHealing (M.support_cutoff S.E (s + 1))
        (x[n][v].st).cache ⇢ c := by
      rw [← hct, hr]; exact hc
    have hD' : M.duties_update_confirmation_with (M.gradeContract c) S.E S.hc
        (M.ns_setClock S.E (x[n][v].st).st (M.support_cutoff S.E (s + 1))) (s + 1 - 1) ⇢ D := by
      rw [Nat.add_sub_cancel, ← hct, hr, ← hslot]; exact hD
    rw [facts.nd.on_tick_emit_confirmation_of_outcomes (Setup.alwaysAwake S) v
        (Record.wakeStage M Sched (M.support_cutoff S.E (s + 1)) x[n] v)
        (s + 1) (Nat.succ_pos s) out₁ hout c
        (by rw [Record.wakeStage_st facts, Record.wakeStage_cache facts]; exact hc') D
        (by rw [Record.wakeStage_st facts]; exact hD') (by rw [← hct]; exact hrun)]
    show (M.toHealing (M.mkNode D (x[n][v].st).record c).st.core).live_confirmed = _
    rewrite [Record.Model.HS.live_confirmed, facts.sto.toHealing_live_confirmed, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; try (with_reducible rfl)
  · obtain ⟨o, ho⟩ := hneTickConf
    rw [← ht'] at ho
    exact absurd ho (hno o)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every store `hs` round `r + 1`'s action can read from `v`'s node state at step `n`, if
    `hs`'s finalized block is an ancestor of `T`'s block and, when `hs`'s running height maximum is
    its justified height plus one, `hs`'s justified block lies on one chain with it, then `hs`'s
    confirmed block lies on one chain with `T`'s block. The hypotheses `hneTickVote`, `hneTick` and
    `hneTickConf` say that the ticks the proof reads have an outcome, and `hrun` that `v`'s tick at
    step `n` passes the grade-2 awake test. -/
theorem live_confirmed_compatible_at_action (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {v : V} {T : NamedBlock V}
    (hanchor : tE ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1)) + 1))
    (hgst : S.E.t_GST ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))))
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hawTc : v ∈ Sched.awakeThroughout (slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))))
      (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) v)
    (hprev : Restated.HeadsBelow M S Sched x T.erase ((M.opening_slot S.hc (r + 1))))
    (hres : ∀ m : Nat, Restated.tickStepAt M x m (M.vote_time S.E ((M.opening_slot S.hc (r + 1)))) →
      Restated.HeadsResolve M S Sched x v m n ((M.opening_slot S.hc (r + 1))))
    (hid : Restated.TreeIdealizes M S Sched x v n T.erase)
    (hinlog : ∀ m : Nat, Restated.tickStepAt M x m (M.vote_time S.E ((M.opening_slot S.hc (r + 1)))) →
      ∀ v' ∈ Restated.HonSlot M S Sched ((M.opening_slot S.hc (r + 1))), ∀ G : Block V,
        Restated.gfHeadFrom M S (x[m][v'].st) ((M.opening_slot S.hc (r + 1))) ⇢ G →
        ∃ H : NamedBlock V, Restated.blockInLog M S Sched x H ∧ H.erase = G)
    (hvalid : Protocol.VoteSetValid S.E ((M.opening_slot S.hc (r + 1)))
      (Restated.Vocabulary.Protocol.confLate M S.E (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1))))
        ((M.opening_slot S.hc (r + 1)))))
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n][v].st).st.core)
      (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) (x[n][v].st).cache ⇢ c)
    (A : Block V) (hA : Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
      (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1)))) ⇢ A)
    (hAB : Block.Preceq A T.erase)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C T.erase →
      C ∈ Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1)))))
    (hs : M.HS) (hhs : hs ∈ Restated.actionHealingStore M S (x[n][v].st) (r + 1))
    (hF : Block.Preceq hs.F T.erase)
    (hJ : hs.h_max = hs.h_j + 1 → Block.compatible hs.J T.erase = true)
    (hneTickVote : ∀ m : Nat, Restated.tickStepAt M x m (M.vote_time S.E ((M.opening_slot S.hc (r + 1)))) →
      ∀ q ∈ Restated.HonSlot M S Sched ((M.opening_slot S.hc (r + 1))), ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E ((M.opening_slot S.hc (r + 1)))) x[m] q) (M.vote_time S.E ((M.opening_slot S.hc (r + 1)))) ⇢ out)
    (hneTick : ∀ n' : Nat, Restated.tickStepAt M x n' (slotStart S.E.Δ ((M.opening_slot S.hc (r + 1)))) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (slotStart S.E.Δ ((M.opening_slot S.hc (r + 1)))) x[n'] v) (slotStart S.E.Δ ((M.opening_slot S.hc (r + 1)))) ⇢ out)
    (hneTickConf : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) x[n] v) (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) ⇢ out)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E (M.opening_slot S.hc (r + 1))) x[n] v)
      (M.round_of S.hc (M.opening_slot S.hc (r + 1) + 1))) :
    Block.compatible hs.live_confirmed T.erase = true := by
  have hct : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    Restated.confirmation_time_opening_slot facts S (r + 1)
  have hn' : Restated.tickStepAt M x n (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) := by
    rw [hct]; exact hn
  have hd := S.E.Δ_pos
  have haw : v ∈ Sched.awake (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) :=
    mem_awake_of_awakeThroughout Sched hawTc
      (by
        rw [← facts.sch.slotStart_add_six_delta_eq_confirmation_time]
        linarith)
      (le_refl _)
  have hbridge : hs.live_confirmed = (x[n + 1][v].st).st.core.live_confirmed :=
    Restated.actionHealingStore_live_confirmed facts S Sched x hct
      (Restated.slotOf_a_sub_one facts S (r + 1)) hn'
      (Finset.mem_sdiff.2 ⟨haw, hvh _ (le_refl _)⟩) hneTickConf hrun hs hhs
  have hsopen : 0 < (M.opening_slot S.hc (r + 1)) := facts.gr.opening_slot_pos S (Nat.succ_pos r)
  obtain ⟨m, hm⟩ := Restated.exists_tickStepAt facts x htd
    (facts.sch.vote_time_pos S hsopen)
  have hcone := Restated.coneHeads_of_headsBelow facts S Sched x hprev hm (hres m hm) hid
    (hinlog m hm)
  have hcases := Restated.live_confirmed_cases_of_cone facts S Sched x hexec hsync htd hmono
    hcs hsopen hanchor hgst hm hn' hawTc hvh
    (fun q hq => by
      obtain ⟨H, hH⟩ := gfHeadFrom_nonempty_iter facts S (x[m][q].st) (M.opening_slot S.hc (r + 1))
      exact ⟨H, hH, hcone q hq H hH⟩)
    hvalid c hc A hA hAB hpath (hneTickVote m hm) hneTick hneTickConf hrun
  rw [hbridge]
  rcases hcases with hpre | heq
  · exact Block.compatible_of_preceq_common (Block.preceq_self _)
      (preceq_eq_true_iff_Preceq.mpr hpre)
  · rw [heq]
    obtain ⟨c', hc', X, hX, st₀, hst₀, rfl⟩ := Restated.actionHealingStore_eq facts S (x[n][v].st) (r + 1) hs hhs
    obtain ⟨hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀⟩ :=
      Restated.HS_fields_store_with_cache facts c' hst₀
    simp only [hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀] at *
    rw [Record.Model.HS.F, facts.hd.update_confirmation_with_toHealing_F _ _ _ _ _ X hX,
      facts.hd.setClock_toHealing_F] at hF
    rw [Record.Model.HS.h_max, Record.Model.HS.h_j, Record.Model.HS.J,
      facts.dt.update_confirmation_with_toHealing_h_max _ _ _ _ _ X hX,
      facts.dt.update_confirmation_with_toHealing_h_j _ _ _ _ _ X hX,
      facts.dt.update_confirmation_with_toHealing_J _ _ _ _ _ X hX,
      facts.hd.setClock_toHealing_h_max, facts.hd.setClock_toHealing_h_j,
      facts.hd.setClock_toHealing_J] at hJ
    have hF' : Block.Preceq
        (M.toHealing (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1))))).F T.erase := by
      rw [Restated.confStoreAt, Record.Model.HS.F, facts.hd.setClock_toHealing_F]
      exact hF
    have hJ' : (M.toHealing (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1))))).h_max
        = (M.toHealing (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1))))).h_j + 1 →
        Block.compatible
        (M.toHealing (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1))))).J T.erase
        = true := by
      rw [Restated.confStoreAt, Record.Model.HS.h_max, Record.Model.HS.h_j, Record.Model.HS.J,
        facts.hd.setClock_toHealing_h_max, facts.hd.setClock_toHealing_h_j, facts.hd.setClock_toHealing_J]
      exact hJ
    exact facts.fc.fgRoot_compatible_ofJustifiedBranch hF' hJ'

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- On an execution whose time diverges, some step is the tick at round `r + 1`'s action instant. -/
theorem tick_field_at_succ (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) (r : Round) :
    ∃ n : Nat, Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) :=
  Restated.exists_tickStepAt facts x htd (Restated.action_pos facts S (r + 1))

end

end DecoupledConsensusModel.Sts.Restated
