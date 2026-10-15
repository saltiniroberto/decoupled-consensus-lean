import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13b
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13bSyncView
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.VocabularyAssumptionsLemmas
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Alignment
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepCone
import Model.Conditions.ProcessedFlip
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bStepCone
import Proofs.Claims.Restated.WakeWindow

/-!
# The Goldfish votes of a slot and the cone of support

Facts about the Goldfish votes honest committee members send and receivers hold: their shape, their
uniqueness under an honest name, their arrival in a receiver's pool before the slot's support
cutoff, and the cone of support they give a block, so that the next slot's vote duty selects a
descendant of it. Stated over a model `M : Record.Model V` and its facts `facts : Record.Facts M`.
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
/-- An outcome of `f <$> m` is `f a` for an outcome `a` of `m`. -/
private theorem returns_map_elim_cone {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro_cone {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_cone {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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

/-- Every outcome of `voteReadOf` at slot `s` is `before`'s store with its clock set to slot `s`'s
    vote instant, `before`'s signing record, and an outcome of the phase tick at that instant on
    `before`'s cache. -/
private theorem voteReadOf_cases (S : Setup V) (before : M.N) (s : Slot) {n : M.N}
    (hn : Restated.voteReadOf M S before s ⇢ n) :
    ∃ c : M.Cache, M.onPhaseTick S.E S.hc before.st.core.toHealing (M.vote_time S.E s)
        before.cache ⇢ c ∧
      n = M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c := by
  obtain ⟨c, hc, hcn⟩ := returns_map_elim_cone _ _ _ hn
  exact ⟨c, hc, hcn.symm⟩

/-- Every outcome of `gfHeadWith` at `st` is an outcome of `M.get_head_in_tree_with` over outcomes
    of `st`'s voter tree and its two voter views. -/
private theorem gfHeadWith_cases (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (st : M.S) {H : Block V} (hH : Restated.gfHeadWith M contract E hc st ⇢ H) :
    ∃ T, Restated.voteTreeOf M E st ⇢ T ∧ ∃ W, Restated.voteViewOf M E st ⇢ W ∧
      ∃ U, Restated.voteSupportViewOf M E st ⇢ U ∧
        M.get_head_in_tree_with contract E hc st T W U (st.s - 1) ⇢ H := by
  unfold Restated.gfHeadWith at hH
  obtain ⟨T, hT, hH⟩ := (returns_bind_iff_cone _ _ _).1 hH
  obtain ⟨W, hW, hH⟩ := (returns_bind_iff_cone _ _ _).1 hH
  obtain ⟨U, hU, hH⟩ := (returns_bind_iff_cone _ _ _).1 hH
  exact ⟨T, hT, W, hW, U, hU, hH⟩

/-- An outcome of `M.get_head_in_tree_with` over outcomes of `st`'s voter tree and voter views is an
    outcome of `gfHeadWith` at `st`. -/
private theorem gfHeadWith_intro (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (st : M.S) {T : Finset (Block V)} (hT : Restated.voteTreeOf M E st ⇢ T)
    {W : Finset (GoldfishVote V)} (hW : Restated.voteViewOf M E st ⇢ W)
    {U : Finset (GoldfishVote V)} (hU : Restated.voteSupportViewOf M E st ⇢ U) {H : Block V}
    (hH : M.get_head_in_tree_with contract E hc st T W U (st.s - 1) ⇢ H) :
    Restated.gfHeadWith M contract E hc st ⇢ H := by
  unfold Restated.gfHeadWith
  exact (returns_bind_iff_cone _ _ _).2 ⟨T, hT, (returns_bind_iff_cone _ _ _).2
    ⟨W, hW, (returns_bind_iff_cone _ _ _).2 ⟨U, hU, hH⟩⟩⟩

/-- `gfHeadWith` has an outcome at every store. -/
private theorem gfHeadWith_nonempty (facts : Record.Facts M) (contract : M.Contract) (E : Env V)
    (hc : Protocol.HealConfig) (st : M.S) : ∃ H, Restated.gfHeadWith M contract E hc st ⇢ H := by
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty E st st.s
  obtain ⟨W, hW⟩ := facts.fc.voter_view_nonempty E (M.toHealing st).toFG.toSG.toGoldfishStore st.s
  obtain ⟨U, hU⟩ :=
    facts.fc.voter_support_view_nonempty E (M.toHealing st).toFG.toSG.toGoldfishStore st.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_in_tree_with_layer_nonempty contract E hc (M.toHealing st)
    T W U (st.s - 1)
  exact ⟨H, gfHeadWith_intro contract E hc st hT hW hU
    ((facts.hd.get_head_in_tree_with_eq_layer _ _ _ _ _ _ _ _ _).2 hH)⟩

/-- Every outcome of `gfVoteFrom` is the vote `⟨v, s, H.root⟩` for an outcome `n` of the vote read
    and an outcome `H` of `gfHeadWith` under `n`'s grade contract at `n`'s core store. -/
private theorem gfVoteFrom_cases (S : Setup V) (before : M.N) (v : V) (s : Slot)
    {u : GoldfishVote V} (hu : Restated.gfVoteFrom M S before v s ⇢ u) :
    ∃ n, Restated.voteReadOf M S before s ⇢ n ∧
      ∃ H, Restated.gfHeadWith M (M.gradeContract n.cache) S.E S.hc n.st.core ⇢ H ∧
        u = ⟨v, s, H.root⟩ := by
  obtain ⟨H, hH, rfl⟩ := returns_map_elim_cone _ _ _ hu
  unfold Restated.gfHeadFrom at hH
  obtain ⟨n, hn, hH⟩ := (returns_bind_iff_cone _ _ _).1 hH
  exact ⟨n, hn, H, hH, rfl⟩

/-- For an outcome `n` of the vote read and an outcome `H` of `gfHeadWith` under `n`'s grade
    contract at `n`'s core store, `⟨v, s, H.root⟩` is an outcome of `gfVoteFrom`. -/
private theorem gfVoteFrom_intro (S : Setup V) (before : M.N) (v : V) (s : Slot) {n : M.N}
    (hn : Restated.voteReadOf M S before s ⇢ n) {H : Block V}
    (hH : Restated.gfHeadWith M (M.gradeContract n.cache) S.E S.hc n.st.core ⇢ H) :
    Restated.gfVoteFrom M S before v s ⇢ ⟨v, s, H.root⟩ := by
  unfold Restated.gfVoteFrom
  refine returns_map_intro_cone (fun H : Block V => (⟨v, s, H.root⟩ : GoldfishVote V)) _ H ?_
  unfold Restated.gfHeadFrom
  exact (returns_bind_iff_cone _ _ _).2 ⟨n, hn, hH⟩

/-- `gfVoteFrom` has an outcome from every node state. -/
private theorem gfVoteFrom_nonempty (facts : Record.Facts M) (S : Setup V) (before : M.N) (v : V)
    (s : Slot) : ∃ u, Restated.gfVoteFrom M S before v s ⇢ u := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (M.vote_time S.E s) before.cache
  have hn : Restated.voteReadOf M S before s ⇢
      M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c :=
    returns_map_intro_cone _ _ _ hc
  obtain ⟨H, hH⟩ := gfHeadWith_nonempty facts (M.gradeContract
    (M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c).cache) S.E S.hc
    (M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c).st.core
  exact ⟨_, gfVoteFrom_intro S before v s hn hH⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The Goldfish votes `v` can sign at slot `s` from `Record.wakeStage M Sched t c v`, the node
    state `v`'s tick reads at time `t` from configuration `c`, are those it can sign from `v`'s node
    state in `c`. -/
theorem gfVoteFrom_wakeStage (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (t : Int) (c : Config V (NamedObject V) M.N) (v : V) (s : Slot) :
    Restated.gfVoteFrom M S (Record.wakeStage M Sched t c v) v s =
      Restated.gfVoteFrom M S (c[v].st) v s := by
  simp only [Restated.gfVoteFrom, Restated.gfHeadFrom, Restated.voteReadOf,
    Record.wakeStage_st facts, Record.wakeStage_record facts, Record.wakeStage_cache facts]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every outcome of the slot-`s` vote read has a core store whose slot is `s`. -/
theorem voteReadOf_slot (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) :
    ∀ n, Restated.voteReadOf M S before s ⇢ n → n.st.core.s = s := by
  intro n hn
  obtain ⟨c, -, rfl⟩ := voteReadOf_cases S before s hn
  rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s]
  exact facts.sch.slotOf_vote_time S.E s

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every vote `gfVoteFrom` names at slot `s` carries `s` as its slot. -/
theorem gfVoteFrom_slot (facts : Record.Facts M) (S : Setup V) (before : M.N) (v : V) (s : Slot) :
    ∀ u, Restated.gfVoteFrom M S before v s ⇢ u → u.slot = s := by
  intro u hu
  obtain ⟨n, -, H, -, rfl⟩ := gfVoteFrom_cases S before v s hu
  rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every vote `gfVoteFrom` names for validator `v` carries `v` as its signer. -/
theorem gfVoteFrom_val_index (facts : Record.Facts M) (S : Setup V) (before : M.N) (v : V) (s : Slot) :
    ∀ u, Restated.gfVoteFrom M S before v s ⇢ u → u.val_index = v := by
  intro u hu
  obtain ⟨n, -, H, -, rfl⟩ := gfVoteFrom_cases S before v s hu
  rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For a member `v` of slot `s`'s committee, every outcome of the Goldfish vote duty run on an
    outcome `n` of the slot-`s` vote read returns `⟨v, s, H.root⟩`, for every outcome `H` of
    `gfHeadWith` under `n`'s grade contract at `n`'s core store. -/
theorem voteDuty_eq_gfVoteFrom (facts : Record.Facts M) (S : Setup V) (before : M.N) (v : V) (s : Slot)
    (hcomm : v ∈ S.E.committee s) :
    ∀ n, Restated.voteReadOf M S before s ⇢ n →
      ∀ D, M.duties_goldfish_vote_with (M.gradeContract n.cache) S.E S.hc
          ((Setup.alwaysAwake S).node v) n.st ⇢ D →
        ∀ H, Restated.gfHeadWith M (M.gradeContract n.cache) S.E S.hc n.st.core ⇢ H →
          D.2 = some ⟨v, s, H.root⟩ := by
  intro n hn D hD H hH
  have hidx : ((Setup.alwaysAwake S).node v).val_index = v :=
    (Setup.alwaysAwake S).node_val_index v
  have hslot : n.st.core.s = s := Restated.voteReadOf_slot facts S before s n hn
  have hcomm' : ((Setup.alwaysAwake S).node v).val_index ∈ S.E.committee n.st.core.s := by
    rw [hidx, hslot]; exact hcomm
  obtain ⟨T, hT, W, hW, U, hU, hH⟩ := gfHeadWith_cases _ S.E S.hc n.st.core hH
  rw [facts.fc.goldfish_vote_with_snd_of_mem_committee _ _ _ _ _ hcomm' D hD T hT W hW U hU H
    ((facts.hd.get_head_in_tree_with_eq_layer _ _ _ _ _ _ _ _ _).1 hH), hidx, hslot]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every outcome of the tick of a member `v` of slot `s`'s committee at slot `s`'s Goldfish vote
    instant, at a node state `st` that passes the grade-1 awake test of `s`'s round, emits every
    slot-`s` vote `gfVoteFrom` names for `v`. The hypothesis `hn` says that `st` is a node state a
    run reaches, and `hv` that `st` runs as `v`. -/
theorem namedTick_emits_gfVote (facts : Record.Facts M) (S : Setup V) (v : V) (st : M.N) (s : Slot)
    (hs : 0 < s) (hcomm : v ∈ S.E.committee s)
    (hrun : M.awake_for_grade1 (Setup.alwaysAwake S) v st (M.round_of S.hc s)) :
    ∀ out₁, M.tick (Setup.alwaysAwake S) v st (M.vote_time S.E s) ⇢ out₁ →
      ∀ u, Restated.gfVoteFrom M S st v s ⇢ u →
      ∀ (hn : M.reachedNode st := by trivial) (hv : M.runs_as st v := by trivial),
      NamedObject.gfVote u ∈ out₁.2 := by
  intro out₁ hout u hu _hn _hv
  obtain ⟨n, hn, H, hH, rfl⟩ := gfVoteFrom_cases S st v s hu
  obtain ⟨c, hc, hneq⟩ := voteReadOf_cases S st s hn
  obtain ⟨D, hD⟩ := facts.dt.goldfish_vote_with_nonempty (M.gradeContract n.cache) S.E S.hc
    ((Setup.alwaysAwake S).node v) n.st
  have hDu := Restated.voteDuty_eq_gfVoteFrom facts S st v s hcomm n hn D hD H hH
  rw [hneq, facts.nd.mkNode_cache, facts.nd.mkNode_st,
    facts.dt.duties_goldfish_vote_with_store_with_cache] at hD
  exact facts.nd.on_tick_emit_vote_mem_of_outcomes (Setup.alwaysAwake S) v st s hs c hc D hD hDu
    out₁ hout hrun

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `⟨v, .gfVote u⟩` is in the sent log after `i` steps, `u` names `v`, and `v` is honest through
    a time at or after `x[i].time`, then `u`'s slot is positive, `v` is in that slot's committee,
    and some step `k < i` is the tick at `u`'s slot's vote instant, at which `v` was awake and `u`
    is every vote `gfVoteFrom` names for `v`. -/
theorem gfVote_slot_of_sent (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {v : V} {u : GoldfishVote V} {tB : Int}
    (hv : HonestThroughTime Sched tB v) (hunf : Restated.Unforgeability M S x) (hauth : u.val_index = v)
    {i : Nat} (hi : (x[i].time : Int) ≤ tB)
    (ho : (⟨v, NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent) :
    u.val_index = v ∧ 0 < u.slot ∧ v ∈ S.E.committee u.slot ∧
      ∃ k < i, Restated.tickStepAt M x k (M.vote_time S.E u.slot) ∧
        v ∈ Sched.awake (M.vote_time S.E u.slot) ∧
        ∀ u', Restated.gfVoteFrom M S (x[k][v].st) v u.slot ⇢ u' → u = u' := by
  obtain ⟨k, hk, t, hlbl, haw, hdvd, out, hout, hemit⟩ :=
    Restated.tick_of_honest_signed_upTo facts S Sched x v (NamedObject.gfVote u) tB hv hunf
      (by rw [author_gfVote, hauth]) i hi ho
  have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (k) v (↑t)
  have _hv_s2 := Record.runs_as_wakeStage facts S Sched x (k) v (↑t)
  obtain ⟨hpos, ht, hduty, hidx, hslot⟩ :=
    facts.nd.gfVote_emitted_shape (Setup.alwaysAwake S) v _ (t : Int) out hout u hemit
  rw [Record.wakeStage_st facts, Record.wakeStage_cache facts] at hduty
  have htv : (t : Int) = M.vote_time S.E u.slot := by rw [hslot]; exact ht
  have hspos : 0 < u.slot := by rw [hslot]; exact hpos
  have hidx' : ((Setup.alwaysAwake S).node v).val_index = v :=
    (Setup.alwaysAwake S).node_val_index v
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (x[k][v].st).st.core.toHealing (t : Int)
    (x[k][v].st).cache
  obtain ⟨D, hD⟩ := facts.dt.goldfish_vote_with_nonempty (M.frameContract c) S.E S.hc
    ((Setup.alwaysAwake S).node v) (M.ns_setClock S.E (x[k][v].st).st (t : Int))
  have hDu : D.2 = some u := hduty c hc D hD
  have hcore_s : (M.ns_setClock S.E (x[k][v].st).st (t : Int)).core.s = u.slot := by
    rw [facts.hd.Sts_setClock_core_s, hslot]; rfl
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E
    (M.ns_setClock S.E (x[k][v].st).st (t : Int)).core
    (M.ns_setClock S.E (x[k][v].st).st (t : Int)).core.s
  obtain ⟨W, hW⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing (M.ns_setClock S.E (x[k][v].st).st (t : Int)).core).toFG.toSG.toGoldfishStore
    (M.ns_setClock S.E (x[k][v].st).st (t : Int)).core.s
  obtain ⟨U, hU⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing (M.ns_setClock S.E (x[k][v].st).st (t : Int)).core).toFG.toSG.toGoldfishStore
    (M.ns_setClock S.E (x[k][v].st).st (t : Int)).core.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.frameContract c) S.E S.hc
    (M.toHealing (M.ns_setClock S.E (x[k][v].st).st (t : Int)).core) T W U
    ((M.ns_setClock S.E (x[k][v].st).st (t : Int)).core.s - 1)
  have hcomm0 := (facts.fc.namedDuties_goldfish_vote_with_snd_eq_some _ _ _ _ _ D hD hDu
    T hT W hW U hU H hH).1
  have hcomm : v ∈ S.E.committee u.slot := by rw [hidx', hcore_s] at hcomm0; exact hcomm0
  refine ⟨hidx, hspos, hcomm, k, hk, ⟨t, hlbl, htv⟩,
    by rw [← htv]; exact (Finset.mem_sdiff.1 haw).1, ?_⟩
  intro u' hu'
  have hvf : Restated.gfVoteFrom M S (Record.wakeStage M Sched (t : Int) x[k] v) v u.slot =
      Restated.gfVoteFrom M S (x[k][v].st) v u.slot := by
    simp only [Restated.gfVoteFrom, Restated.gfHeadFrom, Restated.voteReadOf,
      Record.wakeStage_st facts, Record.wakeStage_record facts, Record.wakeStage_cache facts]
  rw [← hvf] at hu'
  have hout' : M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) x[k] v)
      (M.vote_time S.E u.slot) ⇢ out := by
    rw [← htv]; exact hout
  have hrun : M.awake_for_grade1 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (t : Int) x[k] v) (M.round_of S.hc u.slot) := by
    have h := facts.nd.gfVote_mem_on_tick_emit_awake (Setup.alwaysAwake S) v _ (t : Int) out hout
      hemit
    rw [← hslot] at h
    exact h
  have _hr_s3 := Record.reachedNode_wakeStage facts S Sched x (k) v (↑t)
  have hemit' := Restated.namedTick_emits_gfVote facts S v _ u.slot hspos hcomm hrun out
    hout' u' hu'
  have _hr_s4 := Record.reachedNode_wakeStage facts S Sched x (k) v (↑t)
  have _hv_s5 := Record.runs_as_wakeStage facts S Sched x (k) v (↑t)
  have hshape := (facts.nd.gfVote_emitted_shape (Setup.alwaysAwake S) v _ (t : Int) out hout u'
      hemit').2.2.1
  rw [Record.wakeStage_st facts, Record.wakeStage_cache facts] at hshape
  have hDu' : D.2 = some u' := hshape c hc D hD
  exact Option.some_inj.mp (hDu.symm.trans hDu')

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `w`'s store after `m` steps holds `u` in the pool of `u`'s slot and `u` names a validator `q`
    honest through step `m`, then the sent log at some step at or before `m` carries `q`'s signed
    message for `u`. -/
theorem sent_of_mem_pool_honest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {m : Nat} {w q : V} (hq : Restated.HonestThrough M Sched x m q) {u : GoldfishVote V}
    (hu : u ∈ (M.store_pool (x[m][w].st).st.core u.slot)) (hidx : u.val_index = q) :
    ∃ i' : Nat, i' ≤ m ∧
      (⟨q, NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V)) ∈ x[i'].sent := by
  have h0 : Restated.Vocabulary.Execution.Object.processed M (x[0][w].st).st
      (NamedObject.gfVote u) = false := by
    simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not]
    rw [Record.st_zero M S Sched x w, facts.nd.initial_st, ← facts.sto.mem_pool_iff]
    exact facts.hd.initial_core_not_mem_pool _ _
  have hm1 : Restated.Vocabulary.Execution.Object.processed M (x[m][w].st).st
      (NamedObject.gfVote u) = true := by
    simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq]
    exact (facts.sto.mem_pool_iff _ _ _).1 hu
  obtain ⟨i, him, hf0, hf1⟩ :=
    Restated.exists_flip_of_processed facts S Sched x w (NamedObject.gfVote u) h0 hm1
  have hauthor : NamedObject.author (NamedObject.gfVote u) = some q := by
    rw [author_gfVote, hidx]
  rcases Restated.flip_step_cases facts S Sched x hf0 hf1 with
    ⟨sm, hlbl, -, -, hpay⟩ | ⟨τ, hlbl, haw, hdvd, hem⟩
  · refine ⟨i, le_of_lt him, ?_⟩
    have hsm : sm ∈ x[i].sent := (Restated.sent_of_deliver facts S Sched x hlbl).1
    have hhon : Restated.HonestThrough M Sched x i q := fun t ht =>
      hq t (le_trans ht (Restated.time_mono_int facts S Sched x (le_of_lt him)))
    rcases hpay with hmsg | ⟨Bl, hmsg, hcc⟩
    · have hres := hexec.unforgeable i sm q hsm (by rw [hmsg]; exact hauthor) hhon
      rw [hmsg] at hres
      exact hres
    · refine hexec.carried i sm (NamedObject.gfVote u) q hsm ?_ hauthor hhon
      rw [hmsg]
      exact Restated.carries_of_carriedCall facts (Setup.alwaysAwake S) (x[i][w].st).st Bl hcc
  · refine ⟨i + 1, Nat.succ_le_of_lt him, ?_⟩
    have hhon : Restated.HonestThrough M Sched x (i + 1) q := fun t ht =>
      hq t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt him)))
    obtain ⟨out₁, hout₁, hst₁, hem⟩ := hem
    have hsend := facts.nd.tick_send_eq_of_state (Setup.alwaysAwake S) w
      (Record.wakeStage M Sched (τ : Int) x[i] w) (τ : Int)
    rcases hem with hmem | ⟨Bl, hmem, hcc⟩
    · have hsent := Restated.mem_sent_of_tick_of_state facts S Sched x hlbl haw hdvd hsend
        hout₁ hst₁ hmem
      exact hexec.unforgeable (i + 1) ⟨w, NamedObject.gfVote u⟩ q hsent hauthor hhon
    · have hsent := Restated.mem_sent_of_tick_of_state facts S Sched x hlbl haw hdvd hsend
        hout₁ hst₁ hmem
      exact hexec.carried (i + 1) ⟨w, NamedObject.block Bl⟩ (NamedObject.gfVote u) q hsent
        (Restated.carries_of_carriedCall facts (Setup.alwaysAwake S) _ Bl hcc) hauthor hhon

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Two slot-`s` votes in `w`'s pool after `m` steps that both name a validator `q` honest through
    step `m` are the same vote. -/
theorem gfVote_unique_of_honest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {m : Nat} {w q : V} (hq : Restated.HonestThrough M Sched x m q) {s : Slot}
    {u_1 u_2 : GoldfishVote V}
    (h_1 : u_1 ∈ (M.store_pool (x[m][w].st).st.core s)) (h_2 : u_2 ∈ (M.store_pool (x[m][w].st).st.core s))
    (hi_1 : u_1.val_index = q) (hi_2 : u_2.val_index = q) : u_1 = u_2 := by
  have hs_1 : u_1.slot = s := Restated.slot_of_mem_pool_sts facts S Sched x m w h_1
  have hs_2 : u_2.slot = s := Restated.slot_of_mem_pool_sts facts S Sched x m w h_2
  obtain ⟨i_1, hi_1m, hsent_1⟩ :=
    Restated.sent_of_mem_pool_honest facts S Sched x hexec hq (by rw [hs_1]; exact h_1) hi_1
  obtain ⟨i_2, hi_2m, hsent_2⟩ :=
    Restated.sent_of_mem_pool_honest facts S Sched x hexec hq (by rw [hs_2]; exact h_2) hi_2
  obtain ⟨-, -, -, k_1, -, htick_1, -, heq_1⟩ :=
    Restated.gfVote_slot_of_sent facts S Sched x (tB := (x[m].time : Int)) hq hexec.toUnforgeability hi_1
      (Restated.time_mono_int facts S Sched x hi_1m) hsent_1
  obtain ⟨-, -, -, k_2, -, htick_2, -, heq_2⟩ :=
    Restated.gfVote_slot_of_sent facts S Sched x (tB := (x[m].time : Int)) hq hexec.toUnforgeability hi_2
      (Restated.time_mono_int facts S Sched x hi_2m) hsent_2
  rw [hs_1] at htick_1 heq_1
  rw [hs_2] at htick_2 heq_2
  have hkeq : k_1 = k_2 := Restated.tickStepAt_unique facts x htick_1 htick_2
  subst hkeq
  obtain ⟨u', hu'⟩ := gfVoteFrom_nonempty facts S (x[k_1][q].st) q s
  rw [heq_1 u' hu', heq_2 u' hu']

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A validator `q` honest through step `m` does not equivocate in `w`'s slot-`s` pool after `m`
    steps. -/
theorem no_equiv_of_honest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {m : Nat} {w q : V} (hq : Restated.HonestThrough M Sched x m q) (s : Slot) :
    M.equivocates ((M.store_pool (x[m][w].st).st.core s)) q = false := by
  have hcard : (M.votes_by ((M.store_pool (x[m][w].st).st.core s)) q).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    rw [facts.sch.mem_votes_by_iff] at ha hb
    exact Restated.gfVote_unique_of_honest facts S Sched x hexec hq ha.1 hb.1 ha.2 hb.2
  exact facts.sch.equivocates_eq_false_of_card_le_one hcard

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If every vote of `vs` naming a validator `q` honest through step `m` is in `w`'s slot-`s` pool
    after `m` steps, then `q` does not equivocate in `vs`. -/
theorem no_equiv_of_subset_pool (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {m : Nat} {w q : V} (hq : Restated.HonestThrough M Sched x m q) {s : Slot}
    {vs : Finset (GoldfishVote V)}
    (hsub : ∀ u ∈ vs, u.val_index = q → u ∈ (M.store_pool (x[m][w].st).st.core s)) :
    M.equivocates vs q = false := by
  have hcard : (M.votes_by vs q).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    rw [facts.sch.mem_votes_by_iff] at ha hb
    exact Restated.gfVote_unique_of_honest facts S Sched x hexec hq (hsub a ha.1 ha.2) (hsub b hb.1 hb.2)
      ha.2 hb.2
  exact facts.sch.equivocates_eq_false_of_card_le_one hcard

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For `0 < s`, slot `s`'s support cutoff is two delays after the slot's start. -/
private theorem support_cutoff_eq_of_pos (facts : Record.Facts M) (E : Env V) {s : Slot}
    (hs : 0 < s) : M.support_cutoff E s = slotStart E.Δ s + 2 * E.Δ := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, (Nat.succ_pred_eq_of_pos hs).symm⟩
  rw [← facts.sch.confirmation_time_eq_support_cutoff_succ,
    ← facts.sch.slotStart_add_six_delta_eq_confirmation_time, slotStart_succ]
  ring

/-- A Goldfish vote of `q` that slot `s`'s vote tick at step `m` added to the sent log is an honest
    send at step `m`, when `q` is honest through a step at or after the slot's support cutoff. -/
private theorem gfVote_honestSend_at_tick (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {s : Slot} (hs : 0 < s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    {q : V} {u : GoldfishVote V} (_huslot : u.slot = s)
    (hsent : (⟨q, NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V))
      ∈ x[m + 1].sent - x[m].sent)
    {mr : Nat} (hqh : Restated.HonestThrough M Sched x mr q)
    (hmr : M.support_cutoff S.E s ≤ (x[mr].time : Int)) :
    Restated.HonestSendAt M S x m (⟨q, NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V)) := by
  have hd := S.E.Δ_pos
  have hvt : M.vote_time S.E s = slotStart S.E.Δ s + S.E.Δ :=
    (facts.sch.slotStart_add_delta_eq_vote_time S.E s).symm
  have hsc : M.support_cutoff S.E s = slotStart S.E.Δ s + 2 * S.E.Δ :=
    support_cutoff_eq_of_pos facts S.E hs
  have hmtime : (x[m].time : Int) + 1 = M.vote_time S.E s := (Restated.tickStepAt_time facts x hm).2
  have hmle : (x[m].time : Int) ≤ (x[mr].time : Int) := by
    have h1 : (x[m].time : Int) = slotStart S.E.Δ s + S.E.Δ - 1 := by
      rw [hvt] at hmtime; linarith
    have h2 : slotStart S.E.Δ s + 2 * S.E.Δ ≤ (x[mr].time : Int) := by rw [← hsc]; exact hmr
    linarith
  have hqm : Restated.HonestThrough M Sched x m q := fun t ht => hqh t (le_trans ht hmle)
  exact And.intro hsent (hqm _ (le_refl _))

/-- A Goldfish vote honestly sent at the step before slot `s`'s vote instant is delivered to a
    receiver `w` awake from the slot's start to its support cutoff, at a step strictly before that
    cutoff and before the step `mr`. -/
private theorem gfVote_delivery_step (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (hsync : Restated.SynchronyFromWake M S x)
    {s : Slot} (hs : 0 < s) (hgst : S.E.t_GST ≤ slotStart S.E.Δ s)
    {q w : V} {u : GoldfishVote V} {i : Nat}
    (hsend : Restated.HonestSendAt M S x i (⟨q, NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V)))
    (hitime : (x[i].time : Int) + 1 = M.vote_time S.E s)
    {mr : Nat} (hmr : M.support_cutoff S.E s ≤ (x[mr].time : Int))
    (hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s)) :
    ∃ k : Nat, k + 1 ≤ mr ∧ (x[k].time : Int) < M.support_cutoff S.E s ∧
      x.lbl k = AtomicAction.deliver w ⟨q, NamedObject.gfVote u⟩ := by
  have hd := S.E.Δ_pos
  have hvt : M.vote_time S.E s = slotStart S.E.Δ s + S.E.Δ :=
    (facts.sch.slotStart_add_delta_eq_vote_time S.E s).symm
  have hsc : M.support_cutoff S.E s = slotStart S.E.Δ s + 2 * S.E.Δ :=
    support_cutoff_eq_of_pos facts S.E hs
  have hit : (x[i].time : Int) = slotStart S.E.Δ s + S.E.Δ - 1 := by
    rw [hvt] at hitime; linarith
  have hmax : max (x[i].time : Int) S.E.t_GST = (x[i].time : Int) :=
    max_eq_left (by rw [hit]; linarith)
  have hwin : w ∈ Sched.awakeThroughout (x[i].time : Int)
      (max (x[i].time : Int) S.E.t_GST + S.E.Δ) := by
    refine awakeThroughout_mono Sched hawT ?_ ?_
    · rw [hit]; linarith
    · rw [hmax, hit, hsc]; linarith
  obtain ⟨k, -, hlbl, -, hlt⟩ := Restated.synchronyFromWake_from_step facts S hsync hsend hwin
  rw [hmax, hit] at hlt
  have hkcut : (x[k].time : Int) < M.support_cutoff S.E s := by rw [hsc]; linarith
  refine ⟨k, ?_, hkcut, hlbl⟩
  by_contra hcon
  have hmrk : mr ≤ k := by omega
  have h := Restated.time_mono_int facts S Sched x hmrk
  linarith

/-- If step `k` delivers `q`'s slot-`s` vote `u` to `w` strictly before the slot's support cutoff
    and before step `mr`, then `w`'s store at step `mr` holds `u` in its slot-`s` pool with a stamp
    strictly before the cutoff; the second half of `fresh_vote_in_pool`. -/
private theorem fresh_vote_after_delivery (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (htd : Restated.TimeDiverges M x) {s : Slot} (hs : 0 < s) {q w : V} {u : GoldfishVote V}
    (huslot : u.slot = s) (huidx : u.val_index = q) (hcomm : q ∈ S.E.committee s) {k mr : Nat}
    (hlbl : x.lbl k = AtomicAction.deliver w ⟨q, NamedObject.gfVote u⟩) (hk1mr : k + 1 ≤ mr)
    (hkstrict : (x[k].time : Int) < M.support_cutoff S.E s)
    (hqh : Restated.HonestThrough M Sched x mr q)
    (hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s))
    (hwh : w ∉ Sched.adv (slotStart S.E.Δ s))
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (slotStart S.E.Δ s) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (slotStart S.E.Δ s) x[n] w) (slotStart S.E.Δ s) ⇢ out) :
    u ∈ (M.store_pool (x[mr][w].st).st.core s) ∧
      ∃ τ : Stamp, (x[mr][w].st).st.core.timestamp_vote u = some τ ∧
        τ < ((M.support_cutoff S.E s : Int) : Stamp) := by
  have hd := S.E.Δ_pos
  have hvt : M.vote_time S.E s = slotStart S.E.Δ s + S.E.Δ :=
    (facts.sch.slotStart_add_delta_eq_vote_time S.E s).symm
  have hsc : M.support_cutoff S.E s = slotStart S.E.Δ s + 2 * S.E.Δ :=
    support_cutoff_eq_of_pos facts S.E hs
  have hkmr : k ≤ mr := by omega
  have hqk : Restated.HonestThrough M Sched x k q := fun t ht =>
    hqh t (le_trans ht (Restated.time_mono_int facts S Sched x hkmr))
  have hsentk : (⟨q, NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V)) ∈ x[k].sent :=
    (Restated.sent_of_deliver facts S Sched x hlbl).1
  obtain ⟨-, -, -, k_0, hk_0k, htick_0, -, -⟩ :=
    Restated.gfVote_slot_of_sent facts S Sched x (tB := (x[k].time : Int)) hqk hexec.toUnforgeability huidx
      (le_refl _) hsentk
  have hlo : slotStart S.E.Δ s ≤ (x[k].time : Int) := by
    have h1 : (x[k_0 + 1].time : Int) = M.vote_time S.E u.slot :=
      (Restated.tickStepAt_time facts x htick_0).1
    have h2 : (x[k_0 + 1].time : Int) ≤ (x[k].time : Int) :=
      Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt hk_0k)
    rw [h1, huslot, hvt] at h2
    linarith
  have hhi : (x[k].time : Int) < slotStart S.E.Δ (u.slot + 2) := by
    rw [huslot]
    have hexp : slotStart S.E.Δ (s + 2) = slotStart S.E.Δ s + 8 * S.E.Δ := by
      rw [slotStart_add]
      push_cast; ring
    rw [hexp]
    rw [hsc] at hkstrict
    linarith
  have hawTk : w ∈ Sched.awakeThroughout (slotStart S.E.Δ u.slot) (x[k].time : Int) := by
    rw [huslot]
    exact awakeThroughout_shrink Sched hawT (le_of_lt hkstrict)
  have hwin := Restated.gf_window_of_awakeThroughout facts S Sched x htd k w u hawTk
    (by rw [huslot]; exact hwh) (by rw [huslot]; exact hlo) (by rw [huslot]; exact hs) hhi
    (by rw [huslot]; exact hneTick)
  have hcommu : u.val_index ∈ S.E.committee u.slot := by rw [huidx, huslot]; exact hcomm
  have hstampAt : ∀ n : Nat, (x[n][w].st).st.core.t ≤ (x[k].time : Int) →
      u ∈ (M.store_pool (x[n][w].st).st.core u.slot) → n ≤ mr →
      (u ∈ (M.store_pool (x[mr][w].st).st.core s) ∧
        ∃ τ : Stamp, (x[mr][w].st).st.core.timestamp_vote u = some τ ∧
          τ < ((M.support_cutoff S.E s : Int) : Stamp)) := by
    intro n hclk hmem hnmr
    obtain ⟨τ, hτ, hb⟩ := Restated.stamp_le_clock_gfVote facts S Sched x n w hmem
    refine ⟨by rw [← huslot]; exact Restated.mem_pool_mono_sts facts S Sched x w hnmr hmem, τ,
      Restated.stamp_mono_sts facts S Sched x w hnmr hτ, ?_⟩
    refine lt_of_le_of_lt (le_trans hb (WithBot.coe_le_coe.mpr hclk)) ?_
    exact WithBot.coe_lt_coe.mpr hkstrict
  have hdt : x[k + 1].time = x[k].time := Restated.deliver_time facts S Sched x hlbl
  rcases Restated.gfVote_recorded_of_deliver facts S Sched x hlbl hwin hcommu
      (facts.nd.process_nonempty _ _ _ (fun _ h => by cases h)) with hmk | heq | ⟨hm1, hst1⟩
  · exact hstampAt k (Restated.clock_le_time_sts facts S Sched x k w) hmk hkmr
  · have hne := Restated.no_equiv_of_honest facts S Sched x hexec (w := w) hqk u.slot
    rw [huidx] at heq
    exact Bool.noConfusion (heq.symm.trans hne)
  · have hclk1 : (x[k + 1][w].st).st.core.t ≤ (x[k].time : Int) := by
      have h1 : (x[k + 1][w].st).st.core.t ≤ (x[k + 1].time : Int) :=
        Restated.clock_le_time_sts facts S Sched x (k + 1) w
      rw [hdt] at h1
      exact h1
    exact hstampAt (k + 1) hclk1 hm1 hk1mr

/-- If step `m` is the tick at slot `s`'s Goldfish vote instant, GST is at or before the slot's
    start, `q` is awake there, in slot `s`'s committee and honest through step `mr`, step `mr` is at
    or after the slot's support cutoff, and `w` is awake from the slot's start to that cutoff, then
    `w`'s store at step `mr` holds every slot-`s` vote `gfVoteFrom` names for `q` in its slot-`s`
    pool, with a stamp strictly before the cutoff. The hypotheses `hneTickVote` and `hneTick` say
    that the two ticks the proof reads have an outcome, and `hrun` that `q`'s tick passes the
    grade-1 awake test of `s`'s round. -/
theorem fresh_vote_in_pool (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (htd : Restated.TimeDiverges M x)
    {s : Slot} (hs : 0 < s) (hgst : S.E.t_GST ≤ slotStart S.E.Δ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    {q : V} (hqaw : q ∈ Sched.awake (M.vote_time S.E s)) (hcomm : q ∈ S.E.committee s)
    {w : V} {mr : Nat} (hqh : Restated.HonestThrough M Sched x mr q)
    (hmr : M.support_cutoff S.E s ≤ (x[mr].time : Int))
    (hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s))
    (hwh : w ∉ Sched.adv (slotStart S.E.Δ s))
    (hneTickVote : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (slotStart S.E.Δ s) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (slotStart S.E.Δ s) x[n] w) (slotStart S.E.Δ s) ⇢ out)
    (hrun : M.awake_for_grade1 (Setup.alwaysAwake S) q
      (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.round_of S.hc s)) :
    ∀ u, Restated.gfVoteFrom M S (x[m][q].st) q s ⇢ u →
      u ∈ (M.store_pool (x[mr][w].st).st.core s) ∧
        ∃ τ : Stamp, (x[mr][w].st).st.core.timestamp_vote u = some τ ∧
          τ < ((M.support_cutoff S.E s : Int) : Stamp) := by
  have _hr_0 : M.reachedNode (x[m][q].st) := Record.reachedNode_sts facts S Sched x m q
  have _hr_1 : M.reachedNode (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) := Record.reachedNode_wakeStage facts S Sched x m q (M.vote_time S.E s)
  intro u hu
  have hd := S.E.Δ_pos
  have hvt : M.vote_time S.E s = slotStart S.E.Δ s + S.E.Δ :=
    (facts.sch.slotStart_add_delta_eq_vote_time S.E s).symm
  have hsc : M.support_cutoff S.E s = slotStart S.E.Δ s + 2 * S.E.Δ :=
    support_cutoff_eq_of_pos facts S.E hs
  have huslot : u.slot = s := Restated.gfVoteFrom_slot facts S (x[m][q].st) q s u hu
  have huidx : u.val_index = q := Restated.gfVoteFrom_val_index facts S (x[m][q].st) q s u hu
  have hsent : (⟨q, NamedObject.gfVote u⟩ :
        SignedMsg V (NamedObject V)) ∈ x[m + 1].sent - x[m].sent := by
    obtain ⟨t', hlbl_m, ht'⟩ := id hm
    have hqv : q ∈ Sched.awake (M.vote_time S.E s) \ Sched.adv (M.vote_time S.E s) :=
      Finset.mem_sdiff.2 ⟨hqaw, hqh _ (by rw [hvt]; rw [hsc] at hmr; linarith)⟩
    refine Restated.mem_sent_diff_of_tick facts S Sched x hlbl_m (by rw [ht']; exact hqv)
      (by rw [ht']; exact facts.sch.vote_time_emod_delta S s) ?_ (by rw [ht']; exact hneTickVote)
    rw [ht']
    have hvf : Restated.gfVoteFrom M S (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) q s =
        Restated.gfVoteFrom M S (x[m][q].st) q s := by
      simp only [Restated.gfVoteFrom, Restated.gfHeadFrom, Restated.voteReadOf,
        Record.wakeStage_st facts, Record.wakeStage_record facts, Record.wakeStage_cache facts]
    have _hr_g := Record.reachedNode_wakeStage facts S Sched x m q (M.vote_time S.E s)
    have _hv_g := Record.runs_as_wakeStage facts S Sched x m q (M.vote_time S.E s)
    exact fun out hout => Restated.namedTick_emits_gfVote facts S q _ s hs hcomm hrun out
      hout u (by rw [hvf]; exact hu)
  obtain ⟨k, hk1mr, hkstrict, hlbl⟩ :=
    gfVote_delivery_step facts S Sched x hsync hs hgst
      (gfVote_honestSend_at_tick facts S Sched x hs hm huslot hsent hqh hmr)
      (Restated.tickStepAt_time facts x hm).2 hmr hawT
  exact fresh_vote_after_delivery facts S Sched x hexec htd hs huslot huidx hcomm hlbl hk1mr
    hkstrict hqh hawT hwh hneTick

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A validator is in `HonSlot S Sched s` exactly when it is awake throughout slot `s`'s vote
    window, is in slot `s`'s committee, and is not held by the adversary at slot `s`'s confirmation
    instant. -/
theorem mem_HonSlot (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V} {s : Slot} {q : V} :
    q ∈ Restated.HonSlot M S Sched s ↔ q ∈ activeAtW S Sched s ∧ q ∈ S.E.committee s ∧
      q ∉ Sched.adv (M.confirmation_time S.E s) := by
  simp only [Restated.HonSlot, Finset.mem_sdiff, Finset.mem_inter, and_assoc]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every member of `HonSlot S Sched s` is in slot `s`'s committee. -/
theorem HonSlot_subset_committee (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (s : Slot) :
    Restated.HonSlot M S Sched s ⊆ S.E.committee s := fun _ hq => ((Restated.mem_HonSlot facts).mp hq).2.1

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A member of `HonSlot S Sched s` is awake at slot `s`'s Goldfish vote instant. -/
theorem awake_of_mem_HonSlot (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (s : Slot) {q : V}
    (hq : q ∈ Restated.HonSlot M S Sched s) : q ∈ Sched.awake (M.vote_time S.E s) := by
  have h := ((Restated.mem_HonSlot facts).mp hq).1
  simp only [activeAtW, wVote] at h
  have hd := S.E.Δ_pos
  have hw : (0 : Int) ≤ (4 * (S.hc.R : Int) + 2) * S.E.Δ := mul_nonneg (by positivity) hd.le
  have hvt : M.vote_time S.E s = slotStart S.E.Δ s + S.E.Δ :=
    (facts.sch.slotStart_add_delta_eq_vote_time S.E s).symm
  rw [hvt]
  exact mem_awake_of_awakeThroughout Sched h (by linarith) (le_refl _)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under monotone corruption, a member of `HonSlot S Sched s` is honest through every step whose
    time is at or before slot `s`'s confirmation instant. -/
theorem honestThrough_of_mem_HonSlot (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (hmono : Sched.MonotoneCorruption) {s : Slot} {q : V}
    (hq : q ∈ Restated.HonSlot M S Sched s) {mr : Nat}
    (hmr : (x[mr].time : Int) ≤ M.confirmation_time S.E s) :
    Restated.HonestThrough M Sched x mr q := fun t ht hmem =>
  ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono t (M.confirmation_time S.E s) (le_trans ht hmr) hmem)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `committeeSleepinessW` from `tE`, with `tE` at or before slot `s + 1`'s start, the members
    of `HonSlot S Sched s` are more than half of slot `s`'s committee. -/
theorem majority_of_committeeSleepinessW (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE) {s : Slot}
    (hanchor : tE ≤ slotStart S.E.Δ (s + 1)) :
    (S.E.committee s).card < 2 * ((S.E.committee s) ∩ Restated.HonSlot M S Sched s).card := by
  have h := hcs (s + 1) (Nat.succ_le_succ (Nat.zero_le s)) hanchor
  simp only [Nat.add_sub_cancel] at h
  have hfold : (activeAtW S Sched s ∩ S.E.committee s) \
      Sched.adv (M.confirmation_time S.E s) = Restated.HonSlot M S Sched s := rfl
  rw [hfold] at h
  have hsub : Restated.HonSlot M S Sched s ⊆ S.E.committee s := Restated.HonSlot_subset_committee facts S Sched s
  have heq : (S.E.committee s) \ (activeAtW S Sched s \
        Sched.adv (M.confirmation_time S.E s))
      = (S.E.committee s) \ Restated.HonSlot M S Sched s := by
    refine Finset.ext (fun q => ?_)
    simp only [Finset.mem_sdiff, Restated.HonSlot, Finset.mem_inter]
    tauto
  rw [heq, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub] at h
  have hle : (Restated.HonSlot M S Sched s).card ≤ (S.E.committee s).card := Finset.card_le_card hsub
  rw [Finset.inter_eq_right.mpr hsub]
  omega

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The store slot `s'`'s vote duty reads has slot `s'`. -/
theorem voteStoreAt_slot (facts : Record.Facts M) (S : Setup V) (before : M.N) (s' : Slot) :
    (Restated.voteStoreAt M S before s').s = s' := by
  rw [Restated.voteStoreAt, facts.hd.Sts_setClock_core_s]
  exact facts.sch.slotOf_vote_time S.E s'

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `before` holds the vote `⟨q, s, X.root⟩` in its slot-`s` pool and the block `X`, of slot at
    most `s`, both stamped before slot `s`'s support cutoff, then the vote is in every outcome of
    the slot-`(s + 1)` support view of the store slot `s + 1`'s vote duty reads. -/
private theorem vote_mem_support_view_cone (facts : Record.Facts M) (S : Setup V) (before : M.N)
    {s : Slot} {q : V} {X : Block V} {τ σ : Stamp}
    (hpool : (⟨q, s, X.root⟩ : GoldfishVote V) ∈ M.store_pool before.st.core s)
    (hτ : before.st.core.timestamp_vote ⟨q, s, X.root⟩ = some τ)
    (hτlt : τ < ((M.support_cutoff S.E s : Int) : Stamp))
    (hfind : Block.find? before.st.core.T X.root = some X) (hXs : X.slot ≤ s)
    (hσ : before.st.core.timestamp_block X = some σ)
    (hσlt : σ < ((M.support_cutoff S.E s : Int) : Stamp))
    (U : Finset (GoldfishVote V)) (hU : M.voter_support_view S.E
      (M.toHealing (Restated.voteStoreAt M S before (s + 1))).toFG.toSG.toGoldfishStore (s + 1) ⇢ U) :
    (⟨q, s, X.root⟩ : GoldfishVote V) ∈ U := by
  have hgT : (M.toHealing (Restated.voteStoreAt M S before (s + 1))).toFG.toSG.toGoldfishStore.T
      = before.st.core.T := by
    rw [facts.sto.toHealing_gs_T, Restated.voteStoreAt, facts.hd.Sts_setClock_core_T]
  have hgP : M.gs_pool (M.toHealing (Restated.voteStoreAt M S before (s + 1))).toFG.toSG.toGoldfishStore s
      = M.store_pool before.st.core s := by
    rw [facts.sto.toHealing_gs_pool, Restated.voteStoreAt, facts.hd.Sts_setClock_core_pool]
  have hgV :
      (M.toHealing (Restated.voteStoreAt M S before (s + 1))).toFG.toSG.toGoldfishStore.timestamp_vote
        = before.st.core.timestamp_vote := by
    rw [facts.sto.toHealing_gs_timestamp_vote, Restated.voteStoreAt,
      facts.hd.setClock_core_timestamp_vote]
  have hgB :
      (M.toHealing (Restated.voteStoreAt M S before (s + 1))).toFG.toSG.toGoldfishStore.timestamp_block
        = before.st.core.timestamp_block := by
    rw [facts.sto.toHealing_gs_timestamp_block, Restated.voteStoreAt,
      facts.hd.setClock_core_timestamp_block]
  have hvfr : ((M.support_cutoff S.E s : Int) : Stamp) < ((M.view_freeze S.E s : Int) : Stamp) :=
    WithBot.coe_lt_coe.mpr (facts.sch.Sts_support_cutoff_lt_view_freeze S.E s)
  rw [← hgP] at hpool
  rw [← hgV] at hτ
  rw [← hgT] at hfind
  rw [← hgB] at hσ
  exact facts.sch.mem_voter_support_view_of_pool S.E _ s hpool hτ (lt_trans hτlt hvfr) hfind hXs
    hσ (lt_trans hσlt hvfr) U hU

/-- A validator awake throughout slot `s`'s vote window is awake from one delay before the grade-1
    early cutoff of `s`'s round to `s`'s vote instant. -/
private theorem grade1_window_of_activeAtW_cone (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) {s : Slot} {q : V} (hq : q ∈ activeAtW S Sched s) :
    q ∈ Sched.awakeThroughout (M.early S.E S.hc (M.round_of S.hc s) .g1 - S.E.Δ)
      (M.vote_time S.E s) := by
  have hΔ := S.E.Δ_pos
  have hg1 := facts.gr.early_g2_add_delta_le_early_g1 S (M.round_of S.hc s)
  have hg2 := facts.gr.early_g2_eq S (M.round_of S.hc s)
  have ha := facts.sch.a_eq_confirmation_time S.hc S.E (M.round_of S.hc s)
  have hconf := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E
    (M.opening_slot S.hc (M.round_of S.hc s))
  have hvote := facts.sch.slotStart_add_delta_eq_vote_time S.E s
  have hlt := facts.gr.lt_opening_slot_round_of_succ S.hc s
  rw [facts.gr.opening_slot_succ S.hc (M.round_of S.hc s)] at hlt
  have hsle : ((s : Nat) : Int) ≤ ((M.opening_slot S.hc (M.round_of S.hc s) : Nat) : Int) +
      ((S.hc.R : Nat) : Int) - 1 := by
    have h1 : s + 1 ≤ M.opening_slot S.hc (M.round_of S.hc s) + S.hc.R := hlt
    have h2 : ((s + 1 : Nat) : Int) ≤
        ((M.opening_slot S.hc (M.round_of S.hc s) + S.hc.R : Nat) : Int) := by
      exact_mod_cast h1
    push_cast at h2
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsle (by linarith : (0 : Int) ≤ 4 * S.E.Δ)
  have hss : slotStart S.E.Δ s ≤ slotStart S.E.Δ (M.opening_slot S.hc (M.round_of S.hc s)) +
      4 * S.E.Δ * ((S.hc.R : Nat) : Int) - 4 * S.E.Δ := by
    unfold slotStart; linarith
  simp only [activeAtW, wVote, Schedule.awakeThroughout, Finset.mem_inf, Finset.mem_Icc] at hq ⊢
  intro i hi
  apply hq i
  constructor
  · have hRΔ : (4 * ((S.hc.R : Nat) : Int) + 2) * S.E.Δ =
        4 * S.E.Δ * ((S.hc.R : Nat) : Int) + 2 * S.E.Δ := by ring
    rw [hRΔ]
    linarith [hi.1]
  · linarith [hi.2]

/-- If step `m` is the tick at slot `s`'s vote instant, and `q` is awake throughout slot `s`'s vote
    window and not held by the adversary up to that instant, then the node state `q`'s tick at step
    `m` reads passes the grade-1 awake test of `s`'s round. -/
private theorem grade1_at_vote_tick_cone (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {m : Nat} {s : Slot}
    (hm : Restated.tickStepAt M x m (M.vote_time S.E s)) {q : V} (hq : q ∈ activeAtW S Sched s)
    (hhon : ∀ t' ≤ M.vote_time S.E s, q ∉ Sched.adv t') :
    M.awake_for_grade1 (Setup.alwaysAwake S) q
      (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.round_of S.hc s) := by
  obtain ⟨τ, hlbl, hτ⟩ := hm
  have h := Restated.run_fact_g1 facts S Sched x m τ s q hlbl (Or.inr hτ)
    (by rw [hτ]; exact grade1_window_of_activeAtW_cone facts S Sched hq) (by rw [hτ]; exact hhon)
  rw [hτ] at h
  exact h

/-- Under committee sleepiness at slot `s + 1`, if GST is at or before slot `s`'s start, `w` is
    awake from that start to the slot's support cutoff and reads its store at a step `mr` between
    that cutoff and the slot's confirmation instant, and every member of `HonSlot S Sched s` has a
    head resolving in `w`'s tree to a descendant of `B` stamped before the support cutoff, then
    `w`'s slot-`(s + 1)` voter views carry a cone of support for the descendants of `B` at slot `s`. -/
theorem coneSupport_at_slot (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    {s : Slot} (hs : 0 < s) (hanchor : tE ≤ slotStart S.E.Δ (s + 1))
    (hgst : S.E.t_GST ≤ slotStart S.E.Δ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    {w : V} {mr : Nat}
    (hmr : M.support_cutoff S.E s ≤ (x[mr].time : Int))
    (hmrc : (x[mr].time : Int) ≤ M.confirmation_time S.E s)
    (hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s))
    (hwh : w ∉ Sched.adv (slotStart S.E.Δ s))
    {B : Block V}
    (hheads : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ H : Block V,
      Restated.gfHeadFrom M S (x[m][q].st) s ⇢ H ∧ ∃ X : Block V,
      X.root = H.root ∧ Block.Preceq B X ∧ X.slot ≤ s ∧
        Block.find? (x[mr][w].st).st.core.T X.root = some X ∧
        ∃ σ : Stamp, (x[mr][w].st).st.core.timestamp_block X = some σ ∧
          σ < ((M.support_cutoff S.E s : Int) : Stamp))
    (hcarried : ∀ Bl ∈ (x[mr][w].st).st.core.T,
      ∀ u ∈ Bl.gf_support_votes, u ∈ Bl.gf_votes)
    (W : Finset (GoldfishVote V))
    (hW : Restated.voteViewOf M S.E (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ W)
    (hviewPool : ∀ q ∈ Restated.HonSlot M S Sched s,
      ∀ u ∈ W, u.val_index = q → u ∈ (M.store_pool (x[mr][w].st).st.core s))
    (hneTickVote : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (slotStart S.E.Δ s) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (slotStart S.E.Δ s) x[n] w) (slotStart S.E.Δ s) ⇢ out) :
    ∀ U, Restated.voteSupportViewOf M S.E (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ U →
      Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E
        (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).T W U W
        ((Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).s - 1) (Restated.HonSlot M S Sched s)
        (fun X => Block.Preceq B X) := by
  intro U hU
  have hT : (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).T = (x[mr][w].st).st.core.T := by
    rw [Restated.voteStoreAt, facts.hd.Sts_setClock_core_T]
  have hgT : (M.toHealing (Restated.voteStoreAt M S (x[mr][w].st) (s + 1))).toFG.toSG.toGoldfishStore.T
      = (x[mr][w].st).st.core.T := by
    rw [facts.sto.toHealing_gs_T, hT]
  have hsc : (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).s - 1 = s := by
    simp only [Restated.voteStoreAt_slot facts S (x[mr][w].st) (s + 1), Nat.add_sub_cancel]
  rw [hsc]
  have hW' : M.voter_view S.E
      (M.toHealing (Restated.voteStoreAt M S (x[mr][w].st) (s + 1))).toFG.toSG.toGoldfishStore
      (s + 1) ⇢ W := by
    have h := hW
    simp only [Restated.voteViewOf, Restated.voteStoreAt_slot facts S (x[mr][w].st) (s + 1)] at h
    exact h
  have hU' : M.voter_support_view S.E
      (M.toHealing (Restated.voteStoreAt M S (x[mr][w].st) (s + 1))).toFG.toSG.toGoldfishStore
      (s + 1) ⇢ U := by
    have h := hU
    simp only [Restated.voteSupportViewOf, Restated.voteStoreAt_slot facts S (x[mr][w].st) (s + 1)]
      at h
    exact h
  refine Restated.Vocabulary.Proofs.Optimistic.coneSupport_of_named_votes facts
    (Restated.majority_of_committeeSleepinessW facts S Sched hcs hanchor) (Finset.Subset.refl _)
    (facts.fc.voter_support_view_subset S.E _ (s + 1) (by rw [hgT]; exact hcarried) U hU' W hW')
    ?_ ?_
  · intro q _ hqH
    exact Restated.no_equiv_of_subset_pool facts S Sched x hexec
      (Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hqH hmrc) (w := w) (s := s)
      (hviewPool q hqH)
  · intro q _ hqH
    obtain ⟨H, hH, X, hXroot, hBX, hXs, hfind, σ, hσ, hσlt⟩ := hheads q hqH
    have hu : Restated.gfVoteFrom M S (x[m][q].st) q s ⇢ (⟨q, s, X.root⟩ : GoldfishVote V) := by
      rw [hXroot]
      exact returns_map_intro_cone (fun H : Block V => (⟨q, s, H.root⟩ : GoldfishVote V)) _ H hH
    obtain ⟨hpool, τ, hτ, hτlt⟩ :=
      Restated.fresh_vote_in_pool facts S Sched x hexec hsync htd hs hgst hm
        (Restated.awake_of_mem_HonSlot facts S Sched s hqH) ((Restated.mem_HonSlot facts).mp hqH).2.1
        (Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hqH hmrc) hmr hawT hwh
        (hneTickVote q hqH) hneTick
        (grade1_at_vote_tick_cone facts S Sched x hm ((Restated.mem_HonSlot facts).mp hqH).1
          (fun t ht hmem => ((Restated.mem_HonSlot facts).mp hqH).2.2 (hmono t _
            (le_trans ht (facts.sch.Sts_vote_time_le_confirmation_time S s)) hmem))) _ hu
    exact ⟨X, hBX, hXs,
      vote_mem_support_view_cone facts S (x[mr][w].st) hpool hτ hτlt hfind hXs hσ hσlt U hU',
      by rw [hT]; exact hfind⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the members of `Hon` support a cone of descendants of `B` in the outcomes `W`, `U` of `st`'s
    voter views, the votes of `W` are valid for slot `st.s − 1`, the outcome `A` of the SG root is
    an ancestor of `B`, and `B`'s chain from `A` lies in the outcome `T` of `st`'s voter tree, then
    every head `M.get_head_in_tree_with` selects over `T`, `W`, `U` is a descendant of `B`. -/
theorem head_preceq_of_cone (facts : Record.Facts M) (contract : M.Contract) (E : Env V)
    (hc : Protocol.HealConfig) (st : M.S) {B : Block V} {Hon : Finset V}
    (T : Finset (Block V)) (hT : Restated.voteTreeOf M E st ⇢ T)
    (W : Finset (GoldfishVote V)) (hW : Restated.voteViewOf M E st ⇢ W)
    (U : Finset (GoldfishVote V)) (hU : Restated.voteSupportViewOf M E st ⇢ U)
    (A : Block V) (hA : Restated.voteAnchorOf M contract E hc st ⇢ A)
    (hsup : Restated.Vocabulary.Proofs.Optimistic.ConeSupport M E st.T W U W (st.s - 1) Hon
      (fun X => Block.Preceq B X))
    (hvalid : Protocol.VoteSetValid E (st.s - 1) W)
    (hAB : Block.Preceq A B)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B → C ∈ T) :
    ∀ H, M.get_head_in_tree_with contract E hc st T W U (st.s - 1) ⇢ H → Block.Preceq B H := by
  intro H hH
  have hfc := (facts.hd.get_head_in_tree_with_eq_fork_choice contract E hc st T W U (st.s - 1)
    A hA H).1 hH
  exact facts.fc.goldfish_passes_cone E (M.toHealing st).toFG.σ (M.toHealing st).toFG.h_max st.T
    T st.s W U (st.s - 1) Hon hsup.majority hsup.counted hsup.sub
    hsup.no_equiv hsup.vote hvalid hAB hpath H hfc

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under the hypotheses of `coneSupport_at_slot`, if the votes of `w`'s raw view are valid for slot
    `s`, the SG root of `w`'s vote duty is an ancestor of `B`, and `B`'s chain from it lies in `w`'s
    voter tree, then every head `w`'s slot-`(s + 1)` vote duty selects is a descendant of `B`. -/
theorem gf_hop (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    {s : Slot} (hs : 0 < s) (hanchor : tE ≤ slotStart S.E.Δ (s + 1))
    (hgst : S.E.t_GST ≤ slotStart S.E.Δ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    {w : V} {mr : Nat}
    (hmr : M.support_cutoff S.E s ≤ (x[mr].time : Int))
    (hmrc : (x[mr].time : Int) ≤ M.confirmation_time S.E s)
    (hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s))
    (hwh : w ∉ Sched.adv (slotStart S.E.Δ s))
    {B : Block V}
    (hheads : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ H : Block V,
      Restated.gfHeadFrom M S (x[m][q].st) s ⇢ H ∧ ∃ X : Block V,
      X.root = H.root ∧ Block.Preceq B X ∧ X.slot ≤ s ∧
        Block.find? (x[mr][w].st).st.core.T X.root = some X ∧
        ∃ σ : Stamp, (x[mr][w].st).st.core.timestamp_block X = some σ ∧
          σ < ((M.support_cutoff S.E s : Int) : Stamp))
    (hcarried : ∀ Bl ∈ (x[mr][w].st).st.core.T,
      ∀ u ∈ Bl.gf_support_votes, u ∈ Bl.gf_votes)
    (n : M.N) (hn : Restated.voteReadOf M S (x[mr][w].st) (s + 1) ⇢ n)
    (T : Finset (Block V))
    (hT : Restated.voteTreeOf M S.E (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ T)
    (W : Finset (GoldfishVote V))
    (hW : Restated.voteViewOf M S.E (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ W)
    (U : Finset (GoldfishVote V))
    (hU : Restated.voteSupportViewOf M S.E (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ U)
    (A : Block V)
    (hA : Restated.voteAnchorOf M (M.gradeContract n.cache) S.E S.hc
      (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ A)
    (hviewPool : ∀ q ∈ Restated.HonSlot M S Sched s,
      ∀ u ∈ W, u.val_index = q → u ∈ (M.store_pool (x[mr][w].st).st.core s))
    (hvalid : Protocol.VoteSetValid S.E ((Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).s - 1) W)
    (hAB : Block.Preceq A B)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B → C ∈ T)
    (hneTickVote : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (slotStart S.E.Δ s) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (slotStart S.E.Δ s) x[n] w) (slotStart S.E.Δ s) ⇢ out) :
    ∀ H, M.get_head_in_tree_with (M.gradeContract n.cache) S.E S.hc
        (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) T W U
        ((Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).s - 1) ⇢ H →
      Block.Preceq B H :=
  Restated.head_preceq_of_cone facts (M.gradeContract n.cache)
    S.E S.hc (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) T hT W hW U hU A hA
    (Restated.coneSupport_at_slot facts S Sched x hexec hsync htd hmono hcs hs hanchor hgst hm
      hmr hmrc hawT hwh hheads hcarried W hW hviewPool hneTickVote hneTick U hU)
    hvalid hAB hpath

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A slot's late confirmation votes are in that slot's pool. -/
theorem confLate_subset_pool (facts : Record.Facts M) (E : Env V) (st : M.S) (s : Slot) :
    Restated.Vocabulary.Protocol.confLate M E st s ⊆ M.store_pool st s := by
  intro u hu
  rw [Restated.Vocabulary.Protocol.confLate, mem_beforeCutoff_iff] at hu
  exact hu.1

/-- Every outcome of `confVotes` at slot `s` is inside the store's slot-`s` pool. -/
private theorem confVotes_subset_pool_cone (E : Env V) (st : M.S) (s : Slot) :
    ∀ e, Restated.Vocabulary.Protocol.confVotes M E st s ⇢ e → e ⊆ M.store_pool st s := by
  intro e he u hu
  obtain ⟨e', he', rfl⟩ := returns_map_elim_cone _ _ _ he
  obtain ⟨tm, -, rfl⟩ := returns_map_elim_cone _ _ _ he'
  rw [Finset.mem_filter, mem_beforeCutoff_iff] at hu
  exact hu.1.1

/-- Every outcome of `confVotes` at slot `s` is, for an outcome `tm` of `st`'s resolution times, the
    slot-`s` pool filtered by `tm` against the support cutoff and then by the absence of a second
    vote of the same signer in the late set. -/
private theorem confVotes_cases (E : Env V) (st : M.S) (s : Slot) {e : Finset (GoldfishVote V)}
    (he : Restated.Vocabulary.Protocol.confVotes M E st s ⇢ e) :
    ∃ tm, st.tau ⇢ tm ∧
      e = (beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) u = true) := by
  obtain ⟨e', he', rfl⟩ := returns_map_elim_cone _ _ _ he
  obtain ⟨tm, htm, rfl⟩ := returns_map_elim_cone _ _ _ he'
  exact ⟨tm, htm, rfl⟩

/-- Every vote in an outcome of `confVotes` at a slot is in that slot's late set. -/
theorem confVotes_subset_confLate (facts : Record.Facts M) (E : Env V) (st : M.S) (s : Slot) :
    ∀ e, Restated.Vocabulary.Protocol.confVotes M E st s ⇢ e →
      e ⊆ Restated.Vocabulary.Protocol.confLate M E st s := by
  intro e he u hu
  obtain ⟨tm, htm, rfl⟩ := confVotes_cases E st s he
  have he' := (Finset.mem_filter.mp hu).1
  rw [beforeCutoff, Finset.mem_filter] at he'
  rw [Restated.Vocabulary.Protocol.confLate]
  refine DecoupledConsensusModel.Protocol.beforeCutoff_mono _
    (facts.sch.Protocol_support_cutoff_le_confirmation_time E s) _ ?_
  rw [beforeCutoff, Finset.mem_filter]
  exact ⟨he'.1, facts.sto.stampedBefore_vote_of_tau st tm htm he'.2⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A vote in the slot-`s` pool of `stc`, stamped before the slot's support cutoff, whose head
    resolves to a block `X` of slot at most the vote's slot also stamped before that cutoff, and
    with no other vote of its signer in the pool, is in every outcome of `confVotes` at slot `s`. -/
theorem mem_confVotes_of (facts : Record.Facts M) (E : Env V) (stc : M.S) {s : Slot} {u : GoldfishVote V}
    (hu : u ∈ (M.store_pool stc s)) {τ : Stamp} (hτ : stc.timestamp_vote u = some τ)
    (hlt : τ < ((M.support_cutoff E s : Int) : Stamp))
    {X : Block V} (hX : Block.find? stc.T u.head = some X) (hXs : X.slot ≤ u.slot)
    {σ : Stamp} (hσ : stc.timestamp_block X = some σ)
    (hσlt : σ < ((M.support_cutoff E s : Int) : Stamp))
    (huniq : ∀ u' ∈ (M.store_pool stc s), u'.val_index = u.val_index → u' = u) :
    ∀ e, Restated.Vocabulary.Protocol.confVotes M E stc s ⇢ e → u ∈ e := by
  intro e he
  obtain ⟨tm, htm, rfl⟩ := confVotes_cases E stc s he
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [mem_beforeCutoff_iff]
    exact ⟨hu, stampedBefore_of_lt (facts.sto.tau_eq_max stc hX hXs hτ hσ tm htm)
      (max_lt hlt hσlt)⟩
  · apply facts.fc.no_second_vote_in_of_forall
    intro u' hu'
    by_cases hc : u'.val_index = u.val_index
    · exact Or.inl (huniq u' (Restated.confLate_subset_pool facts E stc s hu') hc)
    · exact Or.inr hc

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under the hypotheses of `coneSupport_at_slot`, `w`'s slot-`s` confirmation views carry, for
    every outcome of its confirmation votes, a cone of support for the descendants of `B` at slot
    `s`. -/
theorem coneSupport_at_confirmation (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    {s : Slot} (hs : 0 < s) (hanchor : tE ≤ slotStart S.E.Δ (s + 1))
    (hgst : S.E.t_GST ≤ slotStart S.E.Δ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    {w : V} {mr : Nat}
    (hmr : M.support_cutoff S.E s ≤ (x[mr].time : Int))
    (hmrc : (x[mr].time : Int) ≤ M.confirmation_time S.E s)
    (hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s))
    (hwh : w ∉ Sched.adv (slotStart S.E.Δ s))
    {B : Block V}
    (hheads : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ H : Block V,
      Restated.gfHeadFrom M S (x[m][q].st) s ⇢ H ∧ ∃ X : Block V,
      X.root = H.root ∧ Block.Preceq B X ∧ X.slot ≤ s ∧
        Block.find? (x[mr][w].st).st.core.T X.root = some X ∧
        ∃ σ : Stamp, (x[mr][w].st).st.core.timestamp_block X = some σ ∧
          σ < ((M.support_cutoff S.E s : Int) : Stamp))
    (hneTickVote : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (slotStart S.E.Δ s) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (slotStart S.E.Δ s) x[n] w) (slotStart S.E.Δ s) ⇢ out) :
    ∀ e, Restated.Vocabulary.Protocol.confVotes M S.E (Restated.confStoreAt M S (x[mr][w].st) s) s ⇢ e →
      Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E
        (Restated.confStoreAt M S (x[mr][w].st) s).T e e
        (Restated.Vocabulary.Protocol.confLate M S.E (Restated.confStoreAt M S (x[mr][w].st) s) s)
        s (Restated.HonSlot M S Sched s) (fun X => Block.Preceq B X) := by
  intro e he
  refine Restated.Vocabulary.Proofs.Optimistic.coneSupport_of_named_votes facts
    (Restated.majority_of_committeeSleepinessW facts S Sched hcs hanchor)
    (Restated.confVotes_subset_confLate facts S.E _ s e he) (Finset.Subset.refl _) ?_ ?_
  · intro q _ hqH
    refine Restated.no_equiv_of_subset_pool facts S Sched x hexec
      (Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hqH hmrc) (w := w) (s := s) ?_
    intro u hu _
    rw [← facts.hd.Sts_setClock_core_pool S.E (x[mr][w].st).st (M.confirmation_time S.E s) s]
    exact confVotes_subset_pool_cone S.E _ s e he hu
  · intro q _ hqH
    obtain ⟨H, hH, X, hXroot, hBX, hXs, hfind, σ, hσ, hσlt⟩ := hheads q hqH
    have hu : Restated.gfVoteFrom M S (x[m][q].st) q s ⇢ (⟨q, s, X.root⟩ : GoldfishVote V) := by
      rw [hXroot]
      exact returns_map_intro_cone (fun H : Block V => (⟨q, s, H.root⟩ : GoldfishVote V)) _ H hH
    obtain ⟨hpoolX, τ, hτ, hτlt⟩ :=
      Restated.fresh_vote_in_pool facts S Sched x hexec hsync htd hs hgst hm
        (Restated.awake_of_mem_HonSlot facts S Sched s hqH) ((Restated.mem_HonSlot facts).mp hqH).2.1
        (Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hqH hmrc) hmr hawT hwh
        (hneTickVote q hqH) hneTick
        (grade1_at_vote_tick_cone facts S Sched x hm ((Restated.mem_HonSlot facts).mp hqH).1
          (fun t ht hmem => ((Restated.mem_HonSlot facts).mp hqH).2.2 (hmono t _
            (le_trans ht (facts.sch.Sts_vote_time_le_confirmation_time S s)) hmem))) _ hu
    have hfind' : Block.find? (Restated.confStoreAt M S (x[mr][w].st) s).T X.root = some X := by
      rw [Restated.confStoreAt, facts.hd.Sts_setClock_core_T]
      exact hfind
    have hpool' : (⟨q, s, X.root⟩ : GoldfishVote V) ∈
        (M.store_pool (Restated.confStoreAt M S (x[mr][w].st) s) s) := by
      rw [Restated.confStoreAt, facts.hd.Sts_setClock_core_pool]
      exact hpoolX
    have hτ' : (Restated.confStoreAt M S (x[mr][w].st) s).timestamp_vote ⟨q, s, X.root⟩
        = some τ := by
      rw [Restated.confStoreAt, facts.hd.setClock_core_timestamp_vote]
      exact hτ
    have hσ' : (Restated.confStoreAt M S (x[mr][w].st) s).timestamp_block X = some σ := by
      rw [Restated.confStoreAt, facts.hd.setClock_core_timestamp_block]
      exact hσ
    refine ⟨X, hBX, hXs, ?_, hfind'⟩
    refine Restated.mem_confVotes_of facts S.E _ (u := ⟨q, s, X.root⟩) hpool'
      hτ' hτlt hfind' hXs hσ' hσlt ?_ e he
    intro u' hu' hidx
    have hu'' : u' ∈ (M.store_pool (x[mr][w].st).st.core s) := by
      rw [← facts.hd.Sts_setClock_core_pool S.E (x[mr][w].st).st (M.confirmation_time S.E s) s]
      exact hu'
    exact Restated.gfVote_unique_of_honest facts S Sched x hexec
      (Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hqH hmrc) (s := s) hu'' hpoolX
      hidx rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under the hypotheses of `coneSupport_at_confirmation`, if the votes of the late set are valid
    for slot `s`, the outcome `A` of the confirmation anchor is an ancestor of `B`, and `B`'s chain
    from `A` lies in the confirmation tree, then every head of `w`'s slot-`s` confirmation walk from
    `A` is a descendant of `B`. -/
theorem confirmed_hop (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    {s : Slot} (hs : 0 < s) (hanchor : tE ≤ slotStart S.E.Δ (s + 1))
    (hgst : S.E.t_GST ≤ slotStart S.E.Δ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    {w : V} {mr : Nat}
    (hmr : M.support_cutoff S.E s ≤ (x[mr].time : Int))
    (hmrc : (x[mr].time : Int) ≤ M.confirmation_time S.E s)
    (hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s))
    (hwh : w ∉ Sched.adv (slotStart S.E.Δ s))
    {B : Block V}
    (hheads : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ H : Block V,
      Restated.gfHeadFrom M S (x[m][q].st) s ⇢ H ∧ ∃ X : Block V,
      X.root = H.root ∧ Block.Preceq B X ∧ X.slot ≤ s ∧
        Block.find? (x[mr][w].st).st.core.T X.root = some X ∧
        ∃ σ : Stamp, (x[mr][w].st).st.core.timestamp_block X = some σ ∧
          σ < ((M.support_cutoff S.E s : Int) : Stamp))
    (contract : M.Contract)
    (hvalid : Protocol.VoteSetValid S.E s
      (Restated.Vocabulary.Protocol.confLate M S.E (Restated.confStoreAt M S (x[mr][w].st) s) s))
    (A : Block V)
    (hA : Restated.Vocabulary.Protocol.confAnchorWith M contract S.E S.hc
      (Restated.confStoreAt M S (x[mr][w].st) s) ⇢ A)
    (hAB : Block.Preceq A B)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A →
      Block.Preceq C B → C ∈ Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[mr][w].st) s))
    (hneTickVote : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (slotStart S.E.Δ s) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (slotStart S.E.Δ s) x[n] w) (slotStart S.E.Δ s) ⇢ out) :
    ∀ e, Restated.Vocabulary.Protocol.confVotes M S.E (Restated.confStoreAt M S (x[mr][w].st) s) s ⇢ e →
      ∀ sc : Block V → ℕ, (∀ C, M.goldfish_score S.E (Restated.confStoreAt M S (x[mr][w].st) s).T
          e e s C ⇢ sc C) →
      ∀ X, M.ghost A (Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[mr][w].st) s))
          sc (fun C => decide (Restated.Vocabulary.Protocol.confCount M S.E
            (Restated.confStoreAt M S (x[mr][w].st) s) s < 2 * sc C)) ⇢ X →
        Block.Preceq B X := by
  intro e he sc hsc X hX
  have hsup := Restated.coneSupport_at_confirmation facts S Sched x hexec hsync htd hmono hcs
    hs hanchor hgst hm hmr hmrc hawT hwh hheads hneTickVote hneTick e he
  exact facts.fc.ghost_passes_cone S.E (Restated.confStoreAt M S (x[mr][w].st) s).T
    (Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[mr][w].st) s)) e e
    (Restated.Vocabulary.Protocol.confLate M S.E (Restated.confStoreAt M S (x[mr][w].st) s) s) s
    (Restated.HonSlot M S Sched s)
    hsup.majority hsup.counted hsup.sub hsup.no_equiv hsup.vote hvalid hAB hpath sc hsc X hX

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `n` is the tick at slot `s`'s confirmation instant, `w` is awake and not held by the
    adversary there, `w`'s tick at step `n` has an outcome, and the node state it reads passes the
    grade-2 awake test of slot `s + 1`'s round, then after the step `w`'s `live_confirmed` is the
    head `W` of the confirmation walk from `A` along the given outcomes, or the FG root of its
    clock-stamped store. -/
private theorem live_confirmed_after_confirmation_tick_cases (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {n : Nat} {s : Slot} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s)) {w : V}
    (haw : w ∈ Sched.awake (M.confirmation_time S.E s) \ Sched.adv (M.confirmation_time S.E s))
    (hneTickConf : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w) (M.confirmation_time S.E s) ⇢ out)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) w
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w) (M.round_of S.hc (s + 1)))
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n][w].st).st.core)
      (M.confirmation_time S.E s) (x[n][w].st).cache ⇢ c)
    (A : Block V) (hA : Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
      (Restated.confStoreAt M S (x[n][w].st) s) ⇢ A)
    (e : Finset (GoldfishVote V))
    (he : Restated.Vocabulary.Protocol.confVotes M S.E (Restated.confStoreAt M S (x[n][w].st) s) s ⇢ e)
    (sc : Block V → ℕ)
    (hsc : ∀ C, M.goldfish_score S.E (Restated.confStoreAt M S (x[n][w].st) s).T e e s C ⇢ sc C)
    (W : Block V)
    (hW : M.ghost A (Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[n][w].st) s))
      sc (fun C => decide (Restated.Vocabulary.Protocol.confCount M S.E
        (Restated.confStoreAt M S (x[n][w].st) s) s < 2 * sc C)) ⇢ W) :
    (x[n + 1][w].st).st.core.live_confirmed = W ∨
      (x[n + 1][w].st).st.core.live_confirmed
        = Restated.Vocabulary.Protocol.confRoot M (Restated.confStoreAt M S (x[n][w].st) s) := by
  have _hr_0 : M.reachedNode (x[n][w].st) := Record.reachedNode_sts facts S Sched x n w
  have _hr_1 : M.reachedNode (Record.wakeStage M Sched (M.support_cutoff S.E (s + 1)) x[n] w) := Record.reachedNode_wakeStage facts S Sched x n w (M.support_cutoff S.E (s + 1))
  obtain ⟨t', hlbl, ht'⟩ := id hn
  have hct := facts.sch.confirmation_time_eq_support_cutoff_succ S.E s
  have hdvd : (t' : Int) % S.E.Δ = 0 := by
    rw [ht', hct]
    exact facts.sch.support_cutoff_emod_delta S (s + 1)
  have haw' : w ∈ Sched.awake (t' : Int) \ Sched.adv (t' : Int) := by rw [ht']; exact haw
  rcases Restated.st_succ_of_tick_awake facts S Sched x w hlbl haw' hdvd with
    ⟨out₁, hout, hst⟩ | ⟨hno, -⟩
  · rw [hst]
    rw [ht', hct] at hout
    rw [hct] at hc
    obtain ⟨D, hD⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
      S.hc (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))) (s + 1 - 1)
    obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core (s + 1 - 1)
    have hc' : M.onPhaseTick S.E S.hc
        (Record.wakeStage M Sched (M.support_cutoff S.E (s + 1)) x[n] w).st.core.toHealing
        (M.support_cutoff S.E (s + 1))
        (Record.wakeStage M Sched (M.support_cutoff S.E (s + 1)) x[n] w).cache ⇢ c := by
      rw [Record.wakeStage_st facts, Record.wakeStage_cache facts]; exact hc
    have hD' : M.duties_update_confirmation_with (M.gradeContract c) S.E S.hc
        (M.ns_setClock S.E (Record.wakeStage M Sched (M.support_cutoff S.E (s + 1)) x[n] w).st
          (M.support_cutoff S.E (s + 1))) (s + 1 - 1) ⇢ D := by
      rw [Record.wakeStage_st facts]; exact hD
    rw [hct] at hrun
    rw [facts.nd.on_tick_emit_confirmation_of_outcomes (Setup.alwaysAwake S) w _
        (s + 1) (Nat.succ_pos s) out₁ hout c hc' D hD' hrun,
      facts.dt.named_update_confirmation_with_core _ _ _ _ _ D hD X hX]
    rw [Nat.add_sub_cancel] at hX
    obtain ⟨tm, htm, rfl⟩ := confVotes_cases S.E _ s he
    have hconf : Restated.confStoreAt M S (x[n][w].st) s
        = (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core := by
      rw [Restated.confStoreAt, hct]
    rw [hconf] at hA htm hsc hW ⊢
    exact facts.hd.update_confirmation_with_live_confirmed_walk_or_fgRoot _ _ _ _ _ tm htm A hA
      sc hsc W hW X hX
  · obtain ⟨o, ho⟩ := hneTickConf
    rw [← ht'] at ho
    exact absurd ho (hno o)

/-- Right after the tick at slot `s`'s confirmation instant, a receiver `w` awake from the slot's
    start to that instant and honest through it holds as its `live_confirmed` either a descendant of
    `B` or the FG root of its own clock-stamped store. The hypotheses `hneTickVote`, `hneTick` and
    `hneTickConf` say that the ticks the proof reads have an outcome, and `hrun` that `w`'s tick at
    step `n` passes the grade-2 awake test of slot `s + 1`'s round. -/
theorem live_confirmed_cases_of_cone (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    {s : Slot} (hs : 0 < s) (hanchor : tE ≤ slotStart S.E.Δ (s + 1))
    (hgst : S.E.t_GST ≤ slotStart S.E.Δ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    {w : V} {n : Nat} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s))
    (hawTc : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.confirmation_time S.E s))
    (hwh : HonestThroughTime Sched (M.confirmation_time S.E s) w)
    {B : Block V}
    (hheads : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ H : Block V,
      Restated.gfHeadFrom M S (x[m][q].st) s ⇢ H ∧ ∃ X : Block V,
      X.root = H.root ∧ Block.Preceq B X ∧ X.slot ≤ s ∧
        Block.find? (x[n][w].st).st.core.T X.root = some X ∧
        ∃ σ : Stamp, (x[n][w].st).st.core.timestamp_block X = some σ ∧
          σ < ((M.support_cutoff S.E s : Int) : Stamp))
    (hvalid : Protocol.VoteSetValid S.E s
      (Restated.Vocabulary.Protocol.confLate M S.E (Restated.confStoreAt M S (x[n][w].st) s) s))
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n][w].st).st.core)
      (M.confirmation_time S.E s) (x[n][w].st).cache ⇢ c)
    (A : Block V) (hA : Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
      (Restated.confStoreAt M S (x[n][w].st) s) ⇢ A)
    (hAB : Block.Preceq A B)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A →
      Block.Preceq C B → C ∈ Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[n][w].st) s))
    (hneTickVote : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ n' : Nat, Restated.tickStepAt M x n' (slotStart S.E.Δ s) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (slotStart S.E.Δ s) x[n'] w) (slotStart S.E.Δ s) ⇢ out)
    (hneTickConf : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w) (M.confirmation_time S.E s) ⇢ out)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) w
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w) (M.round_of S.hc (s + 1))) :
    Block.Preceq B (x[n + 1][w].st).st.core.live_confirmed ∨
      (x[n + 1][w].st).st.core.live_confirmed
        = Restated.Vocabulary.Protocol.confRoot M (Restated.confStoreAt M S (x[n][w].st) s) := by
  have hd := S.E.Δ_pos
  have hsc : M.support_cutoff S.E s = slotStart S.E.Δ s + 2 * S.E.Δ :=
    support_cutoff_eq_of_pos facts S.E hs
  have hct : M.confirmation_time S.E s = slotStart S.E.Δ s + 6 * S.E.Δ :=
    (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s).symm
  obtain ⟨hnsucc, hnself⟩ := Restated.tickStepAt_time facts x hn
  have hd1 : (1 : Int) ≤ S.E.Δ := Int.add_one_le_iff.mpr hd
  have hmr : M.support_cutoff S.E s ≤ (x[n].time : Int) := by
    rw [hsc]; rw [hct] at hnself; linarith
  have hmrc : (x[n].time : Int) ≤ M.confirmation_time S.E s := by
    rw [hct]; rw [hct] at hnself; linarith
  have hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s) :=
    awakeThroughout_shrink Sched hawTc
      (facts.sch.Sts_support_cutoff_le_confirmation_time S.E s)
  have haw : w ∈ Sched.awake (M.confirmation_time S.E s) :=
    mem_awake_of_awakeThroughout Sched hawTc (by rw [hct]; linarith) (le_refl _)
  obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty (Restated.confStoreAt M S (x[n][w].st) s)
  obtain ⟨e, he⟩ : ∃ e, Restated.Vocabulary.Protocol.confVotes M S.E
      (Restated.confStoreAt M S (x[n][w].st) s) s ⇢ e :=
    ⟨_, returns_map_intro_cone _ _ _ (returns_map_intro_cone _ _ _ htm)⟩
  obtain ⟨sc, hsc⟩ : ∃ sc : Block V → ℕ, ∀ C,
      M.goldfish_score S.E (Restated.confStoreAt M S (x[n][w].st) s).T e e s C ⇢ sc C :=
    ⟨fun C => Classical.choose (facts.fc.goldfish_score_nonempty S.E _ e e s C),
      fun C => Classical.choose_spec (facts.fc.goldfish_score_nonempty S.E _ e e s C)⟩
  obtain ⟨W, hW⟩ := facts.fc.ghost_nonempty A
    (Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[n][w].st) s)) sc
    (fun C => decide (Restated.Vocabulary.Protocol.confCount M S.E
      (Restated.confStoreAt M S (x[n][w].st) s) s < 2 * sc C))
  have hlc := live_confirmed_after_confirmation_tick_cases facts S Sched x hn
    (Finset.mem_sdiff.2 ⟨haw, hwh _ (le_refl _)⟩) hneTickConf hrun c hc A hA e he sc hsc W hW
  have hhop := Restated.confirmed_hop facts S Sched x hexec hsync htd hmono hcs hs hanchor hgst
    hm hmr hmrc hawT (hwh _ (by rw [hct]; linarith)) hheads (M.gradeContract c) hvalid A hA hAB
    hpath hneTickVote hneTick e he sc hsc W hW
  rcases hlc with hl | hl
  · exact Or.inl (by rw [hl]; exact hhop)
  · exact Or.inr hl

end

end DecoupledConsensusModel.Sts.Restated
