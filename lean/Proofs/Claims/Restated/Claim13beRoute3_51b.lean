import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_47
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Vocabulary_Execution_Acceptance
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Confirmation
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_AcceptanceTiming
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockAdmission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_HMaxMonotone
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_JustificationBound
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Objects
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Goldfish_ForkChoice
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Adoption
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Confirmation
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterInterference
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25

/-!
# SG targets, vote duties and the opening cone-root lock along a path

Theorems over a model `M : Record.Model V` and its facts, read along a path `W` of the run: the
vote-duty processed trees and FG roots, run blocks and their ancestors, and the construction of the
opening cone-root lock from a fixed-frontier certificate. A store strictly before a time `t` is the
store in `W (strictEventIndex rho t)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-! ### Helpers -/

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event at index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict_p51b (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)) (t : Time) :
    Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t =
      Record.stateBeforeOf M S rho (strictEventIndex rho t) := by
  have hpre : rho.events.filter (fun e => decide (e.time < t)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
  show (rho.events.filter (fun e => decide (e.time < t))).foldlM (Record.worldStepOf M S)
      (fun v => M.initial S v) =
    (rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length).foldlM
      (Record.worldStepOf M S) (fun v => M.initial S v)
  rw [← hpre]

/-- In a run sorted by key, along every path `W` of `rho`, the world `W (strictEventIndex rho t)` is
    a world strictly before `t`. -/
private theorem mem_stateBeforeTime_along_p51b {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict_p51b S rho hsorted]
  exact (hW _).1

/-- Along a path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` lead to
    from `W m`. -/
private theorem onePath_reach_p51b {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (m : Nat) :
    ∀ k : Nat, W (m + k) ∈ ((rho.events.drop m).take k).foldlM (Record.worldStepOf M S) (W m) := by
  intro k
  induction k with
  | zero => exact Set.mem_singleton _
  | succ k ih =>
    have hstep := (hW (m + k)).2
    rw [Nat.add_sub_cancel_left] at hstep
    rw [List.take_add, List.foldlM_append, Set.bind_def, List.drop_drop]
    refine Set.mem_iUnion₂.mpr ⟨W (m + k), ih, ?_⟩
    rw [← Nat.add_assoc]
    exact hstep

/-- Along a path `W` of `rho`, for `m ≤ n`, `W n` is among the worlds the events `m` to `n - 1` lead
    to from `W m`. -/
private theorem onePath_reach_le_p51b {S : Setup V} {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {m n : Nat} (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach_p51b W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

omit [DecidableEq V] [Fintype V] in
private theorem strictEventIndex_mono_p51b (rho : Record.Run V) {d t : Time} (hdt : d ≤ t) :
    strictEventIndex rho d ≤ strictEventIndex rho t :=
  (List.monotone_filter_right rho.events (fun e he => by
    simp only [decide_eq_true_eq] at he ⊢
    exact lt_of_lt_of_le he hdt)).length_le

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event among the first `strictEventIndex rho t` events has a time
    before `t`. -/
private theorem time_lt_of_lt_strict_p51b {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {j : Nat} {e : Record.Event V} (he : rho.events[j]? = some e) {t : Time}
    (hj : j < strictEventIndex rho t) : e.time < t := by
  have hpre : rho.events.filter (fun f => decide (f.time < t)) =
      rho.events.take (rho.events.filter (fun f => decide (f.time < t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e' f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
  have hj' : j < (rho.events.filter (fun f => decide (f.time < t))).length := hj
  have hmem : e ∈ rho.events.filter (fun f => decide (f.time < t)) := by
    rw [hpre]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj']; exact he)
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hmem).2

/-- The store the tick at `t` hands its first duty is the core store of `n`'s store with its clock
    set to `t`. -/
private theorem tickStore_eq_p51b (facts : Record.Facts M) (S : Setup V) (n : M.N) (t : Time) :
    Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t =
      (M.ns_setClock S.E n.st t).core := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]

/-- The store the slot-`s` vote duty reads is the core store of `n`'s store with its clock set to
    the slot-`s` vote instant. -/
private theorem voteStore_eq_p51b (facts : Record.Facts M) (S : Setup V) (n : M.N) (s : Slot) :
    Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core s =
      (M.ns_setClock S.E n.st (M.vote_time S.E s)).core := by
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_eq_p51b facts]

/-- Setting the clock of `n`'s store keeps the tree, the block stamps and the `h_max` of its core
    store. -/
private theorem setClock_frame_p51b (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (t : Time) :
    (M.ns_setClock S.E n.st t).core.T = n.st.core.T ∧
      (M.ns_setClock S.E n.st t).core.timestamp_block = n.st.core.timestamp_block ∧
      (M.ns_setClock S.E n.st t).core.h_max = n.st.core.h_max :=
  ⟨facts.hd.Sts_setClock_core_T _ _ _, facts.hd.setClock_core_timestamp_block _ _ _,
    facts.hd.setClock_core_h_max _ _ _⟩

/-- Setting the clock of `st` keeps the FG root of its core store. -/
private theorem setClock_fgRoot_p51b (facts : Record.Facts M) (S : Setup V) (st : M.NS)
    (t : Time) :
    M.get_fg_root (M.toHealing (M.ns_setClock S.E st t).core).toFG =
      M.get_fg_root (M.toHealing st.core).toFG := by
  rw [facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_fg_root_toHealing_clock _ _ _

open scoped DC in
private theorem returns_map_intro_p51b {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨.ok a, h, rfl⟩

open scoped DC in
private theorem returns_map_elim_p51b {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

/-- Every outcome of the early confirmation votes of `st` at slot `s` is among its late confirmation
    votes. -/
private theorem confEarly_subset_late_p51b (facts : Record.Facts M) (E : Env V) (st : M.S)
    (s : Slot) :
    ∀ e, Restated.Vocabulary.Protocol.confEarly M E st s ⇢ e →
      e ⊆ Restated.Vocabulary.Protocol.confLate M E st s := by
  intro e he u hu
  obtain ⟨τ, hτ, rfl⟩ := returns_map_elim_p51b _ _ _ he
  rw [beforeCutoff, Finset.mem_filter] at hu
  refine DecoupledConsensusModel.Protocol.beforeCutoff_mono _
    (facts.sch.Protocol_support_cutoff_le_confirmation_time E s) _ ?_
  rw [beforeCutoff, Finset.mem_filter]
  exact ⟨hu.1, facts.sto.stampedBefore_vote_of_tau st τ hτ hu.2⟩

/-- A genuine confirmation of `B` by `st` at slot `s` passes the eligibility test along one outcome
    of the early confirmation votes and one choice of Goldfish scores. -/
private theorem genuine_eligible_p51b (facts : Record.Facts M) {contract : M.Contract}
    {E : Env V} {hc : Protocol.HealConfig} {st : M.S} {s : Slot} {B : Block V}
    (hB : Restated.Vocabulary.Protocol.GenuineConfirmation M (contract := contract) E hc st s B) :
    ∃ (early : Finset (GoldfishVote V)) (sc : Block V → Nat),
      Restated.Vocabulary.Protocol.confEarly M E st s ⇢ early ∧
      Restated.Vocabulary.Protocol.confVotes M E st s ⇢
        early.filter (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true) ∧
      (∀ B', M.goldfish_score E st.T
        (early.filter (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true))
        (early.filter (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true))
        s B' ⇢ sc B') ∧
      M.voters_count E (Restated.Vocabulary.Protocol.confLate M E st s) s < 2 * sc B := by
  obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty st
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty contract E hc st.toHealing
    (M.round_of hc st.s)
  have hearly : Restated.Vocabulary.Protocol.confEarly M E st s ⇢
      beforeCutoff tm (M.support_cutoff E s) (st.pool s) :=
    returns_map_intro_p51b _ _ _ htm
  have hu := returns_map_intro_p51b
    (fun e => e.filter (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true))
    _ _ hearly
  choose sc hsc using fun B' => facts.fc.goldfish_score_nonempty E st.T
    ((beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
      (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true))
    ((beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
      (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true)) s B'
  obtain ⟨H, hH⟩ := facts.fc.ghost_nonempty R (Restated.Vocabulary.Protocol.confTree M st) sc
    (fun B' => decide (Restated.Vocabulary.Protocol.confCount M E st s < 2 * sc B'))
  have helig := hB.genuine R hR _ hu sc hsc H hH
  obtain ⟨st', hst'⟩ := facts.dt.update_confirmation_with_nonempty contract E hc st s
  have hW := facts.hd.update_confirmation_with_live_confirmed_of_eligible contract E hc st s tm htm
    R hR sc hsc H hH helig st' hst'
  have hBH : B = H := (hB.selected st' hst').symm.trans hW
  subst hBH
  exact ⟨_, sc, hearly, hu, hsc, of_decide_eq_true helig⟩

/-- The round-`r` action read from `before` can give some node state. -/
private theorem actionReadFrom_nonempty_p51b (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

/-- For every slot `s`, `slotStart s + 2Δ ≤ support_cutoff s`. -/
private theorem slotStart_add_two_delta_le_support_cutoff_p51b (facts : Record.Facts M)
    (S : Setup V) (s : Slot) :
    slotStart S.E.Δ s + 2 * S.E.Δ ≤ M.support_cutoff S.E s := by
  have hd := S.E.Δ_pos
  have hvt := facts.sch.slotStart_add_delta_eq_vote_time S.E s
  have hp0 : slotStart S.E.Δ s ≤ M.proposal_time S.E s :=
    slotStart_le_of_le_slotOf S (facts.sch.Sts_proposal_time_nonneg S s)
      (le_of_eq (facts.sch.slotOf_proposal_time S.E s).symm)
  have hpv := facts.sch.proposal_time_lt_vote_time S.E s
  have hc0 : slotStart S.E.Δ s ≤ M.support_cutoff S.E s :=
    slotStart_le_of_le_slotOf S (le_of_lt (facts.sch.support_cutoff_pos S s))
      (le_of_eq (facts.sch.slotOf_support_cutoff S.E s).symm)
  have hcp := facts.sch.support_cutoff_ne_proposal_time S.E s
  have hcv := facts.sch.support_cutoff_ne_vote_time S.E s
  obtain ⟨a, ha⟩ := Int.dvd_of_emod_eq_zero (slotStart_emod_delta S s)
  obtain ⟨b, hb⟩ := Int.dvd_of_emod_eq_zero (facts.sch.proposal_time_emod_delta_inclX S.E s)
  obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero (facts.sch.support_cutoff_emod_delta S s)
  rw [ha, hb] at hp0
  rw [← hvt, ha, hb] at hpv
  rw [ha, hc] at hc0
  rw [hc, hb] at hcp
  rw [← hvt, hc, ha] at hcv
  rw [ha, hc]
  have hab : a ≤ b := le_of_mul_le_mul_left hp0 hd
  have hba : b < a + 1 :=
    lt_of_mul_lt_mul_left (by rw [mul_add, mul_one]; exact hpv) (le_of_lt hd)
  have hbeq : b = a := by omega
  subst hbeq
  have hac : b ≤ c := le_of_mul_le_mul_left hc0 hd
  have hc1 : c ≠ b := fun h => hcp (by rw [h])
  have hc2 : c ≠ b + 1 := fun h => hcv (by rw [h, mul_add, mul_one])
  have hc3 : b + 2 ≤ c := by omega
  nlinarith

/-- For every slot `s`, `vote_time s + Δ ≤ support_cutoff s`. -/
private theorem vote_time_add_delta_le_support_cutoff_p51b (facts : Record.Facts M)
    (S : Setup V) (s : Slot) :
    M.vote_time S.E s + S.E.Δ ≤ M.support_cutoff S.E s := by
  have h1 := slotStart_add_two_delta_le_support_cutoff_p51b facts S s
  have h2 := facts.sch.slotStart_add_delta_eq_vote_time S.E s
  linarith

/-- In a parent-closed named store, every ancestor of a body is a body. -/
private theorem ancestor_body_mem_p51b {st : M.NS}
    (hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M st)
    {A B : NamedBlock V} (hB : B ∈ st.bodies)
    (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  induction B with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq,
        decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent slot root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · have hP : parent ∈ st.bodies := by
          simpa only [NamedBlock.parent] using hpc.2 _ hB
        exact ih hP (by simpa only [NamedBlock.Preceq] using hparent)

/-- In a world `wd` strictly before `read`, a non-genesis body of `w`'s store whose erasure is the
    store's FG root has derived height less than the store's `h_max`. -/
private theorem selectedFGRoot_deriveHeight_lt_hMax_p51b (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (w : V) (read : Time) (wd : V → M.N)
    (hwd : wd ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho read)
    {R : NamedBlock V}
    (hRmem : R ∈ (wd w).st.bodies)
    (hroot : R.erase = M.get_fg_root (M.toHealing (wd w).st.core).toFG)
    (hne : R ≠ NamedBlock.genesis) :
    (M.derive_named S.E S.cfg R).h < (wd w).st.core.h_max := by
  have hco : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (wd w).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho read w wd hwd).1.1.1
  have hbelow : (wd w).st.core.h_j < (wd w).st.core.h_max :=
    Restated.Vocabulary.Proofs.NamedJustificationBound.justificationBelowMax_stateBeforeTime facts
      S rho read w wd hwd
  by_cases hgate : (wd w).st.core.h_max = (wd w).st.core.h_j + 1
  · have hRJ : R.erase = (wd w).st.core.J :=
      hroot.trans (facts.fc.get_fg_root_toHealing_of_eq _ hgate)
    obtain ⟨C, hCmem, hCJ, hChj⟩ :=
      Restated.Vocabulary.Proofs.Bridges.storeJustificationOnChain_stateBeforeTime facts S rho read w
        wd hwd
    rcases facts.cs.justified_ancestor_height S.E S.cfg C with hz | ⟨J, hJC, hJerase, hJheight⟩
    · have hJgen : (wd w).st.core.J = Block.genesis := by
        rw [← hCJ]
        exact facts.cs.justified_zero_is_genesis S.E S.cfg C hz
      have hRgen : R = NamedBlock.genesis :=
        (priv% Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicality
          DecoupledConsensusModel.Proofs.HealingSurface.rootLock_named_genesis_of_erase_genesis)
          (hRJ.trans hJgen)
      exact (hne hRgen).elim
    · have hJmem : J ∈ (wd w).st.bodies :=
        ancestor_body_mem_p51b hco.2.2.1 hCmem hJC
      have hRJerase : R.erase = J.erase :=
        hRJ.trans (hJerase.trans hCJ).symm
      have hRJnamed : R = J := hco.2.1 R hRmem J hJmem hRJerase
      calc
        (M.derive_named S.E S.cfg R).h =
            (M.derive_named S.E S.cfg J).h := by rw [hRJnamed]
        _ = (M.derive_named S.E S.cfg C).h_j := hJheight
        _ = (wd w).st.core.h_j := hChj
        _ < (wd w).st.core.h_max := hbelow
  · have hRF : R.erase = (wd w).st.core.F :=
      hroot.trans (facts.fc.get_fg_root_toHealing_of_ne _ hgate)
    obtain ⟨C, hCmem, hCF, hCFbelow⟩ :=
      Restated.Vocabulary.Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime facts S rho read w
        wd hwd
    rcases facts.csAdded.finalized_ancestor_height S.E S.cfg C with hz | ⟨F, hFC, hFerase, hFheight⟩
    · have hFgen : (wd w).st.core.F = Block.genesis := by
        rw [← hCF]
        exact facts.cs.finalized_zero_is_genesis S.E S.cfg C hz
      have hRgen : R = NamedBlock.genesis :=
        (priv% Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicality
          DecoupledConsensusModel.Proofs.HealingSurface.rootLock_named_genesis_of_erase_genesis)
          (hRF.trans hFgen)
      exact (hne hRgen).elim
    · have hFmem : F ∈ (wd w).st.bodies :=
        ancestor_body_mem_p51b hco.2.2.1 hCmem hFC
      have hRFerase : R.erase = F.erase :=
        hRF.trans (hFerase.trans hCF).symm
      have hRFnamed : R = F := hco.2.1 R hRmem F hFmem hRFerase
      calc
        (M.derive_named S.E S.cfg R).h =
            (M.derive_named S.E S.cfg F).h := by rw [hRFnamed]
        _ = (M.derive_named S.E S.cfg C).h_F := hFheight
        _ < (wd w).st.core.h_max := hCFbelow

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Proofs.HealingLemmas

/-- On the path `W` of the bundle, if every tick has an outcome, `v` is in the set for
    `support_cutoff source`, `w` in the set for `view_freeze k`, `source + 1 ≤ k`,
    `lo ≤ proposal_time source`, `vote_time (k + 1) ≤ horizon`, `B` is a genuine confirmation of
    `v`'s confirmation store of `source`, and the FG root of `w`'s slot-`k + 1` vote-duty store is
    an ancestor of `B`, then `B` is in every outcome of the voter-processed tree of that store. -/
theorem voterProcessedTarget_of_genuineConfirmation_at_laterVoteDuty_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {v w : V} {source k : Slot}
    (hv : v ∈ Hs (M.support_cutoff S.E source))
    (hw : w ∈ Hs (M.view_freeze S.E k))
    (hsourceNextLe : source + 1 ≤ k)
    (hpost : lo ≤ M.proposal_time S.E source)
    (hhor : M.vote_time S.E (k + 1) ≤ rho.horizon)
    {B : Block V} {contract : M.Contract}
    (hgenuine : Restated.Vocabulary.Protocol.GenuineConfirmation M (contract := contract) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E source)) v).st.core
        (M.confirmation_time S.E source)) source B)
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (k + 1))) w).st.core (k + 1))).toFG) B) :
    ∀ P : Finset (Block V), M.voter_processed_block_tree S.E
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (k + 1))) w).st.core (k + 1))).toFG.toSG.toGoldfishStore
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (k + 1))) w).st.core (k + 1))).s ⇢ P →
    B ∈ P := by
  intro P hP
  have hW := hf.onePath
  set nC := strictEventIndex rho (M.confirmation_time S.E source) with hnC
  set nV := strictEventIndex rho (M.vote_time S.E (k + 1)) with hnV
  set cs := Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W nC v).st.core
    (M.confirmation_time S.E source) with hcs
  have hcsFrame := setClock_frame_p51b facts S (W nC v) (M.confirmation_time S.E source)
  rw [← tickStore_eq_p51b facts] at hcsFrame
  obtain ⟨early, sc, hearlyR, -, hsc, hlt⟩ := genuine_eligible_p51b facts hgenuine
  have hel' := confEarly_subset_late_p51b facts S.E cs source early hearlyR
  choose tS htS using fun u => facts.fc.targets_under_nonempty cs.T B u
  obtain ⟨sT, hsT⟩ := facts.fc.raw_supporters_nonempty cs.T
    (early.filter (fun x => M.no_second_vote_in
      (Restated.Vocabulary.Protocol.confLate M S.E cs source) x = true))
    (early.filter (fun x => M.no_second_vote_in
      (Restated.Vocabulary.Protocol.confLate M S.E cs source) x = true)) source B
  have hmaj := (facts.fc.confirmation_adoption (E := S.E)
    (sourceTree := cs.T) (targetTree := cs.T)
    hel' rfl tS htS tS htS (fun u hu ht => Or.inl ⟨hu, ht⟩)
    (fun u hu => Or.inl (hel' (Finset.mem_filter.mp hu).1)) (sc B) (hsc B) hlt sT hsT sT hsT).2
  obtain ⟨y, hy⟩ : sT.Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨-, u, huBy, -, htargets⟩ :=
    (Restated.Vocabulary.Protocol.mem_supporters_iff facts (E := S.E) sT hsT tS htS).mp hy
  rw [facts.sch.mem_votes_by_iff] at huBy
  obtain ⟨H, hfind, -, hBH⟩ := (facts.fc.targets_under_iff (tS u) (htS u)).mp htargets
  have hdutyMem : Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W nV w).st.core (k + 1) ∈
      Restated.Vocabulary.Proofs.Optimistic.voteDutyStore M S rho w (k + 1) :=
    Set.mem_image_of_mem _ (Set.mem_image_of_mem _
      (mem_stateBeforeTime_along_p51b hf.sorted hW (M.vote_time S.E (k + 1))))
  have hslot : (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W nV w).st.core (k + 1))).s = k + 1 := by
    rw [Record.Model.HS.s, facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.Optimistic.voteDutyStore_slot facts S rho w (k + 1) _ hdutyMem
  have hdutyFrame := setClock_frame_p51b facts S (W nV w) (M.vote_time S.E (k + 1))
  rw [← voteStore_eq_p51b facts] at hdutyFrame
  rw [hslot] at hP
  by_cases hgen : H = Block.genesis
  · subst H
    have hBgen : B = Block.genesis :=
      Block.preceq_antisymm hBH (Protocol.preceq_genesis B)
    subst hBgen
    have hgenesis := Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf w
        (M.vote_time S.E (k + 1))
        (M.view_freeze S.E k)
    refine facts.fc.mem_voter_processed_block_tree_of_stamped _ _ _ ?_ ?_ P hP
    · rw [facts.sto.toHealing_gs_T, hdutyFrame.1]
      exact hgenesis.1
    · rw [Nat.add_sub_cancel, facts.sto.toHealing_gs_timestamp_block, hdutyFrame.2.1]
      exact hgenesis.2
  · have hHsource : H ∈ cs.T :=
      Proofs.HealingLemmas.find?_mem hfind
    have hearly : u ∈ early := (Finset.mem_filter.mp huBy.1).1
    obtain ⟨τ, hτ, hτearly⟩ := returns_map_elim_p51b _ _ _ hearlyR
    have hresolved : stampedBefore τ (M.support_cutoff S.E source) u = true := by
      rw [← hτearly, beforeCutoff, Finset.mem_filter] at hearly
      exact hearly.2
    have hHstamp : stampedBefore cs.timestamp_block (M.support_cutoff S.E source) H = true :=
      facts.sto.stampedBefore_block_of_tau _ hfind τ hτ hresolved
    have hHn : H ∈ (W nC v).st.core.T := by
      rw [← hcsFrame.1]
      exact hHsource
    have hstampn : stampedBefore (W nC v).st.core.timestamp_block
        (M.support_cutoff S.E source) H = true := by
      rw [← hcsFrame.2.1]
      exact hHstamp
    obtain hgen' | ⟨D, hDerase, i, hin, t, hacc⟩ :=
      Restated.Vocabulary.Protocol.acceptsAt_block_of_processed_erased facts S rho v W hW nC hHn
    · exact False.elim (hgen hgen')
    · have hd := S.E.Δ_pos
      have hpvSource := facts.sch.proposal_time_lt_vote_time S.E source
      have hvcSource := vote_time_add_delta_le_support_cutoff_p51b facts S source
      have hpostCut : lo ≤ M.support_cutoff S.E source := by
        linarith
      have htSupport : t < M.support_cutoff S.E source :=
        Restated.acceptsAt_block_lt_of_stamp_beforeOn facts S Hs Xb hf hacc
          (Nat.succ_le_of_lt hin)
            (Restated.Vocabulary.Protocol.publicTime_support_cutoff facts S source) hv hpostCut (by
              simpa only [hDerase] using hstampn)
      have hDposErase : 0 < D.erase.slot :=
        Nat.zero_lt_of_lt (Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hW
          hacc)
      have hDpos : 0 < D.slot := by
        rw [Proofs.NamedWire.erase_slot] at hDposErase
        exact hDposErase
      -- The relay to `w` is read from `vote_time k`: `t < vote_time k`, and `vote_time k + Δ` is at
      -- most `support_cutoff k`, which is before `view_freeze k`.
      have hsourceLeK : source + 1 ≤ k := hsourceNextLe
      have htVoteK : t < M.vote_time S.E k :=
        lt_of_lt_of_le htSupport ((facts.sch.support_cutoff_le_vote_time_succ S.E source).trans
          (facts.sch.vote_time_mono S.E hsourceLeK))
      have hpostVoteK : lo ≤ M.vote_time S.E k := by
        have h := facts.sch.vote_time_mono S.E (le_trans (Nat.le_succ source) hsourceLeK)
        linarith
      have hvcK := vote_time_add_delta_le_support_cutoff_p51b facts S k
      have hcfK := facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E k
      have hfvK := facts.sch.view_freeze_lt_vote_time_succ S.E k
      have hOutFreeze : M.vote_time S.E k + S.E.Δ ≤ M.view_freeze S.E k := by
        linarith
      have hOutHor : M.vote_time S.E k + S.E.Δ ≤ rho.horizon := by
        linarith
      have hwOut : w ∈ Hs (M.vote_time S.E k + S.E.Δ) := hHs _ _ hOutFreeze hw
      have hvMax : v ∈ Hs (max t lo) :=
        hHs _ _ (max_le htSupport.le hpostCut) hv
      have hroot' : Block.Preceq
          (M.get_fg_root (M.toHealing (W nV w).st.core).toFG) B := by
        have h := hroot
        rw [voteStore_eq_p51b facts, setClock_fgRoot_p51b facts] at h
        exact h
      have hadmit : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w H
          (M.vote_time S.E k + S.E.Δ) := by
        simpa only [hDerase] using
          (Restated.block_admittedBefore_of_accepted_after_cutoffOn facts
            S Hs Xb hf hHs hHsXb hvMax hwOut hDpos hacc
              htVoteK hpostVoteK rfl hOutHor
            (by
              intro j hj
              have hjVote : j ≤ nV := hj.trans (strictEventIndex_mono_p51b rho
                (by linarith))
              exact preceq_trans_Preceq
                (Restated.Vocabulary.Proofs.finalized_preceq_at_prefix_of_storeBeforeRoot_preceq facts
                  S rho hf.sorted (d := M.vote_time S.E (k + 1)) hjVote (W j) (hW j).1 (W nV)
                  (onePath_reach_le_p51b hW hjVote) hroot')
                (by rw [hDerase]; exact preceq_eq_true_iff_Preceq.1 hBH)))
      have hvisibleB := Restated.admittedBefore_ancestor_mem_and_stamp_atOn facts S Hs Xb hf
        (Γ' := M.vote_time S.E (k + 1)) hadmit (preceq_eq_true_iff_Preceq.1 hBH) (by linarith)
      refine facts.fc.mem_voter_processed_block_tree_of_stamped _ _ _ ?_ ?_ P hP
      · rw [facts.sto.toHealing_gs_T, hdutyFrame.1]
        exact hvisibleB.1
      · rw [Nat.add_sub_cancel, facts.sto.toHealing_gs_timestamp_block, hdutyFrame.2.1]
        exact _root_.DecoupledConsensusModel.Proofs.GradeCutoffMono.stampedBefore_mono _
          hOutFreeze hvisibleB.2

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Proofs.HealingLemmas

/-- If `B` is a run block read through `Xb` along `W` and `A ⪯ B`, then `A` is a run block read
    through `Xb` along `W`. -/
theorem rootLock_runBlock_ancestorOn (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} (W : Nat → V → M.N) (Xb : Finset V) {A B : NamedBlock V}
    (hB : Restated.RunBlockOn M S rho W Xb B) (hAB : NamedBlock.Preceq A B) :
    Restated.RunBlockOn M S rho W Xb A :=
  Restated.blockInRun_of_ancestorOn facts S rho W Xb hB hAB

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Proofs.HealingLemmas

/-- On the path `W` of the bundle, if `v ∈ Xb`, `B` is a run block read through `Xb`, and `B`'s
    erasure is in the tree of `v`'s store in `W i`, then `B` is a body of that store. -/
theorem rootLock_named_body_of_erased_stateBeforeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {i : Nat} {B : NamedBlock V}
    (hBrun : Restated.RunBlockOn M S rho W Xb B)
    (hBmem : B.erase ∈ (W i v).st.core.T) :
    B ∈ (W i v).st.bodies := by
  obtain ⟨D, hD, hDe⟩ := Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts
    S rho i v (W i) (hf.onePath i).1 hBmem
  have hDrun : Restated.RunBlockOn M S rho W Xb D :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb hv hD
  have hroot : D.root = B.root := by
    calc
      D.root = D.erase.root := (Proofs.NamedWire.erase_root D).symm
      _ = B.erase.root := congrArg (fun X : Block V => X.root) hDe
      _ = B.root := Proofs.NamedWire.erase_root B
  have hDB := hf.rootCollisionFree.root_injective
    D B hDrun hBrun D B (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self B)) hroot
  rw [← hDB]
  exact hD

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Proofs.HealingLemmas

/-- On the path `W` of the bundle, if `v ∈ Xb`, `B` is a run block read through `Xb`, and `B`'s
    erasure is in the tree of `v`'s store in `W (strictEventIndex rho read)`, then `B` is a body of
    that store. -/
theorem rootLock_named_body_of_erased_stateBeforeTimeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) (read : Time) {B : NamedBlock V}
    (hBrun : Restated.RunBlockOn M S rho W Xb B)
    (hBmem : B.erase ∈ (W (strictEventIndex rho read) v).st.core.T) :
    B ∈ (W (strictEventIndex rho read) v).st.bodies :=
  Restated.rootLock_named_body_of_erased_stateBeforeOn facts S Hs Xb hf hv hBrun hBmem

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Proofs.HealingLemmas

/-- On the path `W` of the bundle, if `v ∈ Xb` and `B` is a body of `v`'s store in
    `W (strictEventIndex rho read)`, then `B` is a run block read through `Xb`. -/
theorem rootLock_runBlock_of_body_stateBeforeTimeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) (read : Time) {B : NamedBlock V}
    (hB : B ∈ (W (strictEventIndex rho read) v).st.bodies) :
    Restated.RunBlockOn M S rho W Xb B :=
  Restated.runBlock_of_stateBefore_memOn facts S W Xb hv hB

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Proofs.HealingLemmas

/-- On the path `W` of the bundle, if `A` and `B` are run blocks read through `Xb` and `A`'s erasure
    is an ancestor of `B`'s, then `A`'s derived height is at most `B`'s. -/
theorem rootLock_named_height_mono_of_erase_preceqOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {A B : NamedBlock V} (hArun : Restated.RunBlockOn M S rho W Xb A)
    (hBrun : Restated.RunBlockOn M S rho W Xb B)
    (hAB : Block.Preceq A.erase B.erase) :
    (M.derive_named S.E S.cfg A).h ≤
      (M.derive_named S.E S.cfg B).h := by
  obtain ⟨A', hA'B, hA'e⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hAB
  have hA'run := Restated.rootLock_runBlock_ancestorOn facts W Xb hBrun hA'B
  have hroot : A'.root = A.root := by
    calc
      A'.root = A'.erase.root := (Proofs.NamedWire.erase_root A').symm
      _ = A.erase.root := congrArg (fun X : Block V => X.root) hA'e
      _ = A.root := Proofs.NamedWire.erase_root A
  have hA'eq := hf.rootCollisionFree.root_injective
    A' A hA'run hArun A' A (Or.inl (Proofs.NamedAncestry.named_self A'))
      (Or.inr (Proofs.NamedAncestry.named_self A)) hroot
  rw [← hA'eq]
  exact facts.cs.derive_height_mono S.E S.cfg hA'B

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Proofs.HealingLemmas

/-- On the path `W` of the bundle, if `v ∈ Xb`, `B` is a run block read through `Xb` of height at
    least `H`, `v`'s slot-`s + 1` vote-duty store has `h_max = H`, and the finality filter does not
    interfere with `B` there, then for every outcome of the cache update, the FG root of `v`'s
    slot-`s + 1` vote-duty read is an ancestor of `B`. -/
theorem openingVoteFGRoot_preceq_of_fixedFrontier_noninterferenceOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {H : Height} {v : V} (_hv : v ∈ Xb)
    {s : Slot} {B : NamedBlock V} (hBrun : Restated.RunBlockOn M S rho W Xb B)
    (hBheight : H ≤ (M.derive_named S.E S.cfg B).h)
    (hfrontier : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st.core (s + 1)).h_max = H)
    (hquiet : Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho v
      (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1)))) B.erase) :
    ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st.core.toHealing
        (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).cache ⇢ c →
      Block.Preceq
        (M.get_fg_root
          (M.toHealing (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st (M.vote_time S.E (s + 1)))
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).record c).st.core).toFG)
        B.erase := by
  intro c hc
  have hW := hf.onePath
  let read := M.vote_time S.E (s + 1)
  let wd := W (strictEventIndex rho read)
  have hwd : wd ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho read :=
    mem_stateBeforeTime_along_p51b hf.sorted hW read
  let rootRead := M.get_fg_root (M.toHealing (wd v).st.core).toFG
  have hfrontierPre : (wd v).st.core.h_max = H := by
    have h := hfrontier
    rw [voteStore_eq_p51b facts, (setClock_frame_p51b facts S _ _).2.2] at h
    exact h
  have hquietPre : B.erase ⪯ rootRead ∨ B.erase ∈
      M.get_filtered_block_tree (M.toHealing (wd v).st.core).toFG := hquiet
  have hrootPre : Block.Preceq rootRead B.erase := by
    rcases hquietPre with hBroot | hfiltered
    · by_cases hrootGenesis : rootRead = Block.genesis
      · rw [hrootGenesis]
        exact preceq_eq_true_iff_Preceq.1 (Protocol.preceq_genesis B.erase)
      · have hrootMem : rootRead ∈ (wd v).st.core.T := by
          by_cases hcase : (wd v).st.core.h_max = (wd v).st.core.h_j + 1
          · rw [show rootRead = (wd v).st.core.J from
              facts.fc.get_fg_root_toHealing_of_eq _ hcase]
            exact Restated.Vocabulary.Proofs.NamedStoreBridge.justifiedInTree_stateBeforeTime facts
              S rho read v wd hwd
          · rw [show rootRead = (wd v).st.core.F from
              facts.fc.get_fg_root_toHealing_of_ne _ hcase]
            exact Restated.Vocabulary.Proofs.NamedStoreBridge.finalizedInTree_stateBeforeTime facts
              S rho read v wd hwd
        obtain ⟨Rn, hRnMem, hRnErase⟩ :=
          Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
            read v wd hwd hrootMem
        have hRnNe : Rn ≠ NamedBlock.genesis := by
          intro hgen
          apply hrootGenesis
          rw [← hRnErase, hgen, Proofs.ModelProperties.erase_genesis]
        have hRnRun := Restated.rootLock_runBlock_of_body_stateBeforeTimeOn facts S Hs Xb hf
          _hv read hRnMem
        have hrootHeight :
            (M.derive_named S.E S.cfg Rn).h < (wd v).st.core.h_max :=
          selectedFGRoot_deriveHeight_lt_hMax_p51b facts S rho v read wd hwd hRnMem hRnErase hRnNe
        have hBrootHeight :
            (M.derive_named S.E S.cfg B).h ≤
              (M.derive_named S.E S.cfg Rn).h :=
          Restated.rootLock_named_height_mono_of_erase_preceqOn facts S Hs Xb hf hBrun hRnRun
            (by simpa only [hRnErase] using hBroot)
        exact ((not_le_of_gt hrootHeight)
          (hfrontierPre ▸ hBheight.trans hBrootHeight)).elim
    · exact preceq_eq_true_iff_Preceq.1 (facts.fc.preceq_get_fg_root_of_mem_filtered hfiltered)
  rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [setClock_fgRoot_p51b facts]
  exact hrootPre

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Proofs.HealingLemmas

/-- On the path `W` of the bundle, if more than half of each slot's committee is in the set for its
    confirmation instant, `S.a r ≤ confirmation_time s`, `C` is a run block of height less than `K`
    whose erasure is an ancestor of every round-`r` action SG target of the set for `S.a r`, the
    canonicality of round `r` at slot `s` holds, and `B` is a run block of height at least `K` into
    whose cone slot `s`'s committee votes, then `C`'s erasure is an ancestor of `B`'s. -/
theorem rootLock_commonActionPrefix_preceqOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {K : Height} {r : Round} {s : Slot} {C B : NamedBlock V}
    (hrs : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ M.confirmation_time S.E s)
    (hCrun : Restated.RunBlockOn M S rho W Xb C)
    (hCheight : (M.derive_named S.E S.cfg C).h < K)
    (hCtargets : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r,
        let gc := M.gradeContract n.cache
        let st := M.toHealing n.st.core
        let kk := M.round_of S.hc st.s
        ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st kk ⇢ A2 →
        ∀ G : Block V, M.get_sg_vote_with gc S.E S.hc st kk A2 ⇢ G → Block.Preceq C.erase G)
    (hcanonical : Restated.SGTargetConeCanonicalityOn M S rho W Hs Xb r s
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))))
    (hBrun : Restated.RunBlockOn M S rho W Xb B)
    (hBheight : K ≤ (M.derive_named S.E S.cfg B).h)
    (hBcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq B.erase X)) :
    Block.Preceq C.erase B.erase := by
  have hmajority := hcom s
  have hpos : 0 < ((S.E.committee s) ∩ Hs (M.confirmation_time S.E s)).card := by
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  have huHonest : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)) :=
    hHs _ _ hrs (Finset.mem_inter.mp hu).2
  obtain ⟨n, hn⟩ := actionReadFrom_nonempty_p51b facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨T, hT⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) A2
  have hTcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq T X) :=
    hcanonical u huHonest n hn A2 hA2 T hT
  have hCT : Block.Preceq C.erase T := hCtargets u huHonest n hn A2 hA2 T hT
  have hTBcompatible : Block.compatible T B.erase = true :=
    Restated.sgTargetCompatible_of_honestVotesConeOn facts S Hs Xb hf hHs hcom hTcone hBcone
  rcases compatible_cases hTBcompatible with hTB | hBT
  · exact preceq_trans_Preceq hCT hTB
  · have hCBcompatible : Block.compatible C.erase B.erase = true :=
      compatible_of_common_honest_goldfish_head hCT hBT
    rcases compatible_cases hCBcompatible with hCB | hBC
    · exact hCB
    · have hBheightLeC :
          (M.derive_named S.E S.cfg B).h ≤
            (M.derive_named S.E S.cfg C).h :=
        Restated.rootLock_named_height_mono_of_erase_preceqOn facts S Hs Xb hf hBrun hCrun hBC
      exact ((not_le_of_gt hCheight)
        (hBheight.trans hBheightLeC)).elim

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Proofs.HealingLemmas

/-- The conclusion of `rootLock_commonActionPrefix_preceqOn`, under the same hypotheses. -/
theorem commonActionPrefix_preceq_heightQualifiedConeTargetOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {K : Height} {r : Round} {s : Slot} {C B : NamedBlock V}
    (hrs : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ M.confirmation_time S.E s)
    (hCrun : Restated.RunBlockOn M S rho W Xb C)
    (hCheight : (M.derive_named S.E S.cfg C).h < K)
    (hCtargets : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r,
        let gc := M.gradeContract n.cache
        let st := M.toHealing n.st.core
        let kk := M.round_of S.hc st.s
        ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st kk ⇢ A2 →
        ∀ G : Block V, M.get_sg_vote_with gc S.E S.hc st kk A2 ⇢ G → Block.Preceq C.erase G)
    (hcanonical : Restated.SGTargetConeCanonicalityOn M S rho W Hs Xb r s
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))))
    (hBrun : Restated.RunBlockOn M S rho W Xb B)
    (hBheight : K ≤ (M.derive_named S.E S.cfg B).h)
    (hBcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq B.erase X)) :
    Block.Preceq C.erase B.erase :=
  Restated.rootLock_commonActionPrefix_preceqOn facts S Hs Xb hf hHs hcom hrs hCrun hCheight hCtargets
    hcanonical hBrun hBheight hBcone

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Proofs.HealingLemmas

/-- On the path `W` of the bundle, if more than half of each slot's committee is in the set for its
    confirmation instant, `v` is in the set for `support_cutoff s`, `lo ≤ vote_time s`,
    `vote_time (s + 1) ≤ horizon`, `B` is a run block of height at least `K` into whose cone slot
    `s`'s committee votes, and `v`'s slot-`s + 1` vote-duty store has `h_max = K`, then `B` is a
    body of `v`'s store strictly before `vote_time (s + 1)`. -/
theorem heightQualifiedConeTarget_mem_openingVoteRead_of_fixedFrontierOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {K : Height} {s : Slot} {B : NamedBlock V} {v : V}
    (hv : v ∈ Hs (M.support_cutoff S.E s))
    (hpost : lo ≤ M.vote_time S.E s)
    (hnextHor : M.vote_time S.E (s + 1) ≤ rho.horizon)
    (hBheight : K ≤ (M.derive_named S.E S.cfg B).h)
    (hfrontier : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st.core (s + 1)).h_max = K)
    (hBcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq B.erase X))
    (hBrun : Restated.RunBlockOn M S rho W Xb B) :
    B ∈ (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st.bodies := by
  have hW := hf.onePath
  have hmajority := hcom s
  have hpos : 0 < ((S.E.committee s) ∩ Hs (M.confirmation_time S.E s)).card := by
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  obtain ⟨hxCommittee, hxConf⟩ := Finset.mem_inter.mp hx
  have hxVote : x ∈ Hs (M.vote_time S.E s) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) hxConf
  obtain ⟨X, hBX, hXrun, hXemit⟩ := hBcone x hxVote hxCommittee
  set nX := strictEventIndex rho (M.vote_time S.E s) with hnX
  set nV := strictEventIndex rho (M.vote_time S.E (s + 1)) with hnV
  obtain ⟨cX, hcX⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W nX x).st.core.toHealing
    (M.vote_time S.E s) (W nX x).cache
  have hXmem := Restated.emittedHead_mem_voteDutyStoreOn facts S Hs Xb hf (hHsXb _ hxVote) hXrun
    hXemit cX hcX
  have hXprefix : X.erase ∈ (W nX x).st.core.T := by
    rewrite [facts.nd.mkNode_st] at hXmem; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hXmem; rw [(setClock_frame_p51b facts S _ _).1] at hXmem
    exact hXmem
  have hXbody : X ∈ (W nX x).st.bodies :=
    Restated.rootLock_named_body_of_erased_stateBeforeOn facts S Hs Xb hf (hHsXb _ hxVote) hXrun
      hXprefix
  have hXprocessed : Restated.Vocabulary.Execution.Object.processed M
      (W nX x).st (.block X) = true := by
    exact decide_eq_true hXbody
  have hvbefore : W nV ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
      (M.vote_time S.E (s + 1)) :=
    mem_stateBeforeTime_along_p51b hf.sorted hW (M.vote_time S.E (s + 1))
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho x W hW nX X hXprocessed with
    hXgen | ⟨iX, hiX, tX, hXacc⟩
  · have hBgen : B.erase = Block.genesis := by
      have hBXgen : Block.Preceq B.erase Block.genesis := by
        rw [hXgen, Proofs.ModelProperties.erase_genesis] at hBX
        exact hBX
      exact Block.preceq_antisymm (preceq_eq_true_iff_Preceq.2 hBXgen)
        (Protocol.preceq_genesis B.erase)
    rw [(priv% Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicality
      DecoupledConsensusModel.Proofs.HealingSurface.rootLock_named_genesis_of_erase_genesis)
      hBgen]
    have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (W nV v).st :=
      (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
        (M.vote_time S.E (s + 1)) v (W nV) hvbefore).1.1.1
    exact hcoh.2.2.1.1
  · obtain ⟨-, eX, heX, -, heXt⟩ := hXacc.1
    have htX : tX < M.vote_time S.E s := by
      rw [← heXt]
      exact time_lt_of_lt_strict_p51b hf.sorted heX hiX
    have hXslotPos : 0 < X.slot := by
      have hXslotPos' : 0 < X.erase.slot :=
        Nat.zero_lt_of_lt (Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hW
          hXacc)
      simpa only [Proofs.NamedWire.erase_slot] using hXslotPos'
    have hcutRead : M.support_cutoff S.E s ≤
        M.vote_time S.E (s + 1) :=
      facts.sch.support_cutoff_le_vote_time_succ S.E s
    have hsupportHor : M.support_cutoff S.E s ≤ rho.horizon :=
      hcutRead.trans hnextHor
    have hfrontierPre : (W nV v).st.core.h_max = K := by
      have h := hfrontier
      rw [voteStore_eq_p51b facts, (setClock_frame_p51b facts S _ _).2.2] at h
      exact h
    have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
    have hFhist : ∀ j ≤ (rho.events.filter (fun e => decide (e.time < M.support_cutoff S.E s))).length,
        (W j v).st.core.F.Preceq X.erase := by
      intro j hj
      have hjN : j ≤ nV := hj.trans (strictEventIndex_mono_p51b rho hcutRead)
      have hstateCap : (W j v).st.core.h_max ≤ K := by
        have hprefix : (W j v).st.core.h_max ≤ (W nV v).st.core.h_max :=
          Restated.Vocabulary.Proofs.HealingSurface.stateBefore_hMax_mono facts S rho v hjN (W j)
            (hW j).1 (W nV) (onePath_reach_le_p51b hW hjN)
        rw [← hfrontierPre]
        exact hprefix
      obtain ⟨D, hD, hDF, hDbound⟩ :=
        Restated.Vocabulary.Proofs.Bridges.storeFinalizationOnChain_stateBefore facts S rho j v (W j)
          (hW j).1
      have hDrun : Restated.RunBlockOn M S rho W Xb D :=
        Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hv) hD
      have hBXheight :
          (M.derive_named S.E S.cfg B).h ≤
            (M.derive_named S.E S.cfg X).h :=
        Restated.rootLock_named_height_mono_of_erase_preceqOn facts S Hs Xb hf hBrun hXrun hBX
      have hcrossed : (M.derive_named S.E S.cfg D).h_F <
          (M.derive_named S.E S.cfg X).h := by
        exact lt_of_lt_of_le (hDbound.trans_le hstateCap)
          (hBheight.trans hBXheight)
      have hpreceq := Restated.finalized_preceq_of_height_ltOn facts
        S rho W Xb X D hsb hf.rootCollisionFree hXrun hDrun hcrossed
      simpa only [hDF] using hpreceq
    have hxMax : x ∈ Hs (max tX lo) :=
      hHs _ _ (max_le htX.le hpost) hxVote
    have hvcS := vote_time_add_delta_le_support_cutoff_p51b facts S s
    have hvOut : v ∈ Hs (M.vote_time S.E s + S.E.Δ) := hHs _ _ hvcS hv
    have hXadmit : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W v X.erase
        (M.vote_time S.E s + S.E.Δ) :=
      Restated.block_admittedBefore_of_accepted_after_cutoffOn facts
        S Hs Xb hf hHs hHsXb hxMax hvOut hXslotPos hXacc htX hpost rfl
          (hvcS.trans hsupportHor)
          (fun j hj => hFhist j (hj.trans (strictEventIndex_mono_p51b rho hvcS)))
    have hXtarget : X.erase ∈ (W nV v).st.core.T :=
      (Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hXadmit
        (hvcS.trans hcutRead)).1
    have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
        (M.vote_time S.E (s + 1)) v (W nV) hvbefore
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
    rw [facts.sto.toHealing_gs_T] at hpc
    have hBtarget : B.erase ∈ (W nV v).st.core.T :=
      Proofs.Records.mem_of_preceq hpc.2
        B.erase X.erase hXtarget (preceq_eq_true_iff_Preceq.2 hBX)
    exact Restated.rootLock_named_body_of_erased_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hv)
      (M.vote_time S.E (s + 1)) hBrun hBtarget

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Proofs.HealingLemmas

/-- On the path `W` of the bundle, if more than half of each slot's committee is in the set for its
    confirmation instant, the validators outside the set for the horizon weigh less than a third,
    `S.a r ≤ confirmation_time s`, the canonicality of round `r` at slot `s` holds, `C` is a run
    block certified at height `K - 1`, of height less than `K` and an ancestor of every round-`r`
    action SG target, `lo ≤ vote_time s`, `vote_time (s + 1) ≤ horizon`, and every member of the set
    for `vote_time (s + 1)` has `h_max = K` at its slot-`s + 1` vote duty, then the opening
    cone-root lock at `K` holds for round `r` and slot `s`. -/
theorem sgTargetOpeningConeRootLock_of_fixedFrontier_certifiedPrefixOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : Execution.BelowOneThird S (Hs rho.horizon))
    {K : Height} {r : Round} {s : Slot} {C : NamedBlock V}
    (hrs : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ M.confirmation_time S.E s)
    (hcanonical : Restated.SGTargetConeCanonicalityOn M S rho W Hs Xb r s
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))))
    (hCrun : Restated.RunBlockOn M S rho W Xb C)
    (hcert : Restated.CertificateOn M S rho W Xb (K - 1) C.root)
    (hCheight : (M.derive_named S.E S.cfg C).h < K)
    (hCtargets : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r,
        let gc := M.gradeContract n.cache
        let st := M.toHealing n.st.core
        let kk := M.round_of S.hc st.s
        ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st kk ⇢ A2 →
        ∀ G : Block V, M.get_sg_vote_with gc S.E S.hc st kk A2 ⇢ G → Block.Preceq C.erase G)
    (hpost : lo ≤ M.vote_time S.E s)
    (hreadHor : M.vote_time S.E (s + 1) ≤ rho.horizon)
    (hfrontier : ∀ v ∈ Hs (M.vote_time S.E (s + 1)),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st.core (s + 1)).h_max = K) :
    Restated.SGTargetOpeningConeRootLockOn M S rho W Hs Xb K r s
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))))
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))) := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  refine ⟨hcanonical, ?_⟩
  intro B hBrun hBheight hBcone v hv c hc
  have hvCut : v ∈ Hs (M.support_cutoff S.E s) :=
    hHs _ _ (facts.sch.support_cutoff_le_vote_time_succ S.E s) hv
  have hCB : Block.Preceq C.erase B.erase :=
    Restated.commonActionPrefix_preceq_heightQualifiedConeTargetOn facts
      S Hs Xb hf hHs hcom hrs hCrun hCheight hCtargets hcanonical hBrun hBheight hBcone
  have hBmem := Restated.heightQualifiedConeTarget_mem_openingVoteRead_of_fixedFrontierOn facts
    S Hs Xb hf hHs hHsXb hcom hvCut hpost hreadHor hBheight (hfrontier v hv) hBcone hBrun
  have hvbefore := mem_stateBeforeTime_along_p51b hf.sorted hf.onePath (M.vote_time S.E (s + 1))
  have hBtarget : B.erase ∈
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st.core.T := by
    have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st :=
      (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
        (M.vote_time S.E (s + 1)) v _ hvbefore).1.1.1
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hBmem
  have hfrontierPre :
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st.core.h_max = K := by
    have h := hfrontier v hv
    rw [voteStore_eq_p51b facts, (setClock_frame_p51b facts S _ _).2.2] at h
    exact h
  have hquiet :=
    Restated.finalityFilterNoninterferenceAtRead_of_fixedFrontier_certifiedPrefixOn facts
      (C := C.erase) S Hs Xb hf hHs hHsXb hfb hsb hv hreadHor hBtarget hBmem rfl hBrun
        hBheight hfrontierPre rfl hCrun
        (by simpa only [Proofs.NamedWire.erase_root] using hcert) hCB
  exact Restated.openingVoteFGRoot_preceq_of_fixedFrontier_noninterferenceOn facts
    S Hs Xb hf (hHsXb _ hv) hBrun hBheight (hfrontier v hv) hquiet c hc

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Proofs.HealingLemmas

end

end DecoupledConsensusModel.Sts.Restated
