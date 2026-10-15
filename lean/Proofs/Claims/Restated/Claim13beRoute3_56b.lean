import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_52b
import Proofs.Claims.Restated.Claim13beRoute3_53
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Claim13beRoute3_55
import Proofs.Claims.Restated.Claim13beRoute3_56
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Adoption
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ReaderLocalCone
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Adoption
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterRetention
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_ReaderLocalCone
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25

/-!
# Persisted grades, exact-height attempts and next-slot vote cones

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`, read along the path
`W` of the bundle `AdmissibleFieldsOn`: a persisted named grade gives the timeout wait at a later
opening, an exact-height attempt on a descendant of a fixed justification root's justified block
raises the largest `h_max`, the fixed-root target data and prepared parent of an opening proposal,
and a confirmed block carried into the next slot's vote cone.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event at index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₅₆b (S : Setup V) (rho : Record.Run V)
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

/-- In a run sorted by key, the world of a path `W` before the event at index
    `strictEventIndex rho t` is a world strictly before `t`. -/
private theorem mem_stateBeforeTime_along₅₆b {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₅₆b S rho hsorted]
  exact (hW _).1

/-- For a path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of `rho`
    lead to from `W m`. -/
private theorem onePath_reach₅₆b {S : Setup V} {rho : Record.Run V}
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

/-- For a path `W` of `rho` and `m ≤ n`, `W n` is among the worlds the events `m` to `n - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_slice₅₆b {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₅₆b W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- The round-`r` action read from `before` has a node state on which the grade-2 block read can
    return some `g` and the SG vote selector on `g` some block. -/
private theorem exists_actionSG₅₆b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      ∃ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g ∧
        ∃ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  refine ⟨M.mkNode st before.record c, ⟨c, hc, st, hst, rfl⟩, ?_⟩
  obtain ⟨g, hg⟩ := facts.dt.grade2_block_with_nonempty
    (M.gradeContract (M.mkNode st before.record c).cache) S.E S.hc
    (M.toHealing (M.mkNode st before.record c).st.core)
    (M.round_of S.hc (M.toHealing (M.mkNode st before.record c).st.core).s)
  obtain ⟨B, hB⟩ := facts.dt.get_sg_vote_with_nonempty
    (M.gradeContract (M.mkNode st before.record c).cache) S.E S.hc
    (M.toHealing (M.mkNode st before.record c).st.core)
    (M.round_of S.hc (M.toHealing (M.mkNode st before.record c).st.core).s) g
  exact ⟨g, hg, B, hB⟩

/-- Setting the clock of `st` to `t` leaves the FG root of its core store unchanged. -/
private theorem setClock_fgRoot₅₆b (facts : Record.Facts M) (S : Setup V) (st : M.NS)
    (t : Time) :
    M.get_fg_root (M.toHealing (M.ns_setClock S.E st t).core).toFG =
      M.get_fg_root (M.toHealing st.core).toFG := by
  rw [facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_fg_root_toHealing_clock _ _ _

/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₅₆b {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₅₆b {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff₅₆b {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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

/-- Every outcome of the early confirmation votes of `st` at slot `s` is a subset of the late
    confirmation votes. -/
private theorem confEarly_subset_late₅₆b (facts : Record.Facts M) (E : Env V) (st : M.S) (s : Slot) :
    ∀ e, Restated.Vocabulary.Protocol.confEarly M E st s ⇢ e →
      e ⊆ Restated.Vocabulary.Protocol.confLate M E st s := by
  intro e he u hu
  obtain ⟨τ, hτ, rfl⟩ := returns_map_elim₅₆b _ _ _ he
  rw [beforeCutoff, Finset.mem_filter] at hu
  refine DecoupledConsensusModel.Protocol.beforeCutoff_mono _
    (facts.sch.Protocol_support_cutoff_le_confirmation_time E s) _ ?_
  rw [beforeCutoff, Finset.mem_filter]
  exact ⟨hu.1, facts.sto.stampedBefore_vote_of_tau st τ hτ hu.2⟩

/-- If `B` satisfies `GenuineConfirmation` for `st` at slot `s`, then for some outcome of the early
    confirmation votes and some choice of Goldfish scores, those votes are an outcome of the
    confirmation votes and the count of the late voters is less than twice the score of `B`. -/
private theorem genuine_eligible₅₆b (facts : Record.Facts M) {contract : M.Contract} {E : Env V}
    {hc : Protocol.HealConfig} {st : M.S} {s : Slot} {B : Block V}
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
    returns_map_intro₅₆b _ _ _ htm
  have hu := returns_map_intro₅₆b
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

/-- If the adoption transport holds for `B` from the source tree to the target tree, `g` is an
    outcome of `B`'s Goldfish score over the source votes with the late voter count less than
    `2 * g`, the target support votes are among the target votes, and `A` is compatible with `B`
    with every block strictly between them in `tree`, then `B` is an ancestor of every outcome of
    the Goldfish fork choice from `A`. -/
private theorem captures_of_confirmation_one₅₆b (facts : Record.Facts M)
    (E : Env V) (σ : Block V → M.CS) (h_max : Height)
    (sourceTree targetTree tree : Finset (Block V)) (cur : Slot)
    (sourceEarly sourceLate sourceVotes targetVotes targetSupport :
      Finset (GoldfishVote V)) (s : Slot) {A B : Block V}
    (hN : Restated.Vocabulary.Protocol.Numerator M sourceEarly sourceLate sourceVotes)
    (hT : Restated.Vocabulary.Protocol.AdoptionTransport M sourceTree targetTree sourceVotes sourceLate
      targetVotes targetSupport B)
    (g : ℕ) (hg : M.goldfish_score E sourceTree sourceVotes sourceVotes s B ⇢ g)
    (heligible : M.voters_count E sourceLate s < 2 * g)
    (hsub : targetSupport ⊆ targetVotes)
    (hcompatible : Block.compatible A B = true)
    (hpath : Block.Preceq A B →
      ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B →
        C ∈ tree) :
    ∀ X : Block V, M.goldfish_fork_choice E σ h_max targetTree cur A tree
        targetVotes targetSupport s ⇢ X → Block.Preceq B X := by
  intro X hX
  have hS := fun u => facts.fc.targets_under_nonempty sourceTree B u
  have hTt := fun u => facts.fc.targets_under_nonempty targetTree B u
  let tS : GoldfishVote V → Bool := fun u => Classical.choose (hS u)
  let tT : GoldfishVote V → Bool := fun u => Classical.choose (hTt u)
  have htS : ∀ u, M.targets_under sourceTree B u ⇢ tS u := fun u => Classical.choose_spec (hS u)
  have htT : ∀ u, M.targets_under targetTree B u ⇢ tT u := fun u => Classical.choose_spec (hTt u)
  obtain ⟨sS, hsS⟩ := facts.fc.raw_supporters_nonempty sourceTree sourceVotes sourceVotes s B
  obtain ⟨sT, hsT⟩ := facts.fc.raw_supporters_nonempty targetTree targetVotes targetSupport s B
  have hforward : ∀ u ∈ sourceVotes, tS u = true →
      (u ∈ targetSupport ∧ tT u = true) ∨ M.equivocates targetVotes u.val_index = true := by
    intro u hu htu
    rcases hT.forward u hu (tS u) (htS u) htu with ⟨hmem, hall⟩ | heq
    · exact Or.inl ⟨hmem, hall (tT u) (htT u)⟩
    · exact Or.inr heq
  have hadopt := facts.fc.confirmation_adoption hN.early_late hN.filtered tS htS tT htT hforward
    hT.backward g hg heligible sS hsS sT hsT
  exact facts.fc.goldfish_fork_choice_captures_supporter_majority E σ h_max targetTree tree cur
    targetVotes targetSupport s hsub sT hsT hadopt.2 hcompatible hpath X hX

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

/-- If every member of `Hs (domain q .g2)` has `P` active with grade `true` in the world of `W`
    before that time, `reader` is in that set and `S.a q ≤ read`, then `P` is in `reader`'s store in
    `W (strictEventIndex rho read)`. -/
private theorem formsW_processedAtRead₅₆b (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {q : Round} {P : Block V}
    (hformsW : ∀ v ∈ Hs (M.domain S.E S.hc q .g2),
      P ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) v).st q .g2 P ⇢ b → b = true)
    {reader : V} (hreader : reader ∈ Hs (M.domain S.E S.hc q .g2))
    {read : Time} (hle : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ read) :
    P ∈ (W (strictEventIndex rho read) reader).st.T := by
  have hdle : M.domain S.E S.hc q .g2 ≤ read := (facts.gr.domain_le_a S q .g2).trans hle
  have hsource : P ∈
      (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) reader).st.core.T := by
    have hfiltered := (hformsW reader hreader).1
    have htree := facts.fc.get_filtered_block_tree_subset _ hfiltered
    rw [facts.sto.toHealing_gs_T] at htree
    exact htree
  have hmn : strictEventIndex rho (M.domain S.E S.hc q .g2) ≤ strictEventIndex rho read :=
    Restated.strict_filter_length_mono rho hdle
  exact Restated.Vocabulary.Proofs.stateBefore_T_subset facts S rho reader
    _ (hf.onePath _).1 _ hmn _ (onePath_slice₅₆b W hf.onePath hmn) hsource

/-- If every member of `Hs (domain r .g2)` has `C` active with grade `true` in the world of `W`
    before that time, `v ∈ Hs (domain r .g0)`, and `C` is active at a node state `n` of `v`'s
    round-`r` action read, then `C` is an ancestor of every SG vote `n` can select. -/
private theorem formsW_preceq_actionSGBlockAt₅₆b (facts : Record.Facts M) (S : Setup V)
    {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon) {C : Block V}
    (hformsW : ∀ v ∈ Hs (M.domain S.E S.hc r .g2),
      C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st r .g2 C ⇢ b → b = true)
    {v : V} (hv : v ∈ Hs (M.domain S.E S.hc r .g0))
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hactive : C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∀ A2 : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2 →
    ∀ G : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ G → Block.Preceq C G := by
  have hvG2 : v ∈ Hs (M.domain S.E S.hc r .g2) :=
    hHs _ _ (facts.gr.domain_le_domain_g0 S r .g2) hv
  set d := W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v with hd
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing d.st.core))
    d.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) C
  have hbtrue : b = true := (hformsW v hvG2).2 b hb
  subst hbtrue
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  have hGq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 := by
    unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 Restated.Vocabulary.Internal.PhaseGrades.nodeRead
    exact returns_map_intro₅₆b (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2) _ G hG
  obtain ⟨Q, hQ, hCQ⟩ :=
    Restated.preceq_actionQ2_of_domainGradeOn facts S Hs Xb hf hHs hr hhor hv hlo
      (hformsW v hvG2).1 hb n hn hactive _ hGq
  rw [hQ] at hGq
  exact Restated.preceq_actionSGBlockAt_of_actionQ2On facts S Hs Xb hf hHs hHsXb hr hhor
    (hHs _ _ (facts.gr.domain_le_domain_g0 S r .g1) hv) hlo n hn hGq hCQ

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if `0 < entry`, `entry + 2 + delayExtra ≤ proposal`, the opening
    proposal of round `entry` can return the run block `B`, `B`'s erasure has the named grade of
    round `proposal − 1` in the world of `W` and is active at the next opening proposer's
    round-`(proposal − 1)` action read, that action time is inside the horizon, the lifecycle packet
    of round `proposal − 1` holds with proposal `Q` whose parent `P` is at `B`'s height, and
    `lo ≤ opening (proposal − 1 − η_SG)`, then every parent of `Q` has its target slot plus the
    timeout delay at most round `proposal`'s opening slot. -/
theorem opening_timeoutMature_of_persistedGradeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {delayExtra : Nat}
    (hdelay : TimeoutDelayBound S delayExtra)
    {entry proposal : Round} {B Q P : NamedBlock V}
    (hentry : 0 < entry)
    (hspace : entry + 2 + delayExtra ≤ proposal)
    (hentryBlock : some B ∈
      Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho ((M.opening_slot S.hc entry)))
    (hBRun : Restated.RunBlockOn M S rho W Xb B)
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc (proposal - 1) .g2),
      B.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (proposal - 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (proposal - 1) .g2)) v).st
          (proposal - 1) .g2 B.erase ⇢ b → b = true)
    (hactive : ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (proposal - 1)))
          (S.E.proposer ((M.opening_slot S.hc proposal)))) (proposal - 1),
      B.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n)
    (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S (proposal - 1)) ≤ rho.horizon)
    {w₁ w₂ : V → M.N}
    (hpacket : Restated.NamedSGProposalLifecyclePacketOn M S rho W
      (fun t => W (strictEventIndex rho t)) w₁ w₂ Hs Xb (proposal - 1)
      ((M.opening_slot S.hc proposal) - 1) Q)
    (hparent : NamedBlock.parent? Q = some P)
    (hsameHeight : (M.derive_named S.E S.cfg P).h =
      (M.derive_named S.E S.cfg B).h)
    (hlo : lo ≤ M.opening S.E S.hc
      (proposal - 1 - S.hc.η_SG)) :
    ∀ P' : NamedBlock V, NamedBlock.parent? Q = some P' →
      (M.derive_named S.E S.cfg P').T_h.slot + S.cfg.timeoutDelay ≤ M.opening_slot S.hc proposal := by
  have hentrySucc : entry + 1 ≤ entry + 2 + delayExtra := by
    exact (Nat.add_le_add_left (by decide : 1 ≤ 2) entry).trans
      (Nat.le_add_right (entry + 2) delayExtra)
  have hproposal : 0 < proposal :=
    (Nat.zero_lt_succ entry).trans_le (hentrySucc.trans hspace)
  have hproposalTwo : 2 ≤ proposal := by
    exact (Nat.le_add_left 2 entry).trans
      ((Nat.le_add_right (entry + 2) delayExtra).trans hspace)
  have hpred : proposal - 1 + 1 = proposal := Nat.sub_add_cancel hproposal
  have hproposalQ : ∃ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc proposal)))
          (S.E.proposer (M.opening_slot S.hc proposal))).st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc proposal))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc proposal)))
          (S.E.proposer (M.opening_slot S.hc proposal))).cache ⇢ c ∧
      M.proposal_with (M.gradeContract c) Protocol.ProposalRowSource.poolAndCarried S.E S.hc
        (S.node (S.E.proposer (M.opening_slot S.hc proposal)))
        (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc proposal)))
            (S.E.proposer (M.opening_slot S.hc proposal))).st
          (M.proposal_time S.E (M.opening_slot S.hc proposal))) ⇢ some Q := by
    have h := hpacket.lifecycle.proposal
    rw [hpred] at h
    exact h
  obtain ⟨c, hc, hoQ⟩ := hproposalQ
  let v := S.E.proposer ((M.opening_slot S.hc proposal))
  have hvConf : v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc proposal))) := by
    have h := hpacket.lifecycle.proposerHonest
    rw [hpred] at h
    exact h
  have hactionConf : (Restated.Vocabulary.Execution.Setup.a M S (proposal - 1)) ≤
      M.confirmation_time S.E ((M.opening_slot S.hc proposal)) :=
    ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
        (Nat.sub_lt hproposal (by decide)))).trans
      (facts.sch.proposal_time_le_confirmation_time S.E _)
  have hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (proposal - 1))) := hHs _ _ hactionConf hvConf
  have hvDom : v ∈ Hs (M.domain S.E S.hc (proposal - 1) .g0) :=
    hHs _ _ (facts.gr.domain_le_a S (proposal - 1) .g0) hv
  obtain ⟨n, hn, A2, hA2, G, hG⟩ := exists_actionSG₅₆b facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (proposal - 1))) v) (proposal - 1)
  have hBG : Block.Preceq B.erase G :=
    formsW_preceq_actionSGBlockAt₅₆b facts S Hs Xb hf hHs hHsXb
      (r := proposal - 1) (Nat.sub_pos_of_lt (Nat.lt_of_succ_le hproposalTwo))
      hactionHor hforms hvDom n hn (hactive n hn) hlo A2 hA2 G hG
  have htarget : Block.Preceq G P.erase := by
    have hnp : M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc proposal))) v).st
        (M.proposal_time S.E (M.opening_slot S.hc proposal)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc proposal))) v).record c ∈
        Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho (M.opening_slot S.hc proposal) :=
      ⟨W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc proposal))),
        mem_stateBeforeTime_along₅₆b hf.sorted hf.onePath _, c, hc, rfl⟩
    have ho : M.proposal_with (M.gradeContract (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc proposal))) v).st
        (M.proposal_time S.E (M.opening_slot S.hc proposal)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc proposal))) v).record c).cache)
      .poolAndCarried S.E S.hc (S.node v) (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc proposal))) v).st
        (M.proposal_time S.E (M.opening_slot S.hc proposal)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc proposal))) v).record c).st
        ⇢ some Q := by
      rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]
      exact hoQ
    obtain ⟨input, hinput⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract (M.mkNode
        (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc proposal))) v).st
        (M.proposal_time S.E (M.opening_slot S.hc proposal)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc proposal))) v).record c).cache)
      S.E S.hc (S.node v) (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc proposal))) v).st
        (M.proposal_time S.E (M.opening_slot S.hc proposal)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc proposal))) v).record c).st.core)
    obtain ⟨p, hp, hperase⟩ :=
      Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_parent facts S rho _ _ hnp ho input hinput
    have hpP : p = P := Option.some.inj (hp.symm.trans hparent)
    subst hpP
    have h := hpacket.actionTargetParent v hv n hn A2 hA2 G hG
    rw [hpred] at h
    rw [facts.nd.mkNode_cache] at hinput
    have h' := h c hc input hinput
    rw [hperase]
    exact h'
  have hBtarget : Block.Preceq B.erase P.erase :=
    preceq_trans_Preceq hBG htarget
  obtain ⟨B', hB'P, hB'erase⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift P hBtarget
  have hPrun : Restated.RunBlockOn M S rho W Xb P :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hpacket.lifecycle.runBlock
      ((priv% Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HeightProgressLadder
        DecoupledConsensusModel.Proofs.HealingSurface.namedParent_preceq_of_parent?) hparent)
  have hB'run : Restated.RunBlockOn M S rho W Xb B' :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hPrun hB'P
  have hrootEq : B'.root = B.root := by
    rw [← Proofs.NamedWire.erase_root B', ← Proofs.NamedWire.erase_root B, hB'erase]
  have hB'eq : B' = B :=
    hf.rootCollisionFree.root_injective B' B hB'run hBRun B' B
      (Or.inl (Proofs.NamedAncestry.named_self B'))
      (Or.inr (Proofs.NamedAncestry.named_self B)) hrootEq
  exact Restated.laterOpening_timeoutMature_of_sameHeightOn facts
    S Hs Xb hf hdelay hentry hspace hentryBlock
      (mem_stateBeforeTime_along₅₆b hf.sorted hf.onePath _) c hc hoQ hparent
      (by simpa only [hB'eq] using hB'P) hsameHeight

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W` and the weight bound, if a store before `read0` has a fixed-height
    justification root at `Mh` whose justified block is an ancestor of `B`, round `q > 0` is a
    carrier round, the run block `B` of height `Mh` has the named grade of round `q − 1` and is in
    the filtered trees of the members of `Hs` at the reads of rounds `q − 1` and `q`,
    `S.E.t_GST ≤ S.a (q − 1)`, the proposal of `q`'s opening slot with the cache outcome `c` is
    mature, `S.a q ≤ endpoint ≤ rho.horizon`, `lo ≤ S.a (q − 1)`, `lo ≤ opening (q − 1 − η_SG)`, and
    the members of `Hs (S.a (q − 1) + Δ)` are awake at `q − 1`, then `Mh` is less than the largest
    `h_max` over `Hs endpoint`. -/
theorem exactHeightAttempt_rise_of_rebasedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {u : V} {read0 : Time}
    (hroot : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb Mh u read0
      (W (strictEventIndex rho read0)))
    {q : Round} (hq : 0 < q) {B : NamedBlock V}
    (hcarrier : Restated.ProposerCarrierAtOn M S Hs q)
    (hformsPrev : ∀ v ∈ Hs (M.domain S.E S.hc (q - 1) .g2),
      B.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v).st (q - 1) .g2 B.erase ⇢ b →
            b = true)
    (hwindowPrev : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      B.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) w).st.core).toFG)
    (hdomainWindow : ∀ w ∈ Hs (M.domain S.E S.hc q .g2),
      B.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) w).st.core).toFG)
    (hBRun : Restated.RunBlockOn M S rho W Xb B)
    (hBheight : (M.derive_named S.E S.cfg B).h = Mh)
    (hpostPrev : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    {P : NamedBlock V}
    (hmature : ∀ Pp : NamedBlock V, NamedBlock.parent? P = some Pp →
      (M.derive_named S.E S.cfg Pp).T_h.slot + S.cfg.timeoutDelay ≤ M.opening_slot S.hc q)
    (hactiveAtAction : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      B.erase ∈ M.get_filtered_block_tree
        (M.toHealing (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) w).st.core).toFG)
    (hJB : Block.Preceq (W (strictEventIndex rho read0) u).st.J B.erase)
    {endpoint : Time} (hactionEnd : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ endpoint)
    (hendHor : endpoint ≤ rho.horizon)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hloOpen : lo ≤ M.opening S.E S.hc (q - 1 - S.hc.η_SG))
    (hA : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S w (W j w) (q - 1))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c)
    (hP : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some P) :
    Mh < ((Hs endpoint).sup fun v => (W (inclusiveEventIndex rho endpoint) v).st.core.h_max) := by
  rcases Restated.activeExactHeightOpening_fixedInterference_or_hMaxRiseOn facts
      S Hs Xb hf hHs hHsXb hfb hq hcarrier hformsPrev hwindowPrev hdomainWindow hBRun
        hBheight hpostPrev hmature hactiveAtAction hactionEnd hendHor hlo hloOpen hA c hc hP with
    hrise | hfixed
  · exact hrise
  · exfalso
    have h₁ := hroot.fixedTarget
    have h₂ := hfixed.1.fixedTarget
    have hrootEq := h₁.uniqueAtHeight _ h₂.certificate
    have hJeq := Restated.runBlockOf_root_uniqueOn_FixedHeightRootAdmission facts Hs Xb hf
      h₂.targetBlock h₁.targetBlock hrootEq
    have hcompatible : Block.compatible
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st.core.J B.erase = true := by
      rw [hJeq]
      exact Proofs.ModelProperties.compatible_eq_true_of_Preceq hJB
    rw [h₂.incompatible] at hcompatible
    exact Bool.false_ne_true hcompatible

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if `B` has the named grade of round `base ≤ q` in the world of `W`,
    `B` is a run block of height at least `Mh − 1` whose erasure descends from the justified block
    of `u`'s store before `read0`, and every member of `Hs (S.a q)` has before `S.a q` that
    justified block as FG root and `h_max = Mh`, then `B`'s erasure is in the filtered tree of each
    such member's store before `S.a q`. -/
theorem fixedRootGrade_mem_filtered_action_of_noRiseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {u : V} {read0 : Time} {base q : Round}
    {B : NamedBlock V}
    (hseed : ∀ v ∈ Hs (M.domain S.E S.hc base .g2),
      B.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc base .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc base .g2)) v).st base .g2 B.erase ⇢ b →
            b = true)
    (hbase : base ≤ q)
    (hBRun : Restated.RunBlockOn M S rho W Xb B)
    (hJB : Block.Preceq (W (strictEventIndex rho read0) u).st.J B.erase)
    (hBheight : Mh - 1 ≤ (M.derive_named S.E S.cfg B).h)
    (hfixed : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      M.get_fg_root
          (M.toHealing (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core).toFG =
        (W (strictEventIndex rho read0) u).st.J ∧
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core.h_max = Mh) :
    ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      B.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core).toFG := by
  intro v hv
  have hle : (Restated.Vocabulary.Execution.Setup.a M S base) ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hbase
  have hvDom : v ∈ Hs (M.domain S.E S.hc base .g2) :=
    hHs _ _ ((facts.gr.domain_le_a S base .g2).trans hle) hv
  have hprocessed : B.erase ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core.T :=
    formsW_processedAtRead₅₆b facts S Hs Xb hf hseed hvDom hle
  exact Restated.fixedRootGrade_mem_filtered_of_exactRootOn facts
    S Hs Xb hf (hHsXb _ hv) hBRun hprocessed hJB hBheight
      (hfixed v hv).1 (hfixed v hv).2

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W` and the weight bound, if `u`'s store before `read0` has a
    fixed-height justification root at `Mh`, the run block `B` of height at least `Mh − 1`
    descending from its justified block has the named grade of round `q1 + 1`,
    `S.E.t_GST ≤ read0 ≤ S.a q1`, `q1 + 1 ≤ q'`, `S.a q'` is inside the horizon with the largest
    `h_max` over `Hs (S.a q')` at most `Mh`, every member of `Hs (S.a r')` keeps that FG root and
    `h_max = Mh` for every round `r'` from `q1 + 1` to `q'`, `lo ≤ read0`,
    `lo ≤ opening (q1 + 1 − η_SG)` and the awake tests hold, then `B` has the named grade of every
    round from `q1 + 1` to `q'` and is in the filtered tree of every member of `Hs (S.a q')` before
    `S.a q'`. -/
theorem gradeFormsAt_persist_of_fixedRoot_noRiseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {u : V} {read0 : Time}
    (hroot : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb Mh u read0
      (W (strictEventIndex rho read0)))
    {q1 q' : Round} {B : NamedBlock V}
    (hseed : ∀ v ∈ Hs (M.domain S.E S.hc (q1 + 1) .g2),
      B.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q1 + 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q1 + 1) .g2)) v).st (q1 + 1) .g2
            B.erase ⇢ b → b = true)
    (hBRun : Restated.RunBlockOn M S rho W Xb B)
    (hpostRoot : S.E.t_GST ≤ read0)
    (hreadBase : read0 ≤ (Restated.Vocabulary.Execution.Setup.a M S q1))
    (hwindow : q1 + 1 ≤ q')
    (hendpoint : (Restated.Vocabulary.Execution.Setup.a M S q') ≤ rho.horizon)
    (hcapEnd : ((Hs (Restated.Vocabulary.Execution.Setup.a M S q')).sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q')) v).st.core.h_max) ≤ Mh)
    (hJB : Block.Preceq (W (strictEventIndex rho read0) u).st.J B.erase)
    (hBheight : Mh - 1 ≤ (M.derive_named S.E S.cfg B).h)
    (hfixed : ∀ r', q1 + 1 ≤ r' → r' ≤ q' → ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r')),
      M.get_fg_root
          (M.toHealing (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r')) v).st.core).toFG =
        (W (strictEventIndex rho read0) u).st.J ∧
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r')) v).st.core.h_max = Mh)
    (hlo : lo ≤ read0)
    (hloOpen : lo ≤ M.opening S.E S.hc (q1 + 1 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S w (W j w) k) :
    (∀ r', q1 + 1 ≤ r' → r' ≤ q' → ∀ v ∈ Hs (M.domain S.E S.hc r' .g2),
      B.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r' .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc r' .g2)) v).st r' .g2 B.erase ⇢ b →
            b = true) ∧
    ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q')),
      B.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q')) v).st.core).toFG := by
  have hmajority : HonestWeightMajorityOn S rho Hs :=
    honestWeightMajorityOn_of_belowOneThirdOn hfb
  have hneEnd : (Hs ((Restated.Vocabulary.Execution.Setup.a M S q'))).Nonempty :=
    nonempty_of_honestWeightMajority_l54 (hmajority _ hendpoint)
  have hmono := (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
  have hactiveAction : ∀ r', q1 + 1 ≤ r' → r' ≤ q' →
      ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r')),
        B.erase ∈ M.get_filtered_block_tree (M.toHealing
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r')) v).st.core).toFG := by
    intro r' hbase hr'end
    exact Restated.fixedRootGrade_mem_filtered_action_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hseed hbase hBRun hJB hBheight (hfixed r' hbase hr'end)
  have hforms : ∀ r', q1 + 1 ≤ r' → r' ≤ q' → ∀ v ∈ Hs (M.domain S.E S.hc r' .g2),
      B.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r' .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc r' .g2)) v).st r' .g2 B.erase ⇢ b →
            b = true := by
    intro r'
    induction r' using Nat.strong_induction_on with
    | h r' ih =>
        intro hbase hr'end
        rcases eq_or_lt_of_le hbase with hEq | hlt
        · subst r'
          exact hseed
        · cases r' with
          | zero => exact (Nat.not_lt_zero _ hlt).elim
          | succ r =>
              have hbasePrev : q1 + 1 ≤ r := Nat.le_of_lt_succ hlt
              have hrendPrev : r ≤ q' := (Nat.le_succ r).trans hr'end
              have hformsPrev := ih r (Nat.lt_succ_self r) hbasePrev hrendPrev
              have hq1lt : q1 < r + 1 := (Nat.lt_succ_self q1).trans_le hbase
              have hdelay : read0 + S.E.Δ ≤ M.domain S.E S.hc (r + 1) .g2 :=
                (Int.add_le_add_right hreadBase S.E.Δ).trans
                  ((facts.gr.action_delta_le_early S S.hc.R_ge_three hq1lt).trans
                    (facts.gr.early_le_domain S (r + 1)))
              have hactionEnd : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤
                  (Restated.Vocabulary.Execution.Setup.a M S q') := hmono hr'end
              have hdomLt := Restated.domain_add_delta_lt_action_l56 facts S (r + 1) .g2
              have hdomainHor : M.domain S.E S.hc (r + 1) .g2 ≤ rho.horizon := by
                linarith [S.E.Δ_pos]
              have hloDom : lo ≤ M.domain S.E S.hc (r + 1) .g2 := by
                linarith [S.E.Δ_pos]
              have hdomainCap : ((Hs (M.domain S.E S.hc (r + 1) .g2)).sup fun v =>
                  (W (inclusiveEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) v).st.core.h_max) ≤ Mh :=
                (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hloDom
                  (lt_of_lt_of_le hdomLt hactionEnd) hendpoint hneEnd).trans hcapEnd
              have hactionDomain : (Restated.Vocabulary.Execution.Setup.a M S r) ≤
                  M.domain S.E S.hc (r + 1) .g2 :=
                Restated.Vocabulary.Proofs.NamedOutageClosure.action_le_domain facts S S.hc.R_ge_three
                  (Nat.lt_succ_self r)
              have hactiveDomain : ∀ v ∈ Hs (M.domain S.E S.hc (r + 1) .g2),
                  B.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
                    (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) v) := by
                intro v hv
                have hfixedV :=
                  Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn
                    facts S Hs Xb hf hHs hHsXb hf.slashableBound hroot hv hlo hdelay hdomainHor
                    hdomainCap
                have hvDom : v ∈ Hs (M.domain S.E S.hc r .g2) :=
                  hHs _ _ ((facts.gr.domain_le_a S r .g2).trans hactionDomain) hv
                have hprocessed : B.erase ∈
                    (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) v).st.core.T :=
                  formsW_processedAtRead₅₆b facts S Hs Xb hf hformsPrev hvDom hactionDomain
                exact Restated.fixedRootGrade_mem_filtered_of_exactRootOn facts
                  S Hs Xb hf (hHsXb _ hv) hBRun hprocessed hJB hBheight hfixedV.1 hfixedV.2
              have hrpos : 0 < r := (Nat.zero_lt_succ q1).trans_le hbasePrev
              have hrHor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon :=
                (hmono hrendPrev).trans hendpoint
              have hloOpenR : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG) :=
                hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S
                  (Nat.sub_le_sub_right hbasePrev _))
              have hwmem := mem_stateBeforeTime_along₅₆b hf.sorted hf.onePath
                (Restated.Vocabulary.Execution.Setup.a M S r)
              have hcover : Restated.ActionCarriersCoverOn M S rho Hs r B.erase
                  (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))) := by
                intro v hv n hn A2 hA2 G hG
                have hvDom : v ∈ Hs (M.domain S.E S.hc r .g0) :=
                  hHs _ _ (facts.gr.domain_le_a S r .g0) hv
                have hactive : B.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n :=
                  Restated.Vocabulary.Proofs.HealingSurface.activeAtAction_of_retainedAtRead facts S
                    (v := v) _ hwmem (hactiveAction r hbasePrev hrendPrev v hv) n hn
                exact formsW_preceq_actionSGBlockAt₅₆b facts S Hs Xb hf hHs hHsXb hrpos hrHor
                  hformsPrev hvDom n hn hactive hloOpenR A2 hA2 G hG
              have hreadR : read0 ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
                hreadBase.trans (hmono (Nat.le_of_succ_le hbasePrev))
              have hpostPrev : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
                hpostRoot.trans hreadR
              have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) ≤
                  rho.horizon := by
                show slotStart S.E.Δ (M.opening_slot S.hc (r + 1)) - S.E.Δ ≤ rho.horizon
                rw [facts.gr.gammaNeg1_eq_domain_g2_succ S r]
                exact hdomainHor
              exact Restated.namedGradeFormsAt_succ_of_actionCarriersCover_and_next_activeOn facts
                S Hs Xb hf hHs hHsXb hmajority hcover hpostPrev hcut
                (hactiveAction (r + 1) (Nat.le_of_lt hlt) hr'end) hactiveDomain
                (hA r (Restated.lo_le_early_g2_sub_delta_of_opening facts S (Nat.succ_pos q1) hloOpen
                  hbasePrev)) (hlo.trans hreadR)
                (nonempty_of_honestWeightMajority_l54 (hmajority _ (hactionEnd.trans hendpoint)))
  exact ⟨hforms, hactiveAction q' hwindow (Nat.le_refl q')⟩

/-- Under the bundle along `W` and the weight bound, if `u`'s store before `read0` has a
    fixed-height justification root at `Mh`, the run block `B` of height `Mh` descending from its
    justified block has the named grade of round `q1 + 1`, `S.E.t_GST ≤ read0 ≤ S.a q1`,
    `q1 + 2 ≤ q`, round `q` is a carrier round whose opening proposal with the cache outcome `c` is
    mature, every member of `Hs (S.a r')` keeps that FG root and `h_max = Mh` for every round `r'`
    from `q1 + 1` to `q`, `S.a q ≤ endpoint ≤ rho.horizon`, the largest `h_max` over `Hs endpoint`
    is at most `Mh`, `lo ≤ read0`, `lo ≤ opening (q1 + 1 − η_SG)` and the awake tests hold, then
    `Mh` is less than that largest `h_max`. -/
theorem exactHeightAttempt_rise_of_rebased_of_fixedRoot_noRiseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {u : V} {read0 : Time}
    (hroot : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb Mh u read0
      (W (strictEventIndex rho read0)))
    {q1 q : Round} {B : NamedBlock V}
    (hseed : ∀ v ∈ Hs (M.domain S.E S.hc (q1 + 1) .g2),
      B.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q1 + 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q1 + 1) .g2)) v).st (q1 + 1) .g2
            B.erase ⇢ b → b = true)
    (hBRun : Restated.RunBlockOn M S rho W Xb B)
    (hpostRoot : S.E.t_GST ≤ read0)
    (hreadBase : read0 ≤ (Restated.Vocabulary.Execution.Setup.a M S q1))
    (hspacing : q1 + 2 ≤ q)
    (hcarrier : Restated.ProposerCarrierAtOn M S Hs q)
    {P : NamedBlock V}
    (hmature : ∀ Pp : NamedBlock V, NamedBlock.parent? P = some Pp →
      (M.derive_named S.E S.cfg Pp).T_h.slot + S.cfg.timeoutDelay ≤ M.opening_slot S.hc q)
    (hBheight : (M.derive_named S.E S.cfg B).h = Mh)
    (hJB : Block.Preceq (W (strictEventIndex rho read0) u).st.J B.erase)
    (hfixed : ∀ r', q1 + 1 ≤ r' → r' ≤ q → ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r')),
      M.get_fg_root
          (M.toHealing (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r')) v).st.core).toFG =
        (W (strictEventIndex rho read0) u).st.J ∧
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r')) v).st.core.h_max = Mh)
    {endpoint : Time} (hactionEnd : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ endpoint)
    (hendHor : endpoint ≤ rho.horizon)
    (hcapEnd : ((Hs endpoint).sup fun v => (W (inclusiveEventIndex rho endpoint) v).st.core.h_max) ≤ Mh)
    (hlo : lo ≤ read0)
    (hloOpen : lo ≤ M.opening S.E S.hc (q1 + 1 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S w (W j w) k)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c)
    (hP : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some P) :
    Mh < ((Hs endpoint).sup fun v => (W (inclusiveEventIndex rho endpoint) v).st.core.h_max) := by
  have hmajority : HonestWeightMajorityOn S rho Hs :=
    honestWeightMajorityOn_of_belowOneThirdOn hfb
  have hneEnd : (Hs endpoint).Nonempty :=
    nonempty_of_honestWeightMajority_l54 (hmajority _ hendHor)
  have hmono := (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
  have hstep : q1 + 1 ≤ q1 + 2 := Nat.add_le_add_left (by decide : 1 ≤ 2) q1
  have hbaseQ : q1 + 1 ≤ q := hstep.trans hspacing
  have hq : 0 < q := (Nat.zero_lt_succ q1).trans_le hbaseQ
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hbasePrev : q1 + 1 ≤ q - 1 :=
    Nat.le_sub_one_of_lt ((Nat.add_lt_add_left (by decide : 1 < 2) q1).trans_le hspacing)
  have hprevQ : q - 1 ≤ q := Nat.sub_le q 1
  have hprevAction : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤
      (Restated.Vocabulary.Execution.Setup.a M S q) := hmono hprevQ
  have hprevHor : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤ rho.horizon :=
    hprevAction.trans (hactionEnd.trans hendHor)
  have hreadPrev : read0 ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
    hreadBase.trans (hmono ((Nat.le_succ q1).trans hbasePrev))
  have hprevStep : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + 1 + S.E.Δ ≤
      (Restated.Vocabulary.Execution.Setup.a M S q) := by
    have h := Restated.action_add_one_add_delta_le_next_action_l52 facts S (q - 1)
    rw [hpred] at h
    exact h
  have hprevCap : ((Hs (Restated.Vocabulary.Execution.Setup.a M S (q - 1))).sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v).st.core.h_max) ≤ Mh :=
    (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb (hlo.trans hreadPrev)
      (by linarith) hendHor hneEnd).trans hcapEnd
  have hthin : Mh - 1 ≤ (M.derive_named S.E S.cfg B).h := by
    rw [hBheight]
    exact Nat.sub_le Mh 1
  obtain ⟨hforms, hwindowPrev⟩ := gradeFormsAt_persist_of_fixedRoot_noRiseOn facts
    S Hs Xb hf hHs hHsXb hfb hroot hseed hBRun hpostRoot hreadBase hbasePrev hprevHor
      hprevCap hJB hthin (fun r' hbase hr'end => hfixed r' hbase (hr'end.trans hprevQ))
      hlo hloOpen hA
  have hformsPrev := hforms (q - 1) hbasePrev (Nat.le_refl _)
  have hpostPrev : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
    hpostRoot.trans hreadPrev
  have hdomLt := Restated.domain_add_delta_lt_action_l56 facts S q .g2
  have hdomainHor : M.domain S.E S.hc q .g2 ≤ rho.horizon := by
    linarith [S.E.Δ_pos]
  have hdelay : read0 + S.E.Δ ≤ M.domain S.E S.hc q .g2 :=
    (Int.add_le_add_right hreadBase S.E.Δ).trans
      ((facts.gr.action_delta_le_early S S.hc.R_ge_three
        ((Nat.lt_succ_self q1).trans_le hbaseQ)).trans (facts.gr.early_le_domain S q))
  have hloDom : lo ≤ M.domain S.E S.hc q .g2 := by
    linarith [S.E.Δ_pos]
  have hdomainCap : ((Hs (M.domain S.E S.hc q .g2)).sup fun v =>
      (W (inclusiveEventIndex rho (M.domain S.E S.hc q .g2)) v).st.core.h_max) ≤ Mh :=
    (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hloDom
      (lt_of_lt_of_le hdomLt hactionEnd) hendHor hneEnd).trans hcapEnd
  have hactionDomain : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤
      M.domain S.E S.hc q .g2 :=
    Restated.Vocabulary.Proofs.NamedOutageClosure.action_le_domain facts S S.hc.R_ge_three
      (Nat.sub_lt hq Nat.one_pos)
  have hdomainWindow : ∀ v ∈ Hs (M.domain S.E S.hc q .g2),
      B.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) v).st.core).toFG := by
    intro v hv
    have hfixedV :=
      Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn
        facts S Hs Xb hf hHs hHsXb hf.slashableBound hroot hv hlo hdelay hdomainHor hdomainCap
    have hvDom : v ∈ Hs (M.domain S.E S.hc (q - 1) .g2) :=
      hHs _ _ ((facts.gr.domain_le_a S (q - 1) .g2).trans hactionDomain) hv
    have hprocessed : B.erase ∈
        (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) v).st.core.T :=
      formsW_processedAtRead₅₆b facts S Hs Xb hf hformsPrev hvDom hactionDomain
    exact Restated.fixedRootGrade_mem_filtered_of_exactRootOn facts
      S Hs Xb hf (hHsXb _ hv) hBRun hprocessed hJB hthin hfixedV.1 hfixedV.2
  have hactive := Restated.fixedRootGrade_mem_filtered_action_of_noRiseOn facts
    S Hs Xb hf hHs hHsXb hseed hbaseQ hBRun hJB hthin (hfixed q hbaseQ (Nat.le_refl q))
  exact Restated.exactHeightAttempt_rise_of_rebasedOn facts
    S Hs Xb hf hHs hHsXb hfb hroot hq hcarrier hformsPrev hwindowPrev hdomainWindow
      hBRun hBheight hpostPrev hmature hactive hJB hactionEnd hendHor (hlo.trans hreadPrev)
      (hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S
        (Nat.sub_le_sub_right hbasePrev _)))
      (hA (q - 1) (Restated.lo_le_early_g2_sub_delta_of_opening facts S (Nat.succ_pos q1) hloOpen
        hbasePrev)) c hc hP

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if `w`'s store `fixed` before `read` has a fixed-height
    justification root at `H`, `pre` is the store of the proposer of round `q`'s opening slot before
    its proposal time `t`, the proposer is in `Hs t`, `lo ≤ read`, `read + Δ ≤ t ≤ rho.horizon`, and
    the largest `h_max` over `Hs t` is at most `H`, then some run block `target` read through `Xb`
    along `W` carries the prepared target data. -/
theorem fixedRoot_preparedTargetData_of_fixedRoot_abstractOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {q : Round} (fixed pre : M.NS)
    (hfixed : (W (strictEventIndex rho read) w).st = fixed)
    (hpre : (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
      (S.E.proposer ((M.opening_slot S.hc q)))).st = pre)
    (hprop : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.proposal_time S.E ((M.opening_slot S.hc q))))
    (hpostRead : lo ≤ read)
    (hproposalDelay : read + S.E.Δ ≤
      M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hproposalHor : M.proposal_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon)
    (hproposalCap : ((Hs (M.proposal_time S.E ((M.opening_slot S.hc q)))).sup fun u =>
      (W (inclusiveEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q)))) u).st.core.h_max) ≤ H) :
    ∃ target : NamedBlock V,
      Restated.FixedRootPreparedTargetDataOn M S rho W Xb H fixed pre target := by
  obtain ⟨target, htargetErase, htargetRun, htargetHeight⟩ :=
    Restated.fixedRoot_namedTarget_of_fixedRootOn facts S Hs Xb hfix
  have htargetEraseFixed : target.erase = fixed.J := by
    rw [← hfixed]
    exact htargetErase
  obtain ⟨hroot, hmax⟩ :=
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hf.slashableBound hfix hprop hpostRead hproposalDelay hproposalHor
      hproposalCap
  have hroot' : M.get_fg_root pre.toHealing.toFG = target.erase := by
    rw [← hpre, htargetErase]
    exact hroot
  have hmax' : pre.h_max = H := by
    rw [← hpre]
    exact hmax
  exact ⟨target,
    { targetErase := htargetEraseFixed
      targetRun := htargetRun
      targetHeight := htargetHeight
      targetHeightPositive := hfix.targetHeightPositive
      rootAtProposal := hroot'
      hMaxAtProposal := hmax' }⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, the committee majority and the weight bound, if `pre` and `source`
    are the store and the duty store of the proposer of round `q`'s opening slot before its proposal
    time `t`, `0 < q`, `lo ≤ vote_time (opening_slot q − 1)`, `t` and round `q`'s cutoff `Γ_neg1`
    are inside the horizon, `lo ≤ S.a (q − 1)`, the proposer is in `Hs t`, the candidate data holds
    for the ceiling `C`, and the members of `Hs (S.a (q − 1) + Δ)` are awake at `q − 1`, then `C` is
    an ancestor of the parent of every proposal input the proposer's node state staged at `t` can
    compute. -/
theorem fixedRoot_preparedParent_of_candidate_abstractOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {w : V} {read : Time} {q : Round} {A : Block V}
    (fixed pre : M.NS) (source : M.S)
    (hpre : (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
      (S.E.proposer ((M.opening_slot S.hc q)))).st = pre)
    (hsource : Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
        (S.E.proposer ((M.opening_slot S.hc q)))).st.core
      (M.proposal_time S.E ((M.opening_slot S.hc q))) = source)
    (hq : 0 < q)
    (hpostCone : lo ≤
      M.vote_time S.E ((M.opening_slot S.hc q) - 1))
    (hproposalHor : M.proposal_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon)
    (hpostPreviousAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hprop : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.proposal_time S.E ((M.opening_slot S.hc q))))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ ((q - 1) + 1) ≤ rho.horizon)
    {Jn : NamedBlock V} {C C0 : Block V} {vC : V}
    (hdata : Restated.FixedRootPreparedParentCandidateOn M
      S rho W Hs Xb H q w read A Jn C C0 vC fixed pre source
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
          (S.E.proposer ((M.opening_slot S.hc q)))).st.core.toHealing
        (M.proposal_time S.E ((M.opening_slot S.hc q)))
        (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
          (S.E.proposer ((M.opening_slot S.hc q)))).cache ⇢ c →
    ∀ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
        (S.node (S.E.proposer ((M.opening_slot S.hc q))))
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
            (S.E.proposer ((M.opening_slot S.hc q)))).st
          (M.proposal_time S.E ((M.opening_slot S.hc q))))
          (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
            (S.E.proposer ((M.opening_slot S.hc q)))).record c).st.core) ⇢ I →
      Block.Preceq C I.parent := by
  intro c hc
  obtain ⟨hslo, _hshi, hsucc⟩ := facts.gr.lastInteriorSlot_before_opening S.hc hq
  have hs : 0 < (M.opening_slot S.hc q) - 1 := by
    exact lt_of_lt_of_le (Nat.zero_lt_succ _) (by simpa only using hslo)
  have hprevLt : q - 1 < q := Nat.sub_lt hq (by decide)
  have hqPredAdd : q - 1 + 1 = q :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq))
  have hwp := mem_stateBeforeTime_along₅₆b hf.sorted hf.onePath (S := S)
    (M.proposal_time S.E ((M.opening_slot S.hc q)))
  have hncache : (M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
        (S.E.proposer ((M.opening_slot S.hc q)))).st
      (M.proposal_time S.E ((M.opening_slot S.hc q))))
      (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
        (S.E.proposer ((M.opening_slot S.hc q)))).record c).cache = c :=
    facts.nd.mkNode_cache _ _ _
  have hrootPre : M.get_fg_root (M.toHealing pre.core).toFG = Jn.erase :=
    hdata.rootAtProposal
  have hcapPre : pre.core.h_max ≤
      (M.derive_named S.E S.cfg Jn).h + 1 := by
    have hHone : 1 ≤ H := Nat.le_of_lt
      (Nat.sub_pos_iff_lt.mp hdata.targetHeightPositive)
    have h := hdata.hMaxAtProposal
    change pre.core.h_max = H at h
    rw [h, hdata.targetHeight]
    exact (Nat.sub_add_cancel hHone).ge
  have hrootCPre : Block.Preceq
      (M.get_fg_root (M.toHealing pre.core).toFG) C := hdata.ceilingRoot
  have hrootC : Block.Preceq
      (M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
          (S.E.proposer ((M.opening_slot S.hc q)))).st
        (M.proposal_time S.E ((M.opening_slot S.hc q))))
        (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
          (S.E.proposer ((M.opening_slot S.hc q)))).record c).st.core).toFG) C := by
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [setClock_fgRoot₅₆b facts S, hpre]
    exact hrootCPre
  have hupper : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v) (q - 1),
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        Block.Preceq B C := hdata.ceilingUpper
  have hanchorGen := Restated.fixedRoot_preparedProposalAnchor_preceq_of_previousCarriersOn facts
    S Hs Xb hf hHs hHsXb hfb (q := q - 1) hpostPreviousAction hcut
  rw [hqPredAdd] at hanchorGen
  have hanchorC := hanchorGen hproposalHor hupper hprop c hc hrootC hA
  have hroundSt : M.round_of S.hc (M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
        (S.E.proposer ((M.opening_slot S.hc q)))).st
      (M.proposal_time S.E ((M.opening_slot S.hc q))))
      (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
        (S.E.proposer ((M.opening_slot S.hc q)))).record c).st.core.s = q := by
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_proposal_time]
    exact facts.gr.round_of_opening_slot_eq_schedule S.hc q
  have hanchorR : ∀ R : Block V, M.get_sg_root_with (M.gradeContract c) S.E S.hc
      (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
          (S.E.proposer ((M.opening_slot S.hc q)))).st
        (M.proposal_time S.E ((M.opening_slot S.hc q))))
        (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
          (S.E.proposer ((M.opening_slot S.hc q)))).record c).st.core)
      (M.round_of S.hc (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
          (S.E.proposer ((M.opening_slot S.hc q)))).st
        (M.proposal_time S.E ((M.opening_slot S.hc q))))
        (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
          (S.E.proposer ((M.opening_slot S.hc q)))).record c).st.core.s) ⇢ R →
      Block.Preceq R C := by
    intro R hR
    rw [hroundSt] at hR
    rw [facts.nd.gradeContract_sgRoot_eq_frameAnchor] at hR
    obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract c) S.E S.hc
      (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
          (S.E.proposer ((M.opening_slot S.hc q)))).st
        (M.proposal_time S.E ((M.opening_slot S.hc q))))
        (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
          (S.E.proposer ((M.opening_slot S.hc q)))).record c).st.core) q
    have hgR : g.anchor = R := facts.nd.Sts_gradeContract_read_anchor c S.E S.hc _ q g hg R hR
    rw [← hgR]
    apply hanchorC
    unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor Restated.Vocabulary.Internal.PhaseGrades.nodeRead
    rw [hncache]
    exact returns_map_intro₅₆b (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.anchor) _ g hg
  have hCmem : C ∈ (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
      (S.E.proposer ((M.opening_slot S.hc q)))).st.core.T := by
    rcases hdata.ceilingChoice with hCA | hCaction
    · rw [hCA]
      have hAsub := facts.fc.get_filtered_block_tree_subset
        (M.toHealing source).toFG hdata.anchorFiltered
      rw [← hsource, facts.sto.toHealing_gs_T, Restated.Vocabulary.Proofs.Optimistic.tickStore,
        ← facts.hd.setClock_core_eq_store_with_t_s, facts.hd.Sts_setClock_core_T] at hAsub
      exact hAsub
    · have htargetC : Block.Preceq Jn.erase C0 := by
        calc
          Jn.erase = M.get_fg_root (M.toHealing pre.core).toFG := hrootPre.symm
          _ ⪯ C := hrootCPre
          _ = C0 := hCaction
      obtain ⟨nC, hnC, gC, hgC, hBC⟩ := hdata.actionCeilingEq
      have hCsource : C0 ∈ (W (strictEventIndex rho
          (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) vC).st.core.T :=
        Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho vC
          (q - 1) _ (mem_stateBeforeTime_along₅₆b hf.sorted hf.onePath _) nC hnC gC hgC C0 hBC
      have hrootActual : M.get_fg_root
          (M.toHealing (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
            (S.E.proposer ((M.opening_slot S.hc q)))).st.core).toFG = Jn.erase := by
        rw [hpre]
        exact hrootPre
      have hcapActual :
          (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
            (S.E.proposer ((M.opening_slot S.hc q)))).st.core.h_max ≤
            (M.derive_named S.E S.cfg Jn).h + 1 := by
        rw [hpre]
        exact hcapPre
      have hpreC0 := Restated.fixedRoot_actionCarrier_mem_proposerReadOn facts S Hs Xb hf hHs hHsXb
        hdata.targetRun htargetC hdata.actionWitnessHonest hCsource
        hprop hproposalHor hpostPreviousAction
        (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts
          S hprevLt) hrootActual hcapActual
      rw [hCaction]
      exact hpreC0.1
  obtain ⟨Cn, hCnbody, hCerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
      (M.proposal_time S.E ((M.opening_slot S.hc q)))
      (S.E.proposer ((M.opening_slot S.hc q))) _ hwp hCmem
  have hCnrun : Restated.RunBlockOn M S rho W Xb Cn :=
    Restated.fixedRoot_runBlock_of_body_at_readOn_FixedHeightRootOpeningParent facts S Hs Xb hf
      (hHsXb _ hprop) hCnbody
  have htargetC : Block.Preceq Jn.erase C := by
    calc
      Jn.erase = M.get_fg_root (M.toHealing pre.core).toFG := hrootPre.symm
      _ ⪯ C := hrootCPre
  have hJCN : NamedBlock.Preceq Jn Cn := by
    exact Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf
      hdata.targetRun hCnrun (by simpa only [hCerase] using htargetC)
  have hCderive : (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
      (S.E.proposer ((M.opening_slot S.hc q)))).st.core.σ C =
      M.derive_named S.E S.cfg Cn := by
    rw [← hCerase]
    exact Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho
      (M.proposal_time S.E ((M.opening_slot S.hc q)))
      (S.E.proposer ((M.opening_slot S.hc q))) _ hwp Cn hCnbody
  have hheightJleC :
      (M.derive_named S.E S.cfg Jn).h ≤
        (M.derive_named S.E S.cfg Cn).h :=
    facts.cs.derive_height_mono S.E S.cfg hJCN
  have hheightC : (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
      (S.E.proposer ((M.opening_slot S.hc q)))).st.core.h_max ≤
      ((W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
        (S.E.proposer ((M.opening_slot S.hc q)))).st.core.σ C).h + 1 := by
    rw [hCderive]
    have h := hdata.hMaxAtProposal
    rw [← hpre] at h
    change (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
      (S.E.proposer ((M.opening_slot S.hc q)))).st.core.h_max = H at h
    rw [h]
    calc
      H = (M.derive_named S.E S.cfg Jn).h + 1 := by
        have hHone : 1 ≤ H := Nat.le_of_lt
          (Nat.sub_pos_iff_lt.mp hdata.targetHeightPositive)
        rw [hdata.targetHeight]
        exact (Nat.sub_add_cancel hHone).symm
      _ ≤ (M.derive_named S.E S.cfg Cn).h + 1 :=
        Nat.add_le_add_right hheightJleC 1
  have hwitness : Restated.Vocabulary.Proofs.HealingSurface.CanonicalConeWitness M
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
          (S.E.proposer ((M.opening_slot S.hc q)))).st
        (M.proposal_time S.E ((M.opening_slot S.hc q))))
        (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
          (S.E.proposer ((M.opening_slot S.hc q)))).record c).st.core C := by
    apply Restated.Vocabulary.Proofs.HealingSurface.canonicalConeWitness_of_processedDescendant_and_hMax_le_succ facts
    · rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_T]
      exact hCmem
    · exact Proofs.ModelProperties.Preceq_self C
    · rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_h_max, facts.hd.Sts_setClock_core_σ]
      exact hheightC
  have hpropSupport : S.E.proposer ((M.opening_slot S.hc q) - 1 + 1) ∈
      Hs (M.support_cutoff S.E ((M.opening_slot S.hc q) - 1)) := by
    have hle := facts.sch.support_cutoff_le_proposal_time_succ S.E ((M.opening_slot S.hc q) - 1)
    rw [hsucc] at hle ⊢
    exact hHs _ _ hle hprop
  have hsupportGen := Restated.fixedRoot_preparedProposalConeSupport_of_namedConeOn facts
    S Hs Xb hf hHs hHsXb hcom (T := C) hs hpostCone
      ((facts.sch.support_cutoff_le_proposal_time_succ S.E
        ((M.opening_slot S.hc q) - 1)).trans
        (by simpa only [hsucc] using hproposalHor))
      hpropSupport
  rw [hsucc] at hsupportGen
  have hsupportC := hsupportGen c hc hrootC hdata.ceilingCone
  have hvalidC : Protocol.VoteSetValid S.E
      ((M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
          (S.E.proposer ((M.opening_slot S.hc q)))).st
        (M.proposal_time S.E ((M.opening_slot S.hc q))))
        (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
          (S.E.proposer ((M.opening_slot S.hc q)))).record c).st.core.s - 1)
      (M.proposer_view
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
            (S.E.proposer ((M.opening_slot S.hc q)))).st
          (M.proposal_time S.E ((M.opening_slot S.hc q))))
          (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
            (S.E.proposer ((M.opening_slot S.hc q)))).record c).st.core).toFG.toSG.toGoldfishStore
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
            (S.E.proposer ((M.opening_slot S.hc q)))).st
          (M.proposal_time S.E ((M.opening_slot S.hc q))))
          (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
            (S.E.proposer ((M.opening_slot S.hc q)))).record c).st.core.s).toFinset := by
    rw [facts.nd.mkNode_st, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_proposer_view,
      facts.hd.setClock_core_eq_store_with_t_s]
    exact Restated.proposerDutyStore_proposer_view_validOn facts S Hs Xb hf
      ((M.opening_slot S.hc q))
  have hcompat : Block.compatible
      (M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
          (S.E.proposer ((M.opening_slot S.hc q)))).st
        (M.proposal_time S.E ((M.opening_slot S.hc q))))
        (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q))))
          (S.E.proposer ((M.opening_slot S.hc q)))).record c).st.core).toFG) C = true := by
    exact Proofs.ModelProperties.compatible_eq_true_of_Preceq hrootC
  exact Restated.fixedRoot_preparedProposalHead_preceq_of_coneOn facts S Hs Xb
    (Hs (M.confirmation_time S.E ((M.opening_slot S.hc q) - 1))) hf c hc hcompat hwitness
    hanchorR hsupportC hvalidC

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle along `W`, if `v ∈ Hs (confirmation_time s)`, `lo ≤ proposal_time s`,
    `confirmation_time s` is inside the horizon, `B` satisfies `GenuineConfirmation` at `v`'s
    confirmation store, and every member of slot `s + 1`'s committee in `Hs (vote_time (s + 1))`
    passes the grade-1 awake test at its vote ticks and has, at every vote node state, `B` in an
    outcome of the voter candidate tree and every outcome of the SG root an ancestor of `B`, then
    slot `s + 1`'s committee votes along `W` into the descendants of `B`. -/
theorem honestVotesCone_succ_of_genuineConfirmation_of_frozenVoteReadsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {v : V} {s : Slot} (hv : v ∈ Hs (M.confirmation_time S.E s)) {B : Block V}
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {contract : M.Contract}
    (hgenuine : Restated.Vocabulary.Protocol.GenuineConfirmation M (contract := contract) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s))
      s B)
    (hcandidate : ∀ w ∈ Hs (M.vote_time S.E (s + 1)),
      w ∈ S.E.committee (s + 1) →
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
          (M.vote_time S.E (s + 1))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      ∃ K : Finset (Block V), Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E
          (M.toHealing (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
              (M.vote_time S.E (s + 1)))
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core) ⇢ K ∧ B ∈ K)
    (hanchor : ∀ w ∈ Hs (M.vote_time S.E (s + 1)),
      w ∈ S.E.committee (s + 1) →
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
          (M.vote_time S.E (s + 1))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      ∀ R : Block V, M.get_sg_root_with
          (M.gradeContract (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
              (M.vote_time S.E (s + 1)))
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).cache)
          S.E S.hc
          (M.toHealing (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
              (M.vote_time S.E (s + 1)))
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core)
          (M.round_of S.hc (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
              (M.vote_time S.E (s + 1)))
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core.s) ⇢ R →
        Block.Preceq R B)
    (hrun : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), w ∈ S.E.committee (s + 1) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (s + 1))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc (s + 1))) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb (s + 1)
      (fun X => Block.Preceq B X) := by
  intro w hw hwcommittee
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
    (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache
  obtain ⟨K, hK, hBK⟩ := hcandidate w hw hwcommittee c hc
  have hK' := hK
  unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree at hK'
  obtain ⟨P0, -, hKP⟩ := (returns_bind_iff₅₆b _ _ _).mp hK'
  have hKeq := (Record.returns_pure _ _).1 hKP
  have hroot := (facts.fc.parts_of_mem_get_filtered_block_tree_from (hKeq ▸ hBK)).2
  have hd := Restated.nextVoteAdoption_of_recovery_after_gstOn facts
    S Hs Xb hf hHs hHsXb hv hw hpost hhor c hc hroot (hanchor w hw hwcommittee c hc) hK hBK
    (hrun w hw hwcommittee)
  obtain ⟨htransport, hsub, hanchorCompat, hpath, hrunBlock, hemit⟩ := hd
  set n := M.mkNode
    (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
      (M.vote_time S.E (s + 1)))
    (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c with hn
  set cw := Restated.Vocabulary.Proofs.Optimistic.tickStore M S
    (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)
    with hcw
  have hslot : n.st.core.s = s + 1 := by
    rewrite [hn, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
  have hprev : n.st.core.s - 1 = s := by
    rw [hslot]
    simp
  have hcommittee : (S.node w).val_index ∈ S.E.committee n.st.core.s := by
    rw [S.node_val_index, hslot]
    exact hwcommittee
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract n.cache) S.E
    S.hc (M.toHealing n.st.core) T L L' (n.st.core.s - 1)
  obtain ⟨early, sc, hearly, hvotes, hsc, helig⟩ := genuine_eligible₅₆b facts hgenuine
  have hel := confEarly_subset_late₅₆b facts S.E cw s early hearly
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  have hs : (M.toHealing n.st.core).s = n.st.core.s := facts.sto.toHealing_s n.st.core
  have hTn : (M.toHealing n.st.core).T = n.st.core.T := facts.sto.toHealing_T n.st.core
  have hR' : M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc n.st.core.s) ⇢ R := by
    rw [hs] at hR
    exact hR
  have hX := (facts.fc.get_head_in_tree_split_with (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) T L L' (n.st.core.s - 1) R hR H).1 hH
  rw [hprev] at hX
  have hhead : Block.Preceq B H :=
    captures_of_confirmation_one₅₆b facts S.E (M.toHealing n.st.core).σ
      (M.toHealing n.st.core).h_max cw.T (M.toHealing n.st.core).T T (M.toHealing n.st.core).s
      early (Restated.Vocabulary.Protocol.confLate M S.E cw s)
      (early.filter (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M S.E cw s) x = true))
      L L' s ⟨hel, rfl⟩
      (by rw [hTn]; exact htransport _ hvotes L hL L' hL')
      (sc B) (hsc B) helig (hsub L hL L' hL') (hanchorCompat R hR')
      (fun hRB C hRC hCR hCB => hpath R hR' hRB C hRC hCR hCB T hT) H hX
  obtain ⟨C, hCH, hCrun⟩ := hrunBlock T hT L hL L' hL' H hH
  obtain ⟨D, hD⟩ := facts.dt.goldfish_vote_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node w) n.st
  have hDvote := facts.fc.goldfish_vote_with_snd_of_mem_committee (M.gradeContract n.cache) S.E
    S.hc (S.node w) n.st hcommittee D hD T hT L hL L' hL' H hH
  have hem := hemit _ D hD hDvote
  refine ⟨C, ?_, hCrun, ?_⟩
  · rw [hCH]
    exact hhead
  · rw [← hCH, hslot] at hem
    simpa only [S.node_val_index] using hem

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle along `W`, if `v ∈ Hs (confirmation_time s)`, `lo ≤ proposal_time s`,
    `confirmation_time s` is inside the horizon, `w ∈ Hs (vote_time (s + 1))` passes the grade-1
    awake test at its ticks there, and `D` is in an outcome of the voter candidate tree of `w`'s
    node state `n` staged at `vote_time (s + 1)` with every outcome of `n`'s SG root an ancestor of
    `D`, then the body of `NamedNextVoteAdoptionOn` for `D` holds at `n`, relative to `v`'s
    confirmation store. -/
theorem nextVoteAdoption_of_frozenCandidateAtReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {v : V} {s : Slot} (hv : v ∈ Hs (M.confirmation_time S.E s)) {D : Block V}
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {w : V} (hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c)
    {K : Finset (Block V)}
    (hK : Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core) ⇢ K)
    (hcandidate : D ∈ K)
    (hanchor : ∀ R : Block V, M.get_sg_root_with
        (M.gradeContract (M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1)))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).cache)
        S.E S.hc
        (M.toHealing (M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1)))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core)
        (M.round_of S.hc (M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1)))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core.s) ⇢ R →
      Block.Preceq R D)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (s + 1))) →
      M.awake_for_grade1 S w (W j w) (M.round_of S.hc (s + 1))) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    let cw := Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)
    (∀ votes : Finset (GoldfishVote V), Restated.Vocabulary.Protocol.confVotes M S.E cw s ⇢ votes →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      Restated.Vocabulary.Protocol.AdoptionTransport M cw.T n.st.core.T votes
        (Restated.Vocabulary.Protocol.confLate M S.E cw s) L L' D) ∧
    (∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      L' ⊆ L) ∧
    (∀ R : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc n.st.core.s) ⇢ R →
      R.compatible D = true) ∧
    (∀ R : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc n.st.core.s) ⇢ R →
      R ⪯ D →
        ∀ C : Block V, R ⪯ C → C ≠ R → C ⪯ D →
          ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
            C ∈ T) ∧
    (∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
      ∃ C : NamedBlock V, C.erase = H ∧ Restated.RunBlockOn M S rho W Xb C) ∧
    (∀ u : GoldfishVote V,
      ∀ Dv : M.NS × Option (GoldfishVote V),
        M.duties_goldfish_vote_with (M.gradeContract n.cache) S.E S.hc (S.node w) n.st ⇢ Dv →
      Dv.2 = some u →
        Restated.Vocabulary.Execution.Run.emits M S rho W w (Object.gfVote u) (M.vote_time S.E (s + 1))) := by
  have hK' := hK
  unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree at hK'
  obtain ⟨P0, -, hKP⟩ := (returns_bind_iff₅₆b _ _ _).mp hK'
  have hKeq := (Record.returns_pure _ _).1 hKP
  have hroot := (facts.fc.parts_of_mem_get_filtered_block_tree_from (hKeq ▸ hcandidate)).2
  exact Restated.nextVoteAdoption_of_recovery_after_gstOn facts
    S Hs Xb hf hHs hHsXb hv hw hpost hhor c hc hroot hanchor hK hcandidate hrun

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic

end

end DecoupledConsensusModel.Sts.Restated
