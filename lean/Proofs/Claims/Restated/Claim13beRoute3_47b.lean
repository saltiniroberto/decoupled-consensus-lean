import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Vocabulary_Execution_CertificateUniqueness
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_Execution_OutageInputs
import Proofs.Claims.Restated.Vocabulary_Execution_OutageProvenance
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_JustificationCertificates
import Proofs.Claims.Restated.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeDelivery
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Ladder
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_FinalizationBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_JustificationBound
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_Schedule
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDerived
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Objects
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterInterference
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25

/-!
# Finality agreement, attestation provenance and fixed-height roots along a path of the run

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, read along a path
`W` of a run, most of them along the path of a bundle
`hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo`. They show that finalized blocks are
compatible, that attestations and votes held or included in blocks were emitted by their authors,
that certificates are unique, and that a reader's finality-gadget root at a fixed `h_max` is
compatible with a protected block.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-! ## Helpers about the run -/

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

omit [Fintype V] in
/-- An attestation of the named chain attestations of `B` is included in some named ancestor of `B`. -/
private theorem named_chain_attestations_carrier₄₇b {B : NamedBlock V} {a : NamedAttestation V}
    (ha : a ∈ Protocol.named_chain_attestations B) :
    ∃ carrier : NamedBlock V, NamedBlock.Preceq carrier B ∧ a ∈ carrier.attestations := by
  induction B with
  | genesis =>
    have h0 : a ∈ (∅ : Finset (NamedAttestation V)) := ha
    exact absurd h0 (by simp)
  | node p s r votes support rows proposer ih =>
    have hu : a ∈ Protocol.named_chain_attestations p ∪ rows.toFinset := ha
    rw [Finset.mem_union, List.mem_toFinset] at hu
    rcases hu with hu | hu
    · obtain ⟨c, hc, hac⟩ := ih hu
      refine ⟨c, ?_, hac⟩
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr (by simpa only [NamedBlock.Preceq] using hc)
    · exact ⟨_, Proofs.NamedAncestry.named_self _, by simpa only [NamedBlock.attestations] using hu⟩

/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_reach₄₇b {S : Setup V} {rho : Record.Run V}
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

/-- For every path `W` of `rho` and `m ≤ n`, `W n` is among the worlds the events `m` to `n - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_slice₄₇b {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {m n : Nat} (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Nat.add_sub_cancel_left]
  exact onePath_reach₄₇b W hW m k

/-- On the path `W` of `hf`, the world `W (strictEventIndex rho t)` is a world that can hold
    strictly before `t`. -/
private theorem path_mem_stateBeforeTime₄₇b (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  have h := Restated.stateBeforeTime_eq_takeOn facts S Hs Xb hf t
  change W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.Run.stateBeforeTime M S rho t
  rw [h]
  exact (hf.onePath _).1

/-- Along a path `W` of `rho`, if `receiver` accepts the block `B` at the `i`-th event at `t`, then
    `receiver` processes `B` at `t` along `W`. -/
private theorem block_accepts_processes₄₇b (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    {i : Nat} {receiver : V} {B : NamedBlock V} {t : Time}
    (h : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i receiver (.block B) t) :
    Restated.Vocabulary.Execution.NamedRun.processes M S rho W receiver (.block B) t := by
  obtain ⟨⟨hcall, e, he, _, het⟩, _, _⟩ := h
  change Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong M S rho W i receiver
    (.block B) at hcall
  rcases hcall with ⟨time, hi, out, hout, hWi, hmem⟩ | ⟨time, hi⟩
  · have heq : Record.Event.tick receiver time = e := Option.some.inj (hi.symm.trans he)
    have ht : time = t := by
      simpa only [Record.Event.time] using (congrArg Record.Event.time heq).trans het
    subst time
    exact Or.inl ⟨i, hi, out, hout, hWi, hmem⟩
  · have heq : Record.Event.deliver receiver (.block B) time = e :=
      Option.some.inj (hi.symm.trans he)
    have ht : time = t := by
      simpa only [Record.Event.time] using (congrArg Record.Event.time heq).trans het
    subst time
    exact Or.inr ⟨i, hi⟩

/-- Along a path `W` of `rho`, the named bodies `u` holds in `W i` contain genesis and the parent of
    each of them. -/
private theorem namedParentClosed_W₄₇b (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (i : Nat) (u : V) :
    Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M (W i u).st :=
  (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i u (W i)
    (hW i).1).1.1.1.2.2.1

/-- If the named bodies of `st` contain the parent of each of them, every named ancestor of a body
    of `st` is a body of `st`. -/
private theorem ancestor_body_mem₄₇b {st : M.NS}
    (hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
    exact hAB ▸ hB
  | node parent s root votes support rows proposer ih =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at hAB
    rcases hAB with rfl | hparent
    · exact hB
    · have hp := hpc.2 _ hB
      rw [Proofs.ModelProperties.named_parent_node] at hp
      exact ih hp (by simp only [NamedBlock.Preceq]; exact hparent)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if the slot-`(s + 1)` proposer's store in `W (i + 1)` has processed the
    slot-`s` vote `u`, and the event at index `i` is before `s + 1`'s proposal time, then `u` is in
    the slot-`s` pool of the store staged at the proposal time from the proposer's store in `W`
    strictly before that time. -/
theorem gfVote_processed_after_event_at_proposerDuty_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {i : Nat} {e : Record.Event V} {u : GoldfishVote V} {s : Slot}
    (he : rho.events[i]? = some e) (hus : u.slot = s)
    (hprocessed : Restated.Vocabulary.Execution.Object.processed M
      (W (i + 1) (S.E.proposer (s + 1))).st (Object.gfVote u) = true)
    (hearly : e.time < M.proposal_time S.E (s + 1)) :
    u ∈ (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st.core
      (M.proposal_time S.E (s + 1))).pool s := by
  have hmem : u ∈ (W (i + 1) (S.E.proposer (s + 1))).st.core.gf_votes s := by
    have hprocessed' : u ∈ (W (i + 1) (S.E.proposer (s + 1))).st.core.gf_votes u.slot := by
      simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq]
        using hprocessed
    rw [hus] at hprocessed'
    exact hprocessed'
  let Gamma := M.proposal_time S.E (s + 1)
  let N := (rho.events.filter (fun x => decide (x.time < Gamma))).length
  have hiN : i < N := by
    by_contra hnot
    have hNle : N ≤ i := Nat.le_of_not_gt hnot
    have hGammae : Gamma ≤ e.time :=
      Restated.le_time_of_index_geOn facts S Hs Xb hf
        (t := Gamma) (j := i) (e := e) (by simpa [N] using hNle) he
    exact (not_le_of_gt (by simpa only [Gamma] using hearly)) hGammae
  have hcarry : Restated.Vocabulary.Protocol.PoolCarry M
      (W (i + 1) (S.E.proposer (s + 1))).st.core (W N (S.E.proposer (s + 1))).st.core :=
    Restated.pool_carryOn facts S Hs Xb hf (S.E.proposer (s + 1)) (m := i + 1) N
      (Nat.succ_le_of_lt hiN)
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.sto.pool_set_clock_slot]
  exact (facts.sto.mem_store_pool_iff _ _ _).mpr (hcarry.mem s u hmem)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if the event at index `j` is before `t` and `u` is in the round-`k`
    projected pool of `w`'s store in `W (j + 1)`, then `u` is in the round-`k` projected pool of
    `w`'s store in `W (strictEventIndex rho t)`. -/
theorem sgVote_mem_stateBeforeTime_of_postOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {j : Nat} {e : Record.Event V} {t : Time} {k : Round}
    {u : Protocol.SGVote V}
    (hj : rho.events[j]? = some e) (hjt : e.time < t)
    (hu : u ∈ (W (j + 1) w).st.toHealing.sg_votes k) :
    u ∈ (W (strictEventIndex rho t) w).st.toHealing.sg_votes k := by
  let N := (rho.events.filter (fun x => decide (x.time < t))).length
  have hjN : j < N := by
    by_contra hnot
    have htle : t ≤ e.time :=
      Restated.le_time_of_index_geOn facts S Hs Xb hf (t := t) (j := j) (e := e)
        (by simpa [N] using Nat.le_of_not_gt hnot) hj
    exact (not_le_of_gt hjt) htle
  change u ∈ (M.toHealing (W (j + 1) w).st.core).toFG.toSG.sg_votes k at hu
  rw [facts.sto.Sts_toHealing_sg_votes] at hu
  obtain ⟨a, ha, hau⟩ := Finset.mem_image.mp hu
  have hcarry := Restated.Vocabulary.Proofs.HealingLemmas.stateBefore_sg_pool_subset facts S rho w k
    (i := j + 1) (W (j + 1)) (hf.onePath (j + 1)).1 N (Nat.succ_le_of_lt hjN) (W N)
    (onePath_slice₄₇b W hf.onePath (Nat.succ_le_of_lt hjN))
  have haN := hcarry ha
  change u ∈ (M.toHealing (W N w).st.core).toFG.toSG.sg_votes k
  rw [facts.sto.Sts_toHealing_sg_votes]
  exact Finset.mem_image.mpr ⟨a, haN, hau⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- With the slashable bound and root-collision freedom over `Xb` along the path `W`, the finalized
    blocks of two run blocks read through `Xb` along `W` are compatible. -/
theorem finalized_compatibleOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (Xb : Finset V) (C D : NamedBlock V)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    (hroot : Restated.RootCollisionFreeOn M S rho W Xb)
    (hC : Restated.blockInRunOn M S rho W Xb C)
    (hD : Restated.blockInRunOn M S rho W Xb D) :
    Block.compatible (M.derive_named S.E S.cfg C).F
      (M.derive_named S.E S.cfg D).F = true := by
  have hCorder := facts.cs.chainOrder_derive_named S.E S.cfg C
  have hDorder := facts.cs.chainOrder_derive_named S.E S.cfg D
  have hCanchor := (facts.cs.derive_named_anchors_preceq S.E S.cfg C).1
  have hDanchor := (facts.cs.derive_named_anchors_preceq S.E S.cfg D).1
  have hlinear :
      Block.Preceq (M.derive_named S.E S.cfg C).F (M.derive_named S.E S.cfg D).F ∨
      Block.Preceq (M.derive_named S.E S.cfg D).F (M.derive_named S.E S.cfg C).F := by
    rcases le_total (M.derive_named S.E S.cfg C).h_F
        (M.derive_named S.E S.cfg D).h_F with hCD | hDC
    · have hlt : (M.derive_named S.E S.cfg C).h_F <
          (M.derive_named S.E S.cfg D).h :=
        lt_of_le_of_lt (hCD.trans hDorder.heights_ordered)
          hDorder.justified_below_height
      have hCtoD := Restated.finalized_preceq_of_height_ltOn facts S rho W Xb D C hsb hroot hD hC hlt
      exact preceq_linear_Preceq hCtoD hDanchor
    · have hlt : (M.derive_named S.E S.cfg D).h_F <
          (M.derive_named S.E S.cfg C).h :=
        lt_of_le_of_lt (hDC.trans hCorder.heights_ordered)
          hCorder.justified_below_height
      have hDtoC := Restated.finalized_preceq_of_height_ltOn facts S rho W Xb C D hsb hroot hC hD hlt
      exact preceq_linear_Preceq hCanchor hDtoC
  exact compatible_of_cases hlinear

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- For every path `W` of `rho`, with the slashable bound and root-collision freedom over `Xb` along
    `W`, for `source, target ∈ Xb`, the finalized blocks of `source` in `W i` and of `target` in
    `W j` are compatible. -/
theorem stateBefore_finalized_compatibleOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (Xb : Finset V)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    (hroot : Restated.RootCollisionFreeOn M S rho W Xb)
    (i j : Nat) (source target : V)
    (hsource : source ∈ Xb) (htarget : target ∈ Xb) :
    Block.compatible (W i source).st.core.F (W j target).st.core.F = true := by
  obtain ⟨C, hCmem, hCF, _⟩ :=
    Restated.Vocabulary.Proofs.NamedFinalizationBridge.finalization_carrier_stateBefore facts S rho i
      source (W i) (hW i).1
  obtain ⟨D, hDmem, hDF, _⟩ :=
    Restated.Vocabulary.Proofs.NamedFinalizationBridge.finalization_carrier_stateBefore facts S rho j
      target (W j) (hW j).1
  have hC : Restated.blockInRunOn M S rho W Xb C :=
    Restated.blockInRun_of_directOn facts S rho W Xb (Or.inr ⟨source, hsource, i, hCmem⟩)
  have hD : Restated.blockInRunOn M S rho W Xb D :=
    Restated.blockInRun_of_directOn facts S rho W Xb (Or.inr ⟨target, htarget, j, hDmem⟩)
  have h := Restated.finalized_compatibleOn facts S rho W Xb C D hsb hroot hC hD
  rw [hCF, hDF] at h
  exact h

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, with the slashable bound and root-collision freedom over `Xb` along
    `W`, for `source, target ∈ Xb`, the finalized blocks of `source` in
    `W (strictEventIndex rho read)` and of `target` in `W (strictEventIndex rho out)` are
    compatible. -/
theorem stateBeforeTime_finalized_compatibleOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    (hroot : Restated.RootCollisionFreeOn M S rho W Xb)
    (read out : Time) (source target : V)
    (hsource : source ∈ Xb) (htarget : target ∈ Xb) :
    Block.compatible (W (strictEventIndex rho read) source).st.core.F
      (W (strictEventIndex rho out) target).st.core.F = true :=
  Restated.stateBefore_finalized_compatibleOn facts S rho W hf.onePath Xb hsb hroot _ _ source
    target hsource htarget

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- For every node state `before`, round `r` and validator `v`, the round-`r` action read computed
    from `before` can give some node state `n`, and the attestation duty of `v` run on `n` with the
    grade contract of `n`'s cache has some outcome `D`. -/
private theorem exists_actionRead_attest_47b (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (r : Round) (v : V) :
    ∃ n ∈ Restated.Vocabulary.Internal.NamedOutageEntry.actionReadFrom M S before r,
      ∃ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v)
        n.st n.record ⇢ D := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c)
    S.E S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨M.mkNode st before.record c, ⟨c, hc, st, hst, rfl⟩,
    facts.dt.attest_with_nonempty _ _ _ _ _ _⟩

/-- On the path `W` of `hf`, two attestations `v` emits for one round are equal. -/
theorem emitted_same_round_uniqueOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {a b : NamedAttestation V} {ta tb : Time}
    (ha : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (.attest a) ta)
    (hb : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (.attest b) tb)
    (hr : a.round = b.round) : a = b := by
  obtain ⟨i, hi, _, _, _, _, hrowi, _, hti, _⟩ :=
    Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_stages facts S rho W hf.onePath ha
  obtain ⟨j, hj, _, _, _, _, hrowj, _, htj, _⟩ :=
    Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_stages facts S rho W hf.onePath hb
  have htt : ta = tb := by rw [hti, htj, hr]
  obtain ⟨hiLen, hiGet⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjLen, hjGet⟩ := List.getElem?_eq_some_iff.mp hj
  have hij : i = j := hf.tickIndexUnique (hj := hiLen) (hk := hjLen) hiGet
    (by rw [hiGet, hjGet, htt])
  subst j
  rw [hr] at hrowi
  obtain ⟨n, hn, D, hD⟩ := exists_actionRead_attest_47b facts S (W i v) b.round v
  exact ((hrowi n hn).1 D hD).symm.trans ((hrowj n hn).1 D hD)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `receiver` processes `B` at `t`, `a` is included in `B`, and `a`'s
    author is in the set for `t`, then `S.a a.round ≤ t` and the author emitted `a` at
    `S.a a.round`. -/
theorem honest_carried_row_emissionOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {receiver : V} {B : NamedBlock V} {a : NamedAttestation V} {t : Time}
    (hB : Restated.Vocabulary.Execution.NamedRun.processes M S rho W receiver (.block B) t)
    (ha : a ∈ B.attestations) (hHon : a.val_index ∈ Hs t) :
    (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ t ∧
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (.attest a)
        (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
  obtain ⟨sent, hsend, hem⟩ := hf.carried_attest receiver B t hB a ha hHon
  obtain ⟨_, _, _, _, _, _, _, _, htime, _⟩ :=
    Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_stages facts S rho W hf.onePath hem
  subst sent
  exact ⟨hsend, hem⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if every event before index `i` has a time at most `T`, `a` is in the
    round row of `receiver`'s store in `W i`, and `a`'s author is in the set for `T`, then
    `receiver` accepted `a` at some index `j < i` and time `t ≥ S.a a.round`, and the author emitted
    `a` at `S.a a.round`. -/
theorem honest_held_row_emissionOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (i : Nat) (receiver : V) {T : Time}
    (hT : ∀ (j : Nat) (e : Record.Event V), j < i → rho.events[j]? = some e → e.time ≤ T)
    {a : NamedAttestation V}
    (ha : a ∈ (W i receiver).st.sg_rows a.round)
    (hHon : a.val_index ∈ Hs T) :
    ∃ j : Nat, j < i ∧ ∃ t : Time,
      Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W j receiver (.attest a) t ∧
      (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ t ∧
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (.attest a)
        (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
  obtain ⟨j, hj, t, hacc⟩ :=
    Restated.Vocabulary.Proofs.NamedOutageProvenance.held_row_origin facts S rho i receiver W
      hf.onePath ha
  have htT : t ≤ T := by
    obtain ⟨e, he, -, het⟩ := hacc.1.2
    rw [← het]
    exact hT j e hj he
  obtain ⟨sent, hsend, hem⟩ := Restated.actual_handles_authenticatedOn facts S rho Hs Xb hf
    hacc.1 (hHs _ _ htT hHon) (author_attest a)
  obtain ⟨_, _, _, _, _, _, _, _, htime, _⟩ :=
    Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_stages facts S rho W hf.onePath hem
  subst sent
  exact ⟨j, hj, t, hacc, hsend, hem⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if every event before index `i` has a time at most `T`, `receiver`'s
    store in `W i` holds `B`, `A` is an ancestor of `B` that includes `a`, and `a`'s author is in
    the set for `T`, then `receiver` accepted `A` at some index `j < i` and time `t ≥ S.a a.round`,
    and the author emitted `a` at `S.a a.round`. -/
theorem honest_held_ancestor_row_emissionOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (i : Nat) (receiver : V) {T : Time}
    (hT : ∀ (j : Nat) (e : Record.Event V), j < i → rho.events[j]? = some e → e.time ≤ T)
    {B A : NamedBlock V} {a : NamedAttestation V}
    (hB : B ∈ (W i receiver).st.bodies)
    (hAB : NamedBlock.Preceq A B) (ha : a ∈ A.attestations)
    (hHon : a.val_index ∈ Hs T) :
    ∃ j : Nat, j < i ∧ ∃ t : Time,
      Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W j receiver (.block A) t ∧
      (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ t ∧
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (.attest a)
        (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
  have hA : A ∈ (W i receiver).st.bodies :=
    ancestor_body_mem₄₇b (namedParentClosed_W₄₇b facts S rho W hf.onePath i receiver) hB hAB
  rcases Restated.Vocabulary.Proofs.NamedOutageProvenance.held_block_origin facts S rho i receiver W
      hf.onePath hA with hgen | ⟨j, hj, t, hacc⟩
  · subst A
    rw [named_genesis_attestations] at ha
    simp only [List.not_mem_nil] at ha
  · have htT : t ≤ T := by
      obtain ⟨e, he, -, het⟩ := hacc.1.2
      rw [← het]
      exact hT j e hj he
    obtain ⟨hsend, hem⟩ := Restated.honest_carried_row_emissionOn facts S rho Hs Xb hf
      (block_accepts_processes₄₇b S rho W hacc) ha (hHs _ _ htT hHon)
    exact ⟨j, hj, t, hacc, hsend, hem⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `Wr` of `hf`, under `hmajority`, if `t` is within the horizon and `v`'s `h_max` in
    `Wr (strictEventIndex rho t)` is greater than `1`, then some body `W` of that store, of height
    at least that `h_max`, includes in its chain an attestation for height `h_max − 1` by a quorum
    member in `Hs t`, emitted along `Wr` before `t`. -/
theorem frontierQuorumWitness_stateBeforeTime_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {Wr : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho Wr Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (hmajority : HonestWeightMajorityOn S rho Hs)
    {t : Time} (hthor : t ≤ rho.horizon) {v : V}
    (hlarge : 1 < (Wr (strictEventIndex rho t) v).st.h_max) :
    ∃ W : NamedBlock V,
      W ∈ (Wr (strictEventIndex rho t) v).st.bodies ∧
      ∃ Q : Finset V, ∃ X : NamedBlock V, ∃ a : NamedAttestation V, ∃ ta,
        (Wr (strictEventIndex rho t) v).st.core.h_max ≤
            (M.derive_named S.E S.cfg W).h ∧
          S.E.electorate.IsQuorum Q ∧ NamedBlock.Preceq X W ∧
          a.erase ∈ M.chain_attestations W.erase ∧
          a.val_index ∈ Hs t ∧
          Restated.Vocabulary.Execution.NamedRun.emits M S rho Wr a.val_index (.attest a) ta ∧
          ta < t ∧
          a.height_pair.erase.height? =
            some ((Wr (strictEventIndex rho t) v).st.core.h_max - 1) := by
  let n := strictEventIndex rho t
  let pre := (Wr n v).st
  have hlarge' : 1 < pre.core.h_max := hlarge
  have hmemT : Wr n ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t :=
    path_mem_stateBeforeTime₄₇b facts S Hs Xb hf t
  obtain ⟨W, hW, hmaxW⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime facts S rho t v
      (Wr n) hmemT
  have hcross : pre.core.h_max - 1 <
      (M.derive_named S.E S.cfg W).h := by
    rw [hmaxW]
    exact Nat.sub_lt (Nat.zero_lt_of_lt hlarge') (by decide)
  have hpositive : 1 ≤ pre.core.h_max - 1 :=
    Nat.le_sub_of_add_le (Nat.succ_le_iff.mpr hlarge')
  obtain ⟨X, hX, hXheight, Q, hQ, hwit⟩ :=
    facts.cs.height_crossing S.E S.cfg W
      (pre.core.h_max - 1) hpositive hcross
  obtain ⟨signer, hsignerQ, hsignerHonest⟩ :=
    HonestWeightMajority.exists_honest_member_of_quorum (hmajority t hthor) hQ
  obtain ⟨carrier, a, hcarrier, ha, hsigner, hmatch⟩ := hwit signer hsignerQ
  have haHonest : a.val_index ∈ Hs t := by
    rw [hsigner]
    exact hsignerHonest
  have hbefore : ∀ j e, j < n → rho.events[j]? = some e → e.time < t := by
    intro j e hj he
    have htrue := Restated.filter_true_of_index_ltOn facts S Hs Xb hf
      (fun f : Record.Event V => decide (f.time < t))
      (fun e₁ f₁ hkey hf₁ => by
        simp only [decide_eq_true_eq] at hf₁ ⊢
        exact lt_of_le_of_lt (Restated.time_le_of_key_le hkey) hf₁) hj he
    simpa only [decide_eq_true_eq] using htrue
  obtain ⟨j, hj, received, hacc, hsend, hemit⟩ :=
    Restated.honest_held_ancestor_row_emissionOn facts S rho Hs Xb hf hHs n v
      (fun j e hj he => (hbefore j e hj he).le) hW hcarrier ha haHonest
  obtain ⟨e, he, -, het⟩ := hacc.1.2
  have hreceived : received < t := by
    rw [← het]
    exact hbefore j e hj he
  have hta : (Restated.Vocabulary.Execution.Setup.a M S a.round) < t := hsend.trans_lt hreceived
  have hheight : a.height_pair.erase.height? = some (pre.core.h_max - 1) := by
    obtain ⟨tmo, hpair⟩ := vote_of_matchesEntry hmatch
    rw [hpair]
    exact namedHeightPair_erase_vote_height? _ _ _
  refine ⟨W, hW, Q, X, a, (Restated.Vocabulary.Execution.Setup.a M S a.round), hmaxW.symm.le, hQ, hX, ?_,
    haHonest, hemit, hta, hheight⟩
  exact facts.ev.erase_mem_chain_attestations W carrier hcarrier a ha

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `Wr` of `hf`, under `hmajority`, if `t` is within the horizon and `v`'s `h_max` in
    `Wr (strictEventIndex rho t)` is greater than `1`, then some body `W` of that store, of height
    at least that `h_max`, includes in its chain an attestation for height `h_max − 1` by a quorum
    member in `Hs t`, emitted along `Wr` before `t`. -/
theorem frontierQuorumWitness_stateBeforeTimeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {Wr : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho Wr Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (hmajority : HonestWeightMajorityOn S rho Hs)
    {t : Time} (hthor : t ≤ rho.horizon) {v : V}
    (hlarge : 1 < (Wr (strictEventIndex rho t) v).st.h_max) :
    ∃ W : NamedBlock V,
      W ∈ (Wr (strictEventIndex rho t) v).st.bodies ∧
      ∃ Q : Finset V, ∃ X : NamedBlock V, ∃ a : NamedAttestation V, ∃ ta,
        (Wr (strictEventIndex rho t) v).st.core.h_max ≤
            (M.derive_named S.E S.cfg W).h ∧
          S.E.electorate.IsQuorum Q ∧ NamedBlock.Preceq X W ∧
          a.erase ∈ M.chain_attestations W.erase ∧
          a.val_index ∈ Hs t ∧
          Restated.Vocabulary.Execution.NamedRun.emits M S rho Wr a.val_index (.attest a) ta ∧
          ta < t ∧
          a.height_pair.erase.height? =
            some ((Wr (strictEventIndex rho t) v).st.core.h_max - 1) :=
  Restated.frontierQuorumWitness_stateBeforeTime_coreOn facts S Hs Xb hf hHs hmajority
    hthor hlarge

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `u` processes `o` at `t`, then `t` is at most the run's horizon. -/
theorem processes_time_le_horizonOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {u : V} {o : Object V} {t : Time}
    (hproc : Restated.Vocabulary.Execution.NamedRun.processes M S rho W u o t) :
    t ≤ rho.horizon := by
  rcases hproc with ⟨i, hi, -⟩ | ⟨i, hi⟩
  · simpa only [Record.Event.time] using (hf.in_horizon _ (List.mem_of_getElem? hi)).2
  · simpa only [Record.Event.time] using (hf.in_horizon _ (List.mem_of_getElem? hi)).2

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `a` is a run attestation read through `Xb` and its author is in the
    set for the horizon, then the author emitted some attestation with the same erasure as `a`. -/
theorem runAttestation_emitsOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {a : NamedAttestation V} (ha : Restated.RunAttestationOn M S rho W Xb a)
    (hh : a.val_index ∈ Hs rho.horizon) :
    ∃ (row : NamedAttestation V) (t : Time), row.erase = a.erase ∧
      (Restated.Vocabulary.Execution.Run.emits M S rho W a.val_index (Object.attest row) t) := by
  rcases ha with hobj | ⟨B, hB, hmem⟩
  · obtain ⟨u, t, hproc⟩ :=
      Restated.Vocabulary.Proofs.HealingSurface.exists_processes_of_mem_objects facts S rho W
        hf.onePath hobj
    obtain ⟨t', -, hem⟩ :=
      hf.unforgeable u (Object.attest a) t hproc a.val_index
        (hHs _ _ (Restated.processes_time_le_horizonOn facts S Hs Xb hf hproc) hh) (author_attest a)
    exact ⟨a, t', rfl, hem⟩
  · obtain ⟨row, t, hrow, hem⟩ := Restated.carriedByHonest_of_runBlockOn facts S Hs Xb hf hHs hB
      a.erase
      (by
        obtain ⟨carrier, hc, hac⟩ := named_chain_attestations_carrier₄₇b hmem
        exact facts.ev.erase_mem_chain_attestations B carrier hc a hac)
      (by rw [namedAttestation_erase_val_index]; exact hh)
    rw [namedAttestation_erase_val_index] at hem
    exact ⟨row, t, hrow, hem⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, a certificate for `T` at height `h`, read through `Xb`, is completable
    by the set for the horizon. -/
theorem completable_of_certificateOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {h : Height} {T : BlockId}
    (hc : Restated.CertificateOn M S rho W Xb h T) :
    Restated.CompletableOn M S rho W (Hs rho.horizon) h T := by
  obtain ⟨Q, hQ, hsig⟩ := hc
  refine ⟨Q ∩ Hs rho.horizon, Finset.inter_subset_right,
    quorum_meets_set S.E ((isQuorum_iff_q_le S.E Q).mpr hQ), ?_⟩
  intro v hv
  obtain ⟨hvQ, hvh⟩ := Finset.mem_inter.mp hv
  obtain ⟨a, hra, hav, hhp⟩ := hsig v hvQ
  obtain ⟨row, t, herase, hem⟩ := Restated.runAttestation_emitsOn facts S Hs Xb hf hHs hra
    (by rw [hav]; exact hvh)
  rw [hav] at hem
  refine ⟨row, t, hem, ?_⟩
  have hT : row.erase.height_pair = HeightPair.target h T := by
    rw [herase]
    rw [namedAttestation_erase_height_pair, hhp, namedHeightPair_erase_vote_false]
  exact Or.inl hT

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if the validators outside the set for the horizon weigh less than one
    third, two certificates at height `h` read through `Xb` name the same target. -/
theorem certificateTarget_uniqueOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (hfb : Execution.BelowOneThird S (Hs rho.horizon))
    (h : Height) (T T' : BlockId)
    (hT : Restated.CertificateOn M S rho W Xb h T)
    (hT' : Restated.CertificateOn M S rho W Xb h T') : T = T' :=
  Restated.perHeightCompletabilityOn facts S W hf.onePath (Hs rho.horizon) hfb h T T'
    (Restated.completable_of_certificateOn facts S Hs Xb hf hHs hT)
    (Restated.completable_of_certificateOn facts S Hs Xb hf hHs hT')

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, two attestations `v` emits for one round are equal. -/
theorem emits_attest_uniqueOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {a b : NamedAttestation V} {t₁ t₂ : Time}
    (h₁ : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (NamedObject.attest a) t₁)
    (h₂ : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (NamedObject.attest b) t₂)
    (hround : a.round = b.round) : a = b :=
  Restated.emitted_same_round_uniqueOn facts S rho Hs Xb hf h₁ h₂ hround

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- If `D` is a run block read through `Xb` along the path `W` and `E` is an ancestor of `D`, then
    `E` is a run block read through `Xb` along `W`. -/
theorem runBlock_ancestorOn_FixedHeightRootCore (facts : Record.Facts M) {S : Setup V} {rho : Record.Run V}
    {W : Nat → V → M.N} {Xb : Finset V}
    {D E : NamedBlock V}
    (hD : Restated.RunBlockOn M S rho W Xb D) (hED : NamedBlock.Preceq E D) :
    Restated.RunBlockOn M S rho W Xb E := by
  obtain ⟨B, hB, hDB⟩ := hD
  exact ⟨B, hB, (priv% Proofs.Vocabulary.Objects.FixedHeightRootCore
    DecoupledConsensusModel.Proofs.HealingSurface.named_preceq_trans) hED hDB⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `w ∈ Xb` holds `D` in `W (strictEventIndex rho read)`, then `D` is a
    run block read through `Xb`. -/
theorem runBlockOf_of_stateBeforeTime_memOn_FixedHeightRootCore (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) (read : Time)
    {D : NamedBlock V} (hD : D ∈ (W (strictEventIndex rho read) w).st.bodies) :
    Restated.RunBlockOn M S rho W Xb D :=
  Restated.runBlock_of_stateBefore_memOn facts S W Xb hw hD

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `w ∈ Xb`, the justified block of `w`'s store in
    `W (strictEventIndex rho read)` is the erasure of a run block read through `Xb`. -/
theorem runBlockOf_justified_atStrictReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) (read : Time) :
    Restated.RunBlockOfOn M S rho W Xb (W (strictEventIndex rho read) w).st.J := by
  have hmem := path_mem_stateBeforeTime₄₇b facts S Hs Xb hf read
  obtain ⟨D, hD, hDe⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho read w
      _ hmem
      (Restated.Vocabulary.Proofs.NamedStoreBridge.justifiedInTree_stateBeforeTime facts S rho read w
        _ hmem)
  exact ⟨D, hDe, Restated.runBlockOf_of_stateBeforeTime_memOn_FixedHeightRootCore facts S Hs Xb hf
    hw read hD⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `w ∈ Xb` and the justified height of `w`'s store in
    `W (strictEventIndex rho read)` is not `0`, then a certificate read through `Xb` exists for that
    height and the root of that store's justified block. -/
theorem certificateOfStoreJustification_atStrictReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) (read : Time)
    (hnz : (W (strictEventIndex rho read) w).st.h_j ≠ 0) :
    Restated.CertificateOn M S rho W Xb (W (strictEventIndex rho read) w).st.h_j
      (W (strictEventIndex rho read) w).st.J.root := by
  let st := (W (strictEventIndex rho read) w).st
  have hmem := path_mem_stateBeforeTime₄₇b facts S Hs Xb hf read
  obtain ⟨D, hD, hDJ, hDhj⟩ :=
    Restated.Vocabulary.Proofs.Bridges.storeJustificationOnChain_stateBeforeTime facts S rho read w
      _ hmem
  have hDJ' : (M.derive_named S.E S.cfg D).J = st.J := hDJ
  have hDhj' : (M.derive_named S.E S.cfg D).h_j = st.h_j := hDhj
  have hDrun : Restated.RunBlockOn M S rho W Xb D :=
    Restated.runBlockOf_of_stateBeforeTime_memOn_FixedHeightRootCore facts S Hs Xb hf hw read hD
  have hnzD : (M.derive_named S.E S.cfg D).h_j ≠ 0 := by rw [hDhj']; exact hnz
  obtain ⟨J, hJD, hJerase, Q, hQ, hwit⟩ :=
    Restated.Vocabulary.Proofs.NamedJustificationCertificates.justification_certificate facts S.E S.cfg D hnzD
  have hroot : J.root = st.J.root := by
    rw [← Proofs.NamedWire.erase_root J, hJerase, hDJ']
  refine ⟨Q, (isQuorum_iff_q_le S.E Q).mp hQ, ?_⟩
  intro u hu
  obtain ⟨carrier, a, hcarrier, harow, hval, hpair⟩ := hwit u hu
  have hcarrierRun : Restated.RunBlockOn M S rho W Xb carrier :=
    Restated.runBlock_ancestorOn_FixedHeightRootCore facts hDrun hcarrier
  refine ⟨a,
    Or.inr ⟨carrier, hcarrierRun,
      (priv% Proofs.Vocabulary.Objects.FixedHeightRootCore
        DecoupledConsensusModel.Proofs.HealingSurface.mem_named_chain_attestations_own) harow⟩,
    hval, ?_⟩
  rw [hpair, hDhj', hroot]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, with the slashable bound over `Xb`, if `w ∈ Xb`, `P` is the erasure of
    the run block `Pn` of height at least `H`, and the `h_max` of `w`'s store in
    `W (strictEventIndex rho read)` is `H`, then that store's finalized block is compatible with
    `P`. -/
theorem finalizedCompatibleAtFixedHeightReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {H : Height} {w : V} (hw : w ∈ Xb)
    (read : Time) {P : Block V} {Pn : NamedBlock V}
    (hPnErase : Pn.erase = P) (hPrun : Restated.RunBlockOn M S rho W Xb Pn)
    (hPheight : H ≤ (M.derive_named S.E S.cfg Pn).h)
    (hfrontier : (W (strictEventIndex rho read) w).st.h_max = H) :
    Block.compatible (W (strictEventIndex rho read) w).st.F P = true := by
  let st := (W (strictEventIndex rho read) w).st
  have hmem := path_mem_stateBeforeTime₄₇b facts S Hs Xb hf read
  obtain ⟨Dst, hDstMem, hDstF, -⟩ :=
    Restated.Vocabulary.Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime facts S rho read w
      _ hmem
  have hDstMem' : Dst ∈ st.bodies := hDstMem
  have hDstF' : (M.derive_named S.E S.cfg Dst).F = st.F := hDstF
  have hDrun : Restated.RunBlockOn M S rho W Xb Dst :=
    Restated.runBlockOf_of_stateBeforeTime_memOn_FixedHeightRootCore facts S Hs Xb hf hw read
      hDstMem'
  have hnoHigh : Restated.Vocabulary.Internal.NamedNoHighJustifications M S.E S.cfg st :=
    Restated.Vocabulary.Proofs.NamedJustificationBound.noHighJustifications_stateBeforeTime facts S rho
      read w _ hmem
  have hbelow : st.h_j < st.h_max :=
    Restated.Vocabulary.Proofs.NamedJustificationBound.justificationBelowMax_stateBeforeTime facts S rho
      read w _ hmem
  have hcrossed : (M.derive_named S.E S.cfg Dst).h_F <
      (M.derive_named S.E S.cfg Pn).h := by
    calc
      (M.derive_named S.E S.cfg Dst).h_F ≤
          (M.derive_named S.E S.cfg Dst).h_j :=
        (facts.cs.chainOrder_derive_named S.E S.cfg Dst).heights_ordered
      _ ≤ st.h_j := hnoHigh Dst hDstMem'
      _ < st.h_max := hbelow
      _ = H := hfrontier
      _ ≤ (M.derive_named S.E S.cfg Pn).h := hPheight
  have hpreceq := Restated.finalized_preceq_of_height_ltOn facts S rho W Xb Pn Dst hsb
    hf.rootCollisionFree hPrun hDrun hcrossed
  rw [hDstF', hPnErase] at hpreceq
  exact compatible_of_cases (Or.inl hpreceq)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, with the slashable bound over `Xb` and the validators outside the set
    for the horizon weighing less than one third, if `w` is in the set for `read ≤ horizon`, `w`'s
    store in `W (strictEventIndex rho read)` holds `P` (the erasure of the run block `Pn` of height
    at least `H`) with `h_max = H`, and that store's finality-gadget root interferes with `P`, then
    `FixedHeightRootInterferenceAtReadOn` holds at that read, in the world
    `W (strictEventIndex rho read)`. -/
theorem fixedHeightRootInterferenceAtRead_of_interferenceOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : Execution.BelowOneThird S (Hs rho.horizon))
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {H : Height} {w : V}
    {read : Time} (hw : w ∈ Hs read) (hread : read ≤ rho.horizon) {P : Block V}
    (hPmem : P ∈ (W (strictEventIndex rho read) w).st.T)
    {Pn : NamedBlock V} (hPnErase : Pn.erase = P) (hPrun : Restated.RunBlockOn M S rho W Xb Pn)
    (hPheight : H ≤ (M.derive_named S.E S.cfg Pn).h)
    (hfrontier : (W (strictEventIndex rho read) w).st.h_max = H)
    (hint : Restated.Vocabulary.Proofs.HealingSurface.FGRootInterferenceAt M
      (W (strictEventIndex rho read) w).st P) :
    Restated.FixedHeightRootInterferenceAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)) P := by
  let st := (W (strictEventIndex rho read) w).st
  have hwXb : w ∈ Xb := hHsXb _ hw
  have hFsafe : Block.compatible st.F P = true :=
    Restated.finalizedCompatibleAtFixedHeightReadOn facts S Hs Xb hf hsb hwXb read hPnErase
      hPrun hPheight hfrontier
  have hrootBad : Block.compatible (M.get_fg_root (M.toHealing st.core).toFG) P = false := hint
  have hgate : st.core.h_max = st.core.h_j + 1 := by
    by_contra hne
    have hrootF : M.get_fg_root (M.toHealing st.core).toFG = st.core.F :=
      facts.fc.get_fg_root_toHealing_of_ne st.core hne
    rw [hrootF] at hrootBad
    have hF : Block.compatible st.core.F P = true := hFsafe
    rw [hF] at hrootBad
    contradiction
  have hrootJ : M.get_fg_root (M.toHealing st.core).toFG = st.core.J :=
    facts.fc.get_fg_root_toHealing_of_eq st.core hgate
  have hJbad : Block.compatible st.core.J P = false := by
    rw [hrootJ] at hrootBad
    exact hrootBad
  have hhj : st.h_j = H - 1 := by
    have hfrontier' : st.core.h_max = H := hfrontier
    exact Nat.eq_sub_of_add_eq (hgate.symm.trans hfrontier')
  have hJne : st.core.J ≠ Block.genesis := by
    intro hgen
    rw [hgen] at hJbad
    have htrue := Proofs.ModelProperties.compatible_eq_true_of_Preceq
      (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis P))
    rw [htrue] at hJbad
    exact Bool.noConfusion hJbad
  have hmem := path_mem_stateBeforeTime₄₇b facts S Hs Xb hf read
  obtain ⟨D, hDmem, hDJeq, hDhjeq⟩ :=
    Restated.Vocabulary.Proofs.Bridges.storeJustificationOnChain_stateBeforeTime facts S rho read w
      _ hmem
  have hDmem' : D ∈ st.bodies := hDmem
  have hDrun : Restated.RunBlockOn M S rho W Xb D :=
    Restated.runBlockOf_of_stateBeforeTime_memOn_FixedHeightRootCore facts S Hs Xb hf hwXb read
      hDmem'
  have hhjne : st.h_j ≠ 0 := by
    intro hz
    apply hJne
    exact hDJeq.symm.trans (facts.cs.justified_zero_is_genesis
      S.E S.cfg D (by rw [hDhjeq]; exact hz))
  have hcert : Restated.CertificateOn M S rho W Xb (H - 1) st.J.root := by
    have h := Restated.certificateOfStoreJustification_atStrictReadOn facts S Hs Xb hf hwXb
      read hhjne
    have hhj' : (W (strictEventIndex rho read) w).st.h_j = H - 1 := hhj
    rw [hhj'] at h
    exact h
  have htargetPos : 0 < H - 1 := by
    rw [← hhj]
    exact Nat.zero_lt_of_ne_zero hhjne
  refine
    { readerHonest := hw
      readInHorizon := hread
      protectedProcessed := hPmem
      protectedHeight := ⟨Pn, hPnErase, hPrun, hPheight⟩
      interference := hint
      carrierExists := ⟨D, hDmem', hDrun, hDJeq, hDhjeq⟩
      targetHeightPositive := htargetPos
      fixedTarget :=
        { frontier := hfrontier
          justificationHeight := hhj
          gate := hgate
          certificate := hcert
          uniqueAtHeight := ?_
          targetBlock := Restated.runBlockOf_justified_atStrictReadOn facts S Hs Xb hf hwXb read
          incompatible := hJbad } }
  intro T hT
  exact Restated.certificateTarget_uniqueOn facts S Hs Xb hf hHs hfb (H - 1) T st.J.root hT
    hcert

/-- On the path `W` of `hf`, with the slashable bound over `Xb` and the validators outside the set
    for the horizon weighing less than one third, if `w` is in the set for `read ≤ horizon`, `w`'s
    store in `W (strictEventIndex rho read)` holds `T` (the erasure of the run block `Tn` of height
    at least `H`) with `h_max = H`, and a run block `C` whose root is certified at `H − 1` is an
    ancestor of `T`, then that store's finality-gadget root is compatible with `T`. -/
theorem getFGRoot_compatible_of_fixedFrontier_certifiedPrefixOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : Execution.BelowOneThird S (Hs rho.horizon))
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {H : Height} {w : V}
    {read : Time} (hw : w ∈ Hs read) (hread : read ≤ rho.horizon) {T : Block V}
    (hTmem : T ∈ (W (strictEventIndex rho read) w).st.T)
    {Tn : NamedBlock V} (hTnErase : Tn.erase = T) (hTrun : Restated.RunBlockOn M S rho W Xb Tn)
    (hTheight : H ≤ (M.derive_named S.E S.cfg Tn).h)
    (hfrontier : (W (strictEventIndex rho read) w).st.h_max = H)
    {C : Block V} {Cn : NamedBlock V}
    (hCnErase : Cn.erase = C) (hCrun : Restated.RunBlockOn M S rho W Xb Cn)
    (hcert : Restated.CertificateOn M S rho W Xb (H - 1) C.root)
    (hCT : Block.Preceq C T) :
    Block.compatible
      (M.get_fg_root (W (strictEventIndex rho read) w).st.toHealing.toFG) T = true := by
  let st := (W (strictEventIndex rho read) w).st
  have hwXb : w ∈ Xb := hHsXb _ hw
  by_contra hnot
  have hrootBad : Block.compatible (M.get_fg_root (M.toHealing st.core).toFG) T = false :=
    Bool.eq_false_of_not_eq_true hnot
  have hFsafe : Block.compatible st.F T = true :=
    Restated.finalizedCompatibleAtFixedHeightReadOn facts S Hs Xb hf hsb hwXb read hTnErase
      hTrun hTheight hfrontier
  have hgate : st.core.h_max = st.core.h_j + 1 := by
    by_contra hne
    have hrootF : M.get_fg_root (M.toHealing st.core).toFG = st.core.F :=
      facts.fc.get_fg_root_toHealing_of_ne st.core hne
    rw [hrootF] at hrootBad
    have hF : Block.compatible st.core.F T = true := hFsafe
    rw [hF] at hrootBad
    contradiction
  have hrootJ : M.get_fg_root (M.toHealing st.core).toFG = st.core.J :=
    facts.fc.get_fg_root_toHealing_of_eq st.core hgate
  have hJbad : Block.compatible st.core.J T = false := by
    rw [hrootJ] at hrootBad
    exact hrootBad
  have hhj : st.h_j = H - 1 := by
    have hfrontier' : st.core.h_max = H := hfrontier
    exact Nat.eq_sub_of_add_eq (hgate.symm.trans hfrontier')
  have hJne : st.core.J ≠ Block.genesis := by
    intro hgen
    rw [hgen] at hJbad
    have htrue := Proofs.ModelProperties.compatible_eq_true_of_Preceq
      (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis T))
    rw [htrue] at hJbad
    exact Bool.noConfusion hJbad
  have hmem := path_mem_stateBeforeTime₄₇b facts S Hs Xb hf read
  obtain ⟨D, hDmem, hDJeq, hDhjeq⟩ :=
    Restated.Vocabulary.Proofs.Bridges.storeJustificationOnChain_stateBeforeTime facts S rho read w
      _ hmem
  have hhjne : st.h_j ≠ 0 := by
    intro hz
    apply hJne
    exact hDJeq.symm.trans (facts.cs.justified_zero_is_genesis
      S.E S.cfg D (by rw [hDhjeq]; exact hz))
  have hcertJ : Restated.CertificateOn M S rho W Xb (H - 1) st.J.root := by
    have h := Restated.certificateOfStoreJustification_atStrictReadOn facts S Hs Xb hf hwXb
      read hhjne
    have hhj' : (W (strictEventIndex rho read) w).st.h_j = H - 1 := hhj
    rw [hhj'] at h
    exact h
  have hroots : C.root = st.J.root :=
    Restated.certificateTarget_uniqueOn facts S Hs Xb hf hHs hfb (H - 1) C.root st.J.root
      hcert hcertJ
  obtain ⟨DJ, hDJe, hDJrun⟩ :=
    Restated.runBlockOf_justified_atStrictReadOn facts S Hs Xb hf hwXb read
  have hCnDJ : Cn = DJ :=
    hf.rootCollisionFree.root_injective Cn DJ hCrun hDJrun Cn DJ
      (Or.inl (Proofs.NamedAncestry.named_self Cn)) (Or.inr (Proofs.NamedAncestry.named_self DJ))
      (by rw [← Proofs.NamedWire.erase_root Cn, ← Proofs.NamedWire.erase_root DJ, hCnErase, hDJe]
          exact hroots)
  have hCeq : C = st.J := by
    rw [← hCnErase, hCnDJ, hDJe]
  have hJpre : Block.Preceq st.core.J T := by
    have h : Block.Preceq st.J T := by
      rw [← hCeq]
      exact hCT
    exact h
  have hcompatible : Block.compatible st.core.J T = true :=
    compatible_of_preceq_common_Preceq hJpre (preceq_eq_true_iff_Preceq.mp (Block.preceq_self T))
  rw [hJbad] at hcompatible
  contradiction

/-- On the path `W` of `hf`, under the hypotheses of
    `getFGRoot_compatible_of_fixedFrontier_certifiedPrefixOn`, with `Tn` a body of `w`'s store in
    `W (strictEventIndex rho read)`, the finality filters of that store do not interfere with `T`
    (`FinalityFilterNoninterferenceAtRead` at that world). -/
theorem finalityFilterNoninterferenceAtRead_of_fixedFrontier_certifiedPrefixOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : Execution.BelowOneThird S (Hs rho.horizon))
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {H : Height} {w : V}
    {read : Time} (hw : w ∈ Hs read) (hread : read ≤ rho.horizon) {T : Block V}
    (hTmem : T ∈ (W (strictEventIndex rho read) w).st.T)
    {Tn : NamedBlock V} (hTnMem : Tn ∈ (W (strictEventIndex rho read) w).st.bodies)
    (hTnErase : Tn.erase = T) (hTrun : Restated.RunBlockOn M S rho W Xb Tn)
    (hTheight : H ≤ (M.derive_named S.E S.cfg Tn).h)
    (hfrontier : (W (strictEventIndex rho read) w).st.h_max = H)
    {C : Block V} {Cn : NamedBlock V}
    (hCnErase : Cn.erase = C) (hCrun : Restated.RunBlockOn M S rho W Xb Cn)
    (hcert : Restated.CertificateOn M S rho W Xb (H - 1) C.root)
    (hCT : Block.Preceq C T) :
    Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w read
      (W (strictEventIndex rho read)) T := by
  have hcompatible :=
    Restated.getFGRoot_compatible_of_fixedFrontier_certifiedPrefixOn facts S Hs Xb hf hHs hHsXb
      hfb hsb hw hread hTmem hTnErase hTrun hTheight hfrontier hCnErase hCrun hcert hCT
  unfold Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead
  rcases compatible_cases hcompatible with hrootT | hTroot
  · right
    by_contra hnotFiltered
    have hprogress := Restated.filteredOut_hMax_of_root_preceqOn facts S Hs Xb hf hw
      hTnMem hTheight (by rw [hTnErase]; exact hrootT)
      (by rw [hTnErase]; exact hnotFiltered)
    rw [hfrontier] at hprogress
    exact (Nat.not_succ_le_self H)
      ((Nat.le_succ (H + 1)).trans hprogress)
  · exact Or.inl hTroot

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `0 < s`, `s`'s vote time is within the horizon and at least `lo`,
    every committee member in the set for that time has a vote store, staged from its node state in
    `W` strictly before that time, extending `B` (`hstores`), and each such member's tick at the
    vote time has an outcome (`hneTick`) from a node state that passes the grade-1 awake test of
    `s`'s round (`hrun`), then every such member's slot-`s` vote names `B`. -/
theorem honestVotesName_of_voteStoresExtendOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} (hs : 0 < s)
    (hvoteHor : M.vote_time S.E s ≤ rho.horizon)
    (hgat : lo ≤ M.vote_time S.E s)
    {B : NamedBlock V}
    (hstores : Restated.VoteStoresExtendOn M S rho Hs s
      (W (strictEventIndex rho (M.vote_time S.E s))) B)
    (hneTick : ∀ v ∈ Hs (M.vote_time S.E s), v ∈ S.E.committee s → ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (M.vote_time S.E s)) →
      ∃ out : M.N × List (NamedObject V), M.tick S v (W j v) (M.vote_time S.E s) ⇢ out)
    (hrun : ∀ v ∈ Hs (M.vote_time S.E s), v ∈ S.E.committee s →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (M.vote_time S.E s)) →
        M.awake_for_grade1 S v (W j v) (M.round_of S.hc s)) :
    Restated.NamedHonestVotesNameOn M S rho W Hs s B.erase :=
  Restated.honestVotesName_of_extendsOn facts S rho W Hs s B
    (Restated.voteTickExtends_of_extendsOn facts S Hs Xb hf hs hvoteHor hgat hstores hneTick hrun)

end

/-! ## Finalized roots of bodies at bounded finalized height -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- For every member `v` of `X`, every time `t` and every named body `C` of `v`'s store in the world
    `Wt t`, if `C`'s finalized height is at most `cap` then `C`'s finalized block is an ancestor of
    `P`. -/
def FinalizedRootsBelowAtReadOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (Wt : Time → V → M.N) (X : Finset V) (cap : Height) (P : Block V) : Prop :=
  ∀ v ∈ X, ∀ t : Time, ∀ C ∈ (Wt t v).st.bodies,
    (M.derive_named S.E S.cfg C).h_F ≤ cap → Block.Preceq (M.derive_named S.E S.cfg C).F P

/-- If the named bodies of `st` contain the parent of each of them, every named ancestor of a body
    of `st` is a body of `st`. -/
private theorem ancestor_body_mem₄₇w {st : M.NS}
    (hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
    exact hAB ▸ hB
  | node parent s root votes support rows proposer ih =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at hAB
    rcases hAB with rfl | hparent
    · exact hB
    · have hp := hpc.2 _ hB
      rw [Proofs.ModelProperties.named_parent_node] at hp
      exact ih hp (by simp only [NamedBlock.Preceq]; exact hparent)

/-- On the path `W` of `hf`, if `X ⊆ Xb`, the slashable bound holds over `Xb`, `P` is a run block
    read through `Xb`, and `cap` is less than `P`'s height, then `FinalizedRootsBelowAtReadOn` holds
    for the worlds `fun t => W (strictEventIndex rho t)`, `X`, `cap` and `P`. -/
theorem finalizedRootsBelowAtRead_of_accountableOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (hX : X ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb) {cap : Height} {P : NamedBlock V}
    (hP : Restated.RunBlockOn M S rho W Xb P)
    (hheight : cap < (M.derive_named S.E S.cfg P).h) :
    Restated.FinalizedRootsBelowAtReadOn M S rho (fun t => W (strictEventIndex rho t)) X cap
      P.erase := by
  intro v hv t C hC hcap
  have hCrun : Restated.RunBlockOn M S rho W Xb C :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb (hX hv) (i := strictEventIndex rho t) hC
  exact Restated.finalized_preceq_of_height_ltOn facts S rho W Xb P C hsb hf.rootCollisionFree
    hP hCrun (hcap.trans_lt hheight)

/-- If `v ∈ X`, the world `Wt time` can hold strictly before `time`, `FinalizedRootsBelowAtReadOn`
    holds for `Wt`, `X`, `cap` and `P`, `v`'s `h_max` in `Wt time` is greater than `cap + 1`, and
    `D` is a body of `v`'s store there whose erasure is that store's finality-gadget root and whose
    height is at most `cap`, then that root is an ancestor of `P`. -/
theorem lowFGRoot_preceq_of_frontier_gap_of_finalizedRootsBelowOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (X : Finset V) {Wt : Time → V → M.N}
    {v : V} (hv : v ∈ X) {time : Time} {cap : Height} {P : Block V}
    (hWt : Wt time ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho time)
    (hlegacy : Restated.FinalizedRootsBelowAtReadOn M S rho Wt X cap P)
    (hfrontier : cap + 1 < (Wt time v).st.core.h_max)
    {D : NamedBlock V}
    (hD : D ∈ (Wt time v).st.bodies)
    (hDR : D.erase = M.get_fg_root (M.toHealing (Wt time v).st.core).toFG)
    (hheight : (M.derive_named S.E S.cfg D).h ≤ cap) :
    Block.Preceq (M.get_fg_root (M.toHealing (Wt time v).st.core).toFG) P := by
  have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (Wt time v).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho time v
      (Wt time) hWt).1.1.1
  have hpc := hcoh.2.2.1
  by_cases hgate : (Wt time v).st.core.h_max = (Wt time v).st.core.h_j + 1
  · have hroot : M.get_fg_root (M.toHealing (Wt time v).st.core).toFG = (Wt time v).st.core.J :=
      facts.fc.get_fg_root_toHealing_of_eq (Wt time v).st.core hgate
    obtain ⟨J, hJ, hJJ', hJh'⟩ :=
      Restated.Vocabulary.Proofs.Bridges.storeJustificationOnChain_stateBeforeTime facts S rho time v
        (Wt time) hWt
    rcases facts.cs.justified_ancestor_height S.E S.cfg J with
      hz | ⟨K, hKJ, hKerase, hKheight⟩
    · have hgen : (M.derive_named S.E S.cfg J).J = Block.genesis :=
        facts.cs.justified_zero_is_genesis S.E S.cfg J hz
      have hstJ : (Wt time v).st.core.J = Block.genesis := hJJ'.symm.trans hgen
      rw [hroot, hstJ]
      exact preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis P)
    · have hK : K ∈ (Wt time v).st.bodies := ancestor_body_mem₄₇w hpc hJ hKJ
      have hKD : K.erase = D.erase := by
        calc
          K.erase = (M.derive_named S.E S.cfg J).J := hKerase
          _ = (Wt time v).st.core.J := hJJ'
          _ = M.get_fg_root (M.toHealing (Wt time v).st.core).toFG := hroot.symm
          _ = D.erase := hDR.symm
      have hKD' : K = D := hcoh.2.1 K hK D hD hKD
      have hDheight : (M.derive_named S.E S.cfg D).h = (Wt time v).st.core.h_j :=
        (congrArg (fun X => (M.derive_named S.E S.cfg X).h) hKD'.symm).trans
          (hKheight.trans hJh')
      have hcap : (Wt time v).st.core.h_j ≤ cap := by
        rw [← hDheight]
        exact hheight
      have hmax : (Wt time v).st.core.h_max ≤ cap + 1 := by
        rw [hgate]
        exact Nat.add_le_add_right hcap 1
      exact False.elim ((Nat.not_lt_of_ge hmax) hfrontier)
  · have hroot : M.get_fg_root (M.toHealing (Wt time v).st.core).toFG = (Wt time v).st.core.F :=
      facts.fc.get_fg_root_toHealing_of_ne (Wt time v).st.core hgate
    obtain ⟨F, hF, hFF', hFh⟩ :=
      Restated.Vocabulary.Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime facts S rho time v
        (Wt time) hWt
    rcases facts.csAdded.finalized_ancestor_height S.E S.cfg F with
      hz | ⟨K, hKF, hKerase, hKheight⟩
    · have hgen : (M.derive_named S.E S.cfg F).F = Block.genesis :=
        facts.cs.finalized_zero_is_genesis S.E S.cfg F hz
      have hstF : (Wt time v).st.core.F = Block.genesis := hFF'.symm.trans hgen
      rw [hroot, hstF]
      exact preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis P)
    · have hK : K ∈ (Wt time v).st.bodies := ancestor_body_mem₄₇w hpc hF hKF
      have hKD : K.erase = D.erase := by
        calc
          K.erase = (M.derive_named S.E S.cfg F).F := hKerase
          _ = (Wt time v).st.core.F := hFF'
          _ = M.get_fg_root (M.toHealing (Wt time v).st.core).toFG := hroot.symm
          _ = D.erase := hDR.symm
      have hKD' : K = D := hcoh.2.1 K hK D hD hKD
      have hDheight : (M.derive_named S.E S.cfg D).h = (M.derive_named S.E S.cfg F).h_F :=
        (congrArg (fun X => (M.derive_named S.E S.cfg X).h) hKD'.symm).trans hKheight
      have hcap : (M.derive_named S.E S.cfg F).h_F ≤ cap := by
        rw [← hDheight]
        exact hheight
      rw [hroot, ← hFF']
      exact hlegacy v hv time F hF hcap

/-- If the events at indices `i` and `j` are ticks at times `ti < tj`, then `i < j`. -/
theorem attestationIndex_lt_of_time_ltOn (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {i j : Nat} {u v : V} {ti tj : Time}
    (hi : rho.events[i]? = some (Record.Event.tick u ti))
    (hj : rho.events[j]? = some (Record.Event.tick v tj)) (ht : ti < tj) : i < j := by
  by_contra hnot
  rcases lt_or_eq_of_le (Nat.le_of_not_gt hnot) with hji | rfl
  · have hkey := Restated.key_le_of_index_ltOn facts S Hs Xb hf hji hj hi
    exact (not_le_of_gt ht) (Restated.time_le_of_key_le hkey)
  · have heq := Option.some.inj (hi.symm.trans hj)
    have htime : ti = tj := congrArg Record.Event.time heq
    exact (lt_irrefl ti) (htime ▸ ht)

/-- If `hseed` is a `PrefixFGSelectorConeAtOn` seed starting at or after
    `strictEventIndex rho (S.a r0)`, and `gstLagged S` is at most `Γ_neg1` of round `r0`, then the
    round of the seed attestation `a` is grade-ready. -/
theorem PrefixFGSelectorConeAtOn.ready_of_postGSTStart (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} {Wt : Time → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {start stop : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time} {Cfg : NamedBlock V}
    {T : Block V}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W Wt Hs Xb start stop blocked i a ta Cfg T)
    {r0 : Round}
    (hgst : gstLagged S ≤ Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hstart : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0) ≤ start) :
    Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round := by
  have hhor : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ rho.horizon := by
    have hin := (hf.in_horizon (Record.Event.tick a.val_index ta)
      (List.mem_of_getElem? hseed.exactTick)).2
    simpa only [Record.Event.time, hseed.actionTime_eq, Record.Event.time] using hin
  have hround : r0 ≤ a.round := by
    by_contra hnot
    have htimeLt : ta < Restated.Vocabulary.Execution.Setup.a M S r0 := by
      rw [hseed.actionTime_eq]
      exact Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S
        (Nat.lt_of_not_ge hnot)
    have htimeLe : Restated.Vocabulary.Execution.Setup.a M S r0 ≤ ta :=
      Restated.le_time_of_index_geOn facts S Hs Xb hf (hstart.trans hseed.startLeIndex)
        hseed.exactTick
    exact (not_le_of_gt htimeLt) htimeLe
  exact Restated.Vocabulary.Proofs.HealingSurface.gradeRoundReady_of_action_horizon facts S hgst
    hround hhor

end

/-! ## Votes following a selected grade-2 action block -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `0 < s`, `s`'s vote time is within the horizon and at least `lo`,
    `w`, in the set for that time, is in `s`'s committee, `w`'s tick at that time has an outcome
    (`hneTick`) from a node state that passes the grade-1 awake test of `s`'s round (`hrun`), then
    for an outcome `c` of the phase tick (`hc`), every head `Hd` the in-tree head computation can
    return at the vote-duty node state `n` staged with `c` is the erasure of a run block `C` read
    through `Xb`, and `w` emits at the vote time the slot-`s` vote naming `C`'s root. -/
theorem preparedVoteHead_runBlock_and_emitsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} (hs : 0 < s)
    (hhor : M.vote_time S.E s ≤ rho.horizon)
    {w : V} (hw : w ∈ Hs (M.vote_time S.E s)) (hgat : lo ≤ M.vote_time S.E s)
    (hcommittee : w ∈ S.E.committee s)
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E s)) →
      ∃ out : M.N × List (NamedObject V), M.tick S w (W j w) (M.vote_time S.E s) ⇢ out)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E s)) →
      M.awake_for_grade1 S w (W j w) (M.round_of S.hc s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing
      (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) w).cache ⇢ c) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st (M.vote_time S.E s))
      (W (strictEventIndex rho (M.vote_time S.E s)) w).record c
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
    ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ Hd →
    ∃ C : NamedBlock V, C.erase = Hd ∧
      Restated.blockInRunOn M S rho W Xb C ∧
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W w
        (Object.gfVote ⟨w, s, C.erase.root⟩)
        (M.vote_time S.E s) := by
  intro n T hT L hL L' hL' Hd hHd
  set i := strictEventIndex rho (M.vote_time S.E s) with hi_def
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W i w).st (M.vote_time S.E s)) c :=
    facts.nd.mkNode_st _ _ _
  have hcache : n.cache = c := facts.nd.mkNode_cache _ _ _
  have hslot : n.st.core.s = s := by
    rw [hnst, facts.nd.store_with_cache_core_s, facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
  have hstT : n.st.core.T = (W i w).st.core.T := by
    rw [hnst, facts.nd.store_with_cache_core_T, facts.hd.Sts_setClock_core_T]
  have hinvPre := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i w
    (W i) (hf.onePath i).1).1
  have hinv := facts.hd.invariant_clock S.E S.cfg (W i w).st (M.vote_time S.E s) hinvPre
  have hrootMem : M.get_fg_root (M.toHealing n.st.core).toFG ∈ n.st.core.T := by
    rw [hnst, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_core_T]
    exact Restated.Vocabulary.Proofs.NamedStoreRoots.fg_root_mem facts _ hinv.1.2
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s)
  have hRmem : R ∈ n.st.core.T := by
    have h := Restated.Vocabulary.Proofs.NamedProposalParent.frame_anchor_mem facts S.E S.hc
      (M.toHealing n.st.core) _ _
      (by
        show M.get_fg_root (M.toHealing n.st.core).toFG ∈
          (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.T
        rw [facts.sto.toHealing_gs_T]
        exact hrootMem) R
      ((facts.nd.gradeContract_sgRoot_eq_frameAnchor _ _ _ _ _ _).mp hR)
    have h' : R ∈ (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.T := h
    rw [facts.sto.toHealing_gs_T] at h'
    exact h'
  have hHmem := facts.fc.Sts_get_head_in_tree_with_layer_mem _ S.E S.hc _ T L L' _ R hR hRmem
    (facts.hd.Sts_voter_filtered_block_tree_subset S.E n.st.core n.st.core.s T hT) Hd hHd
  have hHpre : Hd ∈ (W i w).st.core.T := by
    rw [← hstT]
    exact hHmem
  obtain ⟨C, hCerase, hCrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hw)
      (M.vote_time S.E s) hHpre
  obtain ⟨D, hD⟩ := facts.dt.goldfish_vote_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node w) n.st
  have hout : D.2 = some ⟨(S.node w).val_index, n.st.core.s, Hd.root⟩ :=
    facts.fc.goldfish_vote_with_snd_of_mem_committee _ S.E S.hc (S.node w) n.st
      (by rw [S.node_val_index, hslot]; exact hcommittee) D hD T hT L hL L' hL' Hd hHd
  rw [S.node_val_index, hslot] at hout
  rw [hcache, hnst, facts.dt.duties_goldfish_vote_with_store_with_cache] at hD
  have ho : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E s)) →
      ∀ out ∈ Restated.Vocabulary.Execution.on_tick_emit M S w (W j w) (M.vote_time S.E s),
        Object.gfVote ⟨w, s, Hd.root⟩ ∈ out.2 := by
    intro j hj
    have haw := hrun j hj
    rcases Restated.stateBefore_tick_eq_stateBeforeTimeOn facts S Hs Xb hf hj with hj' | hj'
    · rw [hj'] at haw ⊢
      have _hr_s1 := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 w
      have _hv_s2 := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 w
      exact Restated.Vocabulary.Proofs.Optimistic.on_tick_emit_vote_mem facts S w (W i w) s hs c hc
        D hD hout haw
    · rw [hj'] at haw ⊢
      have hst' := (facts.nd.wake_st_record (W i w)).1
      have hca' := facts.nd.wake_cache (W i w)
      have _hr_s3 := facts.nd.reachedNode_wake _ (facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 w)
      have _hv_s4 := facts.nd.runs_as_wake _ w (facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 w)
      exact Restated.Vocabulary.Proofs.Optimistic.on_tick_emit_vote_mem facts S w (M.wake (W i w)) s
        hs c (by rw [hst', hca']; exact hc) D (by rw [hst']; exact hD) hout haw
  have hemit := Restated.emits_of_on_tick_emitOn facts S Hs Xb hf hw
    (Restated.Vocabulary.Proofs.Optimistic.publicTime_vote_time facts S s) hgat hhor hneTick ho
  refine ⟨C, hCerase, hCrun, ?_⟩
  rw [hCerase]
  exact hemit

/-- On the path `W` of `hf`, if `u` is in the set for `S.a r`, a node state `nu` of `u`'s round-`r`
    action read in `W (strictEventIndex rho (S.a r))` selects the grade-2 block `Q`, `s` is a
    positive slot of round `r` whose vote time is after the round's grade-1 domain time, at most
    `S.a r` and within the horizon, `lo` is at most that domain time, and every committee member of
    `s` in the set for its vote time satisfies `htransport`, `hvoteDisposition` and `hrun`, then
    every such member emits a slot-`s` vote naming a run block that `Q` is an ancestor of. -/
theorem honestVotesCone_of_selectedActionG2_of_readDispositionOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r)
    (_ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {u : V} (hu : u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S r)) {Q : Block V}
    (nu : M.N)
    (hnu : nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r)
    (hsource : M.grade2_block_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
      r ⇢ some Q)
    {s : Slot} (hs : 0 < s)
    (hround : M.round_of S.hc s = r)
    (hread : M.domain S.E S.hc r .g1 < M.vote_time S.E s)
    (hta : M.vote_time S.E s ≤ Restated.Vocabulary.Execution.Setup.a M S r)
    (hhor : M.vote_time S.E s ≤ rho.horizon)
    (hgat : lo ≤ M.domain S.E S.hc r .g1)
    (htransport : ∀ w ∈ Hs (M.vote_time S.E s), w ∈ S.E.committee s →
      Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w) ∧
      Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st r .g1 Q ⇢ true ∧
      Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (W (strictEventIndex rho (M.vote_time S.E s)) w))
    (hvoteDisposition : ∀ w ∈ Hs (M.vote_time S.E s), w ∈ S.E.committee s →
      Block.Preceq Q (M.get_fg_root (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E s)) w).st (M.vote_time S.E s)).core).toFG) ∨
      Q ∈ M.get_filtered_block_tree (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E s)) w).st (M.vote_time S.E s)).core).toFG)
    (hrun : ∀ w ∈ Hs (M.vote_time S.E s), w ∈ S.E.committee s →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E s)) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc s)) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq Q X) := by
  intro w hw hcommittee
  obtain ⟨hdom, hgrade, hreadMem⟩ := htransport w hw hcommittee
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing (M.vote_time S.E s)
    (W (strictEventIndex rho (M.vote_time S.E s)) w).cache
  have hdisp := hvoteDisposition w hw hcommittee
  rw [← facts.nd.store_with_cache_get_fg_root _ c,
    ← facts.nd.store_with_cache_get_filtered_block_tree _ c,
    ← facts.nd.mkNode_st (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
    (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record c] at hdisp
  set n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
    (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record c with hn
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨Hd, hHd⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract n.cache) S.E
    S.hc (M.toHealing n.st.core) T L L' (n.st.core.s - 1)
  have hQX : Block.Preceq Q Hd := by
    rcases hdisp with hroot | hactive
    · obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s)
      obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc n.st.core.s)
        (M.readFrame n.cache (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s)).g1
      have hGa := facts.nd.ModelProperties_gradeContract_read_anchor _ _ _ _ _ G hG a ha
      have hQa : Block.Preceq Q a := facts.gr.preceq_anchor_of_fgRoot S.E S.hc _ _ _ hroot a ha
      have hhead : Block.Preceq G.anchor Hd :=
        facts.fc.read_anchor_preceq_get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) T L L' (n.st.core.s - 1) G
          (by rw [facts.sto.toHealing_s]; exact hG) Hd hHd
      rw [hGa] at hhead
      exact Proofs.ModelProperties.Preceq_trans hQa hhead
    · exact Restated.selectedActionG2_preceq_sameRoundVoteDutyHead_of_activeAtVoteOn facts
        S Hs Xb hf hr hu nu hnu hsource hround (hHs _ _ (le_of_lt hread) hw) hgat hread hta
        (le_trans (le_of_lt hread) hhor) hdom hgrade hreadMem
        (fun j hj => hf.tick_outcome j _ _ hj) c hc hactive
        T hT L hL L' hL' Hd hHd
  obtain ⟨C, hCerase, hCrun, hemit⟩ :=
    preparedVoteHead_runBlock_and_emitsOn facts S Hs Xb hf hHsXb hs hhor hw
      (hgat.trans (le_of_lt hread)) hcommittee (fun j hj => hf.tick_outcome j _ _ hj)
      (hrun w hw hcommittee) c hc T hT L hL L' hL' Hd hHd
  exact ⟨C, by rw [hCerase]; exact hQX, hCrun, hemit⟩

end

end DecoupledConsensusModel.Sts.Restated
