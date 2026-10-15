import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_26
import Proofs.Claims.Restated.Claim13beRoute3_29
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Vocabulary_Execution_BodyRetention
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_Execution_OutageProvenance
import Proofs.Claims.Restated.Vocabulary_Execution_ReceiptCallsBase
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry
import Proofs.Claims.Restated.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_GuardedGradeHelpers
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_OppositionGradeTransport
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockAdmission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockStamp
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_FinalityMonotoneCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_FinalizationBridge
import Proofs.Vocabulary.Protocol.Handlers.HandlerAdmissionGuards
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_JustificationBound
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_ReceiptCallsGF
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_HeldSkipProducers
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDerived
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_ModelVocabulary_Execution_GradeRuntime_Transport
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Vocabulary.Protocol.Grades
import Model.Conditions.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Model.Conditions.Vocabulary_Protocol_Grades_RelativeCrossReader
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Statements_Instantiation_Certificates
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13beRoute3_53b

/-!
# Finality relay and cross-reader facts

Theorems read along the path `W` of a run satisfying `AdmissibleFieldsOn`, over a model
`M : Record.Model V` and its facts: an accepted block's derived finalized block becomes an ancestor
of the receiver's, finalized blocks are ordered across one delay, the cross-reader conditions of the
grade readers, and the acceptance of SG votes after two cutoffs.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open scoped DC
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

/-- `NamedProvenance` of a named store is kept when its clock is set to `t`. -/
private theorem namedProvenance_setClock₅₃b (facts : Record.Facts M) (S : Setup V) (st : M.NS)
    (t : Int) (h : Restated.Vocabulary.Proofs.Bridges.NamedProvenance M S st) :
    Restated.Vocabulary.Proofs.Bridges.NamedProvenance M S (M.ns_setClock S.E st t) := by
  obtain ⟨⟨D, hD, hF, hh⟩, ⟨D', hD', hJ, hj⟩⟩ := h
  refine ⟨⟨D, ?_, ?_, ?_⟩, ⟨D', ?_, ?_, ?_⟩⟩
  · rw [facts.hd.ModelProperties_setClock_bodies]; exact hD
  · rw [facts.hd.setClock_core_F]; exact hF
  · rw [facts.hd.setClock_core_h_max]; exact hh
  · rw [facts.hd.ModelProperties_setClock_bodies]; exact hD'
  · rw [facts.hd.setClock_core_J]; exact hJ
  · rw [← facts.sto.toHealing_h_j, facts.hd.setClock_toHealing_h_j]; exact hj

/-- Along a path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` lead to
    from `W m`. -/
private theorem onePath_reach₅₃b {S : Setup V} {rho : Record.Run V}
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
private theorem onePath_slice₅₃b {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {m n : Nat} (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Nat.add_sub_cancel_left]
  exact onePath_reach₅₃b W hW m k

/-- Along a path `W`, for `m ≤ n`, `v`'s finalized block in `W m` is an ancestor of its finalized
    block in `W n`. -/
private theorem path_F_mono₅₃b (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (v : V) {m n : Nat} (hmn : m ≤ n) :
    Block.Preceq (W m v).st.core.F (W n v).st.core.F :=
  Restated.Vocabulary.Protocol.stateBefore_F_mono facts S rho v hmn (W m) (hW m).1 (W n)
    (onePath_slice₅₃b W hW hmn)

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event among the first `strictEventIndex rho t` events is at a time
    before `t`. -/
private theorem time_lt_of_lt_strict₅₃b {rho : Record.Run V}
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

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If `target ∈ Xb`, `B` is a run block, a call of `target` at event `i` along `W` inserts `B` new
    into its store, and `B`'s derived finalized block is a descendant of `target`'s finalized block
    in `W i`, then the store after the call has `B`'s derived finalized block as an ancestor of its
    finalized block. -/
theorem fresh_receipt_absorbs_finalityOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hsb : Restated.SlashableBoundOn M S rho W Xb) {i : Nat} {target : V}
    (htarget : target ∈ Xb) (B : NamedBlock V)
    (hBscope : Restated.blockInRunOn M S rho W Xb B)
    (before : M.NS)
    (hcall : Restated.Vocabulary.Execution.NamedReceiptCalls.blockCallAt M
      S rho W i target B before)
    (hnew : B.erase ∉ before.core.T)
    (hpost : B.erase ∈
      (M.postCore S before B).core.T)
    (hfloor : Block.Preceq
      (W i target).st.core.F
      (M.derive_named S.E S.cfg B).F) :
    Block.Preceq (M.derive_named S.E S.cfg B).F
      (M.postCore S before B).core.F := by
  have _hr_0 : M.reachedNode (W i target) := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 target
  have hW := hf.onePath
  have hWi := (hW i).1
  have hco : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg before :=
    (Restated.Vocabulary.Proofs.NamedReceiptCallsBase.block_call_before_invariant facts S rho W hW
      hcall).1.1
  have hinputF : before.core.F = (W i target).st.core.F := by
    rcases hcall with ⟨time, -, rfl⟩ | ⟨time, -, -, rfl⟩
    · rfl
    · exact facts.hd.setClock_core_F _ _ _
  have hfloorBefore : Block.Preceq before.core.F (M.derive_named S.E S.cfg B).F := by
    rw [hinputF]
    exact hfloor
  have hfacts :
      (∀ D ∈ before.bodies, Restated.RunBlockOn M S rho W Xb D) ∧
      Restated.Vocabulary.Internal.NamedNoHighJustifications M S.E S.cfg before ∧
      Restated.Vocabulary.Proofs.Bridges.NamedProvenance M S before ∧
      (∃ D ∈ before.bodies,
        (M.derive_named S.E S.cfg D).h =
          before.core.h_max) := by
    rcases hcall with ⟨time, -, rfl⟩ | ⟨time, -, -, rfl⟩
    · refine ⟨?_, Restated.Vocabulary.Proofs.NamedJustificationBound.noHighJustifications_stateBefore facts
          S rho i target (W i) hWi,
        Restated.Vocabulary.Proofs.Bridges.namedProvenance_stateBefore facts S rho i target (W i) hWi,
        Restated.Vocabulary.Proofs.NamedStoreBridge.maximum_carrier_stateBefore facts S rho i target
          (W i) hWi⟩
      intro D hD
      exact Restated.runBlock_of_stateBefore_memOn facts S W Xb htarget hD
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro D hD
        rw [facts.hd.ModelProperties_setClock_bodies] at hD
        exact Restated.runBlock_of_stateBefore_memOn facts S W Xb htarget hD
      · intro D hD
        rw [facts.hd.ModelProperties_setClock_bodies] at hD
        rw [← facts.sto.toHealing_h_j, facts.hd.setClock_toHealing_h_j]
        exact (Restated.Vocabulary.Proofs.NamedJustificationBound.noHighJustifications_stateBefore facts
          S rho i target (W i) hWi) D hD
      · exact namedProvenance_setClock₅₃b facts S _ _
          (Restated.Vocabulary.Proofs.Bridges.namedProvenance_stateBefore facts S rho i target (W i) hWi)
      · rw [facts.hd.ModelProperties_setClock_bodies, facts.hd.setClock_core_h_max]
        exact Restated.Vocabulary.Proofs.NamedStoreBridge.maximum_carrier_stateBefore facts S rho i target
          (W i) hWi
  have _hrs_before : M.reachedStore before := by
    rcases hcall with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩
    · exact facts.nd.reachedStore_of_node _ _hr_0
    · exact facts.sto.reachedStore_setClock _ _ _ (facts.nd.reachedStore_of_node _ _hr_0)
  refine facts.nd.postCore_absorbs_finality S before B hco hnew hpost hfloorBefore ?_ hfacts.2.2.2 ?_
  · intro A hA hAJ hAh
    exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp (Restated.upgradeOn facts hfacts.2.1
      hfacts.2.2.1 hA ⟨hAJ, hAh⟩ hsb hf.rootCollisionFree hBscope hfacts.1 ⟨rfl, rfl⟩)
  · intro D hD hlt
    exact Restated.finalized_preceq_of_height_ltOn facts S rho W Xb D B hsb hf.rootCollisionFree
      (hfacts.1 D hD) hBscope hlt

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Two run blocks read through `Xb` along `W` with the same erasure are equal. -/
theorem runBlock_unique_of_erase_eqOn_RelativeCrossReader (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {A B : NamedBlock V} (hA : Restated.blockInRunOn M S rho W Xb A)
    (hB : Restated.blockInRunOn M S rho W Xb B) (herase : A.erase = B.erase) :
    A = B :=
  hf.rootCollisionFree.root_injective A B hA hB A B
    (Or.inl (Proofs.NamedAncestry.named_self A))
    (Or.inr (Proofs.NamedAncestry.named_self B)) (by
      rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root B, herase])

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If `reader ∈ Xb` holds `B` in `W (strictEventIndex rho time)`, its tree there finds `B`'s
    erasure at `B`'s root. -/
theorem held_find_at_strictOn_RelativeCrossReader (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {reader : V} (hreader : reader ∈ Xb) (time : Time)
    (B : NamedBlock V)
    (hB : B ∈ (W (strictEventIndex rho time) reader).st.bodies) :
    Block.find?
      (W (strictEventIndex rho time) reader).st.core.T B.root =
        some B.erase := by
  rw [← Proofs.NamedWire.erase_root B]
  exact Restated.held_find_at_strictOn_HealthyHeadReady facts S rho Hs Xb hf reader hreader time B hB

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If `target ∈ Xb` accepts the run block `B` at event `i` along `W`, and `B`'s derived finalized
    block is a descendant of `target`'s finalized block in `W i`, then it is an ancestor of
    `target`'s finalized block in `W (i + 1)`. -/
theorem accepted_carrier_finality_preceqOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hsb : Restated.SlashableBoundOn M S rho W Xb) {target : V}
    (htarget : target ∈ Xb) {i : Nat} {B : NamedBlock V}
    {t : Time} (hBscope : Restated.blockInRunOn M S rho W Xb B)
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i target (.block B) t)
    (hfloor : Block.Preceq
      (W i target).st.core.F
      (M.derive_named S.E S.cfg B).F) :
    Block.Preceq (M.derive_named S.E S.cfg B).F
      (W (i + 1) target).st.core.F := by
  obtain ⟨before, hcall, hnew, hpost, hbridge⟩ :=
    Restated.Vocabulary.Proofs.NamedOutageHistory.HeldSkipProducers.accepted_block_fresh_call facts
      S rho i target B t W hf.onePath hacc
  exact preceq_trans_Preceq
    (Restated.fresh_receipt_absorbs_finalityOn facts S rho Hs Xb hf hsb htarget B hBscope
      before hcall hnew hpost hfloor) hbridge

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If `source` is in the set for `read`, `target` in the set for `out = read + Δ`, `lo ≤ read` and
    `out` is inside the horizon, then `source`'s finalized block in `W (strictEventIndex rho read)`
    is an ancestor of `target`'s finalized block in `W (strictEventIndex rho out)`. -/
theorem finalized_preceq_of_evidence_deliveredOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb) {source target : V} {read out : Time}
    (hsource : source ∈ Hs read) (htarget : target ∈ Hs out)
    (hpost : lo ≤ read)
    (hhop : read + S.E.Δ = out) (hhor : out ≤ rho.horizon) :
    Block.Preceq
      (W (strictEventIndex rho read) source).st.core.F
      (W (strictEventIndex rho out) target).st.core.F := by
  have hW := hf.onePath
  have hsafe := Restated.stateBeforeTime_finalized_compatibleOn facts S rho Hs Xb hf hsb
      hf.rootCollisionFree read out source target (hHsXb _ hsource) (hHsXb _ htarget)
  rcases compatible_cases hsafe with hforward | hreverse
  · exact hforward
  · obtain ⟨D, hDread, hDF, -⟩ :=
      Restated.Vocabulary.Proofs.NamedFinalizationBridge.finalization_carrier_stateBefore facts
        S rho (strictEventIndex rho read) source (W (strictEventIndex rho read))
        (hW (strictEventIndex rho read)).1
    have hDscope : Restated.blockInRunOn M S rho W Xb D :=
      Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hsource) hDread
    rcases Restated.Vocabulary.Proofs.NamedOutageProvenance.held_block_origin facts
        S rho (strictEventIndex rho read) source W hW hDread with hgen | ⟨j, hj, t, hacc⟩
    · subst D
      rw [← hDF, facts.csAdded.derive_named_genesis_F]
      exact (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _))
    · obtain ⟨e, he, -, het⟩ := hacc.1.2
      have htRead : t < read := by
        rw [← het]
        exact time_lt_of_lt_strict₅₃b hf.sorted he hj
      have hDpos : 0 < D.slot := by
        rw [← Proofs.NamedWire.erase_slot]
        exact Nat.zero_lt_of_lt
          (Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hW hacc)
      have hFhist : ∀ k : Nat,
          k ≤ (rho.events.filter (fun e => decide (e.time < out))).length →
            Block.Preceq (W k target).st.core.F D.erase := by
        intro k hk
        have hmono := path_F_mono₅₃b facts S rho W hW target (n := strictEventIndex rho out) hk
        exact preceq_trans_Preceq hmono
          (preceq_trans_Preceq hreverse (by
            rw [← hDF]
            exact
              (facts.cs.derive_named_anchors_preceq
                S.E S.cfg D).1))
      have hsrcMax : source ∈ Hs (max t lo) := hHs _ _ (max_le htRead.le hpost) hsource
      obtain ⟨k, tk, hCacc, htk⟩ :=
        Restated.named_acceptsAt_after_cutoffOn facts S Hs Xb hf hHs hHsXb hsrcMax htarget hDpos
          hacc htRead hpost hhop hhor hFhist
      have hkOut : k < strictEventIndex rho out := by
        obtain ⟨event, hevent, -, heventTime⟩ := hCacc.1.2
        by_contra hnot
        have houtLe : out ≤ event.time :=
          Restated.le_time_of_index_ge_of_sorted hf.sorted
            (Nat.le_of_not_gt hnot) hevent
        exact (not_le_of_gt htk) (by simpa only [heventTime] using houtLe)
      have hmonoBefore := path_F_mono₅₃b facts S rho W hW target (Nat.le_of_lt hkOut)
      have hfloor : Block.Preceq
          (W k target).st.core.F
          (M.derive_named S.E S.cfg D).F :=
        preceq_trans_Preceq hmonoBefore (by
          rw [hDF]
          exact hreverse)
      have habsorb := Restated.accepted_carrier_finality_preceqOn facts S rho Hs Xb hf hsb
        (hHsXb _ htarget) hDscope hCacc hfloor
      have hmonoAfter := path_F_mono₅₃b facts S rho W hW target (Nat.succ_le_of_lt hkOut)
      rw [← hDF]
      exact preceq_trans_Preceq habsorb hmonoAfter

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If `source` is in the set for `domain r .g2`, `target` in the set for `domain r .g1`,
    `lo ≤ early r .g2`, `domain r .g0` is inside the horizon, and `hforward` holds, then
    `CrossReaderFinalizedBelow` holds for `B` at their node states in
    `W (strictEventIndex rho (domain r .g2))` and `W (strictEventIndex rho (domain r .g1))`. -/
theorem crossReaderFinalizedBelow_of_finalitySafety_and_relayOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb) {r : Round}
    (hgst : lo ≤ M.early S.E S.hc r .g2)
    (horizon : M.domain S.E S.hc r .g0 ≤ rho.horizon)
    {source target : V} (hsource : source ∈ Hs (M.domain S.E S.hc r .g2))
    (htarget : target ∈ Hs (M.domain S.E S.hc r .g1)) {B : Block V}
    (hforward : ∀ sender u root H,
      ∀ I, M.interpretedInputs
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core.F
        S.hc.η_SG r (M.early S.E S.hc r .g2) sender ⇢ I → u ∈ I →
      ∀ c, M.localCovers
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core))
        u.confirmed B ⇢ c → c = true →
      u.confirmed = some root →
      Block.find?
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core)).T
          root = some H →
      Block.Preceq (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core.F H) :
    Restated.Vocabulary.Proofs.HealingSurface.CrossReaderFinalizedBelow M S rho r source target
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source)
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target) B := by
  have hW := hf.onePath
  have hhop : M.domain S.E S.hc r .g2 + S.E.Δ ≤ M.domain S.E S.hc r .g1 :=
    facts.gr.domain_g2_add_delta_le_domain_g1 S r
  have hgstDomain : lo ≤ M.domain S.E S.hc r .g2 :=
    hgst.trans (facts.gr.early_le_domain S r)
  have hg1Horizon : M.domain S.E S.hc r .g1 ≤ rho.horizon :=
    (facts.gr.domain_le_domain_g0 S r .g1).trans horizon
  have hForder0 := Restated.finalized_preceq_of_evidence_deliveredOn facts S Hs Xb hf hHs hHsXb hsb
    hsource (hHs _ _ hhop htarget) hgstDomain rfl (hhop.trans hg1Horizon)
  have hForder : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core.F
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core.F :=
    Proofs.ModelProperties.Preceq_trans hForder0
      (path_F_mono₅₃b facts S rho W hW target (strictEventIndex_mono rho hhop))
  refine ⟨hforward, ?_⟩
  intro sender u root H I hI hu hconf hfind
  obtain ⟨R, hR⟩ := facts.gr.rawInputs_nonempty _ S.hc.η_SG r (M.late S.E S.hc r .g1) sender
  obtain ⟨b, hb⟩ := facts.gr.bodyReady_nonempty _
    (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core.F
    (M.late S.E S.hc r .g1) u
  have hbtrue := ((facts.gr.mem_interpretedInputs_iff I hI R hR b hb).mp hu).2
  obtain ⟨H', hfind', -, hcompat⟩ := facts.gr.bodyReady_parts b hb hbtrue hconf
  obtain rfl : H = H' := Option.some.inj (hfind.symm.trans hfind')
  rcases Sts.compatible_cases hcompat with hHF | hFH
  · rcases Sts.preceq_linear_Preceq hForder hHF with hsourceH | hHsource
    · exact Sts.compatible_of_cases (Or.inr hsourceH)
    · exact Sts.compatible_of_cases (Or.inl hHsource)
  · exact Sts.compatible_of_cases (Or.inr (Proofs.ModelProperties.Preceq_trans hForder hFH))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.NamedRawRelay
local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If `source` is in the set for `domain r .g2`, `target` in the set for `domain r .g1`, `0 < r`,
    `lo ≤ early r .g2`, `domain r .g0` is inside the horizon, and `CrossReaderFinalizedBelow` holds
    for `B` at their node states along `W`, then `CrossReaderBodyReadyGuard` holds for `B` at the
    same node states. -/
theorem crossReaderBodyReadyGuard_of_finalizedBelowOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r)
    (hgst : lo ≤ M.early S.E S.hc r .g2)
    (horizon : M.domain S.E S.hc r .g0 ≤ rho.horizon)
    {source target : V} (hsource : source ∈ Hs (M.domain S.E S.hc r .g2))
    (htarget : target ∈ Hs (M.domain S.E S.hc r .g1)) {B : Block V}
    (hbelow : Restated.Vocabulary.Proofs.HealingSurface.CrossReaderFinalizedBelow M S rho r source target
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source)
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target) B) :
    Restated.Vocabulary.Proofs.HealingSurface.CrossReaderBodyReadyGuard M S rho r source target
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source)
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target) B := by
  have hW := hf.onePath
  have hΔ := S.E.Δ_pos
  have hE2E1 := facts.gr.early_g2_add_delta_le_early_g1 S r
  have hE1D1 := facts.gr.early_g1_le_domain_g1 S r
  have hE1L1 := facts.gr.early_g1_le_late_g1 S r
  have hE2D2 := facts.gr.early_le_domain S r
  have hL1D1 := facts.gr.late_le_domain S r .g1
  have hL1L2 := facts.gr.late_g1_add_delta_le_late_g2 S r
  have hL2D2 : M.late S.E S.hc r .g2 = M.domain S.E S.hc r .g2 :=
    le_antisymm (facts.gr.late_le_domain S r .g2) (facts.gr.q10_domain_g2_le_late_g2 S r)
  have hD2D1 := facts.gr.domain_g2_le_domain_g1 S r
  have hD1D0 := facts.gr.domain_le_domain_g0 S r .g1
  have hgstLate : lo ≤ M.late S.E S.hc r .g1 := by linarith only [hgst, hE2E1, hE1L1, hΔ]
  have hearlyHorizon : M.early S.E S.hc r .g1 ≤ rho.horizon := by
    linarith only [hE1D1, hD1D0, horizon]
  have hlateHorizon : M.late S.E S.hc r .g2 ≤ rho.horizon := by
    linarith only [hL2D2, hD2D1, hD1D0, horizon]
  have hsourceEarly : source ∈ Hs (M.early S.E S.hc r .g2) := hHs _ _ hE2D2 hsource
  have htargetEarly : target ∈ Hs (M.early S.E S.hc r .g1) := hHs _ _ hE1D1 htarget
  have htargetLate : target ∈ Hs (M.late S.E S.hc r .g1) := hHs _ _ hL1D1 htarget
  have hsourceLate : source ∈ Hs (M.late S.E S.hc r .g2) := hHs _ _ hL2D2.le hsource
  refine ⟨?_, ?_⟩
  · intro sender u I hI hu c hc hctrue b hb
    cases hconf : u.confirmed with
    | none => exact facts.gr.bodyReady_of_confirmed_none hconf b hb
    | some root =>
      obtain ⟨R₀, hR₀⟩ := facts.gr.rawInputs_nonempty _ S.hc.η_SG r (M.early S.E S.hc r .g2) sender
      obtain ⟨b₀, hb₀⟩ := facts.gr.bodyReady_nonempty _
        (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core.F
        (M.early S.E S.hc r .g2) u
      have hready := ((facts.gr.mem_interpretedInputs_iff I hI R₀ hR₀ b₀ hb₀).mp hu).2
      obtain ⟨H, hfind, hstamp, -⟩ := facts.gr.bodyReady_parts b₀ hb₀ hready hconf
      rw [facts.gr.gradeView_timestamp_block] at hstamp
      have hHtree : H ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core.T := by
        have h := Proofs.HealingLemmas.find?_mem hfind
        rw [facts.gr.Sts_gradeView_T] at h
        exact h
      obtain ⟨Hn, hHbody, hHnErase⟩ :=
        Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho
          (strictEventIndex rho (M.domain S.E S.hc r .g2)) source _
          (hW (strictEventIndex rho (M.domain S.E S.hc r .g2))).1 hHtree
      have hHearly : Hn ∈ (W (strictEventIndex rho (M.early S.E S.hc r .g2)) source).st.bodies := by
        apply Restated.body_mem_stateBeforeTime_of_public_stampedBeforeOn facts S rho Hs Xb hf
          hsourceEarly (facts.gr.early_g2_public S r hr) hgst hHbody
        rw [hHnErase]
        exact hstamp
      have hdeadline : max (M.early S.E S.hc r .g2) lo + S.E.Δ ≤ M.early S.E S.hc r .g1 := by
        rw [max_eq_left hgst]
        exact hE2E1
      have hFH : Block.Preceq
          (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core.F Hn.erase := by
        rw [hHnErase]
        exact hbelow.forward sender u root H I hI hu c hc hctrue hconf hfind
      obtain ⟨-, hstampTarget, hfindTarget⟩ :=
        Restated.healthy_head_body_at_read_after_gst_admitOn facts S rho Hs Xb hf hHs hHsXb source
          target Hn (M.early S.E S.hc r .g2) (M.early S.E S.hc r .g1) (M.domain S.E S.hc r .g1)
          (by rw [max_eq_left hgst]; exact hsourceEarly) htargetEarly hHearly hdeadline hE1D1
          hearlyHorizon hFH
      have hroot : Hn.root = root := by
        rw [← Proofs.NamedWire.erase_root, hHnErase]
        exact Proofs.HealingLemmas.find?_root hfind
      refine facts.gr.bodyReady_of_find hconf (H := Hn.erase) ?_ ?_ ?_ b hb
      · rw [facts.gr.Sts_gradeView_T, ← hroot, ← Proofs.NamedWire.erase_root]
        exact hfindTarget
      · rw [facts.gr.gradeView_timestamp_block]
        exact hstampTarget
      · exact Sts.compatible_of_cases (Or.inr hFH)
  · intro sender u I hI hu b hb
    cases hconf : u.confirmed with
    | none => exact facts.gr.bodyReady_of_confirmed_none hconf b hb
    | some root =>
      obtain ⟨R₀, hR₀⟩ := facts.gr.rawInputs_nonempty _ S.hc.η_SG r (M.late S.E S.hc r .g1) sender
      obtain ⟨b₀, hb₀⟩ := facts.gr.bodyReady_nonempty _
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core.F
        (M.late S.E S.hc r .g1) u
      have hready := ((facts.gr.mem_interpretedInputs_iff I hI R₀ hR₀ b₀ hb₀).mp hu).2
      obtain ⟨H, hfind, hstamp, -⟩ := facts.gr.bodyReady_parts b₀ hb₀ hready hconf
      rw [facts.gr.gradeView_timestamp_block] at hstamp
      have hHtree : H ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core.T := by
        have h := Proofs.HealingLemmas.find?_mem hfind
        rw [facts.gr.Sts_gradeView_T] at h
        exact h
      obtain ⟨Hn, hHbody, hHnErase⟩ :=
        Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho
          (strictEventIndex rho (M.domain S.E S.hc r .g1)) target _
          (hW (strictEventIndex rho (M.domain S.E S.hc r .g1))).1 hHtree
      have hHlate : Hn ∈ (W (strictEventIndex rho (M.late S.E S.hc r .g1)) target).st.bodies := by
        apply Restated.body_mem_stateBeforeTime_of_public_stampedBeforeOn facts S rho Hs Xb hf
          htargetLate (facts.gr.q10_late_g1_public S r hr) hgstLate hHbody
        rw [hHnErase]
        exact hstamp
      have hdeadline : max (M.late S.E S.hc r .g1) lo + S.E.Δ ≤ M.late S.E S.hc r .g2 := by
        rw [max_eq_left hgstLate]
        exact hL1L2
      have hcompatSource : Block.compatible Hn.erase
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core.F = true := by
        rw [hHnErase]
        exact hbelow.backward sender u root H I hI hu hconf hfind
      obtain ⟨hstampSource, hfindSource⟩ :
          stampedBefore
            (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core.timestamp_block
            (M.late S.E S.hc r .g2) Hn.erase = true ∧
          Block.find? (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core.T
            Hn.erase.root = some Hn.erase := by
        rcases Sts.compatible_cases hcompatSource with hHF | hFH
        · have hFmem := Restated.Vocabulary.Proofs.NamedStoreBridge.finalizedInTree_stateBefore facts S
            rho (strictEventIndex rho (M.domain S.E S.hc r .g2)) source _
            (hW (strictEventIndex rho (M.domain S.E S.hc r .g2))).1
          have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBefore facts S
            rho (strictEventIndex rho (M.domain S.E S.hc r .g2)) source _
            (hW (strictEventIndex rho (M.domain S.E S.hc r .g2))).1
          unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
          rw [facts.sto.toHealing_gs_T] at hpc
          have hHraw : Hn.erase ∈
              (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core.T :=
            Proofs.Records.mem_of_preceq hpc.2
              Hn.erase _ hFmem (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hHF)
          obtain ⟨K, hKheld, hKErase⟩ :=
            Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho
              (strictEventIndex rho (M.domain S.E S.hc r .g2)) source _
              (hW (strictEventIndex rho (M.domain S.E S.hc r .g2))).1 hHraw
          have hKscope : Restated.blockInRunOn M S rho W Xb K :=
            Restated.blockInRun_of_directOn facts S rho W Xb
              (Restated.directBlock_of_prefixOn facts S rho W Xb (hHsXb _ hsource) _ hKheld)
          have hHscope : Restated.blockInRunOn M S rho W Xb Hn :=
            Restated.blockInRun_of_directOn facts S rho W Xb
              (Restated.directBlock_of_prefixOn facts S rho W Xb (hHsXb _ htarget) _ hHbody)
          have hKH : K = Hn :=
            Restated.runBlock_unique_of_erase_eqOn_RelativeCrossReader facts hf hKscope hHscope
              hKErase
          subst K
          have hstampK :=
            Restated.held_body_stampedBefore_stateBeforeTimeOn facts S rho Hs Xb hf source
              (M.domain S.E S.hc r .g2) Hn hKheld
          refine ⟨?_, ?_⟩
          · rw [hL2D2]
            exact hstampK
          · simpa only [Proofs.NamedWire.erase_root] using
              Restated.held_find_at_strictOn_RelativeCrossReader facts S rho Hs Xb hf (hHsXb _ hsource)
                (M.domain S.E S.hc r .g2) Hn hKheld
        · obtain ⟨-, h2, h3⟩ :=
            Restated.healthy_head_body_at_read_after_gst_admitOn facts S rho Hs Xb hf hHs hHsXb target
              source Hn (M.late S.E S.hc r .g1) (M.late S.E S.hc r .g2) (M.domain S.E S.hc r .g2)
              (by rw [max_eq_left hgstLate]; exact htargetLate) hsourceLate hHlate hdeadline
              hL2D2.le hlateHorizon hFH
          exact ⟨h2, h3⟩
      have hroot : Hn.root = root := by
        rw [← Proofs.NamedWire.erase_root, hHnErase]
        exact Proofs.HealingLemmas.find?_root hfind
      refine facts.gr.bodyReady_of_find hconf (H := Hn.erase) ?_ ?_ hcompatSource b hb
      · rw [facts.gr.Sts_gradeView_T, ← hroot, ← Proofs.NamedWire.erase_root]
        exact hfindSource
      · rw [facts.gr.gradeView_timestamp_block]
        exact hstampSource

/-- If `Hs` shrinks as time grows, `c₂ + Δ ≤ d`, `c₂ + Δ < opening r`, `c₂ + Δ` is inside the
    horizon, `lo ≤ opening (r − η_SG)`, every tick has an outcome, and a source in the set for `ta`
    accepted `a` of round `r`'s window at `ta < c₂`, then for every reader in the set for `d`, every
    outcome of its raw-input read for `a`'s signer at `d` with cutoff `c₂ + Δ` holds `a`'s
    projection or two projections of `a`'s signer and round with different confirmed blocks. -/
theorem accepted_sg_vote_or_equiv_of_twoCutoffOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (r : Round) (c₂ d : Time)
    (hd : c₂ + S.E.Δ ≤ d) (hopen : c₂ + S.E.Δ < M.opening S.E S.hc r)
    (hhor : c₂ + S.E.Δ ≤ rho.horizon)
    (hlow : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG))
    {i : Nat} {source : V} {a : NamedAttestation V} {ta : Time}
    (hsource : source ∈ Hs ta)
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i source (.attest a) ta)
    (hsourceCut : ta < c₂)
    (hwindow : a.round ∈ M.latest_window S.hc.η_SG r) :
    ∀ reader ∈ Hs d, ∀ X, M.rawInputs
          (M.gradeView (M.toHealing (W (strictEventIndex rho d) reader).st.core))
          S.hc.η_SG r (c₂ + S.E.Δ) a.val_index ⇢ X →
      M.sgVote a.erase ∈ X ∨
        ∃ left ∈ X, ∃ right ∈ X,
          left.round = a.round ∧ right.round = a.round ∧
          left.val_index = a.val_index ∧ right.val_index = a.val_index ∧
          left.confirmed ≠ right.confirmed := by
  have hW := hf.onePath
  obtain ⟨sourceEvent, hsourceEvent, -, hsourceTime⟩ := hacc.1.2
  have hΔ := S.E.Δ_pos
  have htaCut : ta < c₂ + S.E.Δ := lt_trans hsourceCut (lt_add_of_pos_right _ S.E.Δ_pos)
  have hwin := Restated.Vocabulary.Proofs.NamedRawRelay.opening_bounds_of_window facts S hwindow
  have hgat : lo ≤ M.opening S.E S.hc a.round := le_trans hlow hwin.1
  have hsourceFloor := Restated.Vocabulary.Proofs.NamedRawRelay.source_acceptance_opening_le_of_fields
    facts S rho hf.sorted hf.in_horizon W hW hacc
  have hta : lo ≤ ta := le_trans hgat hsourceFloor
  have hdom : M.opening S.E S.hc a.round ≤ d := by linarith
  intro reader hreader X hX
  by_cases hskip : a ∈
      (W (i + 1) reader).st.sg_rows a.round
  · apply Or.inl
    exact Restated.Vocabulary.Proofs.NamedRawRelay.held_projection_raw_after_event_of_fields facts S rho
      hf.sorted hf.in_horizon r reader
      a.val_index (c₂ + S.E.Δ) d hd hsourceEvent
      (by simpa only [hsourceTime] using htaCut) a W hW hskip hwindow rfl X hX
  · have hmissing : Restated.Vocabulary.Execution.Object.processed M
        (W (i + 1) reader).st (.attest a) = false := by
      simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not] using hskip
    have hreaderΔ : reader ∈ Hs (ta + S.E.Δ) := hHs _ _ (by linarith) hreader
    obtain ⟨td, htdlo, htdCut, j, hcall⟩ := hf.two_cutoff r c₂ source i a ta hsource hacc hta
      hsourceCut hwindow reader hreaderΔ hmissing hhor
    have htdOpen : td < M.opening S.E S.hc r := lt_trans htdCut hopen
    have hout := Restated.call_vote_or_equivOn_RawRelay facts S rho Hs Xb hf r hcall htdlo
      htdOpen hwindow (hHs _ _ hdom hreader) hgat
    obtain ⟨e, he, _, het⟩ := hcall.2
    have heCut : e.time < c₂ + S.E.Δ := by
      simpa only [het] using htdCut
    rcases hout with ⟨vote, hvote, hround, hval, hkey⟩ |
      ⟨left, right, hleft, hright, hlround, hrround, hlval, hrval, hkeys⟩
    · have hraw := Restated.Vocabulary.Proofs.NamedRawRelay.held_projection_raw_after_event_of_fields
        facts S rho hf.sorted hf.in_horizon r
        reader a.val_index (c₂ + S.E.Δ) d hd he heCut vote W hW
        hvote (by simpa only [hround] using hwindow) hval
      have hproj : M.sgVote vote.erase = M.sgVote a.erase :=
        facts.sto.sgVote_erase_eq_of_fields hval hround hkey
      exact Or.inl (by rw [← hproj]; exact hraw X hX)
    · have hlraw := Restated.Vocabulary.Proofs.NamedRawRelay.held_projection_raw_after_event_of_fields
        facts S rho hf.sorted hf.in_horizon r
        reader a.val_index (c₂ + S.E.Δ) d hd he heCut left W hW
        hleft (by simpa only [hlround] using hwindow) hlval
      have hrraw := Restated.Vocabulary.Proofs.NamedRawRelay.held_projection_raw_after_event_of_fields
        facts S rho hf.sorted hf.in_horizon r
        reader a.val_index (c₂ + S.E.Δ) d hd he heCut right W hW
        hright (by simpa only [hrround] using hwindow) hrval
      exact Or.inr ⟨M.sgVote left.erase, hlraw X hX,
        M.sgVote right.erase, hrraw X hX,
        (facts.sto.sgVote_round left).trans hlround,
        (facts.sto.sgVote_round right).trans hrround,
        (facts.sto.sgVote_val left).trans hlval,
        (facts.sto.sgVote_val right).trans hrval, by
          rw [facts.sto.sgVote_confirmed, facts.sto.sgVote_confirmed]
          exact hkeys⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.NamedRawRelay
local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

open scoped DC

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event at a time before `t` has an index less than
    `strictEventIndex rho t`. -/
private theorem lt_strict_of_time_lt₅₃b₂ {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {j : Nat} {e : Record.Event V} (he : rho.events[j]? = some e) {t : Time} (ht : e.time < t) :
    j < strictEventIndex rho t := by
  by_contra hnot
  exact absurd ht (not_lt.mpr
    (Restated.le_time_of_index_ge_of_sorted hsorted
      (Nat.le_of_not_gt hnot) he))

/-- If `raw` is clean from round `k` and `k ≤ j`, `raw` has no equivocation at round `j`. -/
private theorem clean_excludes_equivocation₅₃b₂ (facts : Record.Facts M) {Key : Type}
    {raw : Finset (Token Key)} {k j : Nat} (hclean : M.CleanFrom raw k) (hkj : k ≤ j) :
    ¬ EquivocationAt raw j := by
  rintro ⟨x, hx, y, hy, hxj, hyj, hne⟩
  apply hne
  exact facts.gr.key_eq_of_cleanFrom hclean x hx y hy (by simpa only [hxj] using hkj)
    (hxj.trans hyj.symm)

/-- If every token of `early` has round at most `k` and `raw` has an equivocation at round `k`, the
    tokens oppose `B`. -/
private theorem equivocation_opposes_of_round_bound₅₃b₂ (facts : Record.Facts M) {Key Blk : Type}
    (covers : Key → Blk → Prop) {early late raw : Finset (Token Key)} {B : Blk} {k : Nat}
    (hbound : ∀ u ∈ early, u.round ≤ k) (heq : EquivocationAt raw k) :
    M.Opposes covers early late raw B := by
  obtain ⟨x, hx, y, hy, hxk, hyk, hne⟩ := heq
  exact facts.gr.opposes_of_raw x hx y hy (fun u hu => by simpa only [hxk] using hbound u hu)
    (hxk.trans hyk.symm) hne

/-- Along a path `W`, for `m ≤ n`, every body `v` holds in `W m` it holds in `W n`. -/
private theorem bodies_mono_path₅₃b₂ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {m n : Nat} (hmn : m ≤ n) : (W m v).st.bodies ⊆ (W n v).st.bodies :=
  Restated.Vocabulary.Proofs.NamedBodyRetention.stateBefore_bodies_mono facts S rho v hmn (W m) (hW m).1
    (W n) (onePath_slice₅₃b W hW hmn)

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event of index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₅₃b₂ (S : Setup V) (rho : Record.Run V)
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

/-- If `source, target ∈ Xb` and `x` is in an outcome of the grade-2 late ready view of `source`'s
    node state in `W (strictEventIndex rho (domain r .g2))` and in an outcome of the grade-1 late
    ready view of `target`'s node state in `W (strictEventIndex rho (domain r .g1))`, then every
    outcome of the first node state's cover test of `x`'s key for `B` is `true` exactly when every
    outcome of the second's is. -/
theorem localCovers_iff_of_cross_late_readyOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (r : Round) (source target : V) (hsource : source ∈ Xb)
    (htarget : target ∈ Xb) (sender : V) (B : Block V)
    (x : Token (Option BlockId))
    (X : Finset (Token (Option BlockId)))
    (hX : M.readyView
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core.F
      S.hc.η_SG r (M.late S.E S.hc r .g2) sender ⇢ X)
    (hsourceReady : x ∈ X)
    (Y : Finset (Token (Option BlockId)))
    (hY : M.readyView
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core.F
      S.hc.η_SG r (M.late S.E S.hc r .g1) sender ⇢ Y)
    (htargetReady : x ∈ Y) :
    ∀ c, M.localCovers
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core))
        x.key B ⇢ c →
    ∀ d, M.localCovers
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core))
        x.key B ⇢ d →
    (c = true ↔ d = true) := by
  intro c hc d hd
  obtain ⟨I, hI⟩ := facts.gr.interpretedInputs_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core.F
    S.hc.η_SG r (M.late S.E S.hc r .g2) sender
  obtain ⟨J, hJ⟩ := facts.gr.interpretedInputs_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core.F
    S.hc.η_SG r (M.late S.E S.hc r .g1) sender
  obtain ⟨u, hu, rfl⟩ := (facts.gr.mem_readyView_iff X hX I hI).mp hsourceReady
  obtain ⟨z, hz, hzu⟩ := (facts.gr.mem_readyView_iff Y hY J hJ).mp htargetReady
  have hkey : z.confirmed = u.confirmed := by
    rw [← facts.gr.token_key z, ← facts.gr.token_key u, hzu]
  obtain ⟨RU, hRU⟩ := facts.gr.rawInputs_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core))
    S.hc.η_SG r (M.late S.E S.hc r .g2) sender
  obtain ⟨RZ, hRZ⟩ := facts.gr.rawInputs_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core))
    S.hc.η_SG r (M.late S.E S.hc r .g1) sender
  obtain ⟨bU, hbU⟩ := facts.gr.bodyReady_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core.F
    (M.late S.E S.hc r .g2) u
  obtain ⟨bZ, hbZ⟩ := facts.gr.bodyReady_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core.F
    (M.late S.E S.hc r .g1) z
  have hbodyU := ((facts.gr.mem_interpretedInputs_iff I hI RU hRU bU hbU).mp hu).2
  have hbodyZ := ((facts.gr.mem_interpretedInputs_iff J hJ RZ hRZ bZ hbZ).mp hz).2
  rw [facts.gr.token_key] at hc hd
  cases hconf : u.confirmed with
  | none =>
      rw [hconf] at hc hd
      rw [facts.gr.localCovers_none _ _ c hc, facts.gr.localCovers_none _ _ d hd]
  | some root =>
      have hconfZ : z.confirmed = some root := hkey.trans hconf
      obtain ⟨H, hfindU, -, -⟩ := facts.gr.bodyReady_parts bU hbU hbodyU hconf
      obtain ⟨K, hfindZ, -, -⟩ := facts.gr.bodyReady_parts bZ hbZ hbodyZ hconfZ
      have hHK :=
        Restated.find_agreeOn facts S rho Hs Xb hf
          source target hsource htarget
          (M.domain S.E S.hc r .g2) (M.domain S.E S.hc r .g1)
          root (by rw [facts.gr.Sts_gradeView_T] at hfindU; exact hfindU)
          (by rw [facts.gr.Sts_gradeView_T] at hfindZ; exact hfindZ)
      subst K
      rw [hconf] at hc hd
      rw [facts.gr.localCovers_some_iff_of_find hfindU c hc,
        facts.gr.localCovers_some_iff_of_find hfindZ d hd]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.NamedRawRelay
local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If every tick has an outcome, `Hs` shrinks as time grows, `lo ≤ opening (r − η_SG)`,
    `domain r .g0` is inside the horizon, `source` is in the set for `domain r .g2`, `target` in the
    set for `domain r .g1`, and `CrossReaderBodyReadyGuard` holds for `B` at their node states along
    `W`, then `CrossReaderTokenTransport` holds for `B` at those node states. -/
theorem crossReaderTokenTransport_of_deliveryOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (r : Round) (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG))
    (horizon : M.domain S.E S.hc r .g0 ≤ rho.horizon)
    (source target : V) (hsource : source ∈ Hs (M.domain S.E S.hc r .g2))
    (htarget : target ∈ Hs (M.domain S.E S.hc r .g1)) (B : Block V)
    (guard : Restated.Vocabulary.Proofs.HealingSurface.CrossReaderBodyReadyGuard M S rho r source target
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source)
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target) B) :
    Restated.Vocabulary.Proofs.HealingSurface.CrossReaderTokenTransport M S rho r source target
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source)
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target) B := by
  have hA1 := facts.gr.early_g2_add_delta_le_early_g1 S r
  have hA2 := facts.gr.late_g1_add_delta_le_late_g2 S r
  have hA3 := facts.gr.opening_sub_five_delta_le_early_g2 S r
  have hA4 := facts.gr.late_g1_add_delta_lt_opening S r
  have hΔ := S.E.Δ_pos
  have hE2E1 := facts.gr.q10_early_g2_le_early_g1 S r
  have hE1L1 := facts.gr.early_g1_le_late_g1 S r
  have hE1D1 := facts.gr.early_g1_le_domain_g1 S r
  have hE2D2 := facts.gr.early_le_domain S r
  have hL1D1 := facts.gr.late_le_domain S r .g1
  have hL2D2 := facts.gr.late_le_domain S r .g2
  have hD1D0 := facts.gr.domain_le_domain_g0 S r .g1
  have hD2D0 := facts.gr.domain_le_domain_g0 S r .g2
  have hearlyHorizon : M.early S.E S.hc r .g2 + S.E.Δ ≤ rho.horizon := by
    linarith only [hA1, hE1D1, hD1D0, horizon]
  have hlateHorizon : M.late S.E S.hc r .g1 + S.E.Δ ≤ rho.horizon := by
    linarith only [hA2, hL2D2, hD2D0, horizon]
  have hEd : M.early S.E S.hc r .g2 + S.E.Δ ≤ M.domain S.E S.hc r .g1 := by
    linarith only [hA1, hE1D1]
  have hEo : M.early S.E S.hc r .g2 + S.E.Δ < M.opening S.E S.hc r := by
    linarith only [hA1, hE1L1, hA4, hΔ]
  have hLo := hA4
  have hLd : M.late S.E S.hc r .g1 + S.E.Δ ≤ M.domain S.E S.hc r .g2 := by
    linarith only [hA2, hL2D2]
  have hcL : M.opening S.E S.hc r - 5 * S.E.Δ ≤ M.late S.E S.hc r .g1 := by
    linarith only [hA3, hE2E1, hE1L1]
  have hsrcE : source ∈ Hs (M.early S.E S.hc r .g2) := hHs _ _ hE2D2 hsource
  have htgtL : target ∈ Hs (M.late S.E S.hc r .g1) := hHs _ _ hL1D1 htarget
  refine ⟨?_, ?_, ?_⟩
  · intro sender x X hX hx c hc hctrue Y hY R hR
    obtain ⟨Is, hIs⟩ := facts.gr.interpretedInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core.F
      S.hc.η_SG r (M.early S.E S.hc r .g2) sender
    obtain ⟨u, hu, rfl⟩ := (facts.gr.mem_readyView_iff X hX Is hIs).mp hx
    obtain ⟨Rs, hRs⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core))
      S.hc.η_SG r (M.early S.E S.hc r .g2) sender
    obtain ⟨bs, hbs⟩ := facts.gr.bodyReady_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core.F
      (M.early S.E S.hc r .g2) u
    obtain ⟨hraw, -⟩ := (facts.gr.mem_interpretedInputs_iff Is hIs Rs hRs bs hbs).mp hu
    have hval : u.val_index = sender := facts.gr.val_index_of_mem_rawInputs Rs hRs hraw
    obtain ⟨a, i, accepted, hproj, hwindow, hbefore, hacc⟩ :=
      Restated.g2_raw_input_source_acceptanceOn facts S rho Hs Xb hf source r sender u Rs hRs hraw
        hsrcE (facts.gr.lo_le_of_rawInputs_l53 S hlo hA3 Rs hRs hraw)
    have hround : a.round = u.round :=
      (facts.sto.sgVote_round a).symm.trans
        (congrArg Protocol.SGVote.round hproj)
    have hidx : a.val_index = sender :=
      (facts.sto.sgVote_val a).symm.trans
        ((congrArg Protocol.SGVote.val_index hproj).trans hval)
    have hrelay := Restated.accepted_sg_vote_or_equiv_of_twoCutoffOn facts S rho Hs Xb hf hHs r
      (M.early S.E S.hc r .g2) (M.domain S.E S.hc r .g1) hEd hEo hearlyHorizon hlo
      (hHs _ _ hbefore.le hsrcE) hacc hbefore hwindow target htarget
    obtain ⟨Rt, hRt⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core))
      S.hc.η_SG r (M.early S.E S.hc r .g2 + S.E.Δ) a.val_index
    have hrelay' := hrelay Rt hRt
    simp only [hproj, hidx] at hrelay'
    rw [hidx] at hRt
    rcases hrelay' with hexact |
      ⟨left, hleft, right, hright, hlr, hrr, _, _, hne⟩
    · obtain ⟨It, hIt⟩ := facts.gr.interpretedInputs_nonempty
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core.F
        S.hc.η_SG r (M.early S.E S.hc r .g1) sender
      obtain ⟨Rt₁, hRt₁⟩ := facts.gr.rawInputs_nonempty
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core))
        S.hc.η_SG r (M.early S.E S.hc r .g1) sender
      obtain ⟨bt, hbt⟩ := facts.gr.bodyReady_nonempty
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core.F
        (M.early S.E S.hc r .g1) u
      rw [facts.gr.token_key] at hc
      exact Or.inl ((facts.gr.mem_readyView_iff Y hY It hIt).mpr ⟨u,
        (facts.gr.mem_interpretedInputs_iff It hIt Rt₁ hRt₁ bt hbt).mpr
          ⟨facts.gr.rawInputs_mono _ _ _ hA1 _ Rt hRt Rt₁ hRt₁ hexact,
            guard.forward sender u Is hIs hu c hc hctrue bt hbt⟩, rfl⟩)
    · obtain ⟨Rl, hRl⟩ := facts.gr.rawInputs_nonempty
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core))
        S.hc.η_SG r (M.late S.E S.hc r .g1) sender
      have hsub := facts.gr.rawInputs_mono _ _ _ (hA1.trans hE1L1) _ Rt hRt Rl hRl
      exact Or.inr ⟨M.token left,
        (facts.gr.mem_rawView_iff _ _ _ _ _ _ R hR Rl hRl).mpr ⟨left, hsub hleft, rfl⟩,
        M.token right,
        (facts.gr.mem_rawView_iff _ _ _ _ _ _ R hR Rl hRl).mpr ⟨right, hsub hright, rfl⟩,
        (by rw [facts.gr.token_round, facts.gr.token_round]; exact hlr.trans hround),
        (by rw [facts.gr.token_round, facts.gr.token_round]; exact hrr.trans hround),
        (by rw [facts.gr.token_key, facts.gr.token_key]; exact hne)⟩
  · intro sender x X hX hx Y hY R hR
    obtain ⟨It, hIt⟩ := facts.gr.interpretedInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core.F
      S.hc.η_SG r (M.late S.E S.hc r .g1) sender
    obtain ⟨u, hu, rfl⟩ := (facts.gr.mem_readyView_iff X hX It hIt).mp hx
    obtain ⟨Rt, hRt⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core))
      S.hc.η_SG r (M.late S.E S.hc r .g1) sender
    obtain ⟨bt, hbt⟩ := facts.gr.bodyReady_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core.F
      (M.late S.E S.hc r .g1) u
    obtain ⟨hraw, -⟩ := (facts.gr.mem_interpretedInputs_iff It hIt Rt hRt bt hbt).mp hu
    have hval : u.val_index = sender := facts.gr.val_index_of_mem_rawInputs Rt hRt hraw
    obtain ⟨a, i, accepted, hproj, hwindow, hbefore, hacc⟩ :=
      Restated.g1_late_raw_input_acceptanceOn facts S rho Hs Xb hf target r sender u Rt hRt hraw
        htgtL (facts.gr.lo_le_of_rawInputs_l53 S hlo hcL Rt hRt hraw)
    have hround : a.round = u.round :=
      (facts.sto.sgVote_round a).symm.trans
        (congrArg Protocol.SGVote.round hproj)
    have hidx : a.val_index = sender :=
      (facts.sto.sgVote_val a).symm.trans
        ((congrArg Protocol.SGVote.val_index hproj).trans hval)
    have hone := Restated.accepted_sg_vote_or_equiv_of_twoCutoffOn facts S rho Hs Xb hf hHs r
      (M.late S.E S.hc r .g1) (M.domain S.E S.hc r .g2) hLd hLo hlateHorizon hlo
      (hHs _ _ hbefore.le htgtL) hacc hbefore hwindow source hsource
    obtain ⟨Rs, hRs⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core))
      S.hc.η_SG r (M.late S.E S.hc r .g1 + S.E.Δ) a.val_index
    have hone' := hone Rs hRs
    simp only [hproj, hidx] at hone'
    rw [hidx] at hRs
    obtain ⟨Rs₂, hRs₂⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core))
      S.hc.η_SG r (M.late S.E S.hc r .g2) sender
    have hsub := facts.gr.rawInputs_mono _ _ _ hA2 _ Rs hRs Rs₂ hRs₂
    rcases hone' with hexact |
      ⟨left, hleft, right, hright, hlr, hrr, _, _, hne⟩
    · obtain ⟨Is, hIs⟩ := facts.gr.interpretedInputs_nonempty
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core.F
        S.hc.η_SG r (M.late S.E S.hc r .g2) sender
      obtain ⟨bs, hbs⟩ := facts.gr.bodyReady_nonempty
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core.F
        (M.late S.E S.hc r .g2) u
      exact Or.inl ((facts.gr.mem_readyView_iff Y hY Is hIs).mpr ⟨u,
        (facts.gr.mem_interpretedInputs_iff Is hIs Rs₂ hRs₂ bs hbs).mpr
          ⟨hsub hexact, guard.backward sender u It hIt hu bs hbs⟩, rfl⟩)
    · exact Or.inr ⟨M.token left,
        (facts.gr.mem_rawView_iff _ _ _ _ _ _ R hR Rs₂ hRs₂).mpr ⟨left, hsub hleft, rfl⟩,
        M.token right,
        (facts.gr.mem_rawView_iff _ _ _ _ _ _ R hR Rs₂ hRs₂).mpr ⟨right, hsub hright, rfl⟩,
        (by rw [facts.gr.token_round, facts.gr.token_round]; exact hlr.trans hround),
        (by rw [facts.gr.token_round, facts.gr.token_round]; exact hrr.trans hround),
        (by rw [facts.gr.token_key, facts.gr.token_key]; exact hne)⟩
  · intro sender x X hX hx Y hY
    obtain ⟨Rt, hRt⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core))
      S.hc.η_SG r (M.late S.E S.hc r .g1) sender
    obtain ⟨u, hu, rfl⟩ := (facts.gr.mem_rawView_iff _ _ _ _ _ _ X hX Rt hRt).mp hx
    have hval : u.val_index = sender := facts.gr.val_index_of_mem_rawInputs Rt hRt hu
    obtain ⟨a, i, accepted, hproj, hwindow, hbefore, hacc⟩ :=
      Restated.g1_late_raw_input_acceptanceOn facts S rho Hs Xb hf target r sender u Rt hRt hu
        htgtL (facts.gr.lo_le_of_rawInputs_l53 S hlo hcL Rt hRt hu)
    have hround : a.round = u.round :=
      (facts.sto.sgVote_round a).symm.trans
        (congrArg Protocol.SGVote.round hproj)
    have hidx : a.val_index = sender :=
      (facts.sto.sgVote_val a).symm.trans
        ((congrArg Protocol.SGVote.val_index hproj).trans hval)
    have hone := Restated.accepted_sg_vote_or_equiv_of_twoCutoffOn facts S rho Hs Xb hf hHs r
      (M.late S.E S.hc r .g1) (M.domain S.E S.hc r .g2) hLd hLo hlateHorizon hlo
      (hHs _ _ hbefore.le htgtL) hacc hbefore hwindow source hsource
    obtain ⟨Rs, hRs⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core))
      S.hc.η_SG r (M.late S.E S.hc r .g1 + S.E.Δ) a.val_index
    have hone' := hone Rs hRs
    simp only [hproj, hidx] at hone'
    rw [hidx] at hRs
    obtain ⟨Rs₂, hRs₂⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st.core))
      S.hc.η_SG r (M.late S.E S.hc r .g2) sender
    have hsub := facts.gr.rawInputs_mono _ _ _ hA2 _ Rs hRs Rs₂ hRs₂
    rcases hone' with hexact |
      ⟨left, hleft, right, hright, hlr, hrr, _, _, hne⟩
    · exact Or.inl ((facts.gr.mem_rawView_iff _ _ _ _ _ _ Y hY Rs₂ hRs₂).mpr ⟨u, hsub hexact, rfl⟩)
    · exact Or.inr ⟨M.token left,
        (facts.gr.mem_rawView_iff _ _ _ _ _ _ Y hY Rs₂ hRs₂).mpr ⟨left, hsub hleft, rfl⟩,
        M.token right,
        (facts.gr.mem_rawView_iff _ _ _ _ _ _ Y hY Rs₂ hRs₂).mpr ⟨right, hsub hright, rfl⟩,
        (by rw [facts.gr.token_round, facts.gr.token_round]; exact hlr.trans hround),
        (by rw [facts.gr.token_round, facts.gr.token_round]; exact hrr.trans hround),
        (by rw [facts.gr.token_key, facts.gr.token_key]; exact hne)⟩

/-- Under the hypotheses of `crossReaderTokenTransport_of_deliveryOn` for `v` and `w`, if the
    support test of `sender` for `B` at `v`'s grade-2 read in
    `W (strictEventIndex rho (domain r .g2))` can return `true`, then every outcome of the support
    test of `sender` for `B` at `w`'s grade-1 read in `W (strictEventIndex rho (domain r .g1))` is
    `true`. -/
theorem positive_g2_at_v_imp_positive_g1_at_wOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (r : Round) (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG))
    (horizon : M.domain S.E S.hc r .g0 ≤ rho.horizon)
    (v w : V) (hv : v ∈ Hs (M.domain S.E S.hc r .g2)) (hw : w ∈ Hs (M.domain S.E S.hc r .g1))
    (B : Block V) (guard : Restated.Vocabulary.Proofs.HealingSurface.CrossReaderBodyReadyGuard M S rho r v w
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v)
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w) B)
    (sender : V)
    (hpositive : M.positive
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core.F S.hc.η_SG r
      (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2)
      sender B ⇢ true) :
    ∀ p, M.positive
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F S.hc.η_SG r
      (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1)
      sender B ⇢ p → p = true := by
  have tr := Restated.crossReaderTokenTransport_of_deliveryOn facts S rho Hs Xb hf hHs r hlo
    horizon v w hv hw B guard
  set ns := W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v with hns
  set nt := W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w with hnt
  choose covS hcovS using fun k b => facts.gr.localCovers_nonempty
    (M.gradeView (M.toHealing ns.st.core)) k b
  choose covT hcovT using fun k b => facts.gr.localCovers_nonempty
    (M.gradeView (M.toHealing nt.st.core)) k b
  obtain ⟨Se, hSe⟩ := facts.gr.readyView_nonempty (M.gradeView (M.toHealing ns.st.core))
    ns.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g2) sender
  obtain ⟨Sl, hSl⟩ := facts.gr.readyView_nonempty (M.gradeView (M.toHealing ns.st.core))
    ns.st.core.F S.hc.η_SG r (M.late S.E S.hc r .g2) sender
  obtain ⟨Sr, hSr⟩ := facts.gr.rawView_nonempty (M.gradeView (M.toHealing ns.st.core))
    S.hc.η_SG r (M.late S.E S.hc r .g2) sender
  obtain ⟨De, hDe⟩ := facts.gr.readyView_nonempty (M.gradeView (M.toHealing nt.st.core))
    nt.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g1) sender
  obtain ⟨Dl, hDl⟩ := facts.gr.readyView_nonempty (M.gradeView (M.toHealing nt.st.core))
    nt.st.core.F S.hc.η_SG r (M.late S.E S.hc r .g1) sender
  obtain ⟨Dr, hDr⟩ := facts.gr.rawView_nonempty (M.gradeView (M.toHealing nt.st.core))
    S.hc.η_SG r (M.late S.E S.hc r .g1) sender
  have hsrc : M.Supports (fun k b => covS k b = true) Se Sl Sr B :=
    facts.gr.supports_of_positive true hpositive rfl covS hcovS Se hSe Sl hSl Sr hSr
  have hSL : Se ⊆ Sl :=
    facts.gr.readyView_mono _ _ _ _ (facts.gr.early_g2_le_late_g2 S r) sender Se hSe Sl hSl
  have hSR : Sl ⊆ Sr := facts.gr.readyView_subset_rawView _ _ _ _ _ sender Sl hSl Sr hSr
  have hDL : De ⊆ Dl :=
    facts.gr.readyView_mono _ _ _ _ (facts.gr.early_g1_le_late_g1 S r) sender De hDe Dl hDl
  have hEqBack : ∀ k, EquivocationAt Dr k → EquivocationAt Sr k := by
    intro k hk
    exact DecoupledConsensusModel.Protocol.equivocation_back_of_vote_or_equivocation
      (fun y hy => tr.rawBack sender y Dr hDr hy Sr hSr) hk
  obtain ⟨u, hu, hmax, hcover, hclean, hsweep⟩ := facts.gr.supports_elim hsrc
  have huDst : u ∈ De := by
    rcases tr.forward sender u Se hSe hu (covS u.key B) (hcovS _ _) hcover De hDe Dr hDr with h | h
    · exact h
    · exact False.elim
        (clean_excludes_equivocation₅₃b₂ facts hclean le_rfl (hEqBack _ h))
  obtain ⟨x, hx, hmaxDst⟩ := De.exists_max_image Token.round ⟨u, huDst⟩
  have hux : u.round ≤ x.round := hmaxDst u huDst
  have hxSrc : x ∈ Sl := by
    rcases tr.lateBack sender x Dl hDl (hDL hx) Sl hSl Sr hSr with h | h
    · exact h
    · exact False.elim (clean_excludes_equivocation₅₃b₂ facts hclean hux h)
  have hxCoverSrc : covS x.key B = true := by
    by_cases heq : u.round = x.round
    · have hkey := facts.gr.key_eq_of_cleanFrom hclean u (hSR (hSL hu)) x (hSR hxSrc)
        le_rfl heq
      simpa only [← hkey] using hcover
    · exact hsweep x hxSrc (Nat.lt_of_le_of_ne hux heq)
  have hcross : ∀ y ∈ Sl, y ∈ Dl → (covS y.key B = true ↔ covT y.key B = true) :=
    fun y hyS hyD => Restated.localCovers_iff_of_cross_late_readyOn facts S rho Hs Xb hf r v w
      (hHsXb _ hv) (hHsXb _ hw) sender B y Sl hSl hyS Dl hDl hyD _ (hcovS _ _) _ (hcovT _ _)
  have hxCoverDst : covT x.key B = true := (hcross x hxSrc (hDL hx)).mp hxCoverSrc
  refine facts.gr.positive_of_Supports _ _ _ _ _ _ _ _ covT hcovT De hDe Dl hDl Dr hDr
    (facts.gr.supports_intro x hx hmaxDst hxCoverDst ?_ ?_)
  · refine facts.gr.cleanFrom_intro ?_
    intro y hy z hz hxy hyz
    by_contra hne
    exact clean_excludes_equivocation₅₃b₂ facts hclean (hux.trans hxy)
      (hEqBack _ ⟨y, hy, z, hz, rfl, hyz.symm, hne⟩)
  · intro y hy hxy
    rcases tr.lateBack sender y Dl hDl hy Sl hSl Sr hSr with hySrc | hyEq
    · exact (hcross y hySrc hy).mp (hsweep y hySrc (lt_of_le_of_lt hux hxy))
    · exact False.elim
        (clean_excludes_equivocation₅₃b₂ facts hclean (hux.trans hxy.le) hyEq)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.NamedRawRelay
local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the hypotheses of `crossReaderTokenTransport_of_deliveryOn` for `v` and `w`, if the
    opposition test of `sender` for `B` at `w`'s grade-1 read in
    `W (strictEventIndex rho (domain r .g1))` can return `true`, then every outcome of the
    opposition test of `sender` for `B` at `v`'s grade-2 read in
    `W (strictEventIndex rho (domain r .g2))` is `true`. -/
theorem opposing_g1_at_w_imp_opposing_g2_at_vOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (r : Round) (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG))
    (horizon : M.domain S.E S.hc r .g0 ≤ rho.horizon)
    (v w : V) (hv : v ∈ Hs (M.domain S.E S.hc r .g2)) (hw : w ∈ Hs (M.domain S.E S.hc r .g1))
    (B : Block V) (guard : Restated.Vocabulary.Proofs.HealingSurface.CrossReaderBodyReadyGuard M S rho r v w
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v)
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w) B)
    (sender : V)
    (hopposing : M.opposing
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F S.hc.η_SG r
      (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1)
      sender B ⇢ true) :
    ∀ o, M.opposing
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core.F S.hc.η_SG r
      (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2)
      sender B ⇢ o → o = true := by
  have tr := Restated.crossReaderTokenTransport_of_deliveryOn facts S rho Hs Xb hf hHs r hlo
    horizon v w hv hw B guard
  set ns := W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v with hns
  set nt := W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w with hnt
  choose covS hcovS using fun k b => facts.gr.localCovers_nonempty
    (M.gradeView (M.toHealing ns.st.core)) k b
  choose covT hcovT using fun k b => facts.gr.localCovers_nonempty
    (M.gradeView (M.toHealing nt.st.core)) k b
  obtain ⟨Se, hSe⟩ := facts.gr.readyView_nonempty (M.gradeView (M.toHealing ns.st.core))
    ns.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g2) sender
  obtain ⟨Sl, hSl⟩ := facts.gr.readyView_nonempty (M.gradeView (M.toHealing ns.st.core))
    ns.st.core.F S.hc.η_SG r (M.late S.E S.hc r .g2) sender
  obtain ⟨Sr, hSr⟩ := facts.gr.rawView_nonempty (M.gradeView (M.toHealing ns.st.core))
    S.hc.η_SG r (M.late S.E S.hc r .g2) sender
  obtain ⟨De, hDe⟩ := facts.gr.readyView_nonempty (M.gradeView (M.toHealing nt.st.core))
    nt.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g1) sender
  obtain ⟨Dl, hDl⟩ := facts.gr.readyView_nonempty (M.gradeView (M.toHealing nt.st.core))
    nt.st.core.F S.hc.η_SG r (M.late S.E S.hc r .g1) sender
  obtain ⟨Dr, hDr⟩ := facts.gr.rawView_nonempty (M.gradeView (M.toHealing nt.st.core))
    S.hc.η_SG r (M.late S.E S.hc r .g1) sender
  have hdst : M.Opposes (fun k b => covT k b = true) De Dl Dr B :=
    facts.gr.opposes_of_opposing true hopposing rfl covT hcovT De hDe Dl hDl Dr hDr
  have hSL : Se ⊆ Sl :=
    facts.gr.readyView_mono _ _ _ _ (facts.gr.early_g2_le_late_g2 S r) sender Se hSe Sl hSl
  have hEqBack : ∀ k, EquivocationAt Dr k → EquivocationAt Sr k := by
    intro k hk
    exact DecoupledConsensusModel.Protocol.equivocation_back_of_vote_or_equivocation
      (fun y hy => tr.rawBack sender y Dr hDr hy Sr hSr) hk
  have hcross : ∀ y ∈ Sl, y ∈ Dl → (covS y.key B = true ↔ covT y.key B = true) :=
    fun y hyS hyD => Restated.localCovers_iff_of_cross_late_readyOn facts S rho Hs Xb hf r v w
      (hHsXb _ hv) (hHsXb _ hw) sender B y Sl hSl hyS Dl hDl hyD _ (hcovS _ _) _ (hcovT _ _)
  have hsrc : M.Opposes (fun k b => covS k b = true) Se Sl Sr B := by
    by_cases hs : M.Opposes (fun k b => covS k b = true) Se Sl Sr B
    · exact hs
    · have hRound : ∀ k, (∀ u ∈ De, u.round ≤ k) → ∀ u ∈ Se, u.round ≤ k := by
        intro k hk u hu
        obtain ⟨x, hx, hmax⟩ := Se.exists_max_image Token.round ⟨u, hu⟩
        have hxCover : covS x.key B = true := by
          by_contra hnot
          exact hs (facts.gr.opposes_of_late x (hSL hx) hmax hnot)
        rcases tr.forward sender x Se hSe hx (covS x.key B) (hcovS _ _) hxCover De hDe Dr hDr
          with hxDst | hxEq
        · exact (hmax u hu).trans (hk x hxDst)
        · exact False.elim (hs (equivocation_opposes_of_round_bound₅₃b₂ facts
            (fun k b => covS k b = true) hmax (hEqBack _ hxEq)))
      rcases facts.gr.opposes_cases hdst with ⟨x, hx, hmax, hnot⟩ |
          ⟨x, hx, y, hy, hmax, hxy, hne⟩
      · rcases tr.lateBack sender x Dl hDl hx Sl hSl Sr hSr with hxSrc | hxEq
        · refine facts.gr.opposes_of_late x hxSrc (hRound _ hmax) ?_
          intro hxCover
          exact hnot ((hcross x hxSrc hx).mp hxCover)
        · exact equivocation_opposes_of_round_bound₅₃b₂ facts
            (fun k b => covS k b = true) (hRound _ hmax) hxEq
      · exact equivocation_opposes_of_round_bound₅₃b₂ facts (fun k b => covS k b = true)
          (hRound _ hmax)
          (hEqBack _ ⟨x, hx, y, hy, rfl, hxy.symm, hne⟩)
  exact facts.gr.opposing_of_Opposes _ _ _ _ _ _ _ _ covS hcovS Se hSe Sl hSl Sr hSr hsrc

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.NamedRawRelay
local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the hypotheses of `crossReaderTokenTransport_of_deliveryOn` for `v` and `w`, if the
    grade-2 store grade of `B` at `v`'s node state in `W (strictEventIndex rho (domain r .g2))` can
    return `true`, then every outcome of the grade-1 store grade of `B` at `w`'s node state in
    `W (strictEventIndex rho (domain r .g1))` is `true`. -/
theorem storeGrade_g1_of_storeGrade_g2_cross_readerOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (r : Round) (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG))
    (horizon : M.domain S.E S.hc r .g0 ≤ rho.horizon)
    (v w : V) (hv : v ∈ Hs (M.domain S.E S.hc r .g2)) (hw : w ∈ Hs (M.domain S.E S.hc r .g1))
    (B : Block V)
    (hgrade : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st r .g2 B ⇢ true)
    (guard : Restated.Vocabulary.Proofs.HealingSurface.CrossReaderBodyReadyGuard M S rho r v w
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v)
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w) B) :
    ∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st r .g1 B ⇢ b → b = true := by
  intro b hb
  set ns := W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v with hns
  set nt := W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w with hnt
  have hgrade' : M.gradeBool S.E (M.gradeView (M.toHealing ns.st.core)) ns.st.core.F S.hc.η_SG r
      (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) B ⇢ true := hgrade
  have hb' : M.gradeBool S.E (M.gradeView (M.toHealing nt.st.core)) nt.st.core.F S.hc.η_SG r
      (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) B ⇢ b := hb
  choose oppT hoppT using fun u => facts.gr.opposing_nonempty (M.gradeView (M.toHealing nt.st.core))
    nt.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) u B
  choose oppS hoppS using fun u => facts.gr.opposing_nonempty (M.gradeView (M.toHealing ns.st.core))
    ns.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) u B
  choose posS hposS using fun u => facts.gr.positive_nonempty (M.gradeView (M.toHealing ns.st.core))
    ns.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) u B
  choose posT hposT using fun u => facts.gr.positive_nonempty (M.gradeView (M.toHealing nt.st.core))
    nt.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) u B
  have hOpp : (Finset.univ.filter fun sender => oppT sender = true) ⊆
      Finset.univ.filter fun sender => oppS sender = true := by
    intro sender hs
    have hs' := (Finset.mem_filter.mp hs).2
    have hT := hoppT sender
    rw [hs'] at hT
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ sender,
      Restated.opposing_g1_at_w_imp_opposing_g2_at_vOn facts S rho Hs Xb hf hHs hHsXb r hlo
        horizon v w hv hw B guard sender hT _ (hoppS sender)⟩
  have hPos : (Finset.univ.filter fun sender => posS sender = true) ⊆
      Finset.univ.filter fun sender => posT sender = true := by
    intro sender hs
    have hs' := (Finset.mem_filter.mp hs).2
    have hS := hposS sender
    rw [hs'] at hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ sender,
      Restated.positive_g2_at_v_imp_positive_g1_at_wOn facts S rho Hs Xb hf hHs hHsXb r hlo
        horizon v w hv hw B guard sender hS _ (hposT sender)⟩
  exact facts.gr.gradeBool_of_subsets S.E oppT hoppT oppS hoppS posS hposS posT hposT hOpp hPos
    true hgrade' rfl b hb'

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.NamedRawRelay
local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If `source` is in the set for `domain r .g1`, `target` in the set for `domain r .g0`,
    `lo ≤ early r .g1`, `domain r .g0` is inside the horizon, and `hforward` holds, then
    `G1G0CrossReaderFinalizedBelow` holds for `B` at their node states in
    `W (strictEventIndex rho (domain r .g1))` and `W (strictEventIndex rho (domain r .g0))`. -/
theorem g1G0CrossReaderFinalizedBelow_of_finalitySafety_and_relayOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb) {r : Round}
    (hgst : lo ≤ M.early S.E S.hc r .g1)
    (horizon : M.domain S.E S.hc r .g0 ≤ rho.horizon)
    {source target : V} (hsource : source ∈ Hs (M.domain S.E S.hc r .g1))
    (htarget : target ∈ Hs (M.domain S.E S.hc r .g0)) {B : Block V}
    (hforward : ∀ sender u root H,
      ∀ I, M.interpretedInputs
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core.F
        S.hc.η_SG r (M.early S.E S.hc r .g1) sender ⇢ I → u ∈ I →
      ∀ c, M.localCovers
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core))
        u.confirmed B ⇢ c → c = true →
      u.confirmed = some root →
      Block.find?
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core)).T
          root = some H →
      Block.Preceq (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core.F H) :
    Restated.Vocabulary.Proofs.HealingSurface.G1G0CrossReaderFinalizedBelow M S rho r source target
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source)
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target) B := by
  have hgstDomain : lo ≤ M.domain S.E S.hc r .g1 :=
    hgst.trans (facts.gr.early_g1_le_domain_g1 S r)
  have hmid : M.domain S.E S.hc r .g1 + S.E.Δ ≤ M.domain S.E S.hc r .g0 :=
    facts.gr.domain_g1_add_delta_le_domain_g0 S r
  have hForderMid := Restated.finalized_preceq_of_evidence_deliveredOn facts S Hs Xb hf hHs hHsXb
    hsb hsource (hHs _ _ hmid htarget) hgstDomain rfl (hmid.trans horizon)
  have hForder : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core.F
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core.F :=
    Proofs.ModelProperties.Preceq_trans hForderMid
      (path_F_mono₅₃b facts S rho W hf.onePath target
        (Restated.strict_lengths_mono rho hmid))
  refine ⟨hforward, ?_⟩
  intro sender u root H I hI hu hconf hfind
  obtain ⟨R, hR⟩ := facts.gr.rawInputs_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core))
    S.hc.η_SG r (M.late S.E S.hc r .g0) sender
  obtain ⟨b, hb⟩ := facts.gr.bodyReady_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core.F
    (M.late S.E S.hc r .g0) u
  obtain ⟨H', hfind', -, hcompat⟩ := facts.gr.bodyReady_parts b hb
    ((facts.gr.mem_interpretedInputs_iff I hI R hR b hb).mp hu).2 hconf
  obtain rfl : H = H' := Option.some.inj (hfind.symm.trans hfind')
  rcases Sts.compatible_cases hcompat with hHF | hFH
  · rcases Sts.preceq_linear_Preceq hForder hHF with hsourceH | hHsource
    · exact Sts.compatible_of_cases (Or.inr hsourceH)
    · exact Sts.compatible_of_cases (Or.inl hHsource)
  · exact Sts.compatible_of_cases (Or.inr (Proofs.ModelProperties.Preceq_trans hForder hFH))

/-- If the source, in the set for `max sourceCut lo`, holds `H` before `sourceCut`,
    `max sourceCut lo + Δ ≤ targetEarly ≤ targetRead`, `targetEarly` is inside the horizon, the
    reader is in the set for `targetEarly`, and `H` is compatible with the reader's finalized block
    in `W (strictEventIndex rho targetRead)`, then the reader holds `H` there, with a block stamp
    before `targetEarly`, and its tree finds `H` at `H`'s root. -/
theorem compatible_head_body_at_read_after_gstOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (source : V) (reader : V) (H : NamedBlock V)
    (sourceCut targetEarly targetRead : Time)
    (hsource : source ∈ Hs (max sourceCut lo)) (hreader : reader ∈ Hs targetEarly)
    (hHsource : H ∈ (W (strictEventIndex rho sourceCut) source).st.bodies)
    (hDeadline : max sourceCut lo + S.E.Δ ≤ targetEarly)
    (hOrder : targetEarly ≤ targetRead)
    (hCut : targetEarly ≤ rho.horizon)
    (hcompat : Block.compatible H.erase
      (W (strictEventIndex rho targetRead) reader).st.core.F = true) :
    H ∈ (W (strictEventIndex rho targetRead) reader).st.bodies ∧
      stampedBefore
        (W (strictEventIndex rho targetRead) reader).st.core.timestamp_block
        targetEarly H.erase = true ∧
      Block.find?
        (W (strictEventIndex rho targetRead) reader).st.core.T
        H.erase.root = some H.erase := by
  have hW := hf.onePath
  have hroots : Restated.Vocabulary.Execution.NamedRootCollisionFree M S
      ({ rho with honest := Xb } : Record.Run V) W :=
    ⟨fun B C hB hC => hf.rootCollisionFree.root_injective B C hB hC⟩
  have hHscope : Restated.blockInRunOn M S rho W Xb H :=
    Restated.blockInRun_of_directOn facts S rho W Xb
      (Restated.directBlock_of_prefixOn facts S rho W Xb (hHsXb _ hsource) _ hHsource)
  have hEarly : H ∈ (W (strictEventIndex rho targetEarly) reader).st.bodies := by
    by_cases hgen : H = NamedBlock.genesis
    · subst H
      exact (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho _ reader _
        (hW (strictEventIndex rho targetEarly)).1).1.1.1.2.2.1.1
    · rcases Restated.Vocabulary.Proofs.NamedOutageProvenance.held_block_origin facts S rho _ source W hW
          hHsource with hgen' | ⟨i, hin', ta, hacc⟩
      · exact False.elim (hgen hgen')
      · obtain ⟨eSource, heSource, _, htSource⟩ := hacc.1.2
        have hta : ta < sourceCut := by
          rw [← htSource]
          exact time_lt_of_lt_strict₅₃b hf.sorted heSource hin'
        have hmax : max ta lo ≤ max sourceCut lo :=
          max_le_max hta.le (le_refl _)
        have htaDeadline : max ta lo + S.E.Δ ≤ targetEarly :=
          (add_le_add hmax (le_refl _)).trans hDeadline
        have htaEarly : ta < targetEarly :=
          (le_max_left ta lo).trans_lt
            ((lt_add_of_pos_right _ S.E.Δ_pos).trans_le htaDeadline)
        have hiEarly : i + 1 ≤ strictEventIndex rho targetEarly :=
          Nat.succ_le_of_lt (lt_strict_of_time_lt₅₃b₂ hf.sorted heSource (by rw [htSource]; exact htaEarly))
        by_cases hskip : H ∈ (W (i + 1) reader).st.bodies
        · exact bodies_mono_path₅₃b₂ facts S rho W hW reader hiEarly hskip
        · have hmissing : Restated.Vocabulary.Execution.Object.processed M
              (W (i + 1) reader).st (.block H) = false := by
            simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not]
              using hskip
          have hdr : max ta lo + S.E.Δ ≤ targetRead := htaDeadline.trans hOrder
          have hcompatRead : Block.compatible
              (W (strictEventIndex rho targetRead) reader).st.core.F H.erase = true :=
            Sts.compatible_of_cases (Sts.compatible_cases hcompat).symm
          have hguard : Block.compatible
              (W (strictEventIndex rho (max ta lo + S.E.Δ)) reader).st.core.F H.erase = true :=
            Restated.Vocabulary.Proofs.not_excludes_of_compatible_later_time facts S rho hf.sorted
              (w := reader) (B := H) hdr _
              (by rw [stateBeforeTime_eq_strict₅₃b₂ S rho hf.sorted]; exact (hW _).1) _
              (onePath_slice₅₃b W hW (Restated.strict_lengths_mono rho hdr))
              hcompatRead
          obtain ⟨td, hlo, hhi, j, hcall, hslot⟩ :=
            hf.relay_block_admit source i H ta (hHs _ _ hmax hsource) hacc
              reader (hHs _ _ htaDeadline hreader) hmissing (htaDeadline.trans hCut) hguard
          obtain ⟨e, he, _, het⟩ := hcall.2
          have htdEarly : td < targetEarly := hhi.trans_le htaDeadline
          have heEarly : e.time < targetEarly := by rw [het]; exact htdEarly
          have heRead : e.time < targetRead := heEarly.trans_le hOrder
          have hjEarly : j + 1 ≤ strictEventIndex rho targetEarly :=
            Nat.succ_le_of_lt (lt_strict_of_time_lt₅₃b₂ hf.sorted he heEarly)
          have hindex : j + 1 ≤ strictEventIndex rho targetRead :=
            Nat.succ_le_of_lt (lt_strict_of_time_lt₅₃b₂ hf.sorted he heRead)
          have hfuture : Block.Preceq (W j reader).st.core.F
              (W (strictEventIndex rho targetRead) reader).st.core.F :=
            path_F_mono₅₃b facts S rho W hW reader ((Nat.le_succ j).trans hindex)
          by_cases hheldCall : H ∈ (W j reader).st.bodies
          · exact bodies_mono_path₅₃b₂ facts S rho W hW reader ((Nat.le_succ j).trans hjEarly)
              hheldCall
          · have hFcall : Block.Preceq (W j reader).st.core.F H.erase := by
              rcases Sts.compatible_cases hcompat with hHF | hFH
              · rcases Sts.preceq_linear_Preceq hfuture hHF with h | h
                · exact h
                · have hFmem := Restated.Vocabulary.Proofs.NamedStoreBridge.finalizedInTree_stateBefore
                    facts S rho j reader (W j) (hW j).1
                  have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBefore
                    facts S rho j reader (W j) (hW j).1
                  unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
                  rw [facts.sto.toHealing_gs_T] at hpc
                  have hraw : H.erase ∈ (W j reader).st.core.T :=
                    Proofs.Records.mem_of_preceq hpc.2
                      H.erase _ hFmem (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr h)
                  obtain ⟨K, hK, hKErase⟩ :=
                    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore
                      facts S rho j reader (W j) (hW j).1 hraw
                  have hKscope : Restated.blockInRunOn M S rho W Xb K :=
                    Restated.blockInRun_of_directOn facts S rho W Xb
                      (Restated.directBlock_of_prefixOn facts S rho W Xb (hHsXb _ hreader) _ hK)
                  have hKH : K = H :=
                    Restated.runBlock_unique_of_erase_eqOn_RelativeCrossReader facts hf hKscope hHscope
                      hKErase
                  subst K
                  exact False.elim (hheldCall hK)
              · exact Proofs.ModelProperties.Preceq_trans hfuture hFH
            have hpost : H ∈ (W (j + 1) reader).st.bodies :=
              Restated.Vocabulary.Proofs.NamedRelayGuards.handled_block_held_of_finalized_prefix_of_fields
                facts S { rho with honest := Xb } W hW (fun i v o t hi => hf.deps i v o t hi) hroots
                (hHsXb _ hsource) (hHsXb _ hreader) hacc hcall hslot hFcall
            exact bodies_mono_path₅₃b₂ facts S rho W hW reader hjEarly hpost
  have hStamp := Restated.held_body_stampedBefore_stateBeforeTimeOn facts S rho Hs Xb hf reader
    targetEarly H hEarly
  obtain ⟨hHeld, hCarry⟩ := Restated.strict_body_stamp_carryOn facts S rho Hs Xb hf reader hOrder H
    hEarly
  refine ⟨hHeld, ?_, ?_⟩
  · obtain ⟨σ, hσ, hlt⟩ := Sts.exists_stamp_of_stampedBefore hStamp
    exact Sts.stampedBefore_of_lt (hCarry.trans hσ) hlt
  · simpa only [Proofs.NamedWire.erase_root] using
      (Restated.held_find_at_strictOn_RelativeCrossReader facts S rho Hs Xb hf (hHsXb _ hreader)
        targetRead H hHeld)

/-- If every tick has an outcome, `source` is in the set for `domain r .g1`, `target` in the set for
    `domain r .g0`, `0 < r`, `lo ≤ early r .g1`, `domain r .g0` is inside the horizon, and
    `G1G0CrossReaderFinalizedBelow` holds for `B` at their node states along `W`, then
    `G1G0CrossReaderBodyReadyGuard` holds for `B` at the same node states. -/
theorem g1G0CrossReaderBodyReadyGuard_of_finalizedBelowOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r)
    (hgst : lo ≤ M.early S.E S.hc r .g1)
    (horizon : M.domain S.E S.hc r .g0 ≤ rho.horizon)
    {source target : V} (hsource : source ∈ Hs (M.domain S.E S.hc r .g1))
    (htarget : target ∈ Hs (M.domain S.E S.hc r .g0)) {B : Block V}
    (hbelow : Restated.Vocabulary.Proofs.HealingSurface.G1G0CrossReaderFinalizedBelow M S rho r
      source target
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source)
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target) B) :
    Restated.Vocabulary.Proofs.HealingSurface.G1G0CrossReaderBodyReadyGuard M S rho r source target
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source)
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target) B := by
  have hW := hf.onePath
  have hE0D0 : M.early S.E S.hc r .g0 ≤ M.domain S.E S.hc r .g0 := by
    have h := facts.gr.early_add_two_delta_le_domain S r .g0
    linarith [S.E.Δ_pos]
  have hL1D1 := facts.gr.late_le_domain S r .g1
  have hL0D0 := facts.gr.late_le_domain S r .g0
  have hearlyHorizon : M.early S.E S.hc r .g0 ≤ rho.horizon := hE0D0.trans horizon
  have hlateHorizon : M.late S.E S.hc r .g1 ≤ rho.horizon :=
    hL1D1.trans ((facts.gr.domain_le_domain_g0 S r .g1).trans horizon)
  have hgstLate : lo ≤ M.late S.E S.hc r .g0 := by
    have h1 := facts.gr.early_g1_add_delta_le_early_g0 S r
    have h2 := facts.gr.early_le_late S.E S.hc r .g0
    linarith [S.E.Δ_pos]
  have hsourceEarly : source ∈ Hs (M.early S.E S.hc r .g1) :=
    hHs _ _ (facts.gr.early_g1_le_domain_g1 S r) hsource
  have htargetEarly : target ∈ Hs (M.early S.E S.hc r .g0) := hHs _ _ hE0D0 htarget
  have htargetLate : target ∈ Hs (M.late S.E S.hc r .g0) := hHs _ _ hL0D0 htarget
  have hsourceLate : source ∈ Hs (M.late S.E S.hc r .g1) := hHs _ _ hL1D1 hsource
  refine ⟨?_, ?_⟩
  · intro sender u I hI hu c hc hcover b hb
    obtain ⟨R, hR⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core))
      S.hc.η_SG r (M.early S.E S.hc r .g1) sender
    obtain ⟨bs, hbs⟩ := facts.gr.bodyReady_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core.F
      (M.early S.E S.hc r .g1) u
    have hready := ((facts.gr.mem_interpretedInputs_iff I hI R hR bs hbs).mp hu).2
    cases hconf : u.confirmed with
    | none => exact facts.gr.bodyReady_of_confirmed_none hconf b hb
    | some root =>
      obtain ⟨H, hfind, hstamp, -⟩ := facts.gr.bodyReady_parts bs hbs hready hconf
      rw [facts.gr.gradeView_timestamp_block] at hstamp
      have hHtree : H ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core.T := by
        have h := Proofs.HealingLemmas.find?_mem hfind
        rw [facts.gr.Sts_gradeView_T] at h
        exact h
      have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho _
        source _ (hW (strictEventIndex rho (M.domain S.E S.hc r .g1))).1).1.1.1
      rw [hcoh.1] at hHtree
      obtain ⟨Hn, hHbody, hHnErase⟩ := Finset.mem_image.mp hHtree
      have hHearly : Hn ∈ (W (strictEventIndex rho (M.early S.E S.hc r .g1)) source).st.bodies := by
        apply Restated.body_mem_stateBeforeTime_of_public_stampedBeforeOn facts S rho Hs Xb hf
          hsourceEarly (facts.gr.q10_early_g1_public S r hr) hgst hHbody
        rw [hHnErase]
        exact hstamp
      have hdeadline : max (M.early S.E S.hc r .g1) lo + S.E.Δ ≤ M.early S.E S.hc r .g0 := by
        rw [max_eq_left hgst]
        exact facts.gr.early_g1_add_delta_le_early_g0 S r
      have hFH : Block.Preceq
          (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core.F Hn.erase := by
        rw [hHnErase]
        exact hbelow.forward sender u root H I hI hu c hc hcover hconf hfind
      obtain ⟨-, hstampTarget, hfindTarget⟩ :=
        Restated.healthy_head_body_at_read_after_gst_admitOn facts S rho Hs Xb hf hHs hHsXb source
          target Hn (M.early S.E S.hc r .g1) (M.early S.E S.hc r .g0) (M.domain S.E S.hc r .g0)
          (by rw [max_eq_left hgst]; exact hsourceEarly) htargetEarly hHearly hdeadline hE0D0
          hearlyHorizon hFH
      have hroot : Hn.root = root := by
        rw [← Proofs.NamedWire.erase_root, hHnErase]
        exact Proofs.HealingLemmas.find?_root hfind
      refine facts.gr.bodyReady_of_find hconf (H := Hn.erase) ?_ ?_
        (Sts.compatible_of_cases (Or.inr hFH)) b hb
      · rw [facts.gr.Sts_gradeView_T, ← hroot]
        simpa only [Proofs.NamedWire.erase_root] using hfindTarget
      · rw [facts.gr.gradeView_timestamp_block]
        exact hstampTarget
  · intro sender u I hI hu b hb
    obtain ⟨R, hR⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core))
      S.hc.η_SG r (M.late S.E S.hc r .g0) sender
    obtain ⟨bt, hbt⟩ := facts.gr.bodyReady_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core.F
      (M.late S.E S.hc r .g0) u
    have hready := ((facts.gr.mem_interpretedInputs_iff I hI R hR bt hbt).mp hu).2
    cases hconf : u.confirmed with
    | none => exact facts.gr.bodyReady_of_confirmed_none hconf b hb
    | some root =>
      obtain ⟨H, hfind, hstamp, -⟩ := facts.gr.bodyReady_parts bt hbt hready hconf
      rw [facts.gr.gradeView_timestamp_block] at hstamp
      have hHtree : H ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core.T := by
        have h := Proofs.HealingLemmas.find?_mem hfind
        rw [facts.gr.Sts_gradeView_T] at h
        exact h
      have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho _
        target _ (hW (strictEventIndex rho (M.domain S.E S.hc r .g0))).1).1.1.1
      rw [hcoh.1] at hHtree
      obtain ⟨Hn, hHbody, hHnErase⟩ := Finset.mem_image.mp hHtree
      have hHlate : Hn ∈ (W (strictEventIndex rho (M.late S.E S.hc r .g0)) target).st.bodies := by
        apply Restated.body_mem_stateBeforeTime_of_public_stampedBeforeOn facts S rho Hs Xb hf
          htargetLate (facts.gr.late_g0_public S r hr) hgstLate hHbody
        rw [hHnErase]
        exact hstamp
      have hdeadline : max (M.late S.E S.hc r .g0) lo + S.E.Δ ≤ M.late S.E S.hc r .g1 := by
        rw [max_eq_left hgstLate]
        exact facts.gr.late_g0_add_delta_le_late_g1 S r
      have hcompatSource : Block.compatible Hn.erase
          (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core.F = true := by
        rw [hHnErase]
        exact hbelow.backward sender u root H I hI hu hconf hfind
      obtain ⟨-, hstampSource, hfindSource⟩ :=
        Restated.compatible_head_body_at_read_after_gstOn facts S rho Hs Xb hf hHs hHsXb target
          source Hn (M.late S.E S.hc r .g0) (M.late S.E S.hc r .g1) (M.domain S.E S.hc r .g1)
          (by rw [max_eq_left hgstLate]; exact htargetLate) hsourceLate hHlate hdeadline hL1D1
          hlateHorizon hcompatSource
      have hroot : Hn.root = root := by
        rw [← Proofs.NamedWire.erase_root, hHnErase]
        exact Proofs.HealingLemmas.find?_root hfind
      refine facts.gr.bodyReady_of_find hconf (H := Hn.erase) ?_ ?_ hcompatSource b hb
      · rw [facts.gr.Sts_gradeView_T, ← hroot]
        simpa only [Proofs.NamedWire.erase_root] using hfindSource
      · rw [facts.gr.gradeView_timestamp_block]
        exact hstampSource

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.NamedRawRelay
local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If every tick has an outcome, `Hs` shrinks as time grows, `lo ≤ opening (r − η_SG)`,
    `domain r .g0` is inside the horizon, `source` is in the set for `domain r .g1`, `target` in the
    set for `domain r .g0`, and `G1G0CrossReaderBodyReadyGuard` holds for `B` at their node states
    along `W`, then `G1G0CrossReaderTokenTransport` holds for `B` at those node states. -/
theorem g1G0CrossReaderTokenTransport_of_deliveryOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (r : Round) (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG))
    (horizon : M.domain S.E S.hc r .g0 ≤ rho.horizon)
    (source target : V) (hsource : source ∈ Hs (M.domain S.E S.hc r .g1))
    (htarget : target ∈ Hs (M.domain S.E S.hc r .g0)) (B : Block V)
    (guard : Restated.Vocabulary.Proofs.HealingSurface.G1G0CrossReaderBodyReadyGuard M S rho r
      source target
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source)
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target) B) :
    Restated.Vocabulary.Proofs.HealingSurface.G1G0CrossReaderTokenTransport M S rho r source target
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source)
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target) B := by
  have hB1 := facts.gr.early_g1_add_delta_le_early_g0 S r
  have hB2 := facts.gr.late_g0_add_delta_le_late_g1 S r
  have hA3 := facts.gr.opening_sub_five_delta_le_early_g2 S r
  have hA4 := facts.gr.late_g1_add_delta_lt_opening S r
  have hΔ := S.E.Δ_pos
  have hE2E1 := facts.gr.q10_early_g2_le_early_g1 S r
  have hE0L0 := facts.gr.early_le_late S.E S.hc r .g0
  have hE1D1 := facts.gr.early_g1_le_domain_g1 S r
  have hE0D0 := facts.gr.early_add_two_delta_le_domain S r .g0
  have hL0D0 := facts.gr.late_le_domain S r .g0
  have hL1D1 := facts.gr.late_le_domain S r .g1
  have hD1D0 := facts.gr.domain_le_domain_g0 S r .g1
  have hEd : M.early S.E S.hc r .g1 + S.E.Δ ≤ M.domain S.E S.hc r .g0 := by
    linarith only [hB1, hE0D0, hΔ]
  have hearlyHorizon : M.early S.E S.hc r .g1 + S.E.Δ ≤ rho.horizon := hEd.trans horizon
  have hLd : M.late S.E S.hc r .g0 + S.E.Δ ≤ M.domain S.E S.hc r .g1 := by
    linarith only [hB2, hL1D1]
  have hlateHorizon : M.late S.E S.hc r .g0 + S.E.Δ ≤ rho.horizon := by
    linarith only [hLd, hD1D0, horizon]
  have hEo : M.early S.E S.hc r .g1 + S.E.Δ < M.opening S.E S.hc r := by
    linarith only [hB1, hE0L0, hB2, hA4, hΔ]
  have hLo : M.late S.E S.hc r .g0 + S.E.Δ < M.opening S.E S.hc r := by
    linarith only [hB2, hA4, hΔ]
  have hcE : M.opening S.E S.hc r - 5 * S.E.Δ ≤ M.early S.E S.hc r .g1 := by
    linarith only [hA3, hE2E1]
  have hcL : M.opening S.E S.hc r - 5 * S.E.Δ ≤ M.late S.E S.hc r .g0 := by
    linarith only [hcE, hB1, hE0L0, hΔ]
  have hsrcE : source ∈ Hs (M.early S.E S.hc r .g1) := hHs _ _ hE1D1 hsource
  have htgtL : target ∈ Hs (M.late S.E S.hc r .g0) := hHs _ _ hL0D0 htarget
  refine ⟨?_, ?_, ?_⟩
  · intro sender x X hX hx c hc hctrue Y hY R hR
    obtain ⟨Is, hIs⟩ := facts.gr.interpretedInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core.F
      S.hc.η_SG r (M.early S.E S.hc r .g1) sender
    obtain ⟨u, hu, rfl⟩ := (facts.gr.mem_readyView_iff X hX Is hIs).mp hx
    obtain ⟨Rs, hRs⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core))
      S.hc.η_SG r (M.early S.E S.hc r .g1) sender
    obtain ⟨bs, hbs⟩ := facts.gr.bodyReady_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core.F
      (M.early S.E S.hc r .g1) u
    obtain ⟨hraw, -⟩ := (facts.gr.mem_interpretedInputs_iff Is hIs Rs hRs bs hbs).mp hu
    have hval : u.val_index = sender := facts.gr.val_index_of_mem_rawInputs Rs hRs hraw
    obtain ⟨a, i, accepted, hproj, hwindow, hbefore, hacc⟩ :=
      Restated.g1_raw_input_source_acceptanceOn facts S rho Hs Xb hf source r sender u Rs hRs hraw
        hsrcE (facts.gr.lo_le_of_rawInputs_l53 S hlo hcE Rs hRs hraw)
    have hround : a.round = u.round :=
      (facts.sto.sgVote_round a).symm.trans
        (congrArg Protocol.SGVote.round hproj)
    have hidx : a.val_index = sender :=
      (facts.sto.sgVote_val a).symm.trans
        ((congrArg Protocol.SGVote.val_index hproj).trans hval)
    have hrelay := Restated.accepted_sg_vote_or_equiv_of_twoCutoffOn facts S rho Hs Xb hf hHs r
      (M.early S.E S.hc r .g1) (M.domain S.E S.hc r .g0) hEd hEo hearlyHorizon hlo
      (hHs _ _ hbefore.le hsrcE) hacc hbefore hwindow target htarget
    obtain ⟨Rt, hRt⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core))
      S.hc.η_SG r (M.early S.E S.hc r .g1 + S.E.Δ) a.val_index
    have hrelay' := hrelay Rt hRt
    simp only [hproj, hidx] at hrelay'
    rw [hidx] at hRt
    rcases hrelay' with hexact |
      ⟨left, hleft, right, hright, hlr, hrr, _, _, hne⟩
    · obtain ⟨It, hIt⟩ := facts.gr.interpretedInputs_nonempty
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core.F
        S.hc.η_SG r (M.early S.E S.hc r .g0) sender
      obtain ⟨Rt₁, hRt₁⟩ := facts.gr.rawInputs_nonempty
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core))
        S.hc.η_SG r (M.early S.E S.hc r .g0) sender
      obtain ⟨bt, hbt⟩ := facts.gr.bodyReady_nonempty
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core.F
        (M.early S.E S.hc r .g0) u
      rw [facts.gr.token_key] at hc
      exact Or.inl ((facts.gr.mem_readyView_iff Y hY It hIt).mpr ⟨u,
        (facts.gr.mem_interpretedInputs_iff It hIt Rt₁ hRt₁ bt hbt).mpr
          ⟨facts.gr.rawInputs_mono _ _ _ hB1 _ Rt hRt Rt₁ hRt₁ hexact,
            guard.forward sender u Is hIs hu c hc hctrue bt hbt⟩, rfl⟩)
    · obtain ⟨Rl, hRl⟩ := facts.gr.rawInputs_nonempty
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core))
        S.hc.η_SG r (M.late S.E S.hc r .g0) sender
      have hsub := facts.gr.rawInputs_mono _ _ _ (hB1.trans hE0L0) _ Rt hRt Rl hRl
      exact Or.inr ⟨M.token left,
        (facts.gr.mem_rawView_iff _ _ _ _ _ _ R hR Rl hRl).mpr ⟨left, hsub hleft, rfl⟩,
        M.token right,
        (facts.gr.mem_rawView_iff _ _ _ _ _ _ R hR Rl hRl).mpr ⟨right, hsub hright, rfl⟩,
        (by rw [facts.gr.token_round, facts.gr.token_round]; exact hlr.trans hround),
        (by rw [facts.gr.token_round, facts.gr.token_round]; exact hrr.trans hround),
        (by rw [facts.gr.token_key, facts.gr.token_key]; exact hne)⟩
  · intro sender x X hX hx Y hY R hR
    obtain ⟨It, hIt⟩ := facts.gr.interpretedInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core.F
      S.hc.η_SG r (M.late S.E S.hc r .g0) sender
    obtain ⟨u, hu, rfl⟩ := (facts.gr.mem_readyView_iff X hX It hIt).mp hx
    obtain ⟨Rt, hRt⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core))
      S.hc.η_SG r (M.late S.E S.hc r .g0) sender
    obtain ⟨bt, hbt⟩ := facts.gr.bodyReady_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core.F
      (M.late S.E S.hc r .g0) u
    obtain ⟨hraw, -⟩ := (facts.gr.mem_interpretedInputs_iff It hIt Rt hRt bt hbt).mp hu
    have hval : u.val_index = sender := facts.gr.val_index_of_mem_rawInputs Rt hRt hraw
    obtain ⟨a, i, accepted, hproj, hwindow, hbefore, hacc⟩ :=
      Restated.g0_late_raw_input_acceptanceOn facts S rho Hs Xb hf target r sender u Rt hRt hraw
        htgtL (facts.gr.lo_le_of_rawInputs_l53 S hlo hcL Rt hRt hraw)
    have hround : a.round = u.round :=
      (facts.sto.sgVote_round a).symm.trans
        (congrArg Protocol.SGVote.round hproj)
    have hidx : a.val_index = sender :=
      (facts.sto.sgVote_val a).symm.trans
        ((congrArg Protocol.SGVote.val_index hproj).trans hval)
    have hone := Restated.accepted_sg_vote_or_equiv_of_twoCutoffOn facts S rho Hs Xb hf hHs r
      (M.late S.E S.hc r .g0) (M.domain S.E S.hc r .g1) hLd hLo hlateHorizon hlo
      (hHs _ _ hbefore.le htgtL) hacc hbefore hwindow source hsource
    obtain ⟨Rs, hRs⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core))
      S.hc.η_SG r (M.late S.E S.hc r .g0 + S.E.Δ) a.val_index
    have hone' := hone Rs hRs
    simp only [hproj, hidx] at hone'
    rw [hidx] at hRs
    obtain ⟨Rs₂, hRs₂⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core))
      S.hc.η_SG r (M.late S.E S.hc r .g1) sender
    have hsub := facts.gr.rawInputs_mono _ _ _ hB2 _ Rs hRs Rs₂ hRs₂
    rcases hone' with hexact |
      ⟨left, hleft, right, hright, hlr, hrr, _, _, hne⟩
    · obtain ⟨Is, hIs⟩ := facts.gr.interpretedInputs_nonempty
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core.F
        S.hc.η_SG r (M.late S.E S.hc r .g1) sender
      obtain ⟨bs, hbs⟩ := facts.gr.bodyReady_nonempty
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core.F
        (M.late S.E S.hc r .g1) u
      exact Or.inl ((facts.gr.mem_readyView_iff Y hY Is hIs).mpr ⟨u,
        (facts.gr.mem_interpretedInputs_iff Is hIs Rs₂ hRs₂ bs hbs).mpr
          ⟨hsub hexact, guard.backward sender u It hIt hu bs hbs⟩, rfl⟩)
    · exact Or.inr ⟨M.token left,
        (facts.gr.mem_rawView_iff _ _ _ _ _ _ R hR Rs₂ hRs₂).mpr ⟨left, hsub hleft, rfl⟩,
        M.token right,
        (facts.gr.mem_rawView_iff _ _ _ _ _ _ R hR Rs₂ hRs₂).mpr ⟨right, hsub hright, rfl⟩,
        (by rw [facts.gr.token_round, facts.gr.token_round]; exact hlr.trans hround),
        (by rw [facts.gr.token_round, facts.gr.token_round]; exact hrr.trans hround),
        (by rw [facts.gr.token_key, facts.gr.token_key]; exact hne)⟩
  · intro sender x X hX hx Y hY
    obtain ⟨Rt, hRt⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core))
      S.hc.η_SG r (M.late S.E S.hc r .g0) sender
    obtain ⟨u, hu, rfl⟩ := (facts.gr.mem_rawView_iff _ _ _ _ _ _ X hX Rt hRt).mp hx
    have hval : u.val_index = sender := facts.gr.val_index_of_mem_rawInputs Rt hRt hu
    obtain ⟨a, i, accepted, hproj, hwindow, hbefore, hacc⟩ :=
      Restated.g0_late_raw_input_acceptanceOn facts S rho Hs Xb hf target r sender u Rt hRt hu
        htgtL (facts.gr.lo_le_of_rawInputs_l53 S hlo hcL Rt hRt hu)
    have hround : a.round = u.round :=
      (facts.sto.sgVote_round a).symm.trans
        (congrArg Protocol.SGVote.round hproj)
    have hidx : a.val_index = sender :=
      (facts.sto.sgVote_val a).symm.trans
        ((congrArg Protocol.SGVote.val_index hproj).trans hval)
    have hone := Restated.accepted_sg_vote_or_equiv_of_twoCutoffOn facts S rho Hs Xb hf hHs r
      (M.late S.E S.hc r .g0) (M.domain S.E S.hc r .g1) hLd hLo hlateHorizon hlo
      (hHs _ _ hbefore.le htgtL) hacc hbefore hwindow source hsource
    obtain ⟨Rs, hRs⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core))
      S.hc.η_SG r (M.late S.E S.hc r .g0 + S.E.Δ) a.val_index
    have hone' := hone Rs hRs
    simp only [hproj, hidx] at hone'
    rw [hidx] at hRs
    obtain ⟨Rs₂, hRs₂⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core))
      S.hc.η_SG r (M.late S.E S.hc r .g1) sender
    have hsub := facts.gr.rawInputs_mono _ _ _ hB2 _ Rs hRs Rs₂ hRs₂
    rcases hone' with hexact |
      ⟨left, hleft, right, hright, hlr, hrr, _, _, hne⟩
    · exact Or.inl ((facts.gr.mem_rawView_iff _ _ _ _ _ _ Y hY Rs₂ hRs₂).mpr ⟨u, hsub hexact, rfl⟩)
    · exact Or.inr ⟨M.token left,
        (facts.gr.mem_rawView_iff _ _ _ _ _ _ Y hY Rs₂ hRs₂).mpr ⟨left, hsub hleft, rfl⟩,
        M.token right,
        (facts.gr.mem_rawView_iff _ _ _ _ _ _ Y hY Rs₂ hRs₂).mpr ⟨right, hsub hright, rfl⟩,
        (by rw [facts.gr.token_round, facts.gr.token_round]; exact hlr.trans hround),
        (by rw [facts.gr.token_round, facts.gr.token_round]; exact hrr.trans hround),
        (by rw [facts.gr.token_key, facts.gr.token_key]; exact hne)⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.NamedRawRelay
local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If `source, target ∈ Xb`, `G1G0CrossReaderBodyReadyGuard` holds for `B` at their node states in
    `W (strictEventIndex rho (domain r .g1))` and `W (strictEventIndex rho (domain r .g0))`, and `x`
    is in an outcome of the grade-0 late ready view of `target`'s node state, then every outcome of
    the cover test of `x`'s key for `B` at `source`'s node state is `true` exactly when every
    outcome at `target`'s is. -/
theorem localCovers_iff_of_g1G0_target_readyOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (r : Round) (source target : V) (hsource : source ∈ Xb)
    (htarget : target ∈ Xb) (sender : V) (B : Block V)
    (guard : Restated.Vocabulary.Proofs.HealingSurface.G1G0CrossReaderBodyReadyGuard M S rho r
      source target
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source)
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target) B)
    (x : Token (Option BlockId))
    (X : Finset (Token (Option BlockId)))
    (hX : M.readyView
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core.F
      S.hc.η_SG r (M.late S.E S.hc r .g0) sender ⇢ X)
    (htargetReady : x ∈ X) :
    ∀ c, M.localCovers
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core))
        x.key B ⇢ c →
    ∀ d, M.localCovers
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core))
        x.key B ⇢ d →
    (c = true ↔ d = true) := by
  intro c hc d hd
  obtain ⟨J, hJ⟩ := facts.gr.interpretedInputs_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core.F
    S.hc.η_SG r (M.late S.E S.hc r .g0) sender
  obtain ⟨u, hu, rfl⟩ := (facts.gr.mem_readyView_iff X hX J hJ).mp htargetReady
  obtain ⟨RZ, hRZ⟩ := facts.gr.rawInputs_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core))
    S.hc.η_SG r (M.late S.E S.hc r .g0) sender
  obtain ⟨bZ, hbZ⟩ := facts.gr.bodyReady_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core.F
    (M.late S.E S.hc r .g0) u
  obtain ⟨bS, hbS⟩ := facts.gr.bodyReady_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st.core.F
    (M.late S.E S.hc r .g1) u
  have hbodyTarget := ((facts.gr.mem_interpretedInputs_iff J hJ RZ hRZ bZ hbZ).mp hu).2
  have hbodySource := guard.backward sender u J hJ hu bS hbS
  rw [facts.gr.token_key] at hc hd
  cases hconf : u.confirmed with
  | none =>
      rw [hconf] at hc hd
      rw [facts.gr.localCovers_none _ _ c hc, facts.gr.localCovers_none _ _ d hd]
  | some root =>
      obtain ⟨H, hfindSource, -, -⟩ := facts.gr.bodyReady_parts bS hbS hbodySource hconf
      obtain ⟨K, hfindTarget, -, -⟩ := facts.gr.bodyReady_parts bZ hbZ hbodyTarget hconf
      have hHK :=
        Restated.find_agreeOn facts S rho Hs Xb hf
          source target hsource htarget
          (M.domain S.E S.hc r .g1) (M.domain S.E S.hc r .g0)
          root (by rw [facts.gr.Sts_gradeView_T] at hfindSource; exact hfindSource)
          (by rw [facts.gr.Sts_gradeView_T] at hfindTarget; exact hfindTarget)
      subst K
      rw [hconf] at hc hd
      rw [facts.gr.localCovers_some_iff_of_find hfindSource c hc,
        facts.gr.localCovers_some_iff_of_find hfindTarget d hd]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.NamedRawRelay
local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the hypotheses of `g1G0CrossReaderTokenTransport_of_deliveryOn` for `v` and `w`, if the
    grade-1 store grade of `B` at `v`'s node state in `W (strictEventIndex rho (domain r .g1))` can
    return `true`, then every outcome of the grade-0 store grade of `B` at `w`'s node state in
    `W (strictEventIndex rho (domain r .g0))` is `true`. -/
theorem storeGrade_g0_of_storeGrade_g1_cross_readerOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (r : Round) (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG))
    (horizon : M.domain S.E S.hc r .g0 ≤ rho.horizon)
    (v w : V) (hv : v ∈ Hs (M.domain S.E S.hc r .g1)) (hw : w ∈ Hs (M.domain S.E S.hc r .g0))
    (B : Block V)
    (hgrade : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st r .g1 B ⇢ true)
    (guard : Restated.Vocabulary.Proofs.HealingSurface.G1G0CrossReaderBodyReadyGuard M S rho r v w
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v)
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w) B) :
    ∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st r .g0 B ⇢ b → b = true := by
  intro b hb
  have tr := Restated.g1G0CrossReaderTokenTransport_of_deliveryOn facts S rho Hs Xb hf hHs r
    hlo horizon v w hv hw B guard
  set ns := W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v with hns
  set nt := W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w with hnt
  choose covS hcovS using fun k blk => facts.gr.localCovers_nonempty
    (M.gradeView (M.toHealing ns.st.core)) k blk
  choose covT hcovT using fun k blk => facts.gr.localCovers_nonempty
    (M.gradeView (M.toHealing nt.st.core)) k blk
  choose srcEarly hsE using fun sender => facts.gr.readyView_nonempty
    (M.gradeView (M.toHealing ns.st.core)) ns.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g1) sender
  choose srcLate hsL using fun sender => facts.gr.readyView_nonempty
    (M.gradeView (M.toHealing ns.st.core)) ns.st.core.F S.hc.η_SG r (M.late S.E S.hc r .g1) sender
  choose srcRaw hsR using fun sender => facts.gr.rawView_nonempty
    (M.gradeView (M.toHealing ns.st.core)) S.hc.η_SG r (M.late S.E S.hc r .g1) sender
  choose dstEarly hdE using fun sender => facts.gr.readyView_nonempty
    (M.gradeView (M.toHealing nt.st.core)) nt.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g0) sender
  choose dstLate hdL using fun sender => facts.gr.readyView_nonempty
    (M.gradeView (M.toHealing nt.st.core)) nt.st.core.F S.hc.η_SG r (M.late S.E S.hc r .g0) sender
  choose dstRaw hdR using fun sender => facts.gr.rawView_nonempty
    (M.gradeView (M.toHealing nt.st.core)) S.hc.η_SG r (M.late S.E S.hc r .g0) sender
  have hsrc : Restated.Vocabulary.Protocol.grade M S.E.electorate.weight
      (fun k blk => covS k blk = true) srcEarly srcLate srcRaw B :=
    (Restated.Vocabulary.Proofs.NamedOutageHistory.GuardedHelpers.storeGrade_iff facts S ns.st r .g1 B
      true hgrade covS hcovS srcEarly hsE srcLate hsL srcRaw hsR).mp rfl
  have hEqBack : ∀ sender k, EquivocationAt (dstRaw sender) k →
      EquivocationAt (srcRaw sender) k := by
    intro sender k hk
    exact DecoupledConsensusModel.Protocol.equivocation_back_of_vote_or_equivocation
      (fun y hy => tr.rawBack sender y (dstRaw sender) (hdR sender) hy (srcRaw sender) (hsR sender)) hk
  have hdstSub : ∀ sender, dstEarly sender ⊆ dstLate sender := fun sender =>
    facts.gr.readyView_mono _ _ _ _ (facts.gr.early_le_late S.E S.hc r .g0) sender
      _ (hdE sender) _ (hdL sender)
  have htransport : Restated.Vocabulary.Protocol.grade M S.E.electorate.weight
      (fun k blk => covS k blk = true) dstEarly dstLate dstRaw B :=
    Restated.Vocabulary.Protocol.grade_transport_with_cap facts
      (se := srcEarly) (sl := srcLate) (sr := srcRaw)
      (te := dstEarly) (tl := dstLate) (tr := dstRaw) (B := B)
      S.E.electorate.weight (fun k blk => covS k blk = true)
      (fun sender => facts.gr.readyView_mono _ _ _ _ (facts.gr.early_g1_le_late_g1 S r) sender
        _ (hsE sender) _ (hsL sender))
      (fun sender => facts.gr.readyView_subset_rawView _ _ _ _ _ sender
        _ (hsL sender) _ (hsR sender))
      hdstSub
      (fun sender u hu hcov => tr.forward sender u (srcEarly sender) (hsE sender) hu
        (covS u.key B) (hcovS _ _) hcov (dstEarly sender) (hdE sender) (dstRaw sender) (hdR sender))
      (fun sender x hx => tr.lateBack sender x (dstLate sender) (hdL sender) hx
        (srcLate sender) (hsL sender) (srcRaw sender) (hsR sender))
      hEqBack hsrc
  have htarget : Restated.Vocabulary.Protocol.grade M S.E.electorate.weight
      (fun k blk => covT k blk = true) dstEarly dstLate dstRaw B :=
    Restated.Vocabulary.Proofs.NamedOutageHistory.GuardedHelpers.grade_congr facts
      S.E.electorate.weight (fun k blk => covS k blk = true) (fun k blk => covT k blk = true)
      hdstSub
      (fun sender x hx =>
        Restated.localCovers_iff_of_g1G0_target_readyOn facts S rho Hs Xb hf r v w (hHsXb _ hv)
          (hHsXb _ hw) sender B guard x (dstLate sender) (hdL sender) hx _ (hcovS _ _) _ (hcovT _ _))
      htransport
  exact (Restated.Vocabulary.Proofs.NamedOutageHistory.GuardedHelpers.storeGrade_iff facts S nt.st r .g0 B
    b hb covT hcovT dstEarly hdE dstLate hdL dstRaw hdR).mpr htarget

end

section
set_option autoImplicit false
open scoped DC
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If every tick has an outcome, `lo + 4Δ · R · readyLag ≤ Γ_neg1 r0`, event `i` is the attester's
    tick at `ta` that sends `a` along `W`, and the attester is in the set for `domain a.round .g0`,
    then for every node state `n` of its round-`a.round` action read, every `w` in the set for
    `domain a.round .g1` and every `Q` that `n`'s Q2 can be, `CrossReaderBodyReadyGuard` holds for
    `Q` at the attester's node state in `W (strictEventIndex rho (domain a.round .g2))` and `w`'s in
    `W (strictEventIndex rho (domain a.round .g1))`. -/
theorem crossReaderBodyReadyGuard_of_namedHeightRegimeFrameOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} {Wt : Time → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {X : Finset V}
    {r0 : Round}
    (hgst : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    {stop : Nat} {H : Height} {Prev : NamedBlock V}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    (_hframe : Restated.NamedHeightRegimeFrameOn M S rho W Wt Hs X Xb H
      (stop - 1) Prev a.round)
    (hiStart : inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0) ≤ i)
    (_hiStop : i < stop) (haHon : a.val_index ∈ Hs (M.domain S.E S.hc a.round .g0))
    (hiEvent : rho.events[i]? = some (Record.Event.tick a.val_index ta))
    (hiOutput : ∃ out : M.N × List (NamedObject V),
      M.tick S a.val_index (W i a.val_index) ta ⇢ out ∧ W (i + 1) a.val_index = out.1 ∧
        Object.attest a ∈ out.2)
    (_hrow : a.height_pair.erase.height? = some (H + 1))
    (_hfrontier : (X.sup fun v => (W i v).st.h_max) < H + 2) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
      a.round,
    ∀ w, w ∈ Hs (M.domain S.E S.hc a.round .g1) → ∀ Q,
      Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n a.round ⇢ some Q →
      Restated.Vocabulary.Proofs.HealingSurface.CrossReaderBodyReadyGuard M S rho a.round
        a.val_index w
        (W (strictEventIndex rho (M.domain S.E S.hc a.round .g2)) a.val_index)
        (W (strictEventIndex rho (M.domain S.E S.hc a.round .g1)) w) Q := by
  have hW := hf.onePath
  have hΔ := S.E.Δ_pos
  have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (Object.attest a)
      ta := by
    obtain ⟨out, hout, hstep, hmem⟩ := hiOutput
    exact ⟨i, hiEvent, out, hout, hstep, hmem⟩
  have htime : ta = (Restated.Vocabulary.Execution.Setup.a M S a.round) :=
    (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hW hemit).2
  have hactionHorizon : (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ rho.horizon := by
    have hin :=
      (hf.in_horizon (Record.Event.tick a.val_index ta)
        (List.mem_of_getElem? hiEvent)).2
    simpa only [Record.Event.time, htime, Record.Event.time] using hin
  have hroundFromStart : r0 ≤ a.round := by
    by_contra hnot
    have haRoundLt : a.round < r0 := Nat.lt_of_not_ge hnot
    have htimeLt : ta < (Restated.Vocabulary.Execution.Setup.a M S r0) := by
      rw [htime]
      exact Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S haRoundLt
    have hstartCursor : strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S r0)) ≤ i :=
      (strictEventIndex_le_inclusiveEventIndex rho
        ((Restated.Vocabulary.Execution.Setup.a M S r0))).trans hiStart
    have htimeLe : (Restated.Vocabulary.Execution.Setup.a M S r0) ≤ ta :=
      Restated.le_time_of_index_ge_of_sorted hf.sorted hstartCursor hiEvent
    exact (not_le_of_gt htimeLt) htimeLe
  have hloEarly : lo ≤ M.early S.E S.hc a.round .g2 := by
    have hmono : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0 ≤
        Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ a.round :=
      Restated.Vocabulary.Proofs.HealingSurface.Γ_neg1_mono facts S.hc S.E.Δ_pos hroundFromStart
    have hlag : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) =
        lo + 4 * S.E.Δ * (S.hc.R : Nat) := by
      simp [readyLag]
    have hΔnn : (0 : Time) ≤ 4 * S.E.Δ := by linarith [S.E.Δ_pos]
    have hR2 : (2 : Time) ≤ (S.hc.R : Nat) := by exact_mod_cast S.hc.R_ge_two
    have hshift2 : 8 * S.E.Δ ≤ 4 * S.E.Δ * (S.hc.R : Nat) := by
      calc 8 * S.E.Δ = 4 * S.E.Δ * 2 := by ring
        _ ≤ 4 * S.E.Δ * (S.hc.R : Nat) := mul_le_mul_of_nonneg_left hR2 hΔnn
    have hchain : lo + 4 * S.E.Δ * (S.hc.R : Nat) ≤
        Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ a.round :=
      hlag ▸ le_trans hgst hmono
    have hvote := facts.sch.Γ_1_eq_vote_time S.hc S.E a.round
    have hconf := facts.sch.vote_time_add_delta_le_confirmation_time S (M.opening_slot S.hc a.round)
    have hacon := facts.sch.a_eq_confirmation_time S.hc S.E a.round
    unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 at hchain
    rw [facts.gr.early_g2_eq]
    linarith
  have hdomHor : M.domain S.E S.hc a.round .g0 ≤ rho.horizon :=
    (facts.gr.domain_le_a S a.round .g0).trans hactionHorizon
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have haHon2 : a.val_index ∈ Hs (M.domain S.E S.hc a.round .g2) :=
    hHs _ _ ((facts.gr.domain_g2_le_domain_g1 S a.round).trans
      (facts.gr.domain_le_domain_g0 S a.round .g1)) haHon
  intro n hn w hw Q hQ
  have hQ2 : M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      a.round ⇢ some Q := by
    have hq := hQ
    unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2
      Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hq
    obtain ⟨G, hG, hGQ⟩ :=
      (priv% Proofs.Claims.Restated.Claim13beRoute3_50
        DecoupledConsensusModel.Sts.Restated.returns_map_elim₅₀) _ _ _ hq
    obtain ⟨Q', hQ'⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) a.round
    have hQ'eq : Q' = some Q :=
      (facts.dt.grade2_block_with_eq_read_Q2 _ S.E S.hc _ a.round G hG Q' hQ').trans hGQ
    rw [hQ'eq] at hQ'
    exact hQ'
  have hr : 0 < a.round := by
    apply Nat.pos_of_ne_zero
    intro hzero
    obtain ⟨j, raw, -, -, w0, -, -, hfreeze, -⟩ :=
      Restated.Vocabulary.Proofs.HealingSurface.contractQ2_capture_at_action_index facts
        S rho (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round))
        a.val_index a.round (W _) (hW _).1 n hn hQ2
    obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E
      (M.gradeView (M.toHealing (w0 a.val_index).st.core)) (w0 a.val_index).st.core.F S.hc.η_SG
      a.round (M.early S.E S.hc a.round .g2) (M.late S.E S.hc a.round .g2)
    have hfrsome := hfreeze fr hfr
    obtain ⟨g, hg⟩ := facts.gr.gradeBool_nonempty S.E
      (M.gradeView (M.toHealing (w0 a.val_index).st.core)) (w0 a.val_index).st.core.F S.hc.η_SG
      a.round (M.early S.E S.hc a.round .g2) (M.late S.E S.hc a.round .g2) raw
    have hgtrue := facts.gr.gradeBool_of_freezeRoot_eq_some fr hfr hfrsome g hg
    rw [hzero] at hg
    have hgfalse := facts.gr.gradeBool_round_zero _ _ _ _ _ _ _ g hg
    rw [hgtrue] at hgfalse
    cases hgfalse
  have hdomainAction :
      M.domain S.E S.hc a.round .g0 ≤ (Restated.Vocabulary.Execution.Setup.a M S a.round) :=
    facts.gr.domain_le_a S a.round .g0
  have hmono : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc a.round .g0)) a.val_index).st.core.F
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round))
        a.val_index).st.core.F :=
    path_F_mono₅₃b facts S rho W hW a.val_index (strictEventIndex_mono rho hdomainAction)
  have hFQAction : Block.Preceq
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round))
        a.val_index).st.core.F Q := by
    have hmem : W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) ∈
        Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
          (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
      rw [stateBeforeTime_eq_strict₅₃b₂ S rho hf.sorted]
      exact (hW _).1
    have hactive := Restated.Vocabulary.Proofs.HealingSurface.actionQ2_mem_filteredTree facts S rho
      a.val_index a.round _ hmem n hn hQ
    have hFQ := facts.fc.q10_filtered_F hactive
    rw [facts.sto.Sts_toHealing_F,
      (priv% Proofs.Claims.Restated.Claim13beRoute3_48b
        DecoupledConsensusModel.Sts.Restated.actionReadFrom_F₄₈b) facts S _ a.round n hn] at hFQ
    exact hFQ
  have hsourceFQ : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc a.round .g0)) a.val_index).st.core.F Q :=
    Proofs.ModelProperties.Preceq_trans hmono hFQAction
  have hpost : lo ≤ M.domain S.E S.hc a.round .g1 :=
    hloEarly.trans ((facts.gr.early_le_domain S a.round).trans
      (facts.gr.domain_g2_le_domain_g1 S a.round))
  have hhop : M.domain S.E S.hc a.round .g1 + S.E.Δ =
      M.domain S.E S.hc a.round .g0 := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.domain_g0_eq_opening]
  have hrelay : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc a.round .g1)) w).st.core.F
      (W (strictEventIndex rho (M.domain S.E S.hc a.round .g0)) a.val_index).st.core.F :=
    Restated.finalized_preceq_of_evidence_deliveredOn facts S Hs Xb hf hHs hHsXb hsb hw haHon hpost
      hhop hdomHor
  have hfinalized :=
    Restated.crossReaderFinalizedBelow_of_finalitySafety_and_relayOn facts S Hs Xb hf hHs hHsXb hsb
      hloEarly hdomHor haHon2 hw (B := Q)
      (by
        intro sender u root Head I _ _ c hc hctrue hconf hfind
        have hQHead : Block.Preceq Q Head := by
          rw [hconf] at hc
          exact facts.gr.preceq_of_localCovers_of_find c hc hctrue hfind
        exact Proofs.ModelProperties.Preceq_trans hrelay
          (Proofs.ModelProperties.Preceq_trans hsourceFQ hQHead))
  exact Restated.crossReaderBodyReadyGuard_of_finalizedBelowOn facts S Hs Xb hf hHs hHsXb hr
    hloEarly hdomHor haHon2 hw hfinalized

end

end DecoupledConsensusModel.Sts.Restated
