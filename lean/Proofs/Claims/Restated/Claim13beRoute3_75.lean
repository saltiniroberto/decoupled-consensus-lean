import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13b
import Proofs.Claims.Restated.Claim13bDirection
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Claim13bStepAnchor
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bStepSGMove
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_73
import Proofs.Claims.Restated.Claim13beRoute3_8
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_FinalityCertificates
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_8
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_75

/-!
# The clauses `targetsTop` and `fin` from a regime

For a run-scoped regime on the run `runAll`, read along `Restated.runAllPath`, stated over a model
`M : Record.Model V`: honest height votes at the checkpoint's height name the checkpoint, and every
honestly finalized block is an ancestor of the checkpoint, at a round of the phase and at the switch
round.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p63% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_63)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p69b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_69b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p72% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_72)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p73% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_73)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- A chain finalized at `h₁ ≠ 0` and a chain of greater height either have slashable weight between
    the rows of the second chain and the rows of the first, or the second chain's block at
    chain-state height `h₁` erases to the first chain's finalized block. -/
private theorem finalized_vs_crossing_slashable₇₅ (facts : Record.Facts M) (E : Env V)
    (cfg : Protocol.HeightConfig)
    {B₁ B₂ : NamedBlock V} {T₁ : Block V} {h₁ : Height}
    (hroot : RootInjectiveOnAncestors B₁.erase B₂.erase)
    (hf₁ : Restated.NamedFinalizedAt M E cfg B₁ T₁ h₁) (hnz : h₁ ≠ 0)
    (hlt : h₁ < (M.derive_named E cfg B₂).h) :
    M.HasSlashableWeightBetween E (M.chain_attestations B₂.erase)
        (M.chain_attestations B₁.erase) ∨
      ∃ X : NamedBlock V, NamedBlock.Preceq X B₂ ∧
        (M.derive_named E cfg X).h = h₁ ∧ X.erase = T₁ := by
  obtain ⟨hF₁, hh₁⟩ := hf₁
  obtain ⟨F, _hFB₁, hFerase, QF, hQF, hwF⟩ :=
    Restated.Vocabulary.Proofs.NamedFinalityCertificates.finality_certificate facts E cfg B₁
      (by rw [hh₁]; exact hnz)
  have hFroot : F.root = T₁.root := by
    rw [← Proofs.NamedWire.erase_root F, hFerase, hF₁]
  obtain ⟨X, hXB₂, hXh, QP, hQP, hwP⟩ :=
    facts.cs.height_crossing E cfg B₂ h₁
      (Nat.one_le_iff_ne_zero.mpr hnz) hlt
  have hXB₂P : Block.Preceq X.erase B₂.erase := Proofs.NamedWire.erase_preceq hXB₂
  by_cases hxr : X.root = T₁.root
  · refine Or.inr ⟨X, hXB₂, hXh, ?_⟩
    have hT₁B₁ : Block.Preceq T₁ B₁.erase := by
      rw [← hF₁]
      exact ((facts.cs.derive_named_anchors_preceq E cfg B₁)).1
    exact (RootInjectiveOnAncestors.eq_of_root_eq hroot hT₁B₁ hXB₂P
      (by rw [Proofs.NamedWire.erase_root]; exact hxr.symm)).symm
  · refine Or.inl (facts.ev.ModelProperties_hasSlashableWeightBetween_intro (QP ∩ QF)
      (facts.ev.quorum_intersection E hQP hQF) fun i hi => ?_)
    obtain ⟨hiP, hiF⟩ := Finset.mem_inter.mp hi
    obtain ⟨cF, a, hcF, haF, hav, hap⟩ := hwF i hiF
    obtain ⟨cP, b, hcP, hbP, hbv, hbm⟩ := hwP i hiP
    refine facts.ev.ModelProperties_slashableBetween_intro b.erase
      (facts.ev.named_row_erase_mem hcP hbP) a.erase (facts.ev.named_row_erase_mem hcF haF)
      ((namedAttestation_erase_val_index b).trans hbv)
      ((namedAttestation_erase_val_index a).trans hav) ?_
    exact facts.csAdded.matching_finality_e1 b a h₁ X.root T₁.root (hbv.trans hav.symm) hbm
      (by simpa only [hh₁, hFroot] using hap) hxr

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- After `i` steps, `u`'s store carries a body `D` whose replay finalizes the store's finalized
    block; if that replay's finalization height is not `0`, it is the chain-state height the store
    records for its own finalized block. -/
theorem recorded_eq_hF_of_carrier_l75 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (i : Nat) (u : V) :
    ∃ D : NamedBlock V, D ∈ (x[i][u].st).st.bodies ∧
      (M.derive_named S.E S.cfg D).F = (x[i][u].st).st.core.F ∧
      ((M.derive_named S.E S.cfg D).h_F ≠ 0 →
        ((x[i][u].st).st.core.σ (x[i][u].st).st.core.F).h
          = (M.derive_named S.E S.cfg D).h_F) := by
  classical
  obtain ⟨D, hDmem, hDF, -⟩ := Restated.finalization_carrier_sts facts S Sched x i u
  refine ⟨D, hDmem, hDF, fun hz => ?_⟩
  rcases facts.csAdded.finalized_is_entry S.E S.cfg D with hz' | ⟨Fn, hFnD, hFnerase, hFnh, -⟩
  · exact absurd hz' hz
  · have hco := (Restated.nodeInvariant_sts facts S Sched x i u).1.1.1
    have hFnMem : Fn ∈ (x[i][u].st).st.bodies := Restated.mem_bodies_of_preceq hco.2.2.1 hDmem hFnD
    obtain ⟨Fb, hFbMem, hFbe, hFbσ⟩ := Restated.finalized_body_of_store facts S Sched x i u
    have hFnFb : Fn = Fb := by
      refine hco.2.1 Fn hFnMem Fb hFbMem ?_
      rw [hFnerase, hDF, ← hFbe]
    rw [hFbσ, ← hFnFb]
    exact hFnh

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- With the adversary holding less than one third of the total weight at `tB`, a block finalized by
    a validator honest through its read at a time at or before `tB`, at a height less than that of a
    block another such validator holds, is an ancestor of that block. -/
theorem finalized_preceq_of_crossing_stores (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tB : Int)
    (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hthird : 3 * S.E.electorate.weightOf (Sched.adv tB) < S.E.electorate.totalWeight)
    {i j : Nat} (hi : (x[i].time : Int) ≤ tB) (hj : (x[j].time : Int) ≤ tB) {u w : V}
    (hu : Restated.HonestThrough M Sched x i u) (hw : Restated.HonestThrough M Sched x j w)
    {T : NamedBlock V} (hT : T ∈ (x[j][w].st).st.bodies)
    (hlt : ((x[i][u].st).st.core.σ (x[i][u].st).st.core.F).h
      < (M.derive_named S.E S.cfg T).h) :
    Block.Preceq (x[i][u].st).st.core.F T.erase := by
  classical
  obtain ⟨D, hDmem, hDF, hrec⟩ := Restated.recorded_eq_hF_of_carrier_l75 facts S Sched x i u
  by_cases hz : (M.derive_named S.E S.cfg D).h_F = 0
  · have hgen : (M.derive_named S.E S.cfg D).F = Block.genesis :=
      facts.cs.finalized_zero_is_genesis S.E S.cfg D hz
    rw [← hDF, hgen]
    exact (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _))
  · have hDlog : Restated.blockInLog M S Sched x D := Restated.blockInLog_of_mem_bodies facts S Sched hu hDmem
    have hTlog : Restated.blockInLog M S Sched x T := Restated.blockInLog_of_mem_bodies facts S Sched hw hT
    have hroot : RootInjectiveOnAncestors D.erase T.erase :=
      Restated.rootInjectiveOnAncestors_of_collisionFreeInLog facts S Sched x hexec.idealization D T hDlog hTlog
    rcases finalized_vs_crossing_slashable₇₅ facts S.E S.cfg hroot ⟨rfl, rfl⟩ hz
        (by rw [← hrec hz]; exact hlt) with hev | ⟨X, hXT, -, hXe⟩
    · exfalso
      have hDT : D.erase ∈ (x[i][u].st).st.core.T := by
        rw [Restated.bodies_image_eq_T facts S Sched x i u]; exact Finset.mem_image_of_mem _ hDmem
      have hTT : T.erase ∈ (x[j][w].st).st.core.T := by
        rw [Restated.bodies_image_eq_T facts S Sched x j w]; exact Finset.mem_image_of_mem _ hT
      exact Restated.noSlashableWeightBetween_stores_upTo facts S Sched x tB hmono
        hexec.toUnforgeability hthird hj hi w u
        (facts.ev.hasSlashableWeightBetween_mono hev
          (facts.ev.chain_attestations_subset_store hTT)
          (facts.ev.chain_attestations_subset_store hDT))
    · rw [← hDF, ← hXe]
      exact Proofs.NamedWire.erase_preceq hXT

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the theorem's hypotheses, for a regime `hreg` on `runAll M S Sched x v N`, read along
    `Restated.runAllPath M S Sched x v N` over the validators not held, with `n₀` the tick step at
    `S.a r` and `S.a r ≤ x[N].time ≤ tE`, every non-empty height vote at the checkpoint's own
    chain-state height, signed up to step `n₀ + 1` by a validator honest through its send, names the
    checkpoint: every block in play whose root is that vote's entry is an ancestor of `T`. -/
theorem targetsTop_atRound (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    {r : Round} {N : Nat}
    (hNlo : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int)) (hNhi : (x[N].time : Int) ≤ tE)
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r)))) :
    ∀ (v' : V) (n' : Nat) (b : NamedAttestation V) (entry : BlockId) (tmo : Bool),
      n' ≤ n₀ + 1 → Restated.HonestThrough M Sched x n' v' → b.val_index = v' →
      (⟨v', NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∈ x[n'].sent →
      b.height_pair = NamedHeightPair.vote (M.derive_named S.E S.cfg T).h entry tmo →
      ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = entry →
        Block.Preceq C.erase T.erase := by
  intro v' n' b entry tmo hn' hv' hidx hsent hpair C hC hCroot
  subst hidx
  have hn : (x[N].time : Int) ≤ tE := hNhi
  have hrWN : (Restated.Vocabulary.Execution.Setup.a M S (r)) ≤ (x[N].time : Int) := hNlo
  obtain ⟨hn₀1, hn₀0⟩ := Restated.tickStepAt_time facts x hn₀
  have hn₀N : n₀ + 1 ≤ N := by
    by_contra hcon
    have hle : ((x[N].time : Nat) : Int) ≤ ((x[n₀].time : Nat) : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (by omega)
    linarith
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hX : ∀ t : Int, 0 ≤ t → notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ _ => Finset.subset_univ _
  have hXXb : (Finset.univ : Finset V) ⊆ Finset.univ := Finset.Subset.refl _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  obtain ⟨-, hTheight'⟩ := hreg.checkpoint_runBlock facts hf hHsXb
  have hTheight : (M.derive_named S.E S.cfg T).h = blocked + 1 := hTheight'
  have hTlog : Restated.blockInLog M S Sched x T :=
    Restated.inPlay_at_switchRound_of_regime facts S Sched x v hmono hreg
  obtain ⟨k, hkn', τ, hlbl, haw, out, hout, hst, hmemout⟩ :=
    Restated.tick_of_honest_signed_upTo_taken facts S Sched x b.val_index (NamedObject.attest b)
      (x[n'].time : Int) hv' hvalid.toUnforgeability (by rw [author_attest]) n' le_rfl hsent
  have hkN : k < N := by omega
  have hP : Restated.Vocabulary.Execution.NamedRun.OnePath M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) := Restated.OnePath_runAllPath facts S Sched x v N
  have hemit : Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      b.val_index (Object.attest b) (τ : Int) :=
    Restated.emits_runAllPath_of_tick facts S Sched x v hkN hlbl haw hout hst hmemout
  have hτ : (τ : Int) = (Restated.Vocabulary.Execution.Setup.a M S b.round) :=
    (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts (Setup.alwaysAwake S) _ hP hemit).2
  have hb : b.val_index ∈ notHeldAt Sched (τ : Int) := by
    rw [mem_notHeldAt]; exact (Finset.mem_sdiff.mp haw).2
  have hbA : b.val_index ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S b.round)) := by rw [← hτ]; exact hb
  have hrow : b.height_pair.erase.height? = some (blocked + 1) := by
    rw [hpair, hTheight]; exact height?_erase_vote_l72 _ _ _
  have hab : a.round ≤ b.round := hreg.minimal b (τ : Int) hb hemit hrow
  have hbrW : b.round ≤ r := by
    have hk1 : ((x[k + 1].time : Nat) : Int) = (τ : Int) := by
      exact_mod_cast (Restated.tickAllAwake_time facts S Sched x hlbl).2
    have hle : ((x[k + 1].time : Nat) : Int) ≤ ((x[n₀ + 1].time : Nat) : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (by omega)
    apply (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).le_iff_le.mp
    rw [← hτ, ← hn₀1, ← hk1]
    exact hle
  have hk : Restated.tickStepAt M x k ((Restated.Vocabulary.Execution.Setup.a M S b.round)) := ⟨τ, hlbl, hτ⟩
  have hread := Restated.stateBeforeTime_runAll_tick facts S Sched x v hk
    (Nat.succ_le_of_lt hkN) b.val_index
  obtain ⟨nb, hnb⟩ := (p73% actionReadFrom_nonempty₇₃) facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index) b.round
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract nb.cache)
    (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node b.val_index)
    nb.st nb.record
  have hout' : M.tick (Setup.alwaysAwake S) b.val_index
      (Record.wakeStage M Sched (τ : Int) x[k] b.val_index)
      (Restated.Vocabulary.Execution.Setup.a M S b.round) ⇢ out := by
    rw [← hτ]; exact hout
  have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (k) b.val_index (↑τ)
  have _hv_s2 := Record.runs_as_wakeStage facts S Sched x (k) b.val_index (↑τ)
  have hall := Restated.attest_of_tick_eq facts S b.val_index _ b.round hout' hmemout
  rw [Restated.actionAttestationFrom_wakeStage facts, ← hread] at hall
  have hDb : b = D.2.2 := hall D.2.2 ⟨nb, hnb, D.1, D.2.1, hD⟩
  have hsorted := Restated.sorted_runAll_withHonest_events facts S Sched x v
    (notHeldAt Sched (x[N].time : Int)) N
  have hmemW := (p69b% mem_stateBeforeTime_along₆₉b) hsorted hP
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) b.round)
  obtain ⟨o, ho⟩ := (p63% actionFGSource_nonempty₆₃w) facts (Setup.alwaysAwake S) nb
  obtain ⟨Cfgb, rfl, hCfgh, hCfgroot⟩ :=
    Restated.source_of_actionAttestation_heightPair facts (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      b.val_index b.round (h₀ := blocked + 1) (entry := entry) (tmo := tmo) nb ⟨_, hmemW, hnb⟩ D hD
      (by rw [← hDb, hpair, hTheight]) o ho
  have hwit : Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M (Setup.alwaysAwake S)
      nb ⇢ some (nb.st.core.σ Cfgb).T_h :=
    ((p73% returns_map_iff₇₃) _ _ _).2 ⟨some Cfgb, ho, rfl⟩
  have hWT : Block.compatible (nb.st.core.σ Cfgb).T_h T.erase = true := by
    rcases Nat.lt_or_ge a.round b.round with hlt | hge
    · have hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) b.round) ≤
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
            Record.Run V).horizon := by
        show (Restated.Vocabulary.Execution.Setup.a M S b.round) ≤ (x[N].time : Int)
        exact (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbrW).trans hrWN
      exact ((hreg.laterHistory_main facts hf hHs hHsXb hX hXXb hcomOn hbelow
        (Nat.succ_le_of_lt hlt) hlo
        (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono
          hawake hn k hk u j hj)).2 hhor).2 b.val_index hbA nb hnb _ hwit
    · have hround : a.round = b.round := le_antisymm hab hge
      have hsame :=
        hreg.seed.confirmationWitness_of_sameRound_honestHeightRow_of_frame_named facts hf
          hHs hHsXb hX hXXb hreg.crossing hreg.frame hreg.ready hbA hemit hrow hround hlo
          nb hnb _ hwit
      rw [Option.some.inj hsame]
      exact Block.compatible_of_preceq_common (Block.preceq_self _) (Block.preceq_self _)
  have hCfgT : Cfgb ∈ (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index).st.core.T :=
    Restated.fgSource_mem_stateBeforeTime' facts (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      b.val_index b.round _ hmemW nb hnb ho
  have hσeq := (p73% actionReadFrom_σ₇₃) facts (Setup.alwaysAwake S) _ b.round nb hnb
  rw [hσeq] at hCfgh hCfgroot hWT
  rw [hread] at hCfgT hCfgroot hCfgh hWT
  have hco := (Restated.nodeInvariant_sts facts S Sched x k b.val_index).1.1.1
  rw [hco.1] at hCfgT
  obtain ⟨Cfgn, hCfgnMem, hCfgnErase⟩ := Finset.mem_image.mp hCfgT
  have hσ : (x[k][b.val_index].st).st.core.σ Cfgb = M.derive_named S.E S.cfg Cfgn := by
    have hd := hco.2.2.2.2 Cfgn hCfgnMem
    rw [hCfgnErase] at hd
    exact hd
  obtain ⟨En, hEnLe, hEnEr, hEnH⟩ :=
    facts.cs.entry_ancestor_same_height S.E S.cfg Cfgn
  have hEnSelf : (M.derive_named S.E S.cfg En).T_h = En.erase := by
    rw [facts.cs.entry_eq_on_plateau S.E S.cfg hEnLe hEnH]
    exact hEnEr.symm
  have hEnMem : En ∈ (x[k][b.val_index].st).st.bodies :=
    Restated.mem_bodies_of_preceq hco.2.2.1 hCfgnMem hEnLe
  have hhonk : Restated.HonestThrough M Sched x k b.val_index := by
    intro t ht
    exact hv' t (le_trans ht (Restated.time_mono_int facts S Sched x (le_of_lt hkn')))
  have hEnLog : Restated.blockInLog M S Sched x En := Restated.blockInLog_of_mem_bodies facts S Sched hhonk hEnMem
  have hEnRoot : En.root = C.root := by
    rw [← Proofs.NamedWire.erase_root En, hEnEr, ← hσ, hCfgroot]
    exact hCroot.symm
  have hEnC : En = C :=
    hvalid.idealization.root_injective En C hEnLog hC En C
      (Or.inl (Proofs.NamedAncestry.named_self En))
      (Or.inr (Proofs.NamedAncestry.named_self C)) hEnRoot
  have hEnh : (M.derive_named S.E S.cfg En).h = blocked + 1 := by
    rw [hEnH, ← hσ]
    exact hCfgh
  have hEnT : Block.compatible En.erase T.erase = true := by
    rw [hEnEr, ← hσ]
    exact hWT
  rw [hEnC] at hEnSelf hEnh hEnT
  exact Restated.preceq_of_entry_compatible_sts facts S Sched x hvalid.idealization hC hTlog hEnSelf hEnT
    (by rw [hEnh, hTheight])

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the theorem's hypotheses, for a regime `hreg` on `runAll M S Sched x v N`, read along
    `Restated.runAllPath M S Sched x v N` over the validators not held, with `n₀` the tick step at
    `S.a rW`, every non-empty height vote at the checkpoint's own chain-state height, signed up to
    step `n₀ + 1` by a validator honest through its send, names the checkpoint: every block in play
    whose root is that vote's entry is an ancestor of `T`. -/
theorem targetsTop_at_switchRound (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) :
    ∀ (v' : V) (n' : Nat) (b : NamedAttestation V) (entry : BlockId) (tmo : Bool),
      n' ≤ n₀ + 1 → Restated.HonestThrough M Sched x n' v' → b.val_index = v' →
      (⟨v', NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∈ x[n'].sent →
      b.height_pair = NamedHeightPair.vote (M.derive_named S.E S.cfg T).h entry tmo →
      ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = entry →
        Block.Preceq C.erase T.erase := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  exact Restated.targetsTop_atRound facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm hthird hcom
    (by rw [hN]; exact Restated.action_le_confirmation_third facts S _)
    (by rw [hN.trans hN'.symm]; exact hN'E) hreg hn₀

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- With monotone corruption, a valid execution, the adversary holding less than one third of the
    total weight at every time up to `tE`, and `x[n₀ + 1].time ≤ tE`, if `topHonestRow S Sched x n₀`
    is at most `T`'s chain-state height, then the chain-state height a validator honest through its
    own read records for its own finalized block, at any step up to `n₀ + 1`, is at most `T`'s. -/
theorem baseRecordedFinalizedHeightUnderAnchor_of_regime (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hmono : Sched.MonotoneCorruption)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) {tE : Int}
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    {n₀ : Nat} (hn₀E : (x[n₀ + 1].time : Int) ≤ tE) {T : NamedBlock V}
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h) :
    Restated.BaseRecordedFinalizedHeightUnderAnchor M S Sched x n₀ T := by
  intro v n' hn' hv
  have hn'E : (x[n'].time : Int) ≤ tE := (Restated.time_mono_int facts S Sched x hn').trans hn₀E
  rcases Restated.finalized_target_witness facts S Sched x hvalid hv with hgen | ⟨X, -, -, Q, hQ, hsign⟩
  · obtain ⟨Fb, -, hFbe, hFbσ⟩ := Restated.finalized_body_of_store facts S Sched x n' v
    rw [hFbσ]
    have hFbg : Fb = NamedBlock.genesis := by
      rw [hgen] at hFbe
      exact eq_named_genesis_of_erase_eq_genesis hFbe
    rw [hFbg]
    exact facts.cs.derive_height_mono S.E S.cfg (genesis_namedPreceq_l75 T)
  · obtain ⟨q, hqQ, hq⟩ := exists_nonAdv_of_quorum_upTo S Sched hmono (hthird tE le_rfl) hQ
    obtain ⟨carrier, a, tmo, hcarrier, ha, hval, hpair⟩ := hsign q hqQ
    have hqn' : Restated.HonestThrough M Sched x n' q := fun t ht => hq t (ht.trans hn'E)
    have hmem := Restated.carried_vote_in_log facts S Sched x hvalid hcarrier ha (by rw [hval]; exact hqn')
    rw [hval] at hmem
    exact (Restated.honestRow_le_topHonestRow facts S Sched x hvalid.toUnforgeability
      ⟨q, n', a, X.root, tmo, hn', hqn', hval, hmem, hpair⟩).trans htop

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the theorem's hypotheses, for a regime `hreg` on `runAll M S Sched x v N`, read along
    `Restated.runAllPath M S Sched x v N` over the validators not held, with `n₀` the tick step at
    `S.a r`, `S.a r ≤ x[N].time ≤ tE` and `topHonestRow S Sched x n₀` at most `T`'s height, whatever
    a validator honest through its own read has finalized, at any step up to `n₀ + 1`, is an
    ancestor of `T`. -/
theorem finalized_preceq_anchor_of_regime_atRound (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    {r : Round} {N : Nat}
    (hNlo : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int)) (hNhi : (x[N].time : Int) ≤ tE)
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h) :
    ∀ (v' : V) (n' : Nat), n' ≤ n₀ + 1 → Restated.HonestThrough M Sched x n' v' →
      Block.Preceq (x[n'][v'].st).st.core.F T.erase := by
  intro w n' hn' hw
  have hn : (x[N].time : Int) ≤ tE := hNhi
  have hrWN : (Restated.Vocabulary.Execution.Setup.a M S (r)) ≤ (x[N].time : Int) := hNlo
  obtain ⟨hn₀1, -⟩ := Restated.tickStepAt_time facts x hn₀
  have hn₀E : (x[n₀ + 1].time : Int) ≤ tE := by rw [hn₀1]; exact hrWN.trans hn
  have hn'E : (x[n'].time : Int) ≤ tE := (Restated.time_mono_int facts S Sched x hn').trans hn₀E
  have hle := Restated.baseRecordedFinalizedHeightUnderAnchor_of_regime facts S Sched x hmono hvalid hthird
    hn₀E htop w n' hn' hw
  rcases lt_or_eq_of_le hle with hlt | heq
  ·
    obtain ⟨k, hkN, hstore, hhon⟩ := Restated.seedStore_runAll_tick facts S Sched x v hmono hreg
    obtain ⟨na, hna⟩ := (p73% actionReadFrom_nonempty₇₃) facts (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round))) a.val_index) a.round
    have hCfg0 : Cfg ∈ (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round))) a.val_index).st.bodies := by
      rw [← (p73% actionReadFrom_bodies₇₃) facts (Setup.alwaysAwake S) _ a.round na hna]
      exact hreg.seed.sourceMem na hna
    rw [hstore] at hCfg0
    have hco := (Restated.nodeInvariant_sts facts S Sched x k a.val_index).1.1.1
    have hTk : T ∈ (x[k][a.val_index].st).st.bodies :=
      Restated.mem_bodies_of_preceq hco.2.2.1 hCfg0 hreg.checkpointPreceq
    have hkE : (x[k].time : Int) ≤ tE := (Restated.time_mono_int facts S Sched x hkN.le).trans hn
    exact Restated.finalized_preceq_of_crossing_stores facts S Sched x tE hmono hvalid (hthird tE le_rfl)
      hn'E hkE hw hhon hTk hlt
  ·
    rcases Restated.finalized_target_witness facts S Sched x hvalid hw with hgen | ⟨X, hXmem, hFX, Q, hQ, hsign⟩
    · rw [hgen]; exact preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _)
    · obtain ⟨q, hqQ, hq⟩ := exists_nonAdv_of_quorum_upTo S Sched hmono (hthird tE le_rfl) hQ
      obtain ⟨carrier, b, tmo, hcarrier, hb, hval, hpair⟩ := hsign q hqQ
      have hqn' : Restated.HonestThrough M Sched x n' q := fun t ht => hq t (ht.trans hn'E)
      have hmem := Restated.carried_vote_in_log facts S Sched x hvalid hcarrier hb (by rw [hval]; exact hqn')
      rw [hval] at hmem
      rw [heq] at hpair
      have hXT := Restated.targetsTop_atRound facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm
        hthird hcom hNlo hNhi hreg hn₀ q n' b X.root tmo hn' hqn' hval hmem hpair X
        (Restated.blockInLog_of_mem_bodies facts S Sched hw hXmem) rfl
      exact preceq_trans_Preceq hFX hXT

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the theorem's hypotheses, for a regime `hreg` on `runAll M S Sched x v N`, read along
    `Restated.runAllPath M S Sched x v N` over the validators not held, with `n₀` the tick step at
    `S.a r`, `S.a r ≤ x[N].time ≤ tE` and `topHonestRow S Sched x n₀` at most `T`'s height, whatever
    a validator honest through its own read has finalized, at any step up to `n₀ + 1`, lies on one
    chain with `T`. -/
theorem baseFinalizedCompatibleWithAnchor_of_regime_atRound (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    {r : Round} {N : Nat}
    (hNlo : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int)) (hNhi : (x[N].time : Int) ≤ tE)
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h) :
    Restated.BaseFinalizedCompatibleWithAnchor M S Sched x n₀ T := by
  intro w n' hn' hw
  have h := Restated.finalized_preceq_anchor_of_regime_atRound facts S Sched x v hsync hmono hawake hgst hcv
    hvalid hawm hthird hcom hNlo hNhi hreg hn₀ htop w n' hn' hw
  exact compatible_of_preceq_common_Preceq h (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- The clause `fin` at round `r`: under the theorem's hypotheses, for a regime `hreg` on
    `runAll M S Sched x v N`, read along `Restated.runAllPath M S Sched x v N` over the validators
    not held, with `n₀` the tick step at `S.a r`, `S.a r ≤ x[N].time ≤ tE` and
    `topHonestRow S Sched x n₀` at most `T`'s height, whatever a validator honest through its own
    read has finalized, at any step up to `n₀ + 1`, is an ancestor of `T`. -/
theorem fin_atRound_of_regime (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    {r : Round} {N : Nat}
    (hNlo : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int)) (hNhi : (x[N].time : Int) ≤ tE)
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h) :
    ∀ (v : V) (n' : Nat), n' ≤ n₀ + 1 → Restated.HonestThrough M Sched x n' v →
      Block.Preceq (x[n'][v].st).st.core.F T.erase := by
  obtain ⟨hn₀1, -⟩ := Restated.tickStepAt_time facts x hn₀
  have hn₀E : (x[n₀ + 1].time : Int) ≤ tE := by rw [hn₀1]; exact hNlo.trans hNhi
  exact Restated.fin_at_switchRound facts S Sched x hvalid (Restated.inPlay_at_switchRound_of_regime facts S Sched x v hmono hreg)
    (Restated.baseFinalizedCompatibleWithAnchor_of_regime_atRound facts S Sched x v hsync hmono hawake hgst hcv
      hvalid hawm hthird hcom hNlo hNhi hreg hn₀ htop)
    (Restated.baseRecordedFinalizedHeightUnderAnchor_of_regime facts S Sched x hmono hvalid hthird hn₀E htop)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- The clause `fin` at the switch round: under the theorem's hypotheses, for a regime `hreg` on
    `runAll M S Sched x v N`, read along `Restated.runAllPath M S Sched x v N` over the validators
    not held, with `n₀` the tick step at `S.a rW` and `topHonestRow S Sched x n₀` at most `T`'s
    height, whatever a validator honest through its own read has finalized, at any step up to
    `n₀ + 1`, is an ancestor of `T`. -/
theorem fin_at_switchRound_of_regime (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h) :
    ∀ (v : V) (n' : Nat), n' ≤ n₀ + 1 → Restated.HonestThrough M Sched x n' v →
      Block.Preceq (x[n'][v].st).st.core.F T.erase := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  exact Restated.fin_atRound_of_regime facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm hthird hcom
    (by rw [hN]; exact Restated.action_le_confirmation_third facts S _)
    (by rw [hN.trans hN'.symm]; exact hN'E) hreg hn₀ htop

end

end DecoupledConsensusModel.Sts.Restated
