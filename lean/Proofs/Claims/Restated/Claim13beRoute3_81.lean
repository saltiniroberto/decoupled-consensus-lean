import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13b
import Proofs.Claims.Restated.Claim13bDirection
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Claim13bStepAnchor
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bStepSGMove
import Proofs.Claims.Restated.Claim13beRoute3_15
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_73
import Proofs.Claims.Restated.Claim13beRoute3_74
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Claims.Spec2Claims.Claim13bStepSGMove
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_81
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Honest height votes at the switch round's tick and the checkpoint

A theorem over a model `M : Record.Model V` and its facts: in a regime along
`runAllPath M S Sched x v N`, every honest non-empty height vote first sent at the switch round's
tick step, at a height at most the checkpoint `T`'s, has an entry whose blocks in play are ancestors
of `T`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p73% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_73)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p74% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_74)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
open scoped DC
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

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE` and a
    source round at or before `rW`: every non-empty height vote absent from the sent log
    `x[n₀].sent` of the tick step `n₀` of `S.a rW`, signed up to step `n₀ + 1` by a validator honest
    through its send, at a height at most `T`'s, has every block in play whose root is the vote's
    entry an ancestor of `T`. -/
theorem targetsSince_at_switchRound (facts : Record.Facts M)
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
    (harW : a.round ≤ Restated.switchRound M S tE)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (hgrade1 : a.round = Restated.switchRound M S tE → ∀ v ∈ Restated.HonRound M S Sched (Restated.switchRound M S tE),
      ∀ p : Protocol.Phase,
        M.domain S.E S.hc (Restated.switchRound M S tE) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (Restated.switchRound M S tE) p) →
      ∀ B : Block V,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (Restated.switchRound M S tE)
          (M.early S.E S.hc (Restated.switchRound M S tE) p)
          (M.late S.E S.hc (Restated.switchRound M S tE) p) B ⇢ true →
      Block.compatible B T.erase = true)
    (hclear : a.round = Restated.switchRound M S tE → Restated.BaseClearFGSourceCompatibleWithAnchor M S Sched x tE n₀ T) :
    ∀ (v' : V) (n' : Nat) (b : NamedAttestation V) (h' : Height) (entry : BlockId)
        (tmo : Bool),
      n' ≤ n₀ + 1 → Restated.HonestThrough M Sched x n' v' → b.val_index = v' →
      (⟨v', NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∈ x[n'].sent →
      (⟨v', NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∉ x[n₀].sent →
      b.height_pair = NamedHeightPair.vote h' entry tmo →
      h' ≤ (M.derive_named S.E S.cfg T).h →
      ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = entry →
      Block.Preceq C.erase T.erase := by
  intro v' n' b h' entry tmo hn' hv' hidx hsent hnot hpair hh' C hC hCroot
  have _hr_0 : M.reachedNode (x[n₀][b.val_index].st) := Record.reachedNode_sts facts S Sched x n₀ b.val_index
  subst hidx
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hrWN : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (x[N].time : Int) := by
    rw [hN]; exact Restated.action_le_confirmation_third facts S _
  have hn₀N := Restated.succ_le_of_tick_switchRound_l74 facts S Sched x hn₀ hN
  obtain ⟨hn₀1, -⟩ := Restated.tickStepAt_time facts x hn₀
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
  have hTlog : Restated.blockInLog M S Sched x T := Restated.inPlay_at_switchRound_of_regime facts S Sched x v hmono hreg
  obtain ⟨k, hkn', τ, hlbl, haw, out, hout, hst, hmemout⟩ :=
    Restated.tick_of_honest_signed_upTo_taken facts S Sched x b.val_index (NamedObject.attest b)
      (x[n'].time : Int) hv' hvalid.toUnforgeability (by rw [author_attest]) n' le_rfl hsent
  have hkN : k < N := by omega
  have hsentk : (⟨b.val_index, NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent :=
    Restated.mem_sent_of_tick_of_state facts S Sched x hlbl haw
      (facts.nd.tick_send_eq_of_state (Setup.alwaysAwake S) b.val_index _ (τ : Int)) hout hst hmemout
  have hP : Restated.Vocabulary.Execution.NamedRun.OnePath M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) := Restated.OnePath_runAllPath facts S Sched x v N
  have hemit := Restated.emits_runAllPath_of_tick facts S Sched x v hkN hlbl haw hout hst
    hmemout
  obtain ⟨-, hτ0⟩ := Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts (Setup.alwaysAwake S)
    _ hP hemit
  have hτ : (τ : Int) = (Restated.Vocabulary.Execution.Setup.a M S b.round) := hτ0
  rw [hτ] at hout haw
  have hbA : b.val_index ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S b.round)) :=
    mem_notHeldAt.mpr (Finset.mem_sdiff.mp haw).2
  have hk : Restated.tickStepAt M x k ((Restated.Vocabulary.Execution.Setup.a M S b.round)) := ⟨τ, hlbl, hτ⟩
  obtain ⟨n, hnk⟩ := (p74% actionReadFrom_nonempty₇₄) facts (Setup.alwaysAwake S)
    (x[k][b.val_index].st) b.round
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract n.cache) (Setup.alwaysAwake S).E
    (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node b.val_index) n.st n.record
  have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (k) b.val_index (Restated.Vocabulary.Execution.Setup.a M S b.round)
  have _hv_s2 := Record.runs_as_wakeStage facts S Sched x (k) b.val_index (Restated.Vocabulary.Execution.Setup.a M S b.round)
  have hbD : b = D.2.2 :=
    Restated.attest_of_tick_eq facts S b.val_index _ b.round hout hmemout D.2.2
      (by rw [Restated.actionAttestationFrom_wakeStage facts (Setup.alwaysAwake S) Sched _ x[k]
            b.val_index b.round]
          exact ⟨n, hnk, D.1, D.2.1, hD⟩)
  have hkn₀ : k = n₀ := by
    have hge : n₀ ≤ k := by
      by_contra hlt
      exact hnot (Restated.mem_sent_of_le facts x (by omega) hsentk)
    omega
  have hbeq : b.round = Restated.switchRound M S tE := by
    have h1 := (Restated.tickStepAt_time facts x hk).1
    rw [hkn₀] at h1
    exact (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).injective (h1.symm.trans hn₀1)
  have hread : Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index = x[k][b.val_index].st :=
    Restated.stateBeforeTime_runAll_tick facts S Sched x v hk (Nat.succ_le_of_lt hkN) b.val_index
  have hsorted := Restated.sorted_runAll_withHonest_events facts S Sched x v
    (notHeldAt Sched (x[N].time : Int)) N
  have hmemW := (p74% mem_stateBeforeTime_along₇₄) hsorted hP
    (Restated.Vocabulary.Execution.Setup.a M S b.round)
  have hnW : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index) b.round := by
    rw [hread]; exact hnk
  have hnAt : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      b.val_index b.round := ⟨_, hmemW, hnW⟩
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache)
    (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing n.st.core)
    (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s)
  obtain ⟨o, ho'⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract n.cache)
    (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing n.st.core)
    (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) A2
  have ho : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) n ⇢ o :=
    ((p73% returns_bind_iff₇₃) _ _ _).2 ⟨A2, hA2, ho'⟩
  obtain ⟨Cfgb, hoCfg, hCfgh, hCfgroot'⟩ :=
    Restated.source_of_actionAttestation_heightPair facts (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      b.val_index b.round n hnAt D hD (by rw [← hbD]; exact hpair) o ho
  subst hoCfg
  have hσn : n.st.core.σ = (x[k][b.val_index].st).st.core.σ :=
    (p73% actionReadFrom_σ₇₃) facts (Setup.alwaysAwake S) _ b.round n hnk
  have hCfgh' : ((x[k][b.val_index].st).st.core.σ Cfgb).h = h' := by rw [← hσn]; exact hCfgh
  have hCfgT : Cfgb ∈ (x[k][b.val_index].st).st.core.T := by
    have hT := Restated.fgSource_mem_stateBeforeTime' facts (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      b.val_index b.round _ hmemW n hnW ho
    rw [hread] at hT
    exact hT
  have hco := (Restated.nodeInvariant_sts facts S Sched x k b.val_index).1.1.1
  rw [hσn] at hCfgroot'
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
    rw [← Proofs.NamedWire.erase_root En, hEnEr, ← hσ, hCfgroot']
    exact hCroot.symm
  have hEnC : En = C :=
    hvalid.idealization.root_injective En C hEnLog hC En C
      (Or.inl (Proofs.NamedAncestry.named_self En))
      (Or.inr (Proofs.NamedAncestry.named_self C)) hEnRoot
  have hEnh : (M.derive_named S.E S.cfg En).h = h' := by
    rw [hEnH, ← hσ]
    exact hCfgh'
  -- `En` is on one chain with `T`: two cases on the seed round
  have hEnT : Block.compatible En.erase T.erase = true := by
    rcases Nat.lt_or_ge a.round b.round with hlt | hge
    · -- case: a later round than the seed's
      have hwit : Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M (Setup.alwaysAwake S) n
          ⇢ some ((n.st.core.σ Cfgb).T_h) :=
        ((p73% returns_map_iff₇₃) _ _ _).2 ⟨some Cfgb, ho, rfl⟩
      have hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) b.round) ≤
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
            Record.Run V).horizon := by
        show (Restated.Vocabulary.Execution.Setup.a M S b.round) ≤ (x[N].time : Int)
        exact (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbeq.le).trans hrWN
      have hWT : Block.compatible ((n.st.core.σ Cfgb).T_h) T.erase = true :=
        ((hreg.laterHistory_main facts hf hHs hHsXb hX hXXb hcomOn hbelow
          (Nat.succ_le_of_lt hlt) hlo
          (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono
            hawake hn k hk u j hj)).2 hhor).2 b.val_index hbA n hnW _ hwit
      rw [hσn] at hWT
      rw [hEnEr, ← hσ]
      exact hWT
    · -- case: the seed round is the switch round
      have hseed : a.round = Restated.switchRound M S tE := le_antisymm harW (hbeq ▸ hge)
      obtain ⟨hwin, hswE⟩ := Restated.switchRound_window_in_phase facts S tGAT tE gap hgst hlen
      have hvadv : b.val_index ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) := by
        apply hv'
        rw [← hn₀1]
        exact Restated.time_mono_int facts S Sched x (by omega)
      have hq : b.val_index ∈ Restated.HonRound M S Sched (Restated.switchRound M S tE) :=
        Restated.nonAdv_mem_honRound facts S Sched tGAT tE _ hmono hawake hwin hswE hvadv
      have hnW' : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
          (x[n₀][b.val_index].st) (Restated.switchRound M S tE) := by
        rw [← hkn₀, ← hbeq]; exact hnk
      have hCfgbT : Block.compatible Cfgb T.erase = true := by
        rcases Restated.source_cases facts S (x[n₀][b.val_index].st) (Restated.switchRound M S tE) n hnW'
          Cfgb ho with hlc | hQ
        · exact hclear hseed _ hq n hnW' Cfgb ho hlc
        · have hne : Restated.switchRound M S tE ≠ 0 :=
            Restated.switchRound_ne_zero_of_cutBoundW facts S tGAT tE gap
              (Restated.hη_of_healingLengthη' facts S tGAT tE gap hgst hlen)
          obtain ⟨r, hr⟩ : ∃ r : Round, Restated.switchRound M S tE = r + 1 :=
            ⟨Restated.switchRound M S tE - 1, (Nat.sub_add_cancel (Nat.pos_of_ne_zero hne)).symm⟩
          have hn₀' : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := by rw [← hr]; exact hn₀
          have hg1 := hgrade1 hseed
          rw [hr] at hg1 hnW' hQ
          have hq' : b.val_index ∈ Restated.HonRound M S Sched (r + 1) := by rw [← hr]; exact hq
          have hg2 := Restated.frameG2Old_of_gradeOld facts S Sched x r n₀ T hn₀' hg1 _ hq'
            (M.readFrame n.cache (M.toHealing n.st.core) (r + 1)) ⟨n, hnW', rfl⟩
          obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
            (M.toHealing n.st.core) (r + 1)
          have hgQ : g.Q2 = some Cfgb := hQ g ((facts.nd.gradeContract_read _ _ _ _ _ _).1 hg)
          obtain ⟨o₂, ho₂⟩ := facts.gr.grade2Block_nonempty (M.toHealing n.st.core)
            (M.readFrame n.cache (M.toHealing n.st.core) (r + 1))
          have hgo : g.Q2 = o₂ :=
            facts.nd.ModelProperties_gradeContract_read_Q2 n.cache S.E S.hc (M.toHealing n.st.core)
              (r + 1) g hg o₂ ho₂
          exact facts.gr.Q2_compatible hg2 o₂ ho₂ (by rw [← hgo, hgQ])
      have hEnCfgb : Block.Preceq En.erase Cfgb := by
        rw [← hCfgnErase]
        exact Proofs.NamedWire.erase_preceq hEnLe
      exact Protocol.compatible_of_preceq_of_compatible hEnCfgb hCfgbT
  rw [hEnC] at hEnSelf hEnh hEnT
  exact Restated.preceq_of_entry_compatible_sts facts S Sched x hvalid.idealization hC hTlog hEnSelf hEnT
    (by rw [hEnh]; exact hh')

end

end DecoupledConsensusModel.Sts.Restated
