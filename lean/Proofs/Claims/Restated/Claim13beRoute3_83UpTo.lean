import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13b
import Proofs.Claims.Restated.Claim13bDirection
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bStepAnchor
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bStepSGMove
import Proofs.Claims.Restated.Claim13beRoute3_15
import Proofs.Claims.Restated.Claim13beRoute3_21
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_44UpTo
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_72UpTo
import Proofs.Claims.Restated.Claim13beRoute3_73
import Proofs.Claims.Restated.Claim13beRoute3_74UpTo
import Proofs.Claims.Restated.Claim13beRoute3_75UpTo
import Proofs.Claims.Restated.Claim13beRoute3_83
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
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
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
# Anchors from the deadline round to the switch round, with synchrony up to a bound

Each theorem here is the theorem of the same name without `_upTo`, stated over a model
`M : Record.Model V` and its facts, with synchrony assumed only up to a bound.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p72u% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_72UpTo)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p73% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_73)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p74% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_74)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open Framework.StsMultisetLog

/-- Synchrony from wake up to a bound `b'` gives synchrony from wake up to any earlier bound `b`. -/
private theorem syncBefore_mono₈₃u {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {b b' : Int} (hb : b ≤ b')
    (hs : Restated.SynchronyFromWakeBefore M S x b') : Restated.SynchronyFromWakeBefore M S x b :=
  fun k w sm hsend hle haw => hs k w sm hsend (le_trans hle hb) haw

end

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

/-- In a regime `hreg` along `runAllPath M S Sched x v N` with `S.a r ≤ x[N].time ≤ tE`, synchrony
    assumed only up to `x[N].time`, `r` from the deadline round to the switch round, and a source
    round at or before `r`: every non-empty height vote absent from the sent log of round `r`'s tick
    step `n₀`, signed up to step `n₀ + 1` by a validator honest through its send, at a height at
    most `T`'s, has every block in play whose root is the vote's entry an ancestor of `T`. -/
theorem targetsSince_atRound_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat} {N : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x (x[N].time : Int)) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    {r : Round} (hrD : Restated.deadlineRoundW M S tGAT gap ≤ r) (hrW : r ≤ Restated.switchRound M S tE)
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
    (harW : a.round ≤ r)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hgrade1 : a.round = r → ∀ v ∈ Restated.HonRound M S Sched r,
      ∀ p : Protocol.Phase,
        M.domain S.E S.hc r p ≤ (Restated.Vocabulary.Execution.Setup.a M S r) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc r p) →
      ∀ B : Block V,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG r
          (M.early S.E S.hc r p)
          (M.late S.E S.hc r p) B ⇢ true →
      Block.compatible B T.erase = true)
    (hclear : a.round = r → Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) :
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
  have hn : (x[N].time : Int) ≤ tE := hNhi
  have hrWN : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) := hNlo
  obtain ⟨hn₀1, hn₀0⟩ := Restated.tickStepAt_time facts x hn₀
  have hn₀N : n₀ + 1 ≤ N := by
    by_contra hcon
    have hle : ((x[N].time : Nat) : Int) ≤ ((x[n₀].time : Nat) : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (by omega)
    linarith
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N hsync hmono hawake hgst hcv hvalid
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
  obtain ⟨k, hkn', τ, hlbl, haw, hdvd, out, hout, hst, hmemout⟩ :=
    Restated.tick_of_honest_signed_upTo_taken facts S Sched x b.val_index (NamedObject.attest b)
      (x[n'].time : Int) hv' hvalid.toUnforgeability (by rw [author_attest]) n' le_rfl hsent
  have hkN : k < N := by omega
  have hsentk : (⟨b.val_index, NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent :=
    Restated.mem_sent_of_tick_of_state facts S Sched x hlbl haw hdvd
      (facts.nd.tick_send_eq_of_state (Setup.alwaysAwake S) b.val_index _ (τ : Int)) hout hst hmemout
  have hP : Restated.Vocabulary.Execution.NamedRun.OnePath M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) := Restated.OnePath_runAllPath facts S Sched x v N
  have hemit := Restated.emits_runAllPath_of_tick facts S Sched x v hkN hlbl haw hdvd hout hst
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
      (by
        rw [Restated.actionAttestationFrom_wakeStage facts _ Sched _ x[k] b.val_index b.round]
        exact ⟨n, hnk, D.1, D.2.1, hD⟩)
  have hkn₀ : k = n₀ := by
    have hge : n₀ ≤ k := by
      by_contra hlt
      exact hnot (Restated.mem_sent_of_le facts x (by omega) hsentk)
    omega
  have hbeq : b.round = r := by
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
    · -- case: the seed round is `r`
      have hseed : a.round = r := le_antisymm harW (hbeq ▸ hge)
      obtain ⟨hwin, hswE⟩ := Restated.window_in_phase_atRound facts S tGAT tE gap hgst hlen hrD hrW
      have hvadv : b.val_index ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)) := by
        apply hv'
        rw [← hn₀1]
        exact Restated.time_mono_int facts S Sched x (by omega)
      have hq : b.val_index ∈ Restated.HonRound M S Sched r :=
        Restated.nonAdv_mem_honRound facts S Sched tGAT tE _ hmono hawake hwin hswE hvadv
      have hnW' : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
          (x[n₀][b.val_index].st) r := by
        rw [← hkn₀, ← hbeq]; exact hnk
      have hCfgbT : Block.compatible Cfgb T.erase = true := by
        rcases Restated.source_cases facts S (x[n₀][b.val_index].st) r n hnW'
          Cfgb ho with hlc | hQ
        · exact hclear hseed _ hq n hnW' Cfgb ho hlc
        · have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
          obtain ⟨r', hr⟩ : ∃ r' : Round, r = r' + 1 :=
            ⟨r - 1, (Nat.sub_add_cancel (hapos.trans_le harW)).symm⟩
          have hn₀' : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r' + 1))) := by rw [← hr]; exact hn₀
          have hg1 := hgrade1 hseed
          rw [hr] at hg1 hnW' hQ
          have hq' : b.val_index ∈ Restated.HonRound M S Sched (r' + 1) := by rw [← hr]; exact hq
          have hg2 := Restated.frameG2Old_of_gradeOld facts S Sched x r' n₀ T hn₀' hg1 _ hq'
            (M.readFrame n.cache (M.toHealing n.st.core) (r' + 1)) ⟨n, hnW', rfl⟩
          obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
            (M.toHealing n.st.core) (r' + 1)
          have hgQ : g.Q2 = some Cfgb := hQ g ((facts.nd.gradeContract_read _ _ _ _ _ _).1 hg)
          obtain ⟨o₂, ho₂⟩ := facts.gr.grade2Block_nonempty (M.toHealing n.st.core)
            (M.readFrame n.cache (M.toHealing n.st.core) (r' + 1))
          have hgo : g.Q2 = o₂ :=
            facts.nd.ModelProperties_gradeContract_read_Q2 n.cache S.E S.hc (M.toHealing n.st.core)
              (r' + 1) g hg o₂ ho₂
          exact facts.gr.Q2_compatible hg2 o₂ ho₂ (by rw [← hgo, hgQ])
      have hEnCfgb : Block.Preceq En.erase Cfgb := by
        rw [← hCfgnErase]
        exact Proofs.NamedWire.erase_preceq hEnLe
      exact Protocol.compatible_of_preceq_of_compatible hEnCfgb hCfgbT
  rw [hEnC] at hEnSelf hEnh hEnT
  exact Restated.preceq_of_entry_compatible_sts facts S Sched x hvalid.idealization hC hTlog hEnSelf hEnT
    (by rw [hEnh]; exact hh')

/-- In a regime `hreg` along `runAllPath M S Sched x v N` whose source round is at or before `r`,
    with `n₀` the tick step at `S.a r`, `x[N].time ≤ tE` and synchrony assumed only up to
    `x[N].time`: the seed attestation is in the sent log one step after a tick step `k ≤ n₀` at its
    round's action instant, its signer is honest through `k + 1`, and its height pair is a vote at
    `h(T)` whose entry is `T`'s root. -/
theorem seedRow_of_regime_atRound_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {N : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x (x[N].time : Int)) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    {r : Round} (hNhi : (x[N].time : Int) ≤ tE)
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ r) {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r))) :
    ∃ (k : Nat) (entry : BlockId) (tmo : Bool),
      k ≤ n₀ ∧ Restated.tickStepAt M x k ((Restated.Vocabulary.Execution.Setup.a M S a.round)) ∧ Restated.HonestThrough M Sched x (k + 1) a.val_index ∧
      (⟨a.val_index, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent ∧
      a.height_pair = NamedHeightPair.vote (M.derive_named S.E S.cfg T).h entry tmo ∧
      entry = T.root := by
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hNhi
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  obtain ⟨-, hTheight'⟩ := hreg.checkpoint_runBlock facts hf hHsXb
  have hTheight : (M.derive_named S.E S.cfg T).h = blocked + 1 := hTheight'
  obtain ⟨k, -, hk, hsent⟩ := Restated.mem_sent_of_emits_runAll facts S Sched x v hreg.seed.emitted
  have hta : ta = (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round) := hreg.seed.actionTime_eq
  have hk' : Restated.tickStepAt M x k ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
    have h := hk
    rw [hta] at h
    exact h
  obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hk'
  obtain ⟨hn1, -⟩ := Restated.tickStepAt_time facts x hn₀
  have hle : (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := Restated.Vocabulary.Proofs.Assembly.a_mono facts S harW
  have hkn : k ≤ n₀ := by
    by_contra hcon
    have hmn : ((x[n₀ + 1].time : Nat) : Int) ≤ ((x[k].time : Nat) : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (by omega)
    linarith
  have hsig : a.val_index ∈ notHeldAt Sched ta := hreg.seed.signerHonest
  have hk1' : (x[k + 1].time : Int) = ta := by rw [hta]; exact hk1
  have hsig' : a.val_index ∈ notHeldAt Sched (x[k + 1].time : Int) := by rw [hk1']; exact hsig
  have hhon : Restated.HonestThrough M Sched x (k + 1) a.val_index :=
    Restated.honestThrough_of_mem_notHeld facts S Sched x (k + 1) hmono _ hsig'
  have hh : a.height_pair.erase.height? = some (blocked + 1) := by
    rcases hreg.seed.targetOrTimeout with h | h <;> rw [h] <;> rfl
  obtain ⟨entry, tmo, hpair⟩ := heightPair_vote_of_height_l72 hh
  have hP : Restated.Vocabulary.Execution.NamedRun.OnePath M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) := Restated.OnePath_runAllPath facts S Sched x v N
  have hsorted := Restated.sorted_runAll_withHonest_events facts S Sched x v
    (notHeldAt Sched (x[N].time : Int)) N
  have hmemW := (p74% mem_stateBeforeTime_along₇₄) hsorted hP
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round)
  obtain ⟨n, hn⟩ := (p74% actionReadFrom_nonempty₇₄) facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round)) a.val_index) a.round
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract n.cache) (Setup.alwaysAwake S).E
    (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node a.val_index) n.st n.record
  have haD : a = D.2.2 := hreg.seed.exactAction n hn D hD
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache)
    (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing n.st.core)
    (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s)
  obtain ⟨o, ho'⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract n.cache)
    (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing n.st.core)
    (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) A2
  have ho : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) n ⇢ o :=
    ((p73% returns_bind_iff₇₃) _ _ _).2 ⟨A2, hA2, ho'⟩
  have hnAt : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      a.val_index a.round := ⟨_, hmemW, hn⟩
  obtain ⟨Cfgb, hoCfg, -, hCfgroot⟩ :=
    Restated.source_of_actionAttestation_heightPair facts (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      a.val_index a.round n hnAt D hD (by rw [← haD]; exact hpair) o ho
  have hCfgb : Cfgb = Cfg.erase :=
    Option.some.inj (hoCfg.symm.trans (hreg.seed.exactFGSource n hn o ho))
  have hroot : entry = T.root := by
    rw [← hCfgroot, hCfgb, ← Proofs.NamedWire.erase_root T]
    exact (congrArg Block.root (hreg.seed.checkpointStored n hn)).symm
  refine ⟨k, entry, tmo, hkn, hk', hhon, hsent, ?_, hroot⟩
  rw [hTheight]; exact hpair

end

/-! ## Round-`r` anchors, with the premises as section variables -/

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

variable (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
  (x : AtomicExec (Record.protocolOf M S) Sched)
  {tGAT tE : Int}
  (hsync : Restated.SynchronyFromWakeBefore M S x tE) (hmono : Sched.MonotoneCorruption)
  (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
  (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
  (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
  (hawm : AwakeAtMultiples S Sched)
  (hthird : ∀ t : Int, t ≤ tE →
    3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
include facts hsync hmono hawake hgst hcv hvalid hawm hthird

/-- With synchrony up to `tE`, every round `r` from the deadline round to the switch round has a
    round-`r` anchor. -/
private theorem exists_anchor₈₃u {gap : Nat}
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {r : Round} (hrD : Restated.deadlineRoundW M S tGAT gap ≤ r)
    (hrW : r ≤ Restated.switchRound M S tE) :
    ∃ T : NamedBlock V, Restated.AnchorAtRound M S Sched x tGAT tE r T := by
  obtain ⟨n₀, hn₀⟩ := Restated.exists_tickStepAt facts x htd (Restated.action_pos facts S r)
  obtain ⟨hn₀1, -⟩ := Restated.tickStepAt_time facts x hn₀
  obtain ⟨v, -⟩ := exists_not_adv_l76 S Sched (hthird tE le_rfl)
  obtain ⟨-, hrE⟩ := Restated.window_in_phase_atRound facts S tGAT tE gap hgst hlen hrD hrW
  have hNlo : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[n₀ + 1].time : Int) := le_of_eq hn₀1.symm
  have hNhi : (x[n₀ + 1].time : Int) ≤ tE := by rw [hn₀1]; exact hrE
  obtain ⟨blocked, first, i, a, ta, Cfg, T, Tprev, c0, hreg, harW, -, htop, -⟩ :=
    Restated.switchRoundRegime_runAll_notHeld_atRound_upTo facts S Sched x v
      (syncBefore_mono₈₃u hNhi hsync) hmono hawake hgst hcv
      hvalid hawm hthird hcom hrec hrD hn₀ hNlo hNhi
  exact ⟨T, v, n₀ + 1, n₀, blocked, first, i, a, ta, Cfg, Tprev, c0, hn₀, hNlo, hNhi, hreg, harW,
    htop⟩

/-- With synchrony up to `tE`, if `T` is a round-`r` anchor and `n₀` the tick step at `S.a r`, then
    `h(T) = topHonestRow M S Sched x n₀`. -/
private theorem anchor_height₈₃u {r : Round} {T : NamedBlock V}
    (hA : Restated.AnchorAtRound M S Sched x tGAT tE r T) {n₀ : Nat}
    (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r))) :
    (M.derive_named S.E S.cfg T).h = Restated.topHonestRow M S Sched x n₀ := by
  obtain ⟨v, N, n₁, blocked, first, i, a, ta, Cfg, Tprev, c0, hn₁, -, hNhi, hreg, harW, htop⟩ := hA
  have hnn : n₁ = n₀ := Restated.tickStepAt_unique facts x hn₁ hn₀
  rw [hnn] at htop
  obtain ⟨k, entry, tmo, hkn, -, hhon, hsent, hpair, -⟩ :=
    Restated.seedRow_of_regime_atRound_upTo facts S Sched x v (syncBefore_mono₈₃u hNhi hsync)
      hmono hawake hgst hcv hvalid hawm hthird hNhi hreg harW hn₀
  have hrow := Restated.honestRow_le_topHonestRow facts S Sched x hvalid.toUnforgeability (n₀ := n₀)
    ⟨a.val_index, k + 1, a, entry, tmo, by omega, hhon, rfl, hsent, hpair⟩
  exact le_antisymm hrow htop

/-- With synchrony up to `tE`, any two round-`r` anchors have the same erasure. -/
private theorem anchor_erase_eq₈₃u
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    {r : Round} {T T' : NamedBlock V} (hA : Restated.AnchorAtRound M S Sched x tGAT tE r T)
    (hA' : Restated.AnchorAtRound M S Sched x tGAT tE r T') :
    T.erase = T'.erase := by
  obtain ⟨v, N, n₀, blocked, first, i, a, ta, Cfg, Tprev, c0, hn₀, hNlo, hNhi, hreg, harW, -⟩ :=
    id hA
  obtain ⟨v', N', n₀', blocked', first', i', a', ta', Cfg', Tprev', c0', hn₀', -, hNhi', hreg',
    harW', -⟩ := id hA'
  have hTh := anchor_height₈₃u facts S Sched x hsync hmono hawake hgst hcv hvalid hawm hthird
    hA hn₀
  have hTh' := anchor_height₈₃u facts S Sched x hsync hmono hawake hgst hcv hvalid hawm hthird
    hA' hn₀
  have hheq : (M.derive_named S.E S.cfg T').h = (M.derive_named S.E S.cfg T).h :=
    hTh'.trans hTh.symm
  obtain ⟨k, entry, tmo, hkn, -, hhon, hsent, hpair, hentry⟩ :=
    Restated.seedRow_of_regime_atRound_upTo facts S Sched x v' (syncBefore_mono₈₃u hNhi' hsync)
      hmono hawake hgst hcv hvalid hawm hthird hNhi' hreg' harW' hn₀
  rw [hheq] at hpair
  have hT'log : Restated.blockInLog M S Sched x T' :=
    Restated.inPlay_at_switchRound_of_regime facts S Sched x v' hmono hreg'
  have hTlog : Restated.blockInLog M S Sched x T :=
    Restated.inPlay_at_switchRound_of_regime facts S Sched x v hmono hreg
  have hT'T : Block.Preceq T'.erase T.erase :=
    Restated.targetsTop_atRound_upTo facts S Sched x v (syncBefore_mono₈₃u hNhi hsync) hmono hawake
      hgst hcv hvalid hawm hthird hcom
      hNlo hNhi hreg hn₀ a'.val_index (k + 1) a' entry tmo (by omega) hhon rfl hsent hpair T'
      hT'log hentry.symm
  have hTself := Restated.anchorEntry_at_switchRound_of_regime facts S Sched x v hmono hvalid hreg
  have hTT' : Block.Preceq T.erase T'.erase :=
    Restated.preceq_of_entry_compatible_sts facts S Sched x hvalid.idealization hTlog hT'log hTself
      (compatible_of_preceq_common_Preceq (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hT'T)
      (le_of_eq hheq.symm)
  exact Block.preceq_antisymm (preceq_eq_true_iff_Preceq.mpr hTT') (preceq_eq_true_iff_Preceq.mpr hT'T)

/-- With synchrony up to `tE`, for `r` at or after the deadline round, every round-`r` anchor is an
    ancestor of every round-`(r + 1)` anchor. -/
private theorem anchor_preceq_succ₈₃u {gap : Nat}
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    {r : Round} (hrD : Restated.deadlineRoundW M S tGAT gap ≤ r) {T T' : NamedBlock V}
    (hA : Restated.AnchorAtRound M S Sched x tGAT tE r T)
    (hA' : Restated.AnchorAtRound M S Sched x tGAT tE (r + 1) T') :
    Block.Preceq T.erase T'.erase := by
  obtain ⟨v, N, n₀, blocked, first, i, a, ta, Cfg, Tprev, c0, hn₀, hNlo, hNhi, hreg, harW, -⟩ :=
    id hA
  obtain ⟨v', N', n₁, blocked', first', i', a', ta', Cfg', Tprev', c0', hn₁, hNlo', hNhi', hreg',
    harW', htop'⟩ := id hA'
  have hunf := hvalid.toUnforgeability
  have hTh := anchor_height₈₃u facts S Sched x hsync hmono hawake hgst hcv hvalid hawm hthird
    hA hn₀
  obtain ⟨hn₀1, hn₀0⟩ := Restated.tickStepAt_time facts x hn₀
  obtain ⟨hn₁1, hn₁0⟩ := Restated.tickStepAt_time facts x hn₁
  have hsucc : (Restated.Vocabulary.Execution.Setup.a M S r) < (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S) (Nat.lt_succ_self r)
  have hn₀n₁ : n₀ ≤ n₁ := by
    by_contra hcon
    have hle : ((x[n₁ + 1].time : Nat) : Int) ≤ ((x[n₀].time : Nat) : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (by omega)
    linarith
  have hTT'h : (M.derive_named S.E S.cfg T).h ≤ (M.derive_named S.E S.cfg T').h := by
    rw [hTh]; exact (Restated.topHonestRow_mono facts S Sched x hunf hn₀n₁).trans htop'
  have hTlog : Restated.blockInLog M S Sched x T :=
    Restated.inPlay_at_switchRound_of_regime facts S Sched x v hmono hreg
  have hT'log : Restated.blockInLog M S Sched x T' :=
    Restated.inPlay_at_switchRound_of_regime facts S Sched x v' hmono hreg'
  have hTself := Restated.anchorEntry_at_switchRound_of_regime facts S Sched x v hmono hvalid hreg
  rcases lt_or_eq_of_le hTT'h with hlt | heq
  · -- case: a larger height
    obtain ⟨k', entry', tmo', hk'n, hk', hhon', hsent', hpair', -⟩ :=
      Restated.seedRow_of_regime_atRound_upTo facts S Sched x v' (syncBefore_mono₈₃u hNhi' hsync)
        hmono hawake hgst hcv hvalid hawm hthird hNhi' hreg' harW' hn₁
    have ha' : a'.round = r + 1 := by
      rcases Nat.lt_or_ge r a'.round with hgt | hle
      · exact le_antisymm harW' (Nat.succ_le_of_lt hgt)
      · exfalso
        obtain ⟨hk'1, -⟩ := Restated.tickStepAt_time facts x hk'
        have hk'n₀ : k' ≤ n₀ := by
          by_contra hcon
          have hmn : ((x[n₀ + 1].time : Nat) : Int) ≤ ((x[k'].time : Nat) : Int) := by
            exact_mod_cast Restated.time_mono facts S Sched x (by omega)
          have := Restated.Vocabulary.Proofs.Assembly.a_mono facts S hle
          obtain ⟨-, hk'0⟩ := Restated.tickStepAt_time facts x hk'
          linarith
        have hrow := Restated.honestRow_le_topHonestRow facts S Sched x hunf (n₀ := n₀)
          ⟨a'.val_index, k' + 1, a', entry', tmo', by omega, hhon', rfl, hsent', hpair'⟩
        rw [← hTh] at hrow
        exact absurd hlt (not_lt.mpr hrow)
    have hNloR : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N'].time : Int) := hsucc.le.trans hNlo'
    obtain ⟨blocked'', first'', i'', a'', ta'', Cfg'', T'', Tprev'', c0'', hreg'', ha''r, -,
      htop'', -⟩ :=
      Restated.switchRoundRegime_runAll_notHeld_atRound_upTo facts S Sched x v'
        (syncBefore_mono₈₃u hNhi' hsync) hmono hawake hgst hcv
        hvalid hawm hthird hcom hrec hrD hn₀ hNloR hNhi'
    have hA'' : Restated.AnchorAtRound M S Sched x tGAT tE r T'' :=
      ⟨v', N', n₀, blocked'', first'', i'', a'', ta'', Cfg'', Tprev'', c0'', hn₀, hNloR, hNhi',
        hreg'', ha''r, htop''⟩
    have hTT'' : T.erase = T''.erase :=
      anchor_erase_eq₈₃u facts S Sched x hsync hmono hawake hgst hcv hvalid hawm hthird
        hcom hA hA''
    have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v' N'
      (syncBefore_mono₈₃u hNhi' hsync) hmono hawake hgst hcv
      hvalid hawm hthird hNhi'
    have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
      fun _ _ h => notHeldAt_anti hmono h
    have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
      fun _ => Finset.subset_univ _
    have hX : ∀ t : Int, 0 ≤ t → notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
      fun _ _ => Finset.subset_univ _
    have hXXb : (Finset.univ : Finset V) ⊆ Finset.univ := Finset.Subset.refl _
    have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
    have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v' N' hthird hNhi'
    obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
    have hlo := hreg''.lo_le_opening_l71 facts hf hloOpen
    have hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a'.round) ≤
        ({ Restated.runAll M S Sched x v' N' with honest := notHeldAt Sched (x[N'].time : Int) } :
          Record.Run V).horizon := by
      show (Restated.Vocabulary.Execution.Setup.a M S a'.round) ≤ (x[N'].time : Int)
      rw [ha']; exact hNlo'
    obtain ⟨n, hn⟩ := (p74% actionReadFrom_nonempty₇₄) facts (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v' N'
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v' N' with honest := notHeldAt Sched (x[N'].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a'.round)) a'.val_index) a'.round
    obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache)
      (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing n.st.core)
      (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s)
    obtain ⟨o, ho'⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract n.cache)
      (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing n.st.core)
      (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) A2
    have ho : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) n ⇢ o :=
      ((p73% returns_bind_iff₇₃) _ _ _).2 ⟨A2, hA2, ho'⟩
    have hoE : o = some Cfg'.erase := hreg'.seed.exactFGSource n hn o ho
    subst hoE
    have hwit0 : Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M (Setup.alwaysAwake S) n
        ⇢ some ((n.st.core.σ Cfg'.erase).T_h) :=
      ((p73% returns_map_iff₇₃) _ _ _).2 ⟨some Cfg'.erase, ho, rfl⟩
    have hwit : Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M (Setup.alwaysAwake S) n
        ⇢ some T'.erase := by
      rw [hreg'.seed.checkpointStored n hn]; exact hwit0
    have hsig : a'.val_index ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S a'.round)) := by
      have h := hreg'.seed.signerHonest
      rw [hreg'.seed.actionTime_eq] at h
      exact h
    have hcomp : Block.compatible T'.erase T''.erase = true :=
      ((hreg''.laterHistory_main facts hf hHs hHsXb hX hXXb hcomOn hbelow
        (c := a'.round) (by rw [ha']; exact Nat.succ_le_succ ha''r) hlo
        (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v' N' hmono
          hawake hNhi' k hk u j hj)).2 hhor).2 a'.val_index hsig n hn _ hwit
    rw [← hTT''] at hcomp
    exact Restated.preceq_of_entry_compatible_sts facts S Sched x hvalid.idealization hTlog hT'log hTself
      (Protocol.compatible_comm hcomp) hTT'h
  · -- case: equal heights
    obtain ⟨k, entry, tmo, hkn, -, hhon, hsent, hpair, hentry⟩ :=
      Restated.seedRow_of_regime_atRound_upTo facts S Sched x v (syncBefore_mono₈₃u hNhi hsync)
        hmono hawake hgst hcv hvalid hawm hthird hNhi hreg harW hn₀
    rw [heq] at hpair
    exact Restated.targetsTop_atRound_upTo facts S Sched x v' (syncBefore_mono₈₃u hNhi' hsync) hmono
      hawake hgst hcv hvalid hawm hthird hcom
      hNlo' hNhi' hreg' hn₁ a.val_index (k + 1) a entry tmo (by omega) hhon rfl hsent hpair T
      hTlog hentry.symm

/-- With synchrony up to `tE`, for rounds `r ≤ r'` from the deadline round to the switch round,
    every round-`r` anchor is an ancestor of every round-`r'` anchor. -/
private theorem anchor_preceq_of_le₈₃u {gap : Nat}
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {r r' : Round} (hrD : Restated.deadlineRoundW M S tGAT gap ≤ r) (hrr' : r ≤ r')
    (hr'W : r' ≤ Restated.switchRound M S tE) {T T' : NamedBlock V}
    (hA : Restated.AnchorAtRound M S Sched x tGAT tE r T)
    (hA' : Restated.AnchorAtRound M S Sched x tGAT tE r' T') :
    Block.Preceq T.erase T'.erase := by
  induction r', hrr' using Nat.le_induction generalizing T' with
  | base =>
    rw [anchor_erase_eq₈₃u facts S Sched x hsync hmono hawake hgst hcv hvalid hawm hthird
      hcom hA hA']
    exact (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
  | succ r'' hrr'' ih =>
    have hr''W : r'' ≤ Restated.switchRound M S tE := (Nat.le_succ r'').trans hr'W
    obtain ⟨T'', hA''⟩ := exists_anchor₈₃u facts S Sched x hsync hmono hawake hgst hcv hvalid
      hawm hthird hcom hrec hlen htd (hrD.trans hrr'') hr''W
    exact preceq_trans_Preceq (ih hr''W hA'')
      (anchor_preceq_succ₈₃u facts S Sched x hsync hmono hawake hgst hcv hvalid hawm hthird
        hcom hrec (hrD.trans hrr'') hA'' hA')

/-- With synchrony up to `tE`, given `hprev` and `hclear` at round `r`, for a round-`r` anchor `T`,
    every non-empty height vote first sent at round `r`'s tick step, signed up to that step plus one
    by a validator honest through its send, at a height at most `T`'s, names a block on `T`'s chain. -/
private theorem targetsSince_of_anchor₈₃u {gap : Nat}
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    {r : Round} (hrD : Restated.deadlineRoundW M S tGAT gap ≤ r) (hrW : r ≤ Restated.switchRound M S tE)
    (hprev : ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    {T : NamedBlock V} (hA : Restated.AnchorAtRound M S Sched x tGAT tE r T) :
      ∀ n₀ : Nat, Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      ∀ (v' : V) (n' : Nat) (a : NamedAttestation V) (h' : Height) (entry : BlockId)
        (tmo : Bool),
        n' ≤ n₀ + 1 → Restated.HonestThrough M Sched x n' v' → a.val_index = v' →
        (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n'].sent →
        (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x[n₀].sent →
        a.height_pair = NamedHeightPair.vote h' entry tmo →
        h' ≤ (M.derive_named S.E S.cfg T).h →
        ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = entry →
        Block.Preceq C.erase T.erase := by
  intro n₀ hn₀
  obtain ⟨v, N, n₁, blocked, first, i, a, ta, Cfg, Tprev, c0, hn₁, hNlo, hNhi, hreg, harW, htop⟩ :=
    hA
  have hnn : n₁ = n₀ := Restated.tickStepAt_unique facts x hn₁ hn₀
  rw [hnn] at htop
  have hP := Restated.OnePath_runAllPath facts S Sched x v N
  have hsyncN := syncBefore_mono₈₃u hNhi hsync
  have hfin := Restated.fin_atRound_of_regime_upTo facts S Sched x v hsyncN hmono hawake hgst hcv hvalid hawm hthird
    hcom hNlo hNhi hreg hn₀ htop
  have hg1 := Restated.grade1_atRound_upTo facts S Sched x v hsyncN hmono hawake hgst hcv hvalid hawm hthird hcom hNlo
    hNhi hreg harW hn₀ hfin (fun heq => hprev v N blocked first i a ta Cfg T Tprev c0 hNlo hNhi hreg
      heq)
  exact Restated.targetsSince_atRound_upTo facts S Sched x v hsyncN hmono hawake hgst hcv hvalid hawm hthird hcom hlen
    hrD hrW hNlo hNhi hreg harW hn₀ (fun _ => hg1)
    (fun heq => hclear v N blocked first i a ta Cfg T Tprev c0 n₀ hNlo hNhi hreg heq hn₀)

end

/-! ## Round-`r` anchors -/

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

/-- With synchrony assumed only up to `tE`, every round `r` from the deadline round to the switch
    round has a round-`r` anchor (`AnchorAtRound`). -/
theorem exists_anchorAtRound_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x tE) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {r : Round} (hrD : Restated.deadlineRoundW M S tGAT gap ≤ r) (hrW : r ≤ Restated.switchRound M S tE) :
    ∃ T : NamedBlock V, Restated.AnchorAtRound M S Sched x tGAT tE r T :=
  exists_anchor₈₃u facts S Sched x hsync hmono hawake hgst hcv hvalid hawm hthird
    hcom hrec hlen htd hrD hrW

/-- With synchrony assumed only up to `tE`, if `T` is a round-`r` anchor and `n₀` the tick step at
    `S.a r`, then `h(T) = topHonestRow M S Sched x n₀`. -/
theorem anchorAtRound_height_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {tGAT tE : Int}
    (hsync : Restated.SynchronyFromWakeBefore M S x tE) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    {r : Round} {T : NamedBlock V} (hA : Restated.AnchorAtRound M S Sched x tGAT tE r T)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r))) :
    (M.derive_named S.E S.cfg T).h = Restated.topHonestRow M S Sched x n₀ :=
  anchor_height₈₃u facts S Sched x hsync hmono hawake hgst hcv hvalid hawm hthird hA hn₀

/-- With synchrony assumed only up to `tE`, for rounds `r ≤ r'` from the deadline round to the
    switch round, every round-`r` anchor is an ancestor of every round-`r'` anchor. -/
theorem anchorAtRound_preceq_of_le_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x tE) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {r r' : Round} (hrD : Restated.deadlineRoundW M S tGAT gap ≤ r) (hrr' : r ≤ r')
    (hr'W : r' ≤ Restated.switchRound M S tE) {T T' : NamedBlock V}
    (hA : Restated.AnchorAtRound M S Sched x tGAT tE r T) (hA' : Restated.AnchorAtRound M S Sched x tGAT tE r' T') :
    Block.Preceq T.erase T'.erase :=
  anchor_preceq_of_le₈₃u facts S Sched x hsync hmono hawake hgst hcv hvalid hawm hthird
    hcom hrec hlen htd hrD hrr' hr'W hA hA'

/-- With synchrony assumed only up to `tE`, given `hprev` and `hclear` at round `r`, for a round `r`
    from the deadline round to the switch round and a round-`r` anchor `T`, every non-empty height
    vote first sent at round `r`'s tick step, signed up to that step plus one by a validator honest
    through its send, at a height at most `T`'s, has every block in play whose root is the vote's
    entry an ancestor of `T`. -/
theorem targetsSince_of_anchorAtRound_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x tE) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    {r : Round} (hrD : Restated.deadlineRoundW M S tGAT gap ≤ r) (hrW : r ≤ Restated.switchRound M S tE)
    (hprev : ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    {T : NamedBlock V} (hA : Restated.AnchorAtRound M S Sched x tGAT tE r T) :
      ∀ n₀ : Nat, Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      ∀ (v' : V) (n' : Nat) (a : NamedAttestation V) (h' : Height) (entry : BlockId)
        (tmo : Bool),
        n' ≤ n₀ + 1 → Restated.HonestThrough M Sched x n' v' → a.val_index = v' →
        (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n'].sent →
        (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x[n₀].sent →
        a.height_pair = NamedHeightPair.vote h' entry tmo →
        h' ≤ (M.derive_named S.E S.cfg T).h →
        ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = entry →
        Block.Preceq C.erase T.erase :=
  targetsSince_of_anchor₈₃u facts S Sched x hsync hmono hawake hgst hcv hvalid hawm hthird
    hcom hlen hrD hrW hprev hclear hA

end

end DecoupledConsensusModel.Sts.Restated
