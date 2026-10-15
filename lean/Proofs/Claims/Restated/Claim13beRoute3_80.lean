import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13beRoute3_21
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_64b
import Proofs.Claims.Restated.Claim13beRoute3_65
import Proofs.Claims.Restated.Claim13beRoute3_68
import Proofs.Claims.Restated.Claim13beRoute3_70
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_77
import Proofs.Claims.Restated.Claim13beRoute3_78
import Proofs.Claims.Restated.Claim13beRoute3_79
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_OutageInputs
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_SeedEntryCanonical
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RecoveryGenuineClearNextVote
import Proofs.Vocabulary.Protocol.Grades.RelativeSupporter
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_MajoritySG_ForkChoice
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_79
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedVoteConsumers
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Vocabulary_Protocol_Grades_GoldfishConePersistence
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Record.Wiring

/-!
# The second-slot cone at the switch round, and the round-`rW` SG blocks on one chain

Theorems over a model `M : Record.Model V` and its facts, for a regime along
`runAllPath M S Sched x v N`: the honest Goldfish votes of the switch round's second slot descend
from a block graded at an honest round-`rW` read, from the selected grade-2 candidate and from the
anchor of an honest action read. From these, the round-`rW` SG blocks of any two validators in
`notHeldAt Sched` at `S.a rW` lie on one chain (`BaseSGOneChainAtSwitchRound`).
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
local macro "p64b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_64b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p65% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_65)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p68% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_68)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p69b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_69b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p70% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_70)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p72% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_72)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p73% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_73)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p74% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_74)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p77% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_77)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p78% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_78)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Along the path `W` of `hf`, if `1 ≤ c`, `w` is in the set `Hs` for `domain c p`, `w`'s finalized
    block before `domain c p` is an ancestor of `T`, every round-`(c − 1)` action emitter of the set
    has its SG block compatible with `T`, and `B` can pass the relative phase-`p` grade test of
    round `c` at `w`'s store there, then some member `u` of the set for `S.a (c − 1)` emits its
    round-`(c − 1)` attestation, and `B` is an ancestor of every round-`(c − 1)` SG block `u` can
    select. -/
theorem phaseGrade_preceq_previousSGBlock_l80 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hbelow : BelowOneThirdOn S rho Hs)
    {c : Round} (hc : 1 ≤ c) {p : DecoupledConsensusModel.Protocol.Phase}
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hdomainHor : M.domain S.E S.hc c p ≤ rho.horizon)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc c p))
    {T B : Block V}
    (hFT : Block.Preceq (W (strictEventIndex rho (M.domain S.E S.hc c p)) w).st.core.F T)
    (hsg : Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (c - 1) T)
    (hgrade : M.gradeBool S.E
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc c p)) w).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc c p)) w).st.core.F
      S.hc.η_SG c (M.early S.E S.hc c p) (M.late S.E S.hc c p) B ⇢ true)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1)) :
    ∃ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) u) (c - 1),
      ∀ D : M.NS × M.NR × NamedAttestation V,
        M.duties_attest_with (M.gradeContract nu.cache) S.E S.hc (S.node u) nu.st nu.record ⇢ D →
        Restated.Vocabulary.Execution.Run.emits M S rho W u (Object.attest D.2.2)
            (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ∧
          ∀ g : Option (Block V), M.grade2_block_with (M.gradeContract nu.cache) S.E S.hc
              (M.toHealing nu.st.core) (M.round_of S.hc (M.toHealing nu.st.core).s) ⇢ g →
          ∀ Bk : Block V, M.get_sg_vote_with (M.gradeContract nu.cache) S.E S.hc
              (M.toHealing nu.st.core) (M.round_of S.hc (M.toHealing nu.st.core).s) g ⇢ Bk →
            Block.Preceq B Bk := by
  obtain ⟨q, rfl⟩ : ∃ q, c = q + 1 := ⟨c - 1, (Nat.sub_add_cancel hc).symm⟩
  simp only [Nat.add_sub_cancel] at hpost hsg hA ⊢
  have hW := hf.onePath
  have hlatest : q ∈ M.latest_window S.hc.η_SG (q + 1) := by
    simpa only [Nat.add_sub_cancel] using
      facts.fc.pred_mem_latest_window S.hc.η_SG (q + 1) S.hc.η_SG_ge_one (Nat.succ_pos q)
  have hactionDeadline : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤
      M.early S.E S.hc (q + 1) p := by
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self q)
    have h2 := facts.gr.early_g2_add_delta_le_early_g1 S (q + 1)
    have h3 := facts.gr.early_g1_add_delta_le_early_g0 S (q + 1)
    have hΔ := S.E.Δ_pos
    show M.a S.hc S.E.Δ q + S.E.Δ ≤ M.early S.E S.hc (q + 1) p
    cases p <;> linarith
  have hearlyDomain : M.early S.E S.hc (q + 1) p ≤ M.domain S.E S.hc (q + 1) p := by
    have h := facts.gr.early_add_two_delta_le_domain S (q + 1) p
    linarith [S.E.Δ_pos]
  have hearlyHor : M.early S.E S.hc (q + 1) p ≤ rho.horizon := hearlyDomain.trans hdomainHor
  have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans (hactionDeadline.trans hearlyHor)
  have hwE : w ∈ Hs (M.early S.E S.hc (q + 1) p) := hHs _ _ hearlyDomain hw
  have hmemE : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) p), v ∈ Hs (M.early S.E S.hc (q + 1) p) :=
    fun v hv => hHs _ _ hearlyDomain hv
  have hmemAD : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) p),
      v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ) :=
    fun v hv => hHs _ _ (hactionDeadline.trans hearlyDomain) hv
  have hmemA : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) p),
      v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S q) :=
    fun v hv => hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) (hmemAD v hv)
  have hamem := (p65% mem_stateBeforeTime_along₆₅) hf.sorted hW
    (Restated.Vocabulary.Execution.Setup.a M S q)
  have hvoteIn : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) p),
      ∃ (a : NamedAttestation V) (Bk : Block V) (Bn : NamedBlock V),
        a.val_index = v ∧ a.round = q ∧
        Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (Object.attest a)
          (Restated.Vocabulary.Execution.Setup.a M S q) ∧
        a.confirmed = some Bk.root ∧ Bn.erase = Bk ∧ Restated.RunBlockOn M S rho W Xb Bn ∧
        Block.compatible Bk T = true ∧
        ∀ Y, M.interpretedInputs
          (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core))
          (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core.F
          S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p) v ⇢ Y → M.sgVote a.erase ∈ Y := by
    intro v hv
    have hvA := hmemA v hv
    obtain ⟨nv, hnv, g, hg, Bk, hBk⟩ := (p65% exists_actionSG₆₅) facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q
    obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract nv.cache) S.E S.hc (S.node v)
      nv.st nv.record
    have hem := Restated.honest_emits_actionAttestationAtOn facts S Hs Xb hf q hvA hactionHor hpost
      (hA v (hmemAD v hv)) (fun j hj => hf.tick_outcome j _ _ hj) nv hnv D hD
    have hsgv := hem.2 g hg Bk hBk
    have haval : D.2.2.val_index = v := by
      have h := congrArg Protocol.SGVote.val_index hsgv
      rw [facts.sto.sgVote_val_index_eq_val_index, namedAttestation_erase_val_index] at h
      exact h
    have haround : D.2.2.round = q := by
      have h := congrArg Protocol.SGVote.round hsgv
      rw [facts.sto.sgVote_round_eq_round, namedAttestation_erase_round] at h
      exact h
    have haconf : D.2.2.confirmed = some Bk.root := by
      have h := congrArg Protocol.SGVote.confirmed hsgv
      rw [facts.sto.sgVote_confirmed_eq, namedAttestation_erase_confirmed] at h
      exact h
    obtain ⟨i, hi, -, -, -, -, hall⟩ :=
      Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_head facts S rho W hW hem.1
    obtain ⟨ni, hni, -⟩ := (p65% exists_actionSG₆₅) facts S (W i v) D.2.2.round
    obtain ⟨H, hH, hHconf⟩ := hall ni hni
    have hHbody : H ∈ (W i v).st.bodies := by
      rw [← (p65% actionReadFrom_bodies₆₅) facts S _ _ ni hni]
      exact hH
    have hHrun : Restated.RunBlockOn M S rho W Xb H :=
      Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hv) hHbody
    have hBmem : Bk ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core.T :=
      Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho v q _
        hamem nv hnv g hg Bk hBk
    obtain ⟨Bn, hBnerase, hBnrun⟩ := Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb
      hf (hHsXb _ hv) (Restated.Vocabulary.Execution.Setup.a M S q) hBmem
    have hrootEq : H.erase.root = Bn.erase.root := by
      rw [Proofs.NamedWire.erase_root, hBnerase]
      exact Option.some.inj (hHconf.symm.trans haconf)
    have hHB : H.erase = Bn.erase :=
      Restated.runBlock_eq_of_root_eqOn facts W Xb hf.rootCollisionFree hHrun hBnrun hrootEq
    have hHerase : H.erase = Bk := hHB.trans hBnerase
    have hBT : Block.compatible Bk T = true :=
      hsg v hvA nv hnv D hD hem.1 g hg Bk hBk
    have hmem : ∀ Y, M.interpretedInputs
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core.F
        S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p) v ⇢ Y → M.sgVote D.2.2.erase ∈ Y := by
      rcases compatible_cases hBT with hBkT | hTBk
      · exact Restated.action_vote_mem_interpretedInputs_after_gst_common_upperOn facts
          S Hs Xb hf hHs hHsXb p hlatest (hmemE v hv) hwE
          ⟨haval, haround, hem.1⟩ ⟨i, hi, ⟨ni, hni, hH⟩, hHconf⟩
          (by rw [hHerase]; exact hBkT) hFT
          (by rw [haround]; exact hpost)
          (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
          hearlyDomain hearlyHor
      · exact Restated.action_vote_mem_interpretedInputs_after_gst_common_upperOn facts
          S Hs Xb hf hHs hHsXb p hlatest (hmemE v hv) hwE
          ⟨haval, haround, hem.1⟩ ⟨i, hi, ⟨ni, hni, hH⟩, hHconf⟩
          (Proofs.ModelProperties.Preceq_self H.erase)
          (preceq_trans_Preceq hFT (by rw [hHerase]; exact hTBk))
          (by rw [haround]; exact hpost)
          (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
          hearlyDomain hearlyHor
    exact ⟨D.2.2, Bk, Bn, haval, haround, hem.1, haconf, hBnerase, hBnrun, hBT, hmem⟩
  have hwin : ∀ ins : V → Finset (Protocol.SGVote V),
      (∀ v, M.interpretedInputs
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core.F
        S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p) v ⇢ ins v) →
      S.E.electorate.weightOf (Finset.univ \ Hs (M.domain S.E S.hc (q + 1) p)) <
        S.E.electorate.weightOf ((Hs (M.domain S.E S.hc (q + 1) p)).filter
          fun v => (ins v).Nonempty) := by
    intro ins hins
    have hsubset : Hs (M.domain S.E S.hc (q + 1) p) ⊆
        (Hs (M.domain S.E S.hc (q + 1) p)).filter fun v => (ins v).Nonempty := by
      intro v hv
      obtain ⟨a, -, -, -, -, -, -, -, -, -, hmem⟩ := hvoteIn v hv
      exact Finset.mem_filter.2 ⟨hv, ⟨_, hmem _ (hins v)⟩⟩
    exact lt_of_lt_of_le
      (by simpa only [HonestWeightMajority] using
        honestWeightMajorityOn_of_belowOneThirdOn hbelow _ hdomainHor)
      (S.E.electorate.weightOf_mono hsubset)
  obtain ⟨v, hv, I, hI, u, hu, head, hconf, hfind, -, hBhead, -, hmax⟩ :=
    facts.gr.exists_honest_max_positive_supporter_of_relativeGrade S.E S.hc hwin true hgrade rfl
  obtain ⟨a, Bk, Bn, haval, haround, hemit, haconf, hBnerase, hBnrun, hBT, hmem⟩ := hvoteIn v hv
  have hqle : q ≤ u.round := by
    have h := hmax (M.sgVote a.erase) (hmem I hI)
    rw [facts.sto.sgVote_round_eq_round, namedAttestation_erase_round, haround] at h
    exact h
  obtain ⟨R, hR⟩ := facts.gr.rawInputs_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core))
    S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p) v
  obtain ⟨bu, hbu⟩ := facts.gr.bodyReady_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core.F
    (M.early S.E S.hc (q + 1) p) u
  have huraw := ((facts.gr.mem_interpretedInputs_iff I hI R hR bu hbu).mp hu).1
  obtain ⟨b, -, hbround, hbproj, huwindow, -, hbemit⟩ :=
    Restated.rawInputs_traceOn facts S rho Hs Xb hf hHs (M.domain S.E S.hc (q + 1) p)
      (M.early S.E S.hc (q + 1) p) w S.hc.η_SG (q + 1) v hv R hR huraw
  have hule : u.round ≤ q := Nat.le_of_lt_succ (facts.fc.window_bounds huwindow).2
  have huroundEq : u.round = q := Nat.le_antisymm hule hqle
  have hba : b = a := Restated.emits_attest_uniqueOn facts S Hs Xb hf hbemit hemit
    ((hbround.trans huroundEq).trans haround.symm)
  have huEq : u = M.sgVote a.erase := by
    rw [← hbproj, hba]
  have hheadRoot : head.root = Bk.root := by
    have huconf := congrArg Protocol.SGVote.confirmed huEq
    rw [facts.sto.sgVote_confirmed_eq, namedAttestation_erase_confirmed, hconf, haconf] at huconf
    exact Option.some.inj huconf
  have hheadMem : head ∈ (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core.T := by
    have h := Proofs.HealingLemmas.find?_mem hfind
    rw [facts.gr.Sts_gradeView_T] at h
    exact h
  obtain ⟨Headn, hHeaderase, hHeadrun⟩ := Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts
    S Hs Xb hf (hHsXb _ hw) (M.domain S.E S.hc (q + 1) p) hheadMem
  have hheadBnRoot : Headn.erase.root = Bn.erase.root := by
    rw [hHeaderase, hBnerase]
    exact hheadRoot
  have hheadB : head = Bk := by
    rw [← hHeaderase, ← hBnerase]
    exact Restated.runBlock_eq_of_root_eqOn facts W Xb hf.rootCollisionFree hHeadrun hBnrun hheadBnRoot
  rw [hheadB] at hBhead
  have hvA := hmemA v hv
  refine ⟨v, hvA, fun nu hnu D hD => ?_⟩
  have hem := Restated.honest_emits_actionAttestationAtOn facts S Hs Xb hf q hvA hactionHor hpost
    (hA v (hmemAD v hv)) (fun j hj => hf.tick_outcome j _ _ hj) nu hnu D hD
  refine ⟨hem.1, fun g hg Bk' hBk' => ?_⟩
  have hsgv := hem.2 g hg Bk' hBk'
  have haround' : D.2.2.round = q := by
    have h := congrArg Protocol.SGVote.round hsgv
    rw [facts.sto.sgVote_round_eq_round, namedAttestation_erase_round] at h
    exact h
  have haconf' : D.2.2.confirmed = some Bk'.root := by
    have h := congrArg Protocol.SGVote.confirmed hsgv
    rw [facts.sto.sgVote_confirmed_eq, namedAttestation_erase_confirmed] at h
    exact h
  have hDa : D.2.2 = a := Restated.emits_attest_uniqueOn facts S Hs Xb hf hem.1 hemit
    (haround'.trans haround.symm)
  have hroot' : Bk'.root = Bk.root := by
    have h := haconf'
    rw [hDa, haconf] at h
    exact (Option.some.inj h).symm
  have hBmem' : Bk' ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core.T :=
    Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho v q _
      hamem nu hnu g hg Bk' hBk'
  obtain ⟨Bn', hBn'erase, hBn'run⟩ := Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb
    hf (hHsXb _ hv) (Restated.Vocabulary.Execution.Setup.a M S q) hBmem'
  have hEq : Bn'.erase = Bn.erase :=
    Restated.runBlock_eq_of_root_eqOn facts W Xb hf.rootCollisionFree hBn'run hBnrun
      (by rw [hBn'erase, hBnerase]; exact hroot')
  have hBkEq : Bk' = Bk := by
    rw [← hBn'erase, ← hBnerase]
    exact hEq
  rw [hBkEq]
  exact hBhead

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- For every node state `w₁` of `v`'s round-`r` action read and every anchor `A0` of `w₁` at round
    `r`, `A0` is the FG root of `w₁`'s store, or it is the active prefix, in `w₁`'s filtered tree,
    of the grade-1 entry of `w₁`'s frame for round `r`. -/
theorem actionAnchor_cases_l80 (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    ∀ w₁ ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r,
    ∀ A0 : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S w₁ r ⇢ A0 →
      A0 = M.get_fg_root (M.toHealing w₁.st.core).toFG ∨
      ∃ root A,
        (M.readFrame w₁.cache (M.toHealing w₁.st.core) r).g1 = some (some root) ∧
        M.activePrefix (Restated.Vocabulary.Internal.PhaseGrades.filteredTree M w₁) root = some A ∧
        A0 = A := by
  intro n _ A0 hA0
  obtain ⟨g, hg, rfl⟩ := (p64b% returns_map_elim₆₄b) _ _ _ hA0
  exact (p63% actionAnchor_cases_named_history₆₃w) facts S n r g hg

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Along the path `W` of `hf`, if `0 < s`, `lo ≤ proposal_time s`, slot `s`'s confirmation instant
    is in the horizon, every committee member of `s` in the set for its vote instant votes a run
    block descending from `B`, and every member `w` of the set for `vote_time (s + 1)` has an FG
    root comparable with `B` at its vote store of `s + 1`, with `h_max ≤ h(Hn) + 1` there for every
    run block `Hn` descending from `B` when that root is an ancestor of `B`, and an anchor
    compatible with `B`, then every committee member of `s + 1` in the set for its vote instant
    votes a run block descending from `B`. -/
theorem honestVotesCone_succ_of_cone_hMaxOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {B : Block V}
    (hcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq B X))
    (hroot : ∀ w ∈ Hs (M.vote_time S.E (s + 1)),
      Block.Preceq (M.get_fg_root
          (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG) B ∨
        Block.Preceq B (M.get_fg_root
          (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG))
    (hmax : ∀ w ∈ Hs (M.vote_time S.E (s + 1)),
      Block.Preceq (M.get_fg_root
          (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG) B →
      ∀ Hn : NamedBlock V, Restated.RunBlockOn M S rho W Xb Hn → Block.Preceq B Hn.erase →
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_max ≤
          (M.derive_named S.E S.cfg Hn).h + 1)
    (hanchor : ∀ w ∈ Hs (M.vote_time S.E (s + 1)),
      ∀ cw : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
          (M.vote_time S.E (s + 1))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ cw →
      ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
          (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
              (M.vote_time S.E (s + 1)))
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record cw)
          (M.round_of S.hc (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
              (M.vote_time S.E (s + 1)))
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record cw).st.core.s) ⇢ A →
        Block.compatible A B = true)
    (hrun : ∀ d : Slot, s ≤ d → d ≤ s + 1 → ∀ w ∈ S.E.committee d, w ∈ Hs (M.vote_time S.E d) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc d)) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb (s + 1) (fun X => Block.Preceq B X) := by
  have hvoteHor : M.vote_time S.E (s + 1) ≤ rho.horizon :=
    (Restated.vote_time_succ_le_confirmation_time_l77 facts S s).trans hhor
  have hvoteHorS : M.vote_time S.E s ≤ rho.horizon :=
    (facts.sch.Protocol_vote_time_le_confirmation_time S.E s).trans hhor
  have hpostVote : lo ≤ M.vote_time S.E s :=
    hpost.trans (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E s))
  have hfreezeVote : M.view_freeze S.E s ≤ M.vote_time S.E (s + 1) :=
    le_of_lt (facts.sch.view_freeze_lt_vote_time_succ S.E s)
  have hloFreeze : lo ≤ M.view_freeze S.E s :=
    hpostVote.trans (Restated.vote_time_le_view_freeze_l58 facts S.E s)
  have hloVoteSucc : lo ≤ M.vote_time S.E (s + 1) := hloFreeze.trans hfreezeVote
  have hpositive : 0 < ((S.E.committee s) ∩
      Hs (M.confirmation_time S.E s)).card := by
    have hc := hcom s
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpositive
  have hucomm : u ∈ S.E.committee s := (Finset.mem_inter.mp hu).1
  have huVote : u ∈ Hs (M.vote_time S.E s) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) (Finset.mem_inter.mp hu).2
  obtain ⟨X, hBX, hXrun, hXemit⟩ := hcone u huVote hucomm
  obtain ⟨cu, hcu, Tu, hTu, Lu, hLu, Lu', hLu', Hu, hHu⟩ := (p78% exists_voteHead₇₈) facts S
    (W (strictEventIndex rho (M.vote_time S.E s)) u) s
  obtain ⟨Hn, hHerase, hHrun⟩ := Restated.seedVoteDutyHead_runBlockOn facts S Hs Xb hf
    (hHsXb _ huVote) s cu hcu Tu hTu Lu hLu Lu' hLu' Hu hHu
  have hHemit := Restated.seedVoteDutyHead_emitsOn facts S Hs Xb hf huVote hs hucomm hvoteHorS
    hpostVote cu hcu (hrun s le_rfl (Nat.le_succ s) u hucomm huVote) Tu hTu Lu hLu Lu' hLu' Hu hHu
  have hXH : X.erase = Hn.erase :=
    Restated.runBlock_eq_of_root_eqOn facts W Xb hf.rootCollisionFree hXrun hHrun (by
      rw [hHerase]
      exact congrArg GoldfishVote.head
        (Restated.emits_gfVote_uniqueOn facts S Hs Xb hf hXemit hHemit rfl))
  have hBHn : Block.Preceq B Hn.erase := by
    rw [← hXH]
    exact hBX
  have hBHu : Block.Preceq B Hu := by
    rw [← hHerase]
    exact hBHn
  have hinputs : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs' M S rho s B w
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c) := by
    intro w hw c hc
    have hwFreeze : w ∈ Hs (M.view_freeze S.E s) := hHs _ _ hfreezeVote hw
    have hnst : (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st =
        M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) c := facts.nd.mkNode_st _ _ _
    refine { rootSide := ?_, anchor := hanchor w hw c hc }
    intro A hA T hT
    rcases hroot w hw with hrB | hBr
    · left
      have hvisible := Restated.voteHeadVisible_at_nextDuty_confOn facts S Hs Xb hf hHs hHsXb huVote
        hwFreeze hpost hhor hrB cu hcu Tu hTu Lu hLu Lu' hLu' Hu hHu hBHu
      have hvisT : Hu ∈ (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.T := hvisible.1
      have hvisStamp : stampedBefore
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.timestamp_block
          (M.view_freeze S.E s) Hu = true := hvisible.2
      have hdutyEq : (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1))).core =
          Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1) :=
        (p77% setClock_core_eq_tickStore₇₇) facts S _ _
      have hs1 : (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core).s = s + 1 :=
        (facts.sto.toHealing_s _).trans
          ((facts.hd.Sts_setClock_core_s S.E _ _).trans (facts.sch.slotOf_vote_time S.E (s + 1)))
      obtain ⟨P, hP⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
        (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core).toFG.toSG.toGoldfishStore
        (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core).s
      have hHprocessed : Hn.erase ∈ P := by
        refine facts.fc.mem_voter_processed_block_tree_of_stamped S.E _ _ ?_ ?_ P hP
        · rw [facts.sto.toHealing_gs_T, facts.hd.Sts_setClock_core_T, hHerase]
          exact hvisT
        · rw [hs1, Nat.add_sub_cancel, facts.sto.toHealing_gs_timestamp_block,
            facts.hd.setClock_core_timestamp_block, hHerase]
          exact hvisStamp
      have hmaxW : (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.h_max ≤
          (M.derive_named S.E S.cfg Hn).h + 1 := by
        have h := hmax w hw hrB Hn hHrun hBHn
        rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, (p77% tickStore_h_max₇₇) facts] at h
        exact h
      have hrootW : Block.Preceq (M.get_fg_root
          (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core).toFG) B := by
        have h := hrB
        rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, (p77% tickStore_fgRoot₇₇) facts] at h
        exact h
      have hBfilteredPre : B ∈ M.get_filtered_block_tree
          (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core).toFG :=
        Restated.filtered_of_viableDescendantOn facts S Hs Xb hf (hHsXb _ hw)
          hvisible.1 hHerase hHrun hBHu hmaxW hrootW
      have hBfiltered : B ∈ M.get_filtered_block_tree
          (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1))).core).toFG := by
        rw [hdutyEq, Restated.Vocabulary.Proofs.Optimistic.voteStore, (p77% tickStore_filtered₇₇) facts]
        exact hBfilteredPre
      have hmax' : (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core.h_max ≤ (M.derive_named S.E S.cfg Hn).h + 1 := by
        rw [facts.hd.setClock_core_h_max]
        exact hmaxW
      have hcand := Restated.namedAncestorCandidate_of_processedDescendant_and_hMaxOn facts S Hs Xb hf
        hHsXb hwFreeze P hP hHprocessed hHrun hBHn hBfiltered hmax' hloFreeze
      have hT' : M.voter_filtered_block_tree S.E
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1))).core
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1))).core.s ⇢ T := by
        have h := hT
        rewrite [facts.nd.mkNode_st] at h; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h
        exact h
      have hBT : B ∈ T := by
        rw [← facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree S.E _ P hP T hT']
        exact hcand
      refine ⟨by rw [hnst]; (try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]); rw [(p77% setClock_core_eq_tickStore₇₇) facts S]
                 exact hrB, hBT, ?_⟩
      exact Restated.votePathAt_of_candidateOn' facts S Hs Xb hf hwFreeze c hc hloFreeze
        T hT B hBT A hA
    · exact Or.inr (by rw [hnst]; (try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]); rw [(p77% setClock_core_eq_tickStore₇₇) facts S]
                       exact hBr)
  intro w hw hwCommittee
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
    (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache
  obtain ⟨T, L, L', Hd, hT, hL, hL', hHd⟩ := (p77% voterHead_outcome₇₇) facts S
    (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
      (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)
  obtain ⟨H, hHerase', hHrun'⟩ := Restated.seedVoteDutyHead_runBlockOn facts S Hs Xb hf (hHsXb _ hw)
    (s + 1) c hc T hT L hL L' hL' Hd hHd
  refine ⟨H, ?_, hHrun', ?_⟩
  · rw [hHerase']
    exact Restated.goldfishCone_stepOn'_GoldfishCone facts S Hs Xb hf hHs hHsXb hcom hs hpostVote
      hhor hcone hw c hc (hinputs w hw c hc) T hT L hL L' hL' Hd hHd
  · rw [hHerase']
    exact Restated.seedVoteDutyHead_emitsOn facts S Hs Xb hf hw (Nat.succ_pos s) hwCommittee
      hvoteHor hloVoteSucc c hc (hrun (s + 1) (Nat.le_succ s) le_rfl w hwCommittee hw)
      T hT L hL L' hL' Hd hHd

end

section
set_option autoImplicit false
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

end

section
set_option autoImplicit false
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

/-- A choice of one round-`r` action read per validator, staged from the world `w`, that gives `u`
    the node state `nu`. -/
private theorem exists_actionReads_choice₈₀ (facts : Record.Facts M) (S : Setup V) (w : V → M.N)
    (r : Round) (u : V) (nu : M.N)
    (hnu : nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w u) r) :
    ∃ nprev : V → M.N,
      (∀ u' : V, nprev u' ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w u') r) ∧
      nprev u = nu := by
  classical
  have hne : ∀ u' : V, ∃ m : M.N,
      m ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w u') r :=
    fun u' => (p73% actionReadFrom_nonempty₇₃) facts S _ _
  refine ⟨fun u' => if u' = u then nu else Classical.choose (hne u'), fun u' => ?_, if_pos rfl⟩
  by_cases hu' : u' = u
  · subst hu'
    beta_reduce
    rw [if_pos rfl]
    exact hnu
  · beta_reduce
    rw [if_neg hu']
    exact Classical.choose_spec (hne u')

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE`: every
    validator `w` in `notHeldAt Sched` at the vote instant of slot `opening_slot rW + 1` has, at its
    vote store of that slot, `h_max` at most one more than the chain-state height of any run block
    `Hn` along the path descending from `T`. -/
theorem hmax_at_secondSlot_of_checkpointPreceq_l80 (facts : Record.Facts M)
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
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h) :
    ∀ w ∈ notHeldAt Sched
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)),
    ∀ Hn : NamedBlock V,
      Restated.RunBlockOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N) Finset.univ Hn →
      Block.Preceq T.erase Hn.erase →
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M (Setup.alwaysAwake S)
            (Restated.runAllPath M S Sched x v N
              (Restated.strictEventIndex
                ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
                (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st.core
            ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)).h_max ≤
          (M.derive_named S.E S.cfg Hn).h + 1 := by
  intro w hw Hn hHrun hTH
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  have hTrun := (hreg.checkpoint_runBlock facts hf hHsXb).1
  have hTHh : (M.derive_named S.E S.cfg T).h ≤ (M.derive_named S.E S.cfg Hn).h :=
    facts.cs.derive_height_mono S.E S.cfg
      (Restated.namedPreceq_of_runBlock_erase_preceqOn facts (notHeldAt Sched) Finset.univ hf hTrun hHrun hTH)
  have hvote := Restated.vote_time_openingSucc_lt_action_l78 facts S (Restated.switchRound M S tE)
  have hthor : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hN]
    exact le_trans (le_of_lt (Int.lt_add_of_pos_right _ S.E.Δ_pos))
      (Restated.vote_time_add_delta_le_confirmation_l78 facts S (Nat.le_succ _))
  obtain ⟨hn₀1, -⟩ := Restated.tickStepAt_time facts x hn₀
  have hrow : (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st.core.h_max ≤
      Restated.topHonestRow M S Sched x n₀ + 1 := by
    by_cases hlarge : 1 < (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st.core.h_max
    · obtain ⟨b, tb, hb, hemit, htb, hrowb, -⟩ :=
        Restated.frontier_confirmationWitnessOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
          hHs hHsXb (honestWeightMajorityOn_of_belowOneThirdOn hbelow) hthor hlarge
      obtain ⟨k, -, hk, hsent⟩ := Restated.mem_sent_of_emits_runAll facts S Sched x v hemit
      obtain ⟨hk1, -⟩ := Restated.tickStepAt_time facts x hk
      have hkn : k + 1 ≤ n₀ + 1 := by
        by_contra hcon
        have hmono' : ((x[n₀ + 1].time : Nat) : Int) ≤ ((x[k + 1].time : Nat) : Int) := by
          exact_mod_cast Restated.time_mono facts S Sched x (by omega)
        have : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ tb := by
          rw [← hn₀1, ← hk1]; exact hmono'
        linarith
      have hbk : b.val_index ∈ Finset.univ \ Sched.adv (x[k + 1].time : Int) := by
        rw [hk1]
        exact hHs _ _ htb.le hb
      have hhon : Restated.HonestThrough M Sched x (k + 1) b.val_index :=
        Restated.honestThrough_of_mem_notHeld facts S Sched x (k + 1) hmono _ hbk
      obtain ⟨entry, tmo, hpair⟩ := heightPair_vote_of_height_l72 hrowb
      have hle := Restated.honestRow_le_topHonestRow facts S Sched x hvalid.toUnforgeability
        ⟨b.val_index, k + 1, b, entry, tmo, hkn, hhon, rfl, hsent, hpair⟩
      exact Nat.sub_le_iff_le_add.mp hle
    · exact (Nat.le_of_not_lt hlarge).trans (Nat.le_add_left 1 _)
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, (p77% tickStore_h_max₇₇) facts]
  exact hrow.trans (Nat.add_le_add_right (htop.trans hTHh) 1)

end

section
set_option autoImplicit false
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

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE` and the
    round-`(rW − 1)` SG blocks ancestors of the opening-slot votes of `rW` (`hP`): if `T ⪯ B` and
    every committee member of `opening_slot rW` in `notHeldAt Sched` at its vote instant votes a run
    block descending from `B`, then for every validator in `notHeldAt Sched` at the vote instant of
    `opening_slot rW + 1`, every anchor of its vote read at that slot is on one chain with `B`. -/
theorem anchor_compatible_of_openingCone_l80 (facts : Record.Facts M)
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
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    (hP : ∀ nprev : V → M.N,
      (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
        (Restated.switchRound M S tE - 1)) →
      Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) nprev)
    {B : Block V} (hTB : Block.Preceq T.erase B)
    (hcone : Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) (notHeldAt Sched) Finset.univ
      ((M.opening_slot S.hc (Restated.switchRound M S tE))) (fun X => Block.Preceq B X)) :
    ∀ w ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)),
      ∀ cw : M.Cache, M.onPhaseTick S.E S.hc
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st.core.toHealing
          (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).cache ⇢ cw →
      ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M (Setup.alwaysAwake S)
          (M.mkNode
            (M.ns_setClock S.E
              (Restated.runAllPath M S Sched x v N
                (Restated.strictEventIndex
                  ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
                  (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st
              (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)))
            (Restated.runAllPath M S Sched x v N
              (Restated.strictEventIndex
                ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
                (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).record cw)
          (M.round_of S.hc (M.mkNode
            (M.ns_setClock S.E
              (Restated.runAllPath M S Sched x v N
                (Restated.strictEventIndex
                  ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
                  (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st
              (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)))
            (Restated.runAllPath M S Sched x v N
              (Restated.strictEventIndex
                ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
                (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).record cw).st.core.s) ⇢ A →
        Block.compatible A B = true := by
  intro w hw cw hcw A hA
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
  obtain ⟨hpredle, hrW1⟩ := pred_le_pred_pos_l74 a.round (Restated.switchRound M S tE) hapos harW
  obtain ⟨-, hloVote, hloPrev, -⟩ := Restated.loBounds_l70 facts S hapos hlo
  have hoPos : 0 < (M.opening_slot S.hc (Restated.switchRound M S tE)) :=
    facts.gr.opening_slot_pos_of_round_pos S.hc (lt_of_lt_of_le hapos harW)
  have hpostVote : tGAT + 1 ≤ M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) :=
    hloVote.trans (facts.sch.vote_time_mono_slots S.E (facts.gr.opening_slot_mono S harW))
  have hconfHor : M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hN]
    exact facts.sch.confirmation_time_mono_l78 S (Nat.le_add_right _ 2)
  have hpositive : 0 < (((Setup.alwaysAwake S).E.committee
      ((M.opening_slot S.hc (Restated.switchRound M S tE)))) ∩
      notHeldAt Sched (M.confirmation_time (Setup.alwaysAwake S).E
        ((M.opening_slot S.hc (Restated.switchRound M S tE))))).card := by
    have hc := hcomOn ((M.opening_slot S.hc (Restated.switchRound M S tE)))
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hpositive
  have hycomm : y ∈ S.E.committee ((M.opening_slot S.hc (Restated.switchRound M S tE))) :=
    (Finset.mem_inter.mp hy).1
  have hyVote : y ∈ notHeldAt Sched
      (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) (Finset.mem_inter.mp hy).2
  obtain ⟨cc, hcc, Tr, hTr, L, hL, L', hL', H, hH⟩ := (p78% exists_voteHead₇₈) facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))) y)
    ((M.opening_slot S.hc (Restated.switchRound M S tE)))
  obtain ⟨Hy, hHyErase, hHyRun⟩ := Restated.seedVoteDutyHead_runBlockOn facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf (hHsXb _ hyVote) ((M.opening_slot S.hc (Restated.switchRound M S tE)))
    cc hcc Tr hTr L hL L' hL' H hH
  have hvoteHorO : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon :=
    (facts.sch.Protocol_vote_time_le_confirmation_time S.E _).trans hconfHor
  have hrunY : ∀ j : Nat,
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
          Record.Run V).events[j]? =
        some (Record.Event.tick y (M.vote_time S.E (M.opening_slot S.hc (Restated.switchRound M S tE)))) →
      M.awake_for_grade1 (Setup.alwaysAwake S) y (Restated.runAllPath M S Sched x v N j y)
        (M.round_of S.hc (M.opening_slot S.hc (Restated.switchRound M S tE))) := by
    intro j hj
    have hpredLt : Restated.switchRound M S tE - 1 < Restated.switchRound M S tE :=
      Nat.sub_lt hrW1 Nat.one_pos
    have hwin : tGAT + 1 ≤ M.early S.E S.hc
        (M.round_of S.hc (M.opening_slot S.hc (Restated.switchRound M S tE))) .g1 - S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_eq S.hc _]
      have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three hpredLt
      have h2 := facts.gr.q10_early_g2_le_early_g1 S (Restated.switchRound M S tE)
      have h3 : tGAT + 1 ≤ M.a S.hc S.E.Δ (Restated.switchRound M S tE - 1) :=
        hloPrev.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hpredle)
      linarith
    exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj hyVote hwin
  have hHyEmit := Restated.seedVoteDutyHead_emitsOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    hf hyVote hoPos hycomm hvoteHorO hpostVote cc hcc hrunY Tr hTr L hL L' hL' H hH
  have hvoteEq : ∀ X : NamedBlock V,
      Restated.RunBlockOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N) Finset.univ X →
      Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N) y
        (NamedObject.gfVote ⟨y, (M.opening_slot S.hc (Restated.switchRound M S tE)), X.erase.root⟩)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))) →
      X.erase = H := by
    intro X hXrun hXemit
    rw [← hHyErase]
    exact Restated.runBlock_eq_of_root_eqOn facts _ Finset.univ hf.rootCollisionFree hXrun hHyRun (by
      rw [hHyErase]
      exact congrArg GoldfishVote.head
        (Restated.emits_gfVote_uniqueOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hXemit
          hHyEmit rfl))
  have hBy : Block.Preceq B H := by
    obtain ⟨X, hBX, hXrun, hXemit⟩ := hcone y hyVote hycomm
    rw [← hvoteEq X hXrun hXemit]
    exact hBX
  have hsg : Restated.HonestSGEmissionsCompatibleAtRoundOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) (Restated.switchRound M S tE - 1) B := by
    intro u hu nu hnu D hD hemit gc stu k A2' hA2' G' hG'
    obtain ⟨nprev, hnprev, hnprevu⟩ := exists_actionReads_choice₈₀ facts (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))))
      (Restated.switchRound M S tE - 1) u nu hnu
    have hPu := hP nprev hnprev u hu
    rw [hnprevu] at hPu
    obtain ⟨X, hXu, hXrun, hXemit⟩ := hPu D hD hemit A2' hA2' G' hG' y hyVote hycomm
    rw [hvoteEq X hXrun hXemit] at hXu
    exact compatible_of_preceq_common_Preceq hXu hBy
  have hmemW := (p69b% mem_stateBeforeTime_along₆₉b) hf.sorted hf.onePath
    (M.vote_time (Setup.alwaysAwake S).E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))
  have hroot : Block.compatible
      (M.get_fg_root (M.toHealing (M.mkNode
        (M.ns_setClock S.E
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)))
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).record cw).st.core).toFG)
      B = true := by
    refine (congrArg (fun R => Block.compatible R B)
      (Restated.fgRoot_voteDutyRead_eq_l78 facts (Setup.alwaysAwake S) _ w _ _ hmemW cw hcw)).trans ?_
    exact compatible_of_preceq_common_Preceq
      (preceq_trans_Preceq
        (Restated.fgRoot_comparable_anchor_at_secondSlot facts S Sched x v hsync hmono hawake hgst hcv hvalid
          hawm hthird hcom hlen htd hN hreg harW hn₀ htop w hw) hTB)
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
  have hr := Restated.round_of_openingSucc_l78 facts S (Restated.switchRound M S tE)
  have hwdom : w ∈ notHeldAt Sched (M.domain S.E S.hc
      ((M.round_of S.hc ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) .g1) := by
    rw [hr]
    exact hHs _ _ (Restated.domain_g1_le_vote_openingSucc_l78 facts S (Restated.switchRound M S tE)) hw
  have hr' : (M.round_of (Setup.alwaysAwake S).hc ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)) =
      Restated.switchRound M S tE := hr
  have hkPrev : tGAT + 1 ≤ M.early S.E S.hc (Restated.switchRound M S tE - 1) .g2 - S.E.Δ := by
    have hr0 := Restated.NamedHeightRegimeRunOn.r0_le_round_l71 facts hf hreg
    have hη := S.hc.η_SG_ge_one
    have h1 : (Restated.roundAt M S tGAT : Nat) + 1 + 2 ≤
        (Restated.roundAt M S tGAT : Nat) + S.hc.η_SG + 2 :=
      Nat.add_le_add_right (Nat.add_le_add_left hη _) 2
    have h2 : (Restated.roundAt M S tGAT : Nat) + 1 + 2 ≤ (Restated.switchRound M S tE : Nat) :=
      h1.trans (hr0.trans harW)
    have hA1 : tGAT + 1 ≤
        Restated.Vocabulary.Execution.Setup.a M S (Restated.roundAt M S tGAT + 1) :=
      Int.add_one_le_iff.mpr (lt_of_le_of_lt (Restated.Vocabulary.Statements.roundAt_spec facts S tGAT)
        (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S (Nat.lt_succ_self _)))
    exact Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hA1
      (Restated.lt_pred_of_add_two_le_l54 h2)
  exact Restated.voterAnchorAt_compatible_of_previousSGHistory_namedOn facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs hHsXb hbelow hconfHor (by rw [hr']; exact hrW1)
    (by rw [hr']; exact hsg) (by rw [hr']; exact hloPrev.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hpredle))
    hwdom cw hcw hroot
    (by
      rw [hr']
      exact fun u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake
        hn (Restated.switchRound M S tE - 1) hkPrev u j hj) A hA

end

section
set_option autoImplicit false
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

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE` and the
    round-`(rW − 1)` SG blocks ancestors of the opening-slot votes of `rW` (`hP`): if `T ⪯ B` and
    every committee member of `opening_slot rW` in `notHeldAt Sched` at its vote instant votes a run
    block descending from `B`, then so does every committee member of `opening_slot rW + 1` in
    `notHeldAt Sched` at its vote instant. -/
theorem secondSlotCone_of_openingCone_l80 (facts : Record.Facts M)
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
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    (hP : ∀ nprev : V → M.N,
      (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
        (Restated.switchRound M S tE - 1)) →
      Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) nprev)
    {B : Block V} (hTB : Block.Preceq T.erase B)
    (hcone : Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) (notHeldAt Sched) Finset.univ
      ((M.opening_slot S.hc (Restated.switchRound M S tE))) (fun X => Block.Preceq B X)) :
    Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) (notHeldAt Sched) Finset.univ
      ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) (fun X => Block.Preceq B X) := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
  obtain ⟨hpredle, hrW1⟩ := pred_le_pred_pos_l74 a.round (Restated.switchRound M S tE) hapos harW
  obtain ⟨-, hloVote, hloPrev, -⟩ := Restated.loBounds_l70 facts S hapos hlo
  have hoPos : 0 < (M.opening_slot S.hc (Restated.switchRound M S tE)) :=
    facts.gr.opening_slot_pos_of_round_pos S.hc (lt_of_lt_of_le hapos harW)
  have hconfHor : M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hN]
    exact facts.sch.confirmation_time_mono_l78 S (Nat.le_add_right _ 2)
  have hpredLt : Restated.switchRound M S tE - 1 < Restated.switchRound M S tE := Nat.sub_lt hrW1 Nat.one_pos
  have hpredProp : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1)) ≤
      M.proposal_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) := by
    have h1 := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S hpredLt
    exact (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1
  have hpostProp : tGAT + 1 ≤
      M.proposal_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) :=
    (hloPrev.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hpredle)).trans hpredProp
  have hwinW : tGAT + 1 ≤ M.early S.E S.hc (Restated.switchRound M S tE) .g1 - S.E.Δ := by
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three hpredLt
    have h2 := facts.gr.q10_early_g2_le_early_g1 S (Restated.switchRound M S tE)
    have h3 : tGAT + 1 ≤ M.a S.hc S.E.Δ (Restated.switchRound M S tE - 1) :=
      hloPrev.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hpredle)
    linarith
  have hrunW : ∀ d : Slot, (M.opening_slot S.hc (Restated.switchRound M S tE)) ≤ d →
      d ≤ (M.opening_slot S.hc (Restated.switchRound M S tE)) + 1 →
      ∀ w ∈ S.E.committee d, w ∈ notHeldAt Sched (M.vote_time S.E d) →
      ∀ j : Nat, ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
          Record.Run V).events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
        M.awake_for_grade1 (Setup.alwaysAwake S) w (Restated.runAllPath M S Sched x v N j w)
          (M.round_of S.hc d) := by
    intro d hd1 hd2 w _ hw j hj
    have hround : M.round_of S.hc d = Restated.switchRound M S tE := by
      rcases Nat.lt_or_ge d ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) with h | h
      · rw [le_antisymm (Nat.lt_succ_iff.mp h) hd1]
        exact facts.gr.round_of_opening_slot_eq S.hc _
      · rw [le_antisymm hd2 h]
        exact facts.gr.HealingLemmas_round_of_opening_succ S.hc _
    have hwin : tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc d) .g1 - S.E.Δ := by
      rw [hround]
      exact hwinW
    exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin
  exact Restated.honestVotesCone_succ_of_cone_hMaxOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    hf hHs hHsXb hcomOn hoPos hpostProp hconfHor hcone
    (fun w hw => Or.inl (preceq_trans_Preceq
      (Restated.fgRoot_comparable_anchor_at_secondSlot facts S Sched x v hsync hmono hawake hgst hcv hvalid
        hawm hthird hcom hlen htd hN hreg harW hn₀ htop w hw) hTB))
    (fun w hw _ Hn hHrun hBH => Restated.hmax_at_secondSlot_of_checkpointPreceq_l80 facts S Sched x v hsync
      hmono hawake hgst hcv hvalid hawm hthird hcom hlen htd hN hreg harW hn₀ htop w hw Hn hHrun
      (preceq_trans_Preceq hTB hBH))
    (Restated.anchor_compatible_of_openingCone_l80 facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm
      hthird hcom hlen htd hN hreg harW hn₀ htop hP hTB hcone)
    hrunW

end

section
set_option autoImplicit false
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

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE`, `hP`,
    and `hprev` (when the source round is `rW`, every round-`(rW − 1)` SG emission is on one chain
    with `T`): for a validator `v'` in `notHeldAt Sched` at `S.a rW`, a phase `p` whose domain
    instant is at or before `S.a rW`, and a block `B` that can pass the relative phase-`p` grade
    test of round `rW` at `v'`'s store before that instant, every committee member of
    `opening_slot rW + 1` in `notHeldAt Sched` at its vote instant votes along the path a run block
    descending from `B`. -/
theorem gradedBlock_cone_at_secondSlot (facts : Record.Facts M)
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
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    (hP : ∀ nprev : V → M.N,
      (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
        (Restated.switchRound M S tE - 1)) →
      Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) nprev)
    (hprev : a.round = Restated.switchRound M S tE →
      Restated.BasePreviousRoundSGCompatibleWithAnchor M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) T)
    {v' : V} (hv' : v' ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {p : Protocol.Phase}
    (hdom : M.domain S.E S.hc (Restated.switchRound M S tE) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))
    {B : Block V}
    (hB : M.gradeBool S.E
      (M.gradeView (M.toHealing (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.domain S.E S.hc (Restated.switchRound M S tE) p)) v').st.core))
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.domain S.E S.hc (Restated.switchRound M S tE) p)) v').st.core.F
      S.hc.η_SG (Restated.switchRound M S tE) (M.early S.E S.hc (Restated.switchRound M S tE) p)
        (M.late S.E S.hc (Restated.switchRound M S tE) p) B ⇢ true) :
    Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) (notHeldAt Sched) Finset.univ
      ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) (fun X => Block.Preceq B X) := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hrWN : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (x[N].time : Int) := by
    rw [hN]; exact Restated.action_le_confirmation_third facts S _
  obtain ⟨hf, hrW1, hpost, hsg⟩ := (p74% grade1_inputs₇₄) facts S Sched x v hsync hmono hawake hgst
    hcv hvalid hawm hthird hcom hrWN hn hreg harW (fun h => hprev h)
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  have hdomainHor : M.domain S.E S.hc (Restated.switchRound M S tE) p ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    exact hdom.trans hrWN
  have hwdom : v' ∈ notHeldAt Sched (M.domain S.E S.hc (Restated.switchRound M S tE) p) :=
    hHs _ _ hdom hv'
  obtain ⟨n, hnA⟩ := (p73% actionReadFrom_nonempty₇₃) facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v')
    (Restated.switchRound M S tE)
  have hmemA := (p69b% mem_stateBeforeTime_along₆₉b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE))
  have hFT : Block.Preceq
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.domain S.E S.hc (Restated.switchRound M S tE) p)) v').st.core.F T.erase := by
    have h1 := (p77% F_mono_along₇₇) facts (Setup.alwaysAwake S) hf.onePath v'
      ((p65% strictEventIndex_mono₆₅)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) hdom)
    have h2 := (p77% F_preceq_fgRoot_along₇₇) facts (Setup.alwaysAwake S) hf.sorted hf.onePath v'
      (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))
    have h3 := Restated.actionFgRoot_preceq_checkpoint_at_switchRound facts S Sched x v hsync hmono hawake hgst
      hcv hvalid hawm hthird hcom hlen htd hN hreg harW hn₀ htop v' hv' n hnA
    rw [Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_fgRoot_eq_storeBeforeTime facts
      (Setup.alwaysAwake S) _ v' (Restated.switchRound M S tE) _ hmemA n hnA] at h3
    exact preceq_trans_Preceq h1 (preceq_trans_Preceq h2 h3)
  have hkPrev : tGAT + 1 ≤ M.early S.E S.hc (Restated.switchRound M S tE - 1) .g2 - S.E.Δ := by
    have hr0 := Restated.NamedHeightRegimeRunOn.r0_le_round_l71 facts hf hreg
    have hη := S.hc.η_SG_ge_one
    have h1 : (Restated.roundAt M S tGAT : Nat) + 1 + 2 ≤
        (Restated.roundAt M S tGAT : Nat) + S.hc.η_SG + 2 :=
      Nat.add_le_add_right (Nat.add_le_add_left hη _) 2
    have h2 : (Restated.roundAt M S tGAT : Nat) + 1 + 2 ≤ (Restated.switchRound M S tE : Nat) :=
      h1.trans (hr0.trans harW)
    have hA1 : tGAT + 1 ≤
        Restated.Vocabulary.Execution.Setup.a M S (Restated.roundAt M S tGAT + 1) :=
      Int.add_one_le_iff.mpr (lt_of_le_of_lt (Restated.Vocabulary.Statements.roundAt_spec facts S tGAT)
        (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S (Nat.lt_succ_self _)))
    exact Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hA1
      (Restated.lt_pred_of_add_two_le_l54 h2)
  obtain ⟨u, hu, hall⟩ := Restated.phaseGrade_preceq_previousSGBlock_l80 facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs hHsXb hbelow hrW1 hpost hdomainHor hwdom hFT hsg hB
    (fun u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake
      hn (Restated.switchRound M S tE - 1) hkPrev u j hj)
  obtain ⟨nu, hnu, g, hg, Bk, hBk⟩ := (p65% exists_actionSG₆₅) facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
    (Restated.switchRound M S tE - 1)
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract nu.cache) (Setup.alwaysAwake S).E
    (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node u) nu.st nu.record
  obtain ⟨hemit, hBall⟩ := hall nu hnu D hD
  have hBX : Block.Preceq B Bk := hBall g hg Bk hBk
  have hXT : Block.compatible Bk T.erase = true := hsg u hu nu hnu D hD hemit g hg Bk hBk
  have hcheck := Restated.checkpointCone_at_secondSlot facts S Sched x v hsync hmono hawake hgst hcv hvalid
    hawm hthird hcom hlen htd hN hreg harW
  rcases compatible_cases hXT with hXT' | hTX
  · exact Restated.namedHonestVotesConeOn_of_preceq_l78 facts (preceq_trans_Preceq hBX hXT') hcheck
  · rcases preceq_linear_Preceq hBX hTX with hBT | hTB
    · exact Restated.namedHonestVotesConeOn_of_preceq_l78 facts hBT hcheck
    · obtain ⟨nprev, hnprev, hnprevu⟩ := exists_actionReads_choice₈₀ facts (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))))
        (Restated.switchRound M S tE - 1) u nu hnu
      have hPu := hP nprev hnprev u hu
      rw [hnprevu] at hPu
      exact Restated.secondSlotCone_of_openingCone_l80 facts S Sched x v hsync hmono hawake hgst hcv hvalid
        hawm hthird hcom hlen htd hN hreg harW hn₀ htop hP hTB
        (Restated.namedHonestVotesConeOn_of_preceq_l78 facts hBX (hPu D hD hemit g hg Bk hBk))

end

section
set_option autoImplicit false
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

/-- Given the hypotheses of `gradedBlock_cone_at_secondSlot`: for a validator `v'` in
    `notHeldAt Sched` at `S.a rW` and a node state `n` of its round-`rW` action read whose grade-2
    selection can return `some Q`, every committee member of `opening_slot rW + 1` in
    `notHeldAt Sched` at its vote instant votes along the path a run block descending from `Q`. -/
theorem nodeQ2Tier_cone_at_secondSlot (facts : Record.Facts M)
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
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    (hP : ∀ nprev : V → M.N,
      (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
        (Restated.switchRound M S tE - 1)) →
      Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) nprev)
    (hprev : a.round = Restated.switchRound M S tE →
      Restated.BasePreviousRoundSGCompatibleWithAnchor M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) T)
    {v' : V} (hv' : v' ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {n : M.N}
    (hnA : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v')
        (Restated.switchRound M S tE))
    {Q : Block V}
    (hQ : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M (Setup.alwaysAwake S) n
      (Restated.switchRound M S tE) ⇢ some Q) :
    Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) (notHeldAt Sched) Finset.univ
      ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) (fun X => Block.Preceq Q X) := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hrWN : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (x[N].time : Int) := by
    rw [hN]; exact Restated.action_le_confirmation_third facts S _
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
  obtain ⟨hpredle, hrW1⟩ := pred_le_pred_pos_l74 a.round (Restated.switchRound M S tE) hapos harW
  have hloOpenRW : tGAT + 1 ≤ M.opening S.E S.hc (Restated.switchRound M S tE - S.hc.η_SG) :=
    hlo.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le_sub_right harW _))
  have hvG0 : v' ∈ notHeldAt Sched (M.domain S.E S.hc (Restated.switchRound M S tE) .g0) :=
    hHs _ _ (facts.gr.domain_le_a S _ .g0) hv'
  have hhorA : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE)) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    exact hrWN
  have hG1 := Restated.namedG1At_of_nodeQ2On facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
    hHs hHsXb hrW1 hhorA hloOpenRW v' hvG0 Q n hnA hQ
  exact Restated.gradedBlock_cone_at_secondSlot facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm
    hthird hcom hlen htd hN hreg harW hn₀ htop hP hprev hv' (p := .g1)
    (facts.gr.domain_le_a S _ .g1)
    ((p65% storeGrade_true_of_all₆₅) facts (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc _
      (Restated.switchRound M S tE) .g1 Q hG1)

end

section
set_option autoImplicit false
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

/-- Given the hypotheses of `gradedBlock_cone_at_secondSlot`: for a validator `v'` in
    `notHeldAt Sched` at `S.a rW`, every node state `n` of its round-`rW` action read and every
    anchor `A` of `n` at round `rW`, every committee member of `opening_slot rW + 1` in
    `notHeldAt Sched` at its vote instant votes along the path a run block descending from `A`. -/
theorem anchorTier_cone_at_secondSlot (facts : Record.Facts M)
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
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    (hP : ∀ nprev : V → M.N,
      (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
        (Restated.switchRound M S tE - 1)) →
      Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) nprev)
    (hprev : a.round = Restated.switchRound M S tE →
      Restated.BasePreviousRoundSGCompatibleWithAnchor M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) T)
    {v' : V} (hv' : v' ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v')
        (Restated.switchRound M S tE),
    ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M (Setup.alwaysAwake S) n
        (Restated.switchRound M S tE) ⇢ A →
    Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) (notHeldAt Sched) Finset.univ
      ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)
      (fun X => Block.Preceq A X) := by
  intro n hnA A hA
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hrWN : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (x[N].time : Int) := by
    rw [hN]; exact Restated.action_le_confirmation_third facts S _
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hmemA := (p69b% mem_stateBeforeTime_along₆₉b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE))
  rcases Restated.actionAnchor_cases_l80 facts (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      v' (Restated.switchRound M S tE) n ⟨_, hmemA, hnA⟩ A hA with
    hfg | ⟨root, L, hframe, hactive, hAL⟩
  · rw [hfg]
    exact Restated.namedHonestVotesConeOn_of_preceq_l78 facts
      (Restated.actionFgRoot_preceq_checkpoint_at_switchRound facts S Sched x v hsync hmono hawake hgst hcv
        hvalid hawm hthird hcom hlen htd hN hreg harW hn₀ htop v' hv' n hnA)
      (Restated.checkpointCone_at_secondSlot facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm hthird
        hcom hlen htd hN hreg harW)
  · rw [hAL]
    have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
      fun _ _ h => notHeldAt_anti hmono h
    obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
    have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
    have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
    obtain ⟨hpredle, hrW1⟩ := pred_le_pred_pos_l74 a.round (Restated.switchRound M S tE) hapos harW
    have hloOpenRW : tGAT + 1 ≤ M.opening S.E S.hc (Restated.switchRound M S tE - S.hc.η_SG) :=
      hlo.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le_sub_right harW _))
    have hgatG2 : tGAT + 1 ≤ M.domain S.E S.hc (Restated.switchRound M S tE) .g2 :=
      (facts.gr.lo_le_early_g2_of_window_start S hrW1 hloOpenRW).trans
        (facts.gr.early_le_domain S _)
    have hgat : tGAT + 1 ≤ M.domain S.E S.hc (Restated.switchRound M S tE) .g1 :=
      hgatG2.trans (facts.gr.domain_g2_le_domain_g1 S (Restated.switchRound M S tE))
    have hvG1 : v' ∈ notHeldAt Sched (M.domain S.E S.hc (Restated.switchRound M S tE) .g1) :=
      hHs _ _ (facts.gr.domain_le_a S _ .g1) hv'
    have hhorA : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE)) ≤
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V).horizon := by
      show _ ≤ (x[N].time : Int)
      exact hrWN
    have hG1 := Restated.activeActionAnchor_storeGrade_g1_actionHistoryOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf hrW1 hhorA hvG1 n hnA hframe hactive hgat
    exact Restated.gradedBlock_cone_at_secondSlot facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm
      hthird hcom hlen htd hN hreg harW hn₀ htop hP hprev hv' (p := .g1)
      (facts.gr.domain_le_a S _ .g1)
      ((p65% storeGrade_true_of_all₆₅) facts (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc _
        (Restated.switchRound M S tE) .g1 L hG1)

end

section
set_option autoImplicit false
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

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE`, `hP`
    and `hprev`: the round-`rW` SG blocks of any two validators in `notHeldAt Sched` at `S.a rW` lie
    on one chain (`BaseSGOneChainAtSwitchRound`). -/
theorem baseSGOneChainAtSwitchRound_of_prevCompatible (facts : Record.Facts M)
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
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    (hP : ∀ nprev : V → M.N,
      (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
        (Restated.switchRound M S tE - 1)) →
      Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) nprev)
    (hprev : a.round = Restated.switchRound M S tE →
      Restated.BasePreviousRoundSGCompatibleWithAnchor M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) T) :
    Restated.BaseSGOneChainAtSwitchRound M S Sched x v tE N := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hmemA := (p69b% mem_stateBeforeTime_along₆₉b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE))
  unfold Restated.BaseSGOneChainAtSwitchRound
  refine Restated.honestActionCarriersOneChainAt_of_secondSlotConeOn facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs hcomOn ?_
  intro v' hv' n hnA g2 hg2 Bv hBv
  obtain ⟨gr, hgr⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) (Setup.alwaysAwake S).E
    (Setup.alwaysAwake S).hc n.st.core.toHealing (Restated.switchRound M S tE)
  rcases Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_tiers facts (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      v' (Restated.switchRound M S tE) n ⟨_, hmemA, hnA⟩ gr hgr g2 hg2 Bv hBv with
    ⟨-, hclear, -⟩ | ⟨Q, hQ, hEq⟩ | ⟨-, -, hEq⟩ | ⟨-, -, hEq⟩
  · exact Restated.clearTier_cone_at_secondSlot facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm
      hthird hcom hlen htd hN hreg harW hn₀ htop hP hv' hnA hg2 hBv hclear
  · rw [hEq]
    have hQ' := (p77% returns_map_intro₇₇) (fun g : Protocol.GradeRead V => g.Q2) _ gr hgr
    rw [hQ] at hQ'
    exact Restated.nodeQ2Tier_cone_at_secondSlot facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm
      hthird hcom hlen htd hN hreg harW hn₀ htop hP hprev hv' hnA hQ'
  · refine Restated.fgRootTier_cone_at_secondSlot facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm
      hthird hcom hlen htd hN hreg harW hn₀ htop hv' hnA hg2 hBv ?_
    rw [hEq]
    exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)
  · rw [hEq]
    exact Restated.anchorTier_cone_at_secondSlot facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm
      hthird hcom hlen htd hN hreg harW hn₀ htop hP hprev hv' n hnA gr.anchor
      ((p77% returns_map_intro₇₇) (fun g : Protocol.GradeRead V => g.anchor) _ gr hgr)

end

section
set_option autoImplicit false
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

/-- If `roundAt M S tGAT + η_SG + 2 ≤ rW`, then `tGAT + 1` is at or before one delay before round
    `rW`'s grade-1 window start. -/
private theorem win_g1_of_regime₈₀w (facts : Record.Facts M) (S : Setup V) {tGAT : Int}
    {rW : Round} (h : Restated.roundAt M S tGAT + S.hc.η_SG + 2 ≤ rW) :
    tGAT + 1 ≤ M.early S.E S.hc rW .g1 - S.E.Δ := by
  have h1 : Restated.roundAt M S tGAT + 1 < Restated.roundAt M S tGAT + S.hc.η_SG + 2 := by
    rw [Nat.add_assoc]
    exact Nat.add_lt_add_left (Nat.lt_add_left S.hc.η_SG Nat.one_lt_two) _
  have hlt : Restated.roundAt M S tGAT + 1 < rW := lt_of_lt_of_le h1 h
  have hA1 : tGAT + 1 ≤
      Restated.Vocabulary.Execution.Setup.a M S (Restated.roundAt M S tGAT + 1) :=
    Int.add_one_le_iff.mpr (lt_of_le_of_lt (Restated.Vocabulary.Statements.roundAt_spec facts S tGAT)
      (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S (Nat.lt_succ_self _)))
  have hA1' : tGAT + 1 ≤ M.a S.hc S.E.Δ (Restated.roundAt M S tGAT + 1) := hA1
  have h2 := facts.gr.action_delta_le_early S S.hc.R_ge_three hlt
  have h3 := facts.gr.q10_early_g2_le_early_g1 S rW
  linarith

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE` and
    source round `rW`: if the round-`(rW − 1)` SG blocks of the emitting validators in
    `notHeldAt Sched` at `S.a (rW − 1)` are ancestors of every opening-slot vote of `rW` by a
    committee member in `notHeldAt Sched` at its vote instant (`hP`), then every such SG block is on
    one chain with `T` (`BasePreviousRoundSGCompatibleWithAnchor`). -/
theorem basePreviousRoundSGCompatibleWithAnchor_of_belowOpeningVotes (facts : Record.Facts M)
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
    (harW : a.round = Restated.switchRound M S tE)
    (hP : ∀ nprev : V → M.N,
      (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
        (Restated.switchRound M S tE - 1)) →
      Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) nprev) :
    Restated.BasePreviousRoundSGCompatibleWithAnchor M S Sched x v tE N
      (Restated.runAllPath M S Sched x v N) T := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
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
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
  obtain ⟨-, hloVote, -, -⟩ := Restated.loBounds_l70 facts S hapos hlo
  have hoPos : 0 < (M.opening_slot S.hc (Restated.switchRound M S tE)) :=
    facts.gr.opening_slot_pos_of_round_pos S.hc (lt_of_lt_of_le hapos harW.le)
  have hSc : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) =
      M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) := by
    rw [Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time]
  have hcut : M.support_cutoff S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) := by
    rw [hSc]
    exact facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _
  have hpostVote : tGAT + 1 ≤ M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) := by
    rw [← harW]
    exact hloVote
  have hwinW : tGAT + 1 ≤ M.early S.E S.hc
      (M.round_of S.hc (M.opening_slot S.hc (Restated.switchRound M S tE))) .g1 - S.E.Δ := by
    rw [facts.gr.round_of_opening_slot_eq S.hc _]
    have h := Restated.NamedHeightRegimeRunOn.r0_le_round_l71 facts hf hreg
    rw [harW] at h
    exact win_g1_of_regime₈₀w facts S h
  have hrunY : ∀ y ∈ notHeldAt Sched (M.vote_time S.E (M.opening_slot S.hc (Restated.switchRound M S tE))),
      ∀ j : Nat, ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
          Record.Run V).events[j]? =
        some (Record.Event.tick y (M.vote_time S.E (M.opening_slot S.hc (Restated.switchRound M S tE)))) →
      M.awake_for_grade1 (Setup.alwaysAwake S) y (Restated.runAllPath M S Sched x v N j y)
        (M.round_of S.hc (M.opening_slot S.hc (Restated.switchRound M S tE))) :=
    fun y hy j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hy hwinW
  have hconfHor : M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hN]
    exact facts.sch.confirmation_time_mono_l78 S (Nat.le_add_right _ 2)
  have hvoteHorO : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon :=
    (facts.sch.Protocol_vote_time_le_confirmation_time S.E _).trans hconfHor
  have hTCfg : Block.Preceq T.erase Cfg.erase := by
    rw [hreg.seed.checkpointDerived]
    exact facts.csAdded.derive_named_T_h_preceq S.E S.cfg Cfg
  have htail : ∀ y ∈ notHeldAt Sched
      (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))),
      y ∈ S.E.committee ((M.opening_slot S.hc (Restated.switchRound M S tE))) →
      ∀ (H : Block V) (Hy : NamedBlock V), Hy.erase = H →
      Restated.RunBlockOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N) Finset.univ Hy →
      Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N) y
        (NamedObject.gfVote ⟨y, (M.opening_slot S.hc (Restated.switchRound M S tE)), H.root⟩)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))) →
      Block.Preceq T.erase H →
      Restated.BasePreviousRoundSGCompatibleWithAnchor M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) T := by
    intro y hyVote hycomm H Hy hHyErase hHyRun hHyEmit hTy
    unfold Restated.BasePreviousRoundSGCompatibleWithAnchor
    intro u hu nu hnu D hD hemit gc stu k A2' hA2' G' hG'
    obtain ⟨nprev, hnprev, hnprevu⟩ := exists_actionReads_choice₈₀ facts (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))))
      (Restated.switchRound M S tE - 1) u nu hnu
    have hPu := hP nprev hnprev u hu
    rw [hnprevu] at hPu
    obtain ⟨X, hXu, hXrun, hXemit⟩ := hPu D hD hemit A2' hA2' G' hG' y hyVote hycomm
    have hXH : X.erase = Hy.erase :=
      Restated.runBlock_eq_of_root_eqOn facts _ Finset.univ hf.rootCollisionFree hXrun hHyRun (by
        rw [hHyErase]
        exact congrArg GoldfishVote.head
          (Restated.emits_gfVote_uniqueOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hXemit
            hHyEmit rfl))
    rw [hXH, hHyErase] at hXu
    exact compatible_of_preceq_common_Preceq hXu hTy
  have hmemWa := (p69b% mem_stateBeforeTime_along₆₉b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round)
  obtain ⟨na, hna⟩ := (p73% actionReadFrom_nonempty₇₃) facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round)) a.val_index) a.round
  obtain ⟨oQ, hoQ⟩ := (p70% nodeQ2_nonempty₇₀w) facts (Setup.alwaysAwake S) na a.round
  obtain ⟨Q, hQeq⟩ := hreg.seed.exists_nodeQ2_l70 facts na hna oQ hoQ
  rw [hQeq] at hoQ
  obtain ⟨oB, hoB⟩ := (p63% actionFGSource_nonempty₆₃w) facts (Setup.alwaysAwake S) na
  rw [hreg.seed.exactFGSource na hna oB hoB] at hoB
  have hsplit := Restated.Vocabulary.Proofs.HealingSurface.actionFGSource_genuineClear_or_selectedG2_named facts
    (Setup.alwaysAwake S) _ a.val_index a.round _ hmemWa na hna hoQ hoB
  rcases hsplit with ⟨Ca, hCa, -, -, -, hCfgCa⟩ | hCfgQ
  · -- case: `Cfg` is a clear block, an ancestor of the confirmation `Ca` (satisfying `GenuineConfirmation`)
    have hsigner : a.val_index ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) := by
      have h := hreg.seed.signerHonest
      rw [hreg.seed.actionTime_eq, harW] at h
      exact h
    obtain ⟨ca, hca, sta, -, rfl⟩ := hna
    rw [facts.nd.mkNode_cache] at hCa
    have hca' : M.onPhaseTick S.E S.hc
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index).st.core.toHealing
        (Restated.Vocabulary.Execution.Setup.a M S a.round)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index).cache ⇢ ca := hca
    have hCa' : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract ca) S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M (Setup.alwaysAwake S)
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index).st.core
          (M.confirmation_time S.E (M.opening_slot S.hc a.round)))
        (M.opening_slot S.hc a.round) Ca := hCa
    rw [harW, hSc] at hca' hCa'
    obtain ⟨y, hy, hycomm, hCy⟩ :=
      Restated.genuineConfirmation_exists_honestVoteSupporter_ceilingOn facts (Setup.alwaysAwake S)
        (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn (hHs _ _ hcut hsigner) hoPos hpostVote
        hconfHor ca hca' hCa'
        (fun y _ hy j hj => hrunY y
          (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hy) j hj)
    have hyVote : y ∈ notHeldAt Sched
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))) :=
      hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hy
    obtain ⟨cc, hcc, Tr, hTr, L, hL, L', hL', H, hH⟩ := (p78% exists_voteHead₇₈) facts (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))) y)
      ((M.opening_slot S.hc (Restated.switchRound M S tE)))
    obtain ⟨Hy, hHyErase, hHyRun⟩ := Restated.seedVoteDutyHead_runBlockOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf (hHsXb _ hyVote) ((M.opening_slot S.hc (Restated.switchRound M S tE)))
      cc hcc Tr hTr L hL L' hL' H hH
    have hHyEmit := Restated.seedVoteDutyHead_emitsOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
      hf hyVote hoPos hycomm hvoteHorO hpostVote cc hcc (hrunY y hyVote) Tr hTr L hL L' hL' H hH
    exact htail y hyVote hycomm H Hy hHyErase hHyRun hHyEmit
      (preceq_trans_Preceq (preceq_trans_Preceq hTCfg hCfgCa) (hCy cc hcc Tr hTr L hL L' hL' H hH))
  · -- case: `Cfg` is the selected grade-2 block
    rw [← hCfgQ] at hoQ
    have hpositive : 0 < (((Setup.alwaysAwake S).E.committee
        ((M.opening_slot S.hc (Restated.switchRound M S tE)))) ∩
        notHeldAt Sched (M.confirmation_time (Setup.alwaysAwake S).E
          ((M.opening_slot S.hc (Restated.switchRound M S tE))))).card := by
      have hc := hcomOn ((M.opening_slot S.hc (Restated.switchRound M S tE)))
      omega
    obtain ⟨y, hyI⟩ := Finset.card_pos.mp hpositive
    have hycomm : y ∈ S.E.committee ((M.opening_slot S.hc (Restated.switchRound M S tE))) :=
      (Finset.mem_inter.mp hyI).1
    have hyVote : y ∈ notHeldAt Sched
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))) :=
      hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) (Finset.mem_inter.mp hyI).2
    have hyA : y ∈ notHeldAt Sched
        (M.vote_time S.E ((M.opening_slot S.hc a.round))) := by
      rw [harW]
      exact hyVote
    have hCfgy := hreg.seed.selectedSource_preceq_openingHead_of_namedFrame_history facts hf hHs
      hHsXb hX hXXb hreg.crossing hreg.frame hreg.ready hna hoQ hyA hlo
    rw [harW] at hCfgy
    obtain ⟨cc, hcc, Tr, hTr, L, hL, L', hL', H, hH⟩ := (p78% exists_voteHead₇₈) facts (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))) y)
      ((M.opening_slot S.hc (Restated.switchRound M S tE)))
    obtain ⟨Hy, hHyErase, hHyRun⟩ := Restated.seedVoteDutyHead_runBlockOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf (hHsXb _ hyVote) ((M.opening_slot S.hc (Restated.switchRound M S tE)))
      cc hcc Tr hTr L hL L' hL' H hH
    have hHyEmit := Restated.seedVoteDutyHead_emitsOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
      hf hyVote hoPos hycomm hvoteHorO hpostVote cc hcc (hrunY y hyVote) Tr hTr L hL L' hL' H hH
    exact htail y hyVote hycomm H Hy hHyErase hHyRun hHyEmit
      (preceq_trans_Preceq hTCfg (hCfgy cc hcc Tr hTr L hL L' hL' H hH))

end

section
set_option autoImplicit false
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

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE` and
    `hP`: the round-`rW` SG blocks of any two validators in `notHeldAt Sched` at `S.a rW` lie on one
    chain (`BaseSGOneChainAtSwitchRound`). -/
theorem baseSGOneChainAtSwitchRound_of_premises (facts : Record.Facts M)
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
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    (hP : ∀ nprev : V → M.N,
      (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
        (Restated.switchRound M S tE - 1)) →
      Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) nprev) :
    Restated.BaseSGOneChainAtSwitchRound M S Sched x v tE N :=
  Restated.baseSGOneChainAtSwitchRound_of_prevCompatible facts S Sched x v hsync hmono hawake hgst hcv hvalid
    hawm hthird hcom hlen htd hN hreg harW hn₀ htop hP
    (fun heq => Restated.basePreviousRoundSGCompatibleWithAnchor_of_belowOpeningVotes facts S Sched x v hsync
      hmono hawake hgst hcv hvalid hawm hthird hcom hlen htd hN hreg heq hP)

end

end DecoupledConsensusModel.Sts.Restated
