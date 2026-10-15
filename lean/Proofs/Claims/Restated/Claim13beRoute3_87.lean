import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Claim13beRoute3_54b
import Proofs.Claims.Restated.Claim13beRoute3_63
import Proofs.Claims.Restated.Claim13beRoute3_69b
import Proofs.Claims.Restated.Claim13beRoute3_70
import Proofs.Claims.Restated.Claim13beRoute3_70b
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_86b
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_OutageInputs
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Execution_StoreFinalityCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Ladder
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Proofs.Claims.Restated.Vocabulary_Protocol_Store_BoundaryRows
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Proofs.Vocabulary.Protocol.Grades.RelativeOneChain
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# FG roots and SG blocks after the recovery deadline

Theorems over a model `M : Record.Model V`, read along one path `W` of the run: the honest SG blocks
of a run-scoped named regime are on one chain with its checkpoint, a reader's FG root is on one
chain with every honest SG block of a round after the deadline, and the relative carrier window
holds after the recovery deadline.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas

local macro "p63% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_63)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- The round-`r` action read computed from `before` can give some node state. -/
private theorem actionReadFrom_nonempty₈₇n (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

/-- For a run-scoped named regime along `W` with `lo ≤ opening (a.round − η_SG)`, every round
    `c ≥ a.round` with `S.a c` in the horizon has every SG block that a member of the set for
    `S.a c` emitting its round-`c` action attestation can select on one chain with the regime's
    checkpoint `T`. -/
theorem NamedHeightRegimeRunOn.sgHistory_run_l87 (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    (h : Restated.NamedHeightRegimeRunOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb r0 blocked first i a ta Cfg T Tprev c0)
    {c : Round} (hc : a.round ≤ c)
    (hhor : Restated.Vocabulary.Execution.Setup.a M S c ≤ rho.horizon)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs c T.erase := by
  rcases eq_or_lt_of_le hc with hceq | hlt
  · rw [← hceq]
    exact Restated.PrefixFGSelectorConeAtOn.sgEmissionsCompatible_of_source_of_frame_named facts
      hf hHs hHsXb hX hXXb hcom h.seed h.crossing h.frame h.c0le h.ready h.postPrev hlo
  · exact ((Restated.NamedHeightRegimeRunOn.laterHistory_main facts hf hHs hHsXb hX hXXb
      hcom hbelow h (Nat.succ_le_of_lt hlt) hlo hA).2 hhor).1

/-- Given a run-scoped named base along `W` whose first crossing is by `S.a deadline`, for a round
    `c` at or after `deadline` and a `read` between `S.a deadline` and `S.a (c + 1)` within the
    horizon, the FG root of `u`'s store in `W` before `read` is on one chain with every SG block
    that `v`'s round-`c` action read along `W` can select, for `u` in the set for `read` and `v` in
    the set for `S.a c + Δ`. -/
theorem NamedHeightRegimeBaseRunOn.fgRoot_compatible_actionSGBlock_at_read_after_deadline
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height} {first : Nat} {Tprev : NamedBlock V}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    (hgst : gstLagged S ≤ Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (h : Restated.NamedHeightRegimeBaseRunOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb r0 blocked first Tprev)
    {deadline : Round}
    (hdeadline : first ≤
      inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S deadline))
    {c : Round} (hc : deadline ≤ c)
    (hhor : Restated.Vocabulary.Execution.Setup.a M S c ≤ rho.horizon)
    {read : Time} (hread : Restated.Vocabulary.Execution.Setup.a M S deadline ≤ read)
    (hreadHor : read ≤ rho.horizon)
    (hnext : read ≤ Restated.Vocabulary.Execution.Setup.a M S (c + 1))
    {u v : V} (hu : u ∈ Hs read)
    (hv : v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S c + S.E.Δ))
    (hgstLo : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c,
    ∀ A2 : Option (Block V),
      M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2 →
    ∀ G : Block V,
      M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ G →
      Block.compatible
        (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) G =
          true := by
  intro n hn A2 hA2 G hG
  have hmajority : HonestWeightMajorityOn S rho Hs :=
    honestWeightMajorityOn_of_belowOneThirdOn hbelow
  have hvA : v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S c) :=
    hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) hv
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract n.cache) S.E S.hc (S.node v)
    n.st n.record
  rcases Restated.fgRoot_confirmationWitness_at_readOn facts S Hs Xb hf hHs hHsXb hmajority
      (hHsXb _ hu) read hreadHor with
    hgen | ⟨C, hC, hJ, b, tb, hb, hemit, hbt, hpair, hW⟩
  · rw [hgen]
    exact compatible_of_cases (Or.inl (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _)))
  · by_cases hsmall : (M.derive_named S.E S.cfg C).h_j ≤ blocked
    · obtain ⟨i, a, ta, Cfg, T, hreg, ha⟩ :=
        Restated.NamedHeightRegimeBaseRunOn.exists_regime_before_deadline facts hf hHs
          hHsXb hX hXXb hbelow hgst h hgstLo hloOpen hdeadline
      have hlo := Restated.NamedHeightRegimeRunOn.lo_le_opening_l71 facts hf hreg hloOpen
      have hac : a.round ≤ c := ha.trans hc
      have hRT := Restated.NamedHeightRegimeRunOn.fgRoot_compatible_after_source_run_l86b
        facts hf hHs hHsXb hX hXXb hcom hbelow hreg
        (((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone ha).trans
          hread) hreadHor hu hlo hA
      have hRTpre : Block.Preceq
          (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG)
          T.erase := by
        by_cases hz : (M.derive_named S.E S.cfg C).h_j = 0
        · have hgenJ := facts.cs.justified_zero_is_genesis S.E S.cfg C hz
          rw [← hJ, hgenJ]
          exact (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _))
        · obtain ⟨J, hJC, hJerase, hJheight⟩ :=
            (facts.cs.justified_ancestor_height S.E S.cfg C).resolve_left hz
          have hCrun : Restated.RunBlockOn M S rho W Xb C :=
            Restated.lifecycle_runBlock_of_mem_storeBeforeTimeOn facts S Hs Xb hf (hHsXb _ hu) hC
          have hJrun : Restated.RunBlockOn M S rho W Xb J :=
            Restated.blockInRun_of_ancestorOn facts S rho W Xb hCrun hJC
          obtain ⟨hTrun, hTheight⟩ :=
            Restated.NamedHeightRegimeRunOn.checkpoint_runBlock facts hf hHsXb hreg
          rcases (show Block.Preceq
                (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG)
                T.erase ∨
              Block.Preceq T.erase
                (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) from
            compatible_cases hRT) with
            hRT' | hTR
          · exact hRT'
          · have hTJ : NamedBlock.Preceq T J :=
              Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hTrun hJrun
                (by rw [hJerase, hJ]; exact hTR)
            have hmono := facts.cs.derive_height_mono S.E S.cfg hTJ
            rw [hTheight, hJheight] at hmono
            exact False.elim (Nat.not_succ_le_self blocked (hmono.trans hsmall))
      have hloc : lo ≤ Restated.Vocabulary.Execution.Setup.a M S c :=
        (Restated.loBounds_l70 facts S (hreg.seed.round_pos_l70 facts hf) hlo).2.2.2.trans
          (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hac)
      have hSG : G.compatible T.erase = true :=
        Restated.NamedHeightRegimeRunOn.sgHistory_run_l87 facts hf hHs hHsXb hX
          hXXb hcom hbelow hreg hac hhor hlo hA v hvA n hn D hD
          (Restated.honest_emits_exact_actionAttestationAtOn facts S Hs Xb hf c hvA hhor hloc
            (hA c (Restated.lo_le_early_g2_sub_delta_of_opening facts S
              (hreg.seed.round_pos_l70 facts hf) hlo hac) v hv)
            (fun j hj => hf.tick_outcome j _ _ hj) n hn D hD) A2 hA2 G hG
      rcases (show Block.Preceq G T.erase ∨ Block.Preceq T.erase G from
        compatible_cases hSG) with
        hBT | hTB
      · exact compatible_of_preceq_common_Preceq hRTpre hBT
      · exact compatible_of_cases (Or.inl (preceq_trans_Preceq hRTpre hTB))
    · let m := (M.derive_named S.E S.cfg C).h_j - (blocked + 1)
      have heq : blocked + m + 1 = (M.derive_named S.E S.cfg C).h_j := by
        calc
          _ = m + (blocked + 1) := by ac_rfl
          _ = (M.derive_named S.E S.cfg C).h_j :=
            Nat.sub_add_cancel (Nat.lt_of_not_ge hsmall)
      have hrow : b.height_pair.erase.height? = some (blocked + m + 1) := by
        rw [hpair]
        exact congrArg some heq.symm
      have hbT : b.val_index ∈ Hs tb := hHs _ _ hbt.le hb
      obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
        Restated.NamedHeightRegimeBaseRunOn.exists_regime_of_row_named facts hf hHs hHsXb
          hX hXXb hcom hbelow hgst h m hbT hemit hrow hgstLo hloOpen hA
      have hlo := Restated.NamedHeightRegimeRunOn.lo_le_opening_l71 facts hf hreg hloOpen
      obtain ⟨nb, hnb⟩ := actionReadFrom_nonempty₈₇n facts S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index)
        b.round
      obtain ⟨o, ho⟩ := (p63% actionFGSource_nonempty₆₃w) facts S nb
      have hTR : T.erase =
          M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG :=
        (Option.some.inj
          (Restated.NamedHeightRegimeRunOn.witness_eq facts hf hHs hHsXb hX hXXb hcom
            hbelow hreg hbT hemit hrow hlo hA nb hnb _ (hW nb hnb o ho))).symm
      have hbc : b.round ≤ c := by
        have hact : Restated.Vocabulary.Execution.Setup.a M S b.round <
            Restated.Vocabulary.Execution.Setup.a M S (c + 1) := by
          rw [← (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath
            hemit).2]
          exact hbt.trans_le hnext
        exact Nat.le_of_lt_succ
          ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).lt_iff_lt.mp hact)
      have hac : a.round ≤ c := (hreg.minimal b tb hbT hemit hrow).trans hbc
      have hloc : lo ≤ Restated.Vocabulary.Execution.Setup.a M S c :=
        (Restated.loBounds_l70 facts S (hreg.seed.round_pos_l70 facts hf) hlo).2.2.2.trans
          (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hac)
      have hSG : G.compatible T.erase = true :=
        Restated.NamedHeightRegimeRunOn.sgHistory_run_l87 facts hf hHs hHsXb hX
          hXXb hcom hbelow hreg hac hhor hlo hA v hvA n hn D hD
          (Restated.honest_emits_exact_actionAttestationAtOn facts S Hs Xb hf c hvA hhor hloc
            (hA c (Restated.lo_le_early_g2_sub_delta_of_opening facts S
              (hreg.seed.round_pos_l70 facts hf) hlo hac) v hv)
            (fun j hj => hf.tick_outcome j _ _ hj) n hn D hD) A2 hA2 G hG
      rw [← hTR]
      exact compatible_of_cases (compatible_cases hSG).symm

/-- For a round `c` at or after the progress deadline from `rGST` and a `read` between the
    deadline's action instant and `S.a (c + 1)` within the horizon, the FG root of the store of `u`,
    in the set for `read`, in the world of `W` before `read` is on one chain with every SG block
    that the round-`c` action read along `W` of `v`, in the set for `S.a c + Δ`, can select. -/
theorem fgRoot_compatible_actionSGBlock_at_read_after_GSTOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int}
    (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon)
    {read : Time}
    (hread : (Restated.Vocabulary.Execution.Setup.a M S
      (fgSafetyProgressDeadline S rho rGST gap delayExtra)) ≤ read)
    (hreadHor : read ≤ rho.horizon)
    (hnext : read ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)))
    {u v : V} (hu : u ∈ Hs read)
    (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c) + S.E.Δ))
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c,
    ∀ A2 : Option (Block V),
      M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2 →
    ∀ G : Block V,
      M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ G →
      Block.compatible
        (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) G =
          true := by
  have hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ Xb := fun t _ => hHsXb t
  have hXXb : Xb ⊆ Xb := Finset.Subset.refl _
  have hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)) :=
    hloPost.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_add_right rGST 2))
  obtain ⟨blocked, first, Tprev, hfirst, hbase⟩ :=
    Restated.exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadlineOn facts
      S Hs Xb Xb hf hHs hHsXb hX hXXb hcom hbelow hrec hdelay hpost (hread.trans hreadHor)
      hlo hloOpen ht₀ hA
  exact Restated.NamedHeightRegimeBaseRunOn.fgRoot_compatible_actionSGBlock_at_read_after_deadline
    facts hf hHs hHsXb hX hXXb hcom hbelow
    (Restated.Vocabulary.Proofs.HealingSurface.gstLagged_le_Γ_neg1_of_gst_le_a facts S rGST hpost)
    hbase hfirst hc hhor hread hreadHor hnext hu hv
    (Restated.lo_add_lag_le_Γ_neg1_l71 facts S rGST hloPost) hloOpen hA

/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_62` by name. -/
local macro "p62% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_62)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- The relative carrier window along `W` holds at every round `r` at or after the progress deadline
    from `rGST` and every phase `p`: a round-`r` voter `u` still in the set for round `(r + 1)`'s
    early phase-`p` cutoff has, for every SG block `A` its action read can select, an interpreted
    input at `w`'s store before the phase-`p` domain instant of round `r + 1` confirming `A`'s root,
    and `A` is in that store's tree. -/
theorem relativeCarrierWindowAt_after_recovery_deadlineOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int}
    (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {r : Round} (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ r)
    {p : Phase} (hhor : M.domain S.E S.hc (r + 1) p ≤ rho.horizon)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Restated.RelativeCarrierWindowAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs r p := by
  have hqr : r < r + 1 := Nat.lt_succ_self r
  have hk : r ∈ M.latest_window S.hc.η_SG (r + 1) := by
    apply facts.fc.mem_latest_window
    · simpa only [Nat.add_sub_cancel] using
        (Nat.sub_le_sub_left S.hc.η_SG_ge_one (r + 1))
    · exact hqr
  have hactionDelta : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤
      M.early S.E S.hc (r + 1) p := by
    apply (facts.gr.action_delta_le_early S S.hc.R_ge_three hqr).trans
    exact Restated.early_g2_le_early facts S (r + 1) p
  have horder : M.early S.E S.hc (r + 1) p ≤ M.domain S.E S.hc (r + 1) p := by
    exact (le_add_of_nonneg_right (by linarith [S.E.Δ_pos])).trans
      (facts.gr.early_add_two_delta_le_domain S (r + 1) p)
  have hcut : M.early S.E S.hc (r + 1) p ≤ rho.horizon := horder.trans hhor
  have hactionDomain : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ M.domain S.E S.hc (r + 1) p :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans (hactionDelta.trans horder)
  have hsourceHor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon :=
    hactionDomain.trans hhor
  have hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    hloPost.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
      (le_trans (by
        unfold fgSafetyProgressDeadline
        exact (Nat.le_add_right rGST 1).trans (Nat.le_add_right (rGST + 1) _)) hr))
  have hrGSTlt : rGST < fgSafetyProgressDeadline S rho rGST gap delayExtra := by
    unfold fgSafetyProgressDeadline
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self rGST) (Nat.le_add_right (rGST + 1) _)
  have hloEarlyR : lo ≤ M.early S.E S.hc r .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloPost (Nat.lt_of_lt_of_le hrGSTlt hr)
  have hdeadline : max ((Restated.Vocabulary.Execution.Setup.a M S r)) lo + S.E.Δ ≤
      M.early S.E S.hc (r + 1) p := by
    rw [max_eq_left hlo]
    exact hactionDelta
  have hread : (Restated.Vocabulary.Execution.Setup.a M S
      (fgSafetyProgressDeadline S rho rGST gap delayExtra)) ≤ M.domain S.E S.hc (r + 1) p :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hr).trans
      hactionDomain
  have hnext : M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    facts.gr.domain_le_a S (r + 1) p
  intro w hw u hu huEarly na hna g2 hg2 A hAsel I hI
  have huDelta : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ) :=
    hHs _ _ hactionDelta huEarly
  have huHon : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)) :=
    ((Restated.honestRoundVoters_iffOn facts S rho W hf.onePath Hs u r).mp hu).1
  have huXb : u ∈ Xb := hHsXb _ huHon
  have hwEarly : w ∈ Hs (M.early S.E S.hc (r + 1) p) := hHs _ _ horder hw
  have hrootCompat : Block.compatible
      (M.get_fg_root
        (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core).toFG)
      A = true :=
    Restated.fgRoot_compatible_actionSGBlock_at_read_after_GSTOn facts S Hs Xb hf hHs hHsXb
      hcom hbelow hrec hdelay hpost hr hsourceHor hread hhor hnext hw huDelta hloPost hloOpen
      ht₀ hA na hna g2 hg2 A hAsel
  have hwmem := (p62% mem_stateBeforeTime_along₆₂s) hf.sorted hf.onePath
    (M.domain S.E S.hc (r + 1) p)
  have humem := (p62% mem_stateBeforeTime_along₆₂s) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hFroot : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core.F
      (M.get_fg_root
        (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core).toFG) :=
    Restated.Vocabulary.Proofs.StoreFinality.finalized_preceq_fgRoot facts
      (preceq_eq_true_iff_Preceq.mpr
        (Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts
          S rho (M.domain S.E S.hc (r + 1) p) w _ hwmem))
  have hcompat : Block.compatible
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core.F A = true := by
    rcases compatible_cases hrootCompat with hrootCarrier | hcarrierRoot
    · exact compatible_of_cases (Or.inl (preceq_trans_Preceq hFroot hrootCarrier))
    · exact compatible_of_preceq_common_Preceq hFroot hcarrierRoot
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract na.cache) S.E S.hc (S.node u)
    na.st na.record
  set a := D.2.2 with ha
  have hshape : a.val_index = u ∧ a.round = r ∧ a.confirmed = some A.root :=
    Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts S rho u r na
      ((p62% mem_actionReadAt_along₆₂s) hf.sorted hf.onePath u r hna) D hD g2 hg2 A hAsel
  have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W u (Object.attest a)
      ((Restated.Vocabulary.Execution.Setup.a M S r)) :=
    Restated.honest_emits_exact_actionAttestationAtOn facts S Hs Xb hf r huHon hsourceHor hlo
      (hA r hloEarlyR u huDelta) (fun j hj => hf.tick_outcome j _ _ hj) na hna D hD
  obtain ⟨i, hi, -, -, -, -, hhead⟩ :=
    Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_head facts S rho W hf.onePath hemit
  have hna' : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (W i u) a.round := by
    rw [hshape.2.1]
    rcases Restated.action_read_indexOn facts S rho Hs Xb hf i u r hi with hstate | hstate
    · rw [hstate]
      exact hna
    · rw [hstate, (p62% actionReadFrom_wake₆₂) facts]
      exact hna
  obtain ⟨Hb, hHb, hconfirmed⟩ := hhead na hna'
  have hbodies := (p62% actionReadFrom_bodies₆₂s) facts S _ r na hna
  have hcarrierMem : A ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u).st.core.T :=
    Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho u r _
      humem na hna g2 hg2 A hAsel
  obtain ⟨Dn, hDbody, hDerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
      (Restated.Vocabulary.Execution.Setup.a M S r) u _ humem hcarrierMem
  have hDrun : Restated.RunBlockOn M S rho W Xb Dn :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb huXb hDbody
  have hHrun : Restated.RunBlockOn M S rho W Xb Hb :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb huXb (by rw [← hbodies]; exact hHb)
  have hroot : Dn.root = Hb.root := by
    rw [← Proofs.NamedWire.erase_root Dn, hDerase]
    exact Option.some.inj (hshape.2.2.symm.trans hconfirmed)
  have hDH : Dn = Hb :=
    hf.rootCollisionFree.root_injective Dn Hb hDrun hHrun Dn Hb
      (Or.inl (Proofs.NamedAncestry.named_self Dn)) (Or.inr (Proofs.NamedAncestry.named_self Hb))
      hroot
  have hHErase : Hb.erase = A := by
    rw [← hDH, hDerase]
  have hpostA : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
    rw [hshape.2.1]
    exact hlo
  have hdeadlineA : max ((Restated.Vocabulary.Execution.Setup.a M S a.round)) lo + S.E.Δ ≤
      M.early S.E S.hc (r + 1) p := by
    rw [hshape.2.1]
    exact hdeadline
  have hinput : M.sgVote a.erase ∈ I := by
    rcases compatible_cases hcompat with hFCarrier | hcarrierF
    · exact Restated.action_vote_mem_interpretedInputs_after_gst_common_upperOn facts
        S Hs Xb hf hHs hHsXb (t := M.domain S.E S.hc (r + 1) p) p hk huEarly hwEarly
        ⟨hshape.1, hshape.2.1, hemit⟩ ⟨i, hi, ⟨na, hna', hHb⟩, hconfirmed⟩
        (C := Hb.erase) (Proofs.ModelProperties.Preceq_self _)
        (by rw [hHErase]; exact hFCarrier) hpostA hdeadlineA horder hcut I hI
    · exact Restated.action_vote_mem_interpretedInputs_after_gst_common_upperOn facts
        S Hs Xb hf hHs hHsXb (t := M.domain S.E S.hc (r + 1) p) p hk huEarly hwEarly
        ⟨hshape.1, hshape.2.1, hemit⟩ ⟨i, hi, ⟨na, hna', hHb⟩, hconfirmed⟩
        (C := (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core.F)
        (by rw [hHErase]; exact hcarrierF)
        (Proofs.ModelProperties.Preceq_self _) hpostA hdeadlineA horder hcut I hI
  have hfind : Block.find?
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core.T A.root = some A := by
    obtain ⟨Rw, hRw⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core))
      S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p) u
    obtain ⟨b, hb⟩ := facts.gr.bodyReady_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core.F
      (M.early S.E S.hc (r + 1) p) (M.sgVote a.erase)
    have hready : b = true := ((facts.gr.mem_interpretedInputs_iff I hI Rw hRw b hb).mp hinput).2
    have hconf : (M.sgVote a.erase).confirmed = some A.root := by
      rw [facts.sto.sgVote_confirmed, hshape.2.2]
    cases hfindY : Block.find?
        (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core.T A.root with
    | none =>
        have hfalse := facts.gr.bodyReady_eq_false_of_find_none _ _ _ _ hconf
          (by rw [facts.gr.Sts_gradeView_T]; exact hfindY) b hb
        rw [hready] at hfalse
        exact False.elim (Bool.noConfusion hfalse)
    | some Y =>
      have hYmem := Proofs.HealingLemmas.find?_mem hfindY
      obtain ⟨Yn, hYerase, hYrun⟩ :=
        Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hw)
          (M.domain S.E S.hc (r + 1) p) hYmem
      have hYHroot : Yn.root = Hb.root := by
        rw [← Proofs.NamedWire.erase_root Yn, hYerase,
          Proofs.HealingLemmas.find?_root hfindY, ← hHErase,
          Proofs.NamedWire.erase_root Hb]
      have hYH := hf.rootCollisionFree.root_injective Yn Hb hYrun hHrun Yn Hb
        (Or.inl (Proofs.NamedAncestry.named_self Yn))
        (Or.inr (Proofs.NamedAncestry.named_self Hb)) hYHroot
      have hYeq : Y = A := by
        rw [← hYerase, hYH, hHErase]
      rw [hYeq]
  refine ⟨M.sgVote a.erase, hinput, ?_, ?_, hfind⟩
  · rw [facts.sto.sgVote_round]
    exact hshape.2.1
  · rw [facts.sto.sgVote_confirmed, hshape.2.2]

end

end DecoupledConsensusModel.Sts.Restated
